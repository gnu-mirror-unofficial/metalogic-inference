/* Copyright (C) 2017 Hans Åberg.

   This file is part of MLI, MetaLogic Inference.

   This program is free software: you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation, either version 3 of the License, or
   (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program.  If not, see <http://www.gnu.org/licenses/>.  */

#include "inferenceengine.hh"

#include "metacondition.hh"
#include "precedence.hh"


namespace mli {

  class inference_tree {
  public:
    class node;
    class edge;

    enum search_type {
      first_most,           // First-most (as in stack-engine).
      breadth_first,        // Breadth-first search.
      lowest_weight,        // Lowest weight search.
      breadth_first_weight  // First not-less weight in breadth-first order.
    };

    typedef long unsigned size_type;

    struct edge {
    public:
      node *parent_, *child_;
      ref<alternative> alternative_;
      size_type weight_;
      
      edge() : parent_(0), child_(0), weight_(0) {}
      ~edge() { delete child_; }

      edge(const ref<alternative>& a, node* p, size_type w, node* c = 0)
       : alternative_(a), weight_(w), parent_(p), child_(c) {}
      
      void write(std::ostream& os, write_style ws) const {
        os << "edge[ weight " << weight_ << ", alternative = ";
        alternative_->write(os, ws);
        if (child_ != 0) {
          os << "\n";
          child_->write(os, ws);
        }
        os << " ]";
      }
    };

    class node {
    public:
      typedef std::list<edge> edge_container;
      typedef edge_container::iterator iterator;
      typedef edge_container::const_iterator const_iterator;
      typedef edge_container::size_type size_type;

      edge_container::iterator edge_; // Parent edge
      edge_container edges_;

      node(const ref<alternatives>& as) {
        init(as, 0);
      }

      node(const ref<alternatives>& as, edge_container::iterator e)
       : edge_(e) {
        init(as, e->weight_);
      }

      void init(const ref<alternatives>& as, size_type w) {
        if (as.is_null())  return;
        size_type n = as->size();
        alternatives::const_iterator i = as->begin(), i1 = as->end();
        for (; i != i1; ++i) {
          edges_.push_back(edge(*i, this, w + n * (*i)->goal_->metasize()));
        }
      }

      void write(std::ostream& os, write_style ws) const {
        os << "node{\n";
        const_iterator i, i0 = edges_.begin(), i1 = edges_.end();
        for (i = i0; i != i1; ++i) {
          if (i != i0)  os << "\n";
          i->write(os, ws);
        }
        os << "\n} node\n";
      }
    };

    node* root_;
    node::iterator current_edge_;

    inference_tree() : root_(0) {}
    ~inference_tree() { delete root_; }

    struct iterator {
      node* root_;
      node::iterator edge_;

      iterator() : root_(0) {}
      iterator(node* r, const node::iterator& i) : root_(r), edge_(i) {}
      
      ref<proof> get_proof(const ref<formula>& x) const {
        proof* pp = new proof(x);
        ref<proof> pf(pp);
        if (root_ == 0)  return pf;
        node::iterator i = edge_;
        for (;; i = i->parent_->edge_) {
          pp->push_front(i->alternative_);
          if (i->parent_ == root_)  break;
        }
        return pf;
      }
    };

    virtual iterator current() {
      return iterator(root_, current_edge_);
    }

    virtual void push(const ref<alternatives>& as, search_type s = breadth_first_weight) {
      if (root_ == 0) {
        root_ = new node(as);
        // Will select smallest weight if the alternatives are sorted according
        // to metaand size:
        current_edge_ = root_->edges_.begin();
        return;
      }
      current_edge_->child_ = new node(as, current_edge_);
      switch (s) {
        case first_most:
          current_edge_ = begin();  break;

        case breadth_first:
          current_edge_ = next_edge(current_edge_);  break;

        case lowest_weight:
          current_edge_ = lowest_weight_edge();  break;

        case breadth_first_weight:
          current_edge_ = next_notless_weight_edge(current_edge_);  break;
      }
    }

    node::iterator next_edge(const node::iterator& e) {
      node::iterator f = e;
      ++f;
      if (f != e->parent_->edges_.end())
        return f;
      if (e->parent_ != root_)
        return first(next_edge(e->parent_->edge_));
      return begin();
    }

    node::iterator next_notless_weight_edge(const node::iterator& e) {
      // Must program around the fact that, in general, e will not point at
      // an end-edge. The following ensures that f0, as well as f, point at
      // end-edges, enabling the comparison test in the loop below:
      size_type w0 = e->weight_;
      node::iterator f0 = next_edge(e), f = f0;
      while (f->weight_ > w0) {
        f = next_edge(f);
        if (f == f0)  break;
      }
      return f;
    }

    node::iterator lowest_weight_edge() {
      node::iterator e = begin(), f_min = e, f;
      size_type w, w_min = e->weight_; // Lowest weight so far.
      for (f = next_edge(e); f != e; f = next_edge(f)) {
        w = f->weight_;
        if (w < w_min) {
          f_min = f;
          w_min = w;
        }
      }
      return f_min;
    }

    virtual void pop() {
      if (root_ == 0)  return;
      node* pp = current_edge_->parent_;
      // Delete the singleton nodes from here towards the root, in
      // order to avoid non-termination in solve.
      if (pp->edges_.size() <= 1) {
        if (pp == root_)
          root_ = 0;
        else {
          current_edge_ = pp->edge_;
          current_edge_->child_ = 0;
        }
        delete pp;
        pop();
        return;
      }
      node::iterator old = current_edge_;
      node::iterator next = next_edge(current_edge_);
      // Now, as the tree cannot be a list, in view of the deletions above,
      // the current choices of next_edge() functions will ensure that
      // next != current_edge_:
      if (next == current_edge_)
        throw interpret_error("Next edge not new in inference_tree::pop().");
      current_edge_ = next;
      pp->edges_.erase(old);
      if (pp->edges_.empty()) {
        if (pp == root_)
          root_ = 0;
        else
          pp->edge_->child_ = 0;
        delete pp;
      }
      return;
    }

    size_type degree(const node::iterator& e) const {
      if (e->parent_ == root_)  return 1;
      return degree(e->parent_->edge_) + 1;
    }

    virtual bool empty() const { return root_ == 0; }

    virtual size_type size() const {
      if (root_ == 0)  return 0;
      return degree(current_edge_);
    }

    size_type get_level() const { return size() + 1; }

    node* first(node* np) {
      if (np == 0)  return 0;
      node* cp = np->edges_.begin()->child_;
      return (cp == 0)? np : first(cp);
    }

    node::iterator first(node::iterator i) {
      if (i->child_ == 0)  return i;
      return first(i->child_->edges_.begin());
    }

    node::iterator begin() {
      if (root_ == 0)  return node::iterator();
      return first(root_)->edges_.begin();
    }

    virtual void write(std::ostream&, write_style) const;
  };

  inline std::ostream& operator<<(std::ostream& os, const inference_tree& x) {
    x.write(os, write_default);  return os;
  }


  void inference_tree::write(std::ostream& os, write_style ws) const {
    os << "inference_tree {\n";
    if (root_ != 0) {
      root_->write(os, ws);
      os << std::endl << "Current edge: ";
      current_edge_->write(os, ws);
    }
    os << "} inference_tree \n";
  }


  extern ref<formula> theCut;
  void cut(inference_stack&);


  // In the stack engine, the stack is essentially a function parameter stack
  // for multiple function alternatives, where the statements (axioms) searched
  // for, act as though being functions. When a multiple function call appears,
  // i.e., a sequence of proposition (axiom) alternatives, the stack records the
  // data needed for later examination of the alternatives:
  // 1. The so far obtained substitution.
  // 2. The sequence of formulas that need to be proved (the future goals).
  // 3. The list of alternative statements (axioms) that should be investigated
  //    as though being additional function possibilities.
  // Here, essentially, 1 and 2 are the function parameters, and 3 are the
  // alternative function calls.

  std::list<ref<proof> > database::prove(const ref<formula>& x, int n) {
    inference_tree it;
    std::list<ref<proof> > pfs;
    this->solve(x, it, pfs, n);
    return pfs;
  }

  #define NO_SUBST 1

  void database::solve(const ref<formula>& x, inference_tree& it,
    std::list<ref<proof> >& pfs, int n) {
    ref<alternatives> as;
    ref<alternative> a;
    inference_tree::iterator v;
    ref<formula> g = x;

    for (;;) {
  solve: // Prove first goal (formula) of the formula sequence:
      if (trace_value & trace_proof) {
        std::clog << "Solve:\n"
          << "Substitution: " << a->substitution_ << "\n"
          << "Goal: " << g << std::endl;
      }
  #if !NO_SUBST
      g = (*a->substitution_)(g); // Find alternatives: applicable statements (axioms) of substituted goal..
      if (trace_value & trace_proof)
        std::clog << "Substituted goal: " << g << std::endl;
  #endif
      switch ((const int)(const kleenean)g->succeed_or_fail()) {
        case 0: // fail
          if (trace_value & trace_proof)  std::clog << "Fail.\n" << std::flush;
          goto backtrack;
        case 1: // succeed
          pfs.push_back(v.get_proof(x));
          if (n > 0 && pfs.size() >= n) {
            if (trace_value & (trace_result | trace_proof))
              std::clog << "Proof success.\n" << std::flush;
            return; // Found the required max n solutions.
          }
          goto backtrack;  // Then try to unwind the stack.
        default:
          ;
      }
  #if 0
      // Disable the cut for now.
      if (g == theCut) { // If the goal asks for stack manipulation, do that.
        cut(it);
        if (trace_value & trace_proof)
          std::clog << "Level: " << it.get_level() << "\n" << std::flush;
        goto solve;
      }
  #endif
      // Find full list of alternatives; later, in choose, lop off first alternative
      // and push rest onto stack. The found value must be detached from the reference
      // cluster, as it will be mutated.
      as = this->find(g, it.get_level(), this);
      if (trace_value & trace_proof)
        std::clog
          << "Solve, level " << it.get_level()
          << ", find(\n  " << g << "):" << as << std::endl;
      if (as->empty())  goto backtrack;
  #if 1
      as->metaand_sort();  // Set metaand-shortest resolvents first.
  #endif
      as = as->solutions(pfs, v.get_proof(x));
      if (n > 0 && pfs.size() >= n) {
        if (trace_value & (trace_result | trace_proof))
          std::clog << "Proof succeeded.\n" << std::flush;
        return; // Found the required max n solutions.
      }
      if (as->empty())  goto backtrack;
      // Put alternatives onto inference tree. Then select favorite alternative
      // from the inference tree for examination.
      if (level_max > 0 && it.get_level() >= level_max)
        throw interpret_error("Exceeding set max inference tree size.");
      if (trace_value & trace_prooftree)
        std::clog << "Tree before push: " << it << std::endl;
      it.push(as);
      if (trace_value & trace_prooftree)
        std::clog << "Tree after push: " << it << std::endl;
      if (trace_value & trace_proof)
        std::clog << "Level: " << it.get_level() << "\n" << std::flush;
      goto choose;

  choose:
      v = it.current();
      a = v.edge_->alternative_;
      g = a->goal_;
      if (trace_value & trace_proof) {
        std::clog << "Choose:\n";
        std::clog << "Level: " << it.get_level() << "\n";
        std::clog << "Alternative:\n" << a << std::endl;
      }
      goto solve;

  backtrack: // If possible, unwind the stack:
      if (it.empty()) {
        if ((trace_value & (trace_result | trace_proof)) && pfs.empty())
          std::clog << "Proof failed.\n" << std::flush;
        return;
      }
      if (trace_value & trace_proof) {
        std::clog << "Backtrack:\n";
        std::clog << "Level: " << it.get_level() << std::endl;
      }
      if (trace_value & trace_prooftree)
        std::clog << "Tree before pop: " << it << std::endl;
      it.pop();
      if (trace_value & trace_prooftree)
        std::clog << "Tree after pop: " << it << std::endl;
      if (it.empty()) {
        if ((trace_value & (trace_result | trace_proof)) && pfs.empty())
          std::clog << "Proof failed.\n" << std::flush;
        return;
      }
      goto choose;
    } // for (;;)
  }

  #if 0
  void cut(inference_stack& x) {
    if (trace_value & trace_cut) {
      std::clog << "Before cut: " << std::flush;
  #if 0
      x.write(std::clog, write_default);
  #endif
    }
    if (x.size() >= 1) {
      inference_stack::iterator i = x.end();
      --i;
      i->alternatives_->clear(); // Clear top alternatives.
      if (x.size() >= 2) {
        --i;
        i->alternatives_->clear(); // Clear second top alternatives,
      }
    }
    if (trace_value & trace_cut) {
      if (x.size() >= 1) {
        std::clog << "After cut: " << std::flush;
  #if 0
        x.write(std::clog, write_default);
  #endif
      } else
        std::clog << "After cut: No stack change." << std::endl;
    }
  }
  #endif

} // namespace mli

