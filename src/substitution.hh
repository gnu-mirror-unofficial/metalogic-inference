/* Copyright (C) 2017, 2021-2022 Hans Åberg.

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

#pragma once

#include "MLI.hh"
#include "definition.hh"
#include "precedence.hh"

#include <map>
#include <set>
#include <vector>
#include <tuple>


namespace mli {


  /* A substitution is a function mapping variables to formulas of the same
  object type as the variable, i.e., variable describing terms are mapped to
  terms, etc. It is then extended via the functions A::substitute() to a mapping
  of formulas to formulas of matching formula type.

    substitution()  the identity substitution; maps a variable x to itself viewed
                    as a formula.
    variable_substitution(x, f)
                    the substitution that maps the variable x to the formula f.
    s(f)            extends the substituion s to the formula f.
    s1 + s2         the composition (s1 o s2)(x) := s1(s2(x)).
    s1 * s2         the composition (s1 * s2)(x) := s2(s1(x)).
  */


  // Apart from being a base class, substitution() also represents the
  // identity substitution.
  class substitution : public nonempty_formula {
  public:
    new_copy(substitution);
    new_move(substitution);

    virtual bool is_identity() const { return true; }

    virtual ref<formula> substitute_variable(const ref<variable>& x, substitute_environment) const
    { return ref<formula>(x); }

    // Extends the substitution *this to a function, mapping formulas to formulas:
    virtual ref<formula> operator()(const ref<formula>& x) const;

    formula::type get_formula_type() const override { return formula::meta; }

    virtual kleenean has(const ref<variable>&, occurrence) const { return false; }
    virtual void contains(std::set<ref<variable>>&, std::set<ref<variable>>&, bool&, occurrence) const {}


    // Find the set of variables varied in the substitution.
    virtual void get_varied(std::set<ref<variable>>&, metalevel_t) const {}

    // Variables varied of a premise vs, variables varied in reduction vrs, associated
    // with the formulas set variable fsv, and offset m, the position in the substituted premise
    // at where the varied variables should be inserted.
    virtual void get_varied(varied_type& vvs, varied_type& vrs, const variable& fsv, size_type m) const {}


    virtual kleenean free_for(const ref<formula>&, const ref<variable>&, 
      std::set<ref<variable>>&, std::list<ref<variable>>&) const { return true; }

    void unspecialize(depth, bool) override {}
    void unspecialize(std::set<ref<variable>>&, bool) override {}

    virtual ref<formula> substitute(const ref<substitution>&, substitute_environment) const { return this; }

    virtual void set_bind(bind&, name_variable_table&) {}

    virtual alternatives unify(unify_environment, const ref<formula>&, unify_environment, database*, level, degree_pool&, direction) const;

  #if 0  // Defined in class formula:
    virtual split_formula split(unify_environment, const ref<variable>&, const ref<formula>&, unify_environment, database*, level, degree_pool&, direction) const;
  #endif

    // One has *this = innermost()*without(), and innermost() of the form
    // [x↦t] or equal to I:
    virtual ref<substitution> innermost() const { return this; }
    virtual ref<substitution> without() const { return this; }

    // One has *this = within()*outermost(), and outermost() of the form
    // [x↦t] or equal to I:
    virtual ref<substitution> outermost() const { return this; }
    virtual ref<substitution> within() const { return this; }

    virtual order compare(const unit&) const;

    virtual void write(std::ostream& os, write_style) const { os << "I"; }
  };


  class variable_substitution : public substitution {
  public:
    ref<variable> variable_;
    ref<formula> formula_;

    // A substitution from a premise to a conclusion only substitutes
    // free occurrences if explicit, a varied variable in case not
    // representing the identity.
    bool premise_to_conclusion_ = false;
    bool is_varied_ = false;

    size_type premise_index_ = 0;
    size_type conclusion_index_ = 0;

    varied_type varied_, varied_in_reduction_;


  public:
    variable_substitution() {}

    new_copy(variable_substitution);
    new_move(variable_substitution);


    variable_substitution(const ref<variable>& i, const ref<formula>& t)
     : variable_(i), formula_(t) {}

    variable_substitution(const ref<variable>& i, const ref<formula>& t,
      const varied_type& vs, const varied_type& vrs)
     : variable_(i), formula_(t), varied_(vs), varied_in_reduction_(vrs) {}

    variable_substitution(const ref<variable>& i, const ref<formula>& t, size_type px, size_type cx, bool v)
     : variable_(i), formula_(t), premise_index_(px),
       premise_to_conclusion_(true), conclusion_index_(cx), is_varied_(v) {}


    virtual bool is_identity() const { return variable_ == formula_; }

    virtual ref<formula> substitute_variable(const ref<variable>& x, substitute_environment) const;

    formula::type get_formula_type() const override { return formula::meta; }

    virtual void set_bind(bind&, name_variable_table&);
    virtual ref<formula> rename(level, degree) const;
    virtual ref<formula> add_exception_set(variable_map&) const override;

    virtual kleenean has(const ref<variable>&, occurrence) const;
    virtual void contains(std::set<ref<variable>>&, std::set<ref<variable>>&, bool&, occurrence) const;


    // A substitution of limited variables is varied if it comes from a premise to a conclusion,
    // is explicit, and does not represent the identity substitution. However, variable::unify
    // only sets is_varied_ if also is_explicit_ && premise_to_conclusion_ is true, so a check
    // for the latter is not required here.
    bool is_varied() const { return is_varied_; }

    void get_varied(std::set<ref<variable>>& vs, metalevel_t ml) const override {
      if (is_varied() && ml == variable_->metalevel_)
        vs.insert(variable_);
    }


    void get_varied(varied_type& vvs, varied_type& vrs, const variable& fsv, size_type m) const override {
      if (*variable_ == fsv) {
        for (auto& i: varied_)
          for (auto& j: i.second)
            for (auto& k: j.second)
              vvs[i.first][j.first + m].insert(k);

        for (auto& i: varied_in_reduction_)
          for (auto& j: i.second)
            for (auto& k: j.second)
                vrs[i.first][j.first + m].insert(k);
      }
    }


    virtual kleenean free_for(const ref<formula>& f, const ref<variable>& x, 
      std::set<ref<variable>>& s, std::list<ref<variable>>& bs) const;

    void unspecialize(depth, bool) override;
    void unspecialize(std::set<ref<variable>>&, bool) override;

    virtual ref<formula> substitute(const ref<substitution>&, substitute_environment) const;

    virtual alternatives unify(unify_environment, const ref<formula>&, unify_environment, database*, level, degree_pool&, direction) const;

    virtual split_formula split(unify_environment, const ref<variable>&, const ref<formula>&, unify_environment, database*, level, degree_pool&, direction) const;

    virtual ref<substitution> innermost() const;
    virtual ref<substitution> without() const;
    virtual ref<substitution> outermost() const;
    virtual ref<substitution> within() const;

    virtual order compare(const unit&) const;

    virtual precedence_t precedence() const { return formula_->precedence(); }

    virtual void write(std::ostream& os, write_style ws) const;
  };


  class explicit_substitution : public substitution {
  public:
    ref<variable> variable_;
    ref<formula> formula_;

  public:
    explicit_substitution() {}

    new_copy(explicit_substitution);
    new_move(explicit_substitution);


    explicit_substitution(const ref<variable>& i, const ref<formula>& t)
     : variable_(i), formula_(t) {}


    virtual bool is_identity() const { return variable_ == formula_; }

    virtual ref<formula> substitute_variable(const ref<variable>& x, substitute_environment) const;

    virtual alternatives unify_substitution2(const ref<formula>&, unify_environment, const ref<formula>&, unify_environment, database*, level, degree_pool&, direction) const;

    formula::type get_formula_type() const override { return formula::meta; }

    virtual void set_bind(bind&, name_variable_table&);
    virtual ref<formula> rename(level, degree) const;
    virtual ref<formula> add_exception_set(variable_map&) const override;

    virtual kleenean has(const ref<variable>&, occurrence) const;
    virtual void contains(std::set<ref<variable>>&, std::set<ref<variable>>&, bool&, occurrence) const;

    virtual kleenean free_for(const ref<formula>& f, const ref<variable>& x,
      std::set<ref<variable>>& s, std::list<ref<variable>>& bs) const;

    void unspecialize(depth, bool) override;
    void unspecialize(std::set<ref<variable>>&, bool) override;

    virtual ref<formula> substitute(const ref<substitution>&, substitute_environment) const;

    virtual alternatives unify(unify_environment, const ref<formula>&, unify_environment, database*, level, degree_pool&, direction) const;

    virtual split_formula split(unify_environment, const ref<variable>&, const ref<formula>&, unify_environment, database*, level, degree_pool&, direction) const;

    virtual ref<substitution> innermost() const;
    virtual ref<substitution> without() const;
    virtual ref<substitution> outermost() const;
    virtual ref<substitution> within() const;

    virtual order compare(const unit&) const;

    virtual precedence_t precedence() const { return formula_->precedence(); }

    virtual void write(std::ostream& os, write_style ws) const;
  };


  class substitution_composition : public substitution {
    ref<substitution> inner_ = ref<substitution>(make);
    ref<substitution> outer_ = ref<substitution>(make);

  public:
    substitution_composition() = default;

    new_copy(substitution_composition);
    new_move(substitution_composition);

    substitution_composition(const ref<substitution>& outer, const ref<substitution>& inner)
     : outer_(outer), inner_(inner) {}

    virtual bool is_identity() const { return inner_->is_identity() && outer_->is_identity(); }

    virtual ref<formula> substitute_variable(const ref<variable>& x, substitute_environment vt) const;

    formula::type get_formula_type() const override { return formula::meta; }

    // Variable renumbering:
    virtual void set_bind(bind&, name_variable_table&);
    virtual ref<formula> rename(level, degree) const;
    virtual ref<formula> add_exception_set(variable_map&) const override;

    // Free variables:
    virtual kleenean has(const ref<variable>&, occurrence) const;
    virtual void contains(std::set<ref<variable>>&, std::set<ref<variable>>&, bool&, occurrence) const;


    void get_varied(std::set<ref<variable>>& vs, metalevel_t ml) const override
    { inner_->get_varied(vs, ml); outer_->get_varied(vs, ml); }

    void get_varied(varied_type& vvs, varied_type& vrs, const variable& fsv, size_type m) const override
    { inner_->get_varied(vvs, vrs, fsv, m); outer_->get_varied(vvs, vrs, fsv, m); }


    virtual kleenean free_for(const ref<formula>& f, const ref<variable>& x, 
      std::set<ref<variable>>& s, std::list<ref<variable>>& bs) const;

    // Fixed variables:
    void unspecialize(depth, bool) override;
    void unspecialize(std::set<ref<variable>>&, bool) override;

    // Substitution:
    virtual ref<formula> substitute(const ref<substitution>&, substitute_environment) const;

    // Unification:
    virtual alternatives unify(unify_environment, const ref<formula>&, unify_environment, database*, level, degree_pool&, direction) const;
    
    virtual split_formula split(unify_environment, const ref<variable>&, const ref<formula>&, unify_environment, database*, level, degree_pool&, direction) const;

    virtual ref<substitution> innermost() const;
    virtual ref<substitution> without() const;
    virtual ref<substitution> outermost() const;
    virtual ref<substitution> within() const;

    // Comparison, needed for unification and database lookup.
    virtual order compare(const unit&) const;

    // Writing:
    virtual precedence_t precedence() const { return precedence_t(); }

    virtual void write(std::ostream& os, write_style ws) const;
  };


  // Composition objects f * g = f ∙ g ≔ g ∘ f of substitutions viewed as functions f, g (as described above),
  // i.e., written in prefix notation as (f ∙ g)(x) = (g ∘ f)(x) ≔ g(f(x)), and in postfix notation
  // written (x)(f ∙ g) = (x)(g ∘ f) ≔ g(f(x)).
  // Variable substitutions f, g are written postfix, so A f g = A (f*g)
  ref<substitution> operator*(const ref<substitution>& f, const ref<substitution>& g);


  // Used for explicit substitution expressions A[x ⤇ t], formally a pair (A, s)
  // where A is a formula and s = [x ⤇ t] an explicit substitution. Unification is particularly
  // complicated for this type: u(A[x ⤇ t], B) involvs finding all subexpressions of B
  // unifying with t with a set S occurrences in. Any subset of S can be replaced by
  // x to give a possible A. In addition, if t is unspecialized, then so must this
  // property be forwarded to x.
  class substitution_formula : public nonempty_formula {
  public:
    ref<explicit_substitution> substitution_; // Initializes to default substitution, i.e., I.
    ref<formula> formula_;


    substitution_formula() = default;

    substitution_formula(const ref<explicit_substitution>& s, const ref<formula>& f)
     : substitution_(s), formula_(f) {}


    new_copy(substitution_formula);
    new_move(substitution_formula);

    virtual formula::type get_formula_type() const;

    // Variable renumbering:
    virtual void set_bind(bind&, name_variable_table&);
    virtual ref<formula> rename(level, degree) const;
    virtual ref<formula> add_exception_set(variable_map&) const override;

    // Free variables:
    virtual kleenean has(const ref<variable>&, occurrence) const;
    virtual void contains(std::set<ref<variable>>&, std::set<ref<variable>>&, bool&, occurrence) const;

    virtual kleenean free_for(const ref<formula>& f, const ref<variable>& x,
      std::set<ref<variable>>& s, std::list<ref<variable>>& bs) const;

    // Fixed variables:
    void unspecialize(depth, bool) override;
    void unspecialize(std::set<ref<variable>>&, bool) override;

    // Substitution:
    virtual ref<formula> substitute(const ref<substitution>&, substitute_environment) const;

    // Unification:
    virtual alternatives unify(unify_environment, const ref<formula>&, unify_environment, database*, level, degree_pool&, direction) const;


    // Helper functions, for special types of unification:

    // Type 1: 𝐮(𝑨[𝒙 ⤇ 𝒕], 𝑩[𝒚 ⤇ 𝒖]) = 𝐮(𝒙, 𝒚).𝐮(𝑨, 𝑩).𝐮(𝒕, 𝒖).
    alternatives unify1(unify_environment, const substitution_formula&, unify_environment, database*, level, degree_pool&, direction) const;

    // Type 2. 𝐮(𝑨[𝒙 ⤇ 𝒕], 𝑩) = 𝐮(𝒕, 𝒱).𝐮(𝑨, 𝑩[𝒱 ↦ 𝒙]) where 𝒱 is a disjoint set of subformulas of 𝑩.
    // The cases 𝒱 = ∅ and 𝒱 = {𝑩} are allowed, in the latter case, 𝒕 and 𝑩 must be of the same type.
    alternatives unify2(unify_environment, const ref<formula>&, unify_environment, database*, level, degree_pool&, direction) const;


    virtual split_formula split(unify_environment, const ref<variable>&, const ref<formula>&, unify_environment, database*, level, degree_pool&, direction) const;

    // Comparison, needed for unification and database lookup.
    virtual order compare(const unit&) const;

    // Writing:
    virtual precedence_t precedence() const;

    virtual void write(std::ostream& os, write_style) const;
  };


  class alternative : public unit {
  public:
    ref<substitution> substitution_;  // Initializes to default substitution, i.e., I.
    ref<formula> goal_;

#if NEW_PROVED
    // For writing out the proof. The component statement_ is the statement used in the
    // unification, and definitions_ is the set of definitions. The substatements are
    // the statements used implicitly, like for logic, not required explicitly but shown
    // to allow for a more detailed examination of the proof.
    struct statement_data {
      ref<statement> statement_;
      std::vector<ref<statement>> definitions_;
#if NEW_SUBSTATEMENTS
      std::vector<std::string> substatements_;
#else
      std::vector<ref<statement>> substatements_;
#endif
    };

    std::map<size_type, statement_data> labelstatements_;
#else
    // For writing out the proof. First pair component is the statement used in the object
    // formula unification, the second component is the set of definitions and substatements used,
    // if any. A substatement is an implicit statement, like for logic, which is noy required
    // for the proof, but show to allow for a more detailed examination of the proof.
    std::map<size_type, std::pair<ref<statement>, std::vector<ref<statement>>>> labelstatements_;
#endif

    alternative() = default;
    
    new_copy(alternative);
    new_move(alternative);

    alternative(const ref<substitution>& s) : substitution_(s) {}
    alternative(const ref<substitution>& s, const ref<formula>& g)
     : substitution_(s), goal_(g) {}

    virtual alternative& label(const ref<statement>&, level);           // For statements.
    virtual alternative& label(const ref<statement>&, level, degree);   // For definitions and deductions.
    virtual alternative& sublabel(const std::string&, level);           // For substatements.

    alternative add_goal(const ref<formula>& x) const;

    alternative add_premise(const ref<formula>& x, metalevel_t,
      const varied_type& vs, const varied_type& vrs) const;

    virtual size_type metasize() const { return goal_->metasize(); }

    ref<substitution> operator*() { return substitution_; }
    const ref<substitution> operator*() const { return substitution_; }

    ref<formula> substitute_variable(const ref<variable>& x, substitute_environment vt) const
    { return substitution_->substitute_variable(x, vt); }

    ref<formula> operator()(const ref<formula>& x) const { return (*substitution_)(x); }

    void write(std::ostream&, write_style) const;
    
    // Combine substitutions and conditions (goals) as of old x followed by new y.
    // That is, in right hand notation, if x = (s, a), y = (t, b), then
    // x*y = (s*t, (a)t * b) where s*t is substition composition, s inner and t outer,
    // and (a)t is t applied to a.
    // This is the semidirect product 𝒮 ⋉ ℱ of the monoid 𝒮 of the set of
    // substitutions acting on the monoid ℱ the set of formula sequences.
    friend alternative operator*(const alternative& x, const alternative& y);
  };


  class alternatives : public unit {
  public:
    typedef std::list<alternative> container_type;
    typedef container_type::size_type size_type;
    typedef container_type::iterator iterator;
    typedef container_type::const_iterator const_iterator;
    typedef container_type::reverse_iterator reverse_iterator;
    typedef container_type::const_reverse_iterator const_reverse_iterator;

    container_type alternatives_;  

    alternatives() = default;

    new_copy(alternatives);
    new_move(alternatives);

    alternatives(const alternative& x)
     : alternatives_(1, x) {}

    explicit alternatives(const ref<formula>& f)
     : alternatives_(1, alternative(f)) {}

    alternatives(const ref<substitution>& s)
     : alternatives_(1, alternative(s)) {}
    
    alternatives(const ref<substitution>& s, const ref<formula>& g)
     : alternatives_(1, alternative(s, g)) {}

    alternatives(const ref<variable_substitution>& s)
     : alternatives(ref<substitution>(s)) {}

    alternatives(const ref<explicit_substitution>& s)
     : alternatives(ref<substitution>(s)) {}


    iterator               begin() { return alternatives_.begin(); }
    const_iterator         begin() const { return alternatives_.begin(); }
    iterator               end() { return alternatives_.end(); }
    const_iterator         end() const { return alternatives_.end(); }
    reverse_iterator       rbegin() { return alternatives_.rbegin(); }
    const_reverse_iterator rbegin() const { return alternatives_.rbegin(); }
    reverse_iterator       rend() { return alternatives_.rend(); }
    const_reverse_iterator rend() const { return alternatives_.rend(); }

    virtual bool empty() const { return alternatives_.empty(); }
    virtual size_type size() const { return alternatives_.size(); }

    virtual bool operator!() const { return alternatives_.empty(); }

    virtual void clear() { return alternatives_.clear(); }

    iterator erase(iterator i) { return alternatives_.erase(i); }

    virtual alternatives& label(const ref<statement>&, level);          // For statements.
    virtual alternatives& label(const ref<statement>&, level, degree);  // For definitions.
    virtual alternatives& sublabel(const std::string&, level);           // For substatements.

    virtual alternatives& push_back(const alternative& a);
    virtual alternatives& append(const alternatives& as);
    
    virtual const alternative& front() const { return alternatives_.front(); }
    virtual alternative& front() { return alternatives_.front(); }

    virtual alternative pop_front() {
      alternative a = alternatives_.front(); alternatives_.pop_front(); return a; }

    alternatives add_goal(const ref<formula>& x) const;

    alternatives add_premise(const ref<formula>& x, metalevel_t,
      const varied_type& vs, const varied_type& vrs) const;


    // For use in recursive computations of unify:
    // Each *this list alternative substitution s is applied to x and y,
    // computing unify(s(x), s(y)), and these returns are combined into a
    // single alternatives return value.
    virtual alternatives unify(const ref<formula>& x, unify_environment tx, const ref<formula>& y, unify_environment ty, database*, level, degree_pool&, direction, expansion = expand) const;

    // For use in the unification of binder expressions. unify_binder() differs from the recursive
    // unify() in that the substitution of variables is not kept in the total substitution.
    virtual alternatives unify_binder(
      const ref<formula>& x, unify_environment tx,
      const ref<formula>& y, unify_environment ty,
      database*, level, degree_pool&, direction) const;

    virtual void write(std::ostream&, write_style) const;

    // Combine substitutions and conditions (goals) as of old x followed by new y.
    friend alternatives operator*(const alternatives& x, const alternatives& y);
  };


  // Frequent alternatives:
  extern const alternatives O;  // No alternatives.
  extern const alternatives I;  // Identity substitution.


  // Combine substitutions and condition (goals) as of old x followed by new y, i.e., the goals
  // of x and y are concatenated with the substitution of y applied to the goal of x
  // and the substitution of x becomes the inner and the one of y the outer.
  alternative operator*(const alternative& x, const alternative& y);

  // Combining the x*y of the single alternatives contained in x and y:
  alternatives operator*(const alternatives& x, const alternatives& y);


  alternatives merge(const alternatives& x, const alternatives& y, metalevel_t ml);


  class proof : public unit {
  public:
    typedef std::list<alternative> container_type;
    typedef container_type::size_type size_type;
    typedef container_type::iterator iterator;
    typedef container_type::const_iterator const_iterator;
    typedef container_type::reverse_iterator reverse_iterator;
    typedef container_type::const_reverse_iterator const_reverse_iterator;

    ref<formula> goal_;
    container_type proof_;
    bool conditional_ = false; // True if not all statements used have a strict proof.

    proof() = default;

    new_copy(proof);
    new_move(proof);

    proof(const ref<formula>& x) : goal_(x) {}

    void push_front(const alternative&);
    void push_back(const alternative&);

    // Search the statements of the alternatives, and set conditional_
    // to true if not all have a strict proof.
    void set_conditional();

    bool is_conditional() const { return conditional_; }

    virtual void write(std::ostream&, write_style) const;
  };


  // A proof container.
  using proofs = std::list<proof>;


  class subformulas {
  public:
    typedef ref<formula> value_type;
    typedef std::list<value_type> container_type;
    typedef container_type::iterator iterator;
    typedef container_type::const_iterator const_iterator;
    typedef container_type::reverse_iterator reverse_iterator;
    typedef container_type::const_reverse_iterator const_reverse_iterator;

    container_type formulas_;  

    subformulas() = default;

    subformulas(const ref<formula>& f)
     : formulas_(1, f) {}

    bool operator!() const { return formulas_.empty(); }
    void clear() { formulas_.clear(); }

    iterator begin() { return formulas_.begin(); }
    const_iterator begin() const { return formulas_.begin(); }
    iterator end() { return formulas_.end(); }
    const_iterator end() const { return formulas_.end(); }
    reverse_iterator rbegin() { return formulas_.rbegin(); }
    const_reverse_iterator rbegin() const { return formulas_.rbegin(); }
    reverse_iterator rend() { return formulas_.rend(); }
    const_reverse_iterator rend() const { return formulas_.rend(); }

    void push_back(const ref<formula>& f) {
      formulas_.push_back(f);
    }
    void append(const subformulas& x) {
      formulas_.insert(formulas_.end(), x.formulas_.begin(), x.formulas_.end());
    }

    const value_type& front() const { return formulas_.front(); }
    value_type& front() { return formulas_.front(); }
    value_type pop_front() {
      value_type v = formulas_.front(); formulas_.pop_front(); return v; }

    void write(std::ostream& os, write_style ws) const;
  };

  inline std::ostream& operator<<(std::ostream& os, const subformulas& x) {
    x.write(os, write_default);  return os;
  }


  // List of pairs (fs, f), where fs are subformulas and f a formula:
  // Starting with a formula 𝑩 and a variable 𝒙, the 'split' function a set of
  // a list of (fs, f), where fs is a list of disjoint subformulas of 𝑩, and f is
  // the formula achived by replaced each fs with 𝒙.
  // If all subformulas fs unify with 𝑡 in 𝑨[𝒙 ↦ 𝑡], then f is a valid 𝑨.
  class split_formula {
  public:
    using value_type = std::tuple<subformulas, ref<formula>, std::set<ref<variable>>>;

    typedef std::list<value_type> container_type;
    typedef container_type::iterator iterator;
    typedef container_type::const_iterator const_iterator;
    typedef container_type::reverse_iterator reverse_iterator;
    typedef container_type::const_reverse_iterator const_reverse_iterator;

    container_type sequence_;

    split_formula() = default;
    
    split_formula(const ref<formula>& f)
     : sequence_(1, value_type(subformulas(), f, {})) {}
    
    split_formula(const ref<formula>& fs, const ref<formula>& f)
     : sequence_(1, value_type(subformulas(fs), f, {})) {}
    
    split_formula(const subformulas& fs, const ref<formula>& f)
     : sequence_(1, value_type(fs, f, {})) {}

    split_formula(const subformulas& fs, const ref<formula>& f, const std::set<ref<variable>>& vs)
     : sequence_(1, value_type(fs, f, vs)) {}


    bool operator!() const { return sequence_.empty(); }
    void clear() { sequence_.clear(); }

    iterator begin() { return sequence_.begin(); }
    const_iterator begin() const { return sequence_.begin(); }
    iterator end() { return sequence_.end(); }
    const_iterator end() const { return sequence_.end(); }
    reverse_iterator rbegin() { return sequence_.rbegin(); }
    const_reverse_iterator rbegin() const { return sequence_.rbegin(); }
    reverse_iterator rend() { return sequence_.rend(); }
    const_reverse_iterator rend() const { return sequence_.rend(); }

    void push_back(const ref<formula>& f) {
      sequence_.push_back(value_type(subformulas(), f, {}));
    }

    void push_back(const ref<formula>& fs, const ref<formula>& f) {
      sequence_.push_back(value_type(subformulas(fs), f, {}));
    }

    void push_back(const subformulas& fs, const ref<formula>& f) {
      sequence_.push_back(value_type(fs, f, {}));
    }

    void push_back(const ref<formula>& fs, const ref<formula>& f, const std::set<ref<variable>>& vs) {
      sequence_.push_back(value_type(subformulas(fs), f, vs));
    }

    void push_back(const subformulas& fs, const ref<formula>& f, const std::set<ref<variable>>& vs) {
      sequence_.push_back(value_type(fs, f, vs));
    }


    void append(const split_formula& x) {
      sequence_.insert(sequence_.end(), x.sequence_.begin(), x.sequence_.end());
    }

    const value_type& front() const { return sequence_.front(); }
    value_type& front() { return sequence_.front(); }
    value_type pop_front() {
      value_type v = sequence_.front(); sequence_.pop_front(); return v; }

    void write(std::ostream& os, write_style ws) const;
  };


  inline std::ostream& operator<<(std::ostream& os, const split_formula& x) {
    x.write(os, write_default);  return os;
  }


  template<class Construct>
  split_formula split(
      const Construct& c,
      const ref<variable>& x, const ref<formula>& t, direction dr) {
    if (trace_value & trace_split)
      std::clog
        << "split(), replacement "
        << x << ", condition: " << t << ":\n"
        << std::flush;

    split_formula sf; // Return value;
    ref<formula> f = c();

    if (trace_value & trace_split)
      std::clog
        << "  subformulas: none"
        << "\n  construct :\n    "
        << f
        << std::endl;

    sf.push_back(f);
    return sf;
  }


  template<class Construct>
  split_formula split(
      const ref<formula>& a, unify_environment ta, const Construct& c,
      const ref<variable>& x, const ref<formula>& t, unify_environment tt, database* dbp, level lv, degree_pool& sl, direction dr) {
    if (trace_value & trace_split)
      std::clog
        << "Begin split(" << a << "), replacement "
        << x << ", condition: " << t
        << std::endl;

    split_formula sf; // Return value;
    split_formula sf1 = a->split(ta, x, t, tt, dbp, lv, sl, dr);

    if (trace_value & trace_split)
      std::clog
        << "split(" << a << "), replacement "
        << x << ", condition: " << t << ":\n"
        << "  sf1:\n" << sf1
        << std::flush;

    for (auto& i: sf1) {
      subformulas fs = std::get<0>(i);
      ref<formula> f = c(std::get<1>(i));
      std::set<ref<variable>> vs = std::get<2>(i);

      if (trace_value & trace_split)
        std::clog
          << "\n  construct " << std::get<1>(i) << " :\n    "
          << f
          << "\n  " << fs
          << std::endl;

      if (!!fs)
        sf.push_back(fs, f, vs);
    }

    return sf;
  }


  template<class Construct>
  split_formula split(
      const ref<formula>& a, const ref<formula>& b, unify_environment ta, const Construct& c,
      const ref<variable>& x, const ref<formula>& t, unify_environment tt, database* dbp, level lv, degree_pool& sl, direction dr) {
    if (trace_value & trace_split)
      std::clog
        << "Begin split(" << a << " : " << b << "), replacement "
        << x << ", condition: " << t
        << std::endl;

    split_formula sf; // Return value;
    split_formula sf1 = a->split(ta, x, t, tt, dbp, lv, sl, dr);
    split_formula sf2 = b->split(ta, x, t, tt, dbp, lv, sl, dr);

    if (trace_value & trace_split)
      std::clog
        << "split(" << a << " : " << b << "), replacement "
        << x << ", condition: " << t << ":\n"
        << "  sf1:\n" << sf1
        << "  sf2:\n" << sf2
        << std::flush;

    for (auto& i: sf1) {
      for (auto& j: sf2) {
        subformulas fs;
        fs.append(std::get<0>(i));
        fs.append(std::get<0>(j));
        ref<formula> f = c(std::get<1>(i), std::get<1>(j));
        std::set<ref<variable>> vs = std::get<2>(i);
        vs.insert(std::get<2>(j).begin(), std::get<2>(j).end());

        if (trace_value & trace_split)
          std::clog
            << "  construct " << std::get<1>(i) << " : " << std::get<1>(j) << "\n    "
            << f
            << "\n  concatenate: " << std::get<0>(i) << " + " << std::get<0>(j) << ":"
            << fs
            << std::endl;

        if (!!fs)
          sf.push_back(fs, f, vs);
      }
    }

    return sf;
  }


} // namespace mli

