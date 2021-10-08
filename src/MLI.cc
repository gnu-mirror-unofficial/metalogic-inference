/* Copyright (C) 2017, 2021 Hans Åberg.

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

#include "MLI.hh"

#include <algorithm>
#include <cctype>
#include <cstring>
#include <iostream>
#include <sstream>

#include "definition.hh"
#include "metacondition.hh"
#include "proposition.hh"
#include "substitution.hh"
#include "function.hh"
#include "precedence.hh"


#define NEW_INFERENCE_UNIFY 0

#define NEW_INFERENCE_UNIFY_BODY 1


namespace mli {

  extern bool proofs_found;

  size_type level_max = 100;
  size_type unify_count = 0;
  size_type unify_count_max = 0;

  size_type proof_count = 1;

  bool expand_implicit_premise = false;

  bool strict_proof = false;


  degree degree_pool::get() {
    if (unused_.empty())
      return ++max_;  // No unused numbers < max_, so just increase max and return.

    // There are unused numbers, so pick smallest.

    auto i0 = unused_.begin();
    degree k = *i0;
    unused_.erase(i0);

    return k;
  }


  void degree_pool::put_back(degree k) {
    if (k == 0)  // All used degrees are > 0.
      return;

    if (k > max_) // No put back number should exceed max in use:
      throw std::runtime_error("Degree: put back value > max.");;

    // If put back number is smaller than the max in use, save it for future use:
    if (k < max_) {
      unused_.insert(k);
      return;
    }

    // Now k == max_ > 0, so decrease max_ and make sure the new value is not in unused_:

    --max_;

    // unused_ should never contain max_, so erase if it is in.
    if (!unused_.empty()) {
      auto i1 = unused_.end();
      --i1;

      if (*i1 == max_)
        unused_.erase(i1);
    }
  }



  ref<formula> concatenate(const ref<formula>& x, const ref<formula>& y, sequence::type t);


  ref<formula> formula::set_bind() {
    bind b = 0;
    name_variable_table vt;
    this->set_bind(b, vt);
    return this;
  }


  bool formula::contains(std::set<ref<variable>>& s, occurrence oc) const {
    std::set<ref<variable>> bs;
    bool more = false;  contains(s, bs, more, oc);  return more;
  }


  kleenean formula::free_for(const ref<formula>& t, const ref<variable>& x) const {
    // Only limited variables can pose a substitution problem, as the free
    // and bound object variables are kept separate in the semantic model.
    // That is, a free variable can only be substituted by a formula where its
    // free occurrences remian free.

    // Only limited variables can pose a substitution problem, that is, become
    // converted from free to bound by the substitution, in view of that free and
    // bound variables always have distinct names. Specifically, this condition
    // is checked after an explicit substitution A[x ↦ t] has been substituted by
    // the substitution s, in substitution_formula::substitute, and if s(x) remains
    // limited, this check is required. If s(x) is free or bound, then it cannot
    // become bound by the substitution in the semantic model.
#if 0
    const variable* xp = x.data();
    if (!xp->is_limited())
      return true;
#endif

    std::set<ref<variable>> s; // Free variables of t.

#if 0 // debug.hh
    // If *this is without bound occurrences of x, then t is free for x in *this:
    kleenean mb = has(x, occurrence::bound);
    if (mb == false)
      return true;
#endif

    // Find free variable occurrences in t; which are the variables that might
    // become bound by a substitution at x in *this: 
    bool more = t->contains(s, occurrence::free);
    if (more)             // A later substition of t may give it more variables
      return undefined; // that then might become bound.

    // If t has no free variables, then no such variables can become bound either,
    // so t is free for x in *this:
    if (s.empty())
      return true;

    std::list<ref<variable>> bs; // Bound variables currently in scope.

    return this->free_for(t, x, s, bs);
  }


  ref<formula> formula::substitute(const ref<substitution>&, substitute_environment) const {
    return ref<formula>();
  }


  bool formula::unexpanded_premise(unify_environment) const { return false; }


  alternatives formula::unify(unify_environment, const ref<formula>& f, unify_environment, database*, level, degree_pool&, direction) const {
    return (f->empty())? I : O;
  }


  alternatives formula::unify(const ref<formula>& x, unify_environment tx, const ref<formula>& y, unify_environment ty, database* dbp, level lv, degree_pool& sl, direction dr) const {
    return x->unify(tx, y, ty, dbp, lv, sl, dr);
  }


  split_formula formula::split(unify_environment tg,
      const ref<variable>& x, const ref<formula>& t, unify_environment tt, database* dbp, level lv, degree_pool& sl, direction dr) const {
    split_formula sf(this);
    // If t and *this unify, then *this can be replaced by x:
    alternatives as = mli::unify(t, tt, this, tg, dbp, lv, sl, dr);
    if (trace_value & trace_unify) {
      std::lock_guard<std::recursive_mutex> guard(write_mutex);
      std::clog << "formula::split:\n  "
        << "split(" << *this << "), replacement " << x << ", condition " << t << ":" 
        << as << std::endl;
    }

    if (!as.empty())
      sf.push_back(this, ref<formula>(x), tt.table_->find_local());

    return sf;
  }


  ref<formula> formula::expand(size_type) const { return ref<formula_sequence>(make, this); }


  ref<formula> nonempty_formula::add_premise(const ref<formula>& y, metalevel_t ml,
      const varied_type& vs, const varied_type& vrs) const {
    if (y->provable())
      return this;

    return ref<inference>(make, this, y, ml, vs, vrs);
  }


  ref<formula> nonempty_formula::add_goal(const ref<formula>& x) const {
    // If *this is not a sequence, but x is and of metaand type, prepend *this to the latter.
    // If neither of *this and x are a sequence, create a metaand sequence of the pair.

    if (x->provable())
      return this;

    // Find if x is a formula sequence at the proof metalevel, in which case prepend *this
    // to the return formula sequence, otherwise, return a pair formula sequence.

    formula_sequence* spx = ref_cast<formula_sequence*>(x);

    if (spx != 0)
      return ref<formula_sequence>(make, this, *spx); // Pointer 'this' treated as ref<formula>(this).

    return ref<formula_sequence>(make, this, x);  // Pointer 'this' treated as ref<formula>(this).
  }


  ref<formula> nonempty_formula::expand(size_type) const { return ref<formula_sequence>(make, this); }


  bool nonempty_formula::is_metasubset(const ref<formula> x) const {
    formula_sequence* fsp = ref_cast<formula_sequence*>(x);
    if (fsp == nullptr) return *this == *x;

    for (auto& i: fsp->formulas_)
      if (is_metasubset(i))
        return true;

    return false;
  }


  std::ostream& write_unify(std::ostream& os, const char* name, const ref<formula>& x, unify_environment tx, const ref<formula>& y, unify_environment ty, database* dbp, direction dr) {
    std::lock_guard<std::recursive_mutex> guard(write_mutex);

    if (name != 0)  os << name;

    os << "unify( ";
    os << ((dr == reduction)? "[reduction]" : "[deduction]");
    if (dbp != 0) {
      os << " by ";
      dbp->write(os, write_style(write_name | write_type));
    }
    os << "\n";

    if (dr == reduction)
      os
       << (tx.target_? "fact  " : "goal  ") << x << ";\n"
       << (ty.target_? "fact  " : "goal  ") << y << ")";
    else
      os
       << (ty.target_? "fact  " : "goal  ") << y << ";\n"
       << (tx.target_? "fact  " : "goal  ") << x << ")";

    return os;
  }


  // Master unification function mli::unify:
  // Sort out directions and unnest definitions:
  alternatives unify(const ref<formula>& x0, unify_environment tx0, const ref<formula>& y0, unify_environment ty0, database* dbp, level lv, degree_pool& sl, direction dr, expansion ex) {
    if (trace_value & trace_unify)
      write_unify(std::clog, "mli::", x0, tx0, y0, ty0, dbp, dr) << std::endl;

    if (proofs_found)
      throw thread_exit();

    if (unify_count_max != 0 && ++unify_count > unify_count_max)
      throw std::runtime_error("Too many calls to unify.");

    // Optimization:
    if (x0->empty() && y0->empty())
      return I;

    // If one of x0 and y0 is empty, unification is still possible, as
    // a formula sequence variable can unify with an empty formula, and an
    // inference can unify with one of its premises.


    ref<formula> x, y;
    unify_environment tx, ty;

    // If arguments are reversed, change them back, so that 'unify'
    // here always gets them in reduction (original, unreversed) order.
    // Subsequent calls to 'unify' should use directions 'reduction' and 'deduction',
    // not dr and !dr.
    if (dr == reduction) {
      x = x0; tx = tx0; y = y0; ty = ty0;
    }
    else {
      x = y0; tx = ty0; y = x0; ty = tx0;
    }


    // This sequence of conditionals serve to reduce meta objects and objects
    // that require a call in both 'unify' arguments in a specific order.


    // Reduction order of unify(𝑮, 𝑭), 𝑮 goal, 𝑭 fact::
    // • Reduce 𝑮 meta containers (statements, databases) and formula sequences,
    // including inference heads, down to a formula.
    // The goal is then of the form 𝜞 ⊢ 𝑨, or 𝑨, where 𝑨 is a single formula, and 𝜞
    // a formula sequence.
    // • Reduce 𝜞 ⊢ 𝑨, producing alternatives for 𝜞 used as premises for 𝑨, that is u(𝑨, 𝜞),
    // and calls from inference::unify not call unify with a goal inference to avoid infinite recursion.
    // This is necessary to make sure that the all premises alternatives are combined with the
    // alternatives from the facts.
    // • Reduce 𝑭 meta containers (statements, databases) and formula sequences.
    // The fact is then of the form 𝜟 ⊢ 𝑩, or 𝑩, where 𝑩 is a single formula, and 𝜟
    // a formula sequence.
    // • Reduce 𝜟 ⊢ 𝑩, that is u(𝑮, 𝜟 ⊢ 𝑩).


    if (x->meta_container_and_mode(tx.target_))
      return x->unify(tx, y, ty, dbp, lv, sl, reduction);

    if (y->meta_container_and_mode(ty.target_))
      return y->unify(ty, x, tx, dbp, lv, sl, deduction);

  {
    alternatives as;
#if 1
    // Expand premises if not done so, and y does not contain a premise,
    // the latter to avoid proof redundancy.
    // To avoid proof redundancy in the case of a premise is explicitly mentioned
    // in the proof, expanded_premise_ is always marked expanded
    // even if not expanded in this clause, as when y->expand_premise(lv) is false,
    // it will be expanded later by an explicitly mentioned premise.
    //
    // Note: Currently, if there is an explicitly mentioned premise of not belonging
    // to this statement, the premises of the local statement will not be expanded.

#if NEW_INFERENCE_UNIFY_BODY
    if (expand_implicit_premise && x->unexpanded_premise(tx))
#else
    if (x->unexpanded_premise(tx))
#endif
    {

      tx.expanded_premise_ = true;

      if (y->expand_premise(lv)) {
        unify_environment tx1 = tx;

        metalevel_t xm = x->metalevel();

        // A higher inference metalevel of x raises the x environment metalevel:
        if (xm > tx.metalevel_)
          tx1.metalevel_ = xm;

        // Here, the head determines the direction: deduction, since x->head() is the second argument.
        // Also, x is an inference, by the condition unexpanded_premise above.
        alternatives bs = ref<premise>(make, x)->unify(tx1, x->head(), tx1, dbp, lv, sl, deduction);

        auto xp = ref_cast<inference*>(x); // Always != nullptr, since unexpanded_premise true.

        as = bs.add_premise(x->body(), xm, xp->varied_, xp->varied_in_reduction_);
      }
    }

#if NEW_INFERENCE_UNIFY_BODY
    if (y->unexpanded_premise(ty) && x->expand_premise(lv))
      ;
#else
    if (y->unexpanded_premise(ty) && x->expand_premise(lv))
      ;
#endif

#endif

    if (x->meta_container_or_mode(tx.target_))
      return x->unify(tx, y, ty, dbp, lv, sl, reduction);

    if (y->meta_container_or_mode(ty.target_)) {
      alternatives bs = y->unify(ty, x, tx, dbp, lv, sl, deduction);
      as.append(bs);
      return as;
    }

    if (x->inference_mode()) {
      alternatives bs = x->unify(tx, y, ty, dbp, lv, sl, reduction);
      as.append(bs);
      return as;
    }

    if (y->inference_mode()) {
      alternatives bs = y->unify(ty, x, tx, dbp, lv, sl, deduction);
      as.append(bs);
      return as;
    }
  }


    alternatives as, bs;

    // Polymorphic unify call in first variable x; required calls in y covered below.
    as = x->unify(tx, y, ty, dbp, lv, sl, reduction);

    // Expands definitions in both arguments here, which is a reduction call, i.e., arguments
    // in original order, so there should be no expansion in unify calls with arguments in deduction.
    // After expansion, abbreviation::unify calls this function, so there should be no immediate expansion
    // here, as it sets ex = no_expand, but there should be expansion on subsequent, deeper unify calls.
    if (ex == expand && dbp != 0 && dbp->has_definition(lv)) {
      as.append(dbp->unify(x, tx, y, ty, dbp, lv, sl, reduction));
      as.append(dbp->unify(y, ty, x, tx, dbp, lv, sl, deduction));
    }


    variable* vp1 = ref_cast<variable*>(x);
    variable* vp2 = ref_cast<variable*>(y);

    // If (vp1 != 0) then variable::unify has already been called above.
    if (vp1 == 0 && vp2 != 0) {
      bs = vp2->unify(ty, x, tx, dbp, lv, sl, deduction);
      as.append(bs);
    }

#if NEW_SUBSTITUTION_FORMULA_UNIFY
    substitution_formula* sfp1 = ref_cast<substitution_formula*>(x);
    substitution_formula* sfp2 = ref_cast<substitution_formula*>(y);

    // Must always have a substitution_formula::unify polymorphic call in y:
    if (sfp1 == nullptr && sfp2 != nullptr) {
      bs = sfp2->unify(ty, x, tx, dbp, lv, sl, deduction);
      as.append(bs);
    }
#else
    substitution_formula* sfp2 = ref_cast<substitution_formula*>(y);

    // Must always have a substitution_formula::unify polymorphic call in y:
    if (sfp2 != 0) {
      bs = sfp2->unify(ty, x, tx, dbp, lv, sl, deduction);
      as.append(bs);
    }
#endif
    function_application* fap1 = ref_cast<function_application*>(x);
    function_application* fap2 = ref_cast<function_application*>(y);

    // If fap1 != nullptr then function_application::unify has already been called above.
    if (fap1 == nullptr && fap2 != nullptr) {
      bs = fap2->unify(ty, x, tx, dbp, lv, sl, deduction);
      as.append(bs);
    }

    return as;
  }


  alternatives unify(const ref<formula>& x, unify_environment tx, const std::list<ref<formula>>& ys, unify_environment ty, database* dbp, level lv, degree_pool& sl, direction dr) {

    alternatives as;
    bool it0 = true;

    for (auto& i: ys) {
      if (it0) {
        as = mli::unify(x, tx, i, ty, nullptr, lv, sl, dr);
        it0 = false;
      }
      else
        as = as.unify(x, tx, i, ty, nullptr, lv, sl, dr);

      if (as.empty())
        return O;
    }

    return as;
  }


  split_formula split(const ref<formula>& f, unify_environment tf,
      const ref<variable>& x, const ref<formula>& t, unify_environment tt, database* dbp, level lv, degree_pool& sl, direction dr) {
    return f->split(tf, x, t, tt, dbp, lv, sl, dr);
  }


  // Implementation of class statement.

  alternatives statement::unify(unify_environment tx, const ref<formula>& y, unify_environment ty, database* dbp, level lv, degree_pool& sl, direction dr) const {
#if NEW_PROVED
    // A formula can be provable, say an inference from its premises, and then
    // the statement should not be tried.
    if (ty.target_ == goal && y->provable())
      return I;
#endif

    alternatives as = mli::unify(statement_, tx, y, ty, dbp, lv, sl, dr);

    // Add a label for the write out of the proof in the case of a fact:
    // Only facts used are recorded in the proof.
    if (tx.target_ == fact)
      return as.label(this, lv);
    else
      return as;
  }


  alternatives statement::unify(const ref<formula>& x, unify_environment tx, const ref<formula>& y, unify_environment ty, database* dbp, level lv, degree_pool& sl, direction dr) const {
    // Also add a label for the write out of the proof:
    return statement_->unify(x, tx, y, ty, dbp, lv, sl, dr).label(this, lv);
  }


  ref<formula> statement::rename(level lv, degree sl) const {
    statement* rp = this->new_p();
    ref<formula> rt(rp);
    rp->statement_ = statement_->rename(lv, sl);
    return rt;
  }


  ref<formula> statement::add_exception_set(variable_map& vm) const {
    ref<statement> rt(make, *this);
    rt->statement_ = statement_->add_exception_set(vm);
    return rt;
  }


  ref<formula> statement::substitute(const ref<substitution>& s, substitute_environment vt) const {
    statement* rp = this->new_p();
    ref<formula> rt(rp);
    rp->statement_ = statement_->substitute(s, vt);
    return rt;
  }


  void statement::set_bind(bind& b, name_variable_table& vs) {
    statement_->set_bind(b, vs);
  }



  // Implementation of class variable.

  std::string variable::type_name(type t) {
    std::string s;

    switch (t) {
      case none_:           s += "none";  break;
#if USE_VARIABLE_META
      case metaformula_:    s += "metaformula";  break;
      case metapredicate_:  s += "metapredicate";  break;
#endif
      case formula_sequence_:  s += "formula sequence";  break;
      case formula_:        s += "formula";  break;
      case predicate_:      s += "predicate variable";  break;
      case atom_:           s += "atom";  break;
      case function_:       s += "function";  break;
      case object_:         s += "object";  break;
      default:              s += "other";  break;
    }

    return s;
  }


  /* Indicates whether (writing A ≔ *this) explicit substitutions A[v ↦ t], where v is limited,
     cannot immediately be simplified to A, i.e., return value is true if and only if
     A may after substitution contain the variable v. For a substitution s of A[v ↦ t],
     if s(A).may_contain(s(v)) is true, the substitution result is s(A)[s(v) ↦ s(t)]; otherwise
     s(A) suffices, as s(v) is not contained in s(A) or any future substitutions of it.
     If A and v have the same type: if A is ordinary, as v is limited, return true, if
     A is limited, return false.
     It the types of A and v differ
         A                   may after substitution contain:
     metaformula_:           metapredicate_, formula_ & what formula_ may contain.
     formula_:               predicate_, atom_ & what term_ may contain.
     atom_:                  no variables.
     term_:                  function_, object_.
     metapredicate_, predicate_, function_:
                             no variables (can only be substituted to variables
                             of the same type).
     constant_:              no variables.
     object_:                no variables.
  */
  bool variable::may_contain(const ref<variable>& v) const {
    variable* vp = ref_cast<variable*>(v);
    if (vp == 0)  return false;
    if (type_ == none_ || vp->type_ == none_)  return false;
    type vt = vp->type_;;
    switch (type_) {
#if USE_VARIABLE_META
      case metapredicate_:
#endif
      case predicate_:
      case function_:
        return false;

      // Note: No break below!
#if USE_VARIABLE_META
      case metaformula_:
        if (vt == formula_ || vt == predicate_ || vt == atom_)  return true;
#endif
      case formula_:
        if (vt == object_ || vt == function_)  return true;
        return false;

      default:

#if 1
        // Only make exception currently for v an object variable:
        if (vt != object_) return false;

        if (type_ == object_)  return false;
        return true;
#else
        if (type_ == object_)  return false;
        return (vt == object_);
#endif
    }
  }


  // Cases of variable of type x & variable of type y it specializes,
  // via substitution (i.e. [x.y] is legal), to:
  //
  // To be replaced by a metalevel_ value:
  // metaformula_: metaformula_, formula_, predicate_, atom_.
  // metapredicate_: metapredicate_.
  //
  // Universal metaobject; metalevel defined by member with highest metalevel:
  // formula_sequence_: formula_sequence_, formula_, predicate_, atom_.
  //
  // Logic formulas, that is, having logic value:
  // formula_: formula_, predicate_, atom_.
  // predicate_: predicate_
  // atom_: atom_
  //
  // Objects, that is, relations expressed through logic formulas, not having it themselves:
  // object_: object_
  // function_: function_
  bool variable::is_specializable_to(type x, type y) {
    if (x == y)
      return true;

    switch (x) {
#if USE_VARIABLE_META
      case metaformula_:    return y == metaformula_ || y == formula_ || y == predicate_ || y == atom_;
      case metapredicate_:  return y == metapredicate_;
#endif
      // Universal metaobject; metalevel defined by member with highest metalevel.
      case formula_sequence_:  return y == formula_sequence_ || y == formula_ || y == predicate_ || y == atom_;

      // Logic formulas, that is, having logic value.
      case formula_:        return y == formula_ || y == predicate_ || y == atom_;
      case predicate_:      return y == predicate_;
      case atom_:           return y == atom_;

      // Objects, that is, relations expressed through logic formulas, not having it themselves.
      case object_:         return y == object_ || y == function_;
      case function_:       return y == function_;

      default:
        return false;
    }
  }


  bool variable::is_object() const {
    return type_ == object_;
  }
#if USE_VARIABLE_META
  bool variable::is_metaformula() const {
    return type_ == metaformula_;
  }
#endif
  bool variable::is_formula() const {
    return type_ == formula_ || type_ == predicate_ || type_ == atom_;
  }


  bool variable::get_depth() const { return depth_; }


  template<class A>
  inline A& log_unify(A& x) {
    if (trace_value & trace_unify) {
      std::lock_guard<std::recursive_mutex> guard(write_mutex);
      std::clog << x << std::endl;
    }

    return x;
  }


  template<class A>
  inline const A& log_unify(const A& x) {
    if (trace_value & trace_unify) {
      std::lock_guard<std::recursive_mutex> guard(write_mutex);
      std::clog << x << std::endl;
    }

    return x;
  }


  alternatives variable::unify(unify_environment tt, const ref<formula>& f, unify_environment tf, database* dbp, level lv, degree_pool& sl, direction dr) const {
    if (trace_value & trace_unify) {
      std::lock_guard<std::recursive_mutex> guard(write_mutex);
      std::clog << "variable::unify("
        << *this << ", " << f << ")" << std::endl;
    }


    if (type_ == formula_sequence_) {
      variable* vp = ref_cast<variable*>(f);

      if (vp != nullptr && vp->type_ == formula_sequence_) {
        if (*this == *vp)
          return I;

        if (!is_unspecializable())
          return ref<variable_substitution>(make, this, f);

        if (!vp->is_unspecializable())
          return ref<variable_substitution>(make, vp, this);

        return O;
      }

      if (vp == 0 || vp->type_ != formula_sequence_) {
        if (is_limited() || is_unspecializable())
          return O;

        return ref<variable_substitution>(make, this, f);
      }


      formula_type ft = f->get_formula_type();

      // formula_sequence_ only unifies with a formula sequence or an object logical statement:

      auto sp = ref_cast<formula_sequence*>(f);

      if ((sp != nullptr) || ft == object_formula_type_ || ft == no_formula_type_)
        return ref<variable_substitution>(make, this, f);
      else {
        if (trace_value & trace_unify) {
          std::lock_guard<std::recursive_mutex> guard(write_mutex);
          std::clog << "type mismatch " << std::flush;
        }
        return O;
      }
    }


    variable* vp = ref_cast<variable*>(f);

    if (vp == 0) {
      // Case: f is not a variable. Cases of *this variable type & conditions:
      //   type_                                   formula_type(f)
      //   metaformula_, metapredicate_            metaformula_type_
      //   formula_sequence_                       metaformula_type_, object_formula_type_
      //   formula_, predicate_, atom_             object_formula_type_
      //   (deprecated term_) object_, function_             term_type_
      // formula_sequence_ is a metaformula_, but a singleton formula_
      // of object_formula_type_ is here implicitly converted to a formula_sequence_.
      //
      // *this must be specializable and one must have occurs_in(f) == false.

      // Cases not unifying with formulas in general:

      // Limited variables only unify with a term through a rule.
      if (is_limited())
        return O;

      // A variable that is unspecializable only unifies with another variable at
      // least as general.
      if (is_unspecializable())
        return O;

      formula_type ft = f->get_formula_type();

      // Type check cuts down alternatives in unify(A[x ↦ t], B):
      if (ft != get_formula_type()) {
        if (trace_value & trace_unify) {
          std::lock_guard<std::recursive_mutex> guard(write_mutex);
          std::clog << "type mismatch " << std::flush;
        }

        return O;
      }


      kleenean mb = occurs_in(f);

      // Occurs check: a variable is not allowed to unify with a term that
      // contains a free occurrence of it.
      if (mb == true)
        return O;

      // Check that f is free for x ≔ *this in A, the current formula, that is,
      // no free occurrence of f can become bound by a variable currently in scope.
      // The bound variables of the binders that x is in scope of may appear in f here,
      // which is prohibited for unification, as they have a free occurrence in f and
      // become bound. Thus a check that f does not contain any of those.
      std::set<ref<variable>> s; // Free variables of f.

      // Find free variable occurrences in f; which are the variables that might
      // become bound by a substitution at x in *this:
      bool more = f->contains(s, occurrence::free);
      alternatives bs(ref<variable_substitution>(make, this, f));

      // When undefined, should return special occurrence::frees_substitution requiring variables
      // to not be free:
      if (mb == undefined) {
        ref<variable> v(this);
        ref<formula> not_free = ref<free_in_object>(make, v, f, false);

        return bs.add_goal(not_free);
      }

      return bs;
    }


    // Case: f is a variable (vp != 0).


    // Equal variables unify. Can assume they are unequal henceforth.
    if (*this == *vp)
      return I;


    // Variables only unify by congruence if the binding depth agree relative
    // their respective bound variable lookup tables.
    size_type to = get_depth(tt.table_);
    size_type vo = vp->get_depth(tf.table_);

    if (to != vo)
      return O;


    // Now the variable occurrences are both free or both bound.
    // If one variable is unspecializable, the return of the variable
    // substitution must be unspecializable too.

    // If types are different, for unification to succeed, one type must be able to
    // specialize to the other, and the more general variable must be specializable.
    // It can then be mapped to the less general variable, which must be the
    // unspecializable variable in case one of the two variables is unspecializable.
    // If this not the case, unification is not possible.

    // The two variables are now unequal.


    // If both variables are limited and exactly one is a premise,
    // it can be mapped to the other and the substitution is marked a varied.
    // For a free occurrence 𝑥, the substitution rule is 𝑨 ⊢⁽𝑥⁾ 𝑨[𝑥 ⤇ 𝑦].
    // For a bound occurrence 𝑥, congruence 𝑨 ⊢ 𝑨[𝑥 ↦ 𝑦], for example ∀𝑥: 𝑃(𝑥) ⊢ ∀𝑦: 𝑃(𝑦),
    // which does not involve a variation of the variable 𝑥, as the occurrence is not free.
    if (is_limited() && vp->is_limited()) {
#if NEW_INFERENCE_UNIFY
      // Currently, tt and tf are inference body at the same time.
      if (tt.is_inference_body_ && tf.is_inference_body_) {
        // Check that no variable varied in the fact is dropped in the goal:
        if (tt.target_ == goal) {
#if 1
          if (tf.varied_[tf.conclusion_index_][tf.premise_index_].contains(vp)
            && !tt.varied_[tt.conclusion_index_][tt.premise_index_].contains(this))
              return O;
#endif
        }
        else {
          if (tt.varied_[tt.conclusion_index_][tt.premise_index_].contains(this)
            && !tf.varied_[tf.conclusion_index_][tf.premise_index_].contains(vp))
              return O;
        }
      }
#endif

      if (tt.is_premise_ && !tf.is_premise_
        && tt.premise_variables_.contains(this))
        // A premise-to-conclusion substitution is varied if the premise variable is a free occurrence and not equivalent to the conclusion variable.
        return ref<variable_substitution>(make, this, vp, tt.premise_index_, tt.conclusion_index_, to == 0 && !equivalent(*this, *vp));


      if (!tt.is_premise_ && tf.is_premise_
        && tf.premise_variables_.contains(vp))
        // A premise-to-conclusion substitution is varied if the premise variable is a free occurrence and not equivalent to the conclusion variable.
        return ref<variable_substitution>(make, vp, this, tf.premise_index_, tt.conclusion_index_,
          vo == 0 && !equivalent(*this, *vp));


#if 1
      // Bound limited variables unify by congruence, even if both are unspecializable.
      //
      // By the above, the variables are both conclusions or both premises,
      // so congruence occurs, when binding depths are equal (checked above) and > 0.
      if (to > 0) {
        bool tu = is_unspecializable();
        bool vu = vp->is_unspecializable();

        if (tu && vu) {
          if (tt.target_ == fact)
            return ref<variable_substitution>(make, this, vp);
          else
            return ref<variable_substitution>(make, vp, this);
        }

        if (vu)
          return ref<variable_substitution>(make, this, vp);

        return ref<variable_substitution>(make, vp, this);
      }
#endif

      // Fall through here, to cover other cases in the subsequent code.
    }


    bool tu = is_unspecializable();
    bool vu = vp->is_unspecializable();

    // Unequal unspecialized variables do not unify:
    if (tu && vu)
      return O;

    if (tu) {
      // OBJECT_TERM
      // A limited variable can only specialize to a limited variable:
      if (vp->is_limited() && !is_limited())
        return O;

#define NEW_EXCLUDED 1
#define USE_EXCLUDED 0

      if (is_specializable_to(vp->type_, type_)) {

        // Check that the bound variables in scope that are excluded in the fact
        // are not dropped in the goal. These fact excluded variables have been
        // recomputed via the binder unification substitution to goal excluded variables,
        // so it suffices to check that they are in the goal as well.
        for (auto& i: vp->excluded_) {
          if (!tt.table_->contains(i))
            continue;

          if (!excluded_.contains(i))
            return O;
        }

        ref<variable> r(make, *this);
        r->excluded_from_ = vp->excluded_;

        return ref<variable_substitution>(make, vp, r);
      }
      else
        return O;
    }

    // OBJECT_TERM
    if (vu) {
      // A limited variable can only specialize to a limited variable:
      if (is_limited() && !vp->is_limited())
        return O;

      if (is_specializable_to(type_, vp->type_)) {

        // Check that the bound variables in scope that are excluded in the fact
        // are not dropped in the goal. These fact excluded variables have been
        // recomputed via the binder unification substitution to goal excluded variables,
        // so it suffices to check that they are in the goal as well.
        for (auto& i: excluded_) {
          if (!tf.table_->contains(i))
            continue;

          if (!vp->excluded_.contains(i))
            return O;
        }

        ref<variable> r(make, *vp);
        r->excluded_from_ = excluded_;

        return ref<variable_substitution>(make, this, r);
      }
      else
        return O;
    }

    // Both *this and vp are specializable. If one is limited, and the other not,
    // it must be the return.

#if USE_EXCLUDED
    if (vp->type_ == type_ && vp->is_limited() && is_limited()) {
      // Case both are limited, they must be of the same type, and the exception set
      // determines which variable should be sent to which.
      if (std::includes(vp->excluded_.begin(), vp->excluded_.end(),
             excluded_.begin(), excluded_.end()))
        return ref<variable_substitution>(make, this, vp);

      if (std::includes(excluded_.begin(), excluded_.end(),
             vp->excluded_.begin(), vp->excluded_.end()))
        return ref<variable_substitution>(make, vp, this);

      return O;
    }

    // Case one is not limited
    if (is_specializable_to(vp->type_, type_) && !vp->is_limited()
      && std::includes(excluded_.begin(), excluded_.end(),
             vp->excluded_.begin(), vp->excluded_.end()))
      return ref<variable_substitution>(make, vp, this);

    if (is_specializable_to(type_, vp->type_) && !is_limited()
      && std::includes(vp->excluded_.begin(), vp->excluded_.end(),
             excluded_.begin(), excluded_.end()))
      return ref<variable_substitution>(make, this, vp);
#else
    if (is_specializable_to(vp->type_, type_) && !(vp->is_limited() && !is_limited()))
      return ref<variable_substitution>(make, vp, this);

    if (is_specializable_to(type_, vp->type_) && !(is_limited() && !vp->is_limited()))
      return ref<variable_substitution>(make, this, vp);
#endif

    return O;
  }


  kleenean variable::occurs_in(const ref<formula>& f) const {
    return f->has(this, occurrence::free);
  }


  kleenean variable::has(const ref<variable>& v, occurrence oc) const {
    switch (oc) {
      case occurrence::any: default:
      case occurrence::declared:
      case occurrence::free:
        // True if *v is a free occurrence in *this, that is *this == *v, undefined if
        // for some substitution s, v is a free occurrence in s(*this), otherwise false.
        if (*this == *v) return true;
        if (may_contain(v)) return undefined;
        return false;

      case occurrence::free_not_limited:
        return (*this == *v) && !is_limited();

      case occurrence::object:
        return (is_object() && (*this == *v));

      case occurrence::not_object:
        return (!is_object() && (*this == *v));

      case occurrence::limited:
        return (is_limited() && (*this == *v));

      case occurrence::not_limited:
        return (!is_limited() && (*this == *v));

      case occurrence::formula_sequence:
        return (type_ == formula_sequence_) && (*this == *v);

      case occurrence::unspecialized:
        return (*this == *v) && unspecializable_;

      case occurrence::quantified:
      case occurrence::bound:
        // The bound cccurances are handled by bound_formula::has().
        return false;
    }
  }


  void variable::contains(std::set<ref<variable>>& s, std::set<ref<variable>>& bs, bool& more, occurrence oc) const {
    switch (oc) {
      case occurrence::declared:
        if (bind_ > 0)
          return;
        // Fall through here:

#if 1 // debug.hh
      case occurrence::free:
      case occurrence::free_not_limited:
        // But do not add *this if it is bound:
        if (!bs.contains(this)) {
          s.insert(this);  // The occurrence of *this is not bound.
          if (!is_limited())
            more = true;
        }
        return;
#else
      case occurrence::free:
      case occurrence::free_not_limited:
        // But do not add *this if it is bound:
        if (bs.find(this) == bs.end()) {
          if (!((oc == occurrence::free_not_limited) && is_limited()))
            s.insert(this);  // The occurrence of *this is not bound.
          if ((type_ == metaformula_) || (type_ == formula_) || (type_ == term_))
            more = true;
        }
        return;
#endif

      case occurrence::object:
        if (is_object())
          s.insert(this);
        return;

      case occurrence::not_object:
        if (!is_object())
          s.insert(this);
        return;


      case occurrence::limited:
        if (is_limited())
          s.insert(this);
        return;

      case occurrence::not_limited:
        if (!is_limited())
          s.insert(this);
        return;

      case occurrence::formula_sequence:
        if (type_ == formula_sequence_) s.insert(this);
        return;

      case occurrence::unspecialized:
        if (unspecializable_)
            s.insert(this);  // The occurrence of *this is not bound.
        return;

      case occurrence::quantified:
      case occurrence::bound:
        // Bound variables are handled by bound_formula::contains:
        return;

      default: // Any occurrence.
        s.insert(this);
    }
  }


  kleenean variable::free_for(const ref<formula>& f, const ref<variable>& x,
    std::set<ref<variable>>& s, std::list<ref<variable>>& bs) const {
    variable* fp = ref_cast<variable*>(f);
    ref<variable> fv(fp);

  #if 1
    // If f has no free variables, then f free for x in *this:
    if (s.empty())
      return true;

    // If the set of free variables of f is non-empty and *this after substitution
    // may contain a bound occurrence (of same type as x) of any of them, then
    // f free for x in *this is undefined:
    bool xb = may_contain(x);
    if (xb)
      return undefined;
  #else
    bool xb = may_contain(x);
    bool fb = fp != 0 && may_contain(fv);
    if (xb || fb) {
      if (xb) {
        // Check degree & depth here:
        variable* xp = ref_cast<variable*>(x);
        if (xp == 0 || level_ != xp->level_) // If levels are distinct, *this cannot
          return false;                    // contain x, and has no substitution point.
      }
      if (fb && level_ != fp->level_) // If levels are distinct, the binders of *this
          return false;             // cannot bind any free variables of f.      
      return undefined;
    }
  #endif
    if (ref<variable>(this) != x)
      return true; // *this is no substitution point.

    std::list<ref<variable>>::reverse_iterator i, i0 = bs.rbegin(), i1 = bs.rend();
    for (i = i0; i != i1; ++i) 
      if (s.find(*i) != s.end()) // Assumes variable comparison not using bind_.
        return false;

    return true;
  }


  void variable::unspecialize(depth x, bool y) {
    if (depth_ == x)  unspecializable_ = y;
  }


  void variable::unspecialize(std::set<ref<variable>>& ps, bool b) {
    if (ps.find(this) != ps.end())
      unspecializable_ = b;
  }


  ref<formula> variable::rename(level lv, degree sl) const {
    if (type_ == none_)
      return ref<variable>();

    // Fixed variables will not be renumbered:
    if (is_unspecializable()) {
#if 0  // debug-mli
        return this;
#else
      if (lv.top != 0)
        return this;
      // Return a copy if lv.top is 0.
      return ref<variable>(make, *this);
#endif
    }

    ref<variable> vp(make, *this);

#if 1 // debug.hh
    // If lv.top is 0, just copy, so that the function can be used to copy
    // the formula without renaming:
    if (lv.top != 0) {
      vp->level_ = lv;
      vp->degree_ = sl;

      // Rename the variables in the exception set. As std::set members cannot
      // be mutated, they must copied and inserted.
      // The exception set variables are limited, and have themselves no exception set.
      vp->excluded_.clear();

      for (auto& i: excluded_)
        vp->excluded_.insert(i->rename(lv, sl));
    }
#else
    vp->level_ = lv;
    vp->degree_ = sl;
#endif

    return vp;
  }


  ref<formula> variable::add_exception_set(variable_map& vm) const {
    // Optimization: limited variabled do not have exception set, and should
    // not be a key in the variable_map.
    //
    // When ordinary variables only allow the substitutions permitted by the
    // object substitution rule 𝑨 ⊢⁽𝒙⁾ 𝑨[𝒙 ⤇ 𝒕], cf. Kleene p. 101, then they
    // should not get an exlusion set. (Term variables admit any substitutions, and
    // must be restricted by metaconditions.)
    if (is_limited())
      return this;

    auto i0 = vm.find(this);

    if (i0 == vm.end())
      return this;

    // Now the *this is in the variable map, and should return a copy
    // with the exception se added:

    ref<variable> vr(make, *this);

    for (auto& i: i0->second)
      vr->excluded_.insert(i->add_exception_set(vm));

    return vr;
  }


  ref<formula> variable::substitute(const ref<substitution>& s, substitute_environment vt) const {
    // The formula sequence variable components are substituted if present.
    // By contrast, the term excluded variables are not subtituted as they
    // can only partially be computed depending on the position in the formula,
    // and the subtitution is instead recorde in the set excluded_from_.

    if (components_.empty())
      return s->substitute_variable(this, vt);

    ref<variable> vr(make, *this);
    vr->components_.clear();

    for (auto& i: components_)
      vr->components_.push_back(i->substitute(s, vt));

    return s->substitute_variable(vr, vt);
  }


  order variable::compare(const unit& y) const {
    auto& yr = dynamic_cast<const variable&>(y);

#if (__cplusplus > 201703L) // C++20

#if 1
    return {depth_ <=> yr.depth_, level_ <=> yr.level_, degree_ <=> yr.degree_,
      bind_ <=> yr.bind_, type_ <=> yr.type_, unspecializable_ <=> yr.unspecializable_,
      name <=> yr.name, is_implicit_ <=> yr.is_implicit_};
#else
    return std::tuple(depth_, level_, degree_, bind_, type_, unspecializable_, name)
       <=> std::tuple(yr.depth_, yr.level_, yr.degree_, yr.bind_, yr.type_, yr.unspecializable_, yr.name);
#endif

#else
    // A total ordering for use with std::set.
    if (depth_ != yr.depth_)
      return order(depth_, yr.depth_);

    order c = level_.compare(yr.level_);
    if (c != equal)
      return c;

    if (degree_ != yr.degree_)
      return order(degree_, yr.degree_);

    if (bind_ != yr.bind_)
      return order(bind_, yr.bind_);

    if (type_ != yr.type_)
      return order(type_, yr.type_);

    if (unspecializable_ != yr.unspecializable_)
      return order(unspecializable_, yr.unspecializable_);

    return sgn(name.compare(yr.name));
#endif
  }


  void variable::write(std::ostream& os, write_style) const {

    // Remove if variable type not written in threads.
    std::lock_guard<std::recursive_mutex> guard(write_mutex);

    if (trace_value & trace_unspecializable)
      if (unspecializable_)
        os << '\'';

    if (trace_value & trace_variable_type)
      switch (type_) {
        case none_:         os << "?";  break;
#if USE_VARIABLE_META
        case metaformula_:  os << "M";  break;
#endif
        case formula_:      os << "F";  break;
        case predicate_:    os << "P";  break;
        case atom_:         os << "A";  break;
        case function_:     os << "F";  break;
        case object_:       os << "o";  break;
        case code_:         os << "C";  break;
        default:            os << "!";  break;
      };

    if (is_limited())
      os << "°";

    if (is_term())
      os << "•";

    os << name;

    if (!excluded_.empty() || !excluded_from_.empty()) {
      os << "ₓ₍";

      if (!excluded_from_.empty()) {
        bool it0 = true;
        for (auto& i: excluded_from_) {
          if (it0) it0 = false;
          else os << " ";
          os << i;
        }

        os << "↦";
      }

      bool it0 = true;
      for (auto& i: excluded_) {
        if (it0) it0 = false;
        else os << " ";
        os << i;
      }
      os << "₎";
    }

    if ((trace_value & trace_substitute) && !components_.empty()) {
      os << "⦅";
      bool it0 = true;
      for (auto& i: components_) {
        if (it0) it0 = false;
        else os << "; ";
        os << i;
      }
      os << "⦆";
    }

    if (index_ != -1)
      os << "₍" << to_index(subscript, index_) << "₎";

    if (trace_value & trace_variable_label) {
      os << to_index(superscript, depth_, hide_zero);

      if (bind_ > 0) {
        if (depth_ == 0)
          os << "⁰";
        os << "⁺" << to_index(superscript, bind_);
      }

      // Only write if at least one level is non-zero; then, if produced by 'unify',
      // the top level is non-zero:
      if (level_.top == 0 && level_.sub == 0 && degree_ == 0)
        return;

      // If any level requires two digits, separate by a plus:
      if (level_.top > 9 || level_.sub > 9 || degree_ > 9) {
        os << to_index(subscript, level_.top)
           << "₊"
           << to_index(subscript, level_.sub);

        // Only write degree if non-zero:
        if (degree_ != 0)
          os << "₊"
             << to_index(subscript, degree_);
      }
      else // All levels are one digit: no separator; write last only if non-zero.
        os << to_index(subscript, level_.top)
           << to_index(subscript, level_.sub)
           << to_index(subscript, degree_, hide_zero);
      }
  }


  order equivalence(const variable& x, const variable& y) {
    return {x.depth_ <=> y.depth_, x.level_ <=> y.level_, x.degree_ <=> y.degree_,
      x.bind_ <=> y.bind_, x.type_ <=> y.type_,
      x.name <=> y.name};
  }

  bool equivalent(const variable& x, const variable& y) {
    return comparison(equal)(equivalence(x, y));
  }

  bool precedes::operator()(ref<variable> x, ref<variable> y) {
    return comparison(less)(equivalence(*x, *y));
  }


  void variable_list::write(std::ostream& os, write_style ws) const {
    std::list<value_type>::const_iterator i, i0 = variables_.begin(), i1 = variables_.end();
    for (i = i0; i != i1; ++i) {
      if (i != i0)  os << ", ";
        i->first->write(os, ws);
    }
  }


  // Unification of sequence objects by their iterators.
  template<class I, class J>
  alternatives unify(I i0, I i1, unify_environment tx, J j0, J j1,
    unify_environment ty, database* dbp, level lv, degree_pool& sl, direction dr) {

    alternatives as; // The return alternatives.

    I i = i0;
    J j = j0;

    // Unify from beginning of list, making sure to substitute
    // found substitutions to latter components:
    for (; i != i1 && j != j1; ++i, ++j) {
      if (i == i0)
        as = unify(*i, tx, *j, ty, dbp, lv, sl, dr);
      else
        as = as.unify(*i, tx, *j, ty, dbp, lv, sl, dr);

      if (as.empty())
        return as;
    }

    // Sequences of unequal length.
    if (i != i1 || j != j1)
      return O;

    return as;
  }


  unify_environment unify_environment::substitute(ref<substitution> s) {
    unify_environment tr = *this;

    return tr;
  }


  alternatives unify(const std::list<ref<formula>>& xs, unify_environment tx,
      const std::list<ref<formula>>& ys, unify_environment ty, database* dbp, level lv, degree_pool& sl, direction dr) {
    if (xs.empty() && ys.empty())  return I;
    if (xs.size() != ys.size())  return O;

    alternatives as; // The return alternatives.

    std::list<ref<formula>>::const_iterator i, i0 = xs.begin(), i1 = xs.end();
    std::list<ref<formula>>::const_iterator j = ys.begin(), j1 = ys.end();

    // Unify from beginning of list, making sure to substitute
    // found substitutions to latter components:
    for (i = i0; i != i1; ++i, ++j) {
      if (i == i0)
        as = unify(*i, tx, *j, ty, dbp, lv, sl, dr);
      else
        as = as.unify(*i, tx, *j, ty, dbp, lv, sl, dr);
      if (as.empty())  return as;
    }

    return as;
  }


  // Implementation of class constant.

  alternatives constant::unify(unify_environment, const ref<formula>& x, unify_environment, database*, level, degree_pool&, direction) const {
    if (trace_value & trace_unify) {
      std::lock_guard<std::recursive_mutex> guard(write_mutex);
      std::clog
       << "constant::unify\n  " << *this << ";\n  " << x << ")"
       << std::endl;
    }

    constant* xp = ref_cast<constant*>(x);
    return (xp != 0) && (*this == *xp)? I : O;
  }


  inline order compare(const constant& x, const constant& y) {
    return sgn(x.name.compare(y.name));
  }


  order constant::compare(const unit& x) const {
    auto& xr = dynamic_cast<const constant&>(x);

    if (type_ != xr.type_)
      return unordered;

    return sgn(name.compare(xr.name));
  }


  void constant::write(std::ostream& os, write_style) const {
    if (trace_value & trace_formula_type)
      switch (type_) {
        case metaformula_type_:     os << "M"; break;
        case object_formula_type_:  os << "F"; break;
        case term_type_:            os << "T"; break;
        default:                    os << "?"; break;
      }
    os << name; 
  }



  // Implementation of class sequence.

  formula_type sequence::get_formula_type() const {
    switch (type_) {
      case logic: return object_formula_type_;
      case tuple: return no_formula_type_;

      case member_list_set:
      case implicit_set:
      case vector:
      case list:
      case bracket:
        return term_type_;
      default:
        return no_formula_type_;
    }
  }


  alternatives sequence::unify(unify_environment tt, const ref<formula>& x, unify_environment tx, database* dbp, level lv, degree_pool& sl, direction dr) const {
    if (trace_value & trace_unify)
      write_unify(std::clog, "sequence::", this, tt, x, tx, dbp, dr) << std::endl;

    // Here, *this is not a meta object, and global unify makes sure that
    // neither is x, so unify indices, with the result the composition.
    sequence* xp = ref_cast<sequence*>(x);
    if (xp == 0)  return O;
    if (type_ != xp->type_)  return O;
    return mli::unify(formulas_, tt, xp->formulas_, tx, dbp, lv, sl, dr);
  }


  struct sequence_construct {
    sequence::type type_;

    sequence_construct(sequence::type t) : type_(t) {}

    ref<formula> operator()() const { return ref<sequence>(make, type_); }

    ref<formula> operator()(const ref<formula>& x) const { return ref<sequence>(make, x, type_); }

    ref<formula> operator()(const ref<formula>& x, const ref<formula>& y) const {
      sequence* yp = ref_cast<sequence*>(y);
      if (yp == 0)  return ref<sequence>(make, x, y, type_);
      std::list<ref<formula>> ls = yp->formulas_;
      ls.push_front(x);
      return ref<sequence>(make, ls, type_);
    }
  };


  split_formula sequence::split(unify_environment tg,
    const ref<variable>& x, const ref<formula>& t, unify_environment tt, database* dbp, level lv, degree_pool& sl, direction dr) const {
    split_formula sf(this);  // Return value.

#define SPLIT_CONTAINER 0

#if SPLIT_CONTAINER
    // If t and *this unify, then *this can be replaced by x:
    if (!as.empty())
      sf.push_back(this, ref<formula>(x), tt.table_->find_local());
#endif

    if (formulas_.empty()) {
      sf.push_back(ref<sequence>(make, type_));
      return sf;
    }

    const ref<formula> f = formulas_.front();
    if (formulas_.size() == 1) {
      sf.append(mli::split(f, tg, sequence_construct(type_), x, t, tt, dbp, lv, sl, dr));
      return sf;
    }

    std::list<ref<formula>> fs = formulas_;
    fs.pop_front();
    ref<formula> g = ref<sequence>(make, fs, type_);
    sf.append(mli::split(f, g, tg, sequence_construct(type_), x, t, tt, dbp, lv, sl, dr));

    return sf;
  }


  kleenean sequence::has(const ref<variable>& v, occurrence oc) const {
    kleenean kr = false;

    for (auto& i: formulas_) {
      kleenean k = i->has(v, oc);
      if (k == true)  return true;
      kr = kr || k;
    }

    return kr;
  }


  void sequence::contains(std::set<ref<variable>>& s, std::set<ref<variable>>& bs, bool& more, occurrence oc) const {
    for (auto& i: formulas_)
      i->contains(s, bs, more, oc);
  }


  kleenean sequence::free_for(const ref<formula>& f, const ref<variable>& x,
    std::set<ref<variable>>& s, std::list<ref<variable>>& bs) const {

    kleenean kr = true;

    for (auto& i: formulas_) {
      kleenean k = i->free_for(f, x, s, bs);
      if (k == false)  return false;
      kr = kr && k;
    }

    return kr;
  }


  void sequence::unspecialize(depth x, bool y) {
    for (auto& i: formulas_)
      i->unspecialize(x, y);
  }


  void sequence::unspecialize(std::set<ref<variable>>& vs, bool b) {
    for (auto& i: formulas_)
      i->unspecialize(vs, b);
  }


  ref<formula> sequence::rename(level lv, degree sl) const {
    ref<sequence> s(make, *this);

    std::transform(formulas_.begin(), formulas_.end(), s->formulas_.begin(),
      [=](const ref<formula>& x) { return x->rename(lv, sl); });

    return s;
  }


  ref<formula> sequence::add_exception_set(variable_map& vm) const {
    ref<sequence> sr(make, *this);

    std::transform(formulas_.begin(), formulas_.end(), sr->formulas_.begin(),
      [&vm](const ref<formula>& x) { return x->add_exception_set(vm); });

    return sr;
  }


  ref<formula> sequence::substitute(const ref<substitution>& s, substitute_environment vt) const {
    ref<sequence> sq(make, *this);

    std::transform(formulas_.begin(), formulas_.end(), sq->formulas_.begin(),
      [&s, vt](const ref<formula>& x) { return x->substitute(s, vt); });

    return sq;
  }


  void sequence::set_bind(bind& b, name_variable_table& vt) {
    for (auto& i: formulas_)
      i->set_bind(b, vt);
  }


  order sequence::compare(const unit& x) const {
    auto& xr = dynamic_cast<const sequence&>(x);
    if (type_ != xr.type_)  return unordered;
    return order(formulas_.begin(), formulas_.end(), xr.formulas_.begin(), xr.formulas_.end());
  }


  precedence_t sequence::precedence() const {
    switch (type_) {
      case logic: return logic_oprec;
      case tuple: return tuple_oprec;

      case member_list_set:
        return member_list_set_oprec;
      case implicit_set:
        return implicit_set_oprec;
      case vector:
        return vector_oprec;
      case list:
        return list_oprec;
      case bracket:
        return bracket_oprec;
      default:
        return precedence_t();
    }
  }


  void sequence::write(std::ostream& os, write_style ws) const {
    switch (type_) {
      case logic: os << "("; break;
      case tuple: os << "("; break;

      case member_list_set: os << "{"; break;
      case implicit_set: break;
      case vector: os << "("; break;
      case list: os << "["; break;
      case bracket: os << "<"; break;
      default: os << "(?"; break;
    }

    auto i0 = formulas_.begin(), i = i0, i1 = formulas_.end(), i_last = i1;
    if (!formulas_.empty())  --i_last;
    for(i = i0; i != i1; ++i) {
      if (i != i0)
      switch (type_) {
        case logic:
        case tuple:

        case member_list_set:
        case vector:
        case list:
        case bracket:
          os << ", "; break;

        case implicit_set:
         os << "|"; break;

        default: os << ",?"; break;
      }

      ref<formula> x = *i;

      argument_position ap;
      if (i == i0)  ap = first;
      else if (i == i_last)  ap = last;
      else ap = middle;

      bool do_bracket = precedence().argument(ap, x->precedence());

      if (do_bracket)  os << "(";
      x->write(os, ws);
      if (do_bracket)  os << ")";
    }

    switch (type_) {
      case logic: os << ")"; break;
      case tuple: os << ")"; break;

      case member_list_set: os << "}"; break;
      case implicit_set: break;
      case vector: os << ")"; break;

      case list: os << "]"; break;
      case bracket: os << ">"; break;
      default: os << "?)"; break;
    }
  }


  // Implementation of class structure.

  void structure::push_back(const ref<formula>& x) {
    sequence* vp = ref_cast<sequence*>(argument);
    if (vp == 0) {
      std::cerr << "structure::push_back: argument not a sequence: " << argument << std::endl;
      return;
    }
    vp->push_back(x);
  }


  alternatives structure::unify(unify_environment tt, const ref<formula>& x, unify_environment tx, database* dbp, level lv, degree_pool& sl, direction dr) const {
    if (trace_value & trace_unify) {
      std::lock_guard<std::recursive_mutex> guard(write_mutex);
      std::clog
       << "structure::unify(\n  " << *this << ";\n  " << x << ")" << std::endl;
    }

    structure* sp = ref_cast<structure*>(x);

    // Structures of different metalevel do not unify:
    if (sp == 0 || metalevel_ != sp->metalevel_)
      return O;

    alternatives as = mli::unify(atom, tt, sp->atom, tx, dbp, lv, sl, dr);
    return as.unify(argument, tt, sp->argument, tx, dbp, lv, sl, dr);
  }


  struct structure_construct {
    precedence_t precedence_;
    structure::type type_;
    structure::style style_;
    metalevel_t metalevel_;

    structure_construct(structure::type t, structure::style s, precedence_t p, metalevel_t ml)
     : type_(t), style_(s), precedence_(p), metalevel_(ml) {}

    ref<formula> operator()(const ref<formula>& x, const ref<formula>& y) const {
      return ref<structure>(make, x, y, type_, metalevel_, style_, precedence_);
    }
  };


  split_formula structure::split(unify_environment tg,
    const ref<variable>& x, const ref<formula>& t, unify_environment tt, database* dbp, level lv, degree_pool& sl, direction dr) const {
    split_formula sf(this);  // Return value.
    // If t and *this unify, then *this can be replaced by x:
    alternatives as = mli::unify(t, tt, this, tg, dbp, lv, sl, dr); // Direction correct?

    if (!as.empty())
      sf.push_back(this, ref<formula>(x), tt.table_->find_local());

    sf.append(mli::split(atom, argument, tg, structure_construct(type_, style_, precedence_, metalevel_), x, t, tt, dbp, lv, sl, dr));
    return sf;
  }


  kleenean structure::has(const ref<variable>& v, occurrence oc) const {
    kleenean k1 = atom->has(v, oc);
    if (k1 == true)  return true;
    kleenean k2 = argument->has(v, oc);
    return k1 || k2;
  }


  void structure::contains(std::set<ref<variable>>& s, std::set<ref<variable>>& bs, bool& more, occurrence oc) const {
    atom->contains(s, bs, more, oc);
    argument->contains(s, bs, more, oc);
  }


  kleenean structure::free_for(const ref<formula>& f, const ref<variable>& x,
    std::set<ref<variable>>& s, std::list<ref<variable>>& bs) const {
    kleenean k1 = atom->free_for(f, x, s, bs);
    if (k1 == false)  return false;
    kleenean k2 = argument->free_for(f, x, s, bs);
    return k1 && k2;
  }


  void structure::unspecialize(depth x, bool y) {
    atom->unspecialize(x, y);
    argument->unspecialize(x, y);
  }


  void structure::unspecialize(std::set<ref<variable>>& vs, bool b) {
    atom->unspecialize(vs, b);
    argument->unspecialize(vs, b);
  }


  ref<formula> structure::rename(level lv, degree sl) const {
    return ref<structure>(make,
      atom->rename(lv, sl),
      argument->rename(lv, sl),
      type_, metalevel_, style_, precedence_);
  }


  ref<formula> structure::add_exception_set(variable_map& vm) const {
    return ref<structure>(make,
      atom->add_exception_set(vm),
      argument->add_exception_set(vm),
      type_, metalevel_, style_, precedence_);
  }


  ref<formula> structure::substitute(const ref<substitution>& s, substitute_environment vt) const {
    return ref<structure>(make,
      atom->substitute(s, vt),
      argument->substitute(s, vt), type_, metalevel_, style_, precedence_);
  }


  void structure::set_bind(bind& b, name_variable_table& vt) {
    atom->set_bind(b, vt);
    argument->set_bind(b, vt);
  }


  order structure::compare(const unit& x) const {
    auto& xr = dynamic_cast<const structure&>(x);

#if (__cplusplus > 201703L) // C++20
    order d = metalevel_ <=> xr.metalevel_;
#else
    order d = order(metalevel_, xr.metalevel_);
#endif
    if (d != equal)  return d;

#if (__cplusplus > 201703L) // C++20
    order c = atom <=> xr.atom;
    if (c != equal)  return c;
    return argument <=> xr.argument;
#else
    order c = mli::compare(atom, xr.atom);
    if (c != equal)  return c;
    return mli::compare(argument, xr.argument);
#endif
  }


  void write_structure_type(std::ostream& os, structure::type t) {
    switch (t) {
      case structure::logic:          os << "†"; break;
      case structure::predicate:      os << "π"; break;
      case structure::function:       os << "ƒ"; break;
      default:                        os << "?"; break;
    }
  }


  void structure::write(std::ostream& os, write_style) const {
    std::string ml = to_index(superscript, (size_type)metalevel_, hide_zero);

    if (style_ == infix) {
      sequence& v = ref_cast<sequence&>(argument);

      if (v.formulas_.size() == 2) {
        if (precedence().argument(first, v.formulas_.front()->precedence()))
          os << "(" << v.formulas_.front() << ")";
        else
          os << v.formulas_.front();

        os << " ";

        if (trace_value & trace_structure_type)
          write_structure_type(os, type_);

        os << atom << ml << " ";

        if (precedence().argument(last, v.formulas_.back()->precedence()))
          os << "(" << v.formulas_.back() << ")";
        else
          os << v.formulas_.back();

        return;
      }
    }

    if (style_ == prefix) {
      sequence& v = ref_cast<sequence&>(argument);
      if (v.formulas_.size() == 1) {
        if (trace_value & trace_structure_type)
          write_structure_type(os, type_);
        os << atom << ml;
        if (precedence().argument(last, v.formulas_.front()->precedence()))
          os << "(" << v.formulas_.front() << ")";
        else
          os << v.formulas_.front();
        return;
      }
    }

    if (style_ == postfix) {
      sequence& v = ref_cast<sequence&>(argument);
      if (v.formulas_.size() == 1) {
        if (precedence().argument(first, v.formulas_.front()->precedence()))
          os << "(" << v.formulas_.front() << ")";
        else
          os << v.formulas_.front();
        if (trace_value & trace_structure_type)
          write_structure_type(os, type_);
        os << atom << ml;
        return;
      }
    }

    if (trace_value & trace_structure_type)
      write_structure_type(os, type_);

    // postargument: write argument as is after the atom.
    os << atom << ml << argument; return;
  }


  bound_formula::bound_formula(const variable_list& vs, const ref<formula>& f)
   : formula_(f) {
    push_back(vs);
  }


  bound_formula::bound_formula(const variable_list& vs, const ref<formula>& d, const ref<formula>& f)
   : domain_(d), formula_(f) {
    push_back(vs);
  }


  bound_formula* bound_formula::push_back(const ref<variable>& v, const bound_formula::type& bt) {
    if (variable_->name.empty()) { // *this has no variable yet.
      variable_ = v;
      type_ = bt;
      return this;
    }

    bound_formula* bp = new bound_formula(v, domain_, formula_, bt);
    formula_ = bp;
    return bp; 
  }


  void bound_formula::push_back(const variable_list& vs) {
    bound_formula* bp;
    auto i0 = vs.variables_.begin(), i = i0, i1 = vs.variables_.end();
    for (i = i0; i != i1; ++i)
      if (i == i0)
        bp = push_back(i->first, i->second);
      else
        bp = bp->push_back(i->first, i->second);
  }


  void bound_formula::set(const ref<formula>& t) {
    formula_ = t;
  }


  void bound_formula::set(const bound_formula& q) {
    push_back(q.variable_, q.type_);
    set(q.formula_);
  }


  // Forward declaration.
  alternatives unify_bound1(
      const ref<variable>&, unify_environment, const ref<formula>&,
      const ref<variable>&, unify_environment, const ref<formula>&,
      database*, level, degree_pool&, direction);


  // Unify bound variables: Assumes both x and y are bound.
  alternatives unify_bound(
      const ref<variable>& x, unify_environment tx, const ref<formula>& fx,
      const ref<variable>& y, unify_environment ty, const ref<formula>& fy,
      database* dbp, level lv, degree_pool& sl, direction dr) {

    if (trace_value & trace_unify) {
      std::lock_guard<std::recursive_mutex> guard(write_mutex);
      write_unify(std::clog, "mli::bound_", ref<formula>(x), tx, ref<formula>(y), ty, dbp, dr) << std::endl;
    }

    // Check if x, y are unifiable. If so, add to the unifying substitution free(fx) if x
    // is the mapped variable, or free(fy) if y.


    // For congruence, the variables must have the same binding depth:
    size_type dx = x->get_depth(tx.table_);
    size_type dy = y->get_depth(ty.table_);

    if (dx != dy)
      return O;


    if ((x->is_unspecializable() && !y->is_unspecializable()))
      return unify_bound1(y, ty, fy, x, tx, fx, dbp, lv, sl, !dr);

    return unify_bound1(x, tx, fx, y, ty, fy, dbp, lv, sl, dr);
  }


  // Assumes that if one of x, y is specializable, x is specializable;
  // but else both x, y may be unspecializable.
  alternatives unify_bound1(
      const ref<variable>& x, unify_environment tx, const ref<formula>& fx,
      const ref<variable>& y, unify_environment, const ref<formula>&,
      database*, level, degree_pool&, direction) {

    // Need not check unspecializable condition. If one variable is
    // unspecializable, it will be preferred as the mapped variable, and it is x.

    ref<variable_substitution> vsx(make, x, ref<formula>(y));

    return log_unify(alternatives(ref<substitution>(vsx)));
  }


  // u(𝛽 𝑥 𝐴, 𝛽 𝑦 𝐵) = [𝑥 ↦ 𝑦]•[𝐵↦𝐴[𝑥 ↦ 𝑦]] ⊢
  //  𝑦 free for 𝑥 in 𝐴; 𝑦 not free in 𝐴; 𝑥 free for 𝑦 in 𝐵, 𝑥 not free in 𝐵.
  alternatives bound_formula::unify(unify_environment tt, const ref<formula>& x, unify_environment tx, database* dbp, level lv, degree_pool& sl, direction dr) const {
    if (trace_value & trace_unify) {
      std::lock_guard<std::recursive_mutex> guard(write_mutex);
      std::clog << "bound_formula::unify(\n  " << *this << ";\n  " << x << ")\n" << std::flush;
    }

    // Solutions:
    // Define the metapredicate u(f, g) ≔ set of unifying substitutions of f, g. Then:
    // For 𝑥, 𝑦 object variables, with x, y possibly swapped:
    //   u(𝛽𝑥 𝐴, 𝛽𝑦 𝐵) = [𝑥 ↦ 𝑦]•u(𝐴[𝑥 ↦ 𝑦], 𝐵)
    //     ⊢ 𝑦 free for 𝑥 in 𝐴; 𝑦 not free in 𝐴; 𝑥 free for 𝑦 in 𝐵, 𝑥 not free in 𝐵.
    // Special cases:
    //   𝐴, 𝐵 variables, u(𝐴[𝑥↦𝑦], 𝐵) = [𝑥 ↦ 𝑦]•[𝐵 ↦ 𝐴[𝑥 ↦ 𝑦]].
    //   x, y object, x = y resp. x ≡ y: u(𝛽𝑥 𝐴, 𝛽𝑦 𝐵) = u(𝐴, 𝐵).
    //

    /*
        u(all x A, all y B) == [y\x][B\A].
        x == y ⊢ u(all x A, all y B) == [B\A].
        x =/= y, y not free in A, x not free in B ⊢ u(all x A, all y B) == [B\A].
    */
    bound_formula* xp = ref_cast<bound_formula*>(x);
    if (xp == 0 || type_ != xp->type_)
      return O;

    // Elements popped when the syntactic environment expires:
    push_bound p0(tt);

    tt.table_->insert(variable_);

    push_bound p1(tx);

    tx.table_->insert(xp->variable_);

    alternatives as;

#if 1 // debug.hh
    // u(x, y) * u(A, B):
    alternatives as0 = mli::unify(variable_, tt, xp->variable_, tx, dbp, lv, sl, dr);
    as0 = as0.unify(domain_, tt, xp->domain_, tx, dbp, lv, sl, dr);
    as0 = as0.unify(formula_, tt, xp->formula_, tx, dbp, lv, sl, dr);
    as = as.append(as0);

#else
    // This segment is not in use, probably obsolete:

    // Solutions:
    // If x, y object, x = y resp. x ≡ y:
    //   u(A, B)
    // If x, y object, x ≠ y:
    //   u(x, y) * u(A, B) ⊢ x not free in B, y not free in A.
    // If x object, y metaobject or x metaobject, y object:
    //   u(x, y) * u(A, B) ⊣ x not free in B, y not free in A
    // If x, y metaobject, x ≢ y:
    //   u(A, B) ⊣ x == y
    //   u(x, y) * u(A, B) ⊣ x ≠ y, x not free in B, y not free in A.
    //   u(x, y) * u(A, B) ⊣ x not free in B, y not free in A.

    if (variable_ == xp->variable_) {
      as = mli::unify(domain_, tt, xp->domain_, tx, dbp, lv, sl, dr);
      as = as.unify(formula_, tt, xp->formula_, tx, dbp, lv, sl, dr);
      return as;
    }

    if ((variable_->is_bound() || variable_->is_limited())
      && (xp->variable_->is_bound() || xp->variable_->is_limited())) {
      // u(x, y) * u(A, B):
      alternatives as0 = mli::unify(ref<formula>(variable_), tt, ref<formula>(xp->variable_), tx, dbp, lv, sl, dr);
      as0 = as0.unify(domain_, tt, xp->domain_, tx, dbp, lv, sl, dr);
      as0 = as0.unify(formula_, tt, xp->formula_, tx, dbp, lv, sl, dr);
      as = as.append(as0);
      if (!as.empty())
        return as;
    }

    kleenean free1 = domain_->has(xp->variable_, occurrence::free) || formula_->has(xp->variable_, occurrence::free);
    kleenean free2 = xp->domain_->has(variable_, occurrence::free) || xp->formula_->has(variable_, occurrence::free);
    if (free1 == true || free2 == true)
      return O;

#if 0
    // Any type of variable can now be bound:
    bool to = variable_->is_object();
    bool xo = xp->variable_->is_object();
    if (!(to && xo))
      throw std::runtime_error("In bound_formula, variable not representing object variable.");
#endif

    // Conditions:

    ref<objectidentical> id(make, variable_, xp->variable_, true);
    ref<objectidentical> not_id(make, variable_, xp->variable_, false);

    ref<free_in_object> not_free1(make, xp->variable_, formula_, false);
    ref<free_in_object> not_free2(make, variable_, xp->formula_, false);

    // y not free in A, x not free in B:
    ref<sequence> s1(make, formula_sequence_);

    if (free1 == undefined)
      s1->push_back(not_free1);
    if (free2 == undefined)
      s1->push_back(not_free2);

#if 0
    // x /== y, y not free in A, x not free in B:
    ref<sequence> sp2(make, not_id, formula_sequence_);
    ref<formula> c2 = sp2;
    if (free1 == undefined)
      sp2->push_back(not_free1);
    if (free2 == undefined)
      sp2->push_back(not_free2);
#endif

    if (to && xo) { // Both object variables.
      // Adds the free variables of formulas as not-free-in conditions:
      as = mli::unify_bound(variable_, tt, xp->formula_, xp->variable_, tx, formula_, dbp, lv, sl, dr);
      as = as.unify_binder(formula_, tt, xp->formula_, tx, dbp, lv, sl, dr);
      // Need to add bound variables table here, in +:
      as = as + s1;
    }
    else {
      // u(x, y) * u(A, B):
      alternatives as0 = mli::unify(ref<formula>(variable_), tt, ref<formula>(xp->variable_), tx, dbp, lv, sl, dr);
      as0 = as0.unify(formula_, tt, xp->formula_, tx, dbp, lv, sl, dr);
      as = as.append(as0);

  #if 0
      // One might add conditional solutions here:
      // If x, y metaobject:
      //             u(A, B) ⊣ x == y
      //   u(x, y) • u(A, B) ⊣ x /== y, x not free in B, y not free in A
      alternatives as1 = mli::unify(formula_, tt, xp->formula_, tx, dbp, lv, sl, dr);
      // Need to add bound variables table here, in +:
      as = as.append(as1 + id);
      alternatives as2 = mli::unify_bound(variable_, tt, xp->formula_, xp->variable_, tx, formula_, dbp, lv, sl, dr);
      as2 = as2->unify_binder(formula_, tt, xp->formula_, tx, dbp, lv, sl, dr);
      as = as.append(as1 + c2);
  #endif
    }
#endif // debug.hh

    if (trace_value & trace_unify) {
      std::lock_guard<std::recursive_mutex> guard(write_mutex);
      std::clog << "Result bound_formula::unify(\n  " << *this << ";\n  " << x << "):"
                << as << std::endl;
    }

    return as;
  }


  struct bound_formula_construct {
    ref<variable> variable_;
    bound_formula::type type_;
    bind bind_;

    bound_formula_construct(const ref<variable>& v, bound_formula::type bt, bind b)
     : variable_(v), type_(bt), bind_(b) {}

    ref<formula> operator()(const ref<formula>& d, const ref<formula>& x) const {
      return ref<bound_formula>(make, variable_, d, x, type_, bind_);
    }
  };


  split_formula bound_formula::split(unify_environment tg,
    const ref<variable>& x, const ref<formula>& t, unify_environment tt, database* dbp, level lv, degree_pool& sl, direction dr) const {

    // Elements popped when the syntactic environment expires:
    push_bound p0(tt);

    tt.table_->insert(variable_);

    split_formula sf(this);  // Return value.
    // If t and *this unify, then *this can be replaced by x:
    alternatives as = mli::unify(t, tt, this, tg, dbp, lv, sl, dr);

    if (!as.empty())
      sf.push_back(this, ref<formula>(x), tt.table_->find_local());

    sf.append(
      mli::split(domain_, formula_, tg, bound_formula_construct(variable_, type_, bind_), x, t, tt, dbp, lv, sl, dr));
    return sf;
  }


  kleenean bound_formula::has(const ref<variable>& v, occurrence oc) const {
    switch (oc) {
      case occurrence::declared:
        if (variable_ == v && bind_ == 0)
          return true;
        // Fall through to occurrence::free here:
      case occurrence::free:
      case occurrence::free_not_limited:
        if (variable_ == v)
          return false;

        return domain_->has(v, oc) || formula_->has(v, oc);

      case occurrence::object:
        if (variable_ == v)
          return true;
        return domain_->has(v, oc) || formula_->has(v, oc);

      case occurrence::not_object:
        return domain_->has(v, oc) || formula_->has(v, oc);


      case occurrence::limited:
        // All bound occurrences are limited:
        if (variable_ == v)
          return true;
        return domain_->has(v, oc) || formula_->has(v, oc);

      case occurrence::not_limited:
        return domain_->has(v, oc) || formula_->has(v, oc);


      case occurrence::unspecialized:
        return (variable_ == v && v->unspecializable_);

      // occurrence::quantified is a quantified variable occurrence::bound:
      case occurrence::quantified:
        if (!(type_ == all_ || type_ == exist_))
          return domain_->has(v, oc) || formula_->has(v, oc);
        // Fall through here to occurrence::bound:

      case occurrence::bound: {
        if (variable_ == v) return true;

        bool maybe_undefined = false;
        if (variable_->may_contain(v))
          maybe_undefined = true;

        kleenean kl = domain_->has(v, oc) || formula_->has(v, oc);
        if (!maybe_undefined) return kl;
        if (kl == true) return true;

        return undefined;
      }
   
      case occurrence::any: default:
        if (variable_ == v)  return true;
        return domain_->has(v, oc) || formula_->has(v, oc);
    }
  }


  void bound_formula::contains(std::set<ref<variable>>& s, std::set<ref<variable>>& bs, bool& more, occurrence oc) const {
    bs.insert(variable_);

    switch (oc) {
      case occurrence::declared:
        if (variable_->bind_ == 0)
          s.insert(variable_);
        // Fall through to occurrence::free here:
      case occurrence::free:
      case occurrence::free_not_limited:
        // But do not add variable_ here; it must somehow be excluded:
        domain_->contains(s, bs, more, oc);
        formula_->contains(s, bs, more, oc);
        return;

      case occurrence::object:
        s.insert(variable_);
        domain_->contains(s, bs, more, oc);
        formula_->contains(s, bs, more, oc);
        return;

      case occurrence::not_object:
        domain_->contains(s, bs, more, oc);
        formula_->contains(s, bs, more, oc);
        return;


      case occurrence::limited:
        // All bound occurrences are limited.
        s.insert(variable_);
        domain_->contains(s, bs, more, oc);
        formula_->contains(s, bs, more, oc);
        return;

      case occurrence::not_limited:
        domain_->contains(s, bs, more, oc);
        formula_->contains(s, bs, more, oc);
        return;


      case occurrence::unspecialized:
        if (variable_->unspecializable_)
          s.insert(variable_);
        domain_->contains(s, bs, more, oc);
        formula_->contains(s, bs, more, oc);
        return;

      // occurrence::quantified is a quantified variable occurrence::bound:
      case occurrence::quantified:
        if (!(type_ == all_ || type_ == exist_)) {
          domain_->contains(s, bs, more, oc);
          formula_->contains(s, bs, more, oc);
          return;
        }
        // Fall through here to occurrence::bound:

      case occurrence::bound:
        s.insert(variable_);
        if (variable_->is_limited())
          more = true;
        domain_->contains(s, bs, more, oc);
        formula_->contains(s, bs, more, oc);
        return;

      case occurrence::any: default:
        s.insert(variable_);
        if (variable_->is_limited())
          more = true;
        domain_->contains(s, bs, more, oc);
        formula_->contains(s, bs, more, oc);
        return;
    }
  }


  kleenean bound_formula::free_for(const ref<formula>& f, const ref<variable>& x,
    std::set<ref<variable>>& s, std::list<ref<variable>>& bs) const {
    kleenean mb;
    bs.push_back(variable_);
    mb = domain_->free_for(f, x, s, bs) && formula_->free_for(f, x, s, bs);
    bs.pop_back();
    return mb;
  }


  void bound_formula::unspecialize(depth x, bool y) {
    variable_->unspecialize(x, y);
    domain_->unspecialize(x, y);
    formula_->unspecialize(x, y);
  }


  void bound_formula::unspecialize(std::set<ref<variable>>& vs, bool b) {
    variable_->unspecialize(vs, b);
    domain_->unspecialize(vs, b);
    formula_->unspecialize(vs, b);
  }


  ref<formula> bound_formula::rename(level l, degree sl) const {
    ref<bound_formula> qf(make, *this);
    qf->variable_ = ref<variable>(variable_->rename(l, sl));
    qf->domain_ = domain_->rename(l, sl);
    qf->formula_ = formula_->rename(l, sl);
    return qf;
  }


  ref<formula> bound_formula::add_exception_set(variable_map& vm) const {
    ref<bound_formula> qf(make, *this);
    // The limited qf->variable_ does not have an exception set.
    qf->domain_ = domain_->add_exception_set(vm);
    qf->formula_ = formula_->add_exception_set(vm);
    return qf;
  }


  // Variation that does not create a variable table if not already existing.
  ref<formula> bound_formula::substitute(const ref<substitution>& s, substitute_environment vt) const {
    if (trace_value & trace_substitute) {
      std::lock_guard<std::recursive_mutex> guard(write_mutex);
      std::clog << "Begin bound_formula::substitute\n  "
        << "(" << *this << ")" << s
        << std::endl;
    }

    // Push a level, which pops when the element lg expires:
    level_guard lg(*vt.table_);

    vt.table_->insert(variable_);

    ref<bound_formula> qf(make, *this);

    ref<formula> vr = variable_->substitute(s, vt);
    variable* vp = ref_cast<variable*>(vr);

    // The following works as bound variables are only unified to (bound)
    // variables (i.e., vp == 0 possible only if there is a programming error).

    // Note: function 'substitute' may return a variable with a condition attached, via
    // variable_substitution::substitute_variable.
    if (vp == 0) {
      std::ostringstream ost;

      ost << "Error: bound_formula::substitute: " << *this << "\n"
        << s << "\n" << variable_ << "\n" << vr << std::endl;

      throw std::runtime_error(ost.str());
    }

    qf->variable_ = vp;
    qf->domain_ = domain_->substitute(s, vt);
    qf->formula_ = formula_->substitute(s, vt);

    if (trace_value & trace_substitute) {
      std::lock_guard<std::recursive_mutex> guard(write_mutex);
      std::clog << "bound_formula::substitute\n  "
        << "(" << *this << ")" << s << ":\n    "
        << qf
        << std::endl;
    }

    return qf;
  }


  void variable::set_bind(bind& b, name_variable_table& vt) {
  }


  void bound_formula::set_bind(bind& b, name_variable_table& vt) {
    ++b;        // New binder head gets a new identity.
    bind_ = b;  // Binder number set, even though it may hold a variable without it.

    // Limited variables behave as free variables, even though appearing in a binder.
    // Setting the binder limited causes its bound variable behave this way without
    // the variable itself being so.
    if (variable_->bind_ > 0)
      variable_->bind_ = b;

    vt.push_level(); // New level to the stacked name variable table.
    vt.insert(variable_->name, variable_);

    domain_->set_bind(b, vt);
    formula_->set_bind(b, vt);

    vt.pop_level(); // This binder is finished.
  }


  order bound_formula::compare(const unit& t) const {
    auto& tr = dynamic_cast<const bound_formula&>(t);

#if (__cplusplus > 201703L) // C++20
    order r = variable_ <=> tr.variable_;
    if (r != equal)  return r;

    order d = domain_ <=> tr.domain_;
    if (d != equal)  return d;

    return formula_ <=> tr.formula_;
#else
    order r = mli::compare(variable_, tr.variable_);
    if (r != equal)  return r;

    order d = mli::compare(domain_, tr.domain_);
    if (d != equal)  return d;

    return mli::compare(formula_, tr.formula_);
#endif
  }


  precedence_t bound_formula::precedence() const {
    switch (type_) {
      case none_:
        return precedence_t();
      case all_:
      case exist_:
        if (body_simple())
          return simple_quantizer_oprec; 
        return quantizer_oprec;
      case is_set_:
        return is_set_oprec;
      case set_:
        return member_list_set_oprec;
      case implicit_set:
        return implicit_set_oprec;
      case mapto_:
        return mapto_oprec;
      case other_:
        return precedence_t();
      default:
        return precedence_t();
    }
  }


  void bound_formula::write(std::ostream& os, write_style ws) const {
    write(os, ws, bound_formula::none_);
  }


  void bound_formula::write(std::ostream& os, write_style ws,
      bound_formula::type type_above) const {

    // Remove if bind_ numbers not written in threads.
    std::lock_guard<std::recursive_mutex> guard(write_mutex);

    if (type_ == is_set_) {
      os << "Set";
      if ((trace_value & trace_variable_label) && bind_ != 0)
        os << to_index(superscript, bind_);

      os << "₍";
      variable_->write(os, ws);
      if (!domain_->empty())
        os << " ∈ " << domain_;
      os << "₎ ";
      formula_->write(os, ws);
      return;
    }

    if (type_ == set_) {
      os << "{";
      if ((trace_value & trace_variable_label) && bind_ != 0)
        os << to_index(superscript, bind_);
      variable_->write(os, ws);
      if (!domain_->empty())
        os << " ∈ " << domain_;
      os << "|";
      formula_->write(os, ws);
      os << "}";
      return;
    }

    if (type_above == none_
      || (type_above != type_)) {
      if (type_above != none_)  os << " ";
      switch (type_) {
        case all_: os << "∀"; break;
        case exist_: os << "∃"; break;
        case implicit_set: os << "{"; break;
        default: os << "bind?";
      }

      if ((trace_value & trace_variable_label) && bind_ != 0)
        os << to_index(superscript, bind_);

      if (type_ == implicit_set)
        os << "₍";
      else if (type_ == all_ || type_ == exist_)
        ;
      else
        os << " ";
    }
    else {
      os << ",";

      if ((trace_value & trace_variable_label) && bind_ != 0)
        os << to_index(superscript, bind_);

      os << " ";
    }

    variable_->write(os, ws);

    bound_formula* bp = ref_cast<bound_formula*>(formula_);

    if (type_ == implicit_set) {
      if (bp != 0 && bp->type_ == implicit_set)
        bp->write(os, ws, type_);
      else {
        if (!domain_->empty())
          os << " ∈ " << domain_;
        os << "₎ ";
        formula_->write(os, ws);
      }
      if (type_above == none_)  os << "}";
      return;
    }

    if (body_simple()) {
      if (!domain_->empty())
        os << " ∈ " << domain_ << ":";
      os << " ";
      formula_->write(os, ws);
      return;
    }

    const variable* vp = 0;
    if (bp != 0)
      vp = bp->variable_.data();

    // If at the end of a quantifier sequence ∀… or ∃…, write the domain:
    if (is_quantified() && bp != nullptr && type_ != bp->type_) {
      if (!domain_->empty())
        os << " ∈ " << domain_;
    }

    if (bp == 0 || vp == 0 || !bp->is_quantified()) {
      if (!domain_->empty())
        os << " ∈ " << domain_;

      os << ": ";
    }
    if (precedence().argument(last, formula_->precedence()))
      os << "(";
    if (bp != 0)
      bp->write(os, ws, type_);
    else
      formula_->write(os, ws);
    if (precedence().argument(last, formula_->precedence()))
      os << ")";
  }


  bool bound_formula::body_simple() const {
    variable* vp0 = ref_cast<variable*>(formula_);
    constant* cp = ref_cast<constant*>(formula_);
    structure* sp = ref_cast<structure*>(formula_);
    return (vp0 != 0 || cp != 0
      || (sp != 0 && sp->type_ == structure::predicate));
  }


  formula_type formula_sequence::get_formula_type() const { return metaformula_type_; }


  // 𝜞.add_premise(𝑨, 𝑘):
  // If 𝜞 is not a formula sequence or formula sequence with metalevel(𝜞) < 𝑘 then 𝑨 ⊢^𝑘 𝜞 is possible.
  // Otherwise, writing 𝜞 ≔ {𝜞₀, …}, one must have {𝜞₀.add_premise(𝑨, 𝑘), …}:
  ref<formula> formula_sequence::add_premise(const ref<formula>& x, metalevel_t ml,
      const varied_type& vs, const varied_type& vrs) const {
    if (x->provable())
      return this;

    if (metalevel() < ml)
      return ref<inference>(make, this, x, ml, vs, vrs);

    ref<formula_sequence> mf(make);

    for (auto& i: formulas_)
      mf->push_back(i->add_premise(x, ml, vs, vrs));

    return mf;
  }


  ref<formula> formula_sequence::add_goal(const ref<formula>& x) const {
    // If x is a formula_sequence of metaand type, concatenate, otherwise, append x to *this.

    if (x->provable())
      return this;

    formula_sequence* spx = ref_cast<formula_sequence*>(x);

    // Find which of *this and x that are formula sequences at the proof metalevel:
    if (spx != 0)
      return ref<formula_sequence>(make, *this, *spx);

    return ref<formula_sequence>(make, *this, x);
  }


  metalevel_t formula_sequence::metalevel() const {
    // Sets the formula sequence metalevel to the maximum metalevel of its members.

    metalevel_t ml;

    for (auto& i: formulas_) {
      metalevel_t ml1 = i->metalevel();

      if (ml < ml1)
        ml = ml1;
    }

    return ml;
  }


  bool formula_sequence::is_metasubset(const ref<formula> x) const {
    for (auto& i: formulas_)
      if (!i->is_metasubset(x))
        return false;

      return true;
  }


  alternatives formula_sequence::unify(unify_environment tt, const ref<formula>& x, unify_environment tx, database* dbp, level lv, degree_pool& sl, direction dr) const {
    if (trace_value & trace_unify)
      write_unify(std::clog, "formula_sequence::", this, tt, x, tx, dbp, dr) << std::endl;

    // Expand 𝜞 ⊢ ⦅𝑨₀, …⦆ to ⦅𝜞 ⊢ 𝑨₀; …⦆ both goal and fact.
    if (unexpanded())
      return mli::unify(expand(tt.conclusion_index_), tt, x, tx, dbp, lv, sl, dr);

    if (x->unexpanded())
      return mli::unify(this, tt, x->expand(tx.conclusion_index_), tx, dbp, lv, sl, dr);

    // A metaand (resp. metaor) goal, will behave as such, but a metaand
    // (resp. metaor) fact will behave as the dual metaor (resp. metaand).
    // If there is a mix of an object behaving as a metaand, and the other as a metaor,
    // then the metaand object must be decomposed first; otherwise, for example, the
    // statement A | B ⊢ A | B will not be proved.

    // If both *this and x are formula sequences, then master 'unify' will ensure that
    // *this is the goal and x the fact. Therefore, it suffices to treat the case
    // when they both are when *this is the goal.

    if (tt.target_ == goal) {

      auto vp = ref_cast<variable*>(x);

      if (vp != nullptr && vp->type_ == variable::formula_sequence_)
        return vp->unify(tx, this, tt, dbp, lv, sl, !dr);

      auto xp = ref_cast<formula_sequence*>(x);

#if 0
      if (xp == nullptr) {
        ref<formula_sequence> xs(make, x);
        return this->unify(tt, xs, tx, dbp, lv, sl, dr);
      }
#endif
      // If x is a formula sequence that contains top level formula sequence variables 𝜞, then for each 𝜞
      // there should be exactly one end marker [𝜞 ↦ ⦰] for the whole metaand-metaor
      // reduction, so both formula sequences must be resolved together here, as otherwise, each metaor
      // treated separately will add one end marker, terminating the formula sequence variable reduction
      // too early.
      if (xp != nullptr) {

        alternatives as = I;
        size_type m = 0; // Conclusion index.

        for (auto& i: formulas_) {
          unify_environment tt1 = tt;
          tt1.conclusion_index_ = m;

          alternatives bs;
          size_type n = 0; // Premise index.

          for (auto& j: xp->formulas_) {
            alternatives cs = as.unify(i, tt1, j, tx, dbp, lv, sl, dr);
            bs = bs.append(cs);

            ++n;
          }

          as = bs;

          // Optimization: There will be no alternatives if one is O.
          if (as.empty())
            return O;

          // Step sublevel reduction in places where goal formula sequences are expanded:
          // The metasize is the total formula sequence size including subobjects, and using it
          // here allows for proof line sublevels to be written without nesting.
          lv.sub += i->metasize();
          ++m;

          if (trace_value & trace_unify) {
            std::lock_guard<std::recursive_mutex> guard(write_mutex);
            std::clog << "formula_sequence::unify(\n  " << i << ";\n  " << x << "):" << as << std::endl;
          }
        }

        return as;
      }


      // Here, x is not a formula sequence.

      alternatives as = I;
      size_type m = 0; // Conclusion index.

      for (auto& i: formulas_) {
        unify_environment tt1 = tt;
        tt1.conclusion_index_ = m;

        as = as.unify(i, tt1, x, tx, dbp, lv, sl, dr);

        // Optimization: There will be no alternatives if one is O.
        if (as.empty())
          return O;

        // Step sublevel reduction in places where goal formula sequences are expanded:
        // The metasize is the total formula sequence size including subobjects, and using it
        // here allows for proof line sublevels to be written without nesting.
        lv.sub += i->metasize();

        if (trace_value & trace_unify) {
          std::lock_guard<std::recursive_mutex> guard(write_mutex);
          std::clog << "formula_sequence::unify(\n  " << i << ";\n  " << x << "):" << as << std::endl;
        }

        ++m;
      }

      return as;
    }


    // Now tt.target_ == fact:

    // If x is metaand, for example a formula sequence, that must be resolved before *this.

    alternatives as;
    size_type n = 0; // Premise index.

    for (auto& i: formulas_) {
      unify_environment tt1 = tt;
      tt1.premise_index_ = n;

      alternatives s = mli::unify(i, tt1, x, tx, dbp, lv, sl, dr);

      if (trace_value & trace_unify) {
        std::lock_guard<std::recursive_mutex> guard(write_mutex);
        std::clog << "unify(\n  " << i << ";\n  " << x << "):" << s << std::endl;
      }

      as = as.append(s);
      ++n;
    }

    return as;
  }


  struct formula_sequence_construct {
    formula_sequence_construct() {}

    ref<formula> operator()() const { return ref<formula_sequence>(make); }

    ref<formula> operator()(const ref<formula>& x) const { return ref<formula_sequence>(make, x); }

    ref<formula> operator()(const ref<formula>& x, const ref<formula>& y) const {
      formula_sequence* yp = ref_cast<formula_sequence*>(y);
      if (yp == 0)  return ref<formula_sequence>(make, {x, y});

      return ref<formula_sequence>(make, x, *yp);
    }
  };


  split_formula formula_sequence::split(unify_environment tg,
    const ref<variable>& x, const ref<formula>& t, unify_environment tt, database* dbp, level lv, degree_pool& sl, direction dr) const {
    split_formula sf(this);  // Return value.

#if SPLIT_CONTAINER
    // If t and *this unify, then *this can be replaced by x:
    alternatives as = mli::unify(t, tt, this, tg, dr, lv, sl, dbp);

    if (!as.empty())
      sf.push_back(this, ref<formula>(x), tt.table_->find_local());
#endif
    if (formulas_.empty()) {
      sf.push_back(ref<formula_sequence>(make));
      return sf;
    }

    const ref<formula> f = formulas_.front();
    if (formulas_.size() == 1) {
      sf.append(mli::split(f, tg, formula_sequence_construct(), x, t, tt, dbp, lv, sl, dr));
      return sf;
    }

    std::vector<ref<formula>> fs(formulas_.begin() + !formulas_.empty(), formulas_.end());

    ref<formula> g = ref<formula_sequence>(make, fs);
    sf.append(mli::split(f, g, tg, formula_sequence_construct(), x, t, tt, dbp, lv, sl, dr));

    return sf;
  }


  kleenean formula_sequence::has(const ref<variable>& v, occurrence oc) const {
    kleenean kr = false;

    for (auto& i: formulas_) {
      kleenean k = i->has(v, oc);
      if (k == true)  return true;
      kr = kr || k;
    }

    return kr;
  }


  void formula_sequence::contains(std::set<ref<variable>>& s, std::set<ref<variable>>& bs, bool& more, occurrence oc) const {
    for (auto& i: formulas_)
      i->contains(s, bs, more, oc);
  }


  kleenean formula_sequence::free_for(const ref<formula>& f, const ref<variable>& x,
    std::set<ref<variable>>& s, std::list<ref<variable>>& bs) const {

    kleenean kr = true;

    for (auto& i: formulas_) {
      kleenean k = i->free_for(f, x, s, bs);
      if (k == false)  return false;
      kr = kr && k;
    }

    return kr;
  }


  void formula_sequence::unspecialize(depth x, bool y) {
    for (auto& i: formulas_)
      i->unspecialize(x, y);
  }


  void formula_sequence::unspecialize(std::set<ref<variable>>& vs, bool b) {
    for (auto& i: formulas_)
      i->unspecialize(vs, b);
  }


  ref<formula> formula_sequence::rename(level lv, degree sl) const {
    ref<formula_sequence> s(make, *this);

    std::transform(formulas_.begin(), formulas_.end(), s->formulas_.begin(),
      [=](const ref<formula>& x) { return x->rename(lv, sl); });

    return s;
  }


  ref<formula> formula_sequence::add_exception_set(variable_map& vm) const {
    ref<formula_sequence> s(make, *this);

    std::transform(formulas_.begin(), formulas_.end(), s->formulas_.begin(),
      [&vm](const ref<formula>& x) { return x->add_exception_set(vm); });

    return s;
  }


  ref<formula> formula_sequence::substitute(const ref<substitution>& s, substitute_environment vt) const {
    ref<formula_sequence> s1(make);

    for (auto& i: formulas_) {
      ref<formula> x = i->substitute(s, vt);

#if NEW_PROVED
      // Exclude proved formulas from substituted formula sequence:
      if (x->provable()) continue;
#else
      // Exclude empty formulas from substituted formula sequence:
      if (x->empty()) continue;
#endif
      auto xp = ref_cast<formula_sequence*>(x);

      // A formula sequence variable may substitute into a formula sequence, which then
      // should be concatenated.
      if (xp == nullptr)
        s1->formulas_.push_back(x);
      else
        s1->formulas_.insert(s1->formulas_.end(), xp->formulas_.begin(), xp->formulas_.end());
    }

    // Reduce ⦅⦆ to ⦰.
    if (s1->formulas_.empty())
      return {};

    // Reduce ⦅x⦆ to x.
    if (s1->formulas_.size() == 1)
      return s1->formulas_.front();

    return s1;
  }


  void formula_sequence::set_bind(bind& b, name_variable_table& vt) {
    for (auto& i: formulas_)
      i->set_bind(b, vt);
  }


  bool formula_sequence::provable() const {
    for (auto i: formulas_)
      if (!i->provable())
        return false;

    return true;
  }


  size_type formula_sequence::metasize() const {
    size_type ms = 0;

    for (auto& i: formulas_)
      ms += i->metasize();

    return ms;
  }


  bool formula_sequence::unexpanded() const {
    if (formulas_.size() <= 1)
      return true;

    for (auto& i: formulas_) {
      auto ip = ref_cast<formula_sequence*>(i);
      if (ip != nullptr || i->unexpanded())
        return true;
    }

    return false;
  }


  ref<formula> formula_sequence::expand(size_type k) const {
    ref<formula_sequence> r(make);
    size_type l = k;

    for (auto& i: formulas_) {
      auto ir = i->expand(l);

      auto fsp = ref_cast<formula_sequence*>(ir);

      if (fsp == nullptr) { r->push_back(ir); ++l; continue; }

      if (fsp->formulas_.empty()) { r->push_back({}); ++l; continue; }

      if (fsp->formulas_.size() == 1) { r->push_back(fsp->formulas_.front()); ++l; continue; }

      r->formulas_.insert(r->formulas_.end(), fsp->formulas_.begin(), fsp->formulas_.end());
      l += ir->metasize();
    }

    auto rp = ref_cast<formula_sequence*>(r);

    // Formula sequences of length should return empty or the formula it contains,
    // so fall through for length >= 1.
    if (rp != nullptr) {
      if (rp->formulas_.empty())
        return {};

      if (rp->formulas_.size() == 1)
        return rp->formulas_.front();
    }

    return r;
  }


  bool formula_sequence::has_formula(ref<formula> x) const {
    for (auto i: formulas_)
      if (i->has_formula(x))
        return true;

    return false;
  }


  order formula_sequence::compare(const unit& x) const {
    auto& xr = dynamic_cast<const formula_sequence&>(x);

    return order(formulas_.begin(), formulas_.end(), xr.formulas_.begin(), xr.formulas_.end());
  }


  precedence_t formula_sequence::precedence() const { return formula_sequence_oprec; }


  void formula_sequence::write(std::ostream& os, write_style ws) const {
    metalevel_t mt = metalevel();

    if ((trace_value & trace_empty) || mt > 1)
      os << "⦅";

    auto i0 = formulas_.begin(), i = i0, i1 = formulas_.end(), i_last = i1;
    if (!formulas_.empty())  --i_last;

    for(i = i0; i != i1; ++i) {
      if (i != i0) {
        switch (mt) {
          case 0: os << ", "; break;
          case 1: os << "; "; break;
          default: os << "¦"; break;
        }
      }

      ref<formula> x = *i;

      argument_position ap;
      if (i == i0)  ap = first;
      else if (i == i_last)  ap = last;
      else ap = middle;
#if 1
      x->write(os, ws);
#else
      bool do_bracket = precedence().argument(ap, x->precedence());

      if (do_bracket)  os << "⦅";
      x->write(os, ws);
      if (do_bracket)  os << "⦆";
#endif
    }

    if ((trace_value & trace_empty) || mt > 1)
      os << "⦆";
  }


  // If one
  ref<formula> concatenate(const ref<formula>& x, const ref<formula>& y) {
#if NEW_PROVED
    if (y->provable()) { if (x->provable()) return {}; else return x; }
    if (x->provable())  return y;
#else
    if (y->empty())  return x;
    if (x->empty())  return y;
#endif

    formula_sequence* sp1 = ref_cast<formula_sequence*>(x);
    formula_sequence* sp2 = ref_cast<formula_sequence*>(y);

    bool b1 = (sp1 != 0);
    bool b2 = (sp2 != 0);

    if (b1 && b2)
      return ref<formula_sequence>(make, *sp1, *sp2);
    else if (b1)
      return ref<formula_sequence>(make, *sp1, y);
    else if (b2)
      return ref<formula_sequence>(make, x, *sp2);

    return ref<formula_sequence>(make, {x, y});
  }


  // class inference implementation


  ref<formula> inference::get_formula(size_type k) const {
    return ref<inference>(make, head_->get_formula(k), body_, metalevel_);
  }


  // inference::add_premise(𝑷, 𝑘) adds (front) the premise 𝑷 to an inference of metalevel 𝑘
  // where it fits in the meta-hierarchy:
  // (𝑨 ⊢^𝑙 𝑩).add_premise(𝑷, 𝑘) ≔
  //   𝑙 < 𝑘 ⤳ 𝑷 ⊢^𝑘 (𝑨 ⊢^𝑙 𝑩)
  //   𝑙 = 𝑘 ⤳ 𝑷, 𝑨 ⊢^𝑘 𝑩
  //   𝑙 > 𝑘 ⤳ 𝑨 ⊢^𝑙 (𝑩.add_premise(𝑷, 𝑘))
  // 𝑷 is added front in the second case, as it is a premise that should be retained
  // after new goals have been created via unification, so eventual premises of the
  // new goals (as created via the Deduction Theorem and variants) will come after.
  ref<formula> inference::add_premise(const ref<formula>& y, metalevel_t ml,
      const varied_type& vs, const varied_type& vrs) const {
    if (y->provable())
      return this;

#if DEBUG_ADD_PREMISE
    std::cout << "inference::add_premise:\n*this = " << *this << "\ny = " << y << std::endl;
#endif
    // If *this has lower metalevel than the construction metalevel ml, then it an object
    // at this higher metalevel, and should become the head of the new inference.
    // Otherwise, y would be concatenated to the body.

    if (metalevel_ < ml)
      return ref<inference>(make, this, y, ml, vs, vrs);

    // Writing *this = 𝑨_0, …, 𝑨_k ⊢ 𝑩, returns y, 𝑨_0, …, 𝑨_k ⊢ 𝑩.
    if (metalevel_ == ml)
      return ref<inference>(make, head_, concatenate(y, body_), ml, vs, vrs);

    // metalevel_ > ml:
    return ref<inference>(make, head_->add_premise(y, ml, vs, vrs), body_, metalevel_, vs, vrs);
  }


  bool inference::is_axiom() const {
    if (metalevel() > 1)
      return head_->is_axiom();

    return false;
  }


  bool inference::is_rule() const {
    if (metalevel() > 1)
      return head_->is_rule();

    return true;
  }


  // Helper function checking that the varied variables vx of the body xb contains all
  // varied variables vy of yb, excluding the varied variable in vy not occurring free in xb.
  bool includes_varied(ref<inference> xinf, ref<inference> yinf, size_type xi, size_type yi) {

    bool b = false;

    auto xb = xinf->body_;
    auto xbp = ref_cast<formula_sequence*>(xb);

    auto iy = yinf->varied_.find(yi);

    if (iy != yinf->varied_.end()) {
      for (auto& jy: iy->second) {
        for (auto& ky: jy.second) {
          if (xbp == nullptr) {
            // xinf body is not formula sequence, so only possibly non-empty varied
            // variable set is xinf->varied_[tt.conclusion_index_][0]

            kleenean kl = xinf->body_->has(ky, occurrence::free);

            // ky not free in xinf->body_, then it cannot be varied, so can be dropped.
            if (kl == false)
              continue;

            auto it = xinf->varied_.find(xi);

            if (it == xinf->varied_.end()) { b = true; break; }

            auto jt = it->second.find(jy.first);

            if (jt == it->second.end()) { b = true; break; }

            auto kt = jt->second.find(ky);

            if (kt == jt->second.end()) { b = true; break; }
          }
          else {
            size_type j = 0;

#if DEBUG_BODY
            std::cout << "H: " << ky << ", " << b << "\n"
              << *this << "\n" << xinf << "\n\n" << yinf << "\n" << r << "\n" << a << std::endl;
#endif

            for (auto& xj: xbp->formulas_) {
              kleenean kl = xj->has(ky, occurrence::free);

              if (kl == false) {
                ++j;
                continue;
              }

              auto it = xinf->varied_.find(xi);

              if (it == xinf->varied_.end()) { b = true; break; }

              auto jt = it->second.find(j);

              if (jt == it->second.end()) {
               b = true;
                break; }

              auto kt = jt->second.find(ky);

              if (kt == jt->second.end()) {
               b = true;
                break; }

              ++j;
            }

            if (b) break;
          }

          if (b) break;
        }

        if (b) break;
      }

    }

    return !b;
  }


  alternatives inference::unify(unify_environment tt0, const ref<formula>& y, unify_environment ty, database* dbp, level lv, degree_pool& sl, direction dr) const {

    if (trace_value & trace_unify)
      write_unify(std::clog, "inference::", this, tt0, y, ty, dbp, dr) << std::endl;

    unify_environment tt = tt0;

    // A higher inference level of *this raises the *this environment level:
    if (metalevel_ > tt0.metalevel_)
      tt.metalevel_ = metalevel_;

    // If *this inference is of the form 𝑨 ⊢ ⦃𝑩_0, ..., 𝑩_k⦄ with a formula sequence ⦃𝑩_0, ..., 𝑩_k⦄,
    // convert to formula sequence ⦃𝑨 ⊢ 𝑩_0, ..., 𝑨 ⊢ 𝑩_k⦄, where each 𝑩_i is an object formula,
    // not a formula sequence. This form is then suitable for the Deduction Theorem (DT).
    // In lower metalevel syntax, this is, with the metalevel written as superscripts:
    //  𝑨 ⊢¹ 𝑩_0, …, 𝑩_k ⤳ 𝑨 ⊢¹ 𝑩_0; …; 𝑨 ⊢¹ 𝑩_k
    //  𝑨 ⊩² 𝑩_0; …; 𝑩_k ⤳ ⦃𝑨 ⊩² 𝑩_0, …, 𝑨 ⊩² 𝑩_k⦄

    // Expand 𝜞 ⊢ ⦅𝑨₀, …⦆ to ⦅𝜞 ⊢ 𝑨₀; …⦆ both goal and fact.
    if (unexpanded())
      return mli::unify(expand(tt.conclusion_index_), tt, y, ty, dbp, lv, sl, dr);

    if (y->unexpanded())
      return mli::unify(this, tt, y->expand(ty.conclusion_index_), ty, dbp, lv, sl, dr);

#if NEW_PROVED
    if (tt.target_ == goal && provable())
      return I;
#endif

    // Now *this is of the form 𝜞 ⊢ 𝑨 where 𝑨 is not a formula sequence, and also, if y
    // is an inference, it is of the form 𝜟 ⊢ 𝑩 where 𝑩 is not a formula sequence.

    // If also y is an inference of the same metalevel, of the form 𝑪 ⊢ 𝑫, unify as
    //   u(𝑩, 𝑫)*u(𝑨, 𝑪)
    // If this produces alternatives, expanding the inferences (below) is not necessary.

    inference* yip = ref_cast<inference*>(y);

    if (yip != nullptr) {
      unify_environment ty1 = ty;

      // A higher inference metalevel of y raises the y environment metalevel:
      if (yip->metalevel_ > ty.metalevel_)
        ty1.metalevel_ = yip->metalevel_;


      if (metalevel_ == yip->metalevel_) {
        // u(𝜞 ⊢⁽𝜸⁾ 𝑨; 𝜟 ⊢⁽𝜹⁾ 𝑩), of a goal-fact pair:
        // First unify 𝑨 and 𝑩. After that, two cases, whether 𝜟 does not contain a
        // formula sequence variable, and when it does.
        //
        // First case, 𝜟 does not contain a formula sequence variable. Find substitutions 𝑠
        // together with, for each 𝑠, disjoint subsequences 𝜟', 𝜟" jointly containing
        // all components of 𝜟, with corresponding varied variables 𝜹', 𝜹", and
        // substitutions 𝑠 such that 𝑠(𝜟") ⊂ 𝑠(𝜞) and 𝑠(𝜹") ⊂ 𝑠(𝜸). The new goal is
        // 𝑠(𝜞) ⊢⁽𝑠(𝜸)'⁾ 𝑠(𝜟'), where  𝑠(𝜸)' is 𝑠(𝜸) with the variables not occurring
        // free in 𝑠(𝜞) removed. Note: If all variables of 𝜞 are unspecializable, 𝑠(𝜞) ≡ 𝜞.



        // Note: The full formula sequence equality s(head_) = s(yip->head_) follows
        // as the heads are reduced to singletons before arriving here.
        // If admitting formula sequences in the heads that are not reduced,
        // both formula sequence inclusions must be done, as in the case of the body
        // unificiaton just below here.
        alternatives as = mli::unify(head_, tt, yip->head_, ty1, dbp, lv, sl, dr);

#if 1
        // Alternatively, return unify with arguents reversed, but does not arrive here.
        if (tt.target_ == fact)
          throw std::runtime_error("inference::unify: *this not a goal.");
#endif
        // With *this the goal and *yip the fact:, two cases:
        // 1. yip->body_ does not contain a formula sequence variable. Then find
        // substitutions s and disjoint formula sequence variables 𝜞, 𝜟 ⊂ yip->body_,
        // 𝜞 ∪ 𝜟 = yip->body_, such s(𝜟) ⊂ s(body_) and no formula in 𝜞 unifies with
        // one in body_. The varied variables of s(𝜟) must be a subset of the varied
        // variables of s(body_) of the corresponding formula it unifies with.
        // Then the new goal is s(body_) ⊢ s(𝜞).
        //
        // 2. yip->body_ contains a formula sequence variable 𝜞. Then the expectation is
        // that 𝜞 should pick up all formulas in body_ that do not unify with a formula in
        // yip->body_, so that s(body_) = yip->body_.

    if (tt.target_ == goal) {
      alternatives qs; // Return alternatives.

      for (auto& a: as) {
        ref<substitution> s = a.substitution_;
        ref<inference> xinf, yinf;


       // An illegal substitution merely produces no alternative, but the search loop continues:
        try {
          // Check use of tt/tt1, ty1/ty2:
          xinf = this->substitute(s, tt);
          yinf = y->substitute(s, ty1);
#if DEBUG_INFERENCE_UNIFY
          std::cout << "inference::unify X:\n"
            << "this = " << *this << "\n"
            << "xinf = " << xinf << "\n"
            << "y    = " << y << "\n"
            << "yinf = " << yinf << "\n"
            << "s = " << s << std::endl;
          yinf = y->substitute(s, ty1);
#endif
        }
        catch (illegal_substitution& ex) {
          if (trace_value & trace_unify)
            std::clog << ex.what() << std::endl;

          continue;
        }


        auto xb = xinf->body_;
        auto xbp = ref_cast<formula_sequence*>(xb);

        auto yb = yinf->body_;
        auto ybp = ref_cast<formula_sequence*>(yb);


        // If the fact body consist of a single formula sequence variable, it picks up
        // all of the goal body and varied variables.
        auto vp = ref_cast<variable*>(yb);

        if (vp != nullptr && vp->type_ == variable::formula_sequence_&& !vp->is_unspecializable()) {
          // The formula sequence variable vp of y should carry reduction the varied_ and
          // varied_in_reduction_ variables of xinf.
          ref<substitution> sr = ref<variable_substitution>(make, vp, xb, xinf->varied_, xinf->varied_in_reduction_);
          qs.push_back(a * sr);

#if DEBUG_INFERENCE_UNIFY
          std::cout << "inference::unify Y:\n"
            << "this = " << *this << "\n"
            << "xinf = " << xinf << "\n"
            << "y    = " << y << "\n"
            << "yinf = " << yinf << "\n"
            << "s  = " << s << "\n"
            << "sr  = " << sr << "\n"
            << "a * sr = " << a * sr << std::endl;
#endif
          continue;
        }


        // If the fact body is a single formula, not a formula sequence variable, it may unify
        // with one of goal premises if the varied variables are not dropped in the deduction,
        // or become the new goal.
        // Even if it unifies with one of the premises, that may not be the correct solution,
        // due to variable dependenies between different conclusions, as here only one conclusion
        // is present.
        if (ybp == nullptr) {
#if NEW_PROVED
          alternatives ds;

          if (xbp == nullptr)
            ds = a * mli::unify(xb, tt, yb, ty1, dbp, lv, sl, dr);
          else
            for (auto& i: xbp->formulas_)
              ds.append(a * mli::unify(i, tt, yb, ty1, dbp, lv, sl, dr));

          if (ds.empty()) {
            ref<inference> r0(make, yinf->body_, xinf->body_, metalevel_, varied_);

            if (includes_varied(xinf, yinf, 0, 0))
              ds = a.add_goal(r0);
          }

          qs.append(ds);
#else
          ref<inference> r0(make, yinf->body_, xinf->body_, metalevel_, varied_);

          if (includes_varied(xinf, yinf, 0, 0))
            qs.append(a.add_goal(r0));

          if (xbp == nullptr)
            qs.append(a * mli::unify(xb, tt, yb, ty1, dbp, lv, sl, dr));
          else
            for (auto& i: xbp->formulas_)
              qs.append(a * mli::unify(i, tt, yb, ty1, dbp, lv, sl, dr));
#endif
          continue;
        }


        // Now ybp != nullptr, that is, the fact body is a formula sequence.
        //
        // If the fact body formula sequence does not contain a formula sequence variable,
        // then each component may unify with a goal body component, that is, a premise.
        // The part of the fact body that does not unify with the goal premises becomes the new goal.
        //
        // If the fact body formula sequence contains a formula sequence variable, then this variable
        // should pick up what the fact body that does not unify with the goal inference premises.

        // Find the sets of indices in yb with formulas, respective formula sequence variables:
        std::list<formula_sequence::iterator> fi, fsvi;

        formula_sequence::iterator i, i0 = ybp->formulas_.begin(), i1 = ybp->formulas_.end();

        for (i = i0; i != i1; ++i) {
          auto ip = ref_cast<variable*>(*i);

          if (ip != nullptr && ip->type_ == variable::formula_sequence_ && !ip->is_unspecializable())
            fsvi.push_back(i);
          else
            fi.push_back(i);
        }


        // Case: fact inference body has no formula sequence variable.
#if 1
        if (yinf->metalevel_ == ty1.metalevel_ && fsvi.empty())
#else
        if (fsvi.empty())
#endif
        {
          // Making an internal, implicit, formula sequence variable:
          ref<variable> fsv(make, "𝚪", variable::formula_sequence_, 0, lv);
          fsv->metalevel_ = metalevel_;
          fsv->is_implicit_ = true;

          if (xbp != nullptr) {
            alternatives bs = I;

            size_type m = 0; // Premise index.

            for (auto& i: ybp->formulas_) {
              alternatives ds;

              ref<variable> vr(make, *fsv);
              vr->index_ = m;
              ds = bs.unify(vr, tt, i, ty1, dbp, lv, sl, dr);

              for (auto& j: xbp->formulas_)
                ds.append(bs.unify(j, tt, i, ty1, dbp, lv, sl, dr));

              bs = ds;
              ++m;
            }

            // Adding end marker [fsv ↦ ⦰]
            ref<substitution> sr
              = ref<substitution>(ref<variable_substitution>(make, fsv, ref<end_of_formula_sequence>()));
            bs = bs * sr;

            // For each alternative, compute the part of the fact body that was not
            // used by applying the substitution to fsv, which becomes the new goal.
            // If the result is an empty formula sequence, that is no new goal, which
            // further is compatible with the variable variation, then
            // the alternatives not fulling these conditions are redundant, as
            // the current goal formula is provable without further reductions.
            alternatives rs; // All alternatives
#if NEW_PROVED
            alternatives ps; // Only alternatives with empty hrp->formulas_.
            bool hrb = false; // Set to true if one of the hrp->formulas_ is non-empty.
#endif

            for (auto& b: bs) {
              ref<formula> hr;

              try {
                ref<substitution> t = b.substitution_;

                hr = fsv->substitute(t, ty1);
              }
              catch (illegal_substitution& ex) {
                if (trace_value & trace_unify)
                  std::clog << ex.what() << std::endl;

                continue;
              }


              // Simplify hr, by removing formulas present as a premise, and also
              // add the varied variables of the unused premises, that will become
              // the new conclusion, as varied in the reduction.

              auto hrp = ref_cast<formula_sequence*>(hr);
              size_type j = 0; // Premise index.
              size_type k = 0; // Index of the new conclusion.

              for (auto i = hrp->formulas_.begin(); i != hrp->formulas_.end(); ) {
                if (xinf->body_->has_formula(*i))
                  i = hrp->formulas_.erase(i);
                else {
                  auto iy = yinf->varied_.find(0);

                  if (iy != yinf->varied_.end()) {
                    auto jy = iy->second.find(j);

                    if (jy != iy->second.end())
                      if (!jy->second.empty())
                        for (size_type p = 0; p < xinf->body_->formula_sequence_size(); ++p)
                          xinf->varied_in_reduction_[k][p].insert(jy->second.begin(), jy->second.end());
                  }

                  ++k;
                  ++i;
                }

                ++j;
              }

#if NEW_PROVED
              if (!hrp->formulas_.empty()) {
                ref<inference> r0(make, hr, xinf->body_, xinf->metalevel_, xinf->varied_, xinf->varied_in_reduction_);

                rs.push_back(b.add_goal(r0));
              }
              else {
                hrb = true;
                ps.push_back(b);
                rs.push_back(b);
              }
#else
              if (!hrp->formulas_.empty()) {
                ref<inference> r0(make, hr, xinf->body_, xinf->metalevel_, xinf->varied_, xinf->varied_in_reduction_);

                rs.push_back(b.add_goal(r0));
              }
              else
                rs.push_back(b);
#endif
            }

#if NEW_PROVED
            if (hrb)
              qs.append(a * ps);
            else
              qs.append(a * rs);
#else
            qs.append(a * rs);
#endif

            continue;
          }
            // Now xbp == nullptr.
          else {
            alternatives bs = I;

            size_type m = 0; // Premise index.

            for (auto& i: ybp->formulas_) {
              alternatives ds;

              ref<variable> vr(make, *fsv);
              vr->index_ = m;
              ds = bs.unify(vr, tt, i, ty1, dbp, lv, sl, dr);

              ds.append(bs.unify(xb, tt, i, ty1, dbp, lv, sl, dr));

              bs = ds;
              ++m;
            }

            // Adding end marker [fsv ↦ ⦰]
            ref<substitution> sr
              = ref<substitution>(ref<variable_substitution>(make, fsv, ref<end_of_formula_sequence>()));
            bs = bs * sr;

            // For each alternative, compute the part of the fact body that was not
            // used by appying the substitution to fsv, which becomes the new goal.
            alternatives rs;  // All alternatives
#if NEW_PROVED
            alternatives ps;  // Only alternatives with empty hrp->formulas_.
            bool hrb = false; // Set to true if one of the hrp->formulas_ is non-empty.
#endif

            for (auto& b: bs) {
              ref<formula> hr;

              try {
                ref<substitution> t = b.substitution_;

                hr = fsv->substitute(t, ty1);
              }
              catch (illegal_substitution& ex) {
                if (trace_value & trace_unify)
                  std::clog << ex.what() << std::endl;

                continue;
              }

              // Simplify hr, by removing formulas present as a premise, and also
              // add the varied variables of the unused premises, that will become
              // the new conclusion, as varied in the reduction.

              auto hrp = ref_cast<formula_sequence*>(hr);
              size_type j = 0; // Premise index.
              size_type k = 0; // Index of the new conclusion.

              for (auto i = hrp->formulas_.begin(); i != hrp->formulas_.end(); ) {
                if (xinf->body_->has_formula(*i))
                  i = hrp->formulas_.erase(i);
                else {
                  auto iy = yinf->varied_.find(0);

                  if (iy != yinf->varied_.end()) {
                    auto jy = iy->second.find(j);

                    if (jy != iy->second.end())
                      if (!jy->second.empty())
                        for (size_type p = 0; p < xinf->body_->formula_sequence_size(); ++p)
                          xinf->varied_in_reduction_[k][p].insert(jy->second.begin(), jy->second.end());
                  }

                  ++k;
                  ++i;
                }

                ++j;
              }

#if NEW_PROVED
              if (!hrp->formulas_.empty()) {
                ref<inference> r0(make, hr, xinf->body_, xinf->metalevel_, xinf->varied_, xinf->varied_in_reduction_);

                rs.push_back(b.add_goal(r0));
              }
              else {
                hrb = true;
                ps.push_back(b);
                rs.push_back(b);
              }
#else
              if (!hrp->formulas_.empty()) {
                ref<inference> r0(make, hr, xinf->body_, xinf->metalevel_, xinf->varied_, xinf->varied_in_reduction_);

                rs.push_back(b.add_goal(r0));
              }
              else
                rs.push_back(b);
#endif
            }

#if NEW_PROVED
            if (hrb)
              qs.append(a * ps);
            else
              qs.append(a * rs);
#else
            qs.append(a * rs);
#endif
            continue;
          }

          return qs;
        }

        // Now fact body has at least one formula sequence variable, that is, bfsv == true.
        // As before, ybp != nullptr, that is, the fact body is a formula sequence.
        //
        // The formula sequence variables of the fact body should pick up the part
        // of goal body that does not unify with the fact body, formula sequence variables excluded,
        // so that the fact body and the goal body become equivalent after substitution viewed as
        // sets of formulas.
        // In particular, if the fact body formulas, formula sequence variables excluded, are not
        // after substitution a subset of the goal body formulas viewed as a set, the unification fails.

        // The objective is to find substitutions s such that s(xb) = s(sy) viewed as sets of
        // formulas, on the condition that the varied variables of a fact premise, after
        // substitution, must not be dropped in the goal premis it unifies with.
        //
        // The following finds substitutions s such that, in this order, xb goal and yb fact:
        //   s(xb) ⊆ s(yb)
        //   s(xb) ⊇ s(yb)
        // The first check s(xb) ⊆ s(yb) computes the formula sequence variables of yb, but yb may have additional
        // formulas not unified in xb, so the check s(xb) s(xb) ⊇ s(yb) is necessary to ensure they
        // are equal. In addition, the same formula can more than one occurence, but with different
        // sets of varied variables, so it is necessary to check these as well.
        // So strictly, xb and yb are not unifed as sets of formulas, but the pairs of formulas
        // and their sets of varied variables.





#if 1 // bfsv == true
        // First find substitution s such that s(yb') ⊆ s(xb), where yb' is the part of yb
        // holding formulas and not formula sequence variables. Thereafter compute the values of the
        // formula sequence variables of yb by a variation of s(xb) ⊆ s(yb).
        {
          if (xbp != nullptr) {
            alternatives bs = I;

            // fi holds the indices of *ybp holding formulas:
            for (auto& i: fi) {
              alternatives ds;
              for (auto& j: xbp->formulas_)
                ds.append(bs.unify(j, tt, *i, ty1, dbp, lv, sl, dr));

              bs = ds;
            }

            // Here, bs should be expanded into alternatives, in case different
            // substitutions unify different formulas.

            // If there are no alternatives, then not s(yb') ⊆ s(xb), and yb does not
            // unify with xb, as adjusting the yb formuls set variables will not help:
            if (bs.empty())
              continue;

            // Compute the formula sequence variables of yb by a variation of s(xb) ⊆ s(yb):

            formula_sequence::iterator i, i0 = xbp->formulas_.begin(), i1 = xbp->formulas_.end();

            for (i = i0; i != i1; ++i) {
              // If *i unifies with at least formula in yb', that is, fi, then
              // it should not be added to the formula sequence variables.
              bool b0 = false;

              for (auto& j: fi) {
                alternatives ds = bs.unify(*i, tt, *j, ty1, dbp, lv, sl, dr);

                if (!ds.empty()) {
                  b0 = true; break;
                }
              }

              if (b0)
                continue;

              // As i does not unify with any formula in yb, that is yb', compute the
              // alternatives for the formula sequence variables in yb:

              alternatives ds;

              for (auto& j: fsvi) {
                ref<variable> jp = ref_cast<variable*>(*j);

                ref<variable> vr(make, *jp);
                vr->index_ = i - i0;
                ds.append(bs.unify(*i, tt, vr, ty, dbp, lv, sl, dr));
              }

              bs = ds;
            }

              // Adding end marker [*i ↦ ⦰] for all i in fsvi.
              for (auto& i: fsvi) {
                ref<substitution> sr
                  = ref<substitution>(ref<variable_substitution>(make, *i, ref<end_of_formula_sequence>()));

                bs = bs * sr;
              }

            qs.append(a * bs);
            continue;
          }
            // Now xbp == nullptr.
          else {
            alternatives bs = I;

            // fi holds the indices of *ybp holding formulas:
            for (auto& i: fi)
              bs = bs.unify(xb, tt, *i, ty1, dbp, lv, sl, dr);

            // If there are no alternatives, then not s(yb') ⊆ s(xb), and yb does not
            // unify with xb, as adjusting the yb formuls set variables will not help:
            if (!fi.empty() && bs.empty())
              continue;

            // Compute the formula sequence variables of yb by a variation of s(xb) ⊆ s(yb):

            // If bs is non-empty, then the single formula in xb unified with all formulas
            // in yb', and the formula sequence variables should be sent to the empty formula.
            // If bs is empty, then one of the formula sequence variables should be sent to xb,
            // and the others to the empty formula. Do this by making alternatives of
            // fromula set variable components of index 0, which should have an end
            // marker [*i ↦ ⦰] for all i in fsvi.

            // Here, bs should be expanded into alternatives, in case different
            // substitutions unify different formulas.

            if (!bs.empty()) {
              for (auto& i: fsvi) {
                ref<substitution> sr
                  = ref<substitution>(ref<variable_substitution>(make, *i, ref<formula>()));
                bs = bs * sr;
              }
            }
            else {

              // As i does not unify with any formula in yb, that is yb', compute the
              // alternatives for the formula sequence variables in yb:

              alternatives ds;

              for (auto& j: fsvi) {
                ref<variable> jp = ref_cast<variable*>(*j);

                ref<variable> vr(make, *jp);
                vr->index_ = 0;  // Turn into a formula sequence variable component of index 0.

                ds.append(bs.unify(xb, tt, vr, ty, dbp, lv, sl, dr));
              }

              // Adding end marker ['i ↦ ⦰] for all i in fsvi.
              for (auto& i: fsvi)
                ds = ds * ref<variable_substitution>(make, *i, ref<end_of_formula_sequence>());

              bs = ds;
            }

            qs.append(a * bs);
            continue;
          }

        }
#endif  // bfsv == true

        qs.push_back(a);
      }

      return qs;
    }
      }
      else if (metalevel_ < yip->metalevel_) {
        alternatives as;

        // If the goal has lower metalevel than the inference fact, it should
        // only unify as an object against the head of the fact, and the body of the latter becomes
        // the new fact.
        if (tt.target_ == goal && metalevel_ < yip->metalevel_) {
          as = mli::unify(this, tt, yip->head_, ty1, dbp, lv, sl, dr);
          as = as.add_goal(yip->body_);
        }
        else if (ty1.target_ == goal && metalevel_ > yip->metalevel_) {
          as = mli::unify(head_, tt, y, ty1, dbp, lv, sl, dr);
          as = as.add_goal(body_);
        }

        return as;
      }
      else {
        // metalevel_ > yip->metalevel_:

        alternatives as;

        // Now the goal has higher metalevel than the inference fact, the latter should
        // unify against the head of the former, retaining the body as a premise.
        if (tt.target_ == goal) {
          as = mli::unify(head_, tt, y, ty1, dbp, lv, sl, dr);
#if DEBUG_INFERENCE_UNIFY
          std::cout << "inference::unify Q:\n*this = " << *this << "\ny = " << y << "\nas = " << as << std::endl;
#endif
          as = as.add_premise(body_, metalevel_, varied_, varied_in_reduction_);
        }
        else {
          as = mli::unify(this, tt, yip->head_, ty1, dbp, lv, sl, dr);
          as = as.add_premise(yip->body_, yip->metalevel_, yip->varied_, yip->varied_in_reduction_);
        }

        return as;
      }
    }


    /* Write A ≔ body_, B ≔ head_, x ≔ (A ⊢ B), u ≔ unify, and when y is an
      inference, write y ≔ (C ⊢ D). Solutions:
      1. u(B, D).u(A, C). Unify x and y as objects.
      2. u(B, D), use the A or C that is a goal as premise in this unification.
        In result, add the A or C that is a goal (resp. fact) as premise (resp. condition).
        As A or C can be further be an inference, as in the body of the deduction
        theorem (𝑨 ⊢ 𝑩) ⊢ 𝑨 ⇒ 𝑩, simplify further.
      3a. B is an inference.
         u(B, y), if x is a goal, use A as a premise.
         In result, if A is a goal (resp. fact), add it as premise (resp. condition).
      3b. D is an inference.
         u(x, D), if y is a goal, use C as a premise.
         In result, if C is a goal (resp. fact), add it as premise (resp. condition).
      The cases 2, 3 can be handled by unnesting x, and let recursive calls do the rest
      (including argument reversal in pre_unify).
    */

    // Now, y is not an inference:
    // If *this is a fact, check if in unifies against its body used as premise.
    // and u(*this, y) with the body added as premise.
    // If *this is a fact, u(*this, y) with the dboy added as a goal.

    if (tt.target_ == goal) {

      // The body should be used as a premise. This can be achieved using a
      // metaand (resp. metaor) sequence added to y if y is a fact (resp. goal).
      // When a fact, the metaand and metaor behavior is reversed in the unification
      // implementation, so it is not necessary the change the types, and left unchanged.

      // Case ty.target_ == goal does not occur here; goals are unified against facts only:

      alternatives as = mli::unify(head_, tt, y, ty, dbp, lv, sl, dr);

      as = as.add_premise(body_, metalevel_, varied_, varied_in_reduction_);

      return as;
    }
    else {
      alternatives as = mli::unify(head_, tt, y, ty, dbp, lv, sl, dr);

      // The body can be a formula sequence 𝜞 (or ⦰), in which case there should be a substitution [𝜞 ↦ ⦰].
      alternatives bs = as.unify(body_, tt, ref<formula>(), ty, dbp, lv, sl, dr);

      if (!bs.empty())
        return bs;

      as = as.add_goal(body_);

      return as;
    }
  }


  struct inference_construct {
    metalevel_t metalevel_;

    inference_construct(metalevel_t ml) : metalevel_(ml) {}

    ref<formula> operator()(const ref<formula>& x, const ref<formula>& y) const {
      return ref<inference>(make, x, y, metalevel_);
    }
  };


  split_formula inference::split(unify_environment tg,
    const ref<variable>& x, const ref<formula>& t, unify_environment tt, database* dbp, level lv, degree_pool& sl, direction dr) const {
    split_formula sf(this);  // Return value.
    // If t and *this unify, then *this can be replaced by x:
    alternatives as = mli::unify(t, tt, this, tg, dbp, lv, sl, dr);

    if (!as.empty())
      sf.push_back(this, ref<formula>(x), tt.table_->find_local());

    sf.append(mli::split(head_, body_, tg, inference_construct(metalevel_), x, t, tt, dbp, lv, sl, dr));

    return sf;
  }


  ref<formula> inference::expand(size_type k) const {
    if (!unexpanded())
      return this;

    ref<formula> hx = head_->expand(k);

    auto hxp = ref_cast<formula_sequence*>(hx);

    if (hxp == nullptr)
      return ref<inference>(make, hx, body_, metalevel_, varied_, varied_in_reduction_);

    // Do not remove empty formulas (m == 0), not working with the
    // inference varied variable recomputation.

    ref<formula_sequence> r(make);

    // Conclusion index of *this, not that of the formula sequence expansion of which
    // it is a part of, so it start at 0. Calls to 'expand' shoul start at k.
    size_type l = 0;

    for (auto& i: hxp->formulas_) {
      auto j = varied_.find(l);
      auto k = varied_in_reduction_.find(l);

      ref<inference> ir;

      // As the components varied_[l] and varied_in_reduction_[l] should be extracted,
      // it is necessary to divide into cases when these already exist.
      if (j != varied_.end() && k != varied_in_reduction_.end())
        r->push_back(ref<inference>(make, i, body_, metalevel_, j->second, k->second));
      else if (j != varied_.end())
        r->push_back(ref<inference>(make, i, body_, metalevel_, j->second));
      else if (k != varied_in_reduction_.end())
        r->push_back(ref<inference>(make, i, body_, metalevel_, varied_premise_type(), k->second));
      else
        r->push_back(ref<inference>(make, i, body_, metalevel_));

      ++l;
    }

    return r;
  }


  kleenean inference::has(const ref<variable>& v, occurrence oc) const {
    kleenean k1 = head_->has(v, oc);
    if (k1 == true)  return true;
    kleenean k2 = body_->has(v, oc);
    return k1 || k2;
  }


  void inference::contains(std::set<ref<variable>>& vs, std::set<ref<variable>>& bs, bool& more, occurrence oc) const {
    head_->contains(vs, bs, more, oc);
    body_->contains(vs, bs, more, oc);
  }


  kleenean inference::free_for(const ref<formula>& f, const ref<variable>& x,
    std::set<ref<variable>>& s, std::list<ref<variable>>& bs) const {
    kleenean k1 = head_->free_for(f, x, s, bs);
    if (k1 == false)  return false;
    kleenean k2 = body_->free_for(f, x, s, bs);
    return k1 && k2;
  }


  void inference::unspecialize(depth x, bool b) {
    // Not applied to the varied variables, as they are stored in in a
    // std::set container, which does not allow mutations:
    head_->unspecialize(x, b);
    body_->unspecialize(x, b);
  }


  void inference::unspecialize(std::set<ref<variable>>& vs, bool b) {
    // Not applied to the varied variables, as they are stored in in a
    // std::set container, which does not allow mutations:
    head_->unspecialize(vs, b);
    body_->unspecialize(vs, b);
  }


  ref<formula> inference::rename(level lv, degree sl) const {
    ref<formula> h = head_->rename(lv, sl);
    ref<formula> b = body_->rename(lv, sl);

    varied_type vvs;

    for (auto& i: varied_)
      for (auto& j: i.second)
        for (auto& k: j.second)
          vvs[i.first][j.first].insert(k->rename(lv, sl));

    varied_type vrs;

    for (auto& i: varied_in_reduction_)
      for (auto& j: i.second)
        for (auto& k: j.second)
          vrs[i.first][j.first].insert(k->rename(lv, sl));

    return ref<inference>(make, h, b, metalevel_, vvs, vrs);
  }


  ref<formula> inference::add_exception_set(variable_map& vm) const {
    // No need to add excepted variables to the varied variables, as they are
    // limited variables do not have that:
    ref<formula> h = head_->add_exception_set(vm);
    ref<formula> b = body_->add_exception_set(vm);

    return ref<inference>(make, h, b, metalevel_, varied_);
  }


  // Currently, only partially implemented:
  // Make check for varied variable free occurances to handle body substitution
  // expansions, which may occur due to the presence of formula sequence variables.

  ref<formula> inference::substitute(const ref<substitution>& s, substitute_environment vt) const {
    ref<formula> h = head_->substitute(s, vt);

#if NEW_PROVED
    if (h->provable())
      return {};
#else
    if (h->empty())
      return {};
#endif

    // To properly renumber the varied variable in case of a formula sequence variable
    // in the body, it is necessary, when applicable, to expand the latter into a formula sequence
    // and then substitute the formula sequence variable, as in formulas_set::substitute.

    auto bp = ref_cast<formula_sequence*>(body_);

    if (bp == nullptr) {
      // The body is not a formula sequence, but may expand in size in case of a
      // formula sequence variable.
      ref<formula> b = body_->substitute(s, vt);

      varied_type vvs, vrs;

      size_type n = 1;

      auto fsp = ref_cast<formula_sequence*>(b);

      if (fsp != nullptr)
        n = fsp->formulas_.size();

      // At most one index varied_[c][p] non-empty, as the body is of size 1.

      for (auto& i: varied_)
        for (auto& j: i.second)
          for (auto& k: j.second) {
            ref<variable> sk = k->substitute(s, vt);

            // Only free occurrences count as varied, so if they do not appear
            // in x, there is no need to forward them.

            kleenean kl = b->has(sk, occurrence::free);

            if (kl != false)
              for (size_type m = 0; m < n; ++m)
                vvs[i.first][j.first + m].insert(sk);
          }

      // As the variables varied in reduction do not depend on the premise,
      // only the conclusion, there is no need to take into account changes
      // in the body formula sequence size.

      for (auto& i: varied_in_reduction_)
        for (auto& j: i.second)
          for (auto& k: j.second) {
            ref<variable> sk = k->substitute(s, vt);

            // A variable in varied in reduction, not immediately occurring
            // free in a premise, may later be unify with a premise and
            // substituted to do so, so it cannot be removed, contrary to the
            // case of variables varied for a premise.
            for (size_type m = 0; m < n; ++m)
              vrs[i.first][j.first + m].insert(sk);
          }

      // Extracting the varied variables from substitutable formula sequence variables,
      // become appended after the varied variable of *this.
      auto vp = ref_cast<variable*>(body_);

      if (vp != nullptr && vp->type_ == variable::formula_sequence_&& !vp->is_unspecializable())
        s->get_varied(vvs, vrs, *vp, 0);

      return ref<inference>(make, h, b, metalevel_, vvs, vrs);
    }

    // bp != nullptr, substitute components, and adjust varied premise indices as
    // they expand or shrink from the presence of formula sequence variables.

    ref<formula_sequence> b(make);
    varied_type vvs, vrs;

    size_type n = 0, m = 0; // n = index of body_, m = index of substituted body.


    for (auto& f: bp->formulas_) {
      substitute_environment vt1 = vt;
      vt1.premise_index_ = n;

      ref<formula> x = f->substitute(s, vt1);

#if NEW_PROVED
      // Exclude proved formulas from substituted formula sequence:
      if (x->provable()) {
        ++n;
        continue;
      }
#else
      // Exclude empty formulas from substituted formula sequence:
      if (x->empty()) {
        ++n;
        continue;
      }
#endif

      auto xp = ref_cast<formula_sequence*>(x);

      if (xp == nullptr)
        b->formulas_.push_back(x);
      else
        b->formulas_.insert(b->formulas_.end(), xp->formulas_.begin(), xp->formulas_.end());

      size_type m0 = m, m1 = m + x->formula_sequence_size();

      // If varied_[vt1.conclusion_index_][n] exists, write over to:
      // vvs[vt1.conclusion_index_][m] … vvs[vt1.conclusion_index_][m1]

      for (auto& i: varied_) {
        auto j = i.second.find(n);

        if (j != i.second.end()) {

          std::set<ref<variable>> vs;

          for (auto& v: j->second) {
            ref<variable> v1 = v->substitute(s, vt);

            // Only free occurrences count as varied, so if they do not appear
            // in x, there is no need to forward them.

#if DEBUG_INFERENCE_UNIFY
            std::cout << "f = " << f << ", x = " << x << ", v = " << v << ", v1 = " << v1 << std::endl;
#endif
            kleenean kl = x->has(v1, occurrence::free);

            if (kl != false)
              vs.insert(v1);
          }

          if (!vs.empty())
            for (size_type k = m0; k < m1; ++k)
              vvs[i.first][k].insert(vs.begin(), vs.end());
          }
      }

      // If varied_[vt1.conclusion_index_][n] exists, write over to:
      // vvs[vt1.conclusion_index_][m] … vvs[vt1.conclusion_index_][m1]

      for (auto& i: varied_in_reduction_) {
        auto j = i.second.find(n);

        if (j != i.second.end()) {

          std::set<ref<variable>> vs;

          for (auto& v: j->second) {
            // As the variables varied in reduction are not assoicated with any
            // premise (only carried along to admit that in a later stage), a
            // check for free occurences ahosul not be done (unlike the case of the
            // variables varied of a premise).
            vs.insert(v->substitute(s, vt));
          }

          if (!vs.empty())
            for (size_type k = m0; k < m1; ++k)
              vrs[i.first][k] = vs;
          }
      }

      // Extracting the varied variables from substitutable formula sequence variables,
      // become appended after the varied variable of *this.
      auto vp = ref_cast<variable*>(f);

      if (vp != nullptr && vp->type_ == variable::formula_sequence_&& !vp->is_unspecializable())
        s->get_varied(vvs, vrs, *vp, m);

      ++n;
      m = m1;
    }

#if 1
    // Reduce ⦅⦆ ⊢ 𝑨 to 𝑨, in case no varied in reduction variables.
    if (b->formulas_.empty() && vrs.empty())
      return h;

    // Reduce ⦅𝑨⦆ ⊢ 𝑩 to 𝑨 ⊢ 𝑩.
    if (b->formulas_.size() == 1)
      return ref<inference>(make, h, b->formulas_.front(), metalevel_, vvs, vrs);

    return ref<inference>(make, h, b, metalevel_, vvs, vrs);
#endif
  }


  void inference::set_bind(bind& b, name_variable_table& vt) {
    // No need to set bind to the varied variables, as they are free occurrences:
    head_->set_bind(b, vt);
    body_->set_bind(b, vt);
  }


  bool inference::provable() const {
#if NEW_PROVED
    // Checks if the conclusions (head) can be derived from the premises (body).
    return head_->is_metasubset(body_);
#else
    return head_->provable();
#endif
  }


  order inference::compare(const unit& x) const {
    auto& xr = dynamic_cast<const inference&>(x);

#if (__cplusplus > 201703L) // C++20
#if 1
    return {metalevel_ <=> xr.metalevel_, head_ <=> xr.head_, body_ <=> xr.body_};
#else
    return std::tuple(metalevel_, head_, body_) <=> std::tuple(xr.metalevel_, xr.head_, xr.body_);
#endif
#else
    order d = order(metalevel_, xr.metalevel_);
    if (d != equal)  return d;
    order c = mli::compare(head_, xr.head_);
    if (c != equal)  return c;
    return mli::compare(body_, xr.body_);
#endif
  }


  precedence_t inference::precedence() const {
    return metalevel() > 1? inference_ml_2_oprec : inference_oprec;
  }


  void inference::write(std::ostream& os, write_style ws) const {

    // Parenthesize body:
    bool pb = precedence().argument(first, body_->precedence());
    if (pb) os << "(";
    body_->write(os, ws);
    if (pb) os << ")";

    os << " ";

    switch (metalevel()) {
      case 1: os << "⊢"; break;
      case 2: os << "⊩"; break;
      case 3: os << "⊪"; break;
      default: os << "⊢" << to_index(superscript, (size_t)metalevel());
    }

    if (!varied_.empty()) {

      os << "⁽";

      bool i0 = true;

      for (auto& i: varied_) {
        if (i0) i0 = false;
        else os << ";";

        if (varied_.size() != 1 || i.first != 0)
          os << to_index(superscript, i.first) << " ";

        bool j0 = true;

        for (auto& j: i.second) {
          if (j0) j0 = false;
          else os << ",";

          if (varied_.size() != 1 || !(i.second.size() == 1 && j.first == 0))
            os << to_index(superscript, j.first) << " ";

          bool k0 = true;

          for (auto& k: j.second) {
            if (k0) k0 = false; else os << " ";
            os << k;
          }
        }
      }

      os << "⁾";
    }


    if (!varied_in_reduction_.empty()) {
      os << "₍";

      bool i0 = true;

      for (auto& i: varied_in_reduction_) {
        if (i0) i0 = false;
        else os << ";";

        if (varied_in_reduction_.size() != 1 || i.first != 0)
          os << to_index(subscript, i.first) << " ";

        bool j0 = true;

        for (auto& j: i.second) {
          if (j0) j0 = false;
          else os << ",";

          if (varied_in_reduction_.size() != 1 || !(i.second.size() == 1 && j.first == 0))
            os << to_index(subscript, j.first) << " ";

          bool k0 = true;

          for (auto& k: j.second) {
            if (k0) k0 = false; else os << " ";
            os << k;
          }
        }
      }

      os << "₎";
    }

    os << " ";

    // Parenthesize head:
    bool ph = precedence().argument(last, head_->precedence());
    if (ph) os << "(";
    head_->write(os, ws);
    if (ph) os << ")";
  }


  // Write a list of proofs.
  void write_proofs(std::ostream& os, std::list<proof>& pfs) {
    os << "Proof count: " << pfs.size() << "\n" << std::endl;
    std::list<proof>::iterator i, i0 = pfs.begin(), i1 = pfs.end();
    for (i = i0; i != i1; ++i) {
      if (i != i0)  os << "\n";
      os << *i;
    }
    os << std::endl;
  }


  // Write a set variables.
  void write_variables(std::ostream& os, write_style ws, std::set<ref<variable>>& vs) {
    if (vs.size() == 1)  os << "Variable: ";
    else  os << "Variables: ";
    std::set<ref<variable>>::iterator v, v0 = vs.begin(), v1 = vs.end();
    if (vs.empty())  os << "none";
    else
    for (v = v0; v != v1; ++v) {
      if (v != v0)  os << ", ";
      (*v)->write(os, ws);
    }
  }


#if WRITE_SOLUTIONS
  // Write one solution.
  void write_solution(std::ostream& os, write_style ws,
      std::set<ref<variable>>& vs, ref<substitution> s) {
    if (vs.empty())  return;
    std::set<ref<variable>>::iterator i, i0 = vs.begin(), i1 = vs.end();
    for (i = i0; i != i1; ++i) {
      ref<formula> f = (*s)(ref<formula>(*i));
      if (f != ref<formula>(*i)) {
        if (i != i0)  os << "\n";
        os << *i << " ≡ ";
        f->write(os, ws);
      }
    }
  }


  // Write a list of substitutions.
  void write_solution(std::ostream& os, std::list<ref<substitution>>& ss) {
    std::list<ref<substitution>>::iterator s, s0 = ss.begin(), s1 = ss.end();
    if (ss.size() == 1)   os << "Substitution:";
    else  os << "Substitutions:";
    if (ss.empty())  os << " none\n";
    else if (ss.size() == 1)  os << " " << *s0;
    else
    for (s = s0; s != s1; ++s) {
      os << "\n  ";
      os << *s;
    }
  }


  // Write variables that get new values by the substitutions.
  void write_solution(std::ostream& os, write_style ws,
      std::set<ref<variable>>& vs, std::list<ref<substitution>>& ss) {
    std::list<ref<substitution>>::iterator s, s0 = ss.begin(), s1 = ss.end();
    if (vs.empty()) { // No variables in query:
      os << (ss.empty()? "Not proved." : "Proved.") << std::endl;
      return;
    }

    if (ss.empty()) {
      os << "No solutions." << std::endl;
      return;
    }

    for (s = s0; s != s1; ++s) {
      if (s != s0)  os << ";\n";
      write_solution(os, ws, vs, *s);
    }

    os << ".\n";
  }
#endif

  alternatives database::unify(unify_environment, const ref<formula>&, unify_environment, database*, level, degree_pool&, direction) const {
    return O;
  }

  alternatives database::unify(const ref<formula>& x, unify_environment tx, const ref<formula>& y, unify_environment ty, database* dbp, level lv, degree_pool& sl, direction dr) const {
    return x->unify(tx, y, ty, dbp, lv, sl, dr);
  }


  ref<formula> database::rename(level, degree) const {
    return this->new_p();
  }


  ref<formula> database::add_exception_set(variable_map& vm) const {
    return ref<database>(make, *this);
  }


  bool database::empty() const {
    return true;
  }


  int database::get_level() const {
    return 0;
  }


  bool database::has_definition(level) const {
    return false;
  }


  bool database::insert(const ref<statement>& st) {
    if (trace_value & trace_database)
      std::cerr << "database::insert, no database: " << st << "\n";
    return false;
  }


  std::optional<ref<statement>> database::find(const std::string& name, level lv) {
    if (trace_value & trace_database)
      std::cerr << "database::find, no database, level " << lv.top << ", degree " << lv.sub << ", name: " << name << "\n";

    return {};
  }


  void database::write(std::ostream& os, write_style) const {
    os << "no database\n";
  }


} // namespace mli
