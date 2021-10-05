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

#include "MLI.hh"
#include "substitution.hh"
#include "metacondition.hh"


namespace mli {

  ref<formula> substitution::operator()(const ref<formula>& x) const {
    substitute_environment se;

    return x->substitute(this, se);
  }


  alternatives substitution::unify(unify_environment, const ref<formula>& x, unify_environment, database*, level, degree_pool&, direction) const {
    if (trace_value & trace_unify) {
      std::lock_guard<std::recursive_mutex> guard(write_mutex);
      std::clog
       << "substitution::unify\n  " << *this << ";\n  " << x << ")" << std::endl;
    }

    substitution* xp = ref_cast<substitution*>(x);
    return (xp != 0) && (xp->is_identity())? I : O;
  }


  order substitution::compare(const unit& x) const {
    auto& xr = dynamic_cast<const substitution&>(x);
    return xr.is_identity()? equal : unordered;
  }


  // Class variable_substitution


#define TABLE_DEBUG 0

  ref<formula> variable_substitution::substitute_variable(const ref<variable>& x, substitute_environment vt) const {
    if (trace_value & trace_substitute) {
      std::lock_guard<std::recursive_mutex> guard(write_mutex);
      std::clog << "Begin variable_substitution::substitute_variable\n  "
        << "(" << x << ")" << *this << ".\n"
        << std::flush;
#if TABLE_DEBUG
      std::clog << "Variable table:";
      if (vt.table_->empty()) std::clog << " empty";
      else std::clog << "\n" << vt.table_;
      std::clog << std::endl;
#endif
    }

    // A substitution x[v ↦ f] or x[v ⤇ f].

#if 1 // debug.hh
    // Optimization: identity substitution.
    if (variable_ == formula_)
      return ref<formula>(x);
#endif

    variable* fp = ref_cast<variable*>(formula_);


    // Variable change of limited variables legality verification:
    // Applies to both ordinary (unification) substitutions x[v ↦ f] and
    // explicit substitutions x[v ⤇ f].
    //
    // A congurent variable change prohibits that a variable changes its binding,
    // and it suffices to check that its binding depth does not change. It derives
    // from the condition that a free occurrence in a subpart of the formula cannot
    // change to become bound, which in its turn derives from the substitution
    // free-for condition.
    //
    // In
    //   u(𝛽𝑥 𝑃(𝑥, 𝑦), 𝛽𝑦 𝑃(𝑦, 𝑦))
    // A substitution [𝑥 ↦ 𝑦] or [𝑦 ↦ 𝑥] produces the same variable 𝑥 or 𝑦 in all
    // occurances, causing the free occurrence of 𝑦 in 𝛽𝑥 𝑃(𝑥, 𝑦) to become bound,
    // which is illegal, so it is necessary for a check against this occurring.
    // The substitution [𝑥 ↦ 𝑦] leads to 𝑦[𝑥 ↦ 𝑦] in both formulas, but only in
    // 𝛽𝑥 𝑃(𝑥, 𝑦) it is a sign of an illegal variable change. In this case, 𝑥 is in the
    // bound variable table that is associated with 𝑦 and 𝛽𝑥 𝑃(𝑥, 𝑦). In 𝛽𝑦 𝑃(𝑦, 𝑦), 𝑥 is
    // not in this table. This is the first case:
    //   x[v ↦ f], where x ≡ f, depth v ≠ 0, depth x ≠ depth v.
    // The substitution [𝑦 ↦ 𝑥] leads to 𝑦[𝑦 ↦ 𝑥], but only in 𝛽𝑥 𝑃(𝑥, 𝑦) it is an
    // illegal subtitution. In this case, 𝑥 is in the bound variable table that is
    // associated with 𝑦 and 𝛽𝑥 𝑃(𝑥, 𝑦). In 𝛽𝑦 𝑃(𝑦, 𝑦), 𝑥 is
    // not in this table. This is the second case:
    //   x[v ↦ f], where x ≡ v, depth f ≠ 0, depth x ≠ depth f.
    // For explicit subtitutions, this is done by the free-for check.
    // If x ≡ v ≡ f, there is nothing to check, as the substitution is the identity.
    if (x->is_limited() && variable_->is_limited()) {

      // If the premise or conclusion indices differ, then *this is a substitution of a different
      // premise or conclusion formula and its variable variation is different, and so cannot
      // be used to determine if the Deduction Theorem is applicable.

      // The conclusion indices are set to 0 before arriving here, so need not to be checked:
      if (premise_to_conclusion_ && premise_index_ != vt.premise_index_)
        return x;

      size_type dx = x->get_depth(vt.table_);
      bool is_illegal = false;

      if (x == formula_) {
        size_type dv = variable_->get_depth(vt.table_);

        if (dv != 0 && dx != dv)
          is_illegal = true;
      }
      else  // A change-of-variable check; for explicit substitutions, this is done by a free-for check:
      if (x == variable_) {
        size_type df = ref_cast<variable&>(formula_).get_depth(vt.table_);

        if (df != 0 && dx != df)
          is_illegal = true;
      }

      if (is_illegal) {
        std::ostringstream oss;
        oss << "variable_substitution::substitute_variable: Illegal variable change: "
          << variable_ << " ⤳ " << formula_ << " of " << x << *this;

        throw illegal_substitution(oss.str());
      }
    }


    // For an ordinary (unification) substitution, equal variables substitute, otherwise
    // no effect, delay or other checks, as unification merely makes expressions identical.

    // Extension for (formula) set variable components.
    // When variable_ is a variable sent to an end marker [𝜞 ↦ □], then
    // x->components_, if non-empty, should be returned; otherwise return formula_.
    // When variable_ is a set index, then formula_ should be
    // added to a copy of x, which is returned.
    // Currently, no set index variable can be sent to an end marker.
    if (x == variable_) {
      // If *this is an end marker substitution [𝜞 ↦ □], return the components of x:
      if (formula_->is_end_of_formula_sequence())
        return ref<formula_sequence>(make, x->components_);

      // When the variable_ is not a set index, return formula_,
      // except in the case of a premise-to-conclusion substitution which,
      // if not explicit, only substitutes bound occurrences.
      if (variable_->index_ == -1) {
        if (premise_to_conclusion_ && variable_->get_depth(vt.table_) == 0)
          return variable_;

        return formula_;
      }

      // Now, variable_ is a set index of x, so formula_ should be added to
      // the components in a copy of x, which is returned.
      ref<variable> vr(make, *x);

      vr->components_.push_back(formula_);
      return vr;
    }


#if 1
    // Check that no variables excluded_from_ are dropped with respect to the
    // current substitution, that is, if variable_ is in excluded_from_,
    // the the replacement formula_ must be excluded_.
    if (x->excluded_from_.contains(variable_) && !x->excluded_.contains(formula_)) {
      std::ostringstream oss;
      oss << "variable_substitution::substitute_variable, excluded variables dropped: "
        << "(" << x << ")" << *this;
      throw illegal_substitution(oss.str());
    }

    // If variable_ is excluded in x, it must be replaced by formula_.
    if (x->excluded_.contains(variable_)) {
      ref<variable> xr(make, *x);
      xr->excluded_.erase(variable_);
      xr->excluded_.insert(formula_);
      return xr;
    }

    return x;
#else
    // If *this can substitute a variable in x.excluded_, make a copy of x
    // with this variable substituted.

    if (!x->excluded_.contains(variable_))
      return x;

    ref<variable> x1(make, *x);
    x1->excluded_.erase(variable_);
    x1->excluded_.insert(formula_);

    return x1;
#endif
  }


  void variable_substitution::set_bind(bind& b, name_variable_table& vs) {
    variable_->set_bind(b, vs);  
    formula_->set_bind(b, vs);
  }


  ref<formula> variable_substitution::rename(level lv, degree sl) const {
    ref<variable_substitution> mp(make, *this);
    mp->variable_ = variable_->rename(lv, sl);
    mp->formula_ = formula_->rename(lv, sl);
    return mp;  
  }


  ref<formula> variable_substitution::add_exception_set(variable_map& vm) const {
    ref<variable_substitution> mp(make, *this);
    mp->variable_ = variable_->add_exception_set(vm);
    mp->formula_ = formula_->add_exception_set(vm);
    return mp;
  }


  kleenean variable_substitution::has(const ref<variable>& v, occurrence oc) const {
    kleenean k1 = variable_->has(v, oc);
    if (k1 == true)  return true;

    kleenean k2 = formula_->has(v, oc);

    return k1 || k2;
  }


  void variable_substitution::contains(std::set<ref<variable>>& s, std::set<ref<variable>>& bs, bool& more, occurrence oc) const {
    variable_->contains(s, bs, more, oc);
    formula_->contains(s, bs, more, oc);
  }


  kleenean variable_substitution::free_for(const ref<formula>& f, const ref<variable>& x,
    std::set<ref<variable>>& s, std::list<ref<variable>>& bs) const {
    kleenean k1 = variable_->free_for(f, x, s, bs);
    if (k1 == false)  return false;
    kleenean k2 = formula_->free_for(f, x, s, bs);
    return k1 && k2;
  }


  void variable_substitution::unspecialize(depth x, bool y) {
    variable_->unspecialize(x, y);
    formula_->unspecialize(x, y);
  }


  void variable_substitution::unspecialize(std::set<ref<variable>>& vs, bool b) {
    variable_->unspecialize(vs, b);
    formula_->unspecialize(vs, b);
  }


  ref<formula> variable_substitution::substitute(const ref<substitution>& s, substitute_environment vt) const {
    ref<formula> v0 = variable_->substitute(s, vt);

    variable* vp = ref_cast<variable*>(v0);
    if (vp == 0)
      throw illegal_substitution("In variable_substitution::substitute, substitution of variable not a variable.");

    ref<variable_substitution> mp(make, *this);
    mp->variable_ = vp;
    mp->formula_ = formula_->substitute(s, vt);

    return mp;  
  }


  alternatives variable_substitution::unify(unify_environment tt, const ref<formula>& x, unify_environment tx, database* dbp, level lv, degree_pool& sl, direction dr) const {
    if (trace_value & trace_unify) {
      std::lock_guard<std::recursive_mutex> guard(write_mutex);
      std::clog << "variable_substitution::unify(\n  " << *this << ";\n  " << x << ")\n" << std::flush;
    }

    variable_substitution* xp = ref_cast<variable_substitution*>(x);
    if (xp == 0)  return O;
    alternatives as = mli::unify(ref<formula>(variable_), tt, ref<formula>(xp->variable_), tx, dbp, lv, sl, dr);
    return as.unify(formula_, tt, xp->formula_, tx, dbp, lv, sl, dr);  
  }


  struct variable_substitution_construct {
    ref<variable> variable_;

    variable_substitution_construct(const ref<variable>& v)
     : variable_(v) {}

    ref<formula> operator()(const ref<formula>& x) const {
      return ref<variable_substitution>(make, variable_, x);
    }
  };


  split_formula variable_substitution::split(unify_environment tg,
    const ref<variable>& x, const ref<formula>& t, unify_environment tt, database* dbp, level lv, degree_pool& sl, direction dr) const {
    split_formula sf(this);  // Return value.
    // If t and *this unify, then *this can be replaced by x:
    alternatives as = mli::unify(t, tt, this, tg, dbp, lv, sl, dr);

    if (!as.empty())
      sf.push_back(this, ref<formula>(x), tt.table_->find_local());

    sf.append(mli::split(formula_, tg, variable_substitution_construct(variable_), x, t, tt, dbp, lv, sl, dr));

    return sf;
  }


  ref<substitution> variable_substitution::innermost() const {
    return this;
  }


  ref<substitution> variable_substitution::without() const {
    return ref<substitution>(make);
  }


  ref<substitution> variable_substitution::outermost() const {
    return this;
  }


  ref<substitution> variable_substitution::within() const {
    return ref<substitution>(make);
  }


  order variable_substitution::compare(const unit& x) const {
    auto& xr = dynamic_cast<const variable_substitution&>(x);
#if (__cplusplus > 201703L) // C++20
    order c = variable_ <=> xr.variable_;
    if (c != equal)  return c;
    return formula_ <=> xr.formula_;
#else
    order c = mli::compare(variable_, xr.variable_);
    if (c != equal)  return c;
    return mli::compare(formula_, xr.formula_);
#endif
  }


  void variable_substitution::write(std::ostream& os, write_style ws) const {

    // Remove if bind_ numbers not written in threads.
    std::lock_guard<std::recursive_mutex> guard(write_mutex);

    bool write_reverse = write_substitution_mapto_reverse & ws;
    os << "[";

    if (write_reverse)
      os << formula_ << " ↤ " << variable_;
    else {
      os << variable_ << " ↦";


      if (premise_to_conclusion_)
        os << to_index(superscript, conclusion_index_)
          << " " << to_index(superscript, premise_index_);

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

          if (varied_.size() != 1 || i.first != 0)
            os << to_index(subscript, i.first) << " ";

          bool j0 = true;

          for (auto& j: i.second) {
            if (j0) j0 = false;
            else os << ",";

            if (varied_.size() != 1 || !(i.second.size() == 1 && j.first == 0))
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
      if (formula_->empty()) os <<  "⦰";
      else os << formula_;
    }


    os << "]";
  }


  // Class explicit_substitution


  ref<formula> explicit_substitution::substitute_variable(const ref<variable>& x, substitute_environment vt) const {
    if (trace_value & trace_substitute) {
      std::lock_guard<std::recursive_mutex> guard(write_mutex);
      std::clog << "Begin explicit_substitution::substitute_variable\n  "
        << "(" << x << ")" << *this << ".\n"
        << std::flush;
#if TABLE_DEBUG
      std::clog << "Variable table:";
      if (vt.table_->empty()) std::clog << " empty";
      else std::clog << "\n" << vt.table_;
      std::clog << std::endl;
#endif
    }

    // A substitution x[v ⤇ f], v = variable_, f = formula_:

    // Optimization: identity substitution.
    if (variable_ == formula_)
      return x;


    variable* fp = ref_cast<variable*>(formula_);


    // Variable change of limited variables legality verification, and as a limited
    // variable can have both free and bound occurrences, a check also for explicit
    // substitutions x[v ⤇ f], not only (unification) substitutions x[v ↦ f].
    //
    // A congurent variable change prohibits that a variable changes its binding,
    // and it suffices to check that its binding depth does not change. It derives
    // from the condition that a free occurrence in a subpart of the formula cannot
    // change to become bound, which in its turn derives from the substitution
    // free-for condition.
    //
    // In
    //   u(𝛽𝑥 𝑃(𝑥, 𝑦), 𝛽𝑦 𝑃(𝑦, 𝑦))
    // A substitution [𝑥 ↦ 𝑦] or [𝑦 ↦ 𝑥] produces the same variable 𝑥 or 𝑦 in all
    // occurrences, causing the free occurrence of 𝑦 in 𝛽𝑥 𝑃(𝑥, 𝑦) to become bound,
    // which is illegal, so it is necessary for a check against this occurring.
    // The substitution [𝑥 ↦ 𝑦] leads to 𝑦[𝑥 ↦ 𝑦] in both formulas, but only in
    // 𝛽𝑥 𝑃(𝑥, 𝑦) it is a sign of an illegal variable change. In this case, 𝑥 is in the
    // bound variable table that is associated with 𝑦 and 𝛽𝑥 𝑃(𝑥, 𝑦). In 𝛽𝑦 𝑃(𝑦, 𝑦), 𝑥 is
    // not in this table. This is the first case:
    //   x[v ↦ f], where x ≡ f, depth v ≠ 0, depth x ≠ depth v.
    // The substitution [𝑦 ↦ 𝑥] leads to 𝑦[𝑦 ↦ 𝑥], but only in 𝛽𝑥 𝑃(𝑥, 𝑦) it is an
    // illegal subtitution. In this case, 𝑥 is in the bound variable table that is
    // associated with 𝑦 and 𝛽𝑥 𝑃(𝑥, 𝑦). In 𝛽𝑦 𝑃(𝑦, 𝑦), 𝑥 is
    // not in this table. This is the second case:
    //   x[v ↦ f], where x ≡ v, depth f ≠ 0, depth x ≠ depth f.
    // For explicit subtitutions, this is done by the free-for check.
    // If x ≡ v ≡ f, there is nothing to check, as the substitution is the identity.
    if (x->is_limited() && variable_->is_limited()) {

      size_type dx = x->get_depth(vt.table_);
      bool is_illegal = false;

      if (x == formula_) {
        size_type dv = variable_->get_depth(vt.table_);

        if (dv != 0 && dx != dv)
          is_illegal = true;
      }

      // For explicit substitutions, a free-for check instead of a change-of-variables check:

      if (is_illegal) {
        std::ostringstream oss;
        oss << "explicit_substitution::substitute_variable: Illegal variable change: "
          << variable_ << " ⤳ " << formula_ << " of " << x << *this;

        throw illegal_substitution(oss.str());
      }
    }


    // Now the substitution is explicit.

    // An explicit substitution 𝑨[𝑥 ⤇ 𝑓] only substitutes the free occurrences of 𝑥 in 𝑨; 𝑥 may
    // still be bound by being in the scope of binder of which this formula is a local part.
    // The function substitution_formula::substitute pushes a local level onto
    // the bound variables table, enabling a check for bindings within the scope of 𝑨.

    // In addition, an explicit substitution 𝑨[𝑥 ⤇ 𝑓] requires that 𝑓 is
    //  free for (substitutable at) 𝑥 in 𝑨

    // For an explicit substitution 𝑨[𝑥 ⤇ 𝑓], check 𝑓 free for (substitutable at) 𝑥 in 𝑨. Not free-for if
    // in 𝑥[𝑣 ⤇ 𝑓], 𝑥 ≡ 𝑣, 𝑓 contains a free variable 𝑦 that at the substitution point 𝑥
    // is in the scope of a binder β𝑦 that is part of 𝑨, that is, 𝑦 is a bound occurrence at 𝑥.
    // This occurs if 𝑦->local_find(vt.table_), which searches down to the bottom pushed
    // when 𝑨[𝑥 ⤇ 𝑓] was initiated in substitution_formula::substitute.

    if (x == variable_) {
      // Bound variable occurrences should not be substituted, as
      // explicit substitutions only substitued free variable occurrences:
      if (x->is_locally_bound(vt.table_))
        return x;

      // Check 𝑓 free for (substitutable at) 𝑥 in 𝑨:

      std::set<ref<variable>> fvs;   // Free variables of f.

      // If formula_ contains term variables t of the same type as x, then
      // the free-for metacondition is undefined, as it is unknown what variables t
      // will contain when eventually substituted, and must be converted to
      // a metacondition, y not free in t, where y is the set of in scope locally bound
      // object variables of the same type as x.
      // The function 'contains' return true, if formula_ contains a term variable.
      bool more = formula_->contains(fvs, occurrence::free);

      for (auto& i: fvs)
        if (i->is_locally_bound(vt.table_)) {
          std::ostringstream oss;
          oss << "explicit_substitution::substitute_variable: Substitution not free for: "
            << variable_ << " ⤳ " << formula_ << " of " << x << *this;
          throw illegal_substitution(oss.str());
        }


      if (!more)
        return formula_;  // Case formula_ does not contain non-limited variables:


      // Now formula_ contains non-limited variables, whose variable exclusion sets
      // must contain the bound variables in scope.


      // Add the bound variables in local scope at x, of the same type as x, to the
      // set of excluded variables of the non-limited variables of the same type as x.
      // These are variables that may later become bound by an eventual substitution.
      //
      // Currently the ordinary variables are same as the term variables, so they
      // should be included.
      // When ordinary variables only allow the substitutions permitted by the object
      // substitution rule 𝑨 ⊢⁽𝒙⁾ 𝑨[𝒙 ⤇ 𝒕], cf. Kleene p. 101, then they should not
      // have excluded variables. (Term variables admit any substitutions, and
      // must therefore be restricted by metaconditions.)

      std::set<ref<variable>> bvs; // Locally bound variables in scope at x.
      vt.table_->find_local(bvs);

      // Check that the excluded variables of the free variable of formula_ are
      // not bound at x:
      for (auto& i: fvs)
        for (auto& j: i->excluded_)
          if (bvs.find(j) != bvs.end()) {
            std::ostringstream oss;
            oss << "explicit_substitution::substitute_variable: Excluded variable "
              << j << " of " << i << " becoming bound in "
              << variable_ << " ⤳ " << formula_ << " of " << x << *this;

            throw illegal_substitution(oss.str());
          }


      variable_map var_map;

      for (auto& i: fvs)
        if (i->metatype_ != variable::limited_ && i->type_ == x->type_)
          for (auto& j: bvs)
            if (j->metatype_ == variable::limited_ && j->type_ == x->type_)
              var_map[i].insert(j);

      return formula_->add_exception_set(var_map);
    }

    // No substitution case, a delayed return if f can contain x after a future
    // eventual substitution, otherwise return f, i.e., no substitution made:

    ref<formula> r;

    // Delayed return here, if an undefined substitution (if say x is a
    // formula variable and variable_ is an object variable).
    // Can be accepted, if level numbers are unequal.
    if (x->may_contain(variable_)) {
      if (trace_value & trace_substitute) {
        std::lock_guard<std::recursive_mutex> guard(write_mutex);
        std::clog << "explicit_substitution::substitute_variable\n  "
          << "(" << x << ")" << *this << ", not free in ≕\n    ";
      }

      // Note that *this must now have is_explicit_ == true:
      r = ref<substitution_formula>(make, this, x);
    }
    else
      r = ref<formula>(x);

    if (trace_value & trace_substitute) {
      std::lock_guard<std::recursive_mutex> guard(write_mutex);
      std::clog << "explicit_substitution::substitute_variable return\n  "
        << "(" << x << ")" << *this << " =\n    "
        << r << std::endl;
    }

    return r;
  }


  alternatives explicit_substitution::unify_substitution2(const ref<formula>& x, unify_environment tx, const ref<formula>& y, unify_environment ty, database* dbp, level lv, degree_pool& sl, direction dr) const {

    if (trace_value & trace_unify) {
      std::lock_guard<std::recursive_mutex> guard(write_mutex);
      std::clog << "Begin explicit_substitution::unify_substitution2\n  "
        << "unify(" << x << *this << ", " << y << ").\n"
        << std::flush;
    }

    // Write 𝒙 ≔ variable_, 𝒕 = formula_, 𝑨 = x, 𝑩 = y. Then when unifying
    // u(𝑨[𝒙 ⤇ 𝒕], 𝑩), 𝑩 is split up in a set of disjoint subterms 𝝉 which may
    // be empty, and let 𝑩₍𝒙, 𝝉₎ denote 𝑩 where each of the terms of 𝝉 have been
    // replaced by 𝒙. Then, with cases checked in order:
    // If u(𝒕, 𝝉).u(𝒙, 𝒕) is non-empty, the return is u(𝒕, 𝝉).u(𝒙, 𝒕).u(𝑨, 𝑩)
    // If 𝑩 is a goal, the return is u(𝒕, 𝝉).[𝒙 ↦ '𝒙].u(𝑨, 𝑩)
    // Otherwise, the return is u(𝒕, 𝝉).u(𝑨, 𝑩).
    // Here, u(𝒙, 𝒕) is inserted to allow for 𝑨[𝒙 ⤇ 𝒚] when 𝒚 is limited to be reduced
    // to 𝑨[𝒙 ↦ 𝒚], that is, the variable used after substituion is 𝒚 and not 𝒙.
    // The unspecialization substitution [𝒙 ↦ '𝒙] is inserted in order to not lose
    // generality of the goal, otherwise say 𝑃(1, 2) can be proved from 𝑃(𝑥, 𝑥).
    // If the terms contain specializable variables, this is handled by the u(𝒕, 𝝉).
    // To this unification, there are added checks for change of variable
    // and free for (substitutability) consistency.

    // Unspecialize object variables in the body, which may or may not have
    // free and bound occurrences in the head as well.
    // Without it, it is possible to make false proofs via the specialization rule
    //   ∀𝒙 𝑨 ⊢ 𝑨[𝒙 ⤇ 𝒕]
    // A term of the unpecializable goal unifies with the term 𝒕, but if the
    // unpecializability is not carried over to 𝒙 in ∀𝒙 𝑨, the quantifier can be
    // removed by the generalization rule 𝑩 ⊢ ∀𝒚 𝑩, resulting in the originally
    // unspecializable variables becoming specializable. So, for example, 𝑷(𝒚, 𝒛)
    // can be proved from the axiom 𝑷(𝒙, 𝒙).

    split_formula sf = y->split(tx, variable_, formula_, ty, dbp, lv, sl, dr);

    if (trace_value & trace_unify) {
      std::lock_guard<std::recursive_mutex> guard(write_mutex);
      std::clog << "explicit_substitution::unify_substitution2 A\n  "
        << "unify(" << x << "[" << variable_ << " ↦ " << formula_ << "], " << y << "):\n"
        << sf << std::endl;
    }


    alternatives as; // Return value.

    for (auto& i: sf) {

      if (trace_value & trace_unify) {
        std::lock_guard<std::recursive_mutex> guard(write_mutex);

        std::clog << "explicit_substitution::unify_substitution2 B0\n  "
          << "unify(" << formula_ << ", " << std::get<0>(i) << ")."
          << std::endl;
      }

      alternatives as0 = mli::unify(formula_, tx, std::get<0>(i).formulas_, ty, dbp, lv, sl, dr);

      if (trace_value & trace_unify) {
        std::lock_guard<std::recursive_mutex> guard(write_mutex);

        std::clog << "explicit_substitution::unify_substitution2 B1\n  "
          << "unify(" << formula_ << ", " << std::get<0>(i) << ") ="
          << as0
          << std::endl;
      }


      if (as0.empty())
        continue;


      // Check that all non-limited variables of std::get<0>(i) have all variables
      // of std::get<2>(i) as exclusion variables.
      //
      // When ordinary variables have been implemented to only allow the substitutions
      // permitted by the object substitution rule 𝑨 ⊢⁽𝒙⁾ 𝑨[𝒙 ⤇ 𝒕], cf. Kleene p. 101,
      // then they should not have excluded variables, and "all non-limited variables"
      // above should be changed to "all term variables":
      // Term variables admit any substitutions, and must therefore be restricted
      // by metaconditions, which are put into the variable, as opposed to external
      // "not free in" conditions, allowing automation and quicker determination.

      // True if, for a limited variable, the occurrence is substitutable (free for)
      // or for a non-limited variable, exclusion set contains std::get<2>(i).
      // Otherwise, false, and break the loops, as the substitution is not valid.
      bool cont = true;

      if (!std::get<2>(i).empty()) // Nothing to check if std::get<2>(i) is empty.
        for (auto& j: std::get<0>(i).formulas_) {
          std::set<ref<variable>> fvs;
          j->contains(fvs, occurrence::free);

          for (auto& k: fvs) {

            if (k->is_limited()) {
              // This checks if k is substitutable (free for) at the current
              // substitution point, that is, it is not a bound occurrence, or
              // not in the set of bound variable occurrences std::get<2>(i).
              cont = !std::get<2>(i).contains(k);

              if (trace_value & trace_unify) {
                std::clog << "explicit_substitution::unify_substitution2:\n"
                  << "The variables occurrence " << k << " in\n" << y << " ≡ ("
                  << std::get<1>(i) << ")[" << variable_ << " ⤇ " << k << "]\n"
                  << (cont? "is free since not in " : "is not free since in ");

                for (auto& l: std::get<2>(i))
                  std::clog << l << " ";

                std::clog << std::endl;
              }

              if (!cont)
                break;
              else
                continue;
            }

            // This checks if the variable exclusion set of k contains the set of bound
            // variables in the current scope, which is the set std::get<2>(i).
            cont = std::includes(k->excluded_.begin(), k->excluded_.end(),
                std::get<2>(i).begin(), std::get<2>(i).end());

            if (trace_value & trace_unify) {
              std::clog << "explicit_substitution::unify_substitution2:\n"
                << "The set of excluded variables of " << k << " in\n" << y << " ≡ ("
                << std::get<1>(i) << ")[" << variable_ << " ⤇ " << k << "]\n"
                << (cont? "contains " : "does not contain ");

              for (auto& l: std::get<2>(i))
                std::clog << l << " ";

              std::clog << std::endl;
            }
          }

          if (!cont)
            break;
        }

      if (!cont)
        continue;

      // In u(𝑨[𝒙 ⤇ 𝑡], 𝑩), when 𝑡 unifies with a limited variable 𝑦 of 𝑩, this line
      // adds the substitution [𝒙 ⤇ 𝑦], so that the resulting substituted expression
      // will refer to 𝑦 and not 𝒙. Then in the specialization of the rule
      //   ∀𝒙 𝑨 ⊢ 𝑨[𝒙 ⤇ 𝑡]
      // the substituted quantified variable is 𝑦, not 𝒙.
      alternatives as1 = as0.unify(variable_, tx, formula_, ty, dbp, lv, sl, dr);

      if (trace_value & trace_unify) {
        std::lock_guard<std::recursive_mutex> guard(write_mutex);

        std::clog << "explicit_substitution::unify_substitution2\n  "
          << "unify(" << formula_ << ", " << std::get<0>(i) << ") as1 ="
          << as1
          << std::endl;
      }


      // If as1 is non-empty, then the substitution [𝒙 ↦ 𝑦], as described above, has been added.
      // If it is empty, and 𝑩 ≔ y is a goal, then the unspecialization substitution [𝒙 ↦ '𝒙]
      // should be added.
      if (!as1.empty())
        as0 = as1;
      else if (ty.target_ == goal) {
        ref<variable> v = ref<variable>(make, *variable_);
        v->unspecializable_ = true;

        ref<substitution> s = ref<variable_substitution>(make, variable_, v);

        as0 = as0 * s;
      }

      // This is u(𝑨, 𝑩) of u(𝑨[𝒙 ⤇ 𝑡], 𝑩).
      alternatives as2 = as0.unify(x, tx, std::get<1>(i), ty, dbp, lv, sl, dr);


      if (trace_value & trace_unify) {
        std::lock_guard<std::recursive_mutex> guard(write_mutex);
        std::clog << "explicit_substitution::unify_substitution2 Q\n  "
          << "unify(" << x << *this << ", " << y << "):\n"
          << "as0 = " << as0 << "\n"
          << "as2 = " << as2 << "\n"
          << std::endl;
      }

      as = as.append(as2);
    }


    if (trace_value & trace_unify) {
      std::lock_guard<std::recursive_mutex> guard(write_mutex);
      std::clog << "explicit_substitution::unify_substitution2\n  "
        << "unify(" << x << *this << ", " << y << "):"
        << as << std::endl;
    }

    return as;
  }


  void explicit_substitution::set_bind(bind& b, name_variable_table& vs) {
    variable_->set_bind(b, vs);
    formula_->set_bind(b, vs);
  }


  ref<formula> explicit_substitution::rename(level lv, degree sl) const {
    ref<explicit_substitution> mp(make, *this);
    mp->variable_ = variable_->rename(lv, sl);
    mp->formula_ = formula_->rename(lv, sl);
    return mp;
  }


  ref<formula> explicit_substitution::add_exception_set(variable_map& vm) const {
    ref<explicit_substitution> mp(make, *this);
    mp->variable_ = variable_->add_exception_set(vm);
    mp->formula_ = formula_->add_exception_set(vm);
    return mp;
  }


  kleenean explicit_substitution::has(const ref<variable>& v, occurrence oc) const {
    kleenean k1 = variable_->has(v, oc);
    if (k1 == true)  return true;

    kleenean k2 = formula_->has(v, oc);

    return k1 || k2;
  }


  void explicit_substitution::contains(std::set<ref<variable>>& s, std::set<ref<variable>>& bs, bool& more, occurrence oc) const {
    variable_->contains(s, bs, more, oc);
    formula_->contains(s, bs, more, oc);
  }


  kleenean explicit_substitution::free_for(const ref<formula>& f, const ref<variable>& x,
    std::set<ref<variable>>& s, std::list<ref<variable>>& bs) const {
    kleenean k1 = variable_->free_for(f, x, s, bs);
    if (k1 == false)  return false;
    kleenean k2 = formula_->free_for(f, x, s, bs);
    return k1 && k2;
  }


  void explicit_substitution::unspecialize(depth x, bool y) {
    variable_->unspecialize(x, y);
    formula_->unspecialize(x, y);
  }


  void explicit_substitution::unspecialize(std::set<ref<variable>>& vs, bool b) {
    variable_->unspecialize(vs, b);
    formula_->unspecialize(vs, b);
  }


  ref<formula> explicit_substitution::substitute(const ref<substitution>& s, substitute_environment vt) const {
    ref<formula> v0 = variable_->substitute(s, vt);

    variable* vp = ref_cast<variable*>(v0);
    if (vp == 0)
      throw illegal_substitution("In explicit_substitution::substitute, substitution of variable not a variable.");

    ref<explicit_substitution> mp(make, *this);
    mp->variable_ = vp;
    mp->formula_ = formula_->substitute(s, vt);

    return mp;
  }


  alternatives explicit_substitution::unify(unify_environment tt, const ref<formula>& x, unify_environment tx, database* dbp, level lv, degree_pool& sl, direction dr) const {
    if (trace_value & trace_unify) {
      std::lock_guard<std::recursive_mutex> guard(write_mutex);
      std::clog << "explicit_substitution::unify(\n  " << *this << ";\n  " << x << ")\n" << std::flush;
    }

    explicit_substitution* xp = ref_cast<explicit_substitution*>(x);
    if (xp == 0)  return O;
    alternatives as = mli::unify(ref<formula>(variable_), tt, ref<formula>(xp->variable_), tx, dbp, lv, sl, dr);
    return as.unify(formula_, tt, xp->formula_, tx, dbp, lv, sl, dr);
  }


  struct explicit_substitution_construct {
    ref<variable> variable_;

    explicit_substitution_construct(const ref<variable>& v)
     : variable_(v) {}

    ref<formula> operator()(const ref<formula>& x) const {
      return ref<explicit_substitution>(make, variable_, x);
    }
  };


  split_formula explicit_substitution::split(unify_environment tg,
    const ref<variable>& x, const ref<formula>& t, unify_environment tt, database* dbp, level lv, degree_pool& sl, direction dr) const {
    split_formula sf(this);  // Return value.
    // If t and *this unify, then *this can be replaced by x:
    alternatives as = mli::unify(t, tt, this, tg, dbp, lv, sl, dr);

    if (!as.empty())
      sf.push_back(this, ref<formula>(x), tt.table_->find_local());

    sf.append(mli::split(formula_, tg, explicit_substitution_construct(variable_), x, t, tt, dbp, lv, sl, dr));

    return sf;
  }


  ref<substitution> explicit_substitution::innermost() const {
    return this;
  }


  ref<substitution> explicit_substitution::without() const {
    return ref<substitution>(make);
  }


  ref<substitution> explicit_substitution::outermost() const {
    return this;
  }


  ref<substitution> explicit_substitution::within() const {
    return ref<substitution>(make);
  }


  order explicit_substitution::compare(const unit& x) const {
    auto& xr = dynamic_cast<const explicit_substitution&>(x);
#if (__cplusplus > 201703L) // C++20
    order c = variable_ <=> xr.variable_;
    if (c != equal)  return c;
    return formula_ <=> xr.formula_;
#else
    order c = mli::compare(variable_, xr.variable_);
    if (c != equal)  return c;
    return mli::compare(formula_, xr.formula_);
#endif
  }


  void explicit_substitution::write(std::ostream& os, write_style ws) const {

    // Remove if bind_ numbers not written in threads.
    std::lock_guard<std::recursive_mutex> guard(write_mutex);

    bool write_reverse = write_substitution_mapto_reverse & ws;
    os << "[";

    if (write_reverse)
      os << formula_ << " ⤆ " << variable_;
    else {
      os << variable_ << " ⤇ ";
      if (formula_->empty()) os <<  "⦰";
      else os << formula_;
    }


    os << "]";
  }


  ref<formula> substitution_composition::substitute_variable(const ref<variable>& x, substitute_environment vt) const {
    return (inner_->substitute_variable(x, vt))->substitute(outer_, vt);
  }


  void substitution_composition::set_bind(bind& b, name_variable_table& vs) {
    inner_->set_bind(b, vs);  
    outer_->set_bind(b, vs);  
  }


  ref<formula> substitution_composition::rename(level lv, degree sl) const {
    ref<substitution_composition> mp(make, *this);
    mp->inner_ = inner_->rename(lv, sl);
    mp->outer_ = outer_->rename(lv, sl);
    return mp;
  }


  ref<formula> substitution_composition::add_exception_set(variable_map& vm) const {
    ref<substitution_composition> mp(make, *this);
    mp->inner_ = inner_->add_exception_set(vm);
    mp->outer_ = outer_->add_exception_set(vm);
    return mp;
  }


  kleenean substitution_composition::has(const ref<variable>& v, occurrence oc) const {
    kleenean k1 = inner_->has(v, oc);
    if (k1 == true)  return true;

    kleenean k2 = outer_->has(v, oc);

    return k1 || k2;
  }


  void substitution_composition::contains(std::set<ref<variable>>& s, std::set<ref<variable>>& bs, bool& more, occurrence oc) const {
    inner_->contains(s, bs, more, oc);
    outer_->contains(s, bs, more, oc);
  }


  kleenean substitution_composition::free_for(const ref<formula>& f, const ref<variable>& x,
    std::set<ref<variable>>& s, std::list<ref<variable>>& bs) const {
    kleenean k1 = inner_->free_for(f, x, s, bs);
    if (k1 == false)  return false;

    kleenean k2 = outer_->free_for(f, x, s, bs);

    return k1 && k2;
  }


  void substitution_composition::unspecialize(depth x, bool y) {
    inner_->unspecialize(x, y);
    outer_->unspecialize(x, y);  
  }


  void substitution_composition::unspecialize(std::set<ref<variable>>& vs, bool b) {
    inner_->unspecialize(vs, b);
    outer_->unspecialize(vs, b);
  }


  ref<formula> substitution_composition::substitute(const ref<substitution>& s, substitute_environment vt) const {
    ref<substitution_composition> mp(make, *this);
    mp->inner_ = ref<substitution>(inner_->substitute(s, vt));
    mp->outer_ = ref<substitution>(outer_->substitute(s, vt));
    return mp;
  }


  alternatives substitution_composition::unify(unify_environment tt, const ref<formula>& x, unify_environment tx, database* dbp, level lv, degree_pool& sl, direction dr) const {
    if (trace_value & trace_unify) {
      std::lock_guard<std::recursive_mutex> guard(write_mutex);
      std::clog << "substitution_composition::unify(\n  " << *this << ";\n  " << x << ")\n" << std::flush;
    }

    substitution_composition* xp = ref_cast<substitution_composition*>(x);
    if (xp == 0)  return O;
    alternatives as = mli::unify(ref<formula>(inner_), tt, ref<formula>(xp->inner_), tx, dbp, lv, sl, dr);
    return as.unify(ref<formula>(outer_), tt, ref<formula>(xp->outer_), tx, dbp, lv, sl, dr);  
  }


  struct composition_construct {
    ref<formula> operator()(const ref<formula>& x, const ref<formula>& y) const {
      return ref<substitution_composition>(make, ref<substitution>(x), ref<substitution>(y));
    }
  };


  split_formula substitution_composition::split(unify_environment tg,
    const ref<variable>& x, const ref<formula>& t, unify_environment tt, database* dbp, level lv, degree_pool& sl, direction dr) const {
    split_formula sf(this);  // Return value.
    // If t and *this unify, then *this can be replaced by x:
    alternatives as = mli::unify(t, tt, this, tg, dbp, lv, sl, dr);

    if (!as.empty())
      sf.push_back(this, ref<formula>(x), tt.table_->find_local());

    sf.append(mli::split(ref<formula>(outer_), ref<formula>(inner_), tg, composition_construct(), x, t, tt, dbp, lv, sl, dr));
    return sf;
  }


  ref<substitution> substitution_composition::innermost() const {
    return inner_->innermost();
  }


  ref<substitution> substitution_composition::without() const {
    ref<substitution> s = inner_->without();
    if (s->is_identity())
      return outer_;
    return ref<substitution_composition>(make, outer_, s);
  }


  ref<substitution> substitution_composition::outermost() const {
    return outer_->outermost();
  }


  ref<substitution> substitution_composition::within() const {
    ref<substitution> s = outer_->within();
    if (s->is_identity())
      return inner_;
    return ref<substitution_composition>(make, s, inner_);
  }


  order substitution_composition::compare(const unit& x) const {
    auto& xr = dynamic_cast<const substitution_composition&>(x);
#if (__cplusplus > 201703L) // C++20
    return {inner_ <=> xr.inner_, outer_ <=> xr.outer_};
#else
    order c = mli::compare(inner_, xr.inner_);
    if (c != equal)  return c;
    return mli::compare(outer_, xr.outer_);
#endif
  }


  void substitution_composition::write(std::ostream& os, write_style ws) const {
    bool write_reverse = write_substitution_composition_reverse & ws;
    if (write_reverse)
      os << outer_ << " o " << inner_;
    else
      os << inner_ << outer_;
  }


  ref<substitution> operator*(const ref<substitution>& inner, const ref<substitution>& outer) {
#if 1 // debug.hh
    if (inner->is_identity())  return outer;
    if (outer->is_identity())  return inner;
#endif
    return ref<substitution_composition>(make, outer, inner);
  }


  formula_type substitution_formula::get_formula_type() const {
    return formula_->get_formula_type();
  }


  void substitution_formula::set_bind(bind& b, name_variable_table& t) {
    substitution_->set_bind(b, t);
    formula_->set_bind(b, t);
  }


  ref<formula> substitution_formula::rename(level lv, degree sl) const {
    ref<substitution_formula> sfp(make, *this);
    sfp->substitution_ = substitution_->rename(lv, sl);
    sfp->formula_ = formula_->rename(lv, sl);
    return sfp;
  }


  ref<formula> substitution_formula::add_exception_set(variable_map& vm) const {
    ref<substitution_formula> sfp(make, *this);
    sfp->substitution_ = substitution_->add_exception_set(vm);
    sfp->formula_ = formula_->add_exception_set(vm);
    return sfp;
  }


  kleenean substitution_formula::has(const ref<variable>& v, occurrence oc) const {
    // If v is substituted by substitution_:
    // If oc == free: return false
    // if oc = bound: if substitution_ on v is all occurances, return false.
    kleenean k1 = substitution_->has(v, oc);
    if (k1 == true)  return true;

    kleenean k2 = formula_->has(v, oc);

    return k1 || k2;
  }


  void substitution_formula::contains(std::set<ref<variable>>& vs, std::set<ref<variable>>& bs, bool& more, occurrence oc) const {
    substitution_->contains(vs, bs, more, oc);
    formula_->contains(vs, bs, more, oc);
  }


  kleenean substitution_formula::free_for(const ref<formula>& f, const ref<variable>& x,
      std::set<ref<variable>>& s, std::list<ref<variable>>& bs) const {
    kleenean k1 = substitution_->free_for(f, x, s, bs);
    if (k1 == false)  return false;
    kleenean k2 = formula_->free_for(f, x, s, bs);
    return k1 && k2;
  }


  void substitution_formula::unspecialize(depth x, bool y) {
    substitution_->unspecialize(x, y);
    formula_->unspecialize(x, y);
  }


  void substitution_formula::unspecialize(std::set<ref<variable>>& vs, bool b) {
    substitution_->unspecialize(vs, b);
    formula_->unspecialize(vs, b);
  }


  ref<formula> substitution_formula::substitute(const ref<substitution>& s, substitute_environment vt) const {
    if (trace_value & trace_substitute) {
      std::lock_guard<std::recursive_mutex> guard(write_mutex);
      std::clog
       << "Begin substitution_formula::substitute:\n  " << *this
       << ".substitute(" << s << ")"
       << std::endl;
    }

    // First apply the unification substitution s to *this, then evaluate the
    // explicit substitution formula with free-for checks:

    // Push a bottom, used for free-for checks, which pops when the element bg expires:
    bottom_guard bg(*vt.table_);

    ref<formula> f1 = formula_->substitute(s, vt);
    ref<substitution> s1 = substitution_->substitute(s, vt);

    ref<formula> fr;

    fr = f1->substitute(s1, vt);

    if (trace_value & trace_substitute) {
      std::lock_guard<std::recursive_mutex> guard(write_mutex);
      std::clog
       << "End substitution_formula::substitute:\n  " << *this
       << ".substitute(" << s << "):\n    "
       << fr
       << std::endl;
    }

    return fr;
  }


  alternatives substitution_formula::unify(unify_environment tt, const ref<formula>& x, unify_environment tx, database* dbp, level lv, degree_pool& sl, direction dr) const {
    if (trace_value & trace_unify) {
      std::lock_guard<std::recursive_mutex> guard(write_mutex);
      std::clog
       << "substitution_formula::unify(\n  " << *this << ";\n  " << x << ")"
       << std::endl;
    }

    substitution_formula* xp = ref_cast<substitution_formula*>(x);

    if (xp == nullptr)
      // u(A[x.t], B) type 2 solutions. Case u(A, B[y.u]) is handled
      // in mli::unify by reversing arguments to arrive here.
      return unify2(tt, x, tx, dbp, lv, sl, dr);

    // u(A[x.t], B[y.u]):

    alternatives as;

#if !DEBUG_SUBSTITUTION_FORMULA_UNIFY
    // u(A[x.t], B[y.u]) type 1 solution u(x, y) u(t, u) u(A, B).
    as = as.append(unify1(tt, *xp, tx, dbp, lv, sl, dr));
#if 0
    // u(A[x.t], B) type 2 solutions:
    as = as.append(unify2(tt, x, tx, dbp, lv, sl, dr));

    // u(A, B[y.u]) type 2 solutions:
    as = as.append(xp->unify2(tx, this, tt, dbp, lv, sl, !dr));
#endif
#else
    // u(A, B[y.u]) type 2 solutions:
    as = as.append(xp->unify2(tx, this, tt, dbp, lv, sl, !dr));
#endif
    return as;
  }


  // Type 1: 𝐮(𝑨[𝒙 ⤇ 𝒕], 𝑩[𝒚 ⤇ 𝒖]) = 𝐮(𝒙, 𝒚).𝐮(𝑨, 𝑩).𝐮(𝒕, 𝒖).
  alternatives substitution_formula::unify1(unify_environment tt, const substitution_formula& sf, unify_environment tx, database* dbp, level lv, degree_pool& sl, direction dr) const {
    if (trace_value & trace_unify) {
      std::lock_guard<std::recursive_mutex> guard(write_mutex);
      std::clog
       << "substitution_formula::unify(\n  "
       << *this << ";\n  " << sf << ") ="
       << std::endl;
    }

    alternatives as;

    // In the formulas 𝑨[𝒙 ⤇ 𝒕], 𝑩[𝒚 ⤇ 𝒖], the variables 𝒙, 𝒚 are bound, and 𝑨, 𝑩 are
    // in the scope of their respective explicit substitution operator, so therefore
    // push_bound is used to add the variables to their respective bound variables table.
    // By contrast, 𝒕, 𝒖 are not in the scope of this binding operator, so the environment
    // with push_bound is expired before these are unified.

    // Elements popped when the syntactic environment expires:
    {
    push_bound p0(tt);
    tt.table_->insert(substitution_->variable_);

    push_bound p1(tx);
    tx.table_->insert(sf.substitution_->variable_);

    as = mli::unify(substitution_->variable_, tt, sf.substitution_->variable_, tx, dbp, lv, sl, dr);
    as = as.unify(formula_, tt, sf.formula_, tx, dbp, lv, sl, dr);
    }
    // The syntactic environment for push_bound expires here, implemented so as
    // formula_ and sf.formula_ are not in the scope of the binding operator.

    as = as.unify(substitution_->formula_, tt, sf.substitution_->formula_, tx, dbp, lv, sl, dr);

    if (trace_value & trace_unify) {
      std::lock_guard<std::recursive_mutex> guard(write_mutex);
      std::clog
       << "substitution_formula::unify(\n  "
       << *this << ";\n  " << sf << ") ="
       << as
       << std::endl;
    }

    return as;
  }


  alternatives substitution_formula::unify2(unify_environment tt, const ref<formula>& x, unify_environment tx, database* dbp, level lv, degree_pool& sl, direction dr) const {
    // u(A[x.t], B) type 2 solutions:
    return substitution_->unify_substitution2(formula_, tt, x, tx, dbp, lv, sl, dr);
  }


  struct substitution_formula_construct {
    ref<formula> operator()(const ref<formula>& x, const ref<formula>& y) const {
      return ref<substitution_formula>(make, ref<substitution>(x), y);
    }
  };


  split_formula substitution_formula::split(unify_environment tg,
    const ref<variable>& x, const ref<formula>& t, unify_environment tt, database* dbp, level lv, degree_pool& sl, direction dr) const {
    split_formula sf(this);  // Return value.
#if !DEBUG_SUBSTITUTION_FORMULA_UNIFY
    // If t and *this unify, then *this can be replaced by x:
    alternatives as = mli::unify(t, tt, this, tg, dbp, lv, sl, dr);

    if (!as.empty())
      sf.push_back(this, ref<formula>(x), tt.table_->find_local());
#endif
    sf.append(mli::split(ref<formula>(substitution_), formula_, tg, substitution_formula_construct(), x, t, tt, dbp, lv, sl, dr));
    return sf;
  }


  order substitution_formula::compare(const unit& x) const {
    auto& xr = dynamic_cast<const substitution_formula&>(x);
#if (__cplusplus > 201703L) // C++20
    order c = substitution_ <=> xr.substitution_;
    if (c != equal)  return c;
    return formula_ <=> xr.formula_;
#else
    order c = mli::compare(substitution_, xr.substitution_);
    if (c != equal)  return c;
    return mli::compare(formula_, xr.formula_);
#endif
  }


  precedence_t substitution_formula::precedence() const {
    return substitution_formula_oprec;
  }


  void substitution_formula::write(std::ostream& os, write_style ws) const {
      bool do_bracket = precedence().argument(first, formula_->precedence());

      if (do_bracket) os << "(";
      formula_->write(os, ws);
      if (do_bracket) os << ")";

      os << substitution_;
  }


  alternative& alternative::label(const ref<statement>& ls, level lv) {
#if NEW_PROVED
    labelstatements_[lv.sub].statement_ = ls;
#else
    labelstatements_[lv.sub].first = ls;
#endif

    return *this;
  }


  alternative& alternative::label(const ref<statement>& ls, level lv, degree sl) {
#if NEW_PROVED
    labelstatements_[lv.sub].definitions_.push_back(ls);
#else
    labelstatements_[lv.sub].second.push_back(ls);
#endif

    return *this;
  }


  void alternative::write(std::ostream& os, write_style ws) const {
    if (!(ws & write_statement)) {
      bool it0 = true;
      for (auto& i: labelstatements_) {
        if (it0)  it0 = false;
        else  os << "; ";

#if NEW_PROVED
        i.second.statement_->write(os, ws);

        if (!i.second.definitions_.empty()) {
          os << "₍";

          bool it0 = true;

          for (auto& j: i.second.definitions_) {
            if (it0) it0 = false;
            else     os << ", ";

            j->write(os, ws);
          }

          os << "₎";
        }

        if (!i.second.substatements_.empty()) {
          os << "⁽";

          bool it0 = true;

          for (auto& j: i.second.substatements_) {
            if (it0) it0 = false;
            else     os << ", ";

            j->write(os, ws);
          }

          os << "⁾";
        }
#else
        i.second.first->write(os, ws);

        for (auto& j: i.second.second) {
          os << ", ";
          j->write(os, ws);
        }
#endif
      }

      return;
    }

#if NEW_PROVED
    for (auto& i: labelstatements_) {
      if (!i.second.statement_->empty()) {
        i.second.statement_->write(os, write_style(write_name | write_type | write_statement | tabs2));
        os << "\n";
      }

      for (auto& j: i.second.definitions_) {
        if (!j->empty()) {
          j->write(os, write_style(write_name | write_type | write_statement | tabs2));
          os << "\n";
        }
      }

      if (!i.second.substatements_.empty())
        os << "Substatement section:\n";

      for (auto& j: i.second.substatements_) {
        if (!j->empty()) {
          j->write(os, write_style(write_name | write_type | write_statement | tabs2));
          os << "\n";
        }
      }
    }
#else
    for (auto& i: labelstatements_) {
      if (!i.second.first->empty()) {
        i.second.first->write(os, write_style(write_name | write_type | write_statement | tabs2));
        os << "\n";
      }

      for (auto& j: i.second.second) {
        if (!j->empty()) {
          j->write(os, write_style(write_name | write_type | write_statement | tabs2));
          os << "\n";
        }
      }
    }
#endif

    substitution_->write(os, ws);

    if (!goal_->empty()) {
      os << "\n∴ ";
      goal_->write(os, ws);
    }

    if (!unifier_->empty()) {
      os << "\n      unifier: ";
      unifier_->write(os, ws);
    }
  }


  alternative operator*(const alternative& x, const alternative& y) {
    if (trace_value & trace_unify) {
      std::lock_guard<std::recursive_mutex> guard(write_mutex);
      std::clog
       << "alternative *(\n  "
       << x << ";\n  "
       << y << ")"
       << std::endl;

      if (!x.goal_->empty() && !y.goal_->empty())
        std::clog << std::flush;
    }

    alternative a;

    a.substitution_ = x.substitution_ * y.substitution_;

    // Dictated by use in alternatives::unify(const ref<formula>&):
    a.unifier_ = (*y.substitution_)(x.unifier_);

    // If the statement labels are inserted into a sequencetial container, then x should
    // be inserted before y, but as an associative container is used here, the
    // order does not matter from the functional point of view, but lists definitions
    // in the order they are used in 'unify'.

    a.labelstatements_ = x.labelstatements_;

#if NEW_PROVED
    for (auto& i: y.labelstatements_) {
      // Only insert if statement label is non-empty:
      a.labelstatements_[i.first].statement_ = i.second.statement_;

      // Currently permits definition duplicates:
      auto it1 = a.labelstatements_[i.first].definitions_.end();
      a.labelstatements_[i.first].definitions_.insert(it1, i.second.definitions_.begin(), i.second.definitions_.end());

      // Permits substatement duplicates:
      a.labelstatements_[i.first].substatements_.insert(a.labelstatements_[i.first].substatements_.end(),
        i.second.substatements_.begin(), i.second.substatements_.end());
    }
#else
    for (auto& i: y.labelstatements_) {
      // Only insert if statement label is non-empty:
      a.labelstatements_[i.first].first = i.second.first;

      // Currently permits definition duplicates:
      auto it1 = a.labelstatements_[i.first].second.end();
      a.labelstatements_[i.first].second.insert(it1, i.second.second.begin(), i.second.second.end());
    }
#endif

    // Forward goal concatenation order:
    // The order of the goals are preserved here: the old x.goal_ followed by the new
    // y.goal_, with the new subtitution y.substitution_ applied to the old goal x.goal_.
    a.goal_ = concatenate((*y.substitution_)(x.goal_), y.goal_);

    return a;
  }

  alternative alternative::add_goal(const ref<formula>& x) const {
    if (trace_value & trace_unify) {
      std::lock_guard<std::recursive_mutex> guard(write_mutex);
      std::clog
       << "alternative::add_goal(\n  "
       << *this << ";\n  "
       << x << ")"
       << std::endl;
    }

#if NEW_PROVED
    if (x->provable())
      return *this;
#else
    if (x->empty())
      return *this;
#endif

    alternative a = *this;

    a.goal_ = goal_->add_goal((*substitution_)(x));

    return a;

  }


  // Add the premise x to the body of goal_, turning the latter
  // into an inference, if not alredy of that form.
  alternative alternative::add_premise(const ref<formula>& x, metalevel_t ml,
      const varied_type& vs, const varied_type& vrs) const {
    if (trace_value & trace_unify) {
      std::lock_guard<std::recursive_mutex> guard(write_mutex);
      std::clog
       << "alternative::add_premise(\n  "
       << *this << ";\nx = "
       << x << ")"
       << std::endl;
    }

    if (x->provable())  return *this;

    alternative a = *this;

    a.goal_ = goal_->add_premise((*substitution_)(x), ml, vs, vrs);

    return a;
  }


  // Implementation of class alternatives:

  const alternatives O = alternatives();
  const alternatives I = alternative();


  alternatives& alternatives::label(const ref<statement>& ls, level lv) {
    for (auto& i: alternatives_)
      i = i.label(ls, lv);
    return *this;
  }


  alternatives& alternatives::label(const ref<statement>& ls, level lv, degree sl) {
    for (auto& i: alternatives_)
      i = i.label(ls, lv, sl);
    return *this;
  }


  alternatives& alternatives::push_back(const alternative& a) {
    alternatives_.push_back(a);
    return *this;
  }


  alternatives& alternatives::append(const alternatives& as) {
    alternatives_.insert(alternatives_.end(), as.alternatives_.begin(), as.alternatives_.end());
    return *this;
  }


  alternatives alternatives::add_goal(const ref<formula>& x) const {
#if NEW_PROVED
    if (x->provable())
      return *this;
#else
    if (x->empty())
      return *this;
#endif

    alternatives as;

    for (auto& i: *this) {
     // An illegal substitution, which may throw an exception in alternative::add_goal,
     // merely produces no alternative, but the alternatives search loop continues:
      try {
        as.push_back(i.add_goal(x));
      }
      catch (illegal_substitution& ex) {
        if (trace_value & trace_unify)
          std::clog << ex.what() << std::endl;
      }
    }

    return as;
  }


  alternatives alternatives::add_premise(const ref<formula>& x, metalevel_t ml,
      const varied_type& vs, const varied_type& vrs) const {

    if (x->provable())  return *this;

    alternatives as;

    for (auto& i: *this)
      as.push_back(i.add_premise(x, ml, vs, vrs));

    return as;
  }


#define WRITE_TABLE 0

  alternatives alternatives::unify(const ref<formula>& x, unify_environment tx, const ref<formula>& y, unify_environment ty, database* dbp, level lv, degree_pool& sl, direction dr, expansion ex) const {

#if WRITE_TABLE
    {
      std::lock_guard<std::recursive_mutex> guard(write_mutex);

      std::clog << "A: alternatives::unify(\n  "
        << "("  << x << ", " << y << ")" << ".\n"
        << std::flush;

      std::clog << "tx: \n";

      if (tx.table_ != 0) {
        variable_table::stack::iterator i,
          i0 = tx.table_->table_stack_.begin(), i1 = tx.table_->table_stack_.end();
        if (i0 != i1) {
          std::clog << "Variable table:\n";
          for (i = i0; i != i1; ++i) {
            if (i != i0)  std::clog << "\n";
            variable_table::table::iterator j, j0 = i->begin(), j1 = i->end();
            for (j = j0; j != j1; ++j) {
              if (j != j0)  std::clog << ", ";
              std::clog << "(" << j->first << ";" << j->second << ")";
            }
          }
          std::clog << std::endl;
        }
      }

      std::clog << "ty: \n";

      if (ty.table_ != 0) {
        variable_table::stack::iterator i,
          i0 = ty.table_->table_stack_.begin(), i1 = ty.table_->table_stack_.end();
        if (i0 != i1) {
          std::clog << "Variable table:\n";
          for (i = i0; i != i1; ++i) {
            if (i != i0)  std::clog << "\n";
            variable_table::table::iterator j, j0 = i->begin(), j1 = i->end();
            for (j = j0; j != j1; ++j) {
              if (j != j0)  std::clog << ", ";
              std::clog << "(" << j->first << ";" << j->second << ")";
            }
          }
          std::clog << std::endl;
        }
      }

    }
#endif

    alternatives as;

    for (auto& i: alternatives_) {
      ref<substitution> s = i.substitution_;
#if WRITE_TABLE
      std::clog << "s: " << s << std::endl;
#endif
      unify_environment tx1 = tx;
      unify_environment ty1 = ty;

#if 0
      // Substitute tables tx, ty by s.
      if (tx.table_ != 0) {
        unify_environment::table_type* txp = new unify_environment::table_type();
#if TABLE_DEBUG
        txp->table_stack_.resize(tx1.table_->size());

        variable_table::stack::iterator i,
          i0 = tx.table_->table_stack_.begin(), i1 = tx.table_->table_stack_.end(),
          j, j0 = txp->table_stack_.begin(), j1 = txp->table_stack_.end();

        for (i = i0, j = j0; i != i1; ++i, ++j)
          for (auto& k: *i) {
#if WRITE_TABLE
            std::clog << "C: " << k.first << ", " << s(k.first) << std::endl;
#endif
            j->insert({s(k.first), s(k.second)});
          }

        tx1.table_ = txp;
#endif
      }


      if (ty.table_ != 0) {
        unify_environment::table_type* typ = new unify_environment::table_type();
#if TABLE_DEBUG
        typ->table_stack_.resize(ty1.table_->size());

        variable_table::stack::iterator i,
          i0 = ty.table_->table_stack_.begin(), i1 = ty.table_->table_stack_.end(),
          j, j0 = typ->table_stack_.begin(), j1 = typ->table_stack_.end();

        for (i = i0, j = j0; i != i1; ++i, ++j)
          for (auto& k: *i) {
#if WRITE_TABLE
            std::clog << "D: " << k.first << ", " << s(k.first) << std::endl;
#endif
            j->insert({s(k.first), s(k.second)});
          }

        ty1.table_ = typ;
#endif
      }
#endif

#if WRITE_TABLE
    {
      std::lock_guard<std::recursive_mutex> guard(write_mutex);

      std::clog << "B: alternatives::unify(\n  "
        << "("  << x << "," << y << ")" << ".\n"
        << std::flush;

      std::clog << "tx1: \n";

      if (tx1.table_ != 0) {
        variable_table::stack::iterator i,
          i0 = tx1.table_->table_stack_.begin(), i1 = tx1.table_->table_stack_.end();
        if (i0 != i1) {
          std::clog << "Variable table:\n";
          for (i = i0; i != i1; ++i) {
            if (i != i0)  std::clog << "\n";
            variable_table::table::iterator j, j0 = i->begin(), j1 = i->end();
            for (j = j0; j != j1; ++j) {
              if (j != j0)  std::clog << ", ";
              std::clog << "(" << j->first << ";" << j->second << ")";
            }
          }
          std::clog << std::endl;
        }
      }

      std::clog << "ty1: \n";

      if (ty1.table_ != 0) {
        variable_table::stack::iterator i,
          i0 = ty1.table_->table_stack_.begin(), i1 = ty1.table_->table_stack_.end();
        if (i0 != i1) {
          std::clog << "Variable table:\n";
          for (i = i0; i != i1; ++i) {
            if (i != i0)  std::clog << "\n";
            variable_table::table::iterator j, j0 = i->begin(), j1 = i->end();
            for (j = j0; j != j1; ++j) {
              if (j != j0)  std::clog << ", ";
              std::clog << "(" << j->first << ";" << j->second << ")";
            }
          }
          std::clog << std::endl;
        }
      }

    }
#endif

     // An illegal substitution merely produces no alternative, but the search loop continues:
      try {
        alternatives bs = mli::unify(
          // Check use of tx/tx1, ty/ty1:
#if 1
          // The unification varied variables are substituted so that they come out correctly
          // in formula_sequence::unify:
          x->substitute(s, tx), tx.substitute(s), y->substitute(s, ty), ty.substitute(s), dbp, lv, sl, dr, ex);
#else
          x->substitute(s, tx), tx, y->substitute(s, ty), ty, dbp, lv, sl, dr, ex);
#endif

          as.append(i * bs);
      }
      catch (illegal_substitution& ex) {
        if (trace_value & trace_unify)
          std::clog << ex.what() << std::endl;
      }

    }

    return as;
  }


  alternatives alternatives::unify_binder(
      const ref<formula>& x, unify_environment tx,
      const ref<formula>& y, unify_environment ty,
      database* dbp, level lv, degree_pool& sl, direction dr) const {

    alternatives as;

    for (auto& i: alternatives_) {
      ref<substitution> s = i.substitution_;
      alternatives bs = mli::unify(
        x->substitute(s, tx), tx, y->substitute(s, ty), ty, dbp, lv, sl, dr);

      // Only add the condition here, not the substitution, as the bound
      // variables do not unify themselves:
      as.append(bs.add_goal(i.goal_));
    }

    return as;
  }


  alternatives alternatives::unifier(const ref<formula>& x) const {
    alternatives as;

    for (auto& i: alternatives_) {
      alternative a = i;
      a.unifier_ = (*i.substitution_)(x);
      as.push_back(a);
    }

    return as;
  }


  alternatives alternatives::unify(unify_environment tt, const ref<formula>& y, unify_environment ty, database* dbp, level lv, degree_pool& sl) const {
    alternatives as;


    for (auto& i: alternatives_)
      as.append(i * mli::unify(i.unifier_, tt, (*i.substitution_)(y), ty, dbp, lv, sl));

    return as;
  }


  void alternatives::write(std::ostream& os, write_style ws) const {
    if (empty()) { os << "\n    no solutions."; return; }

    bool it0 = true;
    for (auto& i: alternatives_) {
      if (i.labelstatements_.empty()) {
        if (it0) { it0 = false; os << "\n    "; }
        else          os << "\n  & ";
      } else {
        if (it0) { it0 = false; os << "\n"; }
        else          os << "\n &\n";
      }

      i.write(os, ws);
    }
  }


  alternatives operator*(const alternatives& x, const alternatives& y) {
    if (y.empty() || x.empty())  return O;

    alternatives as;

    for (auto& i: x)
      for (auto& j: y)
        as.push_back(i*j);

    return as;
  }


  void proof::push_front(const alternative& a) {
    proof_.push_front(a);
  }

  void proof::push_back(const alternative& a) {
    proof_.push_back(a);
  }


  void proof::set_conditional() {
    conditional_ = false;

#if NEW_PROVED
    for (auto& i: proof_)
      for (auto& j: i.labelstatements_)
        if (!j.second.statement_->is_proved()) {
          conditional_ = true;
          break;
        }
#else
    for (auto& i: proof_)
      for (auto& j: i.labelstatements_)
        if (!j.second.first->is_proved()) {
          conditional_ = true;
          break;
        }
#endif
  }

  void proof::write(std::ostream& os, write_style ws) const {
    if (ws & write_statement) {
      os << "Proof of\n  " << goal_->get_formula() << "\n";

      const_iterator i, i0 = proof_.begin(), i1 = proof_.end();

      if (i0 == i1 || !proof_.back().goal_->provable()) {
        // Empty proof or last alternative has non-metaempty goal:
        os << "failed." << std::endl;
        return;
      }

      os << "succeeded:\n  ";
    }

    bool it0 = true;
    for (auto& i: proof_) {
      if (it0) it0 = false; else os << ": ";
      i.write(os, write_name);
    }

    if (ws & write_statement) {
      os << ".\n";

      for (auto& i: proof_) {
        i.write(os, ws);
        os << "\n";
      }

      os << "∎" << std::endl;
    }
  }


  void subformulas::write(std::ostream& os, write_style ws) const {
    const_iterator i, i0 = begin(), i1 = end();
    os << "{";
    for (i = i0; i != i1; ++i) {
      if (i != i0)
        os << ", ";
      (*i)->write(os, ws);
    }  
    os << "}";
  }


  void split_formula::write(std::ostream& os, write_style ws) const {
    const_iterator i, i0 = begin(), i1 = end();

    os << "formula split:";

    for (auto& i: *this) {
      os << "\n";
      std::get<1>(i)->write(os, ws);
      os << "; ";
      std::get<0>(i).write(os, ws);
      os << "; ";

      bool j0 = true;
      for (auto& j: std::get<2>(i)) {
        if (j0) j0 = false; else os << " ";
        os << j;
      }
    }
  }


} // namespace mli
