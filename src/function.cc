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


#include "function.hh"


namespace mli {

  ref<formula> function::operator()(ref<formula> x) const {
    return x;
  }


  alternatives function::unify(unify_environment, const ref<formula>& x, unify_environment, database*, level, degree_pool&, direction) const {
    if (trace_value & trace_unify) {
      std::lock_guard<std::recursive_mutex> guard(write_mutex);
      std::clog
       << "function::unify\n  " << *this << ";\n  " << x << ")" << std::endl;
    }

    function* xp = ref_cast<function*>(x);
    return (xp != 0) && (xp->is_identity())? I : O;
  }


  order function::compare(const unit& x) const {
    auto& xr = dynamic_cast<const function&>(x);
    return xr.is_identity()? equal : unordered;
  }


  // Class function_map

  
  ref<formula> function_map::operator()(ref<formula> x) const {
    // Function evaluation, (𝒙 ↦ 𝒇)(𝒂) ≔ 𝒇[𝒙 ⤇ 𝒂].
    // variable_ = 𝒙, formula_ = 𝒇, x = 𝒂.
    // Also, when 𝒂 is function argument sequences singleton (x) reduce to x,
    // and when and empty tuple () reduce to an empty formula.

    ref<formula> x1 = x;

    sequence* vp = ref_cast<sequence*>(x);

    // Reduce function argument sequences singletons (x) to x, and () to empty formula.
    // As x1 = x above, only these cases need to be considered.
    if (vp != nullptr && (vp->type_ == sequence::tuple || vp->type_ == sequence::logic)) {
      if (vp->formulas_.empty())
        x1 = ref<formula>(make);
      else if (vp->formulas_.size() == 1)
        x1 = vp->formulas_.front();
    }

    ref<explicit_substitution> vs(make, variable_, x1);

    return vs(formula_);
  }


  void function_map::set_bind(bind& b, name_variable_table& vs) {
    variable_->set_bind(b, vs);
    formula_->set_bind(b, vs);
  }



  ref<formula> function_map::rename(level lv, degree sl) const {
    ref<function_map> mp(make, *this);
    mp->variable_ = variable_->rename(lv, sl);
    mp->formula_ = formula_->rename(lv, sl);
    return mp;
  }


  ref<formula> function_map::add_exception_set(variable_map& vm) const {
    ref<function_map> mp(make, *this);
    mp->variable_ = variable_->add_exception_set(vm);
    mp->formula_ = formula_->add_exception_set(vm);
    return mp;
  }


  kleenean function_map::has(const ref<variable>& v, occurrence oc) const {
    kleenean k1 = variable_->has(v, oc);
    if (k1 == true)  return true;

    kleenean k2 = formula_->has(v, oc);

    return k1 || k2;
  }


  void function_map::contains(std::set<ref<variable>>& s, std::set<ref<variable>>& bs, bool& more, occurrence oc) const {
    variable_->contains(s, bs, more, oc);
    formula_->contains(s, bs, more, oc);
  }


  kleenean function_map::free_for(const ref<formula>& f, const ref<variable>& x,
    std::set<ref<variable>>& s, std::list<ref<variable>>& bs) const {
    kleenean k1 = variable_->free_for(f, x, s, bs);
    if (k1 == false) return false;
    kleenean k2 = formula_->free_for(f, x, s, bs);
    return k1 && k2;
  }


  void function_map::unspecialize(depth x, bool y) {
    variable_->unspecialize(x, y);
    formula_->unspecialize(x, y);
  }


  void function_map::unspecialize(std::set<ref<variable>>& vs, bool b) {
    variable_->unspecialize(vs, b);
    formula_->unspecialize(vs, b);
  }


  ref<formula> function_map::substitute(const ref<substitution>& s, substitute_environment vt) const {
    ref<formula> v0 = variable_->substitute(s, vt);

    variable* vp = ref_cast<variable*>(v0);
    if (vp == 0)
      throw illegal_substitution("In function_map::substitute, substitution of variable not a variable.");

    ref<function_map> mp(make, *this);
    mp->variable_ = vp;
    mp->formula_ = formula_->substitute(s, vt);

    return mp;
  }


  alternatives function_map::unify(unify_environment tt, const ref<formula>& x, unify_environment tx, database* dbp, level lv, degree_pool& sl, direction dr) const {
    if (trace_value & trace_unify) {
      std::lock_guard<std::recursive_mutex> guard(write_mutex);
      std::clog << "function_map::unify(\n  " << *this << ";\n  " << x << ")\n" << std::flush;
    }

    function_map* xp = ref_cast<function_map*>(x);
    if (xp == 0)  return O;
    alternatives as = mli::unify(ref<formula>(variable_), tt, ref<formula>(xp->variable_), tx, dbp, lv, sl, dr);
    return as.unify(formula_, tt, xp->formula_, tx, dbp, lv, sl, dr);
  }


  struct function_map_construct {
    ref<variable> variable_;

    function_map_construct(const ref<variable>& v)
     : variable_(v) {}

    ref<formula> operator()(const ref<formula>& x) const {
      return ref<function_map>(make, variable_, x);
    }
  };


  split_formula function_map::split(unify_environment tg,
    const ref<variable>& x, const ref<formula>& t, unify_environment tt, database* dbp, level lv, degree_pool& sl, direction dr) const {
    split_formula sf(this);  // Return value.
    // If t and *this unify, then *this can be replaced by x:
    alternatives as = mli::unify(t, tt, this, tg, dbp, lv, sl, dr);

    if (!as.empty())
      sf.push_back(this, ref<formula>(x), tt.table_->find_local());

    sf.append(mli::split(formula_, tg, function_map_construct(variable_), x, t, tt, dbp, lv, sl, dr));

    return sf;
  }


  ref<function> function_map::innermost() const {
    return this;
  }


  ref<function> function_map::without() const {
    return ref<function>(make);
  }


  ref<function> function_map::outermost() const {
    return this;
  }


  ref<function> function_map::within() const {
    return ref<function>(make);
  }


  order function_map::compare(const unit& x) const {
    auto& xr = dynamic_cast<const function_map&>(x);
    order c = variable_ <=> xr.variable_;
    if (c != equal)  return c;
    return formula_ <=> xr.formula_;
  }


  void function_map::write(std::ostream& os, write_style ws) const {

    // Remove if bind_ numbers not written in threads.
    std::lock_guard<std::recursive_mutex> guard(write_mutex);

    bool write_reverse = write_function_map_reverse & ws;

    os << "(";

    if (write_reverse)
      os << formula_ << " ↤ " << variable_;
    else {
      os << variable_ << " ↦";

      os << " ";
      if (formula_->empty()) os <<  "⦰";
      else os << formula_;
    }

    os << ")";
  }


  void function_composition::set_bind(bind& b, name_variable_table& vs) {
    inner_->set_bind(b, vs);
    outer_->set_bind(b, vs);
  }


  ref<formula> function_composition::rename(level lv, degree sl) const {
    ref<function_composition> mp(make, *this);
    mp->inner_ = inner_->rename(lv, sl);
    mp->outer_ = outer_->rename(lv, sl);
    return mp;
  }


  ref<formula> function_composition::add_exception_set(variable_map& vm) const {
    ref<function_composition> mp(make, *this);
    mp->inner_ = inner_->add_exception_set(vm);
    mp->outer_ = outer_->add_exception_set(vm);
    return mp;
  }


  kleenean function_composition::has(const ref<variable>& v, occurrence oc) const {
    kleenean k1 = inner_->has(v, oc);
    if (k1 == true)  return true;

    kleenean k2 = outer_->has(v, oc);

    return k1 || k2;
  }


  void function_composition::contains(std::set<ref<variable>>& s, std::set<ref<variable>>& bs, bool& more, occurrence oc) const {
    inner_->contains(s, bs, more, oc);
    outer_->contains(s, bs, more, oc);
  }


  kleenean function_composition::free_for(const ref<formula>& f, const ref<variable>& x,
    std::set<ref<variable>>& s, std::list<ref<variable>>& bs) const {
    kleenean k1 = inner_->free_for(f, x, s, bs);
    if (k1 == false)  return false;

    kleenean k2 = outer_->free_for(f, x, s, bs);

    return k1 && k2;
  }


  void function_composition::unspecialize(depth x, bool y) {
    inner_->unspecialize(x, y);
    outer_->unspecialize(x, y);
  }


  void function_composition::unspecialize(std::set<ref<variable>>& vs, bool b) {
    inner_->unspecialize(vs, b);
    outer_->unspecialize(vs, b);
  }


  ref<formula> function_composition::substitute(const ref<substitution>& s, substitute_environment vt) const {
    ref<function_composition> mp(make, *this);
    mp->inner_ = ref<substitution>(inner_->substitute(s, vt));
    mp->outer_ = ref<substitution>(outer_->substitute(s, vt));
    return mp;
  }


  alternatives function_composition::unify(unify_environment tt, const ref<formula>& x, unify_environment tx, database* dbp, level lv, degree_pool& sl, direction dr) const {
    if (trace_value & trace_unify) {
      std::lock_guard<std::recursive_mutex> guard(write_mutex);
      std::clog << "function_composition::unify(\n  " << *this << ";\n  " << x << ")\n" << std::flush;
    }

    function_composition* xp = ref_cast<function_composition*>(x);
    if (xp == 0)  return O;
    alternatives as = mli::unify(ref<formula>(inner_), tt, ref<formula>(xp->inner_), tx, dbp, lv, sl, dr);
    return as.unify(ref<formula>(outer_), tt, ref<formula>(xp->outer_), tx, dbp, lv, sl, dr);
  }


  struct composition_construct {
    ref<formula> operator()(const ref<formula>& x, const ref<formula>& y) const {
      return ref<function_composition>(make, ref<substitution>(x), ref<substitution>(y));
    }
  };


  split_formula function_composition::split(unify_environment tg,
    const ref<variable>& x, const ref<formula>& t, unify_environment tt, database* dbp, level lv, degree_pool& sl, direction dr) const {
    split_formula sf(this);  // Return value.
    // If t and *this unify, then *this can be replaced by x:
    alternatives as = mli::unify(t, tt, this, tg, dbp, lv, sl, dr);

    if (!as.empty())
      sf.push_back(this, ref<formula>(x), tt.table_->find_local());

    sf.append(mli::split(ref<formula>(outer_), ref<formula>(inner_), tg, composition_construct(), x, t, tt, dbp, lv, sl, dr));
    return sf;
  }


  ref<function> function_composition::innermost() const {
    return inner_->innermost();
  }


  ref<function> function_composition::without() const {
    ref<function> s = inner_->without();
    if (s->is_identity())
      return outer_;
    return ref<function_composition>(make, outer_, s);
  }


  ref<function> function_composition::outermost() const {
    return outer_->outermost();
  }


  ref<function> function_composition::within() const {
    ref<function> s = outer_->within();
    if (s->is_identity())
      return inner_;
    return ref<function_composition>(make, s, inner_);
  }


  order function_composition::compare(const unit& x) const {
    auto& xr = dynamic_cast<const function_composition&>(x);
#if (__cplusplus > 201703L) // C++20
    return {inner_ <=> xr.inner_, outer_ <=> xr.outer_};
#else
    order c = mli::compare(inner_, xr.inner_);
    if (c != equal)  return c;
    return mli::compare(outer_, xr.outer_);
#endif
  }


  void function_composition::write(std::ostream& os, write_style ws) const {
    bool write_reverse = write_function_composition_reverse & ws;
    if (write_reverse)
      os << outer_ << " ∘ " << inner_;
    else
      os << inner_ << " ∙ " << outer_;
  }


  ref<function> operator*(const ref<function>& inner, const ref<function>& outer) {
    if (inner->is_identity())  return outer;
    if (outer->is_identity())  return inner;

    return ref<function_composition>(make, outer, inner);
  }


  formula_type function_application::get_formula_type() const {
    return formula_->get_formula_type();
  }


  void function_application::set_bind(bind& b, name_variable_table& t) {
    function_->set_bind(b, t);
    formula_->set_bind(b, t);
  }


  ref<formula> function_application::rename(level lv, degree sl) const {
    ref<function_application> sfp(make, *this);
    sfp->function_ = function_->rename(lv, sl);
    sfp->formula_ = formula_->rename(lv, sl);
    return sfp;
  }


  ref<formula> function_application::add_exception_set(variable_map& vm) const {
    ref<function_application> sfp(make, *this);
    sfp->function_ = function_->add_exception_set(vm);
    sfp->formula_ = formula_->add_exception_set(vm);
    return sfp;
  }


  kleenean function_application::has(const ref<variable>& v, occurrence oc) const {
    // If v is substituted by function:
    // If oc == free: return false
    // if oc = bound: if function on v is all occurances, return false.
    kleenean k1 = function_->has(v, oc);
    if (k1 == true)  return true;

    kleenean k2 = formula_->has(v, oc);

    return k1 || k2;
  }


  void function_application::contains(std::set<ref<variable>>& vs, std::set<ref<variable>>& bs, bool& more, occurrence oc) const {
    function_->contains(vs, bs, more, oc);
    formula_->contains(vs, bs, more, oc);
  }


  kleenean function_application::free_for(const ref<formula>& f, const ref<variable>& x,
      std::set<ref<variable>>& s, std::list<ref<variable>>& bs) const {
    kleenean k1 = function_->free_for(f, x, s, bs);
    if (k1 == false)  return false;
    kleenean k2 = formula_->free_for(f, x, s, bs);
    return k1 && k2;
  }


  void function_application::unspecialize(depth x, bool y) {
    function_->unspecialize(x, y);
    formula_->unspecialize(x, y);
  }


  void function_application::unspecialize(std::set<ref<variable>>& vs, bool b) {
    function_->unspecialize(vs, b);
    formula_->unspecialize(vs, b);
  }


  ref<formula> function_application::substitute(const ref<substitution>& s, substitute_environment vt) const {
    if (trace_value & trace_substitute) {
      std::lock_guard<std::recursive_mutex> guard(write_mutex);
      std::clog
       << "Begin function_application::substitute:\n  " << *this
       << ".substitute(" << s << ")"
       << std::endl;
    }


    // First apply the unification substitution s to *this, then evaluate the
    // explicit substitution formula with free-for checks:
#if 0
    // Push a bottom, used for free-for checks, which pops when the element bg expires:
    bottom_guard bg(*vt.table_);
#endif

    ref<formula> fc = function_->substitute(s, vt);

    function* fcp = ref_cast<function*>(fc);
    if (fcp == 0)
      throw illegal_substitution("In function_map::substitute, substitution of function not a function.");

    ref<formula> fr = formula_->substitute(s, vt);


    if (trace_value & trace_substitute) {
      std::lock_guard<std::recursive_mutex> guard(write_mutex);
      std::clog
       << "End function_application::substitute:\n  " << *this
       << ".substitute(" << s << "):\n    "
       << fc << ", " << fr
       << std::endl;
    }

    return (*fcp)(fr);
  }


  alternatives function_application::unify(unify_environment tt, const ref<formula>& x, unify_environment tx, database* dbp, level lv, degree_pool& sl, direction dr) const {
    if (trace_value & trace_unify) {
      std::lock_guard<std::recursive_mutex> guard(write_mutex);
      std::clog
       << "function_application::unify(\n  " << *this << ";\n  " << x << ")"
       << std::endl;
    }

    // Unification of the function application t place by replacing
    // with the corresponding explicit substitution formula:
    //   (𝒙 ↦ 𝑨)(𝒕) = (𝒙 ↦ 𝑨, 𝒕) ≔ 𝑨[𝒙 ⤇ 𝒕] = ([𝒙 ⤇ 𝒕], 𝑨)
    //   id(𝒕) = (id, 𝒕) ≔ (I, 𝒕)
    //   (𝒇 ∘ 𝒈)(𝒕) = (𝒇 ∘ 𝒈, 𝒕) ≔ 𝒇(𝒈(𝒕))
    // So, for example,
    //   𝐮((𝒙 ↦ 𝑨)(𝒕); 𝑩) ≔ 𝐮(; 𝑩)
    //

    function_application* xp = ref_cast<function_application*>(x);

    if (xp == nullptr)
      return mli::unify(function_(formula_), tt, x, tx, dbp, lv, sl, dr);
    else
      return mli::unify(function_(formula_), tt, xp->function_(xp->formula_), tx, dbp, lv, sl, dr);
  }


  struct function_application_construct {
    ref<formula> operator()(const ref<formula>& x, const ref<formula>& y) const {
      return ref<function_application>(make, x, y);
    }
  };


  split_formula function_application::split(unify_environment tg,
    const ref<variable>& x, const ref<formula>& t, unify_environment tt, database* dbp, level lv, degree_pool& sl, direction dr) const {
    split_formula sf(this);  // Return value.
    // If t and *this unify, then *this can be replaced by x:
    alternatives as = mli::unify(t, tt, this, tg, dbp, lv, sl, dr);

    if (!as.empty())
      sf.push_back(this, ref<formula>(x), tt.table_->find_local());

    sf.append(mli::split(ref<formula>(function_), formula_, tg, function_application_construct(), x, t, tt, dbp, lv, sl, dr));
    return sf;
  }


  order function_application::compare(const unit& x) const {
    auto& xr = dynamic_cast<const function_application&>(x);
#if (__cplusplus > 201703L) // C++20
    order c = function_ <=> xr.function_;
    if (c != equal)  return c;
    return formula_ <=> xr.formula_;
#else
    order c = mli::compare(function_, xr.function_);
    if (c != equal)  return c;
    return mli::compare(formula_, xr.formula_);
#endif
  }


  precedence_t function_application::precedence() const {
#if 0
    return function_application_oprec;
#else
    return substitution_formula_oprec;
#endif
  }


  void function_application::write(std::ostream& os, write_style ws) const {
      bool do_bracket = precedence().argument(first, formula_->precedence());

      if (do_bracket) os << "(";
      function_->write(os, ws);
      if (do_bracket) os << ")";

      // Function aruments are constructed with tuple sequences as arguments,
      // so parentheses (…) need not be written out here.
      os << formula_;
  }

} // namespace mli

