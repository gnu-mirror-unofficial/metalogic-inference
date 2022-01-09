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

#include "substitution.hh"


namespace mli {

  // Class for function 𝒙 ↦ 𝑨, where in evaluation only the free variables of
  // are substituted: (𝒙 ↦ 𝑨)(𝒕) ≔ 𝑨[𝒙 ⤇ 𝒕].
  // Apart from being a base class, function() also represents the
  // identity function.
  class function : public nonempty_formula {
  public:
    new_copy(function);
    new_move(function);

    virtual bool is_identity() const { return true; }


    // Function evaluation.
    // Translates a function application expression into a formula using substitions:
    //   id(𝒕) ≔ 𝒕
    //   (𝒙 ↦ 𝑨)(𝒕) ≔ 𝑨[𝒙 ⤇ 𝒕]
    //   (𝒇 ∘ 𝒈)(𝒕) ≔ 𝒇(𝒈(𝒕))
    virtual ref<formula> operator()(ref<formula>) const;

    formula::type get_formula_type() const override { return formula::logic; }

    virtual kleenean has(const ref<variable>&, occurrence) const { return false; }
    virtual void contains(std::set<ref<variable>>&, std::set<ref<variable>>&, bool&, occurrence) const {}


    // Find the set of variables varied in the function.
    virtual void get_varied(std::set<ref<variable>>&, metalevel_t) const {}

    // Variables varied of a premise vs, variables varied in reduction vrs, associated
    // with the formulas set variable fsv, and offset m, the position in the substituted premise
    // at where the varied variables should be inserted.
    virtual void get_varied(varied_type& vvs, varied_type& vrs, const variable& fsv, size_type m) const {}


    virtual kleenean free_for(const ref<formula>&, const ref<variable>&,
      std::set<ref<variable>>&, std::list<ref<variable>>&) const { return true; }

    void unspecialize(depth, bool) override {}
    void unspecialize(std::set<ref<variable>>&, bool) override {}

    ref<formula> substitute(const ref<substitution>&, substitute_environment) const override { return this; }

    virtual void set_bind(bind&, name_variable_table&) {}

    virtual alternatives unify(unify_environment, const ref<formula>&, unify_environment, database*, level, degree_pool&, direction) const;

  #if 0  // Defined in class formula:
    virtual split_formula split(unify_environment, const ref<variable>&, const ref<formula>&, unify_environment, database*, level, degree_pool&, direction) const;
  #endif

    // One has *this = innermost()*without(), and innermost() of the form
    // [x↦t] or equal to I:
    virtual ref<function> innermost() const { return this; }
    virtual ref<function> without() const { return this; }

    // One has *this = within()*outermost(), and outermost() of the form
    // [x↦t] or equal to I:
    virtual ref<function> outermost() const { return this; }
    virtual ref<function> within() const { return this; }

    virtual order compare(const unit&) const;

    virtual void write(std::ostream& os, write_style) const { os << "id"; }
  };


  class function_map : public function {
  public:
    ref<variable> variable_;
    ref<formula> formula_;

  public:
    function_map() {}

    new_copy(function_map);
    new_move(function_map);

    function_map(const ref<variable>& i, const ref<formula>& t)
     : variable_(i), formula_(t) {}


    // Function evaluation, (𝒙 ↦ 𝒇)(𝒂) ≔ 𝒇[𝒙 ⤇ 𝒂].
    ref<formula> operator()(ref<formula> x) const override;

    bool is_identity() const override { return variable_ == formula_; }

    formula::type get_formula_type() const override { return formula::meta; }

    void set_bind(bind&, name_variable_table&) override;
    ref<formula> rename(level, degree) const override;
    ref<formula> add_exception_set(variable_map&) const override;

    kleenean has(const ref<variable>&, occurrence) const override;
    void contains(std::set<ref<variable>>&, std::set<ref<variable>>&, bool&, occurrence) const override;

    kleenean free_for(const ref<formula>& f, const ref<variable>& x,
      std::set<ref<variable>>& s, std::list<ref<variable>>& bs) const override;

    void unspecialize(depth, bool) override;
    void unspecialize(std::set<ref<variable>>&, bool) override;

    ref<formula> substitute(const ref<substitution>&, substitute_environment) const override;

    virtual alternatives unify(unify_environment, const ref<formula>&, unify_environment, database*, level, degree_pool&, direction) const override;

    virtual split_formula split(unify_environment, const ref<variable>&, const ref<formula>&, unify_environment, database*, level, degree_pool&, direction) const override;

    ref<function> innermost() const override;
    ref<function> without() const override;
    ref<function> outermost() const override;
    ref<function> within() const override;

    order compare(const unit&) const override;

    precedence_t precedence() const override { return formula_->precedence(); }

    void write(std::ostream& os, write_style ws) const override;
  };


  class function_composition : public function {
    ref<function> inner_ = ref<function>(make);
    ref<function> outer_ = ref<function>(make);

  public:
    function_composition() = default;

    new_copy(function_composition);
    new_move(function_composition);

    function_composition(const ref<function>& outer, const ref<function>& inner)
     : outer_(outer), inner_(inner) {}

    // Function evaluation, (𝒇 ∘ 𝒈)(𝒂) ≔ 𝒇(𝒈(𝒂)).
    ref<formula> operator()(ref<formula> x) const override { return outer_(inner_(x)); }

    bool is_identity() const override { return inner_->is_identity() && outer_->is_identity(); }

    formula::type get_formula_type() const override { return formula::logic; }

    // Variable renumbering:
    void set_bind(bind&, name_variable_table&) override;
    ref<formula> rename(level, degree) const override;
    ref<formula> add_exception_set(variable_map&) const override;

    // Free variables:
    kleenean has(const ref<variable>&, occurrence) const override;
    void contains(std::set<ref<variable>>&, std::set<ref<variable>>&, bool&, occurrence) const override;

    kleenean free_for(const ref<formula>& f, const ref<variable>& x,
      std::set<ref<variable>>& s, std::list<ref<variable>>& bs) const override;

    // Fixed variables:
    void unspecialize(depth, bool) override;
    void unspecialize(std::set<ref<variable>>&, bool) override;

    // Substitution:
    ref<formula> substitute(const ref<substitution>&, substitute_environment) const override;

    // Unification:
    alternatives unify(unify_environment, const ref<formula>&, unify_environment, database*, level, degree_pool&, direction) const override;

    split_formula split(unify_environment, const ref<variable>&, const ref<formula>&, unify_environment, database*, level, degree_pool&, direction) const override;

    ref<function> innermost() const override;
    ref<function> without() const override;
    ref<function> outermost() const override;
    ref<function> within() const override;

    // Comparison, needed for unification and database lookup.
    order compare(const unit&) const override;

    // Writing:
    precedence_t precedence() const override { return precedence_t(); }

    void write(std::ostream& os, write_style ws) const override;
  };


  // Reverse function composition f * g = f ∙ g ≔ g ∘ f of functions f, g, in functional
  //   prefix notation: (f ∙ g)(x) = (g ∘ f)(x) ≔ g(f(x))
  //   postfix notation: (x)(f ∙ g) = (x)(g ∘ f) ≔ g(f(x))
  ref<function> operator*(const ref<function>& f, const ref<function>& g);


  // Used for explicit function expressions A[x ⤇ t], formally a pair (A, s)
  // where A is a formula and s = [x ⤇ t] an explicit function. Unification is particularly
  // complicated for this type: u(A[x ⤇ t], B) involvs finding all subexpressions of B
  // unifying with t with a set S occurrences in. Any subset of S can be replaced by
  // x to give a possible A. In addition, if t is unspecialized, then so must this
  // property be forwarded to x.
  class function_application : public nonempty_formula {
  public:
    ref<function> function_; // Initializes to the default function id.
    ref<formula> formula_;

    function_application() = default;

    function_application(const ref<function>& f, const ref<formula>& x) : function_(f), formula_(x) {}

    new_copy(function_application);
    new_move(function_application);

    formula::type get_formula_type() const override;

    // Variable renumbering:
    void set_bind(bind&, name_variable_table&) override;
    ref<formula> rename(level, degree) const override;
    ref<formula> add_exception_set(variable_map&) const override;

    // Free variables:
    kleenean has(const ref<variable>&, occurrence) const override;
    void contains(std::set<ref<variable>>&, std::set<ref<variable>>&, bool&, occurrence) const override;

    kleenean free_for(const ref<formula>& f, const ref<variable>& x,
      std::set<ref<variable>>& s, std::list<ref<variable>>& bs) const override;

    // Fixed variables:
    void unspecialize(depth, bool) override;
    void unspecialize(std::set<ref<variable>>&, bool) override;

    // Substitution:
    ref<formula> substitute(const ref<substitution>&, substitute_environment) const override;

    // Unification:
    alternatives unify(unify_environment, const ref<formula>&, unify_environment, database*, level, degree_pool&, direction) const override;

    split_formula split(unify_environment, const ref<variable>&, const ref<formula>&, unify_environment, database*, level, degree_pool&, direction) const override;

    order compare(const unit&) const override;

    // Writing:
    precedence_t precedence() const override;

    void write(std::ostream& os, write_style) const override;
  };

} // namespace mli

