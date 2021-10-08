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

#pragma once


#if (__cplusplus < 202002L) // C++20
#error "C++20 or later required."
#endif

#include <climits>

#include <iostream>

#include <deque>
#include <list>
#include <unordered_map>
#include <set>

#include <string>
#include <sstream>
#include <typeinfo>

#include <optional>


#include "config.h"
#include "pragmas.hh"

#include "gc.hh"

#include "exception.hh"
#include "kleenean.hh"
#include "polymorphy.hh"
#include "precedence.hh"
#include "table-stack.hh"
#include "write-style.hh"


#define DEBUG_INFERENCE_UNIFY 0
#define DEBUG_ADD_PREMISE 0
#define DEBUG_BODY 0

// Varied variable checks in NEW_PROVED 0 shoul be integrated before removed:
#define NEW_PROVED 1

#define NEW_SUBSTITUTION_FORMULA_UNIFY 1
#define DEBUG_SUBSTITUTION_FORMULA_UNIFY 0

#define NEW_LEXER 1


namespace mli {

  // std::string operator<=> not defined in C++20:
  inline order operator<=>(const std::string& x, const std::string& y) { return sgn(x.compare(y)); }


  // Number k of concurrent threads used if k >= 0. If k < 0, then -k times the thread::hardware_concurrency
  // value is used, which may be 0. If k or the result is 0, then no threads are created; if k is 1,
  // one thread is created. Default -1, i.e., the hardware_concurrency value.
  extern long thread_count;

  typedef std::ptrdiff_t difference_type;
  typedef std::size_t size_type;

  extern size_type level_max;
  extern size_type sublevel_max;
  extern size_type unify_count_max;

  extern size_type proof_count;
  extern bool expand_implicit_premise;

  extern bool strict_proof;


  // A class as to avoid the enum sequence::type implicitly converted to metalevel_t.
  class metalevel_t {
  public:
    size_type value = 0;

    constexpr metalevel_t() = default;

    constexpr explicit metalevel_t(size_type k) : value(k) {}

    constexpr operator size_type() const { return value; }
  };

  constexpr metalevel_t operator "" _ml(unsigned long long k) { return metalevel_t(k); }


  typedef size_type bind;    // Numbering for variable binding.
  typedef size_type depth;   // Depth of nested proofs of statement, starting a 0.


  // Class for renumbering variables according to inference tree level (distance from root
  // plus one), called top, and the numbering of object formulas in a formula sequence at a inference
  // tree node, called sub, which starts at 0.
  class level {
  public:
    size_type top = 0;
    size_type sub = 0;

    level(size_type n) : top(n) {}

#if (__cplusplus > 201703L) // C++20
    order operator<=>(const level& x) const {
      return {top <=> x.top, sub <=> x.sub};
    }
#endif

    order compare(const level& x) const {
#if (__cplusplus > 201703L) // C++20
      if (top != x.top) return top <=> x.top;
      return sub <=> x.sub;
#else
      if (top != x.top) return order(top, x.top);
      return order(sub, x.sub);
#endif
    }
  };


} // namespace mli

namespace std {
  template<> struct hash<mli::level> {
    size_t operator()(mli::level const& x) const {
      return std::hash<unsigned>()(x.top) ^ std::hash<unsigned>()(x.sub);
    }
  };
} // namespace std

namespace mli {

  // Degree of definition used in the unificiation of a formula in s formula sequence:
  // Each use, gets a new, lowest number assigned by class degree_pool (in definition::unify).
  typedef unsigned degree;

  // Class for selecting the smallest degree not in use in the current instantiation.
  class degree_pool {
  public:
    degree max_ = 0;           // If > 0, largest used degree; 0 if none is used.
    std::set<degree> unused_;  // Numbers not in use < max_.

    degree_pool() = default;

    // Get lowest number not in use in the current instantiation.
    degree get();

    // Put back a number into the pool, as when found to not be needed.
    // Requirement: k != 0 and k <= max. If k < max, k is stored as unused;
    // if k == max, max is decreased, and new value removed from unused if there.
    void put_back(degree k);
  };


  // Indentation shows class hierarchy:
  // MLI.hh:
  class unit;
    class formula;
      class nonempty_formula;
        class statement;
    // definition.hh:
          class definition;
    // proposition.hh:
          class supposition;
          class proof_line;
          class theorem;
          class premise;
          class statement_substitution;
    // MLI.hh:
        class variable;
        class constant;
        class sequence;
        class structure;
        class bound_formula;
        class formula_sequence;
        class inference;
        class database;
    // database.hh:
          class sequential_database;
            class theory;
          class level_database;
        class theory_database;
    // basictype.hh:
        class integer;
    // definition.hh:
        class abbreviation;
    // metacondition.hh:
        class metanot;
        class succeed_fail;
        class identical;
        class objectidentical;
        class free_in_object;
        class free_for_object;
    // substitution.hh:
        class substitution;
          class variable_substitution;
          class composition;
        class substitution_formula;
    // MLI.hh:
      class variable_list;
    // substitution.hh:
      class alternative;
      class alternatives;
      class proof;

  // substitution.hh:
  class split_formula;
  // inferenceengine.cc:
  class inference_tree;
  // MLI.hh:
  class unify_environment;
  class substitute_environment;

  // inferenceengine.cc:
  class inference_stack;


  using proofs = std::list<proof>;


  enum class occurrence : uint8_t {
    free,
    bound,
    quantified,
    free_not_limited,
    object,
    not_object,
    limited,
    not_limited,
    formula_sequence,
    unspecialized,
    declared,
    any
  };


  // Unification direction of u(x, y):
  //  deduction  fact argument before goal argument
  //  reduction  goal argument before fact argument
  enum direction { deduction, reduction };


  // Should be removed: only used in function unify_bound (Unify bound variables).
  inline direction operator!(direction dr) { return (direction)!(int)dr; }


  enum target { goal, fact };

  inline target operator!(target x) { return (target)!(int)x; }


  // Top level expansion of definitions and abbreviations:
  enum expansion { no_expand, expand };


  // Type for indicating the set of varied variables of an inference, one set
  // for each conclusion formula.
  using varied_type = std::map<size_type, std::map<size_type, std::set<ref<variable>>>>;

  // Type for indicating the set of varied variables of an inference,
  // having only one conclusion formula.
  using varied_premise_type = std::map<size_type, std::set<ref<variable>>>;


  // Macros simplifying virtual copy and move operators, usage, in class A declaration:
  //   new_copy(A);
  //   new_move(A);
  #define new_copy(A)  virtual A* new_p() const& { return new (collect) A(*this); }
  #define new_move(A)  virtual A* new_p() && { return new (collect) A(std::move(*this)); }


  // The root class of the dynamic polymorphic hierarchy.
  class unit {
    typedef unsigned long count_type;

  public:
    // If other constructors are defined, the default constructor must be
    // explicitly defined if one wants to have it:
    unit() = default;
    // The destructor must be virtual in this base class, in order to ensure that is true
    // for derived classes, that is, the whole class hierarchy. In the base classes, it will be
    // then be virtual without explicitly specifying so.
    virtual ~unit() = default;

    // If the destructor is explicit, explicit copy constructor and assignment operator must be added.
    // If any of these latter are explicit, move constructor or move assignment operator must be explicit
    // if one wants to have them. If any of move constructor or move assignment operator are explicit,
    // explicit copy constructor and assignment operators must be added if one wants to have them.
    unit(const unit&) = default;
    unit(unit&&) = default;
    unit& operator=(const unit&) & = default;
    unit& operator=(unit&&) & = default;

    // Virtual copy and move constructors. Every derived class A should have a pair of the form
    //   A* new_p() const& { return new A(*this); }
    //   A* new_p() && { return new A(std::move(*this)); }
    // Instead of writing these explicitly, the following macros may be used
    //   new_copy(A);
    //   new_move(A);
    virtual unit* new_p() const& { return new (collect) unit(*this); }
    virtual unit* new_p() && { return new (collect) unit(std::move(*this)); }

    // Semantic comparison.
    virtual order compare(const unit& x) const { return equal; }

    virtual size_t hash() const { return 0; }

    virtual void write(std::ostream& os, write_style) const { os << "∅"; }
  };

  inline std::ostream& operator<<(std::ostream& os, const unit& a) {
    a.write(os, write_default);  return os;
  }

} // namespace mli

namespace std {
  template<> struct hash<mli::unit> {
    size_t operator()(mli::unit const& x) const {
      return typeid(x).hash_code() ^ x.hash();
    }
  };
} // namespace std

namespace mli {


// If the set of types should have a total order set to 1, or if unequal types
// should be unordered, set to 0:
#define TOTAL_TYPE_ORDER 1


#if (__cplusplus > 201703L) // C++20
  // Semantic comparison.
  // Different types are unequal, a total order by the C++ implementation
  // dependent class typeid collation order.
  inline order operator<=>(const unit& x, const unit& y) {
#if TOTAL_TYPE_ORDER
    if (typeid(x) != typeid(y))
      return (typeid(x).before(typeid(y)))? less : greater;
#else
    if (typeid(x) != typeid(y)) return unordered;
#endif
    return x.compare(y);
  }
#else
  // Semantic comparison.
  // Different types are unequal, a total order by the C++ implementation
  // dependent class typeid collation order.
  inline order compare(const unit& x, const unit& y) {
#if TOTAL_TYPE_ORDER
    if (typeid(x) != typeid(y))
      return (typeid(x).before(typeid(y)))? less : greater;
#else
    if (typeid(x) != typeid(y)) return unordered;
#endif
    return x.compare(y);
  }
#endif


#if (__cplusplus > 201703L) // C++20
  inline bool operator==(const unit& x, const unit& y) { return comparison(equal)(x <=> y); }

  inline bool operator!=(const unit& x, const unit& y) { return comparison(~equal)(x <=> y); }

  inline bool operator<(const unit& x, const unit& y) { return comparison(less)(x <=> y); }

  inline bool operator>(const unit& x, const unit& y) { return comparison(greater)(x <=> y); }

  inline bool operator<=(const unit& x, const unit& y) { return comparison(less|equal)(x <=> y); }

  inline bool operator>=(const unit& x, const unit& y) { return comparison(greater|equal)(x <=> y); }
#else
  inline bool operator==(const unit& x, const unit& y) {
    return compare(x, y) == equal;
  }

  inline bool operator!=(const unit& x, const unit& y) {
    return compare(x, y) != equal;
  }

  inline bool operator<(const unit& x, const unit& y) {
    return compare(x, y) == less;
  }

  inline bool operator<=(const unit& x, const unit& y) {
    order r = compare(x, y);
    return (r == less) || (r == equal);
  }

  inline bool operator>(const unit& x, const unit& y) {
    return compare(x, y) == greater;
  }

  inline bool operator>=(const unit& x, const unit& y) {
    order r = compare(x, y);
    return (r == greater) || (r == equal);
  }
#endif

  enum statement_type {
    no_statement,
    a_proposition,
    a_definition
  };


  enum formula_type {
    no_formula_type_,
    metaformula_type_,
    object_formula_type_,
    term_type_
  };


  // Used in parsing to assign bind numbers to variables with syntactically
  // same name, unique to the binder they belong to.
  typedef table_stack<std::string, ref<variable>> name_variable_table;

  // Used to keep track of binder variables for explicit substitution free-for checks.
  using variable_table = set_stack<ref<variable>>;

  // Used to add variable exception sets.
  using variable_map = std::map<ref<variable>, std::set<ref<variable>>>;


  // Meta and public unit formulas.
  class formula : public unit {
  public:
    new_copy(formula);
    new_move(formula);

    virtual bool empty() const { return true; }

    virtual formula_type get_formula_type() const { return no_formula_type_; }

    // Variable renumbering:
    ref<formula> set_bind(); // Set numbering of binders and their associated bound variable occurrences.
    virtual void set_bind(bind&, name_variable_table&) {}

    // Return a copy with relabeled variables; if level.top = 0, a copy without changing the labels:
    virtual ref<formula> rename(level = 0, degree = 0) const { return this; }

    // Return a copy with exception set variables added to the variables, as indicated by the map:
    virtual ref<formula> add_exception_set(variable_map&) const { return this; }

    // Statement name access; empty string if not defined:
    virtual std::string name() const { return {}; }
    virtual ref<formula> get_formula() const { return this; }
    virtual ref<formula> get_formula(size_type) const { return this; }


    // Free variables:
    virtual kleenean has(const ref<variable>&, occurrence) const { return false; }

    // Find all variables of the category indicated by the occurrence argument.
    // The second argument collects the bound variables (needed for correct computation
    // of the free variables).
    // The bool& argument will be set to true if the search encounters a metavariable
    // that, if later substituted, may contain more variables of the search type.
    // This is needed by free_for() which will then be undefined.
    virtual void contains(std::set<ref<variable>>&, std::set<ref<variable>>&, bool&, occurrence) const {}

    // The bool value as a return instead of as an argument:
    bool contains(std::set<ref<variable>>& s, occurrence oc) const;

    // Compute f free for x in *this, i.e., true if no free occurance of x in *this
    // is in the scope of a binder β y, where y is free in f; otherwise false. Thus,
    // if true, substituting f for x in *this does not cause any free variables of
    // f to become bound.
    kleenean free_for(const ref<formula>& f, const ref<variable>& x) const;

    // Implementation helper function:
    //   free_for(f, x, s, bs)
    // s = set of variables that cannot become bound at free occurance of x,
    // bs = bound variables currently in scope.
    virtual kleenean free_for(const ref<formula>&, const ref<variable>&,
      std::set<ref<variable>>&, std::list<ref<variable>>&) const { return true; }


    // Make variables unspecializable during proof (ensuring generality):
    virtual void unspecialize(depth, bool) {}
    virtual void unspecialize(std::set<ref<variable>>& ps, bool b) {}

    // Substitution:
    virtual ref<formula> substitute(const ref<substitution>&, substitute_environment) const;


    // Add y as a goal to *this, merging with inferences as necessary.
    // An empty formula has no goals, so x is the only new goal:
    virtual ref<formula> add_goal(const ref<formula>& x) const { return x; }

    // Add y as a premise to *this, creating inferences as necessary.
    // An empty formula is proved, so needs no premises:
    virtual ref<formula> add_premise(const ref<formula>& x, metalevel_t,
      const varied_type& vs, const varied_type& vrs) const { return this; }

    // Metalevel:
    // 0  object formula 0
    // 1  metaformula, e.g., inference, formula sequence.
    // 2  metametaformula, e.g., metainference, metaformula sequence.
    virtual metalevel_t metalevel() const { return 0_ml; }


    virtual bool is_metasubset(const ref<formula> x) const { return true; }


    // Return metaand resp. metaor behavior, which is reversed relatively a goal when a
    // fact. Normally, when defining objects, one departs from the goal description.

    // A formula sequence goal which may have variable dependencies between its components
    // marked metaaand mode, to ensure the whole set is unified in one go against the
    // fact formula sequence, which is required by a sequential unification method.
    // Thus, the metaaand mode formula sequence is reduced before the fact formula sequence.

    virtual bool meta_container_and_mode(target) const { return false; }
    virtual bool meta_container_or_mode(target) const  { return false; }

    // True exactly when an inference with premise that has not been expanded.
    virtual bool unexpanded_premise(unify_environment) const;


    // Metaobjects like A ⊢ B with a head and body that need to be expanded,
    // or its head B or body A to be extracted.
    virtual bool inference_mode() const { return false; }

    virtual ref<formula> head() const { return this; }
    virtual ref<formula> body() const { return {}; }


    // Defining axioms and rules for traditional labeling of formal theory statements:
    // An axiom is an object formula that is not of the form A ⊢ B, and a rule is of
    // this form. Other metaobjects may be involved, such as metainference A ⊩ B, and
    // do not affect this labeling.
    virtual bool is_axiom() const { return true; }
    virtual bool is_rule() const { return false; }


    // True if and only if object is (formula) set end marker.
    virtual bool is_end_of_formula_sequence() const { return false; }


    // Unification:
    virtual alternatives unify(unify_environment tx, const ref<formula>& y, unify_environment ty, database* dbp, level lv, degree_pool& sl, direction dr) const;


    // Unifier with both arguments u(x, y):
    // For objects A that change the behavior of the unifier u_A(x, y), rather than
    // participating in the unification itself. The default is though calling x->unify(y).
    virtual alternatives unify(const ref<formula>& x, unify_environment tx, const ref<formula>& y, unify_environment ty, database* dbp, level lv, degree_pool& sl, direction dr) const;


    // Find <formula, subformulas> pairs (g, fs), where fs = v_1, ..., v_k is such that
    // unify(t, v_1, ..., v_k) is non-empty, and each g is such that f ≔ *this can be obtained by
    // replacing each occurrence of x in g with the fs subformula v_i corresponding to the position.
    // Thus, in f, some subformulas v_1, ..., v_k have in g been replaced by the variable x.
    // This is used when finding all substitution solutions to unify(g[x↦t], f) where g is unknown:
    // Replacing x with t in g creates an expression that unifies with f, as unify(t, v_1, ..., v_k)
    // is non-empty, and in the rest, f and g are identical.
    virtual split_formula split(unify_environment, const ref<variable>& x, const ref<formula>& t, unify_environment, database*, level, degree_pool&, direction) const;

    friend split_formula split(const ref<formula>& f,
      const ref<variable>& x, const ref<formula>& t, database*, level lv, degree_pool& sl, direction dr);


    // These are the defaults for empty formulas; for nonempty formulas, see class nonempty_formula:


    // Return true if provable as metaobject goal, else return false:
    // Empty formula, metaand if all components provable, metaor if
    // one component provable, and inference if the head is provable.
    // Used in the inference engine for checking if an alternative holds
    // the end of a proof search, i.e., the last reduction.
    virtual bool provable() const { return true; }

    // Formula sequence size counted with any eventual nesting.
    virtual size_type metasize() const { return 0; }

    // Formula sequence size only counting top level formula sequence.
    // For use with varied variables, where the index refer to the top level premise.
    virtual size_type formula_sequence_size() const { return 0; }

    // True if formula sequence or inference nestedly contains a formula sequence.
    virtual bool unexpanded() const { return false; }

    // Expand nested formula sequences. The argument is the index used to
    // recompute the indices of data such as inference varied variables.
    // The return is a formula sequence.
    virtual ref<formula> expand(size_type) const;

    // True if x is a member of *this viewed as a formula sequence.
    // Does not make sense when x is the empty formula.
    virtual bool has_formula(ref<formula> x) const { return false; }

    // True when the inference implicit premise should be expanded.
    // An exception is when the database has been specified to not do that,
    // in order to avoid proof search redundancy.
    virtual bool expand_premise(level) const { return true; }


    // Ordering, with requirements:
    //   x.compare(y) == less ⇔ y.compare(x) == greater
    //   x.compare(y) == equal ⇔ y.compare(x) == equal
    //   x.compare(y) == unordered ⇔ y.compare(x) == unordered
    // When the types of x and y differ, the default is set in the function
    // compare(x, y). Thus x.compare(y)
    // should not be called directly unless x and y are of the same type.
    // An implementation can assume x and y being of the same type.
    // Required for unification and database lookup.

    // Semantic comparison.
    virtual order compare(const unit& x) const override { return equal; }


    // Writing:

    virtual precedence_t precedence() const { return precedence_t(); }

    virtual void write(std::ostream& os, write_style) const override
    { if (trace_value & trace_empty)  os << "⦰"; }
  };


  // Master unification function mli::unify:
  alternatives unify(const ref<formula>&, unify_environment, const ref<formula>&, unify_environment, database*, level, degree_pool&, direction = reduction, expansion = expand);

  // Unifying a formula x with a list of formulas ys:
  alternatives unify(const ref<formula>& x, unify_environment tx, const std::list<ref<formula>>& ys, unify_environment ty, database* dbp, level lv, degree_pool& sl, direction dr);


  // A formula x to be proved x (is a goal), referencing a database dbr of proved statements.
  // Formally, one look for substitions s such that s(x) ⊂ s(dbr), called a solution.
  // Each solution results in a proof, added to the proof list, which is the return.
  // n = number of solutions to be found; n = 0 ⇔ find all solutions
  // When n solutions have been found the search ends, but additional already found
  // proofs may or may not be reported.
  proofs prove(const ref<formula>& x, database& dbr, size_type n);


  // Class setting some common defaults for non-empty formulas.
  class nonempty_formula : public formula {
  public:
    new_copy(nonempty_formula);
    new_move(nonempty_formula);

    // Defaults for nonempty formulas:

    bool empty() const override { return false; }

    ref<formula> add_goal(const ref<formula>& x) const override;

    ref<formula> add_premise(const ref<formula>& x, metalevel_t,
      const varied_type& vs, const varied_type& vrs) const override;


    bool provable() const override { return false; }

    bool is_metasubset(const ref<formula> x) const override;

    size_type metasize() const override { return 1; }
    size_type formula_sequence_size() const override { return 1; }

    ref<formula> expand(size_type) const override;

    bool has_formula(ref<formula> x) const override { return *x == *this; }
  };


  // Metaobject with name holding a statement plus information about provabiliy,
  // provedness status, and an eventual proof.
  class statement : public nonempty_formula {
  public:
    std::string name_;
    ref<formula> statement_;

    statement() = default;
    statement(const ref<formula>& f) : statement_(f) {}
    statement(const std::string& nm, const ref<formula>& f) : name_(nm), statement_(f) {}

    new_copy(statement);
    new_move(statement);

    virtual formula_type get_formula_type() const override { return metaformula_type_; }

    virtual ref<formula> get_formula(size_type k) const { return statement_->get_formula(k); }

    virtual metalevel_t metalevel() const override { return statement_->metalevel(); }

    bool meta_container_and_mode(target x) const override { return x == goal; }
    bool meta_container_or_mode(target x) const override { return x == fact; }


#if 0 // debug.hh
    virtual bool inference_mode() const override { return statement_->inference_mode(); }
#else
    // Implicit conversion to inference, formula A to metaformula ⊢ A:
    virtual bool inference_mode() const override { return true; }
#endif

    virtual ref<formula> head() const { return statement_->head(); }
    virtual ref<formula> body() const { return statement_->body(); }


    virtual alternatives unify(unify_environment, const ref<formula>&, unify_environment, database*, level, degree_pool&, direction) const override;

    virtual alternatives unify(const ref<formula>& x, unify_environment tx, const ref<formula>& y, unify_environment ty, database* dbp, level lv, degree_pool& sl, direction dr) const;


    virtual kleenean has(const ref<variable>& v, occurrence oc) const override { return statement_->has(v, oc); }
    virtual void contains(std::set<ref<variable>>& s, std::set<ref<variable>>& bs, bool& more, occurrence oc) const override { return statement_->contains(s, bs, more, oc); }

    virtual kleenean free_for(const ref<formula>& f, const ref<variable>& x,
      std::set<ref<variable>>& s, std::list<ref<variable>>& bs) const override { return statement_->free_for(f, x, s, bs); }

    void unspecialize(depth d, bool b) override { statement_->unspecialize(d, b); }
    void unspecialize(std::set<ref<variable>>& ps, bool b) override { statement_->unspecialize(ps, b); }

    virtual ref<formula> rename(level = 0, degree = 0) const override;
    virtual ref<formula> add_exception_set(variable_map&) const override;
    virtual ref<formula> substitute(const ref<substitution>&, substitute_environment) const override;

    // Variable renumbering:
    virtual void set_bind(bind& b, name_variable_table& vs);

    virtual void declared(std::set<ref<variable>>& vs) const { statement_->contains(vs, occurrence::declared); }


    // Statement access:
    virtual std::string name() const override { return name_; }
    virtual ref<formula> get_formula() const override { return statement_; }

    virtual statement_type get_statement_type() const { return no_statement; }


    // Proving & solving.
    virtual void prove(size_type n) {}

    // Return value for statement according provablity status:
    //  true      Has a strict proof or is a postulate (axiom or rule).
    //  undefined Has a conditional proof.
    //  false     Has a no proof or is a conjecture.
    // A conditional proof means that at least for one statement used in the
    // proof, is_proved does not return true.
    virtual kleenean is_proved() const { return false; }


    size_type metasize() const override { return statement_->metasize(); }
    size_type formula_sequence_size() const override { return statement_->formula_sequence_size(); }

    order compare(const unit& x) const override { return statement_->compare(x); }

    void write(std::ostream& os, write_style) const override { os << "empty statement"; }
  };


  class variable : public nonempty_formula {
  public:
    std::string name;

    // Level numbers. Semantically, name plus level numbers act as a variable
    // identifier.
    depth depth_ = 0;     // Proof nesting depth; top = 0.
    level level_ = 0;     // Formula instantiation level, bottom = 0.
    degree degree_ = 0;   // Definition instantiation degree, subbottom = 0.

    bind bind_ = 0;   // Identifies, within a formula, different binders and their variable occurrences.
                      // Used to enable local substitutions. Free variables have value 0.

    // Component index, as of (formula) sets, if set a number other than the default.
    size_type index_ = -1;

    // The partially substituted components for a formula sequence variable.
    std::list<ref<formula>> components_;

    // Used to create internal, implicit, variables that semantically cannot
    // clash with user defined variables, like the 𝚪 in inference::unify.
    bool is_implicit_ = false;

#if 0
    // Variables with limited unification: though can appear simultanously as both free and
    // bound occurrences referring to the same semantic value, and treated as free in both cases,
    // can only be substituted with other variables, as in the case bound occurrences,
    // not admitting variable change (α-conversion).
    // So when the limited flag is set, the variable in effect only admits the intersection
    // of the unification properties of the free and bound occurrences of that type of variable do.
    // Used to define properties of binders by semantically linking free and bound occurrences,
    // and also operators such as differentals.
#endif

    // Variable metatype: ordinary, limited, term.
    // The ordinary variable is what is used in normal application use, and the limited
    // and term variables are used for the metamathematical desciprtion of the ordinary
    // variable through explicit axiomatic rules.
    // The limited varible corresponds to the metavariables in standard metmathematics,
    // behavior expressed through unification, keeping implicitly track of variable clashes.
    enum metatype {
      ordinary_, free_, bound_, limited_, term_
    };

    metatype metatype_ = ordinary_;

    // For use with varied variables in the Deduction Theorem:
    // The object variables relative an inference of metalevel k for
    // which this applies have level k-1.
    metalevel_t metalevel_ = 0_ml;


    // Variable that when substituted requires that no free variable occurrences become bound.
    // This occurs in defining substitions 𝑨[𝒙 ↦ 𝒕] expressad as 𝒕 free for 𝒙 in 𝑨,
    // and in variable changes.
    bool substituition_free_ = false;

    // For a non-limited variable, when substituted, the result should contain no free
    // occurrences of any of the variables in this container.
    // These result from explicit substitutions 𝑨[𝒙 ↦ 𝒕], 𝒕 free for 𝒙 in 𝑨, and 𝑨
    // is sufficiently explicit so that the expression is simplified; then the binders
    // that 𝒕 is in the scope of of the same type should be added to this container.
    //
    // When ordinary variables only allow the substitutions permitted by the object
    // substitution rule 𝑨 ⊢⁽𝒙⁾ 𝑨[𝒙 ⤇ 𝒕], cf. Kleene p. 101, then they should not
    // have excluded variables. (Term variables admit any substitutions, and
    // must therefore be restricted by metaconditions.)
    std::set<ref<variable>> excluded_;

    // To check that excluded variables are not dropped in unification from the fact,
    // those are recorded in excluded_from_ so that they can be checked as the
    // unified bound variables are substituted.
    std::set<ref<variable>> excluded_from_;


// Should be replaced by implementation of metalevel_ before removing:
#define USE_VARIABLE_META 0

    // The free and bound variables belong to the logic, the others
    // to the metalogic.
    // The order in the list below cannot be changed, as used in several searches.
    enum type { none_,
#if USE_VARIABLE_META
      metaformula_, metapredicate_,
#endif
      formula_sequence_,
      formula_, predicate_, atom_,
      function_,
      metaobject_, object_,
      code_
    };

    type type_ = none_;

    // Variables kept unspecializable during proof. After the proof,
    // they should be made specializable again, so that they can be used as facts.
    // Note that some goal variables may end up as fact through substitution, so it does not suffice
    // to merely treat goal variables as unspecializable in through the unification process.
    bool unspecializable_ = false;


    static std::string type_name(type);  // Produce a string from type.


    variable() {}

    new_copy(variable);
    new_move(variable);

    variable(std::string s, type t, depth d, level lv = 0, degree sl = 0)
     : name(s), type_(t), depth_(d), unspecializable_(false), level_(lv), degree_(sl) {}

    variable(std::string s, metatype l, type t, depth d, level lv = 0, degree sl = 0)
     : name(s), metatype_(l), type_(t), depth_(d), unspecializable_(false), level_(lv), degree_(sl) {}


    virtual variable::type variable_type() const { return type_; }


    // True iff a substitution of *this may result in an expression containing x:
    bool may_contain(const ref<variable>& x) const;

    // True iff if a variable of type x may be substitued by a variable of type y:
    static bool is_specializable_to(type x, type y);

    // Metatypes: ordinary, limited and term variables.
    bool is_ordinary() const { return metatype_ == ordinary_; }
    bool is_limited() const { return metatype_ == limited_; }
    bool is_term() const { return metatype_ == term_; }


    // Variable binding depth in the current context relative the bound variable
    // lookup table. Congurence requires limited variables having the same depth.
    size_type get_depth(ref<variable_table> vt) const { return vt->depth(this); }

    // In an explicit substitution 𝑨[𝑥 ⤇ 𝑓], determines if the variable 𝑥 is
    // a free occurrence locally in 𝑨; 𝑥 may be bound at a higher level.
    // The function substitution_formula::substitute pushes a local level onto
    // the bound variables table.
    bool is_locally_bound(ref<variable_table> vt) const { return vt->contains_local(this); }
    bool is_locally_free(ref<variable_table> vt) const { return !vt->contains_local(this); }


    bool is_object() const;
#if USE_VARIABLE_META
    bool is_metaformula() const;
#endif
    bool is_formula() const;

    bool is_unspecializable() const { return unspecializable_; }
    bool get_depth() const;

#if USE_VARIABLE_META
    virtual formula_type get_formula_type() const override {
      return is_metaformula()? metaformula_type_
              : (is_formula()? object_formula_type_ : term_type_); }
#else
    virtual formula_type get_formula_type() const override {
      return is_formula()? object_formula_type_ : term_type_; }
#endif

    virtual alternatives unify(unify_environment, const ref<formula>&, unify_environment, database*, level, degree_pool&, direction) const override;

    kleenean occurs_in(const ref<formula>&) const;
    virtual kleenean has(const ref<variable>&, occurrence) const override;
    virtual void contains(std::set<ref<variable>>&, std::set<ref<variable>>&, bool&, occurrence) const override;

    virtual kleenean free_for(const ref<formula>& f, const ref<variable>& x, 
      std::set<ref<variable>>& s, std::list<ref<variable>>& bs) const override;

    void unspecialize(depth, bool) override;
    void unspecialize(std::set<ref<variable>>&, bool) override;

    virtual ref<formula> rename(level = 0, degree = 0) const override;
    virtual ref<formula> add_exception_set(variable_map&) const override;
    virtual ref<formula> substitute(const ref<substitution>&, substitute_environment) const override;

    virtual void set_bind(bind&, name_variable_table&) override;

    // compare() is on the object level the classical variable comparison, comparing only
    // name and level numbers, even though on the meta level, also type is compared.
    virtual order compare(const unit&) const override;

    virtual size_t hash() const override {
      return std::hash<std::string>()(name) ^ std::hash<depth>()(depth_)
        ^ std::hash<level>()(level_) ^ std::hash<degree>()(degree_);
    }

    virtual void write(std::ostream&, write_style) const override;
  };


  // Temporary comparison function, disregarding variable unspecialization.
  bool equivalent(const variable& x, const variable& y);

  // Temporary comparison class, disregarding variable unspecialization.
  struct precedes {
    bool operator()(ref<variable> x, ref<variable> y);
  };


} // namespace mli


namespace std {
  template<> struct hash<mli::variable> {
    size_t operator()(mli::variable const& x) const {
      return x.hash();
    }
  };
} // namespace std


namespace mli {

  template<class Vs> // A class whose iterators dereference to class variable.
  inline void write_variable_declaration(const Vs& vs, std::ostream& os) {
    if (!vs.empty()) {
      typename Vs::const_iterator i, i0 = vs.begin(), i1 = vs.end();
      variable::type vt0 = variable::none_, vt1;
      for (i = i0; i != i1; ++i) {
        vt1 = (*i)->type_;
        if (vt0 != vt1) {
          if (vt0 != variable::none_)  os << " ";
          os << variable::type_name(vt1) << " ";
        }
        else if (i != i0)  os << ", ";
        vt0 = vt1;
        os << *i;
      }
      os << ".";
    }
  }


  class unify_environment {
  public:
    ref<variable_table> table_;     // Bound variables lookup.

    target target_ = goal;
    metalevel_t metalevel_;

    bool is_premise_ = false;
    std::set<ref<variable>> premise_variables_; // Premise limited variables.

    size_type premise_index_ = 0;
    size_type conclusion_index_ = 0;

    // Used to make sure the premises of an inference are expanded only once.
    bool expanded_premise_ = false;


    unify_environment() {}

    unify_environment(const target& t, metalevel_t ml) : target_(t), metalevel_(ml) {}

    unify_environment(ref<variable_table> tbl, const target& t)
     : table_(tbl), target_(t) {}

    void push() { table_->push_level(); }
    void pop() { table_->pop_level(); }

    constexpr bool is_goal() const { return (target_ == goal); }
    constexpr bool is_fact() const { return (target_ == fact); }

    // Recompute varied variables:
    unify_environment substitute(ref<substitution> s);
  };

  // A class push_pound element makes sure that the stack is popped
  // when the C++ environment it is in expires.
  class push_bound {
    unify_environment* uf_;
  public:
    push_bound() : uf_(0) {}
    ~push_bound() { if (uf_ != 0)  uf_->pop(); }

    push_bound(unify_environment& uf) : uf_(&uf) { uf_->push(); }
  };


  class substitute_environment {
  public:
    ref<variable_table> table_;

    bool is_premise_ = false;
    std::set<ref<variable>> premise_variables_; // Premise limited variables.

    size_type premise_index_ = 0;
    size_type conclusion_index_ = 0;

    substitute_environment() {}

    substitute_environment(ref<variable_table> tbl) : table_(tbl) {}

    substitute_environment(const unify_environment& ue)
     : table_(ue.table_), is_premise_(ue.is_premise_), premise_variables_(ue.premise_variables_),
      premise_index_(ue.premise_index_), conclusion_index_(ue.conclusion_index_) {}
  };


  class constant : public nonempty_formula {
  public:
    typedef formula_type type;

    std::string name;
    type type_;

    constant() : type_(no_formula_type_) {}

    new_copy(constant);
    new_move(constant);

    constant(std::string s, type t) : name(s), type_(t) {}

    virtual formula_type get_formula_type() const override { return type_; }

    virtual alternatives unify(unify_environment, const ref<formula>&, unify_environment, database*, level, degree_pool&, direction) const override;

    virtual kleenean has(const ref<variable>&, occurrence) const override { return false; }
    virtual void contains(std::set<ref<variable>>&, std::set<ref<variable>>&, bool&, occurrence) const override {}

    virtual kleenean free_for(const ref<formula>&, const ref<variable>&, 
      std::set<ref<variable>>&, std::list<ref<variable>>&) const override
    { return true; }

    void unspecialize(depth, bool) override {}
    void unspecialize(std::set<ref<variable>>&, bool) override {}

    virtual ref<formula> rename(level, degree) const override { return this; }
    virtual ref<formula> substitute(const ref<substitution>&, substitute_environment) const override { return this; }

    virtual void set_bind(bind&, name_variable_table&) override {}

    virtual order compare(const unit&) const override;

    virtual void write(std::ostream&, write_style) const override;
  };


  class sequence : public nonempty_formula {
  public:
    typedef std::list<ref<formula>> container_type;
    typedef container_type::size_type size_type;
    typedef container_type::iterator iterator;
    typedef container_type::const_iterator const_iterator;
    typedef container_type::reverse_iterator reverse_iterator;
    typedef container_type::const_reverse_iterator const_reverse_iterator;

    container_type formulas_;

    // Tuple: function and predicate arguments, in function evaluation reducing singletons (x) to x.
    // The tuple has components that are terms of same or lower level and logic of strictly lower metalevel.
    // The logic tuple has components that are logic of same or lower level.
    // Logic of lower metallevel can be interpreted as of a higher metalevel through a
    // inference (provability) metapredicate ⊢, ⊩, ….
    enum type {
      logic,
      tuple,
      member_list_set, implicit_set,
      vector, list, bracket
    };

    type type_ = vector;

    metalevel_t metalevel_ = 0_ml;


    sequence() {}

    new_copy(sequence);
    new_move(sequence);


    sequence(type t) : type_(t) {}

    sequence(const ref<formula>& x, type t)
     : formulas_(1, x), type_(t) {}

    sequence(const ref<formula>& x, const ref<formula>& y, type t)
     : formulas_(1, x), type_(t) { formulas_.push_back(y); }


    sequence(const std::list<ref<formula>>& xs, type t)
     : formulas_(xs), type_(t) {}

    sequence(type t, std::initializer_list<ref<formula>> xs)
     : formulas_(xs), type_(t) {}


    sequence(const sequence& x, const sequence& y)
     : formulas_(x.formulas_), type_(x.type_)
    { formulas_.insert(formulas_.end(), y.formulas_.begin(), y.formulas_.end()); }


    sequence(const sequence& x, const ref<formula>& y)
     : formulas_(x.formulas_), type_(x.type_) { formulas_.push_back(y); }

    sequence(const ref<formula>& x, const sequence& y)
     : formulas_(y.formulas_), type_(y.type_) { formulas_.push_front(x); }


    formula_type get_formula_type() const override;

    void push_back(const ref<formula>& t) { formulas_.push_back(t); }
    void reverse() { formulas_.reverse(); }

    virtual alternatives unify(unify_environment, const ref<formula>&, unify_environment, database*, level, degree_pool&, direction) const override;
    virtual split_formula split(unify_environment, const ref<variable>&, const ref<formula>&, unify_environment, database*, level, degree_pool&, direction) const override;

    virtual kleenean has(const ref<variable>&, occurrence) const override;
    virtual void contains(std::set<ref<variable>>&, std::set<ref<variable>>&, bool&, occurrence) const override;

    virtual kleenean free_for(const ref<formula>& f, const ref<variable>& x,
      std::set<ref<variable>>& s, std::list<ref<variable>>& bs) const override;

    void unspecialize(depth, bool) override;
    void unspecialize(std::set<ref<variable>>&, bool) override;

    virtual ref<formula> rename(level, degree) const override;
    virtual ref<formula> add_exception_set(variable_map&) const override;
    virtual ref<formula> substitute(const ref<substitution>&, substitute_environment) const override;

    virtual void set_bind(bind&, name_variable_table&) override;

    virtual order compare(const unit&) const override;

    virtual precedence_t precedence() const override;
    virtual void write(std::ostream&, write_style) const override;

    // Check if x, y are of type t, and return accordingly a sequence of type t:
    friend ref<formula> concatenate(const ref<formula>& x, const ref<formula>& y, sequence::type t);
  };


  // A structure is an object of the form f(x_1, ..., x_n), where f is an
  // identifier and (x_1, ..., x_n) the argument. This style is called postargument.
  // Other styles: unary prefix f x and postfix x f, binary infix x f y.
  class structure : public nonempty_formula {
    precedence_t precedence_;

  public:
    ref<formula> atom;     // Name or letter (identifier).
    ref<formula> argument; // Should be a sequence.

    metalevel_t metalevel_ = 0_ml;

    // logic      logic value and argument
    // predicate  logic value and term argument
    // function   term value and term argument
    enum type { logic, predicate, function };
    type type_;

    // postargument  write argument as is after the atom
    enum style { postargument, prefix, postfix, infix };
    style style_;

    static formula_type to_formula_type(type x) {
      switch (x) {
        case logic:
        case predicate:
          return object_formula_type_;
        case function:
          return term_type_;
        default:
          return no_formula_type_;
      }
    }

    structure() : type_(predicate), style_(postargument) {}

    new_copy(structure);
    new_move(structure);


    // Constructor setting the atom and argument as is.
    structure(const ref<formula>& a, const ref<formula>& arg, type t, metalevel_t ml, style s, precedence_t p)
     : atom(a), argument(arg), type_(t), style_(s), precedence_(p), metalevel_(ml) {}


    // Structure with constant atom (a string, which is its name, and argument a sequence.
    structure(const std::string& s, type t, metalevel_t ml, style st, precedence_t p, std::initializer_list<ref<formula>> xs)
     : atom(ref<constant>(make, s, to_formula_type(t))),
       argument(ref<sequence>(make, (t == logic)? sequence::logic : sequence::tuple, xs)),
       type_(t), style_(st), precedence_(p), metalevel_(ml) {}

    // Allows variadic templates to be forwarded to the initializer list:
    template<class... B>
    structure(const std::string& s, type t, metalevel_t ml, style st, precedence_t p, B&&... bs)
     : structure(s, t, ml, st, p, {bs...}) {}


    void push_back(const ref<formula>&);

    void set(type t) { type_ = t; }
    void set(style s) { style_ = s; }
    void set(precedence_t p) { precedence_ = p; }

    virtual formula_type get_formula_type() const override { return to_formula_type(type_); }

    virtual metalevel_t metalevel() const override { return metalevel_; }

    virtual alternatives unify(unify_environment, const ref<formula>&, unify_environment, database*, level, degree_pool&, direction) const override;
    virtual split_formula split(unify_environment, const ref<variable>&, const ref<formula>&, unify_environment, database*, level, degree_pool&, direction) const override;

    virtual kleenean has(const ref<variable>&, occurrence) const override;
    virtual void contains(std::set<ref<variable>>&, std::set<ref<variable>>&, bool&, occurrence) const override;

    virtual kleenean free_for(const ref<formula>& f, const ref<variable>& x, 
      std::set<ref<variable>>& s, std::list<ref<variable>>& bs) const override;

    void unspecialize(depth, bool) override;
    void unspecialize(std::set<ref<variable>>&, bool) override;

    virtual ref<formula> rename(level, degree) const override;
    virtual ref<formula> add_exception_set(variable_map&) const override;
    virtual ref<formula> substitute(const ref<substitution>&, substitute_environment) const override;

    virtual void set_bind(bind&, name_variable_table&) override;

    virtual order compare(const unit&) const override;

    virtual precedence_t precedence() const override { return precedence_; }
    virtual void write(std::ostream&, write_style) const override;
  };


  // Binder, or binding operator.
  class bound_formula : public nonempty_formula {
  public:
    ref<variable> variable_;  // Variable that is bound.
    ref<formula> domain_;     // Domain of variable.
    ref<formula> formula_;    // The formula that is bound.

    // The bind number identifies, within a formula, different binders and their
    // Used to enable local substitutions. Free variables have value 0.
    bind bind_ = 0;

    enum type { none_,
      all_, exist_, is_set_, set_, implicit_set, mapto_,
      other_
    };

    type type_ = none_;


    bound_formula() {}

    new_copy(bound_formula);
    new_move(bound_formula);

    bound_formula(const ref<variable>& v, const bound_formula::type& bt)
     : variable_(v), type_(bt) {}
    bound_formula(const ref<variable>& v, const ref<formula>& f, const bound_formula::type& bt, bind b = 0)
     : variable_(v), formula_(f), type_(bt) {}

    bound_formula(const ref<variable>& v, const ref<formula>& d, const ref<formula>& f, const bound_formula::type& bt, bind b = 0)
     : variable_(v), domain_(d), formula_(f), type_(bt) {}


    bound_formula(const variable_list& vs, const ref<formula>& f);

    bound_formula(const variable_list& vs, const ref<formula>& d, const ref<formula>& f);


    // Helper function, only used in this class implementation:
    bound_formula* push_back(const ref<variable>&, const bound_formula::type&);

    // Create an iteration of binders, as each can only bind a single variable:
    void push_back(const variable_list&);

    void set(const ref<formula>&);
    void set(const bound_formula&); // Assumes same bind identifier.
    void set(bind b) { bind_ = b; }

    bool is_quantified() const { return (type_ == all_) || (type_ == exist_); }

    virtual formula_type get_formula_type() const override { return object_formula_type_; }

    virtual alternatives unify(unify_environment, const ref<formula>&, unify_environment, database*, level, degree_pool&, direction) const override;
    virtual split_formula split(unify_environment, const ref<variable>&, const ref<formula>&, unify_environment, database*, level, degree_pool&, direction) const override;

    virtual kleenean has(const ref<variable>&, occurrence) const override;
    virtual void contains(std::set<ref<variable>>&, std::set<ref<variable>>&, bool&, occurrence) const override;

    virtual kleenean free_for(const ref<formula>& f, const ref<variable>& x, 
      std::set<ref<variable>>& s, std::list<ref<variable>>& bs) const override;

    void unspecialize(depth, bool) override;
    void unspecialize(std::set<ref<variable>>&, bool) override;

    virtual ref<formula> rename(level, degree) const override;
    virtual ref<formula> add_exception_set(variable_map&) const override;
    virtual ref<formula> substitute(const ref<substitution>&, substitute_environment) const override;

    virtual void set_bind(bind&, name_variable_table&) override;

    virtual order compare(const unit&) const override;

    virtual precedence_t precedence() const override;
    virtual void write(std::ostream&, write_style) const override;
    void write(std::ostream&, write_style, type) const;

    // Returns true b x A, when A is a variable, constant or predicate.
    bool body_simple() const;
  };


  // Only used to construct a variable list for use in other
  // objects, such as bound_formula.
  class variable_list : public unit {
  public:
    typedef std::pair<ref<variable>, bound_formula::type>  value_type;
    typedef std::list<value_type>          sequence_type;
    typedef sequence_type::iterator        iterator;
    typedef sequence_type::const_iterator  const_iterator;

    std::list<value_type> variables_;
    
    variable_list() = default;

    new_copy(variable_list);
    new_move(variable_list);

    variable_list(const ref<variable>& x, const bound_formula::type& bt)
     : variables_(1, value_type(x, bt)) {}

    void push_back(const ref<variable>& x, const bound_formula::type& bt)
    { variables_.push_back(value_type(x, bt)); }
    void push_back(const variable_list& x)
    { variables_.insert(variables_.end(), x.variables_.begin(), x.variables_.end()); }

    void splice_back(variable_list& x) { variables_.splice(variables_.end(), x.variables_); }
    void splice_front(variable_list& x) { variables_.splice(variables_.begin(), x.variables_); }

    void reverse() { variables_.reverse(); }

    virtual void write(std::ostream&, write_style) const override;
  };


  class formula_sequence : public nonempty_formula {
  public:
    using container_type = std::vector<ref<formula>>;

    typedef container_type::size_type size_type;
    typedef container_type::iterator iterator;
    typedef container_type::const_iterator const_iterator;
    typedef container_type::reverse_iterator reverse_iterator;
    typedef container_type::const_reverse_iterator const_reverse_iterator;

    container_type formulas_;


    formula_sequence() {}

    new_copy(formula_sequence);
    new_move(formula_sequence);


    formula_sequence(const ref<formula>& x)
     : formulas_(1, x) {}


    formula_sequence(std::initializer_list<ref<formula>> xs) : formulas_(xs) {}

    formula_sequence(const std::vector<ref<formula>>& xs)
     : formulas_(xs) {}

    formula_sequence(const std::list<ref<formula>>& xs)
     : formulas_(xs.begin(), xs.end()) {}

    formula_sequence(const formula_sequence& x, const formula_sequence& y)
     : formulas_(x.formulas_)
    { formulas_.insert(formulas_.end(), y.formulas_.begin(), y.formulas_.end()); }


    formula_sequence(const formula_sequence& x, const ref<formula>& y)
     : formulas_(x.formulas_) { formulas_.push_back(y); }

    formula_sequence(const ref<formula>& x, const formula_sequence& y)
     : formulas_({x}) { formulas_.insert(formulas_.end(), y.formulas_.begin(), y.formulas_.end()); }

    formula_type get_formula_type() const override;

    void push_back(const ref<formula>& t) { formulas_.push_back(t); }

    virtual ref<formula> get_formula(size_type k) const override {
      if (k >= formulas_.size()) return {};
      auto i = formulas_.begin(); std::advance(i, k);
      return *i;
    }

    ref<formula> add_goal(const ref<formula>& x) const override;

    ref<formula> add_premise(const ref<formula>& x, metalevel_t,
      const varied_type& vs, const varied_type& vrs) const override;


    virtual metalevel_t metalevel() const override;

    bool is_metasubset(const ref<formula> x) const override;

    bool meta_container_and_mode(target x) const override { return x == goal; }
    bool meta_container_or_mode(target x) const override { return x == fact; }


    virtual alternatives unify(unify_environment, const ref<formula>&, unify_environment, database*, level, degree_pool&, direction) const override;
    virtual split_formula split(unify_environment, const ref<variable>&, const ref<formula>&, unify_environment, database*, level, degree_pool&, direction) const override;

    virtual kleenean has(const ref<variable>&, occurrence) const override;
    virtual void contains(std::set<ref<variable>>&, std::set<ref<variable>>&, bool&, occurrence) const override;

    virtual kleenean free_for(const ref<formula>& f, const ref<variable>& x,
      std::set<ref<variable>>& s, std::list<ref<variable>>& bs) const override;

    void unspecialize(depth, bool) override;
    void unspecialize(std::set<ref<variable>>&, bool) override;

    virtual ref<formula> rename(level, degree) const override;
    virtual ref<formula> add_exception_set(variable_map&) const override;
    virtual ref<formula> substitute(const ref<substitution>&, substitute_environment) const override;

    virtual void set_bind(bind&, name_variable_table&) override;

    bool provable() const override;

    size_type metasize() const override;
    size_type formula_sequence_size() const override { return formulas_.size(); }

    bool unexpanded() const override;
    ref<formula> expand(size_type) const override;

    bool has_formula(ref<formula> x) const override;

    virtual order compare(const unit&) const override;

    virtual precedence_t precedence() const override;
    virtual void write(std::ostream&, write_style) const override;

    // Check if x, y are of type t, and return accordingly a formula_sequence of type t:
    friend ref<formula> concatenate(const ref<formula>& x, const ref<formula>& y);
  };


  // Concatenates in case x or y or both are formula sequences:
  // If x or y is empty the other is returned. So if both are empty, the return is an empty formula.
  // If x is not formula sequence and y is, x is prepended to y.
  // If x is a formula sequence and y is not, y is appended to x.
  // If both x and y are formula sequences, they are concatenated into a single formula sequence.
  ref<formula> concatenate(const ref<formula>& x, const ref<formula>& y);


  // End of formula sequence marker object □. Used in a unification with a formula sequence
  // variable 𝜞 when determining its unifying components, adding last a substitution [𝜞 ↦ □].
  class end_of_formula_sequence : public nonempty_formula {
  public:
    new_copy(end_of_formula_sequence);
    new_move(end_of_formula_sequence);

    bool is_end_of_formula_sequence() const override { return true; }

    virtual void write(std::ostream& os, write_style) const override
    { os << "□"; }

  };


  // The inference 𝜞 ⊢⁽𝜸⁾₍𝜸'₎ 𝑨 is a metapredicate ⊢(𝜞, 𝑨; 𝑩; 𝜸; 𝜸'), so arguments
  // are logic and objects of lower metalevel. Thus, proofs are not a part of the
  // original metalevel language, but a technique to describe what is valid in that
  // language.
  // The conclusion argument 𝑨 is permitted to be a formula sequence, but is
  // expanded before unification, that is
  //   𝜞 ⊢⁽𝜸⁾₍𝜸'₎ 𝑨₀, 𝑨₁, … ⤳ 𝜞 ⊢⁽𝜸₀⁾₍𝜸'₀₎ 𝑨₀; 𝜞 ⊢⁽𝜸₁⁾₍𝜸'₁₎ 𝑨₁; ….
  // where the components 𝜸₀, 𝜸₁, … and 𝜸'₀, 𝜸'₁, … are suitably recomputed.
  class inference : public nonempty_formula {
  public:
    ref<formula> head_;
    ref<formula> body_;

    metalevel_t metalevel_ = 1_ml;


    // Variables that are varied in the deduction or by formal declarations, that
    // is, free in a specific premise of the body but involves the application
    // of a universal quantifier ∀, to arrive at one of conclusion formulas.
    // There is thus one variable set for each formula pair: a premise and a conclusion.
    // It is prohibited to apply the Deduction Theorem and variants of it to such a
    // premise-conclusion pair.
    //
    // The following is a sparse matrix for the variables that have been quantified,
    // the outermost index is the conclusion or head formula, and the inner the premise
    // or body formula in respective formula sequences, with index 0 if not a formula sequence.
    varied_type varied_;

    // Variables that are varied in a reduction but not have unified with a premise,
    // and thus currently not varied variables of the inference, but which may become so
    // in a later reduction that unifies with a premise.
    // They are the same for each premise, but may vary with the conclusion index, thus
    // one variable set for each conclusion, implemented as a sparse vector.
    varied_type varied_in_reduction_;


    inference() = default;

    new_copy(inference);
    new_move(inference);


    explicit inference(const ref<formula>& h) : head_(h) {}

    inference(const ref<formula>& h, metalevel_t ml) : head_(h), metalevel_(ml) {}

    inference(const ref<formula>& h, const ref<formula>& b, metalevel_t ml)
     : head_(h), body_(b), metalevel_(ml) {}

    inference(const ref<formula>& h, metalevel_t ml, const varied_type& vs)
     : head_(h), metalevel_(ml), varied_(vs) {}

    inference(const ref<formula>& h, const ref<formula>& b, metalevel_t ml, const varied_type& vs)
     : head_(h), body_(b), metalevel_(ml), varied_(vs) {}

    inference(const ref<formula>& h, const ref<formula>& b, metalevel_t ml,
      const varied_type& vs, const varied_type& vrs)
     : head_(h), body_(b), metalevel_(ml), varied_(vs), varied_in_reduction_(vrs) {}


    // Varied variable premises arguments not attached to a number in a conclusion
    // formula sequence, so it is set to :

    inference(const ref<formula>& h, const ref<formula>& b, metalevel_t ml, const varied_premise_type& vs)
     : head_(h), body_(b), metalevel_(ml) { if(!vs.empty()) varied_[0] = vs; }

    inference(const ref<formula>& h, const ref<formula>& b, metalevel_t ml,
      const varied_premise_type& vs, const varied_premise_type& vrs)
     : head_(h), body_(b), metalevel_(ml) {
       if(!vs.empty()) varied_[0] = vs;
       if(!vrs.empty()) varied_in_reduction_[0] = vrs; }


    inference(const ref<formula>& h, const std::list<ref<formula>>& bfs, metalevel_t ml)
     : head_(h), body_(ref<formula_sequence>(make, bfs)), metalevel_(ml) {}

    virtual formula_type get_formula_type() const { return metaformula_type_; }

    virtual ref<formula> get_formula(size_type k) const;

    bool provable() const override;
    size_type metasize() const override { return head_->metasize(); }
    bool unexpanded() const override
    { return ref_cast<formula_sequence*>(head_) != nullptr || head_->unexpanded(); }

    ref<formula> expand(size_type) const override;

    ref<formula> add_premise(const ref<formula>& x, metalevel_t,
      const varied_type& vs, const varied_type& vrs) const override;

    virtual metalevel_t metalevel() const override { return metalevel_; }


    // Take into account the fact that the head can contain a formula sequence.
    bool meta_container_and_mode(target x) const override { return head_->meta_container_and_mode(x); }
    bool meta_container_or_mode(target x) const override { return head_->meta_container_or_mode(x); }

    // True when a goal if the premise is unexpanded and should be so, and it
    // should not be expanded if metalevel_ < x.metalevel_.
    // The case metalevel_ > x.metalevel_ only appears if the unify_environment
    // metalevel has not been proerly raised.
    bool unexpanded_premise(unify_environment x) const override
    { return x.target_ == goal && metalevel_ >= x.metalevel_ && !x.expanded_premise_; }


    virtual bool inference_mode() const override { return true; }

    virtual ref<formula> head() const { return head_; }
    virtual ref<formula> body() const { return body_; }


    virtual bool is_axiom() const;
    virtual bool is_rule() const;


    virtual alternatives unify(unify_environment, const ref<formula>&, unify_environment, database*, level, degree_pool&, direction) const override;
    virtual split_formula split(unify_environment, const ref<variable>&, const ref<formula>&, unify_environment, database*, level, degree_pool&, direction) const override;

    virtual kleenean has(const ref<variable>&, occurrence) const override;
    virtual void contains(std::set<ref<variable>>&, std::set<ref<variable>>&, bool&, occurrence) const override;

    virtual kleenean free_for(const ref<formula>& f, const ref<variable>& x,
      std::set<ref<variable>>& s, std::list<ref<variable>>& bs) const override;

    void unspecialize(depth, bool) override;
    void unspecialize(std::set<ref<variable>>&, bool) override;

    virtual ref<formula> rename(level, degree) const override;
    virtual ref<formula> add_exception_set(variable_map&) const override;
    virtual ref<formula> substitute(const ref<substitution>&, substitute_environment) const override;

    virtual void set_bind(bind&, name_variable_table&) override;

    virtual order compare(const unit&) const override;

    virtual precedence_t precedence() const override;
    virtual void write(std::ostream&, write_style) const override;
  };


  class database : public nonempty_formula {
  public:
    new_copy(database);
    new_move(database);

    virtual formula_type get_formula_type() const override { return metaformula_type_; }

    virtual alternatives unify(unify_environment, const ref<formula>&, unify_environment, database*, level, degree_pool&, direction) const override;

    virtual alternatives unify(const ref<formula>& x, unify_environment tx, const ref<formula>& y, unify_environment ty, database* dbp, level lv, degree_pool& sl, direction dr) const;


    virtual kleenean has(const ref<variable>&, occurrence) const override { return false; }
    virtual void contains(std::set<ref<variable>>&, std::set<ref<variable>>&, bool&, occurrence) const override {}

    virtual kleenean free_for(const ref<formula>&, const ref<variable>&, 
      std::set<ref<variable>>&, std::list<ref<variable>>&) const override { return true; }

    void unspecialize(depth, bool) override {}
    void unspecialize(std::set<ref<variable>>&, bool) override {}

    virtual ref<formula> rename(level, degree) const override;
    virtual ref<formula> add_exception_set(variable_map&) const override;
    virtual ref<formula> substitute(const ref<substitution>&, substitute_environment) const override {
      return ref<database>();
    }

    virtual void set_bind(bind&, name_variable_table&) override {}

    virtual database& operator[](size_type lv) { return *this; }

    virtual bool empty() const;
    virtual int get_level() const;
    virtual bool has_definition(level) const;

    virtual bool insert(const ref<statement>&);


    // Lookup statement with name nm in the database at level lv.
#if 1
    virtual std::optional<ref<statement>> find(const std::string& nm, level lv);
#else
    // If 'proved' is true, the default, only proved statements are looked for.
    virtual std::optional<ref<statement>> find(const std::string& nm, level lv, bool proved = false);
#endif

    // A database behaves as a metaor if a fact, and as a metand if a goal, that is,
    // if it is proved, one can pick one statement and apply it as a fact, but if it
    // should be proved, all statements in it must be proved as goals.

    bool meta_container_and_mode(target x) const override { return x == goal; }
    bool meta_container_or_mode(target x) const override { return x == fact; }

    virtual size_type metasize() const override { return 0; }

    virtual order compare(const unit&) const override { return unordered; }

    virtual void write(std::ostream&, write_style) const override;
  };


  // Write a list of proofs.
  void write_proofs(std::ostream& os, std::list<proof>& pfs);

  // Write a set variables.
  void write_variables(std::ostream& os, write_style ws, std::set<ref<variable>>& vs);


  // Functions to be used when statement variables are allowed to specialize in proof.

#define WRITE_SOLUTIONS 0

#if WRITE_SOLUTIONS
  // Write one solution.
  void write_solution(std::ostream& os, write_style ws, std::set<ref<variable>>& vs, ref<substitution> s);

  // Write a list of substitutions.
  void write_solution(std::ostream& os, std::list<ref<substitution>>& ss);

  // Write variables that get new values by the substitutions.
  void write_solution(std::ostream& os, write_style ws,
    std::set<ref<variable>>& vs, std::list<ref<substitution>>& ss);
#endif

} // namespace mli


