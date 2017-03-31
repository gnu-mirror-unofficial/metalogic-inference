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

#ifndef header_MLI_hh
#define header_MLI_hh

#include <iostream>
#include <list>
#include <map>
#include <set>
#include <stdexcept>
#include <string>
#include <typeinfo>

#include <climits>


namespace mli {

class parse_error : public std::logic_error {
public:
  explicit parse_error(const char* what_arg) : std::logic_error(what_arg) {}
  explicit parse_error(const std::string& what_arg) : std::logic_error(what_arg) {}
};

typedef std::runtime_error runtime_error;

class interpret_error : public std::runtime_error {
public:
  explicit interpret_error(const char* what_arg) : std::runtime_error(what_arg) {}
  explicit interpret_error(const std::string& what_arg) : std::runtime_error(what_arg) {}
};

typedef long int_type;
typedef unsigned long size_type;

extern size_type level_max;
extern size_type sublevel_max;
extern size_type unify_count_max;


enum {
  trace_bit            = 0x1,
  trace_null           = (trace_bit << 0),
  trace_result         = (trace_bit << 1),
  trace_proof          = (trace_bit << 2),
  trace_prooftree      = (trace_bit << 3),
  trace_unify          = (trace_bit << 4),
  trace_split          = (trace_bit << 5),
  trace_substitute     = (trace_bit << 6),
  trace_cut            = (trace_bit << 7),
  trace_labelstatement = (trace_bit << 8),
  trace_database       = (trace_bit << 9),
  trace_formula_type   = (trace_bit << 10),
  trace_variable_type  = (trace_bit << 11),
  trace_bind           = (trace_bit << 12),
  trace_structure_type = (trace_bit << 13)
};

typedef int trace_type;
extern trace_type trace_value;


typedef int relation;
#if 1
const relation unrelated = -2;
const relation less = -1;
const relation equal = 0;
const relation greater = 1;
#else
enum {
  unrelated = -2,
  less = -1,
  equal = 0,
  greater = 1
};
#endif

template<class X, class Y>
relation inequality_compare(const X& x, const Y& y) {
  if (x < y)   return mli::less;
  if (x > y)   return mli::greater;
  if (x == y)  return mli::equal;
  return unrelated;
}

template<class A> // The sign of a number:
inline int sgn(A x) { return (x > 0) - (x < 0); }


template <class Iterator>
relation lexicographical_compare(Iterator first1, Iterator last1,
                       Iterator first2, Iterator last2) {
  for (; first1 != last1 && first2 != last2; ++first1, ++first2) {
    relation r = compare(*first1, *first2);
    if (r != 0)  return r;
  }
  return (first1 != last1) - (first2 != last2);
}

template <class Iterator>
relation lexicographical_total(Iterator first1, Iterator last1,
                     Iterator first2, Iterator last2) {
  for (; first1 != last1 && first2 != last2; ++first1, ++first2) {
    relation r = total(*first1, *first2);
    if (r != 0)  return r;
  }
  return (first1 != last1) - (first2 != last2);
}



template <class Iterator>
relation lexical_compare(Iterator first1, Iterator last1,
                       Iterator first2, Iterator last2) {
  for (; first1 != last1 && first2 != last2; ++first1, ++first2) {
    relation r = compare(*first1, *first2);
    if (r != 0)  return r;
  }
  return (first1 != last1) - (first2 != last2);
}

template <class Iterator>
relation lexical_total(Iterator first1, Iterator last1,
                     Iterator first2, Iterator last2) {
  for (; first1 != last1 && first2 != last2; ++first1, ++first2) {
    relation r = total(*first1, *first2);
    if (r != 0)  return r;
  }
  return (first1 != last1) - (first2 != last2);
}


class kleenean {
public:
  int value_;
  
  kleenean() : value_(0) {}
  kleenean(const bool& b) : value_(b) {}
  kleenean(const int& x) : value_(x) {}
  
  operator int() { return value_; }
  operator const int() const { return value_; }
  
  friend kleenean operator!(const kleenean&);
  friend kleenean operator||(const kleenean&, const kleenean&);
  friend kleenean operator&&(const kleenean&, const kleenean&);

  friend bool operator==(const kleenean&, const kleenean&);
  friend bool operator!=(const kleenean&, const kleenean&);

  friend std::ostream& operator<<(std::ostream&, const kleenean&);
};


extern const kleenean undecidable;

extern const kleenean fail;
extern const kleenean succeed;


inline kleenean operator!(const kleenean& x) {
  if (x.value_ == false)  return true;
  if (x.value_ == true)  return false;
  return undecidable;
}

inline kleenean operator||(const kleenean& x, const kleenean& y) {
  if (x.value_ == true || y.value_ == true)  return true;
  if (x.value_ == false && y.value_ == false)  return false;
  return undecidable;
}

inline kleenean operator&&(const kleenean& x, const kleenean& y) {
  if (x.value_ == false || y.value_ == false)  return false;
  if (x.value_ == true && y.value_ == true)  return true;
  return undecidable;
}

inline bool operator==(const kleenean& x, const kleenean& y) {
  return (x.value_ == y.value_);
}

inline bool operator!=(const kleenean& x, const kleenean& y) {
  return (x.value_ != y.value_);
}

inline std::ostream& operator<<(std::ostream& os, const kleenean& x) {
  if (x.value_ == false)  os << "fail";
  if (x.value_ == true)  os << "succeed";
  os << "undecidable";
  return os;
}


template<class Value>
class maybe {
  bool non_empty_;
  Value value_;

public:
  maybe() : non_empty_(false) {}
  maybe(bool non_empty) : non_empty_(non_empty) {}
  maybe(const Value& v) : non_empty_(true), value_(v) {}

  bool operator!() const { return !non_empty_; }

  Value& operator*() {
    if (!non_empty_)  throw interpret_error("Taking maybe<>::operator*(empty).");
    return value_;
  }
  Value* operator->() {
    if (!non_empty_)  return 0;
    return &value_;
  }
};


template<class Key, class T, class Compare = std::less<Key> >
class table_stack {
public:
  typedef Key              key_type;
  typedef std::map<Key, T, Compare> table;
  typedef std::list<table>         stack;
  typedef typename stack::size_type         size_type;

  typedef T                            mapped_type;
  typedef std::pair<const key_type, T> value_type;

//private:
  stack table_stack_;

public:
  table_stack() {}

  // Refer to the stack, not the table at each level:
	bool      empty() const { return table_stack_.empty(); }
	size_type size() const  { return table_stack_.size(); }
  table& top()            { return table_stack_.back(); }

  bool insert(const Key&, const T&);
  // Insert at level below top, if possible.
  bool insert_below(const Key&, const T&);
  maybe<T> find(const Key&);
  maybe<T> find_top(const Key&);
  
  // Finds highest level matching both name and mapped value property:
  template<class Property>
  maybe<T> find(const Key& key, Property p) {
    typename stack::reverse_iterator i, i0 = table_stack_.rbegin(), i1 = table_stack_.rend();
    for (i = i0; i != i1; ++i) {
      typename table::iterator j = i->find(key);
      if (j != i->end() && p(j->second))
        return j->second;  // Variable key with matching property found:
    }
    return false;
  }

  void push_level();
  void pop_level();
  void clear();
};


template<class Key, class T, class Compare>
bool table_stack<Key, T, Compare>::insert(const Key& key, const T& x) {
  if (table_stack_.empty())
    return false;
  return table_stack_.back().insert(std::pair<const Key, T>(key, x)).second;
}

template<class Key, class T, class Compare>
bool table_stack<Key, T, Compare>::insert_below(const Key& key, const T& x) {
  if (table_stack_.empty())
    return false;
  if (table_stack_.size() == 1)
    return table_stack_.back().insert(std::pair<const Key, T>(key, x)).second;
  return (--(--table_stack_.end()))->insert(std::pair<const Key, T>(key, x)).second;
}

template<class Key, class T, class Compare>
inline maybe<T> table_stack<Key, T, Compare>::find(const Key& key) {
  typename stack::reverse_iterator i, i0 = table_stack_.rbegin(), i1 = table_stack_.rend();
  for (i = i0; i != i1; ++i) {
    typename table::iterator j = i->find(key);
    if (j != i->end())
      return j->second;  // Variable key found:
  }
  return false;
}

template<class Key, class T, class Compare>
inline maybe<T> table_stack<Key, T, Compare>::find_top(const Key& key) {
  typename stack::reverse_iterator i0 = table_stack_.rbegin();
  typename table::iterator j = i0->find(key);
  if (j != i0->end())
    return j->second;  // Variable key found:
  return false;
}

template<class Key, class T, class Compare>
inline void table_stack<Key, T, Compare>::push_level() {
  table_stack_.push_back(table());
}

template<class Key, class T, class Compare>
inline void table_stack<Key, T, Compare>::pop_level() {
  table_stack_.pop_back();
}

template<class Key, class T, class Compare>
inline void table_stack<Key, T, Compare>::clear() {
  table_stack_.clear();
  push_level();
}


enum write_style {
  // Statements:
  write_proof_margin_level = 0x0F,  // Margin level for proof: 0, ..., 15.
  write_proof_margin_tab = 0xF0,    // Number of spaces for each margin level: 0, ..., 15.
  tabs2 = (2 << 4),                 // Margin tab = 2 spaces.
  write_bit = 0x0100,               // Lowest bit of write mask.
  write_name = write_bit << 0,      // `1.7'
  write_type = write_bit << 1,      // theorem 1.7
  write_statement = write_bit << 2, // theorem 1.7. |- A => A.
  write_unproved = write_bit << 3,  // theorem 1.7 [*unproved*]. |- A => A.
  write_proof = write_bit << 4,     // With proof.
  write_proof_indent = write_bit << 5, // Proof lines indented relative statement.
  write_proof_begin_newline = write_bit << 6, // '\n' after "proof."
  // No '\n' after "proof." if proof is 1 line:
  write_oneline_proof_begin_no_newline = write_bit << 7,
  write_proof_end_newline = write_bit << 8, // '\n' before "##."
  // No '\n' before "proof." if proof is 1 line.
  write_oneline_proof_end_no_newline = write_bit << 9,
  write_substitution_mapto_reverse = write_bit << 10, // Reverse: ~[a/x]A.
  write_substitution_composition_reverse = write_bit << 11, // Reverse: (f o g)(x) = g(f(x)).
  write_default =
      0         // Proof margin level.
    | tabs2
    | write_name | write_type | write_statement | write_unproved
    | write_proof | write_proof_indent
    | write_proof_begin_newline | write_proof_end_newline
};


class argument_precedence;
class operator_precedence;


class precedence_root {
public:
  enum associativity {
    left = 0x1, right = (left << 1), non = (right << 1)
  };
  enum fixity {
    infix, prefix, suffix, enfix
  };
protected:
  int precedence_; // Always > 0.
  associativity associativity_;
  fixity fixity_;
    
public:
  // Default constructor = non precedence set.
  precedence_root(int p = INT_MAX, associativity a = non, fixity f = enfix)
   : precedence_(p), associativity_(a), fixity_(f) {}
};


class operator_precedence : public precedence_root {
public:	
  friend class argument_precedence;

  operator_precedence(int p = INT_MAX, associativity a = non, fixity f = enfix)
   : precedence_root(p, a, f) {}

  argument_precedence first_argument() const;     
  argument_precedence middle_argument() const;     
  argument_precedence last_argument() const;
  
  // x < y if x as argument of y requires grouping like "()", "{}", etc., in writeout.
  friend bool operator<(const operator_precedence& x, const argument_precedence& y);
};


class argument_precedence : public precedence_root {
public:
  friend class operator_precedence;
  
  enum where { first_, middle_, last_ };
  where where_;

  // Default constructor = non precedence set.
  argument_precedence(int p = INT_MAX, associativity a = non,
    fixity f = enfix, where w = first_)
   : precedence_root(p, a, f), where_(w) {}

  // x < y if x as argument of y requires grouping like "()", "{}", etc., in writeout.
  friend bool operator<(const operator_precedence& x, const argument_precedence& y);
};


typedef unsigned bind;
typedef unsigned depth;
typedef unsigned level;
typedef unsigned sublevel;


// Indentation shows class hierarchy:
class object;
  class alternative;
  class alternatives;
  class proof;
  class database;
  class formula;
    class sequence;
    class substitution;
    class substitution_formula;
    class variable;
  class labelstatement;
  class variable_list;

class split_formula;
class inference_stack;
class inference_tree;
class unify_environment;
class substitute_environment;


enum occurrence {
  free_occurrence,
  bound_occurrence,
  declared_occurrence,
  any_occurrence
};


typedef bool direction;
const direction reverse = false;
const direction forward = true;

typedef bool target;
const target goal = false;
const target choice = true;


template<class A>
class ref {
protected:
  mutable A* data_;
  static typename A::null_type null_;

public:
  typedef A&         reference;
  typedef A*         pointer;
  typedef const A&   const_reference;
  typedef const A*   const_pointer;

  typedef ref<A> This;

  ref() : data_(0) {}
  ~ref() { shed(); }

  ref(const ref& x) : data_(x.copy()) {}
  ref& operator=(const ref& x) {
    if (data_ != x.data_) { shed(); data_ = x.copy(); }
    return *this;
  }

  // Conversion constructors.
  ref(A* ap) : data_(ap) {}
  ref(const A* ap) : data_(ap->copy()) {}
  ref(const A& a) : data_(a.copy()) {}

  template<class B>
  explicit ref(B* bp, bool dynamic = true)
   : data_(dynamic? dynamic_cast<A*>(bp) : static_cast<A*>(bp)) {}

  template<class B>
  explicit ref(const B& br, bool dynamic = true)
   : data_(dynamic? dynamic_cast<A*>(br.copy()) : static_cast<A*>(br.copy())) {}

  ref<A> clone() const { return (data_ == 0)? 0 : data_->clone(); }
  A* copy() const { return (data_ == 0)? 0 : data_->copy(); }

  void shed() { if (data_ != 0)  data_->shed(); }

  bool is_null() const { return (data_ == 0); }

  // Operators that return pointer 0 when applicable: 

  operator A*() { return data_; }
  operator const A*() const { return data_; }

  // Operators that return reference to an object A() when applicable: 

  // Return a pointer to the referenced object, or if 0, the A::null_ object:
  A* operator->() { if (data_ == 0) return &null_; else return data_; }
  const A* operator->() const { if (data_ == 0) return &null_; else return data_; }

  // Return a reference to the referenced object, or if 0, the A::null_ object:
  A& operator*() { if (data_ == 0) return null_; else return *data_; }
  const A& operator*() const { if (data_ == 0) return null_; else return *data_; }

  // Create an independent copy of the referenced object.
  ref<A> detach() const {
    if (data_ != 0 && data_->count() > 1) { data_->shed(); data_ = data_->clone(); }
    return copy();
  }

  // If 0, mutate to new A(). Return a reference to an independent copy of the
  // referenced object.
  A& operator+() const {
    if (data_ == 0)  data_ = new A();
    else if (data_->count() > 1) { data_->shed(); data_ = data_->clone(); }
    return *data_;
  }
};


template<class A, class B>
A* cast_pointer(ref<B>& ar) { return dynamic_cast<A*>((B*)ar); }

template<class A, class B>
const A* cast_pointer(const ref<B>& ar) { return dynamic_cast<const A*>((const B*)ar); }

template<class A, class B>
A& cast_reference(ref<B>& ar) { return dynamic_cast<A&>(*(B*)ar); }

template<class A, class B>
const A& cast_reference(const ref<B>& ar) { return dynamic_cast<const A&>(*(const B*)ar); }


#define ref_null(A) template <> A::null_type ref<A>::null_ = A::null_type()

// Use the clone_declare/clone_source if clone he
#define clone_class(A)  virtual A* clone() const { return new A(*this); }
#define copy_class(A)  virtual A* copy() const { increment_count(); return const_cast<A*>(this); }

#define clone_declare(A)  virtual A* clone() const
#define clone_source(A)  A* A::clone() const { return new A(*this); }

#define copy_declare(A)  virtual A* copy() const
#define copy_source(A)  A* A::copy() const { increment_count(); return const_cast<A*>(this); }


template<class A>
inline std::istream& operator>>(std::istream& is, ref<A>& a) {
  return is >> (*a);
}

template<class A>
inline std::ostream& operator<<(std::ostream& os, const ref<A>& a) {
  return os << (*a);
}

template<class A>
inline relation compare(const ref<A>& x, const ref<A>& y) {
  return compare(*x, *y);
}

template<class A>
inline relation total(const ref<A>& x, const ref<A>& y) {
  return total(*x, *y);
}

template<class A>
inline bool operator==(const ref<A>& x, const ref<A>& y) {
  return (*x == *y);  
}

template<class A>
inline bool operator!=(const ref<A>& x, const ref<A>& y) {
  return (*x != *y);
}

template<class A>
inline bool operator<(const ref<A>& x, const ref<A>& y) {
  return (*x < *y);
}

template<class A>
inline bool operator<=(const ref<A>& x, const ref<A>& y) {
  return (*x <= *y);
}

template<class A>
inline bool operator>(const ref<A>& x, const ref<A>& y) {
  return (*x > *y);
}

template<class A>
inline bool operator>=(const ref<A>& x, const ref<A>& y) {
  return (*x >= *y);
}

template<class A>
inline ref<A> operator+(const ref<A>& x, const ref<A>& y) {
  return (*x + *y);
}

template<class A>
inline ref<A> operator*(const ref<A>& x, const ref<A>& y) {
  return ((*x) * (*y));
}


class object {
  typedef unsigned long count_type;
  mutable count_type count_;
public:
  typedef object null_type;

  object() : count_(1) {}
  virtual ~object() {}
  
  object(const object&) : count_(1) {}

  void increment_count() const { ++count_; }
  count_type count() const { return count_; }

  clone_declare(object);
  copy_declare(object);

  void shed() { if (--count_ == 0)  delete this; }

  virtual void write(std::ostream& os, write_style) const { os << "object"; }
};

inline std::ostream& operator<<(std::ostream& os, const object& a) {
  a.write(os, write_default);  return os;
}


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

enum sequence_type { other_sequence_,
  metapredicate_argument_,
  metaor_, metaand_, predicate_argument_,
  function_argument_,
  member_list_set_, implicit_set_,
  vector_, list_, bracket_
};


class formula_null;

typedef table_stack<std::string, ref<variable> > name_variable_table;
typedef table_stack<ref<variable>, ref<formula> > variable_table;


  // Meta and object formulas.
class formula : public object {
public:
  typedef unsigned long size_type;
  typedef formula_null null_type;

  clone_declare(formula) = 0;
  copy_declare(formula) = 0;

  virtual formula_type get_formula_type() const = 0;

  // Variable renumbering:
  ref<formula> set_bind(); // Set numbering of binders and their associated bound variables.
  virtual void set_bind(bind&, name_variable_table&) = 0;
  virtual ref<formula> rename(level, sublevel) const = 0;

  // Free variables:
  virtual kleenean has(const ref<variable>&, occurrence) const = 0;

  // Find all variables of the category indicated by the occurrence argument.
  // The second argument collects the bound variables (needed for correct computation
  // of the free variables).
  // The bool& argument will be set to true if the search encounters a metavariable
  // that, if later substituted, may contain more variables of the search type.
  // This is needed by free_for() which will then be undecidable.
  virtual void contains(std::set<ref<variable> >&, std::set<ref<variable> >&, bool&, occurrence) const = 0;

  // The bool value as a return instead of as an argument:
  bool contains(std::set<ref<variable> >& s, occurrence oc) const;

  // Compute f free for x in *this, i.e., true if no free occurance of x in *this
  // is in the scope of a binder b y, where y is free in f; otherwise false. Thus,
  // if true, substituting f for x in *this does not cause any free variables of
  // f to become bound.
  kleenean free_for(const ref<formula>& f, const ref<variable>& x) const;

  // Implementation helper function:
  //   free_for(f, x, s, bs)
  // s = set of variables that cannot become bound at free occurance of x,
  // bs = bound variables currently in scope.
  virtual kleenean free_for(const ref<formula>&, const ref<variable>&, 
    std::set<ref<variable> >&, std::list<ref<variable> >&) const = 0;

  // Make variables unspecializable during proof (ensuring generality):
  virtual void unspecialize(depth, bool) = 0;

  // Proving & solving.
  virtual kleenean succeed_or_fail() const { return undecidable; }

  // Substitution:
  virtual ref<formula> substitute(const ref<substitution>&, substitute_environment) const = 0;

  // Unification:
  virtual ref<alternatives> unify(unify_environment, const ref<formula>&, unify_environment, database*, level, sublevel&, direction) const = 0;

  // Find <subformulas, formula> pairs (fs, g) where g is obtained from 
  // f := *this by replacing subexpression trees v_1, ..., v_k such that
  // unify(t, v_1, ..., v_k) exists each by x.
  // This is used when finding all substitution solutions to unify([x\t]A, f),
  // where A is an unknown.
  virtual split_formula split(unify_environment, const ref<variable>&, const ref<formula>&, unify_environment, database*, level, sublevel&, direction) const;

  friend split_formula split(const ref<formula>& f,
    const ref<variable>& x, const ref<formula>& t, database*, level lv, sublevel& sl, direction dr);

  // Special unify function to expand the metaor of an inference body:
  virtual ref<alternatives> unify_inference(const ref<formula>& head, unify_environment, const ref<formula>&, unify_environment, database*, level, sublevel&, direction) const;

  // In the case of an inference A |- B, head = B, body = A. In other cases,
  // the whole formula is the head, and the body is empty.
  virtual ref<formula> head() const { return *this; }
  virtual ref<formula> body() const { return ref<formula>(); }

  // Return true if an empty metaand object or null, else return false:
  virtual bool metaempty() const { return false; }

  // Return the number of metaand arguments.
  virtual size_type metasize() const { return 1; }

  // If a metaand object, return the reversed one; else return the whole formula:
  virtual ref<formula> metareverse() const { return *this; }

  // Comparison, needed for unification and database lookup.
  virtual relation compare(const formula&) const = 0;
  virtual relation total(const formula&) const = 0;

  // Writing:
  virtual operator_precedence precedence() const { return operator_precedence(); }
  virtual void write(std::ostream& os, write_style) const
  { if (trace_value & trace_null)  os << "∅"; }
};


class formula_null : public formula {
public:
  clone_declare(formula_null);
  copy_declare(formula_null);

  virtual formula_type get_formula_type() const { return no_formula_type_; }
  virtual void set_bind(bind&, name_variable_table&) {}
  virtual ref<formula> rename(level, sublevel) const { return (formula*)0; }

  virtual kleenean has(const ref<variable>&, occurrence) const { return false; }
  virtual void contains(std::set<ref<variable> >&, std::set<ref<variable> >&, bool&, occurrence) const {}

  virtual kleenean free_for(const ref<formula>&, const ref<variable>&, 
    std::set<ref<variable> >&, std::list<ref<variable> >&) const { return true; }
  virtual void unspecialize(depth, bool) {}

  virtual ref<formula> substitute(const ref<substitution>&, substitute_environment) const;
  virtual ref<alternatives> unify(unify_environment, const ref<formula>&, unify_environment, database*, level, sublevel&, direction) const;

  virtual ref<formula> head() const { return (formula*)0; }

  virtual kleenean succeed_or_fail() const { return succeed; }
  virtual bool metaempty() const { return true; }
  virtual size_type metasize() const { return 0; }

  virtual ref<formula> metareverse() const { return (formula*)0; }

  virtual relation compare(const formula&) const;
  virtual relation total(const formula&) const;

};


// Master unification function:
ref<alternatives> unify(const ref<formula>&, unify_environment, const ref<formula>&, unify_environment, database*, level, sublevel&, direction = forward);

// Helper function that sort out unification precedence between objects, with
// no top level definitions expansion:
ref<alternatives> pre_unify(const ref<formula>&, unify_environment, const ref<formula>&, unify_environment, database*, level, sublevel&, direction);

ref<alternatives> unify(const std::list<ref<formula> >&, database*, level, sublevel&);
ref<alternatives> unify(const ref<formula>&, const std::list<ref<formula> >&, database*, level, sublevel&);


inline relation compare(const formula& x, const formula& y) {
#if 0 // Too slow!
  if (typeid(x) != typeid(y))  return unrelated;
#endif
  return x.compare(y);
}

inline relation total(const formula& x, const formula& y) {
#if 0 // Too slow!
  const std::type_info& tx = typeid(x);  const std::type_info& ty = typeid(y);
  if (tx != ty)  return tx.before(ty)? less : greater;
#endif
  return x.total(y);
}

inline bool operator==(const formula& x, const formula& y) {
  return x.compare(y) == equal;  
}

inline bool operator!=(const formula& x, const formula& y) {
  return x.compare(y) != equal;
}

inline bool operator<(const formula& x, const formula& y) {
  return x.compare(y) == less;
}

inline bool operator<=(const formula& x, const formula& y) {
  relation r = x.compare(y);
  return (r == less) || (r == equal);
}

inline bool operator>(const formula& x, const formula& y) {
  return x.compare(y) == greater;
}

inline bool operator>=(const formula& x, const formula& y) {
  relation r = x.compare(y);
  return (r == greater) || (r == equal);
}


  // Metaobject with name holding a statement plus information about provabiliy,
  // provedness status, and an eventual proof.
class labelstatement : public formula {
public:
  typedef labelstatement null_type;

  labelstatement() {}

  clone_declare(labelstatement);
  copy_declare(labelstatement);

  virtual formula_type get_formula_type() const { return metaformula_type_; }

  virtual ref<alternatives> unify(unify_environment, const ref<formula>&, unify_environment, database*, level, sublevel&, direction) const;

  virtual kleenean has(const ref<variable>&, occurrence) const { return false; }
  virtual void contains(std::set<ref<variable> >&, std::set<ref<variable> >&, bool&, occurrence) const {}

  virtual kleenean free_for(const ref<formula>&, const ref<variable>&, 
    std::set<ref<variable> >&, std::list<ref<variable> >&) const { return true; }

  virtual void unspecialize(depth, bool) {}
  virtual ref<formula> rename(level, sublevel) const { return *this; }
  virtual ref<formula> substitute(const ref<substitution>&, substitute_environment) const;

  // Variable renumbering:
  virtual void set_bind(bind&, name_variable_table&) {}
  // Initiate numbering of binders and their associated bound variables:
  ref<labelstatement> set_bind();

  virtual void declared(std::set<ref<variable> >&) const {}

  // Statement access:
  virtual std::string name() const { return std::string(); }
  virtual statement_type get_statement_type() const { return no_statement; }

  virtual ref<formula> get_statement() const { return (formula*)0; }
  virtual ref<formula> head() const { return (formula*)0; }
  virtual ref<formula> body() const { return (formula*)0; }

  // Proving & solving.
  virtual bool prove() { return false; }
  virtual bool is_proved() const { return false; }

  virtual relation compare(const formula&) const { return unrelated; }
  virtual relation total(const formula&) const { return unrelated; }

  virtual void write(std::ostream& os, write_style) const { os << "empty labelstatement"; }
};


class named_statement : public labelstatement {
public:
  typedef named_statement null_type;

  std::string name_;
  ref<formula> statement_;

  named_statement() {}
  named_statement(const std::string& nm, const ref<formula>& f) : name_(nm), statement_(f) {}

  clone_declare(named_statement);
  copy_declare(named_statement);

  virtual formula_type get_formula_type() const { return metaformula_type_; }

  virtual ref<alternatives> unify(unify_environment, const ref<formula>&, unify_environment, database*, level, sublevel&, direction) const;

  virtual kleenean has(const ref<variable>&, occurrence) const { return false; }
  virtual void contains(std::set<ref<variable> >&, std::set<ref<variable> >&, bool&, occurrence) const {}

  virtual kleenean free_for(const ref<formula>&, const ref<variable>&, 
    std::set<ref<variable> >&, std::list<ref<variable> >&) const { return true; }

  virtual void unspecialize(depth d, bool b) { statement_->unspecialize(d, b); }
  virtual ref<formula> rename(level, sublevel) const;
  virtual ref<formula> substitute(const ref<substitution>&, substitute_environment) const;

  // Variable renumbering:
  virtual void set_bind(bind& b, name_variable_table& vs);
  // Initiate numbering of binders and their associated bound variables:
  ref<labelstatement> set_bind();

  virtual void declared(std::set<ref<variable> >&) const {}

  // Statement access:
  virtual std::string name() const { return name_; }
  virtual statement_type get_statement_type() const { return no_statement; }

  virtual ref<formula> get_statement() const { return statement_; }
  virtual ref<formula> head() const { return statement_->head(); }
  virtual ref<formula> body() const { return statement_->body(); }

  // Proving & solving.
  virtual bool prove() { return false; }
  virtual bool is_proved() const { return false; }

  virtual relation compare(const formula&) const { return unrelated; }
  virtual relation total(const formula&) const { return unrelated; }

  virtual void write(std::ostream& os, write_style) const { os << "empty labelstatement"; }
};


class variable : public formula {
public:
  typedef variable null_type;

  std::string name;
  // Level numbers. Semantically, name plus level numbers act as a variable
  // identifier.
  depth depth_;        // Proof nesting depth; top = 0.
  level level_;        // Formula instantiation level, bottom = 0.
  sublevel sublevel_;  // Definition instantiation sublevel, subbottom = 0.

  // The free and bound variables belong to the logic, the others
  // to the metalogic.
  // The order in the list below cannor be changed, as used in several searches.
  enum type { none_,
    metaformula_, metapredicate_,
    formula_, predicate_, atom_,
    term_, function_, constant_,
    metaobject_, object_
  } type_;

  bool unspecializable_;  // Variables kept unspecializable during proof.

  static std::string type_name(type);  // Produce a string from type.

  variable() : type_(none_), depth_(0), unspecializable_(false), level_(0), sublevel_(0) {}

  clone_declare(variable);
  copy_declare(variable);

  variable(std::string s, type t, depth d, level lv = 0, sublevel sl = 0)
   : name(s), type_(t), depth_(d), unspecializable_(false), level_(lv), sublevel_(sl) {}

  virtual variable::type variable_type() const { return type_; }

  // True iff a substitution of *this may result in an expression containing x:
  bool may_contain(const ref<variable>& x) const;

  // True iff if a variable of type x may be substitued by a variable of type y:
  static bool is_specializable_to(type x, type y);

  bool is_meta() const; // Is a part of the metatheory; any variable but object_.

  bool is_metaobject() const;

  bool represents_object_variable() const;

  bool is_object() const; 

  bool is_metaformula() const;
  bool is_formula() const;
  bool is_term() const;

  bool is_unspecializable() const;
  bool get_depth() const;

  virtual formula_type get_formula_type() const {
    return is_metaformula()? metaformula_type_
            : (is_formula()? object_formula_type_ : term_type_); }

  virtual ref<alternatives> unify(unify_environment, const ref<formula>&, unify_environment, database*, level, sublevel&, direction) const;

  kleenean free_in(const ref<formula>&) const;
  virtual kleenean has(const ref<variable>&, occurrence) const;
  virtual void contains(std::set<ref<variable> >&, std::set<ref<variable> >&, bool&, occurrence) const;

  virtual kleenean free_for(const ref<formula>& f, const ref<variable>& x, 
    std::set<ref<variable> >& s, std::list<ref<variable> >& bs) const;

  virtual void unspecialize(depth, bool);
  virtual ref<formula> rename(level, sublevel) const;
  virtual ref<formula> substitute(const ref<substitution>&, substitute_environment) const;

  virtual void set_bind(bind&, name_variable_table&) {}

  // compare() is on the object level the classical variable comparison, comparing only
  // name and level numbers, even though on the meta level, also type is compared.
  // For comparing also other data, use total().
  virtual relation compare(const formula&) const;
  virtual relation total(const formula&) const;

  virtual void write(std::ostream&, write_style) const;
};


class unify_environment {
public:
  typedef variable_table table_type;

  table_type* table_;     // Bound variables lookup.
  target target_;
  bool is_generalization_;

  unify_environment() : table_(0), is_generalization_(false) {}

  unify_environment(const target& t) : table_(0), target_(t), is_generalization_(false) {}
  unify_environment(table_type* tbl, const target& t, bool gen)
   : table_(tbl), target_(t), is_generalization_(gen) {}

  void push() {
    if (table_ == 0)  table_ = new table_type();
    table_->push_level();
  }
  void pop() {
     if (table_->size() == 1) { delete table_; table_ = 0; }
     else table_->pop_level();
  }

  unify_environment operator!() const
  { return unify_environment(table_, !target_, is_generalization_); }
};


class push_bound {
  unify_environment* uf_;
public:
  push_bound() : uf_(0) {}
  ~push_bound() { if (uf_ != 0)  uf_->pop(); }

  push_bound(unify_environment& uf) : uf_(&uf) { uf_->push(); }
};



class substitute_environment {
public:
  typedef variable_table table_type;

  table_type* table_;

  substitute_environment() : table_(0) {}
  substitute_environment(table_type* tbl) : table_(tbl) {}
  substitute_environment(const unify_environment& ue) : table_(ue.table_) {}
};


class constant : public formula {
public:
  typedef formula_type type;

  std::string name;
  type type_;

  constant() : type_(no_formula_type_) {}

  clone_declare(constant);
  copy_declare(constant);

  constant(std::string s, type t) : name(s), type_(t) {}

  virtual formula_type get_formula_type() const { return type_; }

  virtual ref<alternatives> unify(unify_environment, const ref<formula>&, unify_environment, database*, level, sublevel&, direction) const;

  virtual kleenean has(const ref<variable>&, occurrence) const { return false; }
  virtual void contains(std::set<ref<variable> >&, std::set<ref<variable> >&, bool&, occurrence) const {}

  virtual kleenean free_for(const ref<formula>&, const ref<variable>&, 
    std::set<ref<variable> >&, std::list<ref<variable> >&) const
  { return true; }

  virtual void unspecialize(depth, bool) {}
  virtual ref<formula> rename(level, sublevel) const { return *this; }
  virtual ref<formula> substitute(const ref<substitution>&, substitute_environment) const { return *this; }

  virtual void set_bind(bind&, name_variable_table&) {}

  virtual relation compare(const formula&) const;
  virtual relation total(const formula&) const;

  virtual void write(std::ostream&, write_style) const;

  friend bool operator==(const constant&, const constant&);
  friend bool operator<(const constant&, const constant&);
};

inline std::ostream& operator<<(std::ostream& os, const constant& x) {
  x.write(os, write_default);  return os;
}

inline bool operator==(const constant& x, const constant& y)
{ return x.name == y.name; }


class sequence : public formula {
public:
  typedef std::list<ref<formula> > container_type;
  typedef container_type::size_type size_type;
  typedef container_type::iterator iterator;
  typedef container_type::const_iterator const_iterator;
  typedef container_type::reverse_iterator reverse_iterator;
  typedef container_type::const_reverse_iterator const_reverse_iterator;

  container_type formulas_;
  sequence_type type_;

  sequence() : type_(other_sequence_) {}

  clone_declare(sequence);
  copy_declare(sequence);

  sequence(sequence_type t)
   : type_(t) {}
  sequence(const ref<formula>& x, sequence_type t)
   : formulas_(1, x), type_(t) {}
  sequence(const ref<formula>& x, const ref<formula>& y, sequence_type t)
   : formulas_(1, x), type_(t) { formulas_.push_back(y); }
  sequence(const std::list<ref<formula> >& xs, sequence_type t)
   : formulas_(xs), type_(t) {}
  
  sequence(const sequence& x, const sequence& y)
   : formulas_(x.formulas_), type_(x.type_)
  { formulas_.insert(formulas_.end(), y.formulas_.begin(), y.formulas_.end()); }

  sequence(const sequence& x, const ref<formula>& y)
   : formulas_(x.formulas_), type_(x.type_) { formulas_.push_back(y); }
  sequence(const ref<formula>& x, const sequence& y)
   : formulas_(y.formulas_), type_(y.type_) { formulas_.push_front(x); }

  formula_type get_formula_type() const;

  void push_back(const ref<formula>& t) { formulas_.push_back(t); }
  void reverse() { formulas_.reverse(); }

  virtual ref<alternatives> unify(unify_environment, const ref<formula>&, unify_environment, database*, level, sublevel&, direction) const;
  virtual split_formula split(unify_environment, const ref<variable>&, const ref<formula>&, unify_environment, database*, level, sublevel&, direction) const;
  virtual ref<alternatives> unify_inference(const ref<formula>& head, unify_environment, const ref<formula>&, unify_environment, database*, level, sublevel&, direction) const;

  virtual kleenean has(const ref<variable>&, occurrence) const;
  virtual void contains(std::set<ref<variable> >&, std::set<ref<variable> >&, bool&, occurrence) const;

  virtual kleenean free_for(const ref<formula>& f, const ref<variable>& x, 
    std::set<ref<variable> >& s, std::list<ref<variable> >& bs) const;

  virtual void unspecialize(depth, bool);
  virtual ref<formula> rename(level, sublevel) const;
  virtual ref<formula> substitute(const ref<substitution>&, substitute_environment) const;

  virtual void set_bind(bind&, name_variable_table&);

  virtual kleenean succeed_or_fail() const;
  virtual bool metaempty() const;
  virtual size_type metasize() const;
  virtual ref<formula> metareverse() const;

  virtual relation compare(const formula&) const;
  virtual relation total(const formula&) const;

  virtual operator_precedence precedence() const;
  virtual void write(std::ostream&, write_style) const;

  friend bool operator==(const sequence&, const sequence&);
  // Check if x, y are of type t, and return accordingly a sequence of type t:
  friend ref<formula> concatenate(const ref<formula>&, const ref<formula>&, sequence_type);
};


ref<formula> concatenate(const ref<formula>&, const ref<formula>&, sequence_type);


inline bool operator==(const sequence& x, const sequence& y) {
  return x.compare(y) == mli::equal;
}

inline std::ostream& operator<<(std::ostream& os, const sequence& x) {
  x.write(os, write_default);  return os;
}


  // A structure is an object of the form f(x_1, ..., x_n), where
  // f is an identifier and (x_1, ..., x_n) the argument.
class structure : public formula {
  operator_precedence precedence_;
public:
  ref<formula> atom;     // Name or letter (identifier).
  ref<formula> argument; // Should be a sequence.
  enum type { metapredicate, metalogic, logic, predicate, function };
  type type_;
  enum style { postargument, prefix, postfix, infix };
  style style_;

  structure() : type_(predicate), style_(postargument) {}

  clone_declare(structure);
  copy_declare(structure);

  explicit structure(const ref<formula>& a)
   : atom(a), argument(new sequence(predicate_argument_)),
     type_(predicate), style_(postargument) {}

  structure(const std::string& s, type t)
   : atom(new constant(s,
       (t <= metalogic)? metaformula_type_ :
       (t <= predicate)? object_formula_type_ : term_type_)),
     argument(new sequence(
       (t <= metalogic)? metapredicate_argument_ :
       (t <= predicate)? predicate_argument_ :
         function_argument_)),
     type_(t), style_(postargument) {}

  structure(const ref<formula>& a, const ref<formula>& arg, type t, style s, operator_precedence p)
   : atom(a), argument(arg), type_(t), style_(s), precedence_(p) {}

  void push_back(const ref<formula>&);

  void set(type t) { type_ = t; }
  void set(style s) { style_ = s; }
  void set(operator_precedence p) { precedence_ = p; }

  virtual formula_type get_formula_type() const {
    return (type_ == function)? term_type_ : object_formula_type_; }

  virtual ref<alternatives> unify(unify_environment, const ref<formula>&, unify_environment, database*, level, sublevel&, direction) const;  
  virtual split_formula split(unify_environment, const ref<variable>&, const ref<formula>&, unify_environment, database*, level, sublevel&, direction) const;

  virtual kleenean has(const ref<variable>&, occurrence) const;
  virtual void contains(std::set<ref<variable> >&, std::set<ref<variable> >&, bool&, occurrence) const;

  virtual kleenean free_for(const ref<formula>& f, const ref<variable>& x, 
    std::set<ref<variable> >& s, std::list<ref<variable> >& bs) const;

  virtual void unspecialize(depth, bool);
  virtual ref<formula> rename(level, sublevel) const;
  virtual ref<formula> substitute(const ref<substitution>&, substitute_environment) const;

  virtual void set_bind(bind&, name_variable_table&);

  virtual relation compare(const formula&) const;
  virtual relation total(const formula&) const;

  int arity() const;

  virtual operator_precedence precedence() const { return precedence_; }
  virtual void write(std::ostream&, write_style) const;

  friend bool operator==(const structure&, const structure&);
};

inline bool operator==(const structure& x, const structure& y) {
  return x.atom == y.atom && x.argument == y.argument;
}


class bound_formula : public formula {
public:
  ref<variable> variable_; // Variable that is bound.
  ref<formula> formula_;   // The formula that is bound.
  bind bind_; // Identifies, within a formula, different binders. Also
              // Stamped onto variables. Used to enable local substitutions.
  enum type { none_,
    all_, exist_, is_set_, set_, implicit_set_, mapto_,
    other_
  } type_;

  bound_formula() : bind_(0), type_(none_) {}

  clone_declare(bound_formula);
  copy_declare(bound_formula);

  bound_formula(const ref<variable>& v, const bound_formula::type& bt)
   : bind_(0), variable_(v), type_(bt) {}
  bound_formula(const ref<variable>& v, const ref<formula>& f, const bound_formula::type& bt, bind b = 0)
   : bind_(b), variable_(v), formula_(f), type_(bt) {}
  bound_formula(const variable_list& vs, const ref<formula>& f);
  
  bound_formula* push_back(const ref<variable>&, const bound_formula::type&);
  void push_back(const variable_list&);

  void set(const ref<formula>&);
  void set(const bound_formula&); // Assumes same bind identifier.
  void set(bind b) { bind_ = b; }

  // Compares the binding type signatures of the form q_1, ..., q_n:
  // q is less than q' if there is a non-empty sequence s such that q s = q'.
  // q is greater than q' ⇔ q' less than q.
  // If q and q' are not equal, less or greater, they are unrelated.
  relation signature_compare(const bound_formula&) const;

  bool is_quantified() const { return (type_ == all_) || (type_ == exist_); }

  virtual formula_type get_formula_type() const { return object_formula_type_; }

  virtual ref<alternatives> unify(unify_environment, const ref<formula>&, unify_environment, database*, level, sublevel&, direction) const;  
  virtual split_formula split(unify_environment, const ref<variable>&, const ref<formula>&, unify_environment, database*, level, sublevel&, direction) const;

  virtual kleenean has(const ref<variable>&, occurrence) const;
  virtual void contains(std::set<ref<variable> >&, std::set<ref<variable> >&, bool&, occurrence) const;

  virtual kleenean free_for(const ref<formula>& f, const ref<variable>& x, 
    std::set<ref<variable> >& s, std::list<ref<variable> >& bs) const;

  virtual void unspecialize(depth, bool);
  virtual ref<formula> rename(level, sublevel) const;
  virtual ref<formula> substitute(const ref<substitution>&, substitute_environment) const;

  virtual void set_bind(bind&, name_variable_table&);

  virtual relation compare(const formula&) const;
  virtual relation total(const formula&) const;

  virtual operator_precedence precedence() const;
  virtual void write(std::ostream&, write_style) const;
  void write(std::ostream&, write_style, type) const;

  // Returns true b x A, when A is a variable, constant or predicate.
  bool body_simple() const;

  friend bool operator==(const bound_formula&, const bound_formula&);
};


// Only used to construct a variable list for use in other
// objects, such as bound_formula.
class variable_list : public object {
public:
  typedef std::pair<ref<variable>, bound_formula::type>  value_type;
  typedef std::list<value_type>          sequence_type;
  typedef sequence_type::iterator        iterator;
  typedef sequence_type::const_iterator  const_iterator;

  std::list<value_type> variables_;
  
  variable_list() {}

  clone_declare(variable_list);
  copy_declare(variable_list);

  variable_list(const ref<variable>& x, const bound_formula::type& bt)
   : variables_(1, value_type(x, bt)) {}

  void push_back(const ref<variable>& x, const bound_formula::type& bt)
  { variables_.push_back(value_type(x, bt)); }
  void push_back(const variable_list& x)
  { variables_.insert(variables_.end(), x.variables_.begin(), x.variables_.end()); }

  void splice_back(variable_list& x) { variables_.splice(variables_.end(), x.variables_); }
  void splice_front(variable_list& x) { variables_.splice(variables_.begin(), x.variables_); }

  void reverse() { variables_.reverse(); }

  virtual void write(std::ostream&, write_style) const;
};

inline std::ostream& operator<<(std::ostream& os, const variable_list& x) {
  x.write(os, write_default);  return os;
}


class inference : public formula {
public:
  ref<formula> head_;
  ref<formula> body_;

  enum type { infered_by_,
    infer_
  } type_;

  inference() {}

  clone_declare(inference);
  copy_declare(inference);
  
  explicit inference(const ref<formula>& h) : head_(h), type_(infer_) {}

  inference(const ref<formula>& h, const ref<formula>& b, type t)
   : head_(h), body_(b), type_(t) {}

  inference(const ref<formula>& h, const std::list<ref<formula> >& bfs, type t)
   : head_(h), body_(new sequence(bfs, metaand_)), type_(t) {}

  bool is_infer() const { return (type_ == infer_); }
  bool is_infered_by() const { return (type_ == infered_by_); }

  ref<formula> head() const { return head_; }
  ref<formula> body() const { return body_; }

  virtual formula_type get_formula_type() const { return metaformula_type_; }

  virtual kleenean succeed_or_fail() const { return head_->succeed_or_fail(); }
  virtual bool metaempty() const { return head_->metaempty(); }
  virtual size_type metasize() const { return head_->metasize(); }

  virtual ref<alternatives> unify(unify_environment, const ref<formula>&, unify_environment, database*, level, sublevel&, direction) const;
  virtual split_formula split(unify_environment, const ref<variable>&, const ref<formula>&, unify_environment, database*, level, sublevel&, direction) const;

  virtual kleenean has(const ref<variable>&, occurrence) const;
  virtual void contains(std::set<ref<variable> >&, std::set<ref<variable> >&, bool&, occurrence) const;

  virtual kleenean free_for(const ref<formula>& f, const ref<variable>& x, 
    std::set<ref<variable> >& s, std::list<ref<variable> >& bs) const;

  virtual void unspecialize(depth, bool);
  virtual ref<formula> rename(level, sublevel) const;
  virtual ref<formula> substitute(const ref<substitution>&, substitute_environment) const;

  virtual void set_bind(bind&, name_variable_table&);

  virtual relation total(const formula&) const;
  virtual relation compare(const formula&) const;

  virtual operator_precedence precedence() const;
  virtual void write(std::ostream&, write_style) const;
};

inline std::ostream& operator<<(std::ostream& os, const inference& x) {
  x.write(os, write_default);  return os;
}


class database : public formula {
public:
  typedef database null_type;

  clone_declare(database);
  copy_declare(database);

  virtual formula_type get_formula_type() const { return metaformula_type_; }

  virtual ref<alternatives> unify(unify_environment, const ref<formula>&, unify_environment, database*, level, sublevel&, direction) const;

  virtual kleenean has(const ref<variable>&, occurrence) const { return false; }
  virtual void contains(std::set<ref<variable> >&, std::set<ref<variable> >&, bool&, occurrence) const {}

  virtual kleenean free_for(const ref<formula>&, const ref<variable>&, 
    std::set<ref<variable> >&, std::list<ref<variable> >&) const { return true; }

  virtual void unspecialize(depth, bool) {}
  virtual ref<formula> rename(level, sublevel) const;
  virtual ref<formula> substitute(const ref<substitution>&, substitute_environment) const { return (formula*)0; }

  virtual void set_bind(bind&, name_variable_table&) {}

  virtual bool empty() const;
  virtual int get_level() const;
  virtual bool has_definition(level) const;

  virtual bool insert(const ref<labelstatement>&);

  virtual ref<alternatives> find(ref<formula> key, level, database* dbp, bool proved = true);
  virtual maybe<ref<labelstatement> > find(const std::string& name, level, bool proved = true);

  // Compute unify(x, y) only when definitions can be expanded:
  //   unify_x1() expands definitions for first formula x.
  //   unify_x2() expands definitions for second formula y.
  // The argument dbp is the (to this unification evaluation) global
  // database, forwarded to be used when unificying with the definers
  // of the expanded definition.
  virtual ref<alternatives> unify_x1(const ref<formula>& x, unify_environment tx, const ref<formula>& y, unify_environment ty, database* dbp, level, sublevel&);
  virtual ref<alternatives> unify_x2(const ref<formula>& x, unify_environment tx, const ref<formula>& y, unify_environment ty, database* dbp, level, sublevel&);

  // g is a goal, i.e., a formula to be proved; each solution will result in a proof,
  // added to the proof list ps. *this is the database to look for proved propositions.
  // tr is the inference tree, which saves solution alternatives branching data for
  // later investigation.
  // n = maximum number of solutions to be found; n = 0 ⇔ find all solutions
  virtual void solve(const ref<formula>& g, inference_tree& tr,
    std::list<ref<proof> >& ps, int n);

  virtual std::list<ref<proof> > prove(const ref<formula>& g, int n);

  virtual relation total(const formula&) const { return unrelated; }
  virtual relation compare(const formula&) const { return unrelated; }

  virtual void write(std::ostream&, write_style) const;
};


ref<database> operator+(const ref<database>&, const ref<database>&); // Union.
ref<database> operator*(const ref<database>&, const ref<database>&); // Level concatenation.

  // List proofs:
void show_solution(std::ostream& os, std::list<ref<proof> >& pfs);

  // Show one solution:
void show_solution(std::ostream& os, write_style ws, std::set<ref<variable> >& vs, ref<substitution> s);
  // List variables:
void show_solution(std::ostream& os, write_style ws, std::set<ref<variable> >& vs);
  // List substitutions:
void show_solution(std::ostream& os, std::list<ref<substitution> >& ss);
  // List variables that gets new values by the substitutions:
void show_solution(std::ostream& os, write_style ws,
  std::set<ref<variable> >& vs, std::list<ref<substitution> >& ss);

} // namespace mli


#endif // header_MLI_h

