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

#ifndef header_substitution_hh
#define header_substitution_hh

#include "MLI.hh"
#include "precedence.hh"


namespace mli {


class alternatives_null;


class substitute_error : public runtime_error {
public:
  explicit substitute_error(const char* what_arg) : runtime_error(what_arg) {}
  explicit substitute_error(const std::string& what_arg) : runtime_error(what_arg) {}
};


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
class substitution : public formula {
public:
  typedef substitution null_type;

	clone_declare(substitution);
  copy_declare(substitution);

  virtual bool is_identity() const { return true; }

	virtual ref<formula> substitute_variable(const ref<variable>& x, substitute_environment) const
  { return ref<formula>(x); }
  // Extends the substitution *this to a function, mapping formulas to formulas:
  virtual ref<formula> operator()(const ref<formula>& x) const;

  // If s := *this, and the substitution_formula pair (s, x) substitution
  // sx cannot be simplified (is undecidable), compute unify(sx, y):
	virtual ref<alternatives> unify_substitution2(const ref<formula>&, unify_environment, const ref<formula>&, unify_environment, database*, level, sublevel&, direction) const;
	virtual ref<alternatives> unify_substitution3(const ref<formula>&, unify_environment, const ref<formula>&, unify_environment, database*, level, sublevel&, direction) const;
	virtual ref<alternatives> unify_substitution4(const ref<formula>&, unify_environment, const ref<formula>&, unify_environment, database*, level, sublevel&, direction) const;

  virtual formula_type get_formula_type() const { return metaformula_type_; }

  virtual kleenean has(const ref<variable>&, occurrence) const { return false; }
  virtual void contains(std::set<ref<variable> >&, std::set<ref<variable> >&, bool&, occurrence) const {}

  virtual kleenean free_for(const ref<formula>&, const ref<variable>&, 
    std::set<ref<variable> >&, std::list<ref<variable> >&) const { return true; }

  virtual void unspecialize(depth, bool) {}
  virtual ref<formula> rename(level, sublevel) const { return *this; }
  virtual ref<formula> substitute(const ref<substitution>&, substitute_environment) const { return *this; }

  virtual void set_bind(bind&, name_variable_table&) {}

  virtual ref<alternatives> unify(unify_environment, const ref<formula>&, unify_environment, database*, level, sublevel&, direction) const;

#if 0  // Defined in class formula:
  virtual split_formula split(unify_environment, const ref<variable>&, const ref<formula>&, unify_environment, database*, level, sublevel&, direction) const;
#endif

  // One has *this = without() + innermost(), and innermost() of the form
  // [x.t] or equal to I:
  virtual ref<substitution> innermost() const { return *this; }
  virtual ref<substitution> without() const { return *this; }
  // One has *this = outermost() + within(), and outermost() of the form
  // [x.t] or equal to I:
  virtual ref<substitution> outermost() const { return *this; }
  virtual ref<substitution> within() const { return *this; }

  virtual relation compare(const formula&) const;
  virtual relation total(const formula&) const;

#if 0  // Defined in class formula:
  virtual operator_precedence precedence() const { return formula_->precedence(); }
#endif

	virtual void write(std::ostream& os, write_style) const { os << "I"; }
};


class variable_substitution : public substitution {
public:
  ref<variable> variable_;
  ref<formula> formula_;
  bool all_occurrences_;
  bind bind_;  // Identifying local substitution.
  bool is_explicit_;
  std::set<ref<variable> > not_free_in_; // Simplifying condition.
  std::set<ref<variable> > linkers_;     // Variables that may cause linkage to other binders.

public:
  variable_substitution() : all_occurrences_(false), bind_(0), is_explicit_(false) {}

  clone_declare(variable_substitution);
  copy_declare(variable_substitution);

  variable_substitution(const ref<variable>& i, const ref<formula>& t,
    bool all_ = false, bind b = 0, bool ex = false)
   : variable_(i), formula_(t), all_occurrences_(all_), bind_(b), is_explicit_(ex) {}

  variable_substitution(const ref<variable>& i, const ref<formula>& t,
    bool all_, bind b, bool ex, std::set<ref<variable> > nf)
   : variable_(i), formula_(t), all_occurrences_(all_), bind_(b), is_explicit_(ex),
     not_free_in_(nf) {}

  virtual bool is_identity() const { return false; }

  virtual ref<formula> substitute_variable(const ref<variable>& x, substitute_environment) const;
  // Extra copy, as the compiler otherwise fails to see it:
//  virtual ref<formula> operator()(const ref<formula>& x) const;

	virtual ref<alternatives> unify_substitution2(const ref<formula>&, unify_environment, const ref<formula>&, unify_environment, database*, level, sublevel&, direction) const;
	virtual ref<alternatives> unify_substitution3(const ref<formula>&, unify_environment, const ref<formula>&, unify_environment, database*, level, sublevel&, direction) const;
	virtual ref<alternatives> unify_substitution4(const ref<formula>&, unify_environment, const ref<formula>&, unify_environment, database*, level, sublevel&, direction) const;

  virtual formula_type get_formula_type() const { return metaformula_type_; }

  virtual void set_bind(bind&, name_variable_table&);
  virtual ref<formula> rename(level, sublevel) const;

  virtual kleenean has(const ref<variable>&, occurrence) const;
  virtual void contains(std::set<ref<variable> >&, std::set<ref<variable> >&, bool&, occurrence) const;

  virtual kleenean free_for(const ref<formula>& f, const ref<variable>& x, 
    std::set<ref<variable> >& s, std::list<ref<variable> >& bs) const;

  virtual void unspecialize(depth, bool);

  virtual ref<formula> substitute(const ref<substitution>&, substitute_environment) const;

  virtual ref<alternatives> unify(unify_environment, const ref<formula>&, unify_environment, database*, level, sublevel&, direction) const;

  virtual split_formula split(unify_environment, const ref<variable>&, const ref<formula>&, unify_environment, database*, level, sublevel&, direction) const;

  virtual ref<substitution> innermost() const;
  virtual ref<substitution> without() const;
  virtual ref<substitution> outermost() const;
  virtual ref<substitution> within() const;

  virtual relation compare(const formula&) const;
  virtual relation total(const formula&) const;

  virtual operator_precedence precedence() const { return formula_->precedence(); }

  virtual void write(std::ostream& os, write_style ws) const;
};


ref<substitution> explicit_free_occurrences_substitution(const ref<variable>&, const ref<formula>&);
ref<substitution> free_occurrences_substitution(const ref<variable>&, const ref<formula>&);
ref<substitution> all_occurrences_substitution(const ref<variable>&, const ref<variable>&);
ref<substitution> local_substitution(const ref<variable>&, const ref<variable>&, bind);


class composition : public substitution {
  ref<substitution> outer_, inner_;

public:
  composition() {}

  clone_declare(composition);
  copy_declare(composition);

  composition(const ref<substitution>& outer, const ref<substitution>& inner)
   : outer_(outer), inner_(inner) {}

  virtual bool is_identity() const { return false; }

  virtual ref<formula> substitute_variable(const ref<variable>& x, substitute_environment vt) const;

	virtual ref<alternatives> unify_substitution2(const ref<formula>&, unify_environment, const ref<formula>&, unify_environment, database*, level, sublevel&, direction) const;
	virtual ref<alternatives> unify_substitution3(const ref<formula>&, unify_environment, const ref<formula>&, unify_environment, database*, level, sublevel&, direction) const;
	virtual ref<alternatives> unify_substitution4(const ref<formula>&, unify_environment, const ref<formula>&, unify_environment, database*, level, sublevel&, direction) const;

  virtual formula_type get_formula_type() const { return metaformula_type_; }

  // Variable renumbering:
  virtual void set_bind(bind&, name_variable_table&);
  virtual ref<formula> rename(level, sublevel) const;

  // Free variables:
  virtual kleenean has(const ref<variable>&, occurrence) const;
  virtual void contains(std::set<ref<variable> >&, std::set<ref<variable> >&, bool&, occurrence) const;

  virtual kleenean free_for(const ref<formula>& f, const ref<variable>& x, 
    std::set<ref<variable> >& s, std::list<ref<variable> >& bs) const;

  // Fixed variables:
  virtual void unspecialize(depth, bool);

  // Substitution:
  virtual ref<formula> substitute(const ref<substitution>&, substitute_environment) const;

  // Unification:
  virtual ref<alternatives> unify(unify_environment, const ref<formula>&, unify_environment, database*, level, sublevel&, direction) const;
  
  virtual split_formula split(unify_environment, const ref<variable>&, const ref<formula>&, unify_environment, database*, level, sublevel&, direction) const;

  virtual ref<substitution> innermost() const;
  virtual ref<substitution> without() const;
  virtual ref<substitution> outermost() const;
  virtual ref<substitution> within() const;

  // Comparison, needed for unification and database lookup.
  virtual relation compare(const formula&) const;
  virtual relation total(const formula&) const;

  // Writing:
  virtual operator_precedence precedence() const { return operator_precedence(); }

  virtual void write(std::ostream& os, write_style ws) const;
};

// Composition objects (as described above):
ref<substitution> operator+(const ref<substitution>&, const ref<substitution>&);
ref<substitution> operator*(const ref<substitution>&, const ref<substitution>&);


class substitution_formula : public formula {
public:
  ref<substitution> substitution_;
  ref<formula> formula_;

  substitution_formula() {}

  substitution_formula(const ref<substitution>& s) : substitution_(s) {}
  substitution_formula(const ref<substitution>& s, const ref<formula>& x)
   : substitution_(s), formula_(x) {}
  
  clone_declare(substitution_formula);
  copy_declare(substitution_formula);

  void append(const ref<substitution>& s) { substitution_ = s + substitution_; } 

  virtual formula_type get_formula_type() const;

  // Variable renumbering:
  virtual void set_bind(bind&, name_variable_table&);
  virtual ref<formula> rename(level, sublevel) const;

  // Free variables:
  virtual kleenean has(const ref<variable>&, occurrence) const;
  virtual void contains(std::set<ref<variable> >&, std::set<ref<variable> >&, bool&, occurrence) const;

  virtual kleenean free_for(const ref<formula>& f, const ref<variable>& x, 
    std::set<ref<variable> >& s, std::list<ref<variable> >& bs) const;

  // Fixed variables:
  virtual void unspecialize(depth, bool);

  // Substitution:
  virtual ref<formula> substitute(const ref<substitution>&, substitute_environment) const;

  // Unification:
  virtual ref<alternatives> unify(unify_environment, const ref<formula>&, unify_environment, database*, level, sublevel&, direction) const;

  // Helper functions, for special types of unification:

  // u(A[x.t], B[y.u]) type 1 solution u(x, y) * u(t, u) * u(A, B):
  ref<alternatives> unify1(unify_environment, const substitution_formula&, unify_environment, database*, level, sublevel&, direction) const;
  // u(A[x.t], B) type 2 solutions u(t, V) * u(A, B_(V, x)) where V is a
  // disjoint set of subformulas of B:
  ref<alternatives> unify2(unify_environment, const ref<formula>&, unify_environment, database*, level, sublevel&, direction) const;
  // u(A[x.t], B) type 3 solutions u(x, A) * u(t, B):
  ref<alternatives> unify3(unify_environment, const ref<formula>&, unify_environment, database*, level, sublevel&, direction) const;
  // u(A[x.t], B) type 4 solutions u(A, B) * u(x, t):
  ref<alternatives> unify4(unify_environment, const ref<formula>&, unify_environment, database*, level, sublevel&, direction) const;

  virtual split_formula split(unify_environment, const ref<variable>&, const ref<formula>&, unify_environment, database*, level, sublevel&, direction) const;

  ref<formula> within() const;

  // Comparison, needed for unification and database lookup.
  virtual relation compare(const formula&) const;
  virtual relation total(const formula&) const;

  // Writing:
  virtual operator_precedence precedence() const;

  virtual void write(std::ostream& os, write_style) const;
};


class alternative : public object {
public:
  typedef alternative null_type;

  ref<substitution> substitution_;
  ref<formula> unifier_; // Used by multi-argument unify().
  ref<formula> goal_;
  std::list<ref<labelstatement> > labelstatements_; // For writing out the proof.
  std::set<ref<variable> > bound_in_proof_;
  
  alternative() {}
  
  clone_declare(alternative);
  copy_declare(alternative);

  explicit alternative(const ref<formula>& x) : unifier_(x) {}
  
  explicit alternative(const ref<substitution>& s) : substitution_(s) {}
  alternative(const ref<substitution>& s, const ref<formula>& g)
   : substitution_(s), goal_(g) {}

  virtual ref<alternative> label(const ref<labelstatement>& ls);

  virtual formula::size_type metasize() const { return goal_->metasize(); }

  ref<substitution> operator*() { return substitution_; }
  const ref<substitution> operator*() const { return substitution_; }

  ref<formula> substitute_variable(const ref<variable>& x, substitute_environment vt) const
  { return substitution_->substitute_variable(x, vt); }
  ref<formula> operator()(const ref<formula>& x) const { return (*substitution_)(x); }

  void write(std::ostream&, write_style) const;
  
  // Combine substitutions and condition (goals) as of y followed by x.
  friend ref<alternative> operator+(const ref<alternative>& x, const ref<alternative>& y);

  // Combine substitutions and condition (goals) as of x followed by y.
  friend ref<alternative> operator*(const ref<alternative>& x, const ref<alternative>& y);

  // Prepend y to goals of x:
  friend ref<alternative> operator+(const ref<alternative>& x, const ref<formula>& y);
};


inline std::ostream& operator<<(std::ostream& os, const alternative& x) {
  x.write(os, write_default);  return os;
}


class alternatives : public object {
public:
  typedef alternatives_null null_type;

  typedef std::list<ref<alternative> > container_type;
  typedef container_type::size_type size_type;
  typedef container_type::iterator iterator;
  typedef container_type::const_iterator const_iterator;
  typedef container_type::reverse_iterator reverse_iterator;
  typedef container_type::const_reverse_iterator const_reverse_iterator;

  container_type alternatives_;  

  alternatives() {}

  clone_declare(alternatives);
  copy_declare(alternatives);

  explicit alternatives(const ref<alternative>& x)
   : alternatives_(1, x) {}

  explicit alternatives(const ref<formula>& f)
   : alternatives_(1, new alternative(f)) {}

  explicit alternatives(const ref<substitution>& s)
   : alternatives_(1, new alternative(s)) {}
  
  alternatives(const ref<substitution>& s, const ref<formula>& g)
   : alternatives_(1, new alternative(s, g)) {}

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

  virtual ref<alternatives> label(const ref<labelstatement>&);

  virtual ref<alternatives> push_back(const ref<alternative>& a);
  virtual ref<alternatives> append(const ref<alternatives>& as);
  
  virtual const ref<alternative> front() const { return alternatives_.front(); }
  virtual ref<alternative> front() { return alternatives_.front(); }

  virtual ref<alternative> pop_front() {
    ref<alternative> a = alternatives_.front(); alternatives_.pop_front(); return a; }

  // Find one solution; bool value tells whether a solution was found.
  virtual std::pair<ref<alternative>, bool> solution() const;
  // Put, of pair, all solutions first, the rest in second:
  virtual ref<alternatives> solutions(std::list<ref<proof> >&, const ref<proof>&) const;
  virtual void metaand_sort();  // Sort alternatives according to ascending metaand size:

  // For use in recursive computations of unify:
  // Each *this list alternative substitution s will be applied to x and y,
  // computing unify(s(x), s(y)), and these returns will be combined into a
  // single alternatives return value.
  virtual ref<alternatives> unify(const ref<formula>& x, unify_environment tx, const ref<formula>& y, unify_environment ty, database*, level, sublevel&, direction) const;

  // For use in the unification of binder expressions. unify_binder() differs from the recursive
  // unify() in that the substitution of variables is not kept in the total substitution.
  virtual ref<alternatives> unify_binder(
    const ref<formula>& x, unify_environment tx,
    const ref<formula>& y, unify_environment ty,
    database*, level, sublevel&, direction) const;

#if 0
  // The unify() of the arguments is computed, and appended to *this:
  virtual ref<alternatives> metaor_unify(const ref<formula>& x, unify_environment tx, const ref<formula>& y, unify_environment ty, database*, level, sublevel&, direction) const;
#endif

  // Return is *this with unifier formulas inserted by applying substitutions to x:
  virtual ref<alternatives> unifier(const ref<formula>& x) const;
  
  // Compute unify(xs, x) assuming that *this = unify(xs) with unifier
  // formulas inserted:
  virtual ref<alternatives> unify(unify_environment, const ref<formula>& x, unify_environment tx, database*, level, sublevel&) const;

  virtual void write(std::ostream&, write_style) const;
};


class alternatives_null : public alternatives {
public:
  alternatives_null() {}

  clone_declare(alternatives_null);
  copy_declare(alternatives_null);

  bool empty() const { return true; }
  size_type size() const { return 0; }

  virtual ref<alternatives> label(const ref<labelstatement>&) { return (alternatives*)0; }

  virtual ref<alternatives> push_back(const ref<alternative>& a);
  virtual ref<alternatives> append(const ref<alternatives>& as);

#if 0  
  // The unify() of the arguments is computed, and appended to *this:
  virtual ref<alternatives> metaor_unify(const ref<formula>& x, unify_environment tx, const ref<formula>& y, unify_environment ty, database*, level, sublevel&, direction) const;
#endif
};


// Extract the sequence of y, and prepend it to the sequence of
// each alternative of x:
ref<alternatives> operator+(const ref<alternatives>& x, const ref<formula>& y);

ref<alternatives> operator+(const ref<alternatives>& x, const ref<alternative>& y);


extern const ref<alternatives> O;  // No substitutions.
extern const ref<alternatives> I;  // Identity the only substitution.

// Combine substitutions and condition (goals) as of y followed by x.
ref<alternatives> operator+(const ref<alternatives>& x, const ref<alternatives>& y); 

// Prepend y to each alternative of x:
ref<alternatives> operator+(const ref<alternatives>& x, const ref<formula>& y); 

// Combine substitutions and condition (goals) as of x followed by y.
ref<alternatives> operator*(const ref<alternatives>& x, const ref<alternatives>& y); 

// Add y as inference body to each alternative of x:
ref<alternatives> operator|=(const ref<alternatives>& x, const ref<formula>& y); 


class proof  : public object {
public:
  typedef proof null_type;

  typedef std::list<ref<alternative> > container_type;
  typedef container_type::size_type size_type;
  typedef container_type::iterator iterator;
  typedef container_type::const_iterator const_iterator;
  typedef container_type::reverse_iterator reverse_iterator;
  typedef container_type::const_reverse_iterator const_reverse_iterator;

  ref<formula> goal_;
  container_type proof_;  

  proof() {}

  clone_declare(proof);
  copy_declare(proof);

  proof(const ref<formula>& x) : goal_(x) {}

  void push_front(const ref<alternative>&);

  // Pure (non-mutative) push_back.
  ref<proof> push_back(const ref<alternative>&) const;

  virtual void write(std::ostream&, write_style) const;
};


class subformulas {
public:
  typedef ref<formula> value_type;
  typedef std::list<value_type> container_type;
  typedef container_type::iterator iterator;
  typedef container_type::const_iterator const_iterator;
  typedef container_type::reverse_iterator reverse_iterator;
  typedef container_type::const_reverse_iterator const_reverse_iterator;

  container_type formulas_;  

  subformulas() {}

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


// List of pairs (fs, f), where fs are subformulas and f a formula.
class split_formula {
public:
  typedef std::pair<subformulas, ref<formula> > value_type;
  typedef std::list<value_type> container_type;
  typedef container_type::iterator iterator;
  typedef container_type::const_iterator const_iterator;
  typedef container_type::reverse_iterator reverse_iterator;
  typedef container_type::const_reverse_iterator const_reverse_iterator;

  container_type sequence_;  

  split_formula() {}
  
  split_formula(const ref<formula>& f)
   : sequence_(1, value_type(subformulas(), f)) {}
  
  split_formula(const ref<formula>& fs, const ref<formula>& f)
   : sequence_(1, value_type(subformulas(fs), f)) {}
  
  split_formula(const subformulas& fs, const ref<formula>& f)
   : sequence_(1, value_type(fs, f)) {}

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
    sequence_.push_back(value_type(subformulas(), f));
  }
  void push_back(const ref<formula>& fs, const ref<formula>& f) {
    sequence_.push_back(value_type(subformulas(fs), f));
  }
  void push_back(const subformulas& fs, const ref<formula>& f) {
    sequence_.push_back(value_type(fs, f));
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
    const ref<variable>& x, const ref<formula>& t, unify_environment tt, database* dbp, level lv, sublevel& sl, direction dr) {
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
  split_formula::iterator i, i0 = sf1.begin(), i1 = sf1.end();
  for (i = i0; i != i1; ++i) {
    subformulas fs = i->first;
    ref<formula> f = c(i->second);
    if (trace_value & trace_split)
      std::clog
        << "\n  construct " << i->second << " :\n    "
        << f
        << "\n  " << fs
        << std::endl;
    if (!!fs) 
      sf.push_back(fs, f);
  }
  return sf;
}

template<class Construct>
split_formula split(
    const ref<formula>& a, const ref<formula>& b, unify_environment ta, const Construct& c,
    const ref<variable>& x, const ref<formula>& t, unify_environment tt, database* dbp, level lv, sublevel& sl, direction dr) {
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
  split_formula::iterator i, i0 = sf1.begin(), i1 = sf1.end();
  split_formula::iterator j, j0 = sf2.begin(), j1 = sf2.end();
  for (i = i0; i != i1; ++i) {
    for (j = j0; j != j1; ++j) {
      subformulas fs;
      fs.append(i->first);
      fs.append(j->first);
      ref<formula> f = c(i->second, j->second);
      if (trace_value & trace_split)
        std::clog
          << "  construct " << i->second << " : " << j->second << "\n    "
          << f
          << "\n  concatenate: " << i->first << " + " << j->first << ":"
          << fs
          << std::endl;
      if (!!fs) 
        sf.push_back(fs, f);
    }
  }
  return sf;
}


} // namespace mli

#endif // header_substitution_h
