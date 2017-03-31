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

#ifndef header_basictype_hh
#define header_basictype_hh

#include "MLI.hh"
#include "gmp.hh"


namespace mli {

#if 0
class integer : public virtual formula {
public:
  gmp::integer value_;

  integer() {}

  virtual object_root* clone() const { return new integer(*this); }

  integer(long n) : value_(n) {}

  virtual maybe<substitution> unify(const formula&) const;

  virtual bool has_free(const variable&) const;
  virtual void has_free(std::set<variable>&) const;
  virtual bool free_for(
    std::set<variable>& s, const variable& x, std::list<variable>& bs) const
  { return true; }

  virtual void set_depth(int) {}
  virtual proposition_root* rename(int) const;
  virtual proposition_root* apply(const substitution&) const;
  virtual void set_bind(bind&, table_stack<variable>&) {}

  virtual relate compare(const formula_root&) const;
  virtual relate total(const formula_root&) const;
  virtual bool equal(const formula_root&) const;

  virtual void write(std::ostream&, write_style) const;

  friend bool operator==(const integer&, const integer&);
};

inline bool operator==(const integer& x, const integer& y) {
  return x.value_ == y.value_;
}
#endif

class integer : public formula, public gmp::integer {
public:
  integer() {}

  clone_declare(integer);
  copy_declare(integer);

  integer(const char* str, int base = 0) : gmp::integer(str, base) {}

  virtual formula_type get_formula_type() const { return term_type_; }

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
};

inline std::ostream& operator<<(std::ostream& os, const integer& x) {
  x.write(os, write_default);  return os;
}


#if 0
class integer_addition : public virtual formula_root {
public:
  formula first, second;

  integer_addition() {}

  virtual object_root* clone() const { return new integer_addition(*this); }

  integer_addition(const formula& x, const formula& y) : first(x), second(y) {}

  virtual maybe<substitution> unify(const formula&) const;

  virtual bool has_free(const variable&) const;
  virtual void has_free(std::set<variable>&) const;
  virtual void set_depth(int);
  virtual proposition_root* rename(int) const;
  virtual proposition_root* apply(const substitution&) const;
  virtual void set_bind(bind&, table_stack<variable>&) {}

  virtual relate compare(const formula_root&) const;
  virtual relate total(const formula_root&) const;
  virtual bool equal(const formula_root&) const;

  virtual void write(std::ostream&, write_style) const;

  friend bool operator==(const integer_addition&, const integer_addition&);
};

inline bool operator==(const integer_addition& x, const integer_addition& y) {
  return x.first == y.first && x.second == y.second;
}


class integer_negative : public virtual formula_root {
public:
  formula value_;

  integer_negative() {}

  virtual object_root* clone() const { return new integer_negative(*this); }

  integer_negative(const formula& x) : value_(x) {}

  virtual maybe<substitution> unify(const formula&) const;

  virtual bool has_free(const variable&) const;
  virtual void has_free(std::set<variable>&) const;
  virtual void set_depth(int);
  virtual proposition_root* rename(int) const;
  virtual proposition_root* apply(const substitution&) const;
  virtual void set_bind(bind&, table_stack<variable>&) {}

  virtual relate compare(const formula_root&) const;
  virtual relate total(const formula_root&) const;
  virtual bool equal(const formula_root&) const;

  virtual void write(std::ostream&, write_style) const;

  friend bool operator==(const integer_negative&, const integer_negative&);
};

inline bool operator==(const integer_negative& x, const integer_negative& y) {
  return x.value_ == y.value_;
}
#endif

#if 0
class integer_less : public virtual formula_root {
public:
  formula first, second;

  integer_less() {}

  virtual object_root* clone() const { return new integer_less(*this); }

  integer_less(const formula& x, const formula& y) : first(x), second(y) {}

  virtual maybe<substitution> unify(const formula&) const;

  virtual bool has_free(const variable&) const;
  virtual void has_free(std::set<variable>&) const;
  virtual proposition_root* rename(int) const;
  virtual proposition_root* apply(const substitution&) const;

  virtual void write(std::ostream&, write_style) const;
  virtual bool equal(const formula_root&) const;

  friend bool operator==(const integer_less&, const integer_less&);
};

inline bool operator==(const integer_less& x, const integer_less& y) {
  return x.first == y.first && x.second == y.second;
}
#endif

} // namespace mli


#endif // header_basictype_h



