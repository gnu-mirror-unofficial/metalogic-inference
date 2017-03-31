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

#ifndef header_metacondition_hh
#define header_metacondition_hh

#include "MLI.hh"


namespace mli {


class metanot : public formula {
public:
  ref<formula> formula_;

  metanot() {}

  clone_declare(metanot);
  copy_declare(metanot);

  metanot(const ref<formula>& x) : formula_(x) {}

  virtual formula_type get_formula_type() const { return metaformula_type_; }

  virtual ref<alternatives> unify(unify_environment, const ref<formula>&, unify_environment, database*, level, sublevel&, direction) const;

  virtual kleenean has(const ref<variable>&, occurrence) const;
  virtual void contains(std::set<ref<variable> >&, std::set<ref<variable> >&, bool&, occurrence) const;

  virtual kleenean free_for(const ref<formula>&, const ref<variable>&, 
    std::set<ref<variable> >&, std::list<ref<variable> >&) const;

  virtual void unspecialize(depth, bool);
  virtual ref<formula> rename(level, sublevel) const;
  virtual ref<formula> substitute(const ref<substitution>&, substitute_environment) const;

  virtual void set_bind(bind&, name_variable_table&);

  virtual relation compare(const formula&) const;
  virtual relation total(const formula&) const;

  virtual operator_precedence precedence() const;
  virtual void write(std::ostream&, write_style) const;
};


  // Unification succeeds/fails depending on boolean value true/false:
class succeed_fail : public formula {
public:
  bool succeed_;

  succeed_fail() {}

  clone_declare(succeed_fail);
  copy_declare(succeed_fail);

  succeed_fail(bool x) : succeed_(x) {}

  virtual kleenean succeed_or_fail() const { return succeed_; }
  virtual bool metaempty() const { return succeed_; }

  virtual formula_type get_formula_type() const { return metaformula_type_; }

  virtual ref<alternatives> unify(unify_environment, const ref<formula>&, unify_environment, database*, level, sublevel&, direction) const;

  virtual kleenean has(const ref<variable>&, occurrence) const { return false; }
  virtual void contains(std::set<ref<variable> >&, std::set<ref<variable> >&, bool&, occurrence) const {}

  virtual kleenean free_for(const ref<formula>&, const ref<variable>&, 
    std::set<ref<variable> >&, std::list<ref<variable> >&) const
  { return true; }

  virtual void unspecialize(depth, bool) {}
  virtual ref<formula> rename(level, sublevel) const;
  virtual ref<formula> substitute(const ref<substitution>&, substitute_environment) const;

  virtual void set_bind(bind&, name_variable_table&) {}

  virtual relation compare(const formula&) const;
  virtual relation total(const formula&) const;

  virtual operator_precedence precedence() const;
  virtual void write(std::ostream&, write_style) const;
};


class identical : public formula {
public:
  ref<formula> first_, second_;
  bool positive_;

  identical() {}

  clone_declare(identical);
  copy_declare(identical);

  identical(const ref<formula>& x, const ref<formula>& y, bool not_negated = true)
   : first_(x), second_(y), positive_(not_negated) {}

  virtual formula_type get_formula_type() const { return metaformula_type_; }

  virtual ref<alternatives> unify(unify_environment, const ref<formula>&, unify_environment, database*, level, sublevel&, direction) const;

  virtual kleenean has(const ref<variable>&, occurrence) const;
  virtual void contains(std::set<ref<variable> >&, std::set<ref<variable> >&, bool&, occurrence) const;

  virtual kleenean free_for(const ref<formula>&, const ref<variable>&, 
    std::set<ref<variable> >&, std::list<ref<variable> >&) const;

  virtual void unspecialize(depth, bool);
  virtual ref<formula> rename(level, sublevel) const;
  virtual ref<formula> substitute(const ref<substitution>&, substitute_environment) const;

  virtual void set_bind(bind&, name_variable_table&);

  virtual relation compare(const formula&) const;
  virtual relation total(const formula&) const;

  virtual operator_precedence precedence() const;
  virtual void write(std::ostream&, write_style) const;
};


// Class for comparing that object variables, as well when representaed by
// metaobjectvariables, are identical in the classical sense (object type
// and bind numbers disregarded.
class objectidentical : public formula {
public:
  ref<variable> first_, second_;
  bool positive_;

  objectidentical() {}

  clone_declare(objectidentical);
  copy_declare(objectidentical);

  objectidentical(const ref<variable>& x, const ref<variable>& y, bool not_negated = true)
   : first_(x), second_(y), positive_(not_negated) {}

  virtual formula_type get_formula_type() const { return metaformula_type_; }

  virtual ref<alternatives> unify(unify_environment, const ref<formula>&, unify_environment, database*, level, sublevel&, direction) const;

  virtual kleenean has(const ref<variable>&, occurrence) const;
  virtual void contains(std::set<ref<variable> >&, std::set<ref<variable> >&, bool&, occurrence) const;

  virtual kleenean free_for(const ref<formula>&, const ref<variable>&, 
    std::set<ref<variable> >&, std::list<ref<variable> >&) const;

  virtual void unspecialize(depth, bool);
  virtual ref<formula> rename(level, sublevel) const;
  virtual ref<formula> substitute(const ref<substitution>&, substitute_environment) const;

  virtual void set_bind(bind&, name_variable_table&);

  virtual relation compare(const formula&) const;
  virtual relation total(const formula&) const;

  virtual operator_precedence precedence() const;
  virtual void write(std::ostream&, write_style) const;
};


class free_in_object : public formula {
public:
  ref<variable> variable_;
  ref<formula> formula_;
  bool positive_;    // true iff x free in f
                     // false iff x not free in f

  free_in_object() {}

  clone_declare(free_in_object);
  copy_declare(free_in_object);

  free_in_object(const ref<variable>& x, const ref<formula>& f, bool not_negated)
   : variable_(x), formula_(f), positive_(not_negated) {}

  virtual formula_type get_formula_type() const { return metaformula_type_; }

  virtual ref<alternatives> unify(unify_environment, const ref<formula>&, unify_environment, database*, level, sublevel&, direction) const;

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
};


class free_for_object : public formula {
public:
  ref<formula> term_;
  ref<variable> variable_;
  ref<formula> formula_;
  bool positive_;  // true iff t free for x in f,
                   // false iff t not free for x in f

  free_for_object() {}

  clone_declare(free_for_object);
  copy_declare(free_for_object);

  free_for_object(const ref<formula>& t, const ref<variable>& x, const ref<formula>& f, bool not_negated)
   : term_(t), variable_(x), formula_(f), positive_(not_negated) {}

  virtual formula_type get_formula_type() const { return metaformula_type_; }

  virtual ref<alternatives> unify(unify_environment, const ref<formula>&, unify_environment, database*, level, sublevel&, direction) const;

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
};


} // namespace mli


#endif // header_metacondition_h

