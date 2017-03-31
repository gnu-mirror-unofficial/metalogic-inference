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

#ifndef header_definition_hh
#define header_definition_hh

#include "MLI.hh"

namespace mli {


class definition : public formula {
  operator_precedence precedence_;
public:
  ref<formula> defined_;  // defined_ := definer_
  ref<formula> definer_;
  ref<formula> condition_; // condition_ |- x := y.
  formula_type type_;

  definition() : type_(object_formula_type_) {}

  clone_declare(definition);
  copy_declare(definition);

  definition(const ref<formula>& x, const ref<formula>& y, const ref<formula>& c,
    formula_type t, const operator_precedence& p)
   : defined_(x), definer_(y), condition_(c), type_(t), precedence_(p) {}

  void set(formula_type t) { type_ = t; }
  void set(operator_precedence p) { precedence_ = p; }

  virtual formula_type get_formula_type() const { return type_; }

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

  virtual operator_precedence precedence() const { return precedence_; }
  virtual void write(std::ostream&, write_style) const;
};


class named_definition : public named_statement {
public:
  named_definition() {}

  clone_declare(named_definition);
  copy_declare(named_definition);

  named_definition(const std::string& name, const definition& d)
   : named_statement(name, d) {}

  virtual void declared(std::set<ref<variable> >&) const;

  virtual statement_type get_statement_type() const { return a_definition; }

  // Proving & solving.
  virtual bool prove() { return true; }
  virtual bool is_proved() const { return true; }

  virtual void write(std::ostream&, write_style) const;
};


} // namespace mli

#endif // header_definition_h

