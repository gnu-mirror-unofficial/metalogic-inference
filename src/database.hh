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

#ifndef header_database_hh
#define header_database_hh

#include <vector>

#include "MLI.hh"


namespace mli {


  // Propositions recorded in the order entered into the database.
class sequential_database : public database {
public:
  typedef std::vector<ref<labelstatement> > sequential_table;
  typedef sequential_table::iterator sequential_iterator;
  typedef sequential_table::const_iterator const_sequential_iterator;

  typedef std::map<std::string, ref<labelstatement> > name_table;
  typedef name_table::iterator name_iterator;
  typedef name_table::const_iterator name_const_iterator;
  
  sequential_table sequential_table_;
  name_table name_table_;
  bool has_definition_;

  sequential_database() : has_definition_(false) {}

  clone_declare(sequential_database);
  copy_declare(sequential_database);

  sequential_database(const sequential_database&, const sequential_database&);

  virtual ref<alternatives> unify(unify_environment, const ref<formula>&, unify_environment, database*, level, sublevel&, direction) const;

  virtual ref<formula> rename(level, sublevel) const;
  virtual ref<formula> substitute(const ref<substitution>&, substitute_environment) const;

  virtual bool empty() const { return sequential_table_.empty(); }
  virtual int get_level() const { return 1; }
  virtual bool has_definition(level) const { return has_definition_; }

  virtual bool insert(const ref<labelstatement>&);

  virtual maybe<ref<labelstatement> > find(const std::string& name, level, bool proved);

  virtual ref<alternatives> unify_x1(const ref<formula>& x, unify_environment tx, const ref<formula>& y, unify_environment ty, database* dbp, level, sublevel&);
  virtual ref<alternatives> unify_x2(const ref<formula>& x, unify_environment tx, const ref<formula>& y, unify_environment ty, database* dbp, level, sublevel&);

  virtual void write(std::ostream&, write_style) const;
};


class leveled_database : public database {
public:
  ref<database> first, rest;
 
  leveled_database() {}
 
  clone_declare(leveled_database);
  copy_declare(leveled_database);

  leveled_database(const ref<labelstatement>& s) : first(new sequential_database()) { first->insert(s); }
  leveled_database(const ref<database>& d1, const ref<database>& d2)
   : first(d1), rest(d2) {}
  leveled_database(const ref<database>& d) : rest(d) {}
  leveled_database(const ref<labelstatement>& s, const ref<database>& d)
   : first(new sequential_database()), rest(d) { first->insert(s); }

  virtual ref<alternatives> unify(unify_environment, const ref<formula>&, unify_environment, database*, level, sublevel&, direction) const;

  virtual ref<formula> rename(level, sublevel) const;
  virtual ref<formula> substitute(const ref<substitution>&, substitute_environment) const;

  virtual bool empty() const { return first->empty() && rest->empty(); }
  virtual int get_level() const { return first->get_level() + rest->get_level(); }
  virtual bool has_definition(level) const;

  virtual bool insert(const ref<labelstatement>& s);

  virtual maybe<ref<labelstatement> > find(const std::string& name, level, bool proved);

  virtual ref<alternatives> unify_x1(const ref<formula>& x, unify_environment tx, const ref<formula>& y, unify_environment ty, database*, level, sublevel&);
  virtual ref<alternatives> unify_x2(const ref<formula>& x, unify_environment tx, const ref<formula>& y, unify_environment ty, database*, level, sublevel&);

  virtual void write(std::ostream&, write_style) const;
};


  // Propositions recorded in the order entered in the theory;
  // also name search keys.
class theory : public sequential_database {
public:
  typedef theory null_type;

  std::string name_; // Name of theory.
  
  std::list<ref<theory> >* includes_; // Other theories included.

  theory() : includes_(0) {}
  theory(const theory& th);

  clone_declare(theory);
  copy_declare(theory);

  theory(const std::string& name) : name_(name), includes_(0) {}

  virtual std::string name() const { return name_; }

  virtual bool insert(const ref<theory>&);
  virtual bool insert(const ref<labelstatement>& p) { return sequential_database::insert(p); }

  virtual maybe<ref<labelstatement> > find(const std::string& name, level, bool proved);

  virtual void write(std::ostream&, write_style) const;
};


class theory_database : public object {
public:
  typedef theory_database null_type;

  typedef std::vector<ref<theory> > sequential_table;
  typedef sequential_table::iterator sequential_iterator;
  typedef sequential_table::const_iterator const_sequential_iterator;

  typedef std::map<std::string, ref<theory> > name_table;
  typedef name_table::iterator name_iterator;
  typedef name_table::const_iterator name_const_iterator;

  std::string name_; // Name of theory database.
  
  // Set of theories recorded in two ways:
  sequential_table sequential_table_;
  name_table name_table_;

  theory_database() {}

  clone_declare(theory_database);
  copy_declare(theory_database);

  theory_database(const std::string& name) : name_(name) {}

  virtual std::string name() const { return name_; }

  virtual bool empty() const { return sequential_table_.empty(); }
  virtual int get_level() const { return 1; }

  virtual bool insert(const ref<theory>&);

  virtual maybe<ref<theory> > find(const std::string& name);

  virtual void read(std::istream&);
  virtual void write(std::ostream&, write_style) const;
};


inline std::istream& operator>>(std::istream& is, theory_database& a) {
  a.read(is);  return is;
}


} // namespace mli


#endif // header_database_h

