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

#include "database.hh"

#include "definition.hh"
#include "substitution.hh"


namespace mli {

size_type sublevel_max = 1000;

#define NO_DB_SUBST 1

clone_source(sequential_database)
copy_source(sequential_database)

sequential_database::sequential_database(const sequential_database& x, const sequential_database& y)
 : has_definition_(false) {
  const_sequential_iterator i = x.sequential_table_.begin(), i1 = x.sequential_table_.end();
  for (; i != i1; ++i)
    insert(*i);
  i = y.sequential_table_.begin(), i1 = y.sequential_table_.end();
  for (; i != i1; ++i)
    insert(*i);
}

ref<alternatives> sequential_database::unify(unify_environment tt, const ref<formula>& x, unify_environment tx, database* dbp, level lv, sublevel& sl, direction dr) const {
  if (trace_value & trace_unify)
    std::clog << "sequential_database::unify: " << x << std::endl;
  ref<alternatives> as; // Return value.
  const_sequential_iterator i, i0 = sequential_table_.begin(), i1 = sequential_table_.end();
  if (trace_value & trace_labelstatement) {
    std::clog << "Proposition alternatives:" << std::endl;
    for (i = i0; i != i1; ++i) {
      std::clog << "  ";
      (*i)->write(std::clog,
        write_style(write_name | write_type | write_statement));
      std::clog << "\n" << std::flush;
    }
  }
  for (i = i0; i != i1; ++i) {
    if (!(*i)->is_proved())
      continue; // Do not look at not proved statements.
    if ((*i)->get_statement_type() == a_definition)
      continue; // Do not look at definitions; these are expanded during unification.
    ref<labelstatement> ls = ref<labelstatement>((*i)->rename(lv, sl));
    ref<formula> f = ls->get_statement();
    if ((*i)->name() == "Gen")
      tt.is_generalization_ = true;
    ref<alternatives> s = mli::unify(f, tt, x, tx, dbp, lv, sl, dr);
    if (trace_value & trace_unify)
      std::clog << "unify(\n  " << x << ";\n  " << f << "):" << s << std::endl;
    if (s->empty()) {
      continue;
    }
    ++sl;
    s = s->label(ls);
    as = as->append(s);
  }
  return as;
}

ref<formula> sequential_database::rename(level lv, sublevel sl) const {
  sequential_database* dp = new sequential_database(*this);
  ref<formula> rt(dp);
  const_sequential_iterator i = sequential_table_.begin(), i1 = sequential_table_.end();
  sequential_iterator j = dp->sequential_table_.begin(), j1 = dp->sequential_table_.end();
  for (; i != i1; ++i, ++j)
    (*j) = ref<labelstatement>((*i)->rename(lv, sl));
  return rt;
}

#if NO_DB_SUBST
ref<formula> sequential_database::substitute(const ref<substitution>&, substitute_environment) const {
  return *this;
}
#else
ref<formula> sequential_database::substitute(const ref<substitution>& s, substitute_environment vt) const {
  sequential_database* dp = new sequential_database(*this);
  ref<formula> rt(dp);
  const_sequential_iterator i = sequential_table_.begin(), i1 = sequential_table_.end();
  sequential_iterator j = dp->sequential_table_.begin(), j1 = dp->sequential_table_.end();
  for (; i != i1; ++i, ++j)
    (*j) = ref<labelstatement>((*i)->substitute(s, vt));
  return rt;
}
#endif

bool sequential_database::insert(const ref<labelstatement>& x) {
  if (x->name().empty()) {
    std::cerr << "sequential_database::insert: no name of " << x << std::endl;
    return false;
  }
  if (name_table_.find(x->name()) != name_table_.end()) {
    std::cerr << "sequential_database::insert: duplicate labelstatement name " << x->name() << "." << std::endl;
    return false;
  }
  name_table_[x->name()] = x;
  sequential_table_.push_back(x);
  if (!has_definition_)
    has_definition_ = (cast_pointer<named_definition>(x) != 0);
  return true;
}

maybe<ref<labelstatement> > sequential_database::find(const std::string& name, level lv, bool proved) {
  if (trace_value & trace_labelstatement)
    std::clog << "sequential_database::find " << name << ", level " << lv << ": " << std::flush;
  name_iterator i = name_table_.find(name);
  if (i == name_table_.end()) {
    if (trace_value & trace_labelstatement)
      std::clog << " not found.\n" << std::flush;
    return false;
  }
  if (trace_value & trace_labelstatement)
    std::clog << i->second << ".\n" << std::flush;
  if (proved && !i->second->is_proved())  return false;
  return i->second;
}


ref<alternatives> sequential_database::unify_x1(const ref<formula>& x, unify_environment tx, const ref<formula>& y, unify_environment ty, database* dbp, level lv, sublevel& sl) {
  if (trace_value & trace_unify) {
    std::clog
     << "sequential_database::unify_x1(\n  " << x << ";\n  " << y << ") in ";
    write(std::clog, write_style(write_name));
    std::clog << std::endl;
  }
  // Only unify when there is a definition to expand:
  ref<alternatives> as;
  sequential_iterator i, i0 = sequential_table_.begin(), i1 = sequential_table_.end();
  for (i = i0; i != i1; ++i) {
    if ((*i)->get_statement_type() != a_definition)
      continue;  // Only expand definitions during unification.
    ref<labelstatement> nd = ref<labelstatement>((*i)->rename(lv, sl));
    ref<formula> f = nd->get_statement();
    definition& di = cast_reference<definition>(f);
    if (sublevel_max != 0 && sl > sublevel_max)
      throw std::runtime_error("Too high sublevel in sequential_database::unify_x1");
    ref<formula> d0 = di.defined_;
    ref<formula> d1 = di.definer_;
    ref<alternatives> bs;
    bs = pre_unify(x, tx, d0, ty, 0, lv, sl, forward)->label(nd)->unify(d1, tx, y, ty, dbp, lv, sl, forward);
    if (bs->empty())  continue;
    ++sl;
    as = as->append(bs + di.condition_);
  }
  return as;
}

ref<alternatives> sequential_database::unify_x2(const ref<formula>& x, unify_environment tx, const ref<formula>& y, unify_environment ty, database* dbp, level lv, sublevel& sl) {
  if (trace_value & trace_unify) {
    std::clog
     << "sequential_database::unify_x2(\n  " << x << ";\n  " << y << ") in ";
    write(std::clog, write_style(write_name));
    std::clog << std::endl;
  }
  // Only unify when there is a definition to expand:
  ref<alternatives> as;
  sequential_iterator i, i0 = sequential_table_.begin(), i1 = sequential_table_.end();
  for (i = i0; i != i1; ++i) {
    if ((*i)->get_statement_type() != a_definition)
      continue;  // Only expand definitions during unification.
    ref<labelstatement> nd = ref<labelstatement>((*i)->rename(lv, sl));
    ref<formula> f = nd->get_statement();
    definition& di = cast_reference<definition>(f);
    if (sublevel_max != 0 && sl > sublevel_max)
      throw std::runtime_error("Too high sublevel in sequential_database::unify_x2");
    ref<formula> d0 = di.defined_;
    ref<formula> d1 = di.definer_;
    ref<alternatives> bs;
    bs = pre_unify(d0, tx, y, ty, 0, lv, sl, forward)->label(nd)->unify(x, tx, d1, ty, dbp, lv, sl, forward);
    if (bs->empty())  continue;
    ++sl;
    as = as->append(bs + di.condition_);
  }
  return as;
}

void sequential_database::write(std::ostream& os, write_style ws) const {
  bool show_type = ws & write_type;
  bool show_name = ws & write_name;
  bool show_statement = ws & write_statement;
  bool show_proof = ws & write_proof;
  if ((show_proof || show_statement) && sequential_table_.empty()) {
    os << "-- Empty database --" << std::endl;
    return;
  }
  const_sequential_iterator i, i0 = sequential_table_.begin(), i1 = sequential_table_.end();
  for (i = i0; i != i1; ++i) {
    if (i != i0) {
      if (show_proof || show_statement)  os << "\n";
      else  os << ", ";
    }
    (*i)->write(os, ws);
    if (show_proof || show_statement)  os << "\n";
  }
}


class database_union : public database {
  ref<database> a, b;
public:
  database_union() {}

  virtual database_union* clone() const { return new database_union(*this); }
  virtual database_union* copy() const { increment_count(); return const_cast<database_union*>(this); }

  database_union(const ref<database>& x, const ref<database>& y) : a(x), b(y) {}

  virtual ref<alternatives> unify(unify_environment tt, const ref<formula>& x, unify_environment tx, database* dbp, level lv, sublevel& sl, direction dr) const {
    ref<alternatives> as = a->unify(tt, x, tx, dbp, lv, sl, dr);
    as = as->append(b->unify(tt, x, tx, dbp, lv, sl, dr));
    return as;
  }

  virtual ref<formula> rename(level lv, sublevel sl) const {
    database_union* dp = new database_union(*this);
    ref<formula> r(dp);
    dp->a = ref<database>(a->rename(lv, sl));
    dp->b = ref<database>(b->rename(lv, sl));
    return r;
  }

#if NO_DB_SUBST
  virtual ref<formula> substitute(const ref<substitution>&, substitute_environment) const {
    return *this;
  }
#else
  virtual ref<formula> substitute(const ref<substitution>& s, substitute_environment vt) const {
    database_union* dp = new database_union(*this);
    ref<formula> r(dp);
    dp->a = ref<database>(a->substitute(s, vt));
    dp->b = ref<database>(b->substitute(s, vt));
    return r;
  }
#endif

  virtual bool empty() const { return a->empty() && b->empty(); }
  virtual int get_level() const { return std::max(a->get_level(), b->get_level()); }
  virtual bool has_definition(level lv) const
  { return a->has_definition(lv) || b->has_definition(lv); }

  virtual bool insert(const ref<labelstatement>& s) { return b->insert(s); }

  virtual maybe<ref<labelstatement> > find(const std::string& name, level lv, bool proved) {
    maybe<ref<labelstatement> > s = a->find(name, lv, proved);
    if (!s)  return b->find(name, lv, proved);
    return s;
  }

  virtual ref<alternatives> unify_x1(const ref<formula>& x, unify_environment tx, const ref<formula>& y, unify_environment ty, database* dbp, level lv, sublevel& sl) {
    ref<alternatives> as;
    as = as->append(a->unify_x1(x, tx, y, ty, dbp, lv, sl));
    as = as->append(b->unify_x1(x, tx, y, ty, dbp, lv, sl));
    return as;
  }

  virtual ref<alternatives> unify_x2(const ref<formula>& x, unify_environment tx, const ref<formula>& y, unify_environment ty, database* dbp, level lv, sublevel& sl) {
    ref<alternatives> as = a->unify_x2(x, tx, y, ty, dbp, lv, sl);
    as = as->append(b->unify_x2(x, tx, y, ty, dbp, lv, sl));
    return as;
  }

  virtual void write(std::ostream& os, write_style ws) const {
    bool show_statement = ws & write_statement;
    bool show_proof = ws & write_proof;
    a->write(os, ws);
    os << ",";
    if (show_statement || show_proof)  os << "\n";
    else  os << " ";
    b->write(os, ws);
  }
};


ref<database> operator+(const ref<database>& x, const ref<database>& y) {
#if 1
   const sequential_database* xp = cast_pointer<sequential_database>(x);
   const sequential_database* yp = cast_pointer<sequential_database>(y);
   if (xp == 0 || yp == 0)
     return new database_union(x, y);
   return new sequential_database(*xp, *yp);
#else
  return new database_union(x, y);
#endif
}


class database_concatenation : public database {
  ref<database> a, b;
public:
  database_concatenation() {}

  virtual database_concatenation* clone() const { return new database_concatenation(*this); }
  virtual database_concatenation* copy() const { increment_count(); return const_cast<database_concatenation*>(this); }

  database_concatenation(const ref<database>& x, const ref<database>& y) : a(x), b(y) {}

  virtual ref<alternatives> unify(unify_environment tt, const ref<formula>& x, unify_environment tx, database* dbp, level lv, sublevel& sl, direction dr) const {
    ref<alternatives> as = a->unify(tt, x, tx, dbp, lv, sl, dr);
    as = as->append(b->unify(tt, x, tx, dbp, lv, sl, dr));
    return as;
  }

  virtual ref<formula> rename(level lv, sublevel sl) const {
    database_concatenation* dp = new database_concatenation(*this);
    ref<formula> rt(dp);
    dp->a = ref<database>(a->rename(lv, sl));
    dp->b = ref<database>(b->rename(lv, sl));
    return rt;
  }

#if NO_DB_SUBST
  virtual ref<formula> substitute(const ref<substitution>&, substitute_environment) const {
    return *this;
  }
#else
  virtual ref<formula> substitute(const ref<substitution>& s, substitute_environment) const {
    database_concatenation* dp = new database_concatenation(*this);
    ref<formula> rt(dp);
    dp->a = ref<database>((*s)(ref<formula>(a)));
    dp->b = ref<database>((*s)(ref<formula>(b)));
    return rt;
  }
#endif

  virtual bool empty() const { return a->empty() && b->empty(); }
  virtual int get_level() const { return a->get_level() + b->get_level(); }
  virtual bool has_definition(level lv) const
  { return a->has_definition(lv) || b->has_definition(lv); }

  virtual bool insert(const ref<labelstatement>& s) { return b->insert(s); }
  
  virtual maybe<ref<labelstatement> > find(const std::string& name, level lv, bool proved) {
    if (lv <= a->get_level())  return a->find(name, lv, proved);
    return b->find(name, lv, proved);
  }

  virtual ref<alternatives> unify_x1(const ref<formula>& x, unify_environment tx, const ref<formula>& y, unify_environment ty, database* dbp, level lv, sublevel& sl) {
    ref<alternatives> as;
    as = as->append(a->unify_x1(x, tx, y, ty, dbp, lv, sl));
    as = as->append(b->unify_x1(x, tx, y, ty, dbp, lv, sl));
    return as;
  }

  virtual ref<alternatives> unify_x2(const ref<formula>& x, unify_environment tx, const ref<formula>& y, unify_environment ty, database* dbp, level lv, sublevel& sl) {
    ref<alternatives> as = a->unify_x2(x, tx, y, ty, dbp, lv, sl);
    as = as->append(b->unify_x2(x, tx, y, ty, dbp, lv, sl));
    return as;
  }


  virtual void write(std::ostream& os, write_style ws) const {
    bool show_statement = ws & write_statement;
    bool show_proof = ws & write_proof;
    a->write(os, ws);
    if (!b->empty()) {
      os << " with";
      if (show_statement || show_proof)  os << "\n";
      else  os << " ";
      b->write(os, ws);
    }
  }
};

ref<database> operator*(const ref<database>& x, const ref<database>& y) {
  return new database_concatenation(x, y);
}


clone_source(leveled_database)
copy_source(leveled_database)

bool leveled_database::has_definition(level lv) const {
  // Only works if nested leveled_database are done so to the left (first):
  if (lv <= first->get_level())
    return first->has_definition(lv);
  return rest->has_definition(lv);
}

ref<alternatives> leveled_database::unify(unify_environment tt, const ref<formula>& x, unify_environment tx, database* dbp, level lv, sublevel& sl, direction dr) const {
  // Only works if nested leveled_database are done so to the left (first):
  if (lv <= first->get_level())
    return first->unify(tt, x, tx, dbp, lv, sl, dr);
  return rest->unify(tt, x, tx, dbp, lv, sl, dr);
}

ref<formula> leveled_database::rename(level lv, sublevel sl) const {
  leveled_database* dp = new leveled_database(*this);
  ref<formula> r(dp);
  dp->first = ref<database>(first->rename(lv, sl));
  dp->rest = ref<database>(rest->rename(lv, sl));
  return r;
}

#if NO_DB_SUBST
ref<formula> leveled_database::substitute(const ref<substitution>&, substitute_environment) const {
  return *this;
}
#else
ref<formula> leveled_database::substitute(const ref<substitution>& s, substitute_environment vt) const {
  leveled_database* dp = new leveled_database(*this);
  ref<formula> r(dp);
  dp->first = ref<database>(first->substitute(s, vt));
  dp->rest = ref<database>(rest->substitute(s, vt));
  return r;
}
#endif

bool leveled_database::insert(const ref<labelstatement>& s) {
  if (rest->empty()) return false;
  return rest->insert(s);
}

maybe<ref<labelstatement> > leveled_database::find(const std::string& name, level lv, bool proved) {
  if (lv <= first->get_level())
    return first->find(name, lv, proved);
  return rest->find(name, lv, proved);
}

ref<alternatives> leveled_database::unify_x1(const ref<formula>& x, unify_environment tx, const ref<formula>& y, unify_environment ty, database* dbp, level lv, sublevel& sl) {
  ref<alternatives> as;
  as = as->append(first->unify_x1(x, tx, y, ty, dbp, lv, sl));
  as = as->append(rest->unify_x1(x, tx, y, ty, dbp, lv, sl));
  return as;
}

ref<alternatives> leveled_database::unify_x2(const ref<formula>& x, unify_environment tx, const ref<formula>& y, unify_environment ty, database* dbp, level lv, sublevel& sl) {
  ref<alternatives> as = first->unify_x2(x, tx, y, ty, dbp, lv, sl);
  as = as->append(rest->unify_x2(x, tx, y, ty, dbp, lv, sl));
  return as;
}

void leveled_database::write(std::ostream& os, write_style ws) const {
  bool show_statement = ws & write_statement;
  bool show_proof = ws & write_proof;
  if (!first->empty())
    first->write(os, ws);
  if (!first->empty() && !rest->empty()) {
    if (show_statement || show_proof)  os << "\n";
  }
  if (!rest->empty()) {
    os << ";";
    if (show_statement || show_proof)  os << "\n";
    else  os << " ";
    rest->write(os, ws);
  }
}


// template <> theory::null_type ref<theory>::null_ = theory::null_type();
ref_null(theory);

clone_source(theory)
copy_source(theory)

theory::theory(const theory& th)
 : name_(th.name_),
   includes_(th.includes_? new std::list<ref<theory> >(*th.includes_) : 0)
{}

bool theory::insert(const ref<theory>& x) {
  if (includes_ == 0) {
    includes_ = new std::list<ref<theory> >(1, x);
    return true;
  }
  includes_->push_back(x);
  return true;
}

maybe<ref<labelstatement> > theory::find(const std::string& name, level lv, bool proved) {
  maybe<ref<labelstatement> > p = sequential_database::find(name, lv, proved);
  if (!p) {
    if (includes_ != 0) {
      std::list<ref<theory> >::reverse_iterator i,
        i0 = includes_->rbegin(), i1 = includes_->rend();
      for (i = i0; i != i1; ++i) {
        p = (*i)->find(name, lv, proved);
        if (!p)  continue;
        if (trace_value & trace_labelstatement)
          std::clog << (*i)->name() << "." << *p << ".\n" << std::flush;
        return p;
      }
    }
  }
  return p;
}

void theory::write(std::ostream& os, write_style ws) const {
  bool show_type = ws & write_type;
  bool show_name = ws & write_name;
  bool show_statement = ws & write_statement;
  bool show_proof = ws & write_proof;
  os << "theory " << name_ << ".\n";
  if ((show_proof || show_statement) && sequential_table_.empty() && includes_ == 0) {
    os << "-- Empty theory --\n";
    os << "end theory " << name_ << ".\n";
    return;
  }
  if (includes_ != 0) {
    os << "  include theory";
    std::list<ref<theory> >::iterator i,
      i0 = includes_->begin(), i1 = includes_->end();
    for (i = i0; i != i1; ++i)
      os << " " << (*i)->name();
    os << ".\n";
  }
  os << "\n";
  theory::const_sequential_iterator i, i0 = sequential_table_.begin(), i1 = sequential_table_.end();
  for (i = i0; i != i1; ++i) {
    if (i != i0) {
      if (show_proof || show_statement)  os << "\n";
      else  os << ", ";
    }
    (*i)->write(os, ws);
    if (show_proof || show_statement)  os << "\n";
  }
  os << "\nend theory " << name_ << ".\n";
}


ref_null(theory_database);

clone_source(theory_database)
copy_source(theory_database)

bool theory_database::insert(const ref<theory>& t) {
  if (t->name().empty()) {
    std::cerr << "theory_database::insert: no name of " << t << std::endl;
    return false;
  }
  if (name_table_.find(t->name()) != name_table_.end()) {
    std::cerr << "theory_database::insert: duplicate labelstatement name " << t->name() << "." << std::endl;
    return false;
  }
  name_table_[t->name()] = t;
  sequential_table_.push_back(t);
  return true;
}

maybe<ref<theory> > theory_database::find(const std::string& name) {
  if (trace_value & trace_labelstatement)
    std::clog << "theory_database::find " << name << ": " << std::flush;
  name_iterator i = name_table_.find(name);
  if (i == name_table_.end()) {
    if (trace_value & trace_labelstatement)  std::clog << " not found.\n" << std::flush;
    return false;
  }
  if (trace_value & trace_labelstatement)  std::clog << i->second << ".\n" << std::flush;
  return i->second;
}

void theory_database::write(std::ostream& os, write_style ws) const {
  bool show_type = ws & write_type;
  bool show_name = ws & write_name;
  bool show_statement = ws & write_statement;
  bool show_proof = ws & write_proof;
  os << "theories " << name_ << ".\n\n";
  if (sequential_table_.empty()) {
    os << "-- No theories --\n";
    return;
  }
  theory_database::const_sequential_iterator i, i0 = sequential_table_.begin(), i1 = sequential_table_.end();
  for (i = i0; i != i1; ++i) {
    if (i != i0)  os << "\n\n";
    (*i)->write(os, ws);
  }
  os << "\n-- End: theories " << name_ << ".\n";
}


} // namespace mli
