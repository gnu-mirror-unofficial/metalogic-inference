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

#include "metacondition.hh"

#include "substitution.hh"
#include "precedence.hh"


namespace mli {


clone_source(metanot)
copy_source(metanot)

ref<alternatives> metanot::unify(unify_environment tt, const ref<formula>& x, unify_environment tx, database* dbp, level lv, sublevel& sl, direction dr) const {
  if (trace_value & trace_unify)
    std::clog << "metanot::unify(\n  " << *this << ";\n  " << x << ")\n" << std::flush;
  const metanot* xp = cast_pointer<metanot>(x);
  if (xp != 0)
    // Both *this and x are metanot. So simply discard the metanot in unification:
    return mli::unify(formula_, tt, xp->formula_, tx, dbp, lv, sl, dr);
  // Now, x is a not a metanot object.
  const database* dp = cast_pointer<database>(x);
  if (dp != 0)  // Don't try to unify with a database, as it will do it.
    return O;
  ref<alternatives> as = mli::unify(formula_, tt, x, tx, dbp, lv, sl, dr);
  return (as->empty())? I : O;
}

kleenean metanot::has(const ref<variable>& v, occurrence oc) const {
  return formula_->has(v, oc);
}

void metanot::contains(std::set<ref<variable> >& s, std::set<ref<variable> >& bs, bool& more, occurrence oc) const {
  formula_->contains(s, bs, more, oc);
}

kleenean metanot::free_for(const ref<formula>& f, const ref<variable>& x,
  std::set<ref<variable> >& s, std::list<ref<variable> >& bs) const {
  return formula_->free_for(f, x, s, bs);
}

void metanot::unspecialize(depth x, bool y) {
  formula_->unspecialize(x, y);
}

ref<formula> metanot::rename(level lv, sublevel sl) const {
  metanot* mp = new metanot(*this);
  ref<formula> r(mp);
  mp->formula_ = formula_->rename(lv, sl);
  return r;
}

ref<formula> metanot::substitute(const ref<substitution>& s, substitute_environment vt) const {
  ref<formula> sf = formula_->substitute(s, vt);
  const succeed_fail* sfp = cast_pointer<succeed_fail>(sf);
  if (sfp != 0)
    return new succeed_fail(!sfp->succeed_);
  return new metanot(sf);
}

void metanot::set_bind(bind& b, name_variable_table& vt) {
  formula_->set_bind(b, vt);
}

relation metanot::compare(const formula& x) const {
  const metanot* xp = dynamic_cast<const metanot*>(&x);
  if (xp == 0)  return unrelated;
  return formula_->compare(*xp->formula_);
}

relation metanot::total(const formula& x) const {
  const metanot* xp = dynamic_cast<const metanot*>(&x);
  if (xp == 0)  throw runtime_error("In \"metanot\", total order error.");
  return formula_->total(*xp->formula_);
}

operator_precedence metanot::precedence() const {
  return metanot_oprec;
}

void metanot::write(std::ostream& os, write_style ws) const {
  os << "~";
  bool do_bracket = formula_->precedence() < precedence().last_argument();
	if (do_bracket)  os << "(";
  formula_->write(os, ws);
  if (do_bracket)  os << ")";
}


clone_source(succeed_fail)
copy_source(succeed_fail)

ref<alternatives> succeed_fail::unify(unify_environment, const ref<formula>& x, unify_environment, database*, level, sublevel&, direction) const {
  if (trace_value & trace_unify)
    std::clog << "succeed_fail::unify(\n  " << *this << ";\n  " << x << ")\n" << std::flush;
  const succeed_fail* xp = cast_pointer<succeed_fail>(x);
  return succeed_ == xp->succeed_? I : O;
}

ref<formula> succeed_fail::rename(level, sublevel) const {
  return *this;
}

ref<formula> succeed_fail::substitute(const ref<substitution>&, substitute_environment) const {
  return *this;
}

relation succeed_fail::compare(const formula& x) const {
  const succeed_fail* xp = dynamic_cast<const succeed_fail*>(&x);
  if (xp == 0)  return unrelated;
  return inequality_compare(succeed_, xp->succeed_);
}

relation succeed_fail::total(const formula& x) const {
  const succeed_fail* xp = dynamic_cast<const succeed_fail*>(&x);
  if (xp == 0)  throw runtime_error("In \"succeed_fail\", total order error.");
  return inequality_compare(succeed_, xp->succeed_);
}

operator_precedence succeed_fail::precedence() const {
  return operator_precedence();
}

void succeed_fail::write(std::ostream& os, write_style) const {
  if (succeed_)  os << "succeed";
  else  os << "fail";
}


clone_source(identical)
copy_source(identical)

ref<alternatives> identical::unify(unify_environment, const ref<formula>& x, unify_environment, database*, level, sublevel&, direction) const {
  if (trace_value & trace_unify)
    std::clog << "identical::unify(\n  " << *this << ";\n  " << x << ")\n" << std::flush;
  const identical* xp = cast_pointer<identical>(x);
  if (xp == 0)  return O;
  if (positive_ != xp->positive_)  return O;
  if (positive_)
    return first_ == second_? I : O;
  return first_ != second_? I : O;
}

kleenean identical::has(const ref<variable>& v, occurrence oc) const {
#if 1
  kleenean k1 = first_->has(v, oc);
  if (k1 == succeed)  return true;
  kleenean k2 = second_->has(v, oc);
  return k1 || k2;
#else
  kleenean mb;
  bool is_undecidable = false;
  mb = first_->has(v, oc);
  if (mb == true)  return true;
  if (mb == undecidable)  is_undecidable = true;
  mb = second_->has(v, oc);
  if (mb == true)  return true;
  if (mb == undecidable)  is_undecidable = true;
  if (is_undecidable)  return undecidable;
  return false;
#endif
}

void identical::contains(std::set<ref<variable> >& s, std::set<ref<variable> >& bs, bool& more, occurrence oc) const {
  first_->contains(s, bs, more, oc);
  second_->contains(s, bs, more, oc);
}

kleenean identical::free_for(const ref<formula>& f, const ref<variable>& x,
  std::set<ref<variable> >& s, std::list<ref<variable> >& bs) const {
  kleenean k1 = first_->free_for(f, x, s, bs);
  if (k1 == fail)  return false;
  kleenean k2 = second_->free_for(f, x, s, bs);
  return k1 && k2;
}

void identical::unspecialize(depth x, bool y) {
  first_->unspecialize(x, y);
  second_->unspecialize(x, y);
}

ref<formula> identical::rename(level lv, sublevel sl) const {
  identical* ir = new identical(*this);
  ir->first_ = first_->rename(lv, sl);
  ir->second_ = second_->rename(lv, sl);
  return ir;
}

ref<formula> identical::substitute(const ref<substitution>& s, substitute_environment vt) const {
  ref<formula> x1 = first_->substitute(s, vt);
  ref<formula> x2 = second_->substitute(s, vt);
  bool is_identical = (ref<formula>(x1) == ref<formula>(x2));
  return new succeed_fail(positive_? is_identical : !is_identical);
}

void identical::set_bind(bind& b, name_variable_table& vt) {
  first_->set_bind(b, vt);  second_->set_bind(b, vt);
}

relation identical::compare(const formula& x) const {
  const identical* xp = dynamic_cast<const identical*>(&x);
  if (xp == 0)  return unrelated;
  int a = inequality_compare(positive_, xp->positive_);
  if (a != 0)  return a;
  int c = first_->compare(*xp->first_);
  if (c != 0)  return c;
  return second_->compare(*xp->second_);
}

relation identical::total(const formula& x) const {
  const identical* xp = dynamic_cast<const identical*>(&x);
  if (xp == 0)  throw runtime_error("In \"identical\", total order error.");
  int a = inequality_compare(positive_, xp->positive_);
  if (a != 0)  return a;
  int c = first_->total(*xp->first_);
  if (c != 0)  return c;
  return second_->total(*xp->second_);
}

operator_precedence identical::precedence() const {
  return identical_oprec;
}

void identical::write(std::ostream& os, write_style) const {
  os << first_;
  if (positive_)
    os << " ≣ ";
  else
    os << " ≣̷ ";
  os << second_;
}


clone_source(objectidentical)
copy_source(objectidentical)

ref<alternatives> objectidentical::unify(unify_environment, const ref<formula>& x, unify_environment, database*, level, sublevel&, direction) const {
  if (trace_value & trace_unify)
    std::clog << "objectidentical::unify(\n  " << *this << ";\n  " << x << ")\n" << std::flush;
  const objectidentical* xp = cast_pointer<objectidentical>(x);
  if (xp == 0)  return O;
  if (positive_ != xp->positive_)  return O;
  if (positive_)
    return first_ == second_? I : O;
  return first_ != second_? I : O;
}

kleenean objectidentical::has(const ref<variable>& v, occurrence oc) const {
#if 1
  kleenean k1 = first_->has(v, oc);
  if (k1 == succeed)  return true;
  kleenean k2 = second_->has(v, oc);
  return k1 || k2;
#else
  kleenean mb;
  bool is_undecidable = false;
  mb = first_->has(v, oc);
  if (mb == true)  return true;
  if (mb == undecidable)  is_undecidable = true;
  mb = second_->has(v, oc);
  if (mb == true)  return true;
  if (mb == undecidable)  is_undecidable = true;
  if (is_undecidable)  return undecidable;
  return false;
#endif
}

void objectidentical::contains(std::set<ref<variable> >& s, std::set<ref<variable> >& bs, bool& more, occurrence oc) const {
  first_->contains(s, bs, more, oc);
  second_->contains(s, bs, more, oc);
}

kleenean objectidentical::free_for(const ref<formula>& f, const ref<variable>& x,
  std::set<ref<variable> >& s, std::list<ref<variable> >& bs) const {
  kleenean k1 = first_->free_for(f, x, s, bs);
  if (k1 == fail)  return false;
  kleenean k2 = second_->free_for(f, x, s, bs);
  return k1 && k2;
}

void objectidentical::unspecialize(depth x, bool y) {
  first_->unspecialize(x, y);
  second_->unspecialize(x, y);
}

ref<formula> objectidentical::rename(level lv, sublevel sl) const {
  objectidentical* ir = new objectidentical(*this);
  ir->first_ = ref<variable>(first_->rename(lv, sl));
  ir->second_ = ref<variable>(second_->rename(lv, sl));
  return ir;
}

ref<formula> objectidentical::substitute(const ref<substitution>& s, substitute_environment vt) const {
  ref<formula> v1 = first_->substitute(s, vt);
  ref<formula> v2 = second_->substitute(s, vt);
  if (trace_value & trace_substitute)
    std::clog << "objectidentical::substitute()\n  "
      << "(" << *this << ")" << s << "\n    "
      << "v1 = " << v1 << "\n    "
      << "v2 = " << v2
      << std::endl;
  variable* v1p = cast_pointer<variable>(v1);
  variable* v2p = cast_pointer<variable>(v2);
  if (v1p == 0 || v2p == 0)
    throw runtime_error("In \"objectidentical\", substitute error.");
  if (v1p->is_metaobject() || v2p->is_metaobject())
    return new objectidentical(*v1p, *v2p, positive_);
#if 1
  bool is_identical = (*v1p == *v2p);
#else
  bool is_identical = (v1p->total(*v2p) == equal);
#endif
#if 0
  if (positive_) {
    // Two objects tested identical will remain so after any substitution,
    // but two objects tested non-identical can become identiacl later after a
    // substituon. So introduce a condition in such a case.
    if (is_identical)  return new succeed_fail(true);
    return new objectidentical(*v1p, *v2p, positive_);
  }
#endif  
  return new succeed_fail(positive_? is_identical : !is_identical);
}

void objectidentical::set_bind(bind& b, name_variable_table& vt) {
  first_->set_bind(b, vt);  second_->set_bind(b, vt);
}

relation objectidentical::compare(const formula& x) const {
  const objectidentical* xp = dynamic_cast<const objectidentical*>(&x);
  if (xp == 0)  return unrelated;
  int a = inequality_compare(positive_, xp->positive_);
  if (a != 0)  return a;
  int c = first_->compare(*xp->first_);
  if (c != 0)  return c;
  return second_->compare(*xp->second_);
}

relation objectidentical::total(const formula& x) const {
  const objectidentical* xp = dynamic_cast<const objectidentical*>(&x);
  if (xp == 0)  throw runtime_error("In \"objectidentical\", total order error.");
  int a = inequality_compare(positive_, xp->positive_);
  if (a != 0)  return a;
  int c = first_->total(*xp->first_);
  if (c != 0)  return c;
  return second_->total(*xp->second_);
}

operator_precedence objectidentical::precedence() const {
  return identical_oprec;
}

void objectidentical::write(std::ostream& os, write_style) const {
  os << first_;
  if (positive_)
    os << " ≡ ";
  else
    os << " ≢ ";
  os << second_;
}


clone_source(free_in_object)
copy_source(free_in_object)

ref<alternatives> free_in_object::unify(unify_environment tt, const ref<formula>& x, unify_environment tx, database* dbp, level lv, sublevel& sl, direction dr) const {
  if (trace_value & trace_unify)
    std::clog << "free_in_object::unify(\n  " << *this << ";\n  " << x << ")\n" << std::flush;
  const free_in_object* xp = cast_pointer<free_in_object>(x);
  if (xp == 0)  return O;
  if (positive_ != xp->positive_)  return O;
  ref<alternatives> as = mli::unify(ref<formula>(variable_), tt, ref<formula>(xp->variable_), tx, dbp, lv, sl, dr);
  return as->unify(formula_, tt, xp->formula_, tx, dbp, lv, sl, dr);
}

kleenean free_in_object::has(const ref<variable>& v, occurrence oc) const {
#if 1
  kleenean k1 = variable_->has(v, oc);
  if (k1 == succeed)  return true;
  kleenean k2 = formula_->has(v, oc);
  return k1 || k2;
#else
  kleenean mb;
  bool is_undecidable = false;
  mb = variable_->has(v, oc);
  if (mb == true)  return true;
  if (mb == undecidable)  is_undecidable = true;
  mb = formula_->has(v, oc);
  if (mb == true)  return true;
  if (mb == undecidable)  is_undecidable = true;
  if (is_undecidable)  return undecidable;
  return false;
#endif
}

void free_in_object::contains(std::set<ref<variable> >& s, std::set<ref<variable> >& bs, bool& more, occurrence oc) const {
  variable_->contains(s, bs, more, oc);
  formula_->contains(s, bs, more, oc);
}

kleenean free_in_object::free_for(const ref<formula>& f, const ref<variable>& x,
  std::set<ref<variable> >& s, std::list<ref<variable> >& bs) const {
  kleenean k1 = variable_->free_for(f, x, s, bs);
  if (k1 == fail)  return false;
  kleenean k2 = formula_->free_for(f, x, s, bs);
  return k1 && k2;
}

void free_in_object::unspecialize(depth x, bool y) {
  variable_->unspecialize(x, y);
  formula_->unspecialize(x, y);
}

ref<formula> free_in_object::rename(level lv, sublevel sl) const {
  free_in_object* fp = new free_in_object(*this);
  fp->variable_ = ref<variable>(variable_->rename(lv, sl));
  fp->formula_ = formula_->rename(lv, sl);
  return fp;
}

ref<formula> free_in_object::substitute(const ref<substitution>& s, substitute_environment vt) const {
  ref<formula> v0 = variable_->substitute(s, vt);
  variable* vp = cast_pointer<variable>(v0);
  if (vp == 0)
    throw runtime_error("In free_in_object::substitute, substitution of variable not a variable.");
  ref<variable> v(*vp);
  ref<formula> f = formula_->substitute(s, vt);
  // The (not-)free-in test is only done when the variable v is object, as
  // only object variables can become bound. When v is a metaobjectvariable:
  // delay, until it is substituted with an object variable.
  if (vp->is_metaobject())
    return new free_in_object(v, f, positive_);
  kleenean is_free_in = f->has(v, free_occurrence);
  if (is_free_in == undecidable)
    return new free_in_object(v, f, positive_);
  return new succeed_fail(positive_? is_free_in : !is_free_in);
}

void free_in_object::set_bind(bind& b, name_variable_table& vt) {
  variable_->set_bind(b, vt);  formula_->set_bind(b, vt);
}

relation free_in_object::compare(const formula& x) const {
  const free_in_object* xp = dynamic_cast<const free_in_object*>(&x);
  if (xp == 0)  return unrelated;
  int a = inequality_compare(positive_, xp->positive_);
  if (a != 0)  return a;
  int c = variable_->compare(*xp->variable_);
  if (c != 0)  return c;
  return formula_->compare(*xp->formula_);
}

relation free_in_object::total(const formula& x) const {
  const free_in_object* xp = dynamic_cast<const free_in_object*>(&x);
  if (xp == 0)  throw runtime_error("In \"free_in_object\", total order error.");
  int a = inequality_compare(positive_, xp->positive_);
  if (a != 0)  return a;
  int c = variable_->total(*xp->variable_);
  if (c != 0)  return c;
  return formula_->total(*xp->formula_);
}

operator_precedence free_in_object::precedence() const {
  return free_oprec;
}

void free_in_object::write(std::ostream& os, write_style) const {
  os << variable_;
  if (!positive_)  os << " not";
  os << " free in " << formula_;
}


clone_source(free_for_object)
copy_source(free_for_object)

ref<alternatives> free_for_object::unify(unify_environment tt, const ref<formula>& x, unify_environment tx, database* dbp, level lv, sublevel& sl, direction dr) const {
  if (trace_value & trace_unify)
    std::clog << "free_for_object::unify(\n  " << *this << ";\n  " << x << ")\n" << std::flush;
  const free_for_object* xp = cast_pointer<free_for_object>(x);
  if (xp == 0)  return O;
  if (positive_ != xp->positive_)  return O;
  ref<alternatives> as = mli::unify(term_, tt, xp->term_, tx, dbp, lv, sl, dr);
  as = as->unify(ref<formula>(variable_), tt, ref<formula>(xp->variable_), tx, dbp, lv, sl, dr);
  return as->unify(formula_, tt, xp->formula_, tx, dbp, lv, sl, dr);
}

kleenean free_for_object::has(const ref<variable>& v, occurrence oc) const {
#if 1
  kleenean k1 = term_->has(v, oc);
  if (k1 == succeed)  return true;
  kleenean k2 = variable_->has(v, oc);
  if (k2 == succeed)  return true;
  kleenean k3 = formula_->has(v, oc);
  return k1 || k2 || k3;
#else
  kleenean mb;
  bool is_undecidable = false;
  mb = term_->has(v, oc);
  if (mb == true)  return true;
  if (mb == undecidable)  is_undecidable = true;
  mb = variable_->has(v, oc);
  if (mb == true)  return true;
  if (mb == undecidable)  is_undecidable = true;
  mb = formula_->has(v, oc);
  if (mb == true)  return true;
  if (mb == undecidable)  is_undecidable = true;
  if (is_undecidable)  return undecidable;
  return false;
#endif
}

void free_for_object::contains(std::set<ref<variable> >& s, std::set<ref<variable> >& bs, bool& more, occurrence oc) const {
  term_->contains(s, bs, more, oc);
  variable_->contains(s, bs, more, oc);
  formula_->contains(s, bs, more, oc);
}

kleenean free_for_object::free_for(const ref<formula>& f, const ref<variable>& x,
  std::set<ref<variable> >& s, std::list<ref<variable> >& bs) const {
  kleenean k1 = term_->free_for(f, x, s, bs);
  if (k1 == fail)  return false;
  kleenean k2 = variable_->free_for(f, x, s, bs);
  if (k2 == fail)  return false;
  kleenean k3 = formula_->free_for(f, x, s, bs);
  return k1 && k2 && k3;
}

void free_for_object::unspecialize(depth x, bool y) {
  term_->unspecialize(x, y);
  variable_->unspecialize(x, y);
  formula_->unspecialize(x, y);
}

ref<formula> free_for_object::rename(level lv, sublevel sl) const {
  free_for_object* fp = new free_for_object(*this);
  fp->term_ = term_->rename(lv, sl);
  fp->variable_ = ref<variable>(variable_->rename(lv, sl));
  fp->formula_ = formula_->rename(lv, sl);
  return fp;
}

ref<formula> free_for_object::substitute(const ref<substitution>& s, substitute_environment vt) const {
  ref<formula> v0 = variable_->substitute(s, vt);
  variable* vp = cast_pointer<variable>(v0);
  if (vp == 0)
    throw runtime_error("In free_for_object::substitute, substitution of variable not a variable.");
  ref<variable> v(*vp);
  ref<formula> t = term_->substitute(s, vt);
  ref<formula> f = formula_->substitute(s, vt);
  if (trace_value & trace_substitute)
    std::clog
     << "free_for_object::substitute:\n  "
     << ref<formula>(new free_for_object(t, v, f, positive_))
     << std::endl;
  kleenean is_free_for = f->free_for(t, v);
  if (is_free_for == undecidable)
    return new free_for_object(t, v, f, positive_);
  return new succeed_fail(positive_? is_free_for : !is_free_for);
}

void free_for_object::set_bind(bind& b, name_variable_table& vt) {
  term_->set_bind(b, vt);  variable_->set_bind(b, vt);  formula_->set_bind(b, vt);
}

relation free_for_object::compare(const formula& x) const {
  const free_for_object* xp = dynamic_cast<const free_for_object*>(&x);
  if (xp == 0)  return unrelated;
  int a = inequality_compare(positive_, xp->positive_);
  if (a != 0)  return a;
  int b = term_->compare(*xp->term_);
  if (!b)  return b;
  int c = variable_->compare(*xp->variable_);
  if (c != 0)  return c;
  return formula_->compare(*xp->formula_);
}

relation free_for_object::total(const formula& x) const {
  const free_for_object* xp = dynamic_cast<const free_for_object*>(&x);
  if (xp == 0)  throw runtime_error("In \"free_for_object\", total order error.");
  int a = inequality_compare(positive_, xp->positive_);
  if (a != 0)  return a;
  int b = term_->total(*xp->term_);
  if (!b)  return b;
  int c = variable_->total(*xp->variable_);
  if (c != 0)  return c;
  return formula_->total(*xp->formula_);
}

operator_precedence free_for_object::precedence() const {
  return free_oprec;
}

void free_for_object::write(std::ostream& os, write_style) const {
  os << term_;
  if (!positive_)  os << " not";
  os << " free for " << variable_ << " in " << formula_;
}


} // namespace mli

