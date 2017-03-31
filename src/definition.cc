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

#include "definition.hh"

#include "substitution.hh"


namespace mli {


clone_source(definition)
copy_source(definition)

ref<alternatives> definition::unify(unify_environment tt, const ref<formula>& x, unify_environment tx, database* dbp, level lv, sublevel& sl, direction dr) const {
  // Change this stuff: Obsolete.
  // Should probably unify as a tuple, as other data.
  // Include condition_.
  if (trace_value & trace_unify)
    std::clog << "definition::unify(\n  " << *this << ";\n  " << x << ")\n" << std::flush;
  ref<alternatives> as;
  ref<alternatives> bs = mli::unify(defined_, tt, x, tx, dbp, lv, sl, dr);
  as = as->append(bs + definer_);
  bs = mli::unify(definer_, tt, x, tx, dbp, lv, sl, dr);
  as = as->append(bs + defined_);
  return as;
}

void definition::contains(std::set<ref<variable> >& s, std::set<ref<variable> >& bs, bool& more, occurrence oc) const {
  defined_->contains(s, bs, more, oc);
  definer_->contains(s, bs, more, oc);
  condition_->contains(s, bs, more, oc);
}

kleenean definition::has(const ref<variable>& v, occurrence oc) const {
#if 1
  kleenean k1 = defined_->has(v, oc);
  if (k1 == succeed)  return true;
  kleenean k2 = definer_->has(v, oc);
  if (k2 == succeed)  return true;
  kleenean k3 = condition_->has(v, oc);
  return k1 || k2 || k3;
#else
  kleenean mb;
  bool is_undecidable = false;
  mb = defined_->has(v, oc);
  if (mb == true)  return true;
  if (mb == undecidable)  is_undecidable = true;
  mb = definer_->has(v, oc);
  if (mb == true)  return true;
  if (mb == undecidable)  is_undecidable = true;
  if (is_undecidable)  return undecidable;
  mb = condition_->has(v, oc);
  if (mb == true)  return true;
  if (mb == undecidable)  is_undecidable = true;
  if (is_undecidable)  return undecidable;
  return false;
#endif
}

kleenean definition::free_for(const ref<formula>& f, const ref<variable>& x,
  std::set<ref<variable> >& s, std::list<ref<variable> >& bs) const {
  kleenean k1 = defined_->free_for(f, x, s, bs);
  if (k1 == fail)  return false;
  kleenean k2 = definer_->free_for(f, x, s, bs);
  if (k2 == fail)  return false;
  kleenean k3 = condition_->free_for(f, x, s, bs);
  return k1 && k2 && k3;
}

void definition::unspecialize(depth x, bool y) {
  defined_->unspecialize(x, y);
  definer_->unspecialize(x, y);
  condition_->unspecialize(x, y);
}

ref<formula> definition::rename(level lv, sublevel sl) const {
  definition* fp = new definition(*this);
  fp->defined_ = defined_->rename(lv, sl);
  fp->definer_ = definer_->rename(lv, sl);
  fp->condition_ = condition_->rename(lv, sl);
  return fp;
}

ref<formula> definition::substitute(const ref<substitution>& s, substitute_environment vt) const {
  definition* fp = new definition(*this);
  fp->defined_ = defined_->substitute(s, vt);
  fp->definer_ = definer_->substitute(s, vt);
  fp->condition_ = condition_->substitute(s, vt);
  return fp;
}

void definition::set_bind(bind& b, name_variable_table& vt) {
  defined_->set_bind(b, vt);
  definer_->set_bind(b, vt);
  condition_->set_bind(b, vt);
}

relation definition::compare(const formula& x) const {
  const definition* xp = dynamic_cast<const definition*>(&x);
  if (xp == 0)  return unrelated;
  int c = defined_->compare(*xp->defined_);
  if (c != 0)  return c;
  c = definer_->compare(*xp->defined_);
  if (c != 0)  return c;
  return condition_->compare(*xp->definer_);
}

relation definition::total(const formula& x) const {
  const definition* xp = dynamic_cast<const definition*>(&x);
  if (xp == 0)  throw runtime_error("In \"definition\", total order error.");
  int c = defined_->total(*xp->defined_);
  if (c != 0)  return c;
  c = definer_->total(*xp->defined_);
  if (c != 0)  return c;
  return condition_->total(*xp->definer_);
}


void definition::write(std::ostream& os, write_style) const {
  if (!condition_.is_null())
    os << condition_ << " ⊢ ";
  if (defined_->precedence() < precedence().first_argument())
    os << "(" << defined_ << ")";
  else
    os << defined_;
  os << " ≔ ";
  if (definer_->precedence() < precedence().last_argument())
    os << "(" << definer_ << ")";
  else
    os << definer_;
}


clone_source(named_definition)
copy_source(named_definition)


} // namespace mli
