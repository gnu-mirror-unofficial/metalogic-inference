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

//#include "MLI.h"

#include "substitution.hh"

#include "metacondition.hh"


namespace mli {


ref_null(substitution);

clone_source(substitution);
copy_source(substitution);

ref<formula> substitution::operator()(const ref<formula>& x) const {
  variable_table vt;
  substitute_environment se(&vt);
#if 0
  // Put free variables onto table:
  std::set<ref<variable> > vs;
  x->contains(vs, free_occurrence);
  if (!vs.empty())
    vt.push_level();
  std::set<ref<variable> >::iterator i = vs.begin(), i1 = vs.end();
  for (; i != i1; ++i)
    vt.insert(*i, *i);
#endif
  return x->substitute(*this, se);
}

ref<alternatives> substitution::unify_substitution2(const ref<formula>& x, unify_environment tx, const ref<formula>& y, unify_environment ty, database* dbp, level lv, sublevel& sl, direction dr) const {
  return mli::unify(x, tx, y, ty, dbp, lv, sl, dr);
}

ref<alternatives> substitution::unify_substitution3(const ref<formula>&, unify_environment, const ref<formula>&, unify_environment, database*, level, sublevel&, direction) const {
  return O; // mli::unify(x, y, lv, dr) is already returned by unify_substitution2().
}

ref<alternatives> substitution::unify_substitution4(const ref<formula>&, unify_environment, const ref<formula>&, unify_environment, database*, level, sublevel&, direction) const {
  return O; // mli::unify(x, y, lv, dr) is already returned by unify_substitution2().
}

ref<alternatives> substitution::unify(unify_environment, const ref<formula>& x, unify_environment, database*, level, sublevel&, direction) const {
  if (trace_value & trace_unify)
    std::clog
     << "substitution::unify\n  " << *this << ";\n  " << x << ")" << std::endl;
  const substitution* xp = cast_pointer<substitution>(x);
  return (xp != 0) && (xp->is_identity())? I : O;
}

relation substitution::compare(const formula& x) const {
  const substitution* xp = dynamic_cast<const substitution*>(&x);
  if (xp == 0)  return unrelated;
  return xp->is_identity()? equal : unrelated;
}

relation substitution::total(const formula& x) const {
  const substitution* xp = dynamic_cast<const substitution*>(&x);
  if (xp == 0 || !xp->is_identity())
    throw runtime_error("In \"substitution\", total order error.");
  return equal;
}


clone_source(variable_substitution)
copy_source(variable_substitution)

ref<formula> variable_substitution::substitute_variable(const ref<variable>& x, substitute_environment vt) const {
  if (trace_value & trace_substitute) {
    std::clog << "Begin variable_substitution::substitute_variable\n  "
      << "(" << x << ")" << *this << ".\n"
      << std::flush;
    if (vt.table_ != 0) {
      variable_table::stack::iterator i,
        i0 = vt.table_->table_stack_.begin(), i1 = vt.table_->table_stack_.end();
      if (i0 != i1) {
        std::clog << "Variable table:\n";
        for (i = i0; i != i1; ++i) {
          if (i != i0)  std::clog << "\n";
          variable_table::table::iterator j, j0 = i->begin(), j1 = i->end();
          for (j = j0; j != j1; ++j) {
            if (j != j0)  std::clog << ", ";
            std::clog << "(" << j->first << ";" << j->second << ")";
          }
        }
        std::clog << std::endl;
      }
    }
  }
  // A substitution x[v.f].
  if (x == variable_) {
    const variable* xp = (const variable*)x;
    if (xp == 0)
      throw substitute_error("In variable_substitution::substitute_variable, variable equal with non-variable.");
    if (bind_ != 0) {
      if (vt.table_ == 0)
        goto no_substitution;
      maybe<ref<formula> > mf = vt.table_->find(x);
      if (!mf)
        goto no_substitution;
      bound_formula* bfp = cast_pointer<bound_formula>(*mf);
      if (bfp == 0)
        throw runtime_error("In variable_substitution::substitute_variable, null bound_formula.");
      if (bind_ != bfp->bind_)
        goto no_substitution;
      return formula_;
    }
    // In a substitution y ≔ x[v.f]:
    if (all_occurrences_ || (vt.table_ == 0) || (!vt.table_->find(x))) {
      if (trace_value & trace_substitute)
        std::clog << "variable_substitution::substitute_variable\n  "
          << "(" << x << ")" << *this << " =\n    "
          << formula_
          << std::endl;
      return formula_;
    }
  }

no_substitution:
  ref<formula> ret;
  // Delayed return here, if an undecidable substitution (if say x is a 
  // formula variable and variable_ is an object variable..
  // Can be accepted, if level numbers are unequal.
  if (x->may_contain(variable_)) {// && !x->has(v, free_occurence())
    if (trace_value & trace_substitute) {
      std::clog << "variable_substitution::substitute_variable\n  "
        << "(" << x << ")" << *this << ", not free in ≕\n    ";
      std::set<ref<variable> >::const_iterator i,
        i0 = not_free_in_.begin(), i1 = not_free_in_.end();
      for (i = i0; i != i1; ++i) {
        if (i != i0)  std::clog << ", ";
        std::clog << *i;
      }
      std::clog << std::endl;
    }
    // Check if variable_ is not free in x, in which case
    // there should be no delayed substitution.
    if (not_free_in_.find(x) != not_free_in_.end() || !is_explicit_)
      ret = ref<formula>(x);
    else
      // Note that *this must now have is_explicit_ == true:
      ret = new substitution_formula(*this, ref<formula>(x));
  }
  else
    ret = ref<formula>(x);
  if (trace_value & trace_substitute)
    std::clog << "variable_substitution::substitute_variable\n  "
      << "(" << x << ")" << *this << " =\n    "
      << ret << std::endl;
  return ret;
}

ref<alternatives> variable_substitution::unify_substitution2(const ref<formula>& x, unify_environment tx, const ref<formula>& y, unify_environment ty, database* dbp, level lv, sublevel& sl, direction dr) const {
  ref<alternatives> as; // Return value.
  if (trace_value & trace_unify)
    std::clog << "Begin variable_substitution::unify_substitution2\n  "
      << "unify(" << x << *this << ", " << y << ").\n"
      << std::flush;
  split_formula sf = y->split(tx, variable_, formula_, ty, dbp, lv, sl, dr);
  if (trace_value & trace_unify)
    std::clog << "variable_substitution::unify_substitution2\n  "
      << "unify(" << x << *this << ", " << y << "):\n"
      << sf << std::flush;
  split_formula::iterator i, i0 = sf.begin(), i1 = sf.end();
  for (i = i0; i != i1; ++i) {
    ref<alternatives> as0 = mli::unify(formula_, i->first.formulas_, dbp, lv, sl);
    if (trace_value & trace_unify)
      std::clog << "variable_substitution::unify_substitution2\n  "
        << "unify(" << formula_ << ", " << i->first << ") ="
        << as0
        << std::endl;
    if (as0->empty())  continue;
    ref<alternatives> as1 = as0->unify(x, tx, i->second, ty, dbp, lv, sl, dr);
    alternatives* as1p = (alternatives*)as1;
    ref<alternatives> as2;
    if (as1p != 0) {
    alternatives::iterator j, j0 = as1p->begin(), j1 = as1p->end();
      for (j = j0; j != j1; ++j) {
        ref<substitution> s = (*j)->substitution_;
        ref<formula> f = (*s)(x);
        if (trace_value & trace_unify)
          std::clog << "variable_substitution::unify_substitution2\n  "
            << "alternative " << *j << "\n    "
            << f
            << std::endl;
#if 1
        // Make not-free-in simplification here:        
        std::set<ref<variable> > free;
        bool b = f->contains(free, free_occurrence);
        if (b) { // Substitution of f may produce free variables:
          // Check that the free variables of f which may contain variable_
          // are in not_free_in_.
          std::set<ref<variable> >::iterator k, k0 = free.begin(), k1 = free.end();
          bool delay = false;
          for (k = k0; k != k1; ++k) {
            if ((*k)->may_contain(variable_)
                && (not_free_in_.find(*k) == not_free_in_.end())) {
              delay = true;
              break;
            }
          }
          if (delay)
            as2 = as2->push_back(*j + ref<formula>(new free_in_object(variable_, f, false)));
          else
            as2 = as2->push_back(*j);
        }
        else
          as2 = as2->push_back(*j);
#else
        kleenean mb = f->has(variable_, free_occurrence);
        if (mb == undecidable)
          as2 = as2->push_back(*j + ref<formula>(new free_in_object(variable_, f, false)));
        else
          as2 = as2->push_back(*j);
#endif
      }
    }
    if (trace_value & trace_unify)
      std::clog << "variable_substitution::unify_substitution2\n  "
        << "as->unify(" << x << ", " << i->second << ") where as ="
        << as0
        << "\n  ="
        << as2
        << std::endl;
    if (!as2->empty())
      as = as->append(as2);
  }
  if (trace_value & trace_unify)
    std::clog << "variable_substitution::unify_substitution2\n  "
      << "unify(" << x << *this << ", " << y << "):"
      << as << std::endl;
  return as;
}

ref<alternatives> variable_substitution::unify_substitution3(const ref<formula>& x, unify_environment tx, const ref<formula>& y, unify_environment ty, database* dbp, level lv, sublevel& sl, direction dr) const {
  // u(A[x.t], B) type 3 solutions u(x, A) * u(t, B):
  if (trace_value & trace_unify)
    std::clog << "Begin variable_substitution::unify_substitution3\n  "
      << "unify(" << x << *this << ", " << y << ").\n"
      << std::flush;
  ref<alternatives> as = mli::unify(ref<formula>(variable_), tx, x, tx, dbp, lv, sl, dr);
  as = as->unify(formula_, tx, y, ty, dbp, lv, sl, dr);
  if (trace_value & trace_unify)
    std::clog << "variable_substitution::unify_substitution3\n  "
      << "unify(" << x << *this << ", " << y << "):"
      << as << std::endl;
  return as;
}

ref<alternatives> variable_substitution::unify_substitution4(const ref<formula>& x, unify_environment tx, const ref<formula>& y, unify_environment ty, database* dbp, level lv, sublevel& sl, direction dr) const {
  // u(A[x.t], B) type 4 solutions u(A, B) * u(x, t):
  if (trace_value & trace_unify)
    std::clog << "Begin variable_substitution::unify_substitution4\n  "
      << "unify(" << x << *this << ", " << y << ").\n"
      << std::flush;
#if 0
  // The u(x, t) causes non-termination in connection with delayed substitutions.
  // So, for now, only unify when x == t.
  ref<alternatives> as;
  if (ref<formula>(variable_) == formula_)
    as = mli::unify(x, tx, y, ty, dbp, lv, sl, dr);
#else
  ref<alternatives> as = mli::unify(ref<formula>(variable_), tx, formula_, tx, dbp, lv, sl, dr);
  as = as->unify(x, tx, y, ty, dbp, lv, sl, dr);
#endif
  if (trace_value & trace_unify)
    std::clog << "variable_substitution::unify_substitution4\n  "
      << "unify(" << x << *this << ", " << y << "):"
      << as << std::endl;
  return as;
}

void variable_substitution::set_bind(bind& b, name_variable_table& vs) {
  variable_->set_bind(b, vs);  
  formula_->set_bind(b, vs);  
}

ref<formula> variable_substitution::rename(level lv, sublevel sl) const {
  variable_substitution* mp = new variable_substitution(*this);
  mp->variable_ = ref<variable>(variable_->rename(lv, sl));
  mp->formula_ = formula_->rename(lv, sl);
  return mp;  
}

kleenean variable_substitution::has(const ref<variable>& v, occurrence oc) const {
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

void variable_substitution::contains(std::set<ref<variable> >& s, std::set<ref<variable> >& bs, bool& more, occurrence oc) const {
  variable_->contains(s, bs, more, oc);
  formula_->contains(s, bs, more, oc);
}

kleenean variable_substitution::free_for(const ref<formula>& f, const ref<variable>& x, 
  std::set<ref<variable> >& s, std::list<ref<variable> >& bs) const {
  kleenean k1 = variable_->free_for(f, x, s, bs);
  if (k1 == fail)  return false;
  kleenean k2 = formula_->free_for(f, x, s, bs);
  return k1 && k2;
}

void variable_substitution::unspecialize(depth x, bool y) {
  variable_->unspecialize(x, y);
  formula_->unspecialize(x, y);
}

ref<formula> variable_substitution::substitute(const ref<substitution>& s, substitute_environment vt) const {
  ref<formula> v0 = variable_->substitute(s, vt);
  variable* vp = cast_pointer<variable>(v0);
  if (vp == 0)
    throw substitute_error("In variable_substitution::substitute, substitution of variable not a variable.");
  variable_substitution* mp = new variable_substitution(*this);
  mp->variable_ = *vp;
  mp->formula_ = formula_->substitute(s, vt);
  return mp;  
}

ref<alternatives> variable_substitution::unify(unify_environment tt, const ref<formula>& x, unify_environment tx, database* dbp, level lv, sublevel& sl, direction dr) const {
  if (trace_value & trace_unify)
    std::clog << "variable_substitution::unify(\n  " << *this << ";\n  " << x << ")\n" << std::flush;
  const variable_substitution* xp = cast_pointer<variable_substitution>(x);
  if (xp == 0)  return O;
  ref<alternatives> as = mli::unify(ref<formula>(variable_), tt, ref<formula>(xp->variable_), tx, dbp, lv, sl, dr);
  return as->unify(formula_, tt, xp->formula_, tx, dbp, lv, sl, dr);  
}


struct variable_substitution_construct {
  ref<variable> variable_;
  bool all_occurrences_;
  bind bind_;
  bool is_explicit_;
  std::set<ref<variable> > not_free_in_;

  variable_substitution_construct(const ref<variable>& v, bool a,
    bind b, bool ex, std::set<ref<variable> > nf)
   : variable_(v), all_occurrences_(a), bind_(b), is_explicit_(ex), not_free_in_(nf) {}

  ref<formula> operator()(const ref<formula>& x) const {
    return new variable_substitution(variable_, x, all_occurrences_, bind_, is_explicit_, not_free_in_);
  }
};


split_formula variable_substitution::split(unify_environment tg,
  const ref<variable>& x, const ref<formula>& t, unify_environment tt, database* dbp, level lv, sublevel& sl, direction dr) const {
  split_formula sf(*this);  // Return value.
  // If t and *this unify, then *this can be replaced by x:
  ref<alternatives> as = mli::unify(t, tt, *this, tg, dbp, lv, sl, dr);
  if (!as->empty())
    sf.push_back(*this, ref<formula>(x));
  sf.append(mli::split(formula_, tg, variable_substitution_construct(variable_, all_occurrences_, bind_, is_explicit_, not_free_in_), x, t, tt, dbp, lv, sl, dr));
  return sf;
}

ref<substitution> variable_substitution::innermost() const {
  return *this;
}

ref<substitution> variable_substitution::without() const {
  return (substitution*)0;
}

ref<substitution> variable_substitution::outermost() const {
  return *this;
}

ref<substitution> variable_substitution::within() const {
  return (substitution*)0;
}

relation variable_substitution::compare(const formula& x) const {
  const variable_substitution* xp = dynamic_cast<const variable_substitution*>(&x);
  if (xp == 0)  return unrelated;
  int c = variable_->compare(*xp->variable_);
  if (c != 0)  return c;
  return formula_->compare(*xp->formula_);
}

relation variable_substitution::total(const formula& x) const {
  const variable_substitution* xp = dynamic_cast<const variable_substitution*>(&x);
  if (xp == 0)  throw runtime_error("In variable_substitution, total order error.");
  int c = variable_->total(*xp->variable_);
  if (c != 0)  return c;
  return formula_->total(*xp->formula_);
}

void variable_substitution::write(std::ostream& os, write_style ws) const {
  bool write_reverse = write_substitution_mapto_reverse & ws;
  os << "[";
  if ((trace_value & trace_bind) && bind_ != 0)  os << bind_;
  if (write_reverse)
    os << formula_ << (all_occurrences_? "//" : "/") << variable_;
  else {
    os << variable_;
    if (!not_free_in_.empty()) {
      os << " not free in ";
      std::set<ref<variable> >::const_iterator i,
        i0 = not_free_in_.begin(), i1 = not_free_in_.end();
      for (i = i0; i != i1; ++i) {
        if (i != i0)  os << ", ";
        (*i)->write(os, ws);
      }
    }
    os << (all_occurrences_? ":" : ".") << formula_;
  }
  os << "]";
}


ref<substitution> explicit_free_occurrences_substitution(const ref<variable>& i, const ref<formula>& t) {
  return new variable_substitution(i, t, false, 0, true);
}

ref<substitution> free_occurrences_substitution(const ref<variable>& i, const ref<formula>& t) {
  return new variable_substitution(i, t);
}

ref<substitution> all_occurrences_substitution(const ref<variable>& i, const ref<variable>& t) {
  return new variable_substitution(i, ref<formula>(t), true);
}

ref<substitution> local_substitution(const ref<variable>& i, const ref<variable>& t, bind b) {
  return new variable_substitution(i, ref<formula>(t), true, b);
}


clone_source(composition)
copy_source(composition)

ref<formula> composition::substitute_variable(const ref<variable>& x, substitute_environment vt) const {
  return (inner_->substitute_variable(x, vt))->substitute(outer_, vt);
}

ref<alternatives> composition::unify_substitution2(const ref<formula>& x, unify_environment tx, const ref<formula>& y, unify_environment ty, database* dbp, level lv, sublevel& sl, direction dr) const {
  return outer_->unify_substitution2(new substitution_formula(inner_, x), tx, y, ty, dbp, lv, sl, dr);
}

ref<alternatives> composition::unify_substitution3(const ref<formula>& x, unify_environment tx, const ref<formula>& y, unify_environment ty, database* dbp, level lv, sublevel& sl, direction dr) const {
  return outer_->unify_substitution3(new substitution_formula(inner_, x), tx, y, ty, dbp, lv, sl, dr);
}

ref<alternatives> composition::unify_substitution4(const ref<formula>& x, unify_environment tx, const ref<formula>& y, unify_environment ty, database* dbp, level lv, sublevel& sl, direction dr) const {
  return outer_->unify_substitution4(new substitution_formula(inner_, x), tx, y, ty, dbp, lv, sl, dr);
}

void composition::set_bind(bind& b, name_variable_table& vs) {
  inner_->set_bind(b, vs);  
  outer_->set_bind(b, vs);  
}

ref<formula> composition::rename(level lv, sublevel sl) const {
  composition* mp = new composition(*this);
  mp->inner_ = ref<substitution>(inner_->rename(lv, sl));
  mp->outer_ = ref<substitution>(outer_->rename(lv, sl));
  return mp;
}

kleenean composition::has(const ref<variable>& v, occurrence oc) const {
#if 1
  kleenean k1 = inner_->has(v, oc);
  if (k1 == succeed)  return true;
  kleenean k2 = outer_->has(v, oc);
  return k1 || k2;
#else
  kleenean mb;
  bool is_undecidable = false;
  mb = inner_->has(v, oc);
  if (mb == true)  return true;
  if (mb == undecidable)  is_undecidable = true;
  mb = outer_->has(v, oc);
  if (mb == true)  return true;
  if (mb == undecidable)  is_undecidable = true;
  if (is_undecidable)  return undecidable;
  return false;
#endif
}

void composition::contains(std::set<ref<variable> >& s, std::set<ref<variable> >& bs, bool& more, occurrence oc) const {
  inner_->contains(s, bs, more, oc);
  outer_->contains(s, bs, more, oc);
}

kleenean composition::free_for(const ref<formula>& f, const ref<variable>& x, 
  std::set<ref<variable> >& s, std::list<ref<variable> >& bs) const {
  kleenean k1 = inner_->free_for(f, x, s, bs);
  if (k1 == fail)  return false;
  kleenean k2 = outer_->free_for(f, x, s, bs);
  return k1 && k2;
}

void composition::unspecialize(depth x, bool y) {
  inner_->unspecialize(x, y);
  outer_->unspecialize(x, y);  
}

ref<formula> composition::substitute(const ref<substitution>& s, substitute_environment vt) const {
  composition* mp = new composition(*this);
  mp->inner_ = ref<substitution>(inner_->substitute(s, vt));
  mp->outer_ = ref<substitution>(outer_->substitute(s, vt));
  return mp;
}

ref<alternatives> composition::unify(unify_environment tt, const ref<formula>& x, unify_environment tx, database* dbp, level lv, sublevel& sl, direction dr) const {
  if (trace_value & trace_unify)
    std::clog << "composition::unify(\n  " << *this << ";\n  " << x << ")\n" << std::flush;
  const composition* xp = cast_pointer<composition>(x);
  if (xp == 0)  return O;
  ref<alternatives> as = mli::unify(ref<formula>(inner_), tt, ref<formula>(xp->inner_), tx, dbp, lv, sl, dr);
  return as->unify(ref<formula>(outer_), tt, ref<formula>(xp->outer_), tx, dbp, lv, sl, dr);  
}


struct composition_construct {
  ref<formula> operator()(const ref<formula>& x, const ref<formula>& y) const {
    return new composition(ref<substitution>(x), ref<substitution>(y));
  }
};

split_formula composition::split(unify_environment tg,
  const ref<variable>& x, const ref<formula>& t, unify_environment tt, database* dbp, level lv, sublevel& sl, direction dr) const {
  split_formula sf(*this);  // Return value.
  // If t and *this unify, then *this can be replaced by x:
  ref<alternatives> as = mli::unify(t, tt, *this, tg, dbp, lv, sl, dr);
  if (!as->empty())
    sf.push_back(*this, ref<formula>(x));
  sf.append(mli::split(ref<formula>(outer_), ref<formula>(inner_), tg, composition_construct(), x, t, tt, dbp, lv, sl, dr));
  return sf;
}

ref<substitution> composition::innermost() const {
  return inner_->innermost();
}

ref<substitution> composition::without() const {
  ref<substitution> s = inner_->without();
  if (s->is_identity())
    return outer_;
  return new composition(outer_, s);
}

ref<substitution> composition::outermost() const {
  return outer_->outermost();
}

ref<substitution> composition::within() const {
  ref<substitution> s = outer_->within();
  if (s->is_identity())
    return inner_;
  return new composition(s, inner_);
}

relation composition::compare(const formula& x) const {
  const composition* xp = dynamic_cast<const composition*>(&x);
  if (xp == 0)  return unrelated;
  int c = inner_->compare(*xp->inner_);
  if (c != 0)  return c;
  return outer_->compare(*xp->outer_);
}

relation composition::total(const formula& x) const {
  const composition* xp = dynamic_cast<const composition*>(&x);
  if (xp == 0)  throw runtime_error("In composition, total order error.");
  int c = inner_->total(*xp->inner_);
  if (c != 0)  return c;
  return outer_->total(*xp->outer_);
}

void composition::write(std::ostream& os, write_style ws) const {
  bool write_reverse = write_substitution_composition_reverse & ws;
  if (write_reverse)
    os << outer_ << " o " << inner_;
  else
    os << inner_ << outer_;
}


ref<substitution> operator+(const ref<substitution>& outer, const ref<substitution>& inner) {
  if (inner->is_identity())  return outer;
  if (outer->is_identity())  return inner;
  return new composition(outer, inner);
}

ref<substitution> operator*(const ref<substitution>& inner, const ref<substitution>& outer) {
  if (inner->is_identity())  return outer;
  if (outer->is_identity())  return inner;
  return new composition(outer, inner);
}


clone_source(substitution_formula)
copy_source(substitution_formula)

formula_type substitution_formula::get_formula_type() const {
  return formula_->get_formula_type();
}

void substitution_formula::set_bind(bind& b, name_variable_table& t) {
  substitution_->set_bind(b, t);
  formula_->set_bind(b, t);
}

ref<formula> substitution_formula::rename(level lv, sublevel sl) const {
  substitution_formula* sfp = new substitution_formula(*this);
  sfp->substitution_ = ref<substitution>(substitution_->rename(lv, sl));
  sfp->formula_ = formula_->rename(lv, sl);
  return sfp;
}

kleenean substitution_formula::has(const ref<variable>& v, occurrence oc) const {
#if 1
  // If v is substituted by substitution_:
  // If oc == free: return false
  // if oc = bound: if substitution_ on v is all occurances, return false.
  kleenean k1 = substitution_->has(v, oc);
  if (k1 == succeed)  return true;
  kleenean k2 = formula_->has(v, oc);
  return k1 || k2;
#else
  kleenean mb;
  bool is_undecidable = false;
  mb = substitution_->has(v, oc);
  if (mb == true)  return true;
  if (mb == undecidable)  is_undecidable = true;
  mb = formula_->has(v, oc);
  if (mb == true)  return true;
  if (mb == undecidable)  is_undecidable = true;
  if (is_undecidable)  return undecidable;
  return false;
#endif
}

void substitution_formula::contains(std::set<ref<variable> >& vs, std::set<ref<variable> >& bs, bool& more, occurrence oc) const {
  substitution_->contains(vs, bs, more, oc);
  formula_->contains(vs, bs, more, oc);
}

kleenean substitution_formula::free_for(const ref<formula>& f, const ref<variable>& x,
    std::set<ref<variable> >& s, std::list<ref<variable> >& bs) const {
  kleenean k1 = substitution_->free_for(f, x, s, bs);
  if (k1 == fail)  return false;
  kleenean k2 = formula_->free_for(f, x, s, bs);
  return k1 && k2;
}

void substitution_formula::unspecialize(depth x, bool y) {
  substitution_->unspecialize(x, y);
  formula_->unspecialize(x, y);
}

long substitute_count = 0;

ref<formula> substitution_formula::substitute(const ref<substitution>& s, substitute_environment vt) const {
  if (trace_value & trace_substitute)
    std::clog
     << "Begin substitution_formula::substitute:\n  " << *this
     << ".substitute(" << s << ")"
     << std::endl;
  if (++substitute_count > 1000)
    throw runtime_error("In substitution_formula::substitute, count exceeded.");
  ref<substitution> si = s->innermost();
  ref<substitution> so = s->without();
  ref<substitution> s1 = ref<substitution>(substitution_->substitute(si, vt));
  ref<formula> f1 = formula_->substitute(si, vt);
  ref<formula> fr;
  if (cast_pointer<substitution_formula>(f1) == 0)
    fr = f1->substitute(s1, vt);
  else
    fr = new substitution_formula(s1, f1);
  if (!so->is_identity())
    fr = fr->substitute(so, vt);
  if (trace_value & trace_substitute)
    std::clog
     << "End substitution_formula::substitute:\n  " << *this
     << ".substitute(" << s << "):\n    "
     << fr
     << std::endl;
  return fr;
}

ref<alternatives> substitution_formula::unify(unify_environment tt, const ref<formula>& x, unify_environment tx, database* dbp, level lv, sublevel& sl, direction dr) const {
  ref<alternatives> as;
  if (trace_value & trace_unify)
    std::clog
     << "substitution_formula::unify(\n  " << *this << ";\n  " << x << ")"
     << std::endl;
  const substitution_formula* xp = cast_pointer<substitution_formula>(x);
  if (xp != 0) {
    // u(A[x.t], B[y.u]) type 1 solution u(x, y) u(t, u) u(A, B).
    as = as->append(unify1(tt, *xp, tx, dbp, lv, sl, dr));
    // u(A, B[y.u]) type 2 solutions:
    as = as->append(xp->unify2(tx, *this, tt, dbp, lv, sl, !dr));
    // u(A, B[y.u]) type 3 solutions:
    as = as->append(xp->unify3(tx, *this, tt, dbp, lv, sl, !dr));
  }
  // u(A[x.t], B) type 2 solutions:
  as = as->append(unify2(tt, x, tx, dbp, lv, sl, dr));
  // u(A[x.t], B) type 3 solutions:
  as = as->append(unify3(tt, x, tx, dbp, lv, sl, dr));
#if 1
  // Somehow causes nontermination together with delayed substitutions:
  // u(A[x.t], B) type 4 solutions:
  as = as->append(unify4(tt, x, tx, dbp, lv, sl, dr));
#endif
  return as;
}

ref<alternatives> substitution_formula::unify1(unify_environment tt, const substitution_formula& sf, unify_environment tx, database* dbp, level lv, sublevel& sl, direction dr) const {
  // u(A[x.t], B[y.u]) type 1 solution u(x, y) u(t, u) u(A, B).
  ref<alternatives> as =
    mli::unify(ref<formula>(substitution_->outermost()), tt, ref<formula>(sf.substitution_->outermost()), tt, dbp, lv, sl, dr);
  if (trace_value & trace_unify)
    std::clog
     << "substitution_formula::unify(\n  "
     << substitution_->outermost() << ";\n  " << sf.substitution_->outermost() << ") ="
     << as
     << std::endl;
    as = as->unify(within(), tt, sf.within(), tx, dbp, lv, sl, dr);
  if (trace_value & trace_unify)
    std::clog
     << "substitution_formula::unify(\n  "
     << within() << ";\n  " << sf.within() << ") ="
     << as
     << std::endl;
  return as;
}

ref<alternatives> substitution_formula::unify2(unify_environment tt, const ref<formula>& x, unify_environment tx, database* dbp, level lv, sublevel& sl, direction dr) const {
  // u(A[x.t], B) type 2 solutions:
  return substitution_->unify_substitution2(formula_, tt, x, tx, dbp, lv, sl, dr);
}

ref<alternatives> substitution_formula::unify3(unify_environment tt, const ref<formula>& x, unify_environment tx, database* dbp, level lv, sublevel& sl, direction dr) const {
  // u(A[x.t], B) type 3 solutions u(x, A) * u(t, B):
  return substitution_->unify_substitution3(formula_, tt, x, tx, dbp, lv, sl, dr);
}

size_type unify4_count = 0;

ref<alternatives> substitution_formula::unify4(unify_environment tt, const ref<formula>& x, unify_environment tx, database* dbp, level lv, sublevel& sl, direction dr) const {
  if (++unify4_count > 400)
    throw runtime_error("In substitution_formula::unify4, count overflow.");
  // u(A[x.t], B) type 4 solutions u(A, B) * u(x, t):
  return substitution_->unify_substitution4(formula_, tt, x, tx, dbp, lv, sl, dr);
}


struct substitution_formula_construct {
  ref<formula> operator()(const ref<formula>& x, const ref<formula>& y) const {
    return new substitution_formula(ref<substitution>(x), y);
  }
};

split_formula substitution_formula::split(unify_environment tg,
  const ref<variable>& x, const ref<formula>& t, unify_environment tt, database* dbp, level lv, sublevel& sl, direction dr) const {
  split_formula sf(*this);  // Return value.
  // If t and *this unify, then *this can be replaced by x:
  ref<alternatives> as = mli::unify(t, tt, *this, tg, dbp, lv, sl, dr);
  if (!as->empty())
    sf.push_back(*this, ref<formula>(x));
  sf.append(mli::split(ref<formula>(substitution_), formula_, tg, substitution_formula_construct(), x, t, tt, dbp, lv, sl, dr));
  return sf;
}

ref<formula> substitution_formula::within() const {
  ref<substitution> s = substitution_->within();
  if (trace_value & trace_unify)
    std::clog
     << "substitution_formula::within(\n  "
     << *this << "):\n  "
     << "s = " << s
     << std::endl;
  if (s.is_null())  return formula_;
  return new substitution_formula(s, formula_);
}

relation substitution_formula::compare(const formula& x) const {
  const substitution_formula* xp = dynamic_cast<const substitution_formula*>(&x);
  if (xp == 0)  return unrelated;
  int c = substitution_->compare(*xp->substitution_);
  if (c != 0)  return c;
  return formula_->compare(*xp->formula_);
}

relation substitution_formula::total(const formula& x) const {
  const substitution_formula* xp = dynamic_cast<const substitution_formula*>(&x);
  if (xp == 0)  throw runtime_error("In substitution_formula, total order error.");
  int c = substitution_->total(*xp->substitution_);
  if (c != 0)  return c;
  return formula_->total(*xp->formula_);
}

operator_precedence substitution_formula::precedence() const {
  return substitution_formula_oprec;
}

void substitution_formula::write(std::ostream& os, write_style ws) const {
#if 1
  	if (formula_->precedence() < precedence().first_argument())  os << "(";
	  formula_->write(os, ws);
	  if (formula_->precedence() < precedence().first_argument())  os << ")";
    os << substitution_;
#else
    os << "(" << formula_ << substitution_ << ")";
//    os << formula_ << "." << substitution_;
#endif
}


ref_null(alternative);

clone_source(alternative)
copy_source(alternative)

ref<alternative> alternative::label(const ref<labelstatement>& ls) {
  alternative* ap = this->clone();
  ref<alternative> a(ap);
  ap->labelstatements_.push_back(ls);
  return a;
}

ref<alternative> operator|=(const ref<alternative>& x, const ref<formula>& y) {
  if (trace_value & trace_unify)
    std::clog
     << "premise(\n  "
     << x << ";\n  "
     << y << ")"
     << std::endl;
  if (x.is_null())  return (alternative*)0;
  if (y->metaempty())  return x;
  alternative* ap = x->clone();
  ref<alternative> a(ap);
  ap->goal_ = new inference(x->goal_, (*x->substitution_)(y), inference::infer_);
  return a;
}

void alternative::write(std::ostream& os, write_style ws) const {
  std::list<ref<labelstatement> >::const_iterator i,
    i0 = labelstatements_.begin(), i1 = labelstatements_.end();
  if (!(ws & write_statement)) {
    for (i = i0; i != i1; ++i) {
      if (i != i0)  os << ", ";
      (*i)->write(os, ws);
    }
    if (!bound_in_proof_.empty()) {
      os << "(";
      std::set<ref<variable> >::const_iterator j,
        j0 = bound_in_proof_.begin(), j1 = bound_in_proof_.end();
      for (j = j0; j != j1; ++j) {
        if (j != j0)  os << ", ";
        (*j)->write(os, ws);
      }
      os << ")";
    }
    return;
  }
  for (i = i0; i != i1; ++i) {
    if (!i->is_null()) {
      (*i)->write(os, write_style(write_name | write_type | write_statement | tabs2));
      os << "\n";
    }
  }
  substitution_->write(os, ws);
  if (!goal_.is_null()) {
    os << "\n ⊣ ";
    goal_->write(os, ws);
  }
  if (!unifier_.is_null()) {
    os << "\n      unifier: ";
    unifier_->write(os, ws);
  }
  if (!bound_in_proof_.empty()) {
    os << "\n      bound in proof: ";
    std::set<ref<variable> >::const_iterator j,
      j0 = bound_in_proof_.begin(), j1 = bound_in_proof_.end();
    for (j = j0; j != j1; ++j) {
      if (j != j0)  os << ", ";
      (*j)->write(os, ws);
    }
  }
}


ref<alternative> operator+(const ref<alternative>& x, const ref<alternative>& y) {
  alternative* ap = new alternative();
  ref<alternative> a(ap);
  ap->substitution_ = x->substitution_ + y->substitution_;
  // Dictated by use in alternatives::unify(const ref<formula>&):
  ap->unifier_ = (*x->substitution_)(y->unifier_);
  if (!y.is_null())
    ap->labelstatements_.insert(ap->labelstatements_.end(),
      y->labelstatements_.begin(), y->labelstatements_.end());
  if (!x.is_null())
    ap->labelstatements_.insert(ap->labelstatements_.end(),
      x->labelstatements_.begin(), x->labelstatements_.end());
  ap->goal_ = concatenate(x->goal_, (*x->substitution_)(y->goal_), metaand_);
  ap->bound_in_proof_.insert(x->bound_in_proof_.begin(), x->bound_in_proof_.end());
  ap->bound_in_proof_.insert(y->bound_in_proof_.begin(), y->bound_in_proof_.end());
  return a;
}

#if 1
ref<alternative> operator*(const ref<alternative>& x, const ref<alternative>& y) {
  alternative* ap = new alternative();
  ref<alternative> a(ap);
  ap->substitution_ = x->substitution_ * y->substitution_;
  ap->unifier_ = (*y->substitution_)(x->unifier_);
  ap->goal_ = concatenate(y->goal_, (*y->substitution_)(x->goal_), metaand_);
  return a;
}
#endif


ref<alternative> operator+(const ref<alternative>& x, const ref<formula>& y) {
  if (trace_value & trace_unify)
    std::clog
     << "alternative +(\n  "
     << x << ";\n  "
     << y << ")"
     << std::endl;
  if (x.is_null())  return (alternative*)0;
  if (y.is_null())  return x;
  alternative* ap = x->clone();
  ref<alternative> a(ap);
  ap->goal_ = concatenate(x->goal_, (*x->substitution_)(y), metaand_);
  return a;
}


const ref<alternatives> O = ref<alternatives>();
const ref<alternatives> I = ref<alternatives>(new alternatives(new alternative()));


ref_null(alternatives);

clone_source(alternatives)
copy_source(alternatives)

ref<alternatives> alternatives::label(const ref<labelstatement>& ls) {
  alternatives::iterator i, i0 = this->begin(), i1 = this->end();
  for (i = i0; i != i1; ++i)
    *i = (*i)->label(ls);
  return *this;
}

ref<alternatives> alternatives::push_back(const ref<alternative>& a) {
  alternatives_.push_back(a);
  return *this;
}

ref<alternatives> alternatives::append(const ref<alternatives>& as) {
  if (as->empty())  return *this;
  alternatives_.insert(alternatives_.end(),
    as->alternatives_.begin(), as->alternatives_.end());
  return *this;
}

ref<alternatives> operator|=(const ref<alternatives>& x, const ref<formula>& y) {
  if (x->empty())  return O;
  if (y->metaempty())  return x;
  alternatives* asp = new alternatives();
  ref<alternatives> as(asp);
  alternatives::const_iterator i0 = x->begin(), i, i1 = x->end();
  for (i = i0; i != i1; ++i)
    asp->push_back((*i) |= y);
  return as;
}

std::pair<ref<alternative>, bool> alternatives::solution() const {
  typedef std::pair<ref<alternative>, bool> pair;
  alternatives::const_iterator i, i0 = this->begin(), i1 = this->end();
  for (i = i0; i != i1; ++i) {
    ref<alternative> a = *i;
    if (a->goal_->metaempty())
      return pair(a, true);
  }
  return pair((alternative*)0, false);
}

ref<alternatives> alternatives::solutions(std::list<ref<proof> >& pfs, const ref<proof>& pf) const {
  typedef std::pair<ref<alternatives>, ref<alternatives> > pair;
  alternatives* asp = new alternatives();
  ref<alternatives> as(asp);
  alternatives::const_iterator i, i0 = this->begin(), i1 = this->end();
  for (i = i0; i != i1; ++i) {
    ref<alternative> a = *i;
    if (a->goal_->metaempty())
      pfs.push_back(pf->push_back(a));
    else
      asp->push_back(a);
  }
  return asp->empty()? O : as;
}

struct metaand_size_class {
  bool operator()(const ref<alternative>& x, const ref<alternative>& y) {
    return (x->metasize() < y->metasize());
  }
};

void alternatives::metaand_sort() {
  alternatives_.sort(metaand_size_class());
}

ref<alternatives> alternatives::unify(const ref<formula>& x, unify_environment tx, const ref<formula>& y, unify_environment ty, database* dbp, level lv, sublevel& sl, direction dr) const {
  if (empty())  return O;
  alternatives* asp = new alternatives();
  ref<alternatives> as(asp);
  alternatives::const_iterator i, i0 = this->begin(), i1 = this->end();
  for (i = i0; i != i1; ++i) {
    ref<substitution> s = (*i)->substitution_;
    ref<alternatives> bs = mli::unify(
      x->substitute(s, tx), tx, y->substitute(s, ty), ty, dbp, lv, sl, dr);
    asp->append(bs + *i);
  }
  return (as->empty())? O : as;
}

ref<alternatives> alternatives::unify_binder(
    const ref<formula>& x, unify_environment tx,
    const ref<formula>& y, unify_environment ty,
    database* dbp, level lv, sublevel& sl, direction dr) const {
  if (empty())  return O;
  alternatives* asp = new alternatives();
  ref<alternatives> as(asp);
  alternatives::const_iterator i, i0 = this->begin(), i1 = this->end();
  for (i = i0; i != i1; ++i) {
    ref<substitution> s = (*i)->substitution_;
    ref<alternatives> bs = mli::unify(
      x->substitute(s, tx), tx, y->substitute(s, ty), ty, dbp, lv, sl, dr);
    // Only add the condition here, not the substitution, as the bound
    // variables do not unify themselves:
    asp->append(bs + (*i)->goal_);
  }
  return (as->empty())? O : as;
}

ref<alternatives> alternatives::unifier(const ref<formula>& x) const {
  if (empty())  return O;
  alternatives* asp = new alternatives();
  ref<alternatives> as(asp);
  alternatives::const_iterator i, i0 = this->begin(), i1 = this->end();
  for (i = i0; i != i1; ++i) {
    ref<alternative> a = i->clone();
    a->unifier_ = (*(*i)->substitution_)(x);
    asp->push_back(a);
  }
  return (as->empty())? O : as;
}

ref<alternatives> alternatives::unify(unify_environment tt, const ref<formula>& y, unify_environment ty, database* dbp, level lv, sublevel& sl) const {
  if (empty())  return O;
  alternatives* asp = new alternatives();
  ref<alternatives> as(asp);
  alternatives::const_iterator i, i0 = this->begin(), i1 = this->end();
  for (i = i0; i != i1; ++i)
    asp->append(mli::unify((*i)->unifier_, tt, (*(*i)->substitution_)(y), ty, dbp, lv, sl) + *i);
  return (as->empty())? O : as;
}

void alternatives::write(std::ostream& os, write_style ws) const {
  if (empty()) { os << "\n    no solutions."; return; }
  const_iterator i0 = begin(), i, i1 = end();
  for (i = i0; i != i1; ++i) {
    if ((*i)->labelstatements_.empty()) {
      if (i == i0)  os << "\n    ";
      else          os << "\n  & ";
    } else {
      if (i == i0)  os << "\n";
      else          os << "\n &\n";
    }
    (*i)->write(os, ws);
  }
}


ref_null(alternatives_null);

clone_source(alternatives_null)
copy_source(alternatives_null)

ref<alternatives> alternatives_null::push_back(const ref<alternative>& a) {
  alternatives* asp = new alternatives();
  ref<alternatives> as(asp);
  asp->push_back(a);
  return as;
}

ref<alternatives> alternatives_null::append(const ref<alternatives>& as) {
  if (as->empty())  return (alternatives*)0;
  alternatives* rasp = new alternatives();
  ref<alternatives> ras(rasp);
  rasp->append(as);
  return ras;
}


// Extract the sequence of y, and prepend it to the sequence of
// each alternative of x:
ref<alternatives> operator+(const ref<alternatives>& x, const ref<formula>& y) {
  if (x->empty())  return O;
  if (y.is_null())  return x;
  alternatives* asp = new alternatives();
  ref<alternatives> as(asp);
  const alternatives* xs = cast_pointer<alternatives>(x);
  alternatives::const_iterator i0 = xs->begin(), i, i1 = xs->end();
  for (i = i0; i != i1; ++i)
    asp->push_back(*i + y);
  return as;
}


ref<alternatives> operator+(const ref<alternatives>& x, const ref<alternative>& y) {
  if (x->empty())  return O;
  alternatives* asp = new alternatives();
  ref<alternatives> as(asp);
  const alternatives* xs = cast_pointer<alternatives>(x);
  alternatives::const_iterator i0 = xs->begin(), i, i1 = xs->end();
  for (i = i0; i != i1; ++i)
    asp->push_back(*i + y);
  return as;
}


ref<alternatives> operator+(const ref<alternatives>& x, const ref<alternatives>& y) {
  if (x->empty() || y->empty())  return O;
  alternatives* asp = new alternatives();
  ref<alternatives> as(asp);
  const alternatives* xs = cast_pointer<alternatives>(x);
  alternatives::const_iterator i0 = xs->begin(), i, i1 = xs->end();
  const alternatives* ys = cast_pointer<alternatives>(y);
  alternatives::const_iterator j0 = ys->begin(), j, j1 = ys->end();
  for (i = i0; i != i1; ++i)
    for (j = j0; j != j1; ++j)
      asp->push_back(*i + *j);
  return as;
}

ref<alternatives> operator*(const ref<alternatives>& x, const ref<alternatives>& y) {
  if (x->empty() || y->empty())  return O;
  alternatives* asp = new alternatives();
  ref<alternatives> as(asp);
  const alternatives* xs = cast_pointer<alternatives>(x);
  alternatives::const_iterator i0 = xs->begin(), i, i1 = xs->end();
  const alternatives* ys = cast_pointer<alternatives>(y);
  alternatives::const_iterator j0 = ys->begin(), j, j1 = ys->end();
  for (i = i0; i != i1; ++i)
    for (j = j0; j != j1; ++j)
      asp->push_back(*i * *j);
  return as;
}


ref_null(proof);

clone_source(proof)
copy_source(proof)

void proof::push_front(const ref<alternative>& a) {
  proof_.push_front(a);
}

ref<proof> proof::push_back(const ref<alternative>& a) const {
  proof* pp = this->clone();
  ref<proof> rp(pp);
  pp->proof_.push_back(a);
  return rp;
}

void proof::write(std::ostream& os, write_style ws) const {
  os << "Proof of\n  " << goal_ << "\n";
  const_iterator i, i0 = proof_.begin(), i1 = proof_.end();
  if (i0 == i1 || !proof_.back()->goal_->metaempty()) {
    // Empty proof or last alternative has non-metaempty goal:
    os << "failed." << std::endl;
    return;
  }
  os << "succeeded:\n  ";
  for (i = i0; i != i1; ++i) {
    if (i != i0)  os << "; ";
    (*i)->write(os, write_name);
  }
  os << ".\n";
  for (i = i0; i != i1; ++i) {
    (*i)->write(os, ws);
    os << "\n";
  }
  os << "∎" << std::endl;
}


void subformulas::write(std::ostream& os, write_style ws) const {
  const_iterator i, i0 = begin(), i1 = end();
  os << "~{";
  for (i = i0; i != i1; ++i) {
    if (i != i0)
      os << ", ";
    (*i)->write(os, ws);
  }  
  os << "}";
}

void split_formula::write(std::ostream& os, write_style ws) const {
  const_iterator i, i0 = begin(), i1 = end();
  for (i = i0; i != i1; ++i) {
    os << "-- formula split: ";
    i->second->write(os, ws);
    os << "\n   ";
    i->first.write(os, ws);
    os << ".\n";
  }
}


} // namespace mli
