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

#include "MLI.hh"

#include <cctype>
#include <cstring>
#include <iostream>
#include <sstream>

#include "definition.hh"
#include "metacondition.hh"
#include "substitution.hh"

#include "precedence.hh"


namespace mli {

const kleenean undecidable = kleenean(-1);

const kleenean fail = kleenean(0);
const kleenean succeed = kleenean(1);

trace_type trace_value;

size_type level_max = 100;
size_type unify_count = 0;
size_type unify_count_max = 10000;


  ref<formula> concatenate(const ref<formula>& x, const ref<formula>& y, sequence_type t);
  
argument_precedence operator_precedence::first_argument() const {
  return argument_precedence(
    precedence_, associativity_, fixity_, argument_precedence::first_);
}
   
argument_precedence operator_precedence::middle_argument() const {
  return argument_precedence(
    precedence_, associativity_, fixity_, argument_precedence::middle_);
}
   
argument_precedence operator_precedence::last_argument() const {
  return argument_precedence(
    precedence_, associativity_, fixity_, argument_precedence::last_);
}

  // x < y if x as argument of y requires grouping like "()", "{}", etc., in writeout.
bool operator<(const operator_precedence& x, const argument_precedence& y) {
  if (y.where_ == argument_precedence::first_) {
    if (x.fixity_ == precedence_root::suffix || x.fixity_ == precedence_root::enfix
     || y.fixity_ == precedence_root::prefix || y.fixity_ == precedence_root::enfix)
      return false; // Last argument of x or first of y is delimited.
    if (x.precedence_ < y.precedence_)  return true;
    if (x.precedence_ > y.precedence_)  return false;
    // Now precedences of x and y are equal, x has no suffix and y no prefix
    // components; so associativity will decide:
    if (y.associativity_ == precedence_root::left)
      return false;
    return true;
  }
  if (y.where_ == argument_precedence::middle_) {
    // In a middle argument, only enfix operators of < precedence need no bracketing. 
    if (x.fixity_ == precedence_root::enfix)
      return false; // Argument of x is delimited.
    if (x.precedence_ <= y.precedence_)  return true;
    return false;
  }
  if (y.where_ == argument_precedence::last_) {
    if (x.fixity_ == precedence_root::prefix || x.fixity_ == precedence_root::enfix
     || y.fixity_ == precedence_root::suffix || y.fixity_ == precedence_root::enfix)
      return false; // First argument of x or last of y is delimited.
    if (x.precedence_ < y.precedence_)  return true;
    if (x.precedence_ > y.precedence_)  return false;
    // Now precedences of x and y are equal, x has no suffix and y no prefix
    // components; so associativity will decide:
    if (y.associativity_ == precedence_root::right)
      return false;
    return true;
  }
  return false;
}


ref_null(object);

clone_source(object)
copy_source(object)


ref_null(formula);

ref<formula> formula::set_bind() {
  bind b = 0;
  name_variable_table vt;
  this->set_bind(b, vt);
  return *this;
}

bool formula::contains(std::set<ref<variable> >& s, occurrence oc) const {
  std::set<ref<variable> > bs;
  bool more = false;  contains(s, bs, more, oc);  return more;
}

kleenean formula::free_for(const ref<formula>& f, const ref<variable>& x) const {
  // Only metaobject variables can pose a substitution problem, as object variables
  // are only substituted at free occurances:
  const variable* xp = (const variable*)x;
  if (xp == 0 || !xp->is_metaobject())  return true;
  std::set<ref<variable> > s; // Free variables of f.
  // If *this is without bound occurances of x, then f is free for x in *this:
  kleenean mb = has(x, bound_occurrence);
  if (mb == fail)
    return true;
  // Find free variable occurrences in f; which are the variables that might
  // become bound by a substitution at x in *this: 
  bool more = f->contains(s, free_occurrence);
  if (more)             // A later substition of f may give it more variables
    return undecidable; // that then might become bound.
  // If f has no free variables, then no such variables can become bound either,
  // so f is free for x in *this:
  if (s.empty())
    return true;
  std::list<ref<variable> > bs; // Bound variables currently in scope.
  return this->free_for(f, x, s, bs);
}

split_formula formula::split(unify_environment tg,
    const ref<variable>& x, const ref<formula>& t, unify_environment tt, database* dbp, level lv, sublevel& sl, direction dr) const {
  split_formula sf(*this);
  // If t and *this unify, then *this can be replaced by x:
  ref<alternatives> as = mli::unify(t, tt, *this, tg, dbp, lv, sl, dr);
  if (trace_value & trace_unify)
    std::clog << "formula::split:\n  "
      << "split(" << *this << "), replacement " << x << ", condition " << t << ":" 
      << as << std::endl;
  if (!as->empty())
    sf.push_back(*this, ref<formula>(x));
  return sf;
}

ref<alternatives> formula::unify_inference(const ref<formula>& head, unify_environment tt, const ref<formula>& y, unify_environment ty, database* dbp, level lv, sublevel& sl, direction dr) const {
  /* Write B := *this, A := head, x := (A |- B), u := unify, and when y is an
     inference, write y := (C |- D). Solutions:
  1. u(B, D)*u(A, C). Unify x and y as objects.
  2. u(B, D), use the A/C that is a goal as premise in this unification.
     In result, add the A/C that is a goal (resp. choice) as premise (resp. condition).
  3.a. B is an inference.
     u(B, y), if x is a goal, use A as a premise.
     In result, if A is a goal (resp. choice), add it as premise (resp. condition).
  3.b. D is an inference.
     u(x, D), if y is a goal, use C as a premise.
     In result, if C is a goal (resp. choice), add it as premise (resp. condition).
  The cases 2, 3 cam be handled by unnesting x, and let recursive calls do the rest
  (including argument reversal in pre_unify.
  */
  ref<alternatives> as, bs;
  if (tt.target_ == goal) {
    // The body should be used as a premise. This can be achieved using a
    // metaand (resp. metaor) sequence added to y is y is a choice (resp. goal).
    ref<formula> f = concatenate(*this, y, (ty.target_ == goal)? metaor_ : metaand_);
    bs = mli::unify(head, tt, f, ty, dbp, lv, sl, dr);
    // The body should be retained as a premise:
    as = as->append(bs |= *this);
  } else {
    // f is a choice, so:
    //   A |- u(B, y).
    ref<alternatives> bs = mli::unify(head, tt, y, ty, dbp, lv, sl, dr);
    if (bs->empty())  return O;
  // Here: if (A |- B) is Gen, attach the variable bound in proof to bs:
    as = as->append(bs + *this);
  }
  // Now, treat case 1 above:
  const inference* yp = cast_pointer<inference>(y);
  if (yp == 0)  return as;
  bs = mli::unify(head, tt, yp->head_, ty, dbp, lv, sl, dr);  // Heads.
  // Bodies: Will behave as if goal/choice are reversed.
  bs = bs->unify(*this, !tt, yp->body_, !ty, dbp, lv, sl, dr);
  as = as->append(bs);
  return as;
}


clone_source(formula_null)
copy_source(formula_null)

ref<alternatives> formula_null::unify(unify_environment, const ref<formula>& f, unify_environment, database*, level, sublevel&, direction) const {
  return (f.is_null())? I : O;
}

ref<formula> formula_null::substitute(const ref<substitution>&, substitute_environment) const {
  return (formula*)0;
}

relation formula_null::compare(const formula& x) const {
  return (typeid(*this) == typeid(x))? equal : unrelated;
}

relation formula_null::total(const formula& x) const {
  if (typeid(*this) != typeid(x))
    throw runtime_error("In \"formula\", total order error.");
  return equal;
}

std::ostream& write_unify(std::ostream& os, const char* name, const ref<formula>& x, unify_environment tx, const ref<formula>& y, unify_environment ty, database* dbp, direction dr) {
  if (name != 0)  os << name;
  os << "unify( ";
  os << ((dr == forward)? "[forward]" : "[reverse]");
  if (dbp != 0) {
    os << " by ";
    dbp->write(os, write_style(write_name | write_type));
  }
  os << "\n";
  if (dr == forward)
    os
     << (tx.target_? "choice  " : "goal    ") << x << ";\n"
     << (ty.target_? "choice  " : "goal    ") << y << ")";
  else
    os
     << (ty.target_? "choice  " : "goal    ") << y << ";\n"
     << (tx.target_? "choice  " : "goal    ") << x << ")";
  return os;
}


// Sort out directions and unnest definitions:
ref<alternatives> unify(const ref<formula>& x, unify_environment tx, const ref<formula>& y, unify_environment ty, database* dbp, level lv, sublevel& sl, direction dr) {
  if (trace_value & trace_unify)
    write_unify(std::clog, "mli::", x, tx, y, ty, dbp, dr) << std::endl;
  if (unify_count_max != 0 && ++unify_count > unify_count_max)
    throw std::runtime_error("Too many calls to unify.");
  ref<alternatives> as;
  // Unify without definitions expansion:
  if (dr == forward)
    as = pre_unify(x, tx, y, ty, dbp, lv, sl, forward);
  else
    as = pre_unify(y, ty, x, tx, dbp, lv, sl, forward);
  // Unify only when definitions can be expanded in formula argument x:
  if (dbp != 0 && dbp->has_definition(lv)) {
    if (dr == forward)
      as = as->append(dbp->unify_x1(x, tx, y, ty, dbp, lv, sl));
    else
      as = as->append(dbp->unify_x2(y, ty, x, tx, dbp, lv, sl));
  // Unify only when definitions can be expanded in formula argument y:
    if (dr == forward)
      as = as->append(dbp->unify_x2(x, tx, y, ty, dbp, lv, sl));
    else
      as = as->append(dbp->unify_x1(y, ty, x, tx, dbp, lv, sl));
  }
  if (trace_value & trace_unify)
    write_unify(std::clog, "mli::", x, tx, y, ty, dbp, dr) << as << std::endl;
  return as;
}


ref<alternatives> pre_unify(const ref<formula>& x, unify_environment tx, const ref<formula>& y, unify_environment ty, database* dbp, level lv, sublevel& sl, direction dr) {
  if (x.is_null() && y.is_null())  return I;
  if (x.is_null() || y.is_null())  return O;

  ref<alternatives> as, bs;

  const sequence* sp1 = cast_pointer<sequence>(x);
  const sequence* sp2 = cast_pointer<sequence>(y);

  const database* dp1 = cast_pointer<database>(x);
  const database* dp2 = cast_pointer<database>(y);

  // The case when y is a database and x behaves as a metaor is excluded here, as
  // is will be handled below. As, currently, databases are always choice, paired
  // with a goal, a check for metaor type without target type suffices.
  if (!(dp2 != 0 && sp1 != 0 && (sp1->type_ == metaor_))) {
    bs = x->unify(tx, y, ty, dbp, lv, sl, dr);
    as = as->append(bs);
  }

  if (trace_value & trace_unify)
    write_unify(std::clog, "pre_", x, tx, y, ty, dbp, dr) << bs << std::endl;

  // Here, those objects should be listed that may unify against objects of a
  // different type, to make sure that these unifications take place:

  const inference* ip1 = cast_pointer<inference>(x);
  const inference* ip2 = cast_pointer<inference>(y);
  // If (ip1 != 0), then inference::unify has already been called above. 
  if (ip1 == 0 && ip2 != 0) {
    bs = ip2->unify(ty, x, tx, dbp, lv, sl, !dr);
    as = as->append(bs);
  }

  if (sp1 == 0 && sp2 != 0 && (sp2->type_ == metaand_ || sp2->type_ == metaor_)) {
    bs = sp2->unify(ty, x, tx, dbp, lv, sl, !dr);
    as = as->append(bs);
  }

  // A database has only sporadically the ability to unwind the inference and
  // metaand objects, so this unification is put onto the latter classes instead.
  // By contrast, an object behaving as metaor must be handled by the database classes,
  // as sometimes the such an expression must be matched in full. As, currently, databases are always choice, paired
  // with a goal, a check for metaand type without target type suffices.
  if (dp2 != 0 && dp1 == 0
    && (sp1 == 0 || !(sp1->type_ == metaand_))) {
    bs = dp2->unify(ty, x, tx, dbp, lv, sl, !dr);
    as = as->append(bs);
  }

  const variable* vp1 = cast_pointer<variable>(x);
  const variable* vp2 = cast_pointer<variable>(y);
  // If (vp1 != 0) then variable::unify has already been called above.
  if (vp1 == 0 && vp2 != 0) {
    bs = vp2->unify(ty, x, tx, dbp, lv, sl, !dr);
    as = as->append(bs);
  }

  const substitution_formula* sfp2 = cast_pointer<substitution_formula>(y);
  if (sfp2 != 0) {
    bs = sfp2->unify(ty, x, tx, dbp, lv, sl, !dr);
    as = as->append(bs);
  }

  return as;
}

ref<alternatives> unify(const std::list<ref<formula> >& xs, database* dbxs, level lv, sublevel& sl) {
  switch (xs.size()) {
    case 0:
      return O;
    case 1:
      return ref<alternatives>(new alternatives(xs.front()));
    case 2: {
      ref<formula> a = xs.front();
      ref<formula> b = xs.back();
      return unify(a, goal, b, goal, dbxs, lv, sl)->unifier(a);
    }
    default:
      ;
  }
  // Size >= 3.
  ref<formula> y = xs.back();
  std::list<ref<formula> > ys;
  ys.insert(ys.end(), xs.begin(), --xs.end());
  ref<alternatives> as = unify(ys, dbxs, lv, sl);
  if (as->empty())  return O;
  return as->unify(goal, y, goal, dbxs, lv, sl);
}

ref<alternatives> unify(const ref<formula>& x, const std::list<ref<formula> >& xs, database* dbp, level lv, sublevel& sl) {
  std::list<ref<formula> > ys = xs;
  ys.push_front(x);
  return mli::unify(ys, dbp, lv, sl);
}


split_formula split(const ref<formula>& f, unify_environment tf,
    const ref<variable>& x, const ref<formula>& t, unify_environment tt, database* dbp, level lv, sublevel& sl, direction dr) {
  return f->split(tf, x, t, tt, dbp, lv, sl, dr);
}


ref_null(labelstatement);

clone_source(labelstatement)
copy_source(labelstatement)

ref<labelstatement> labelstatement::set_bind() {
  bind b = 0; name_variable_table vt; this->set_bind(b, vt);
  return *this;
}

ref<alternatives> labelstatement::unify(unify_environment, const ref<formula>&, unify_environment, database*, level, sublevel&, direction) const {
  return O;
}

ref<formula> labelstatement::substitute(const ref<substitution>&, substitute_environment) const {
  return *this;
}


clone_source(named_statement)
copy_source(named_statement)

ref<alternatives> named_statement::unify(unify_environment, const ref<formula>&, unify_environment, database*, level, sublevel&, direction) const {
  return O;
}

ref<formula> named_statement::rename(level lv, sublevel sl) const {
  named_statement* rp = this->clone();
  ref<formula> rt(rp);
  rp->statement_ = statement_->rename(lv, sl);
  return rt;
}

ref<formula> named_statement::substitute(const ref<substitution>& s, substitute_environment vt) const {
  named_statement* rp = this->clone();
  ref<formula> rt(rp);
  rp->statement_ = statement_->substitute(s, vt);
  return rt;
}

void named_statement::set_bind(bind& b, name_variable_table& vs) {
  statement_->set_bind(b, vs);
}


ref_null(variable);

clone_source(variable)
copy_source(variable)

std::string variable::type_name(type t) {
  std::string s;
  switch (t) {
    case none_:           s += "none";  break;
    case metaformula_:    s += "metaformula";  break;
    case metapredicate_:  s += "metapredicate";  break;
    case formula_:        s += "formula";  break;
    case predicate_:      s += "predicate";  break;
    case atom_:           s += "atom";  break;
    case term_:           s += "term";  break;
    case function_:       s += "function";  break;
    case constant_:       s += "constant";  break;
    case metaobject_:     s += "metaobject";  break;
    case object_:         s += "object";
    default:              s += "other";  break;
  }
  return s;
}

bool variable::may_contain(const ref<variable>& v) const {
/* Indicates whether (writing A := *this) explicit A[v, ...]
   cannot immediately be simplified to A, i.e., whether
       A                   may after substitution contain:
   metaformula_:           metapredicate_, formula_ & what formula_ may contain.
   formula_:               predicate_, atom_ & what term_ may contain.
   atom_:                  no variables.
   term_:                  function_, constant_, metaobject_, object_.
   metapredicate_, predicate_, function_:
                           no variables (can only be substituted to variables
                           of the same type).
   constant_:              no variables.
   metaobject_:            object_
   object_:                no variables.
*/
  const variable* vp = cast_pointer<variable>(v);
  if (vp == 0)  return false;
  if (type_ == none_ || vp->type_ == none_)  return false;
  type vt = vp->type_;;
  switch (type_) {
    case metapredicate_:
    case predicate_:
    case function_:
    case constant_:
      return false;
    // Note: No break below!
    case metaformula_:
      if (vt == formula_ || vt == predicate_ || vt == atom_)  return true;
    case formula_:
      if (vt == term_)  return true;
    case term_:
      if (vt == constant_)  return true;
    default:
      if (type_ == object_)  return false;
      if (type_ == metaobject_) {
        return (vt == object_);
      }
      return (vt == metaobject_) || (vt == object_);
  }
}


  // Cases of variable of type x & variable of type y it specializes,
  // via substitution (i.e. [x.y] is legal), to:
  // metaformula_: metaformula_, formula_, predicate_, atom_.
  // metapredicate_: metapredicate_.
  // formula_: formula_, predicate_, atom_.
  // predicate_: predicate_
  // atom_: atom_
  // term_: term_, constant_, metaobject_, object_.
  // function_: function_
  // constant_: constant_
  // metaobject_: metaobject_, object_.
  // object_: object_
bool variable::is_specializable_to(type x, type y) {
  switch (x) {
    case metaformula_:    return y == metaformula_ || y == formula_ || y == predicate_ || y == atom_;
    case metapredicate_:  return y == metapredicate_;
    case formula_:        return y == formula_ || y == predicate_ || y == atom_;
    case predicate_:      return y == predicate_;
    case atom_:           return y == atom_;
    case term_:           return y >= term_ && y != function_;
    case function_:       return y == function_;
    case constant_:       return y == constant_;
    case metaobject_:     return y == metaobject_ || y == object_;
    case object_:         return y == object_;
    default:
      return false;
  }
}

bool variable::is_metaobject() const { return type_ == metaobject_; }

bool variable::represents_object_variable() const {
  return (type_ == metaobject_) || (type_ == object_);
}

bool variable::is_meta() const {
  return type_ <= metaobject_;
}

bool variable::is_object() const {
  return type_ == object_;
}

bool variable::is_metaformula() const {
  return type_ == metaformula_;
}

bool variable::is_formula() const {
  return type_ == formula_ || type_ == predicate_ || type_ == atom_;
}

bool variable::is_term() const {
  return type_ >= term_;
}

bool variable::is_unspecializable() const { return unspecializable_; }
bool variable::get_depth() const { return depth_; }


template<class A>
inline A& log_unify(A& x) {
  if (trace_value & trace_unify)  std::clog << x << std::endl;
  return x;
}
template<class A>
inline const A& log_unify(const A& x) {
  if (trace_value & trace_unify)  std::clog << x << std::endl;
  return x;
}


ref<alternatives> variable::unify(unify_environment tt, const ref<formula>& f, unify_environment tf, database* dbp, level lv, sublevel& sl, direction dr) const {
  if (trace_value & trace_unify)
    std::clog << "variable::unify("
      << *this << ", " << f << "): " << std::flush;
  ref<alternatives> as; // Return value.
  const variable* vp = cast_pointer<variable>(f);
  if (vp == 0) {
    // Case: f is not a variable. Cases of *this variable type & conditions:
    // type_                                      formula_type(f)
    // metaformula_, metapredicate_               metaformula_
    // formula_, predicate_, atom_:               formula_
    // term_, function_, metaobject_, constant_:  term_
    // object_ variables do not unify with f.
    // *this must be specializable and one must have free_in(f) == false.
    if (represents_object_variable())  return log_unify(O);
    if (is_unspecializable())  return log_unify(O);
    // Type check cuts down alternatives in unify([x\t]A, B):
    if (f->get_formula_type() != get_formula_type()) {
      if (trace_value & trace_unify)  std::clog << "type mismatch " << std::flush;
      return log_unify(O);
    }
    kleenean mb = free_in(f);
    if (mb == succeed)  return log_unify(O);
    ref<alternatives> bs(new alternatives(free_occurrences_substitution(*this, f)));
    // When undecidable, should return special free_occurrences_substitution requiring variables
    // to not be free:
    if (mb == undecidable) {
      ref<variable> v(*this);
      ref<formula> not_free = new free_in_object(v, f, false);
      return log_unify(bs + not_free);
    }
    return log_unify(bs);
  }
  // Case: f is a variable (vp != 0).
  if (*this == *vp)
    return log_unify(I);
  if (is_unspecializable() && vp->is_unspecializable()) {
#if 1
    if (tt.table_ == 0 || tf.table_ == 0)
      return log_unify(O);  // *this or f not bound; cannot ensure identity substitution.
    maybe<ref<formula> > mf1 = tt.table_->find(*this);
    if (!mf1)
      return log_unify(O);  // *this not bound; cannot ensure identity substitution.
    maybe<ref<formula> > mf2 = tf.table_->find(*this);
    if (!mf2)
      return log_unify(O);  // f not bound; cannot ensure identity substitution.
    // Both arguments bound variables:
    bound_formula* bf1p = cast_pointer<bound_formula>(*mf1);
    if (bf1p == 0)  throw runtime_error("In variable::unify, null bound_formula.");
    bind b1 = bf1p->bind_;
    return log_unify(ref<alternatives>(new alternatives(local_substitution(*this, *vp, b1))));
#else
# if 0
    // For fixed variables:
    if (is_bound() && vp->is_bound() && (*this == *vp))
      return log_unify(ref<alternatives>(new alternatives(all_occurrences_substitution(*this, *vp))));
# else
    // For alpha-movable variables:
    if (is_bound() && vp->is_bound())
      return log_unify(ref<alternatives>(new alternatives(all_occurrences_substitution(*this, *vp))));
# endif
    return log_unify(O);  // Cannot ensure identity substitution.
#endif
  }
  if (is_unspecializable())
    // If *this is unspecializable, switch unify() arguments and make a new try:
    return vp->unify(tf, *this, tt, dbp, lv, sl, !dr);
  // A metaobjectvariable can specialize to a term variable under the condition
  // that the term variable later is substituted by an object variable:
  if (is_metaobject() && (vp->type_ == term_)) {
    return log_unify(ref<alternatives>(new alternatives(
      free_occurrences_substitution(*vp, *this))));
  }
  if ((type_ == term_) && vp->is_metaobject()) {
    return log_unify(ref<alternatives>(new alternatives(
      free_occurrences_substitution(*this, *vp))));
  }
  if (is_specializable_to(type_, vp->type_)) {
    if (is_metaobject()) {
      if (tt.is_generalization_) {
        alternative* ap = new alternative(all_occurrences_substitution(*this, *vp));
        ref<alternative> a(ap);
        ap->bound_in_proof_.insert(*vp);
        return log_unify(ref<alternatives>(new alternatives(a)));
      }
      else
        return log_unify(ref<alternatives>(new alternatives(all_occurrences_substitution(*this, *vp))));
    }
#if 1
    if (tt.table_ == 0 || tf.table_ == 0) // *this or f not bound.
      return log_unify(ref<alternatives>(new alternatives(free_occurrences_substitution(*this, f))));
    maybe<ref<formula> > mf1 = tt.table_->find(*this);
    maybe<ref<formula> > mf2 = tf.table_->find(*vp);
    if (!mf1 || !mf2) // *this or f not bound.
      // Can probably make an all_occurrences_substitution also for free variables,
      // if variable_substitution::operator() checks the bind numbers, as these will
      // be different from zero in bound occurences. Thus, it automatically becomes a
      // free_occurrences_substitution.
      return log_unify(ref<alternatives>(new alternatives(free_occurrences_substitution(*this, f))));
    bound_formula* bf1p = cast_pointer<bound_formula>(*mf1);
    if (bf1p == 0)  throw runtime_error("In variable::unify, null bound_formula.");
    bind b1 = bf1p->bind_;
    return log_unify(ref<alternatives>(new alternatives(local_substitution(*this, *vp, b1))));
#else
    else 
    if (is_bound())
      return log_unify(ref<alternatives>(new alternatives(all_occurrences_substitution(*this, *vp))));  
    else
      // Can probably make an all_occurrences_substitution also for free variables,
      // if variable_substitution::operator() checks the bind numbers, as these will
      // be different from zero in bound occurences. Thus, it automatically becomes a
      // free_occurrences_substitution.
      return log_unify(ref<alternatives>(new alternatives(free_occurrences_substitution(*this, f))));
#endif
  }
  if (is_specializable_to(vp->type_, type_) && !vp->is_unspecializable())
    return vp->unify(tf, *this, tt, dbp, lv, sl, !dr);
  // may_contain() stuff
  return log_unify(O);
}

ref<alternatives> unify_bound1(
    const ref<variable>&, unify_environment, const ref<formula>&,
    const ref<variable>&, unify_environment, const ref<formula>&,
    database*, level, sublevel&, direction);

// Unify bound variables: Assumes both x and y are bound.
ref<alternatives> unify_bound(
    const ref<variable>& x, unify_environment tx, const ref<formula>& fx,
    const ref<variable>& y, unify_environment ty, const ref<formula>& fy,
    database* dbp, level lv, sublevel& sl, direction dr) {
  if (trace_value & trace_unify)
    write_unify(std::clog, "mli::bound_", ref<formula>(x), tx, ref<formula>(y), ty, dbp, dr) << std::endl;
  // Check if x, y are unifiable. If so, add to the unifying substitution free(fx) if x
  // is the mapped variable, or free(fy) if y.

  // Unspecializable bound variables can unify, except when in the case of an unspecializable
  // metaobject variable that should be specialized to an object variable:
  if ((x->is_metaobject() && x->is_unspecializable() && y->is_object())
    || (y->is_metaobject() && y->is_unspecializable() && x->is_object()))
    return O;

  if ((x->is_unspecializable() && !y->is_unspecializable())
    || (x->is_object() && y->is_metaobject()))
    return unify_bound1(y, ty, fy, x, tx, fx, dbp, lv, sl, !dr);
  return unify_bound1(x, tx, fx, y, ty, fy, dbp, lv, sl, dr);
}

// Assumes that if one of x, y is specializable, x is specializable;
// but else both x, y may be unspecializable. Also assumes that not one
// of x, y is metaobject and unspecializable and the other is object,
// and further assumes that of one of x, y is metaobject and the other object,
// x is metaobject.
ref<alternatives> unify_bound1(
    const ref<variable>& x, unify_environment tx, const ref<formula>& fx,
    const ref<variable>& y, unify_environment, const ref<formula>&,
    database*, level, sublevel&, direction) {

  // Need not check unspecializable condition. If one variable is
  // unspecializable, it will be preferred as the mapped variable, and it is x.
  // And if one is metaobject and the other is object, x is metaobject.

  bind bx;
  if (x->is_metaobject())
    bx = 0;
  else {
    if (tx.table_ == 0)
      return log_unify(O);  // x or y not bound; cannot ensure identity substitution.
    maybe<ref<formula> > mfx = tx.table_->find(x);
    if (!mfx)
      return log_unify(O);  // x not bound; cannot ensure identity substitution.
    bound_formula* bfxp = cast_pointer<bound_formula>(*mfx);
    if (bfxp == 0)  throw runtime_error("In mli::unify_bound, null bound_formula.");
    bx = bfxp->bind_;
  }
  variable_substitution* vsxp = new variable_substitution(x, ref<formula>(y), true, bx, true);
  ref<substitution> sx(vsxp);
  fx->contains(vsxp->not_free_in_, free_occurrence);
  return log_unify(ref<alternatives>(new alternatives(sx)));
}


kleenean variable::free_in(const ref<formula>& f) const {
  if (type_ == none_)  return false;
  return f->has(*this, free_occurrence);
}

kleenean variable::has(const ref<variable>& v, occurrence oc) const {
  switch (oc) {
    case any_occurrence: default:
    case declared_occurrence:
    case free_occurrence:
      if (*this == *v)
        return true;
      if (may_contain(v))
        return undecidable;
      return false;
    case bound_occurrence:
      // The bound cccurances are handled by bound_formula::has().
      return false;
  }
}

void variable::contains(std::set<ref<variable> >& s, std::set<ref<variable> >& bs, bool& more, occurrence oc) const {
  switch (oc) {
    case declared_occurrence:
      if (is_metaobject()) {
        s.insert(*this);
        return;
      }
      // Fall through here:
    case free_occurrence:
      // But do not add *this if it is bound:
      if (bs.find(*this) == bs.end()) {
        s.insert(*this);  // The occurance of *this is not bound.
        if (is_metaobject() || (type_ == metaformula_)
           || (type_ == formula_) || (type_ == term_))
          more = true;
      }
      return;
    case bound_occurrence:
      // Bound variables are handled by bound_formula::contains():
      return;
    default:
      s.insert(*this);
  }
}

kleenean variable::free_for(const ref<formula>& f, const ref<variable>& x,
  std::set<ref<variable> >& s, std::list<ref<variable> >& bs) const {
  const variable* fp = cast_pointer<variable>(f);
  ref<variable> fv(fp? fp->copy() : 0);
#if 1
  // If f has no free variables, then f free for x in *this:
  if (s.empty())
    return true;
  // If the set of free variables of f is non-empty and *this after substitution
  // may contain a bound occurrance (of same type as x) of any of them, then
  // f free for x in *this is undecidable:
  bool xb = may_contain(x);
  if (xb)
    return undecidable;
#else
  bool xb = may_contain(x);
  bool fb = fp != 0 && may_contain(fv);
  if (xb || fb) {
    if (xb) {
      // Check sublevel & depth here:
      const variable* xp = cast_pointer<variable>(x);
      if (xp == 0 || level_ != xp->level_) // If levels are distinct, *this cannot
        return false;                    // contain x, and has no substitution point.
    }
    if (fb && level_ != fp->level_) // If levels are distinct, the binders of *this
        return false;             // cannot bind any free variables of f.      
    return undecidable;
  }
#endif
  if (ref<variable>(*this) != x)
    return true; // *this is no substitution point.
  std::list<ref<variable> >::reverse_iterator i, i0 = bs.rbegin(), i1 = bs.rend();
  for (i = i0; i != i1; ++i) 
    if (s.find(*i) != s.end()) // Assumes variable comparison not using bind_.
      return false;
  return true;
}

void variable::unspecialize(depth x, bool y) {
  if (depth_ == x)  unspecializable_ = y;
}

ref<formula> variable::rename(level lv, sublevel sl) const {
  if (type_ == 0)  return (formula*)0;
  // Fixed variables will not be renumbered:
  if (is_unspecializable())
    return *this;
  variable* vp = new variable(*this);
  vp->level_ = lv;
  vp->sublevel_ = sl;
  return vp;
}

ref<formula> variable::substitute(const ref<substitution>& s, substitute_environment vt) const {
  if (type_ == none_)  return (formula*)0;
  return s->substitute_variable(*this, vt);
}

relation variable::compare(const formula& y) const {
  const variable* yp = dynamic_cast<const variable*>(&y);
  if (yp == 0)  return unrelated;
  if (depth_ != yp->depth_)
    return inequality_compare(depth_, yp->depth_);
  if (level_ != yp->level_)
    return inequality_compare(level_, yp->level_);
  if (sublevel_ != yp->sublevel_)
    return inequality_compare(sublevel_, yp->sublevel_);
  if (type_ != yp->type_)
    return inequality_compare(type_, yp->type_);
  return sgn(name.compare(yp->name));
}

relation variable::total(const formula& y) const {
  const variable* yp = dynamic_cast<const variable*>(&y);
  if (yp == 0)  throw runtime_error("In \"variable\", total order error.");
  if (depth_ != yp->depth_)
    return inequality_compare(depth_, yp->depth_);
  if (level_ != yp->level_)
    return inequality_compare(level_, yp->level_);
  if (sublevel_ != yp->sublevel_)
    return inequality_compare(sublevel_, yp->sublevel_);
  if (type_ != yp->type_)
    return inequality_compare(type_, yp->type_);
  return sgn(name.compare(yp->name));
}

void variable::write(std::ostream& os, write_style) const {
  if (unspecializable_)
    os << '\'';
  if (trace_value & trace_variable_type) {
	  switch (type_) {
	    case none_:         os << "?";  break;
	    case metaformula_:  os << "M";  break;
	    case formula_:      os << "F";  break;
	    case predicate_:    os << "P";  break;
	    case atom_:         os << "A";  break;
	    case term_:         os << "T";  break;
	    case function_:     os << "F";  break;
	    case constant_:     os << "c";  break;
	    case metaobject_:   os << "O";  break;
	    case object_:       os << "o";  break;
	    default:            os << "!";  break;
	  };
  }
  os << name;
  if (depth_ != 0)
    os << "↑" << depth_;
  if (level_ != 0 || sublevel_ != 0)
    os << "↓" << level_;
  if (sublevel_ != 0)
    os << "↓" << sublevel_;
}


void variable_list::write(std::ostream& os, write_style ws) const {
  std::list<value_type>::const_iterator i, i0 = variables_.begin(), i1 = variables_.end();
  for (i = i0; i != i1; ++i) {
    if (i != i0)  os << ", ";
      i->first->write(os, ws);
  }
}

ref<alternatives> unify(const std::list<ref<formula> >& xs, unify_environment tx,
    const std::list<ref<formula> >& ys, unify_environment ty, database* dbp, level lv, sublevel& sl, direction dr) {
  if (xs.empty() && ys.empty())  return I;
  if (xs.size() != ys.size())  return O;

  ref<alternatives> as; // The return alternatives.

  std::list<ref<formula> >::const_iterator i, i0 = xs.begin(), i1 = xs.end();
  std::list<ref<formula> >::const_iterator j = ys.begin(), j1 = ys.end();

  // Unify from beginning of list, making sure to substitute
  // found substitutions to latter components:
  for (i = i0; i != i1; ++i, ++j) {
    if (i == i0)
      as = unify(*i, tx, *j, ty, dbp, lv, sl, dr);
    else
      as = as->unify(*i, tx, *j, ty, dbp, lv, sl, dr);
    if (as->empty())  return as;
  }
  return as;
}


clone_source(constant)
copy_source(constant)

ref<alternatives> constant::unify(unify_environment, const ref<formula>& x, unify_environment, database*, level, sublevel&, direction) const {
  if (trace_value & trace_unify)
    std::clog
     << "constant::unify\n  " << *this << ";\n  " << x << ")"
     << std::endl;
  const constant* xp = cast_pointer<constant>(x);
  return (xp != 0) && (*this == *xp)? I : O;
}

inline relation compare(const constant& x, const constant& y) {
  return sgn(x.name.compare(y.name));
}

relation constant::compare(const formula& x) const {
  const constant* xp = dynamic_cast<const constant*>(&x);
  if (xp == 0)  return unrelated;
  return mli::compare(*this, *xp);
}

relation constant::total(const formula& x) const {
  const constant* xp = dynamic_cast<const constant*>(&x);
  if (xp == 0)  throw runtime_error("In \"constant\", total order error.");
  return mli::compare(*this, *xp);
}

void constant::write(std::ostream& os, write_style) const {
  if (trace_value & trace_formula_type)
    switch (type_) {
      case metaformula_type_:     os << "M"; break;
      case object_formula_type_:  os << "F"; break;
      case term_type_:            os << "T"; break;
      default:                    os << "?"; break;
    }
  os << name; 
}


clone_source(variable_list)
copy_source(variable_list)


clone_source(sequence)
copy_source(sequence)

formula_type sequence::get_formula_type() const {
  switch (type_) {
    case metapredicate_argument_:
    case metaor_:
    case metaand_:
      return metaformula_type_;
    case predicate_argument_:
      return object_formula_type_;
    case function_argument_:
    case member_list_set_:
    case implicit_set_:
    case vector_:
    case list_:
    case bracket_:
      return term_type_;
    case other_sequence_:
    default:
      return no_formula_type_;
  }
}

ref<alternatives> sequence::unify(unify_environment tt, const ref<formula>& x, unify_environment tx, database* dbp, level lv, sublevel& sl, direction dr) const {
  if (trace_value & trace_unify)
    write_unify(std::clog, "sequence::", *this, tt, x, tx, dbp, dr) << std::endl;
  if (type_ == metaand_ || type_ == metaor_) {
  // A metaand (resp. metaor) goal, will behave as such, but a metaand
  // (resp. metaor) choice will behave as the dual metaor (resp. metaand).
  // If there is a mix of an object behaving as a metand, and the other as a metaor,
  // then the metaand object must be decomposed first; otherwise, for example, the
  // statement A | B |- A | B will not be proved.
  bool this_metaand = (type_ == metaand_ && tt.target_ == goal) || (type_ == metaor_ && tt.target_ == choice);
  const sequence* sxp = cast_pointer<sequence>(x);
  bool x_metaand = (sxp != 0)
    && ((sxp->type_ == metaand_ && tx.target_ == goal) || (sxp->type_ == metaor_ && tx.target_ == choice));
  if (this_metaand) {
    ref<alternatives> as;
    std::list<ref<formula> >::const_iterator i, i0 = formulas_.begin(), i1 = formulas_.end();
    for (i = i0; i != i1; ++i) {
      if (i == i0)
        as = mli::unify((*i), tt, x, tx, dbp, lv, sl, dr);
      else
        as = as->unify((*i), tt, x, tx, dbp, lv, sl, dr);
      if (trace_value & trace_unify)
        std::clog << "unify(\n  " << (*i) << ";\n  " << x << "):" << as << std::endl;
    }
    return as;
  } else if (x_metaand)
    return sxp->unify(tx, *this, tt, dbp, lv, sl, !dr);
  if ((type_ == metaand_ && tt.target_ == choice) || (type_ == metaor_ && tt.target_ == goal)) {
    ref<alternatives> as;
    std::list<ref<formula> >::const_iterator i, i0 = formulas_.begin(), i1 = formulas_.end();
    for (i = i0; i != i1; ++i) {
      ref<alternatives> s = mli::unify((*i), tt, x, tx, dbp, lv, sl, dr);
      if (trace_value & trace_unify)
        std::clog << "unify(\n  " << (*i) << ";\n  " << x << "):" << s << std::endl;
      as = as->append(s);
    }
    return as;
  }
 }
  const sequence* xp = cast_pointer<sequence>(x);
  if (xp == 0)  return O;
  if (type_ != xp->type_)  return O;
  return mli::unify(formulas_, tt, xp->formulas_, tx, dbp, lv, sl, dr);
}


struct sequence_construct {
  sequence_type type_;

  sequence_construct(sequence_type t) : type_(t) {}

  ref<formula> operator()() const { return new sequence(type_); }

  ref<formula> operator()(const ref<formula>& x) const { return new sequence(x, type_); }

  ref<formula> operator()(const ref<formula>& x, const ref<formula>& y) const {
    const sequence* yp = cast_pointer<sequence>(y);
    if (yp == 0)  return new sequence(x, y, type_);
    std::list<ref<formula> > ls = yp->formulas_;
    ls.push_front(x);
    return new sequence(ls, type_);
  }
};


split_formula sequence::split(unify_environment tg,
  const ref<variable>& x, const ref<formula>& t, unify_environment tt, database* dbp, level lv, sublevel& sl, direction dr) const {
  split_formula sf(*this);  // Return value.
#if 0
  // If t and *this unify, then *this can be replaced by x:
  ref<alternatives> as = mli::unify(t, tt, *this, tg, dr, lv, sl, dbp);
  if (!!as)
    sf.push_back(*this, x);
#endif
  if (formulas_.empty()) {
    sf.push_back(new sequence(type_));
    return sf;
  }
  const ref<formula> f = formulas_.front();
  if (formulas_.size() == 1) {
    sf.append(mli::split(f, tg, sequence_construct(type_), x, t, tt, dbp, lv, sl, dr));
    return sf;
  }
  std::list<ref<formula> > fs = formulas_;
  fs.pop_front();
  ref<formula> g = new sequence(fs, type_);
  sf.append(mli::split(f, g, tg, sequence_construct(type_), x, t, tt, dbp, lv, sl, dr));
  return sf;
}

ref<alternatives> sequence::unify_inference(const ref<formula>& head, unify_environment tt, const ref<formula>& y, unify_environment ty, database* dbp, level lv, sublevel& sl, direction dr) const {
  if (type_ != metaor_)
    return formula::unify_inference(head, tt, y, ty, dbp, lv, sl, dr);
  ref<alternatives> as;
  std::list<ref<formula> >::const_iterator i, i0 = formulas_.begin(), i1 = formulas_.end();
  for (i = i0; i != i1; ++i) {
    if (i == i0)
      as = (*i)->unify_inference(head, tt, y, ty, dbp, lv, sl, dr);
    else
      as = as + (*i)->unify_inference(head, tt, y, ty, dbp, lv, sl, dr);
  }
  return as;
}

kleenean sequence::has(const ref<variable>& v, occurrence oc) const {
  std::list<ref<formula> >::const_iterator i = formulas_.begin(), i1 = formulas_.end();
#if 1
  kleenean kr = false;
  for (; i != i1; ++i) {
    kleenean k = (*i)->has(v, oc);
    if (k == succeed)  return true;
    kr = kr || k;
  }
  return kr;
#else
  kleenean mb;
  bool is_undecidable = false;
  for (; i != i1; ++i) {
    mb = (*i)->has(v, oc);
    if (mb == true)  return true;
    if (mb == undecidable)  is_undecidable = true;
  }
  if (is_undecidable)  return undecidable;
  return false;
#endif
}

void sequence::contains(std::set<ref<variable> >& s, std::set<ref<variable> >& bs, bool& more, occurrence oc) const {
  std::list<ref<formula> >::const_iterator i = formulas_.begin(), i1 = formulas_.end();
  for (; i != i1; ++i)
    (*i)->contains(s, bs, more, oc);
}

kleenean sequence::free_for(const ref<formula>& f, const ref<variable>& x,
  std::set<ref<variable> >& s, std::list<ref<variable> >& bs) const {
#if 1
  std::list<ref<formula> >::const_iterator i = formulas_.begin(), i1 = formulas_.end();
  kleenean kr = true;
  for (; i != i1; ++i) {
    kleenean k = (*i)->free_for(f, x, s, bs);
    if (k == fail)  return false;
    kr = kr && k;
  }
  return kr;
#else
  std::list<ref<formula> >::const_iterator i = formulas_.begin(), i1 = formulas_.end();
  kleenean mb;
  bool is_undecidable = false;
  for (; i != i1; ++i) {
    mb = (*i)->free_for(f, x, s, bs);
    if (mb == false)  return false;
    if (mb == undecidable)  is_undecidable = true;
  }
  if (is_undecidable)  return undecidable;
  return true;
#endif
}

void sequence::unspecialize(depth x, bool y) {
  std::list<ref<formula> >::iterator i = formulas_.begin(), i1 = formulas_.end();
  for (; i != i1; ++i)
    (*i)->unspecialize(x, y);
}

ref<formula> sequence::rename(level lv, sublevel sl) const {
  sequence* sp = new sequence(*this);
  ref<formula> ret = sp; // Exception safety.
  std::list<ref<formula> >::const_iterator i = formulas_.begin(), i1 = formulas_.end();
  std::list<ref<formula> >::iterator j = sp->formulas_.begin(), j1 = sp->formulas_.end();
  for (; i != i1; ++i, ++j)
    *j = (*i)->rename(lv, sl);
  return ret;
}

ref<formula> sequence::substitute(const ref<substitution>& s, substitute_environment vt) const {
  std::list<ref<formula> >::const_iterator i, i0 = formulas_.begin(), i1 = formulas_.end();
  if (type_ != metaand_ && type_ != metaor_) {
    sequence* sp = new sequence(*this);
    ref<formula> sr = sp; // Exception safety.
    std::list<ref<formula> >::iterator j = sp->formulas_.begin(), j1 = sp->formulas_.end();
    for (i = i0; i != i1; ++i, ++j)
      *j = (*i)->substitute(s, vt);
    return sr;
  }
  if (type_ == metaand_) {
    sequence* s1p = new sequence(metaand_);
    ref<formula> s1r = s1p;
    for (i = i0; i != i1; ++i) {
      ref<formula> x = (*i)->substitute(s, vt);
      kleenean sf = x->succeed_or_fail();
      if (sf == fail)  return new succeed_fail(false);
      if (sf == succeed || x->metaempty())  continue;
      s1p->formulas_.push_back(x);
    }
    return s1r;
  }
  // type_ == metaor_:
  sequence* s2p = new sequence(metaor_);
  ref<formula> s2r = s2p;
  for (i = i0; i != i1; ++i) {
    ref<formula> x = (*i)->substitute(s, vt);
    kleenean sf = x->succeed_or_fail();
    if (sf == fail)  continue;
    if (sf == succeed || x->metaempty())  return (formula*)0;
    s2p->formulas_.push_back(x);
  }
  return s2r;
}

void sequence::set_bind(bind& b, name_variable_table& vt) {
  std::list<ref<formula> >::iterator i = formulas_.begin(), i1 = formulas_.end();
  for (; i != i1; ++i)
    (*i)->set_bind(b, vt);
}

kleenean sequence::succeed_or_fail() const {
  if (type_ != metaand_)  return undecidable;
  const_iterator i = formulas_.begin(), i1 = formulas_.end();
  bool is_undecidable = false;
  for (; i != i1; ++i) {
    const kleenean k = (*i)->succeed_or_fail();
    switch ((const int)k) {
      case 0:
        return fail;
      case 1:
        break;
      case -1:
        is_undecidable = true;
        break;
      default: ;
    }
  }
  return is_undecidable? undecidable : succeed;
}

bool sequence::metaempty() const {
  if (type_ != metaand_)  return false;
  const_iterator i = formulas_.begin(), i1 = formulas_.end();
  for (; i != i1; ++i)
    if (!(*i)->metaempty())
      return false;
  return true;
}

formula::size_type sequence::metasize() const {
  if (type_ != metaand_)  return 1;
  if (formulas_.empty())  return 0;
  size_type ms = 0;
  const_iterator i = formulas_.begin(), i1 = formulas_.end();
  for (; i != i1; ++i)
    ms += (*i)->metasize();
  return ms;
}

ref<formula> sequence::metareverse() const {
  if (type_ != metaand_)  return *this;
  sequence* rsp = new sequence(metaand_);
  ref<formula> rs(rsp);
  const_iterator i, i0 = formulas_.begin(), i1 = formulas_.end();
  for (i = i0; i != i1; ++i)
    rsp->formulas_.push_front((*i)->metareverse());
  return rs;
}

relation sequence::compare(const formula& x) const {
  const sequence* xp = dynamic_cast<const sequence*>(&x);
  if (xp == 0)  return unrelated;
  if (type_ != xp->type_)  return unrelated;
  return lexical_compare(formulas_.begin(), formulas_.end(), xp->formulas_.begin(), xp->formulas_.end());
}

relation sequence::total(const formula& x) const {
  const sequence* xp = dynamic_cast<const sequence*>(&x);
  if (xp == 0)  throw runtime_error("In \"sequence\", total order error.");
  if (type_ != xp->type_)  return inequality_compare(type_, xp->type_);
  return lexical_total(formulas_.begin(), formulas_.end(), xp->formulas_.begin(), xp->formulas_.end());
}

operator_precedence sequence::precedence() const {
  switch (type_) {
    case metapredicate_argument_:
      return metapredicate_argument_oprec; 
    case metaor_:
      return metaor_oprec; 
    case metaand_:
      return metaand_oprec; 
    case predicate_argument_:
      return predicate_argument_oprec;
    case function_argument_:
      return function_argument_oprec;
    case member_list_set_:
      return member_list_set_oprec;
    case implicit_set_:
      return implicit_set_oprec;
    case vector_:
      return vector_oprec;
    case list_:
      return list_oprec;
    case bracket_:
      return bracket_oprec;
    default:
    case other_sequence_:
      return operator_precedence();
  }
}

void sequence::write(std::ostream& os, write_style ws) const {
#if 0
  os << "{"; // Debug.
#endif
  switch (type_) {
    case metapredicate_argument_: os << "("; break;
    case metaor_: break;
    case metaand_: break;
    case predicate_argument_: os << "("; break;
    case function_argument_: os << "("; break;
    case member_list_set_: os << "{"; break;
    case implicit_set_: break;
    case vector_: os << "("; break;
    case list_: os << "["; break;
    case bracket_: os << "<"; break;
    case other_sequence_:
    default: os << "(?"; break;
  }
  std::list<ref<formula> >::const_iterator i,
    i0 = formulas_.begin(), i1 = formulas_.end(), i_last = i1;
  if (!formulas_.empty())  --i_last;
  for(i = i0; i != i1; ++i) {
    if (i != i0)
    switch (type_) {
      case metapredicate_argument_:
      case metaand_:
      case predicate_argument_:
      case function_argument_:
      case member_list_set_:
      case vector_:
      case list_:
      case bracket_:
        os << ", "; break;
      case metaor_:
       os << " | "; break;
      case implicit_set_:
       os << "|"; break;
      case other_sequence_:
      default: os << ",?"; break;
    }
    ref<formula> x = *i;
    operator_precedence op = precedence();
    argument_precedence ap;
    if (i == i0)  ap = op.first_argument();
    else if (i == i_last)  ap = op.last_argument();
    else ap = op.middle_argument();
    bool do_bracket = x->precedence() < ap;
  	if (do_bracket)  os << "(";
	  x->write(os, ws);
	  if (do_bracket)  os << ")";
  }
  switch (type_) {
    case metapredicate_argument_: os << ")"; break;
    case metaor_: break;
    case metaand_: break;
    case predicate_argument_: os << ")"; break;
    case function_argument_: os << ")"; break;
    case member_list_set_: os << "}"; break;
    case implicit_set_: break;
    case vector_: os << ")"; break;
    case list_: os << "]"; break;
    case bracket_: os << ">"; break;
    case other_sequence_:
    default: os << "?)"; break;
  }
#if 0
  os << "}"; // Debug.
#endif
}

ref<formula> concatenate(const ref<formula>& x, const ref<formula>& y, sequence_type t) {
  if (y.is_null())  return x;
  if (x.is_null())  return y;
  const sequence* sp1 = cast_pointer<sequence>(x);
  const sequence* sp2 = cast_pointer<sequence>(y);
  bool b1 = (sp1 != 0) && (sp1->type_ == t);
  bool b2 = (sp2 != 0) && (sp2->type_ == t);
  if (b1 && b2)
    return new sequence(*sp1, *sp2);
  else if (b1)
    return new sequence(*sp1, y);
  else if (b2)
    return new sequence(x, *sp2);
  else
    return new sequence(x, y, t);        
}


clone_source(structure)
copy_source(structure)

void structure::push_back(const ref<formula>& x) {
  sequence* vp = cast_pointer<sequence>(argument);
  if (vp == 0) {
    std::cerr << "structure::push_back: argument not a sequence: " << argument << std::endl;
    return;
  }
  vp->push_back(x);
}

ref<alternatives> structure::unify(unify_environment tt, const ref<formula>& x, unify_environment tx, database* dbp, level lv, sublevel& sl, direction dr) const {
  if (trace_value & trace_unify)
    std::clog
     << "structure::unify(\n  " << *this << ";\n  " << x << ")" << std::endl;
  const structure* sp = cast_pointer<structure>(x);
  if (sp == 0)  return O;
  ref<alternatives> as = mli::unify(atom, tt, sp->atom, tx, dbp, lv, sl, dr);
  return as->unify(argument, tt, sp->argument, tx, dbp, lv, sl, dr);
}

struct structure_construct {
  operator_precedence precedence_;
  structure::type type_;
  structure::style style_;

  structure_construct(structure::type t, structure::style s, operator_precedence p)
   : type_(t), style_(s), precedence_(p) {}

  ref<formula> operator()(const ref<formula>& x, const ref<formula>& y) const {
    return new structure(x, y, type_, style_, precedence_);
  }
};

split_formula structure::split(unify_environment tg,
  const ref<variable>& x, const ref<formula>& t, unify_environment tt, database* dbp, level lv, sublevel& sl, direction dr) const {
  split_formula sf(*this);  // Return value.
  // If t and *this unify, then *this can be replaced by x:
  ref<alternatives> as = mli::unify(t, tt, *this, tg, dbp, lv, sl, dr); // Direction correct?
  if (!as->empty())
    sf.push_back(*this, ref<formula>(x));
  sf.append(mli::split(atom, argument, tg, structure_construct(type_, style_, precedence_), x, t, tt, dbp, lv, sl, dr));
  return sf;
}

kleenean structure::has(const ref<variable>& v, occurrence oc) const {
#if 1
  kleenean k1 = atom->has(v, oc);
  if (k1 == succeed)  return true;
  kleenean k2 = argument->has(v, oc);
  return k1 || k2;
#else
  kleenean mb;
  bool is_undecidable = false;
  mb = atom->has(v, oc);
  if (mb == true)  return true;
  if (mb == undecidable)  is_undecidable = true;
  mb = argument->has(v, oc);
  if (mb == true)  return true;
  if (mb == undecidable)  is_undecidable = true;
  if (is_undecidable)  return undecidable;
  return false;
#endif
}

void structure::contains(std::set<ref<variable> >& s, std::set<ref<variable> >& bs, bool& more, occurrence oc) const {
  atom->contains(s, bs, more, oc);
  argument->contains(s, bs, more, oc);
}

kleenean structure::free_for(const ref<formula>& f, const ref<variable>& x,
  std::set<ref<variable> >& s, std::list<ref<variable> >& bs) const {
  kleenean k1 = atom->free_for(f, x, s, bs);
  if (k1 == fail)  return false;
  kleenean k2 = argument->free_for(f, x, s, bs);
  return k1 && k2;
}

void structure::unspecialize(depth x, bool y) {
  atom->unspecialize(x, y);
  argument->unspecialize(x, y);
}

ref<formula> structure::rename(level lv, sublevel sl) const {
  return new structure(atom->rename(lv, sl), argument->rename(lv, sl),
    type_, style_, precedence_);
}

ref<formula> structure::substitute(const ref<substitution>& s, substitute_environment vt) const {
  return new structure(atom->substitute(s, vt), argument->substitute(s, vt), type_, style_, precedence_);
}

void structure::set_bind(bind& b, name_variable_table& vt) {
  atom->set_bind(b, vt);  argument->set_bind(b, vt);
}

relation structure::compare(const formula& x) const {
  const structure* xp = dynamic_cast<const structure*>(&x);
  if (xp == 0)  return unrelated;
  int c = atom->compare(*xp->atom);
  if (c != 0)  return c;
  return argument->compare(*xp->argument);
}

relation structure::total(const formula& x) const {
  const structure* xp = dynamic_cast<const structure*>(&x);
  if (xp == 0)  throw runtime_error("In \"structure\", total order error.");
  int c = atom->total(*xp->atom);
  if (c != 0)  return c;
  return argument->total(*xp->argument);
}

int structure::arity() const {
  const sequence* vp = cast_pointer<sequence>(argument);
  if (vp == 0)  return 0;
  if (vp->type_ != predicate_argument_)  return 1;
  return vp->formulas_.size();
}

void write_structure_type(std::ostream& os, structure::type t) {
  switch (t) {
    case structure::metapredicate:  os << "∏"; break;
    case structure::metalogic:      os << "‡"; break;
    case structure::logic:          os << "†"; break;
    case structure::predicate:      os << "π"; break;
    case structure::function:       os << "ƒ"; break;
    default:                        os << "?"; break;
  }
}

void structure::write(std::ostream& os, write_style) const {
  if (style_ == infix) {
    const sequence& v = cast_reference<sequence>(argument);
    if (v.formulas_.size() == 2) {
      if (v.formulas_.front()->precedence() < precedence().first_argument())
        os << "(" << v.formulas_.front() << ")";
      else os << v.formulas_.front();
      os << " ";
      if (trace_value & trace_structure_type)
        write_structure_type(os, type_);
      os << atom << " ";
      if (v.formulas_.back()->precedence() < precedence().last_argument())
        os << "(" << v.formulas_.back() << ")";
      else os << v.formulas_.back();
      return;
    }
  }
  if (style_ == prefix) {
    const sequence& v = cast_reference<sequence>(argument);
    if (v.formulas_.size() == 1) {
      if (trace_value & trace_structure_type)
        write_structure_type(os, type_);
      os << atom;
      if (v.formulas_.front()->precedence() < precedence().last_argument())
        os << "(" << v.formulas_.front() << ")";
      else
        os << " " << v.formulas_.front();
      return; 
    }
  }
  if (style_ == postfix) {
    const sequence& v = cast_reference<sequence>(argument);
    if (v.formulas_.size() == 1) {
      if (v.formulas_.front()->precedence() < precedence().first_argument())
        os << "(" << v.formulas_.front() << ")";
      else
        os << v.formulas_.front();
      if (trace_value & trace_structure_type)
        write_structure_type(os, type_);
      os << atom;
      return; 
    }
  }
  if (trace_value & trace_structure_type)
    write_structure_type(os, type_);
  os << atom << argument; return;
}


clone_source(bound_formula)
copy_source(bound_formula)

bound_formula::bound_formula(const variable_list& vs, const ref<formula>& f)
 : bind_(0), formula_(f) {
  push_back(vs);
}

bound_formula* bound_formula::push_back(const ref<variable>& v, const bound_formula::type& bt) {
  if (variable_.is_null()) { // *this has no variable yet.
    variable_ = v;
    type_ = bt;
    return this;
  }
  bound_formula* bp = new bound_formula(v, formula_, bt);
  formula_ = bp;
  return bp; 
}

void bound_formula::push_back(const variable_list& vs) {
  bound_formula* bp;
  variable_list::const_iterator i,
    i0 = vs.variables_.begin(), i1 = vs.variables_.end();
  for (i = i0; i != i1; ++i)
    if (i == i0)
      bp = push_back(i->first, i->second);
    else
      bp = bp->push_back(i->first, i->second);
}

void bound_formula::set(const ref<formula>& t) {
  formula_ = t;
}

void bound_formula::set(const bound_formula& q) {
  push_back(q.variable_, q.type_);
  set(q.formula_);
}

relation bound_formula::signature_compare(const bound_formula& x) const {
  if (variable_->variable_type() != x.variable_->variable_type())
        return unrelated;
  // Now variable types agree, so recurse on formula_:
  const bound_formula* qp = cast_pointer<bound_formula>(formula_);
  const bound_formula* xp = cast_pointer<bound_formula>(x.formula_);
  if (qp == 0 && xp == 0)  return mli::equal;
  if (qp == 0)  return mli::less;
  if (xp == 0)  return mli::greater;
  return qp->signature_compare(*xp);
}

ref<alternatives> bound_formula::unify(unify_environment tt, const ref<formula>& x, unify_environment tx, database* dbp, level lv, sublevel& sl, direction dr) const {
  if (trace_value & trace_unify)
    std::clog << "bound_formula::unify(\n  " << *this << ";\n  " << x << ")\n" << std::flush;
  /* Define a metapredicate U(f, g) := formulas f, g are unifiable. Then:
      u(all x A, all y B) == [y\x][B\A].
      x == y |- u(all x A, all y B) == [B\A].
      x =/= y, y not free in A, x not free in B |- u(all x A, all y B) == [B\A].
  */
  const bound_formula* xp = cast_pointer<bound_formula>(x);
  if (xp == 0 || type_ != xp->type_)
    return O;

  push_bound p0(tt);
  tt.table_->insert(variable_, *this);
  push_bound p1(tx);
  tx.table_->insert(xp->variable_, *xp); 

  // Solutions:
  // If x, y object/metaobject, x == y or x === y:
  //   u(A, B)
  // If x, y object, x /== y:
  //   u(x, y) • u(A, B) |- x not free in B, y not free in A.
  // If x object, y metaobject or x metaobject, y object:
  //   u(x, y) * u(A, B) ⊣ x not free in B, y not free in A
  // If x, y metaobject, x /=== y:
  //   u(A, B) ⊣ x == y
  //   u(x, y) • u(A, B) ⊣ x /== y, x not free in B, y not free in A.
  //   u(x, y) * u(A, B) ⊣ x not free in B, y not free in A.

  ref<alternatives> as;
  if (variable_ == xp->variable_) {
    as = mli::unify(formula_, tt, xp->formula_, tx, dbp, lv, sl, dr);
    return as;
  }
  kleenean free1 = formula_->has(xp->variable_, free_occurrence);
  kleenean free2 = xp->formula_->has(variable_, free_occurrence);
  if (free1 == succeed || free2 == succeed)
    return O;

  bool to = variable_->is_object(), tm = variable_->is_metaobject();
  bool xo = xp->variable_->is_object(), xm = xp->variable_->is_metaobject();
  if (!((to || tm) && (xo || xm)))
    throw runtime_error("In bound_formula, variable not representing object variable.");

    // Conditions:
    ref<formula> id = new objectidentical(variable_, xp->variable_, true);
    ref<formula> not_id = new objectidentical(variable_, xp->variable_, false);
    ref<formula> not_free1 = new free_in_object(xp->variable_, formula_, false);
    ref<formula> not_free2 = new free_in_object(variable_, xp->formula_, false);
    // y not free in A, x not free in B:
    sequence* sp1 = new sequence(metaand_);
    ref<formula> c1(sp1);
    if (free1 == undecidable)
      sp1->push_back(not_free1);
    if (free2 == undecidable)
      sp1->push_back(not_free2);
#if 0
    // x /== y, y not free in A, x not free in B:
    sequence* sp2 = new sequence(not_id, metaand_);
    ref<formula> c2(sp2);
    if (free1 == undecidable)
      sp2->push_back(not_free1);
    if (free2 == undecidable)
      sp2->push_back(not_free2);
#endif

  if (to && xo) {
    // Adds the free variables of formulas as not-free-in conditions:
    as = mli::unify_bound(variable_, tt, xp->formula_, xp->variable_, tx, formula_, dbp, lv, sl, dr);
    as = as->unify_binder(formula_, tt, xp->formula_, tx, dbp, lv, sl, dr);
    // Need to add bound variables table here, in +:
    as = as + c1;
  }
  else if ((to && xm) || (tm && xo)) {
    // u(x, y) * u(A, B):
    ref<alternatives> as0 = mli::unify(ref<formula>(variable_), tt, ref<formula>(xp->variable_), tx, dbp, lv, sl, dr);
    as0 = as0->unify(formula_, tt, xp->formula_, tx, dbp, lv, sl, dr);
    as = as->append(as0);
#if 0
    // One might add conditional solutions here:
    // If x object, y metaobject or x metaobject, y object:
    //             u(A, B) ⊣ x == y
    //   u(x, y) • u(A, B) ⊣ x /== y, x not free in B, y not free in A
    ref<alternatives> as1 = mli::unify(formula_, tt, xp->formula_, tx, dbp, lv, sl, dr);
    // Need to add bound variables table here, in +:
    as = as->append(as1 + id);
    ref<alternatives> as2 = mli::unify_bound(variable_, tt, xp->formula_, xp->variable_, tx, formula_, dbp, lv, sl, dr);
    as2 = as2->unify_binder(formula_, tt, xp->formula_, tx, dbp, lv, sl, dr);
    as = as->append(as1 + c2);
#endif
  }
  else {
    // u(x, y) * u(A, B):
    ref<alternatives> as0 = mli::unify(ref<formula>(variable_), tt, ref<formula>(xp->variable_), tx, dbp, lv, sl, dr);
    as0 = as0->unify(formula_, tt, xp->formula_, tx, dbp, lv, sl, dr);
    as = as->append(as0);
#if 0
    // One might add conditional solutions here:
    // If x, y metaobject:
    //             u(A, B) ⊣ x == y
    //   u(x, y) • u(A, B) ⊣ x /== y, x not free in B, y not free in A
    ref<alternatives> as1 = mli::unify(formula_, tt, xp->formula_, tx, dbp, lv, sl, dr);
    // Need to add bound variables table here, in +:
    as = as->append(as1 + id);
    ref<alternatives> as2 = mli::unify_bound(variable_, tt, xp->formula_, xp->variable_, tx, formula_, dbp, lv, sl, dr);
    as2 = as2->unify_binder(formula_, tt, xp->formula_, tx, dbp, lv, sl, dr);
    as = as->append(as1 + c2);
#endif
  }

  if (trace_value & trace_unify)
    std::clog << "Result bound_formula::unify(\n  " << *this << ";\n  " << x << "):"
              << as << std::endl;
  return as;
}


struct bound_formula_construct {
  ref<variable> variable_;
  bound_formula::type type_;
  bind bind_;

  bound_formula_construct(const ref<variable>& v, bound_formula::type bt, bind b)
   : variable_(v), type_(bt), bind_(b) {}

  ref<formula> operator()(const ref<formula>& x) const {
    return new bound_formula(variable_, x, type_, bind_);
  }
};

split_formula bound_formula::split(unify_environment tg,
  const ref<variable>& x, const ref<formula>& t, unify_environment tt, database* dbp, level lv, sublevel& sl, direction dr) const {
  split_formula sf(*this);  // Return value.
  // If t and *this unify, then *this can be replaced by x:
  ref<alternatives> as = mli::unify(t, tt, *this, tg, dbp, lv, sl, dr);
  if (!as->empty())
    sf.push_back(*this, ref<formula>(x));
  sf.append(
    mli::split(formula_, tg, bound_formula_construct(variable_, type_, bind_), x, t, tt, dbp, lv, sl, dr));
  return sf;
}


kleenean bound_formula::has(const ref<variable>& v, occurrence oc) const {
  switch (oc) {
    case declared_occurrence:
      if (variable_ == v && variable_->is_metaobject())  return true;
      // Fall through to free_occurrence here:
    case free_occurrence:
      if (variable_ == v)  return false;
      return formula_->has(v, oc);

    case bound_occurrence: {
      if (variable_ == v)  return true;
      bool maybe_undecidable = false;
      if (variable_->may_contain(v))
        maybe_undecidable = true;
      kleenean kl = formula_->has(v, oc);
      if (!maybe_undecidable)  return kl;
      if (kl == succeed)  return true;
      return undecidable;
    }
 
    case any_occurrence: default:
      if (variable_ == v)  return true;
      return formula_->has(v, oc);
  }
}

void bound_formula::contains(std::set<ref<variable> >& s, std::set<ref<variable> >& bs, bool& more, occurrence oc) const {
  bs.insert(variable_);
  switch (oc) {
    case declared_occurrence:
      if (variable_->is_metaobject())  s.insert(variable_);
      // Fall through to free_occurrence here:
    case free_occurrence:
      // But do not add variable_ here; it must somehow be excluded:
      formula_->contains(s, bs, more, oc);
      return;

    case bound_occurrence:
      s.insert(variable_);
      if (variable_->is_metaobject())
        more = true;
      formula_->contains(s, bs, more, oc);
      return;
 
    case any_occurrence:
      s.insert(variable_);
      if (variable_->is_metaobject())
        more = true;
      formula_->contains(s, bs, more, oc);
      return;
  }
}

kleenean bound_formula::free_for(const ref<formula>& f, const ref<variable>& x,
  std::set<ref<variable> >& s, std::list<ref<variable> >& bs) const {
  kleenean mb;
  bs.push_back(variable_);
  mb = formula_->free_for(f, x, s, bs);
  bs.pop_back();
  return mb;
}

void bound_formula::unspecialize(depth x, bool y) {
  variable_->unspecialize(x, y);
  formula_->unspecialize(x, y);
}

ref<formula> bound_formula::rename(level l, sublevel sl) const {
  bound_formula* qfp = new bound_formula(*this);
  qfp->variable_ = ref<variable>(variable_->rename(l, sl));
  qfp->formula_ = formula_->rename(l, sl);
  return qfp;
}

ref<formula> bound_formula::substitute(const ref<substitution>& s, substitute_environment vt) const {
  if (trace_value & trace_substitute)
    std::clog << "Begin bound_formula::substitute\n  "
      << "(" << *this << ")" << s
      << std::endl;
  bool b = false; // True if new table was allocated.
  variable_table* vtp = vt.table_;
  substitute_environment se1 = vt;
  if (vt.table_ == 0) {
    vtp = new unify_environment::table_type();
    b = true;
  }
  se1.table_ = vtp;
  vtp->push_level();
  vtp->insert(variable_, *this);
  bound_formula* qfp = new bound_formula(*this);
  ref<formula> vr = variable_->substitute(s, se1);
  const variable* vp = cast_pointer<variable>(vr);
  // The following works as bound variables are only unified to (bound)
  // variables (i.e., vp == 0 possible only if there is a programming error).
  if (vp == 0) {
    std::ostringstream ost;
    ost << "Error: bound_formula::substitute: " << *this << "\n"
      << s << "\n" << variable_ << "\n" << vr << std::endl;
    throw runtime_error(ost.str());
  }
  qfp->variable_ = *vp;
  qfp->formula_ = formula_->substitute(s, se1);
  if (b)  delete vtp;
  else    vtp->pop_level();
  if (trace_value & trace_substitute)
    std::clog << "bound_formula::substitute\n  "
      << "(" << *this << ")" << s << ":\n    "
      << *qfp
      << std::endl;
  return qfp;
}

void bound_formula::set_bind(bind& b, name_variable_table& vt) {
  ++b;             // New binder head gets a new identity.
  bind_ = b;
  vt.push_level(); // New level to the stacked variable table.
  vt.insert(variable_->name, variable_);
  formula_->set_bind(b, vt);
  vt.pop_level(); // This binder is finished.
}

relation bound_formula::compare(const formula& t) const {
  const bound_formula* tp = dynamic_cast<const bound_formula*>(&t);
  if (tp == 0)  return unrelated;
  relation r = variable_->compare(*tp->variable_);
  if (r != 0)  return r;
  return formula_->compare(*tp->formula_);
}

relation bound_formula::total(const formula& t) const {
  const bound_formula* tp = dynamic_cast<const bound_formula*>(&t);
  if (tp == 0)  return less; // Should not occur.
  relation r = variable_->total(*tp->variable_);
  if (r != 0)  return r;
  return formula_->total(*tp->formula_);
}


operator_precedence bound_formula::precedence() const {
  switch (type_) {
    case none_:
      return operator_precedence();
    case all_:
    case exist_:
      if (body_simple())
        return simple_quantizer_oprec; 
      return quantizer_oprec;
    case is_set_:
      return is_set_oprec;
    case set_:
      return member_list_set_oprec;
    case implicit_set_:
      return implicit_set_oprec;
    case mapto_:
      return mapto_oprec;
    case other_:
      return operator_precedence();
    default:
      return operator_precedence();
  }
}

void bound_formula::write(std::ostream& os, write_style ws) const {
  write(os, ws, bound_formula::none_);
}

void bound_formula::write(std::ostream& os, write_style ws,
    bound_formula::type type_above) const {
  if (type_ == is_set_) {
    os << "Set_";
    if ((trace_value & trace_bind) && bind_ != 0)  os << bind_;
    variable_->write(os, ws);
    os << " ";
    formula_->write(os, ws);
    return;
  }
  if (type_ == set_) {
    os << "{";
    if ((trace_value & trace_bind) && bind_ != 0)  os << bind_;
    variable_->write(os, ws);
    os << "| ";
    formula_->write(os, ws);
    os << "}";
    return;
  }
  if (type_above == none_
    || (type_above != type_)) {
    if (type_above != none_)  os << " ";
    switch (type_) {
      case all_: os << "∀"; break;
      case exist_: os << "∃"; break;
      case implicit_set_: os << "{"; break;
      default: os << "bind?";
    }
    if ((trace_value & trace_bind) && bind_ != 0)  os << bind_;
    if (type_ == implicit_set_)
      os << "_";
    else if (type_ == all_ || type_ == exist_)
      ;
    else
      os << " ";
  }
  else {
    if ((trace_value & trace_bind) && bind_ != 0)
      os << "," << bind_ << " ";
    else
      os << ", ";
  }
  variable_->write(os, ws);
  const bound_formula* bp = cast_pointer<bound_formula>(formula_);
  if (type_ == implicit_set_) {
    if (bp != 0 && bp->type_ == implicit_set_)
      bp->write(os, ws, type_);
    else {
      os << " ";
      formula_->write(os, ws);
    }
    if (type_above == none_)  os << "}";
    return;
  }
  if (body_simple()) {
    os << " ";
    formula_->write(os, ws);
    return;
  }
  const variable* vp = 0;
  if (bp != 0)
    vp = (const variable*)bp->variable_;
  if (bp == 0 || vp == 0 || !bp->is_quantified())
    os << ": ";
  if (formula_->precedence() < precedence().last_argument())
    os << "(";
  if (bp != 0)
    bp->write(os, ws, type_);
  else
    formula_->write(os, ws);
  if (formula_->precedence() < precedence().last_argument())
    os << ")";
}

bool bound_formula::body_simple() const {
  const variable* vp0 = cast_pointer<variable>(formula_);
  const constant* cp = cast_pointer<constant>(formula_);
  const structure* sp = cast_pointer<structure>(formula_);
  return (vp0 != 0 || cp != 0
    || (sp != 0 && sp->type_ == structure::predicate));
}


clone_source(inference)
copy_source(inference)

ref<alternatives> inference::unify(unify_environment tt, const ref<formula>& y, unify_environment ty, database* dbp, level lv, sublevel& sl, direction dr) const {
  if (trace_value & trace_unify)
    write_unify(std::clog, "inference::", *this, tt, y, ty, dbp, dr) << std::endl;
  // An inference with metor in the body must be expanded into metaands,
  // which is done by unify_inference():
  return body_->unify_inference(head_, tt, y, ty, dbp, lv, sl, dr);
}


struct inference_construct {
  inference::type type_;

  inference_construct(inference::type t) : type_(t) {}

  ref<formula> operator()(const ref<formula>& x, const ref<formula>& y) const {
    return new inference(x, y, type_);
  }
};


split_formula inference::split(unify_environment tg,
  const ref<variable>& x, const ref<formula>& t, unify_environment tt, database* dbp, level lv, sublevel& sl, direction dr) const {
  split_formula sf(*this);  // Return value.
  // If t and *this unify, then *this can be replaced by x:
  ref<alternatives> as = mli::unify(t, tt, *this, tg, dbp, lv, sl, dr);
  if (!as->empty())
    sf.push_back(*this, ref<formula>(x));
  sf.append(mli::split(head_, body_, tg, inference_construct(type_), x, t, tt, dbp, lv, sl, dr));
  return sf;
}

kleenean inference::has(const ref<variable>& v, occurrence oc) const {
#if 1
  kleenean k1 = head_->has(v, oc);
  if (k1 == succeed)  return true;
  kleenean k2 = body_->has(v, oc);
  return k1 || k2;
#else
  kleenean mb;
  bool is_undecidable = false;
  mb = head_->has(v, oc);
  if (mb == true)  return true;
  if (mb == undecidable)  is_undecidable = true;
  mb = body_->has(v, oc);
  if (mb == true)  return true;
  if (mb == undecidable)  is_undecidable = true;
  if (is_undecidable)  return undecidable;
  return false;
#endif
}

void inference::contains(std::set<ref<variable> >& vs, std::set<ref<variable> >& bs, bool& more, occurrence oc) const {
  head_->contains(vs, bs, more, oc);
  body_->contains(vs, bs, more, oc);
}

kleenean inference::free_for(const ref<formula>& f, const ref<variable>& x,
  std::set<ref<variable> >& s, std::list<ref<variable> >& bs) const {
  kleenean k1 = head_->free_for(f, x, s, bs);
  if (k1 == fail)  return false;
  kleenean k2 = body_->free_for(f, x, s, bs);
  return k1 && k2;
}

void inference::unspecialize(depth x, bool y) {
  head_->unspecialize(x, y);
  body_->unspecialize(x, y);
}

ref<formula> inference::rename(level lv, sublevel sl) const {
  return new inference(head_->rename(lv, sl), body_->rename(lv	, sl), type_);
}

ref<formula> inference::substitute(const ref<substitution>& s, substitute_environment vt) const {
  return new inference(head_->substitute(s, vt), body_->substitute(s, vt), type_);
}

void inference::set_bind(bind& b, name_variable_table& vt) {
  head_->set_bind(b, vt);
  body_->set_bind(b, vt);
}

relation inference::compare(const formula& x) const {
  const inference* xp = dynamic_cast<const inference*>(&x);
  if (xp == 0)  return unrelated;
  int c = head_->compare(*xp->head_);
  if (c != 0)  return c;
  return body_->compare(*xp->body_);
}

relation inference::total(const formula& x) const {
  const inference* xp = dynamic_cast<const inference*>(&x);
  if (xp == 0)  throw runtime_error("In \"structure\", total order error.");
  int c = head_->compare(*xp->head_);
  if (c != 0)  return c;
  return body_->total(*xp->body_);
}


operator_precedence inference::precedence() const {
  return inference_oprec;
}

void inference::write(std::ostream& os, write_style ws) const {
  ref<formula> first, second;
  if (is_infer()) {
    first = body_;
    second = head_;
  } else {
    first = head_;
    second = body_;
  }
  if (!first->metaempty()) {
  	if (first->precedence() < precedence().first_argument())  os << "(";
	  first->write(os, ws);
	  if (first->precedence() < precedence().first_argument())  os << ")";
	  os << " ";
	}
	if (is_infer())
    os << "⊢";
  else
    os << "⊣";
  if (!second->metaempty()) {
    os << " ";
	  if (second->precedence() < precedence().last_argument())  os << "(";
	  second->write(os, ws);
	  if (second->precedence() < precedence().last_argument())  os << ")";
  }
}


void show_solution(std::ostream& os, std::list<ref<proof> >& pfs) {
  std::list<ref<proof> >::iterator i, i0 = pfs.begin(), i1 = pfs.end();
  for (i = i0; i != i1; ++i) {
    if (i != i0)  os << "\n";
    os << *i;
  }
}

void show_solution(std::ostream& os, write_style ws,
    std::set<ref<variable> >& vs, ref<substitution> s) {
  if (vs.empty())  return;
  std::set<ref<variable> >::iterator i, i0 = vs.begin(), i1 = vs.end();
  for (i = i0; i != i1; ++i) {
    ref<formula> f = (*s)(ref<formula>(*i));
    if (f != ref<formula>(*i)) {
      if (i != i0)  os << "\n";
      os << *i << " == "; // Should be identical sign: Three horizontal bars.
      f->write(os, ws);
    }
  }
}

  // List variables:
void show_solution(std::ostream& os, write_style ws, std::set<ref<variable> >& vs) {
  if (vs.size() == 1)  os << "Variable: ";
  else  os << "Variables: ";
  std::set<ref<variable> >::iterator v, v0 = vs.begin(), v1 = vs.end();
  if (vs.empty())  os << "none";
  else
  for (v = v0; v != v1; ++v) {
    if (v != v0)  os << ", ";
    (*v)->write(os, ws);
  }
}


void show_solution(std::ostream& os, std::list<ref<substitution> >& ss) {
  std::list<ref<substitution> >::iterator s, s0 = ss.begin(), s1 = ss.end();
  if (ss.size() == 1)   os << "Substitution:";
  else  os << "Substitutions:";
  if (ss.empty())  os << " none\n";
  else if (ss.size() == 1)  os << " " << *s0;
  else
  for (s = s0; s != s1; ++s) {
    os << "\n  ";
    os << *s;
  }
}

  // List variables that gets new values by the substitutions:
void show_solution(std::ostream& os, write_style ws,
    std::set<ref<variable> >& vs, std::list<ref<substitution> >& ss) {
  std::list<ref<substitution> >::iterator s, s0 = ss.begin(), s1 = ss.end();
  if (vs.empty()) { // No variables in query:
    os << (ss.empty()? "Not proved." : "Proved.") << std::endl;
    return;
  }
  if (ss.empty()) {
    os << "No solutions." << std::endl;
    return;
  }
  for (s = s0; s != s1; ++s) {
    if (s != s0)  os << ";\n";
    show_solution(os, ws, vs, *s);
  }
  os << ".\n";
}


ref_null(database);

clone_source(database)
copy_source(database)


ref<alternatives> database::unify(unify_environment, const ref<formula>&, unify_environment, database*, level, sublevel&, direction) const {
  return O;
}

ref<formula> database::rename(level, sublevel) const {
  return this->clone();
}

bool database::empty() const {
  return true;
}

int database::get_level() const {
  return 0;
}

bool database::has_definition(level) const {
  return false;
}

bool database::insert(const ref<labelstatement>& st) {
  if (trace_value & trace_database)
    std::cerr << "database::insert, no database: " << st << "\n";
  return false;
}

ref<alternatives> database::find(ref<formula> x, level lv, database* dbp, bool) {
  if (trace_value & trace_labelstatement)
    std::clog << "database::find, level "
      << lv << ": " << x << std::endl;
  ref<alternatives> as; // Return value.
  // Renamng of formulas take place in each database::unify().
  sublevel sl = 0;  // The next usable sublevel number.
  if (trace_value & trace_labelstatement)
    std::clog << "database::find: " << *this << std::endl;
  unify_count = 0; // Start to count unify() calls for this find().
  as = mli::unify(x, goal, *this, choice, dbp, lv, sl); // Test
  if (trace_value & trace_unify)
    std::clog << "database::unify() count = " << unify_count << std::endl;
  if (trace_value & trace_labelstatement)
    std::clog << "database::unify(\n  " << x << ";\n  " << *this << "):" << as << std::endl;
  return as;
}

maybe<ref<labelstatement> > database::find(const std::string& name, level lv, bool) {
  if (trace_value & trace_database)
    std::cerr << "database::find, no database, level " << lv << ", name: " << name << "\n";
  return false;
}

ref<alternatives> database::unify_x1(const ref<formula>&, unify_environment, const ref<formula>&, unify_environment, database*, level, sublevel&) {
  return O;
}

ref<alternatives> database::unify_x2(const ref<formula>&, unify_environment, const ref<formula>&, unify_environment, database*, level, sublevel&) {
  return O;
}

#if 0
enum engine_type { stack_engine, pure_engine, Andorra_engine };

void database::demonstrate(const ref<formula>& q, engine_type e) {
  std::list<ref<substitution> > ss; // Find solutions:
  switch (e) {
    default:
    case stack_engine: ss = prove(q, 0); break;
    case pure_engine: ss = pure_prove(q); break;
    case Andorra_engine: ss = Andorra_prove(q); break;
  };

  std::set<ref<variable> > vs; // Find variables:
  q->contains(vs, any_occurrence);

  if (trace_value & (trace_result | trace_proof)) {
    show_solution(std::clog, write_default, vs);
    show_solution(std::clog, ss);
  }
  show_solution(std::cout, write_default, vs, ss);
}
#endif

void database::write(std::ostream& os, write_style) const {
  os << "no database\n";
}


} // namespace mli
