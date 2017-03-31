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

#include "basictype.hh"

#include "substitution.hh"


namespace mli {


clone_source(integer)
copy_source(integer)

ref<alternatives> integer::unify(unify_environment, const ref<formula>& x, unify_environment, database*, level, sublevel&, direction) const {
  if (trace_value & trace_unify)
    std::clog
     << "integer::unify\n  " << *this << ";\n  " << x << ")"
     << std::endl;
  const integer* xp = cast_pointer<integer>(x);
  return (xp != 0) && gmp::operator==(*this, *xp)? I : O;
}

#if 0
inline relation compare(const integer& x, const integer& y) {
  return sgn(x.name.compare(y.name));
}
#endif

relation integer::compare(const formula& x) const {
  const integer* xp = dynamic_cast<const integer*>(&x);
  if (xp == 0)  return unrelated;
  return this->gmp::integer::compare(*xp);
}

relation integer::total(const formula& x) const {
  const integer* xp = dynamic_cast<const integer*>(&x);
  if (xp == 0)  throw runtime_error("In \"integer\", total order error.");
  return this->gmp::integer::compare(*xp);
}

void integer::write(std::ostream& os, write_style) const {
  gmp::operator<<(os, *this);
}


#if 0
maybe<substitution> unify(const integer_addition&, long);
maybe<substitution> unify(const integer_negative&, long);

maybe<substitution> unify(const integer_addition&, const integer_negative&);

maybe<substitution> integer::unify(const formula& t) const {
  const integer_addition* ia = dynamic_cast<const integer_addition*>(t.data());
  if (ia != 0)  return mli::unify(*ia, value_);
  const integer_negative* in = dynamic_cast<const integer_negative*>(t.data());
  if (in != 0)  return mli::unify(in->value_, new integer(-value_));
  const integer* ip = dynamic_cast<const integer*>(t.data());
  if (ip == 0)  return false;
  return value_ == ip->value_;
}

bool integer::has_free(const variable&) const {
  return false;
}

void integer::has_free(std::set<variable>&) const {}

proposition_root* integer::rename(int) const {
  return dynamic_cast<integer*>(copy());
}

proposition_root* integer::apply(const substitution&) const {
  return dynamic_cast<integer*>(copy());
}

relate integer::compare(const formula_root& x) const {
  const integer* xp = dynamic_cast<const integer*>(&x);
  if (xp == 0)  return unrelated;
  return sgn(value_ - xp->value_);
}

relate integer::total(const formula_root& x) const {
  const integer* xp = dynamic_cast<const integer*>(&x);
  if (xp == 0)  throw runtime_error("In \"integer\", total order error.");
  return sgn(value_ - xp->value_);
}

bool integer::equal(const formula_root& x) const {
  const integer* xp = dynamic_cast<const integer*>(&x);
  if (xp == 0)  return false;
  return *this == *xp;
}

void integer::write(std::ostream& os, write_style) const {
  os << value_;
}

inline formula operator-(const formula& x) {
  const integer_negative* xp = dynamic_cast<const integer_negative*>(x.data());
  if (xp != 0)  return xp->value_;
  return new integer_negative(x);
}

inline formula operator+(const formula& x, const formula& y) {
  const integer* xp = dynamic_cast<const integer*>(x.data());
  const integer* yp = dynamic_cast<const integer*>(y.data());
  if (xp != 0 && yp != 0)  return new integer(xp->value_ + yp->value_);
  return new integer_addition(x, y);
}

inline formula operator+(const formula& x, long y) {
  if (y == 0)  return x;
  const integer* xp = dynamic_cast<const integer*>(x.data());
  if (xp != 0)  return new integer(xp->value_ + y);
  return new integer_addition(x, new integer(y));
}

maybe<substitution> unify(const integer_addition& x, long y) {
  const integer* x1 = dynamic_cast<const integer*>(x.first.data());
  const integer* x2 = dynamic_cast<const integer*>(x.second.data());
  if (x1 != 0 && x2 != 0)
    return x1->value_ + x2->value_ == y;
  if (x1 != 0)
    return mli::unify(x.second, new integer(y - x1->value_));
  if (x2 != 0)
    return mli::unify(x.first, new integer(y - x2->value_));
  relate r = x.first.total(x.second);
  if (r == less)
    return mli::unify(x.first, (-x.second) + y);
  return mli::unify(x.second, (-x.first) + y);
}

maybe<substitution> unify(const integer_addition& x, const integer_negative& y) {
  const integer* x1 = dynamic_cast<const integer*>(x.first.data());
  const integer* x2 = dynamic_cast<const integer*>(x.second.data());
  const integer* yp = dynamic_cast<const integer*>(y.value_.data());
  if (yp != 0)  return unify(x, -yp->value_);
  if (x1 != 0)
    return unify(integer_addition(x.second, y.value_), -x1->value_);
  if (x2 != 0)
    return unify(integer_addition(y.value_, x.first), -x2->value_);
#if 0
  relate r12 = x.first.total(x.second);
  relate r13 = x.first.total(y.value_);
  relate r23 = x.second.total(y.value_);
  if (r12 == less && r23 == less)
#endif
  return true;
}

maybe<substitution> unify(const integer_addition& x, const integer_addition& y) {
  const integer* x1 = dynamic_cast<const integer*>(x.first.data());
  const integer* x2 = dynamic_cast<const integer*>(x.second.data());
  const integer* y1 = dynamic_cast<const integer*>(y.first.data());
  const integer* y2 = dynamic_cast<const integer*>(y.second.data());
  if (x1 != 0 && x2 != 0)  return mli::unify(y, x1->value_ + x2->value_);
  if (y1 != 0 && y2 != 0)  return mli::unify(x, y1->value_ + y2->value_);
  if (x1 != 0 && y1 != 0 && x2 != 0 && y2 != 0)
    return x1->value_ + x2->value_ == y1->value_ + y2->value_;
  if (x1 != 0 && y1 != 0) // => x2 == 0 && y2 == 0
    return mli::unify(x.second,
      new integer_addition(new integer(y1->value_ - x1->value_), y.second));
  if (x2 != 0 && y2 != 0) // => x1 == 0 && y1 == 0
    return mli::unify(x.first,
      new integer_addition(y.first, new integer(y2->value_ - x2->value_)));
  // At most one x1, y1, x2, y2 != 0:
  if (x1 != 0)
    return mli::unify(x.second,
      new integer_addition(new integer(-x1->value_), new integer_addition(y)));
  if (x2 != 0)
    return mli::unify(x.first,
      new integer_addition(new integer_addition(y), new integer(-x2->value_)));
  // => x1 == 0 && x2 == 0:
  if (y1 != 0)
    return mli::unify(y.second,
      new integer_addition(new integer(-y1->value_), new integer_addition(x)));
  if (y2 != 0)
    return mli::unify(y.first,
      new integer_addition(new integer_addition(x), new integer(-y2->value_)));
  // All x1, y1, x2, y2 == 0:
  return mli::unify(x.first,
    new integer_addition(new integer_addition(y), new integer_negative(x.second)));
}

maybe<substitution> integer_addition::unify(const formula& t) const {
  const integer* ip = dynamic_cast<const integer*>(t.data());
  if (ip != 0)  return mli::unify(*this, ip->value_);
  const integer_negative* in = dynamic_cast<const integer_negative*>(t.data());
  if (in != 0)  return mli::unify(*this, *in);
  const integer_addition* ia = dynamic_cast<const integer_addition*>(t.data());
  if (ia != 0)  return mli::unify(*this, *ia);
  return false;
}

bool integer_addition::has_free(const variable& v) const {
  return first.has_free(v) || second.has_free(v);
}

void integer_addition::has_free(std::set<variable>& s) const {
  first.has_free(s);  second.has_free(s);
}

void integer_addition::set_depth(int b) {
  first.set_depth(b);  second.set_depth(b);
}

proposition_root* integer_addition::rename(int n) const {
  return new integer_addition(first.rename(n), second.rename(n));
}

proposition_root* integer_addition::apply(const substitution& s) const {
  std::auto_ptr<integer_addition> ip(new integer_addition()); // Exception safety.
  ip->first = first.apply(s);
  ip->second = second.apply(s);
  // If substitutions produced integers, return an integer instead:
  const integer* ip1 = dynamic_cast<const integer*>(ip->first.data());
  const integer* ip2 = dynamic_cast<const integer*>(ip->second.data());
  if (ip1 == 0 || ip2 == 0)  return ip.release();
  return new integer(ip1->value_ + ip2->value_);
}

relate integer_addition::compare(const formula_root& x) const {
  const integer_addition* xp = dynamic_cast<const integer_addition*>(&x);
  if (xp == 0)  return unrelated;
  relate r = first.compare(xp->first);
  if (r != 0)  return r;
  return second.compare(xp->second);
}

relate integer_addition::total(const formula_root& x) const {
  const integer_addition* xp = dynamic_cast<const integer_addition*>(&x);
  if (xp == 0)  throw runtime_error("In \"integer_addition\", total order error.");
  relate r = first.total(xp->first);
  if (r != 0)  return r;
  return second.total(xp->second);
}

bool integer_addition::equal(const formula_root& x) const {
  const integer* ip = dynamic_cast<const integer*>(&x);
  if (ip != 0) {
    const integer* ip1 = dynamic_cast<const integer*>(first.data());
    if (ip1 == 0)  return false;
    const integer* ip2 = dynamic_cast<const integer*>(second.data());
    if (ip2 == 0)  return false;
    return ip1->value_ + ip2->value_ == ip->value_;
  }
  const integer_addition* xp = dynamic_cast<const integer_addition*>(&x);
  if (xp == 0)  return false;
  return *this == *xp;
}

void integer_addition::write(std::ostream& os, write_style) const {
  os << first << " + " << second;
}


maybe<substitution> unify(const integer_negative& x, long y) {
  const integer* xp = dynamic_cast<const integer*>(x.value_.data());
  if (xp != 0)
    return -xp->value_ == y;
  return mli::unify(x.value_, new integer(-y));
}

maybe<substitution> integer_negative::unify(const formula& t) const {
  const integer* ip = dynamic_cast<const integer*>(t.data());
  if (ip != 0)  return mli::unify(*this, ip->value_);
  const integer_negative* in = dynamic_cast<const integer_negative*>(t.data());
  if (in != 0)  return mli::unify(value_, in->value_);
  const integer_addition* ia = dynamic_cast<const integer_addition*>(t.data());
  if (ia != 0)  return mli::unify(*ia, *this);
  return false;
}

bool integer_negative::has_free(const variable& v) const {
  return value_.has_free(v);
}

void integer_negative::has_free(std::set<variable>& s) const {
  value_.has_free(s);
}

void integer_negative::set_depth(int b) {
  value_.set_depth(b);
}


proposition_root* integer_negative::rename(int n) const {
  return new integer_negative(value_.rename(n));
}

proposition_root* integer_negative::apply(const substitution& s) const {
  formula x = value_.apply(s);
  const integer* ip = dynamic_cast<const integer*>(x.data());
  if (ip != 0)  return new integer(-ip->value_);
  const integer_negative* inp = dynamic_cast<const integer_negative*>(x.data());
  if (inp != 0)  return inp->value_.copy();
  return new integer_negative(x);
}

relate integer_negative::compare(const formula_root& x) const {
  const integer_negative* xp = dynamic_cast<const integer_negative*>(&x);
  if (xp == 0)  return unrelated;
  return value_.compare(xp->value_);
}

relate integer_negative::total(const formula_root& x) const {
  const integer_negative* xp = dynamic_cast<const integer_negative*>(&x);
  if (xp == 0)  throw runtime_error("In \"integer_negative\", total order error.");
  return value_.total(xp->value_);
}

bool integer_negative::equal(const formula_root& x) const {
  const integer* ip = dynamic_cast<const integer*>(&x);
  if (ip != 0) {
    const integer* ip1 = dynamic_cast<const integer*>(value_.data());
    if (ip1 == 0)  return false;
    return ip1->value_ == ip->value_;
  }
  const integer_negative* xp = dynamic_cast<const integer_negative*>(&x);
  if (xp == 0)  return false;
  return *this == *xp;
}

void integer_negative::write(std::ostream& os, write_style) const {
  os << "-" << value_;
}
#endif

#if 0
maybe<substitution> unify(const integer_less& x, long y) {
  const integer* x1 = dynamic_cast<const integer*>(x.first.data());
  const integer* x2 = dynamic_cast<const integer*>(x.second.data());
  if (x1 != 0 && x2 != 0)
    return x1->value_ + x2->value_ == y;
  if (x1 != 0)
    return mli::unify(x.second, new integer(y - x1->value_));
  if (x2 != 0)
    return mli::unify(x.first, new integer(y - x2->value_));
  return mli::unify(x.first,
    new integer_less(new integer(y), new integer_negative(x.second)));
}

maybe<substitution> unify(const integer_less& x, const integer_less& y) {
  const integer* x1 = dynamic_cast<const integer*>(x.first.data());
  const integer* x2 = dynamic_cast<const integer*>(x.second.data());
  const integer* y1 = dynamic_cast<const integer*>(y.first.data());
  const integer* y2 = dynamic_cast<const integer*>(y.second.data());
  if (x1 != 0 && x2 != 0)  return mli::unify(y, x1->value_ + x2->value_);
  if (y1 != 0 && y2 != 0)  return mli::unify(x, y1->value_ + y2->value_);
  if (x1 != 0 && y1 != 0 && x2 != 0 && y2 != 0)
    return x1->value_ + x2->value_ == y1->value_ + y2->value_;
  if (x1 != 0 && y1 != 0) // => x2 == 0 && y2 == 0
    return mli::unify(x.second,
      new integer_less(new integer(y1->value_ - x1->value_), y.second));
  if (x2 != 0 && y2 != 0) // => x1 == 0 && y1 == 0
    return mli::unify(x.first,
      new integer_less(y.first, new integer(y2->value_ - x2->value_)));
  // At most one x1, y1, x2, y2 != 0:
  if (x1 != 0)
    return mli::unify(x.second,
      new integer_less(new integer(-x1->value_), new integer_less(y)));
  if (x2 != 0)
    return mli::unify(x.first,
      new integer_less(new integer_less(y), new integer(-x2->value_)));
  // => x1 == 0 && x2 == 0:
  if (y1 != 0)
    return mli::unify(y.second,
      new integer_less(new integer(-y1->value_), new integer_less(x)));
  if (y2 != 0)
    return mli::unify(y.first,
      new integer_less(new integer_less(x), new integer(-y2->value_)));
  // All x1, y1, x2, y2 == 0:
  return mli::unify(x.first,
    new integer_less(new integer_less(y), new integer_negative(x.second)));
}

maybe<substitution> integer_less::unify(const formula& t) const {
  const integer* ip = dynamic_cast<const integer*>(t.data());
  if (ip != 0)  return mli::unify(*this, ip->value_);
  const integer_less* iap = dynamic_cast<const integer_less*>(t.data());
  if (iap == 0)  return false;
  return mli::unify(*this, *iap);
}

bool integer_less::has_free(const variable& v) const {
  return first.has_free(v) || second.has_free(v);
}

void integer_less::has_free(std::set<variable>& s) const {
  first.has_free(s);  second.has_free(s);
}

proposition_root* integer_less::rename(int n) const {
  return new integer_less(first.rename(n), second.rename(n));
}

proposition_root* integer_less::apply(const substitution& s) const {
  integer_less* ip = new integer_less();
  formula ret = ip; // Exception safety.
  ip->first = first.apply(s);
  ip->second = second.apply(s);
  // If substitutions produced integers, return an integer instead:
  const integer* ip1 = dynamic_cast<const integer*>(ip->first.data());
  const integer* ip2 = dynamic_cast<const integer*>(ip->second.data());
  if (ip1 == 0 || ip2 == 0)  return ret;
  return new integer(ip1->value_ + ip2->value_);
}

bool integer_less::equal(const formula_root& x) const {
  const integer_less* xp = dynamic_cast<const integer_less*>(&x);
  if (xp == 0)  return false;
  return *this == *xp;
}

void integer_less::write(std::ostream& os, write_style) const {
  os << first << " < " << second;
}
#endif


} // namespace mli


