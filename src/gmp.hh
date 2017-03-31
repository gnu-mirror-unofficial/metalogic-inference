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

#ifndef GMPXX_H
#define GMPXX_H

#include <iostream>
#include <string>
#include <utility>

#include <gmp.h>


namespace gmp {

typedef int relate;

const relate unrelated = -2;
const relate less = -1;
const relate equal = 0;
const relate greater = 1;

template<class X, class Y>
relate inequality_compare(const X& x, const Y& y) {
  if (x < y)   return gmp::less;
  if (x > y)   return gmp::greater;
  if (x == y)  return gmp::equal;
  return unrelated;
}

template<class A> // The sign of a number:
inline int sgn(A x) { return (x > 0) - (x < 0); }

inline bool less_equal(relate r) { return r == less || r == equal; }
inline bool greater_equal(relate r) { return r == greater || r == equal; }


class rational;
class floating;



template<class A>
class ref {
  class ptr {
  public:
    A data_;
    mutable unsigned count_;

    ptr() : count_(1) {}
    ptr(const ptr& p) : count_(1), data_(p.data_) {}

    ptr* clone() const { return new ptr(*this); }
    ptr* copy() const { ++count_; return const_cast<ptr*>(this); }
    ptr* detach() const {
      if (count_ > 1) { shed(); return clone(); }
      return const_cast<ptr*>(this);
    }
    void shed() const { if (--count_ == 0)  delete this; }
  };

  ptr* ptr_;

  ptr* copy() const { return ptr_->copy(); }
  void shed() const { ptr_->shed(); }

public:
  ref() : ptr_(new ptr()) { }
  ~ref() { shed(); }

  ref(const ref& x) : ptr_(x.copy()) { }
  ref& operator=(const ref& x) {
    if (ptr_ != x.ptr_) { shed(); ptr_ = x.copy(); }
    return *this;
  }

  ref(const A& a) : ptr_(new ptr(a)) { }

  void detach() { ptr_ = ptr_->detach(); }

  A& operator*() { return ptr_->data_; }
  const A& operator*() const { return ptr_->data_; }

  void swap(ref<A>& x) { ptr* p = x.ptr_; x.ptr_ = ptr_; ptr_ = p; }
};


class mpz {
  mpz_t value_;
public:
  mpz() { } // Note: Not initialized. Must be initialized by the class integer.
  ~mpz() { mpz_clear(value_); }
  
  // The copy constructor and assignment functions are in reality never called:
  mpz(const mpz& x) { mpz_init_set(value_, x.value_); }
  mpz& operator=(const mpz& x) { mpz_set(value_, x.value_); return *this; }
  
  mpz_t& operator*() { return value_; }
  const mpz_t& operator*() const { return value_; }
};


class integer {
public:
  ref<mpz> value_;
  void detach() { value_.detach(); }

public:
  integer() { mpz_init(**value_); }

  integer(unsigned long int x) { mpz_init_set_ui(**value_, x); }
  integer(signed long int x) { mpz_init_set_si(**value_, x); }
  integer(double x) { mpz_init_set_d(**value_, x); }
  integer(const char* str, int base = 0) { mpz_init_set_str(**value_, str, base); }

  integer& operator=(unsigned long int x) { detach(); mpz_set_ui(**value_, x); return *this; }
  integer& operator=(signed long int x) { detach(); mpz_set_si(**value_, x); return *this; }
  integer& operator=(double x) { detach(); mpz_set_d(**value_, x); return *this; }
  integer& operator=(const char* str) { detach(); mpz_set_str(**value_, str, 0); return *this; }

  double get_d() const { return mpz_get_d(**value_); }
  signed long int get_si() const { return mpz_get_si(**value_); }
  unsigned long int get_ui() const { return mpz_get_ui(**value_); }
  std::string str(int base = 10) const {
    char* cs = new char[mpz_sizeinbase(**value_, base) + 2];
    mpz_get_str(cs, base, **value_);
    std::string str_r(cs); delete[] cs;
    return str_r;
  }

  relate compare(const integer& x) const { return sgn(mpz_cmp(**value_, **x.value_)); }

  void swap(integer& x) { value_.swap(x.value_); }
  
  size_t read(std::istream&, int base = 0);
  
  friend integer operator+(const integer&, const integer&);
  friend integer operator-(const integer&);
  friend integer operator-(const integer&, const integer&);
  friend integer operator*(const integer&, const integer&);

  friend bool operator<(const integer&, const integer&);
  friend bool operator<=(const integer&, const integer&);
  friend bool operator==(const integer&, const integer&);
  friend bool operator!=(const integer&, const integer&);
  friend bool operator>(const integer&, const integer&);
  friend bool operator>=(const integer&, const integer&);

  friend integer abs(const integer&); // Absolute value.

  friend std::istream& operator>>(std::istream&, integer&);
  friend std::ostream& operator<<(std::ostream&, const integer&);
};


inline integer operator+(const integer& x, const integer& y) {
  integer r;  mpz_add(**r.value_, **x.value_, **y.value_);  return r;
}

inline integer operator-(const integer& x) {
  integer r;  mpz_neg(**r.value_, **x.value_);  return r;
}

inline integer operator-(const integer& x, const integer& y) {
  integer r;  mpz_sub(**r.value_, **x.value_, **y.value_);  return r;
}

inline integer operator*(const integer& x, const integer& y) {
  integer r;  mpz_mul(**r.value_, **x.value_, **y.value_);  return r;
}

inline bool operator<(const integer& x, const integer& y)
{  return x.compare(y) == less;  }

inline bool operator<=(const integer& x, const integer& y)
{  return less_equal(x.compare(y));  }

inline bool operator==(const integer& x, const integer& y)
{  return x.compare(y) == equal;  }

inline bool operator!=(const integer& x, const integer& y)
{  return x.compare(y) != equal;  }

inline bool operator>(const integer& x, const integer& y)
{  return x.compare(y) == greater;  }

inline bool operator>=(const integer& x, const integer& y)
{  return greater_equal(x.compare(y));  }


inline integer abs(const integer& x) {
  integer r;  mpz_abs(**r.value_, **x.value_);  return r;
}


inline std::istream& operator>>(std::istream& is, integer& x) {
  x.read(is);  return is;
}

inline std::ostream& operator<<(std::ostream& os, const integer& n) {
  return os << n.str();
}


class rational {
public:
  mpq_t value_;

public:
  rational() { mpq_init(value_); }
  ~rational() { mpq_clear(value_); }
  
  rational(const rational& x) { mpq_init(value_); mpq_set(value_, x.value_); }
  rational& operator=(const rational& x) { mpq_set(value_, x.value_); return *this; }

  void canonicalize() { mpq_canonicalize(value_); }

  rational(long int x)
  { mpq_init(value_);  mpz_set_si(mpq_numref(value_), x); }
  rational(unsigned long int x, unsigned long int y)
  { mpq_init(value_);  mpq_set_ui(value_, x, y); }
  rational(signed long int x, unsigned long int y)
  { mpq_init(value_);  mpq_set_si(value_, x, y); }
  rational(double x) { mpq_init(value_); mpq_set_d(value_, x); }
  rational(const char*, int base = 0);
  rational(const integer& x) { mpq_init(value_); mpq_set_z(value_, **x.value_); }
  rational(const integer& p, const integer& q) { mpq_init(value_);
    mpq_set_num(value_, **p.value_); mpq_set_den(value_, **q.value_); canonicalize(); }
  rational(const floating& x); // { mpq_init_set_f(value_, x); }

  rational& operator=(double x) { mpq_set_d(value_, x); return *this; }
  rational& operator=(const integer& x) { mpq_set_z(value_, **x.value_); return *this; }
  rational& operator=(const floating& x); // { mpq_set_f(value_, x); return *this; }

  double get_d() const { return mpq_get_d(value_); }
  integer& get_num(integer& p) const { mpq_get_num(**p.value_, value_); return p; }
  integer& get_den(integer& q) const { mpq_get_den(**q.value_, value_); return q; }
  integer get_num() const { integer p; mpq_get_num(**p.value_, value_); return p; }
  integer get_den() const { integer q; mpq_get_den(**q.value_, value_); return q; }
  void get(integer& p, integer& q) const { get_num(p); get_den(q);  }
  std::string str(int base = 10) const;

  relate compare(const rational& x) const { return sgn(mpq_cmp(value_, x.value_)); }

  void swap(rational& x) { mpq_swap(value_, x.value_); }
  
  size_t read(std::istream&, int base = 0);
  
  rational& operator+=(const rational& x) { mpq_add(value_, value_, x.value_); return *this; }
  
  friend rational operator+(const rational&, const rational&);
  friend rational operator-(const rational&);
  friend rational operator-(const rational&, const rational&);
  friend rational operator*(const rational&, const rational&);
  friend rational operator/(const rational&, const rational&);

  friend bool operator<(const rational&, const rational&);
  friend bool operator<=(const rational&, const rational&);
  friend bool operator==(const rational&, const rational&);
  friend bool operator!=(const rational&, const rational&);
  friend bool operator>(const rational&, const rational&);
  friend bool operator>=(const rational&, const rational&);

  friend std::istream& operator>>(std::istream&, rational&);
  friend std::ostream& operator<<(std::ostream&, const rational&);
};


inline rational operator+(const rational& x, const rational& y) {
  rational r;  mpq_add(r.value_, x.value_, y.value_);  return r;
}

inline rational operator-(const rational& x) {
  rational r;  mpq_neg(r.value_, x.value_);  return r;
}

inline rational operator-(const rational& x, const rational& y) {
  rational r;  mpq_sub(r.value_, x.value_, y.value_);  return r;
}

inline rational operator*(const rational& x, const rational& y) {
  rational r;  mpq_mul(r.value_, x.value_, y.value_);  return r;
}

inline rational operator/(const rational& x, const rational& y) {
  rational r;  mpq_div(r.value_, x.value_, y.value_);  return r;
}


inline bool operator<(const rational& x, const rational& y)
{  return x.compare(y) == less;  }

inline bool operator<=(const rational& x, const rational& y)
{  return x.compare(y) <= equal;  }

inline bool operator==(const rational& x, const rational& y)
{  return x.compare(y) == equal;  }

inline bool operator!=(const rational& x, const rational& y)
{  return x.compare(y) != equal;  }

inline bool operator>(const rational& x, const rational& y)
{  return x.compare(y) > equal;  }

inline bool operator>=(const rational& x, const rational& y)
{  return x.compare(y) >= equal;  }


inline std::ostream& operator<<(std::ostream& os, const rational& r) {
  return os << r.str();
}

inline std::istream& operator>>(std::istream& is, rational& x) {
  x.read(is);  return is;
}


inline rational abs(const rational& x) {
  rational r;  mpz_abs(mpq_numref(r.value_), mpq_numref(x.value_));
  mpq_set_den(r.value_, mpq_denref(x.value_));  return r;
}


inline integer ceil(const rational& x) {
  integer r;  mpz_cdiv_q(**r.value_, mpq_numref(x.value_), mpq_denref(x.value_));  return r;
}

inline integer floor(const rational& x) {
  integer r;  mpz_fdiv_q(**r.value_, mpq_numref(x.value_), mpq_denref(x.value_));  return r;
}

inline integer trunc(const rational& x) {
  integer r;  mpz_tdiv_q(**r.value_, mpq_numref(x.value_), mpq_denref(x.value_));  return r;
}

inline rational frac_ceil(const rational& x) {
  rational r;  mpz_cdiv_r(mpq_numref(r.value_), mpq_numref(x.value_), mpq_denref(x.value_));
  mpq_set_den(r.value_, mpq_denref(x.value_));  return r;
}

inline rational frac_floor(const rational& x) {
  rational r;  mpz_fdiv_r(mpq_numref(r.value_), mpq_numref(x.value_), mpq_denref(x.value_));
  mpq_set_den(r.value_, mpq_denref(x.value_));  return r;
}

inline rational frac_trunc(const rational& x) {
  rational r;  mpz_tdiv_r(mpq_numref(r.value_), mpq_numref(x.value_), mpq_denref(x.value_));
  mpq_set_den(r.value_, mpq_denref(x.value_));  return r;
}

inline std::pair<integer, rational> div_ceil(const rational& x) {
  std::pair<integer, rational> r;
  mpz_cdiv_qr(**r.first.value_, mpq_numref(r.second.value_), mpq_numref(x.value_), mpq_denref(x.value_));
  mpq_set_den(r.second.value_, mpq_denref(x.value_));
  return r;
}

inline std::pair<integer, rational> div_floor(const rational& x) {
  std::pair<integer, rational> r;
  mpz_fdiv_qr(**r.first.value_, mpq_numref(r.second.value_), mpq_numref(x.value_), mpq_denref(x.value_));
  mpq_set_den(r.second.value_, mpq_denref(x.value_));
  return r;
}

inline std::pair<integer, rational> div_trunc(const rational& x) {
  std::pair<integer, rational> r;
  mpz_tdiv_qr(**r.first.value_, mpq_numref(r.second.value_), mpq_numref(x.value_), mpq_denref(x.value_));
  mpq_set_den(r.second.value_, mpq_denref(x.value_));
  return r;
}


class floating {
public:
  mpf_t value_;

public:
  struct precision {
    unsigned long prec_;
    precision(unsigned long prec) : prec_(prec) { }
    friend precision min(const precision&, const precision&);
  };

  floating() { mpf_init(value_); }
  ~floating() { mpf_clear(value_); }
  
  floating(const floating& x) { mpf_init(value_); mpf_set(value_, x.value_); }
  floating& operator=(const floating& x) { mpf_set(value_, x.value_); return *this; }

  floating(unsigned long int x) { mpf_init_set_ui(value_, x); }
  floating(signed long int x) { mpf_init_set_si(value_, x); }
  floating(double x) { mpf_init_set_d(value_, x); }
  floating(const char* str, int base = 0) { mpf_init_set_str(value_, str, base); }
  floating(const integer& x) { mpf_init(value_); mpf_set_z(value_, **x.value_); }
  floating(const rational& x) { mpf_set_q(value_, x.value_); }

  floating& operator=(unsigned long int x) { mpf_set_ui(value_, x); return *this; }
  floating& operator=(signed long int x) { mpf_set_si(value_, x); return *this; }
  floating& operator=(double x) { mpf_set_d(value_, x); return *this; }
  floating& operator=(const char* str) { mpf_set_str(value_, str, 0); return *this; }
  floating& operator=(const integer& x) { mpf_set_z(value_, **x.value_); return *this; }
  floating& operator=(const rational& x) { mpf_set_q(value_, x.value_); return *this; }

  struct set_local { // Set default only in the local environment.
    mp_size_t limb_prec_;
    set_local(precision p);
    ~set_local();
  };
  static void set_default(precision p) { mpf_set_default_prec(p.prec_); }
  floating(precision p) { mpf_init2(value_, p.prec_); }
  void set(precision p) { return mpf_set_prec(value_, p.prec_); }
  precision get_prec() const { return mpf_get_prec(value_); }
  
  double get_d() const { return mpf_get_d(value_); }
  std::string str(int base = 10, size_t digits = 0) const;

  relate compare(const floating& x) const { return sgn(mpf_cmp(value_, x.value_)); }

  void swap(floating& x) { mpf_swap(value_, x.value_); }
  
  size_t read(std::istream&, int base = 10);
  
  friend floating operator+(const floating&, const floating&);
  friend floating operator-(const floating&);
  friend floating operator-(const floating&, const floating&);
  friend floating operator*(const floating&, const floating&);
  friend floating operator/(const floating&, const floating&);

  friend bool operator<(const floating&, const floating&);
  friend bool operator<=(const floating&, const floating&);
  friend bool operator==(const floating&, const floating&);
  friend bool operator!=(const floating&, const floating&);
  friend bool operator>(const floating&, const floating&);
  friend bool operator>=(const floating&, const floating&);

  friend std::istream& operator>>(std::istream&, floating&);
  friend std::ostream& operator<<(std::ostream&, const floating&);

  friend floating abs(const floating&); // Absolute value.
};


inline floating::precision min(const floating::precision& x, const floating::precision& y) {
  return x.prec_ <= y.prec_? x.prec_ : y.prec_;
}

inline floating operator+(const floating& x, const floating& y) {
  floating r;  mpf_add(r.value_, x.value_, y.value_);  return r;
}

inline floating operator-(const floating& x) {
  floating r(x.get_prec());  mpf_neg(r.value_, x.value_);  return r;
}

inline floating operator-(const floating& x, const floating& y) {
  floating r;  mpf_sub(r.value_, x.value_, y.value_);  return r;
}

inline floating operator*(const floating& x, const floating& y) {
  floating::precision p(min(x.get_prec(), y.get_prec()));
  floating r(p);
  mpf_mul(r.value_, x.value_, y.value_);  return r;
}

inline floating operator/(const floating& x, const floating& y) {
  floating::precision p(min(x.get_prec(), y.get_prec()));
  floating r(p);
  mpf_div(r.value_, x.value_, y.value_);  return r;
}


inline bool operator<(const floating& x, const floating& y)
{  return x.compare(y) == less;  }

inline bool operator<=(const floating& x, const floating& y)
{  return x.compare(y) <= equal;  }

inline bool operator==(const floating& x, const floating& y)
{  return x.compare(y) == equal;  }

inline bool operator!=(const floating& x, const floating& y)
{  return x.compare(y) != equal;  }

inline bool operator>(const floating& x, const floating& y)
{  return x.compare(y) > equal;  }

inline bool operator>=(const floating& x, const floating& y)
{  return x.compare(y) >= equal;  }


inline std::ostream& operator<<(std::ostream& os, const floating& n) {
  return os << n.str();
}

inline std::istream& operator>>(std::istream& is, floating& x) {
  x.read(is);  return is;
}


inline floating abs(const floating& x) {
  floating r(x.get_prec());  mpf_abs(r.value_, x.value_);  return r;
}

inline integer ceil(const floating& x) {
  integer r;  floating f;  mpf_ceil(f.value_, x.value_);
  mpz_set_f(**r.value_, f.value_);  return r;
}

inline integer floor(const floating& x) {
  integer r;  floating f;  mpf_floor(f.value_, x.value_);
  mpz_set_f(**r.value_, f.value_);  return r;
}

inline integer trunc(const floating& x) {
  integer r;  floating f;  mpf_trunc(f.value_, x.value_);
  mpz_set_f(**r.value_, f.value_);  return r;
}

#if 0
inline floating ceil(const floating& x, precision p) {
  floating r;  mpf_floor(r.value_, x.value_);  return r;
}

inline floating floor(const floating& x, precision p) {
  floating r;  mpf_floor(r.value_, x.value_);  return r;
}

inline floating trunc(const floating& x, precision p) {
  floating r;  mpf_floor(r.value_, x.value_);  return r;
}
#endif

} // namespace gmp

#endif // GMPXX_H
