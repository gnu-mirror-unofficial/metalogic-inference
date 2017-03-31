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

#include "gmp.hh"

#include <sstream>


namespace gmp {


  // Class integer:
static int digit_value_in_base(int c, int base) {
  int digit;

  if (isdigit(c))
    digit = c - '0';
  else if (islower(c))
    digit = c - 'a' + 10;
  else if (isupper(c))
    digit = c - 'A' + 10;
  else
    return -1;

  if (digit < base)
    return digit;
  return -1;
}


size_t integer::read(std::istream& stream, int base) {
#if 0
  detach(); // Remove *this from reference cluster.
  mpz_ptr x = **value_;
  char *str;
  size_t alloc_size, str_size;
  int c;
  int negative;
  mp_size_t xsize;
  size_t nread;

  nread = 0;

  /* Skip whitespace.  */
  do
    {
      c = stream.get();
      nread++;
    }
  while (isspace(c));

  negative = 0;
  if (c == '-')
    {
      negative = 1;
      c = stream.get();
      nread++;
    }

  if (digit_value_in_base (c, base == 0 ? 10 : base) < 0)
    return 0;     /* error if no digits */

  /* If BASE is 0, try to find out the base by looking at the initial
     characters.  */
  if (base == 0)
    {
      base = 10;
      if (c == '0')
  {
    base = 8;
    c = stream.get();
    nread++;
    if (c == 'x' || c == 'X')
      {
        base = 16;
        c = stream.get();
        nread++;
      }
    else if (c == 'b' || c == 'B')
      {
        base = 2;
        c = stream.get();
        nread++;
      }
  }
    }

  /* Skip leading zeros.  */
  while (c == '0')
    {
      c = stream.get();
      nread++;
    }

  alloc_size = 100;
  str = (char *) (*__gmp_allocate_func) (alloc_size);
  str_size = 0;

  for (;;)
    {
      int dig;
      if (str_size >= alloc_size)
  {
    size_t old_alloc_size = alloc_size;
    alloc_size = alloc_size * 3 / 2;
    str = (char *) (*__gmp_reallocate_func) (str, old_alloc_size, alloc_size);
  }
      dig = digit_value_in_base (c, base);
      if (dig < 0)
  break;
      str[str_size++] = dig;
      c = stream.get();
    }

  stream.unget();

  /* Make sure the string is not empty, mpn_set_str would fail.  */
  if (str_size == 0)
    {
      x->_mp_size = 0;
      (*__gmp_free_func) (str, alloc_size);
      return nread;
    }

  xsize = (((mp_size_t) (str_size / __mp_bases[base].chars_per_bit_exactly))
     / __GMP_BITS_PER_MP_LIMB + 2);
  if (x->_mp_alloc < xsize)
    _mpz_realloc (x, xsize);

  /* Convert the byte array in base BASE to our bignum format.  */
  xsize = mpn_set_str (x->_mp_d, (unsigned char *) str, str_size, base);
  x->_mp_size = negative ? -xsize : xsize;

  (*__gmp_free_func) (str, alloc_size);
  return str_size + nread;
#else
  return 0;
#endif
}


  // Class rational:

rational::rational(const char* x, int base) {
  mpq_init(value_);
  std::istringstream iss(x);
  read(iss, base);
}

std::string rational::str(int base) const {
  std::pair<integer, rational> p = div_trunc(*this);
  if (p.first != 0L) {
    p.second = abs(p.second);
    return p.first.str(base) + " " + p.second.get_num().str(base)
      + "/" + p.second.get_den().str(base);
  }
  else
    return p.second.get_num().str(base)
      + "/" + p.second.get_den().str(base);
}

size_t rational::read(std::istream& is, int base) {
  integer n, p, q; // Parsing rational number written "n p/q"; does not
  // error the case when n != 0 and p is negative, or q is negative.
  size_t n1 = 0, n2, n3;
  bool integral_part = false;
  n2 = p.read(is, base);
  if (n2 == 0)  return 0;
  std::istream::int_type ch = is.get();
  if (!is)  return 0;
  if (ch == ' ') {
    integral_part = true;
    n1 = n2;
    p.swap(n);
    n2 = p.read(is, base);
    if (n2 == 0)  return 0;
    ch = is.get();
    if (!is)  return 0;
  }
  if (ch != '/')  return 0;
  n3 = q.read(is, base);
  if (n3 == 0)  return 0;
  mpq_set_num(value_, **p.value_);
  mpq_set_den(value_, **q.value_);
  canonicalize();
  if (integral_part) {
    if (n >= 0L)
      mpq_add(value_, rational(n).value_, value_);
    else
      mpq_sub(value_, rational(n).value_, value_);
  }
  return n1 + (integral_part == true) + n2 + 1 + n3;
}


  // Class floating:

#if 0
floating::set_local::set_local(floating::precision p)
 : limb_prec_(__gmp_default_fp_limb_precision) {
  mpf_set_default_prec(p.prec_);
}
#else
  floating::set_local::set_local(floating::precision p)
   {
    mpf_set_default_prec(p.prec_);
  }
#endif

floating::set_local::~set_local() {
//  __gmp_default_fp_limb_precision = limb_prec_;
}


size_t floating::read(std::istream& is, int base) {
  char *str;
  size_t alloc_size, str_size;
  int c;
  size_t retval;
  size_t nread;

  alloc_size = 100;
//  str = (char *) (*__gmp_allocate_func) (alloc_size);
  str_size = 0;
  nread = 0;

  /* Skip whitespace.  */
  do
    {
      c = is.get();
      nread++;
    }
  while (isspace (c));

  for (;;)
    {
      if (str_size >= alloc_size)
  {
    size_t old_alloc_size = alloc_size;
    alloc_size = alloc_size * 3 / 2;
//    str = (char *) (*__gmp_reallocate_func) (str, old_alloc_size, alloc_size);
  }
      if (c == EOF || isspace (c))
  break;
      str[str_size++] = c;
      c = is.get();
    }
  is.unget();

  if (str_size >= alloc_size)
    {
      size_t old_alloc_size = alloc_size;
      alloc_size = alloc_size * 3 / 2;
//      str = (char *) (*__gmp_reallocate_func) (str, old_alloc_size, alloc_size);
    }
  str[str_size] = 0;

  retval = mpf_set_str (value_, str, base);
  if (retval == -1)
    return 0;     /* error */

//  (*__gmp_free_func) (str, alloc_size);
  return str_size + nread;
}

std::string floating::str(int base, size_t digits) const {
  mp_exp_t ex;
  char* cs = mpf_get_str(0, &ex, base, digits, value_);
  if (cs[0] == '\0') {
    std::free(cs);
    return "0.0e0";
  }
  --ex; // For mantissa with leading (ahead of '.') non-zero digit.
  std::string s;
  int pos = 0; // Position in cs.
  if (cs[pos] == '-') { s += '-'; ++pos; }
  s += cs[pos]; ++pos;
  if (cs[pos] != '\0') {
    s += '.';
    s.insert(pos + 1, cs + pos);
  }
  std::free(cs);
  s += (base <= 10)? "e" : "ⅇ";
  std::ostringstream oss;
  oss << ex;
  s += oss.str();
  return s;
}


} // namespace gmp

