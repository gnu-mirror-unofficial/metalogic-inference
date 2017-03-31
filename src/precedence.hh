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

#ifndef header_precedence_hh
#define header_precedence_hh

#include "MLI.hh"

namespace mli {

enum {
  first_prec = 10,

  metapredicate_argument_prec,

  inference_prec,
  formula_definition_prec,

  metaor_prec,
  metaand_prec,
  metanot_prec,

  predicate_argument_prec,

  free_prec,

  identical_prec,
  term_definition_prec,

  quantizer_prec,  // all x: ...

  equivalent_prec,
  implies_prec,
  impliedby_prec = implies_prec,
  or_prec,
  and_prec,
  not_prec,

  simple_quantizer_prec,  // all x A

  equal_prec,

  function_argument_prec,

  in_prec,
  is_set_prec,
  member_list_set_prec,
  implicit_set_prec = member_list_set_prec,
  subset_prec,
  psubset_prec,

  mapto_prec,

  vector_prec,
  list_prec,
  bracket_prec,
  list_concat_prec,

  plus_prec,
  minus_prec = plus_prec,
  mult_prec,
  divide_prec = mult_prec,
  unary_minus_prec,

  substitution_formula_prec,
 
  last_prec
};

// Precedence p, associativity a, fixity f:
#define op_prec(p, a, f) \
  const operator_precedence p ## _oprec = \
    operator_precedence(p ## _prec, precedence_root::a, precedence_root::f)

op_prec(metapredicate_argument, non, enfix);

op_prec(inference, non, infix);
op_prec(formula_definition, non, infix);

op_prec(metaor, left, infix);
op_prec(metaand, left, infix);
op_prec(metanot, right, prefix);

op_prec(predicate_argument, non, enfix);

op_prec(free, non, infix);

op_prec(identical, non, infix);
op_prec(term_definition, non, infix);

op_prec(quantizer, right, prefix);

op_prec(equivalent, left, infix);
op_prec(implies, non, infix);
op_prec(impliedby, non, infix);
op_prec(or, left, infix);
op_prec(and, left, infix);
op_prec(not, right, prefix);

op_prec(simple_quantizer, right, prefix);

op_prec(equal, non, infix);

op_prec(function_argument, non, enfix);

op_prec(in, non, infix);
op_prec(is_set, right, prefix);
op_prec(member_list_set, non, enfix);
op_prec(implicit_set, non, enfix);
op_prec(subset, non, infix);
op_prec(psubset, non, infix);

op_prec(mapto, non, infix);

op_prec(vector, left, enfix);
op_prec(list, left, enfix);
op_prec(bracket, left, enfix);

op_prec(list_concat, left, infix);

op_prec(plus, left, infix);
op_prec(minus, left, infix);
op_prec(mult, left, infix);
op_prec(divide, left, infix);
op_prec(unary_minus, right, prefix);

op_prec(substitution_formula, non, infix);
 
#undef op_prec


} // namespace mli

#endif // header_precedence_h



