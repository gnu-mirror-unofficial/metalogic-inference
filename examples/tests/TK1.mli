[* Copyright (C) 2017 Hans Åberg.

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
   along with this program.  If not, see <http://www.gnu.org/licenses/>.  *]

insert std/K.mli

theory TK1. -- Test K (predicate theory).
  include theory K.

[*
trace_result -- trace_proof
trace_variable_type  trace_bind
trace_substitute  trace_unify
*]
[*
-- Mendelson, p. 60.
lemma X2. formula A, C.
  A, ∀x A ⇒ C ⊢ ∀x C.
proof.
--  conclusion by Gen, premise, MP.
  1. A by premise.
  2. ∀x A by 1, Gen.
  3. ∀x A ⇒ C by premise.
  4. C by 2, 3, MP.
  conclusion by 4, Gen.
∎
*]


trace_result -- trace_proof
trace_variable_type  trace_bind
[*trace_unify  trace_substitute
*]


-- Mendelson, p. 62.
lemma X3. formula A. --  metaobject x, y.
  ∀x, y A ⊢ ∀y, x A.
proof.
  conclusion by Gen, premise, K1a.
[*
  1. ∀x, y A by premise.
  2. ∀x, y A ⊢ ∀y A by K1a.
-- K1a. ∀x A ⊢ A[x.t]
  3. ∀y A by 2, 1.
  4. ∀y A ⊢ A by K1a.
  conclusion by 3, 4, Gen.
*]
[*
  1. ∀x, y A by premise.
  2. ∀x, y A ⊢ (∀y A) by K1a.
--  2. ∀x, y A ⊢ (∀y A)[x.x] by K1a.
  3. ∀y A by 2, 1.
  4. ∀y A ⊢ A by K1a.
--  4. ∀y A ⊢ A[y.y] by K1a.
  5. A by 3, 4.
  6. ∀x A by 5, Gen.
  7. ∀y, x A by 6, Gen.
  conclusion by 7.
*]
∎

--untrace_all
[*
lemma X3a. formula A. --  metaobject x, y.
  ∀x, y A ⇒ ∀y, x A.
proof.
  conclusion by DT; Gen; Gen; K1a.
--  conclusion by Gen, K1a, DT.
∎
*]

trace_result trace_proof
trace_variable_type  trace_bind
trace_unify  trace_substitute
[**]

lemma X3b. formula A. --  metaobject x, y.
  ∀x, y A ⇒ ∀y, x A.
proof.
  conclusion by DT; “X3”. -- Fails proof.
--  conclusion by Gen, K1a, DT. -- Proves.
∎


-- rule K1a. ∀x A ⊢ A[x.t].

untrace_all
[*
trace_result  trace_proof
trace_variable_type  trace_bind
trace_unify  trace_substitute
*]

[*
lemma X4. formula A  object x.
  ∀x A ⊢ ∀y: A[x.y].
proof.
  conclusion by premise.
∎
*]

untrace_all

end theory TK1.

