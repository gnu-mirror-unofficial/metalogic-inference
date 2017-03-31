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

insert std/S.mli

theory TS1.  -- Test theory S (number theory).
  include theory S.

[*
trace_result  trace_proof  trace_variable_type  trace_bind
 trace_unify  trace_substitute
*]
[* A
-- Should be:
-- A(0), ∀x: A(x) ⇒ A(s(x)) ⊢ ∀x A(x).
lemma IR. -- Induction Rule. 
  predicate variable A.
  A(0) ∧ (∀x: A(x) ⇒ A(s(x))) ⊢ ∀x A(x).
proof. conclusion by premise, S9a, MP. ∎
[*
proof. conclusion by MP; premise, S9a. ∎
proof. 
  P1. A(0) ∧ (∀x: A(x) ⇒ A(s(x))) by premise.
  conclusion by MP; S9, P1.
∎
*]

[*
trace_result  trace_proof  trace_unify  trace_substitute
trace_variable_type  trace_bind
*]

lemma IR1.
  predicate variable A.
  A(0), (∀x: A(x) ⇒ A(s(x))) ⊢ ∀x A(x).
proof.
  1. A(0) by premise.
  2. ∀x: A(x) ⇒ A(s(x)) by premise.
  3. A(0) ∧ (∀x: A(x) ⇒ A(s(x))) by A1, 1, 2.
  conclusion by IR, 3.
[*
  3. A(0) ∧ (∀x: A(x) ⇒ A(s(x))) by A1; 1, 2.
  conclusion by IR; 3.
*]
∎

A *]

 trace_result -- trace_proof
 trace_variable_type  trace_bind
[* trace_unify
 trace_substitute  trace_split
*]

lemma X1. ∀x: 0 + x = x.
proof.
  conclusion by S9c; S5, Gen; DT; MP; A1, S1b; S6, MP; S2.
--  conclusion by S9c; S5, Gen; DT; A1, S1b, S6, MP, S2. -- At 5 MB memory.
--  conclusion by S9c; S5, Gen; DT, A1, S1b, S6, MP, S2. -- At 20 MB memory.
--  conclusion by S9c; S5, Gen, DT, A1, S1b, S6, MP, S2. -- At 20 MB memory.
[*
  definition D5. predicate B  term t.
    B(t) ≔ 0 + t = t.
  1. B(0) by D5, S5.
  claim a. term x. B(x) ⊢ B(s(x)).
  proof.
    a1. 0 + x = x by D5, premise.
    a4. 0 + s(x) = s(x) by MP, A1, S1b, S2, a1, S6.
    conclusion by D5, a4.
[*
  -- Works when weight increases by product of size of alternatives ∧
  -- number of metaand goals:
    a1. 0 + x = x by D5, premise.
    a4. 0 + s(x) = s(x) by MP, A1, S1b, S2, a1, S6.
    conclusion by D5, a4.
  -- Does not work (too much memory).
    conclusion by D5, MP, A1, S1b, S2, premise, S6.
  -- Can be handled if a metaand_sort() is implemented.
    a3. s(0 + x) = s(x) by MP, S2, D5, premise.
    conclusion by D5, MP, A1, S1b, a3, S6.
  -- Original, deterministic proof.
    a1. 0 + x = x by D5, premise.
    a2. 0 + s(x) = s(0 + x) by S6.
    a3. s(0 + x) = s(x) by MP; S2, a1.
    a4. 0 + s(x) = s(x) by MP; A1, S1b, a3, a2.
    conclusion by D5, a4.
*]
  ∎
  -- Works when weight increases by product of size of alternatives ∧
  -- number of metaand goals:
  conclusion by D5, IR1, 1, Gen, DT, a.
[*
  4. ∀x B(x) by IR1, 1, Gen, DT, a.
  conclusion by D5, 4.
  -- Original, deterministic proof:
  2. object x. B(x) ⇒ B(s(x)) by DT, a.
  3. ∀x: B(x) ⇒ B(s(x)) by Gen, 2.
  4. ∀x B(x) by IR1, 1, 3.
  conclusion by D5, 4.
*]
*]
∎
[**]
--untrace_all

trace_all
untrace_all

end theory TS1.

