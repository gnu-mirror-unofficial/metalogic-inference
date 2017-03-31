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

theory S.  -- Natural numbers, Mendelson, p.103:
  include theory K.
  
  formal system.
    constant O -- Letter O, ¬ a digit!
    -- predicate · = ·, · + ·, · “·” ·
    function s.
  
    term x, y, z
    formula P  -- Should be unary predicate variable.
    formula A.

  axiom S1. x = y ∧ x = z ⇒ y = z.
  axiom S1b. x = y ∧ y = z ⇒ x = z. -- Test only.
  axiom S2. x = y ⇒ s(x) = s(y).
  axiom S3. ¬ 0 = s(x).
  axiom S4. s(x) = s(y) ⇒ x = y.
  axiom S5. x + 0 = x.
  axiom S5a. x + 0 = 0 + x.
  axiom S6. x + s(y) = s(x + y).
  axiom S7. x · 0 = 0.
  axiom S8. x · s(x) = x · y + x.
  -- Principle of mathematical induction:
  axiom S9a. predicate variable A.
    A(0) ∧ (∀x: A(x) ⇒ A(s(x))) ⇒ ∀x A(x).
  axiom S9b. metaobject x.
    A[x.0] ∧ (∀x: A[x.x] ⇒ A[x.s(x)]) ⇒ ∀x A.
  postulate S9c. metaobject x.
    A[x.0], (∀x: A ⇒ A[x.s(x)]) ⊢ ∀x A.

  definition IsSet. predicate M. -- Is a set.
    M(x) ≔ ∃y: x ∈ y.

  end formal system.

end theory S.

