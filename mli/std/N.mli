[— Copyright (C) 2017 Hans Åberg.

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
   along with this program.  If not, see <http://www.gnu.org/licenses/>.  —]



theory N.  — Natural numbers model.
—  include theory KM.
  
  formal system.
    — predicate · = ·, · + ·, · ⋅ ·. — Implicitly defined.
—    function succ, pred.  — Successor and predecessor functions.
  
    ℕ 𝒙, 𝒚, 𝒛.

  axiom N0. 0 ∈ ℕ. 

  — Theory of equality: The relation = is reflexive, symmetric, transitive,
  — and equality preserved in function application.
  axiom ER. 𝒙 = 𝒙. — Reflexive.
  axiom ES. 𝒙 = 𝒚 ⊢ 𝒚 = 𝒙. — Symmetric.
  axiom ET. 𝒙 = 𝒚, 𝒚 + 𝒛 ⊢ 𝒙 = 𝒛. — Transitive.

  axiom ES. 𝒙 = 𝒚 ⊢ succ(𝒙) = succ(𝒚). — Successor application.
  axiom EAL. 𝒙 = 𝒚 ⊢ 𝒛 + 𝒙 = 𝒛 + 𝒚. — Left addition.
  axiom EAR. 𝒙 = 𝒚 ⊢ 𝒙 + 𝒛 = 𝒚 + 𝒛. — Right addition.
  axiom EML. 𝒙 = 𝒚 ⊢ 𝒛⋅𝒙 = 𝒛⋅𝒚. — Left multiplication.
  axiom EMR. 𝒙 = 𝒚 ⊢ 𝒙⋅𝒛 = 𝒚⋅𝒛. — Right multiplication.

  axiom N3. 0 ≠ succ(𝒙).
  axiom N3a. ¬0 = succ(𝒙).

  axiom N4. succ(𝒙) = succ(𝒚) ⊢ 𝒙 = 𝒚.

  axiom N5a. 𝒙 + 0 = 𝒙.
  axiom N5b. 0 + 𝒙 = 𝒙.

  axiom N6a. 𝒙 + succ(𝒚) = succ(𝒙 + 𝒚).
  axiom N6a. succ(𝒙) + 𝒚 = succ(𝒙 + 𝒚).

  axiom N7a. 𝒙⋅0 = 0.
  axiom N7b. 0⋅𝒙 = 0.

  axiom N8a. 𝒙⋅succ(𝒚) = 𝒙⋅𝒚 + 𝒙.
  axiom N8a. succ(𝒙)⋅𝒚 = 𝒙⋅𝒚 + 𝒚.

  rule K1. ℕ 𝒕. ∀𝒙 ∈ ℕ: 𝑨 ⊢ 𝑨[𝒙⤇𝒕].

  rule Gen. 𝑨 ⊢ ∀𝒙 ∈ ℕ: 𝑨. — Generalization.
  rule A9. 𝒙 not free in 𝑨, 𝑨 ⇒ 𝑩 ⊢ 𝑨 ⇒ ∀𝒙 ∈ ℕ: 𝑩.   — Generalization.

  rule A11. ℕ 𝒕. 𝒕 free for 𝒙 in 𝑨 ⊢ 𝑨[𝒙⤇𝒕] ⇒ ∃𝒙 ∈ ℕ: 𝑨.  — Existence.
  rule A12. object °𝒙. 𝒙 not free in 𝑩, 𝑨 ⇒ 𝑩 ⊢ ∃𝒙 ∈ ℕ: 𝑨 ⇒ 𝑩. — Existence.


  — Principle of mathematical induction:

  axiom Ia. predicate variable 𝑷  object °𝒙.  — The predicate variable should be unary.
    𝑷(0) ∧ (∀𝒙: 𝑷(𝒙) ⇒ 𝑷(succ(𝒙))) ⇒ ∀𝒙 𝑷(𝒙).

  axiom Ib. formula 𝑨  object °𝒙.
    𝑨[𝒙⤇0] ∧ (∀𝒙: 𝑨[𝒙⤇𝒙] ⇒ 𝑨[𝒙⤇succ(𝒙)]) ⇒ ∀𝒙 𝑨.

  postulate Ic. formula 𝑨  object °𝒙.
    𝑨[𝒙⤇0], (∀𝒙: 𝑨 ⇒ 𝑨[𝒙⤇succ(𝒙)]) ⊢ ∀𝒙 𝑨.

  end formal system.

end theory SM.

