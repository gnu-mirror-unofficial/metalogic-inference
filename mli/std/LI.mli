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


theory LI. — Logic: Intuitionistic propositional calculus by Kleene, p. 82, 101, cf. Mendelson, p. 43.
[— Kleene numbering (second in each pair):
    A1 1a,  A2 1b,  A3 4a,  A4 4b,  A5 3,  A6 5a,  A7 5b,  A8 6,  A9 7,  A10 8I,  MP 2.
—]

  formal system.
    atom 𝕗, 𝕥. — False, true. Not in core of theory.
    formula 𝑨, 𝑩, 𝑪.

  axiom A1. 𝑨 ⇒ (𝑩 ⇒ 𝑨).
  axiom A2. (𝑨 ⇒ (𝑩 ⇒ 𝑪)) ⇒ ((𝑨 ⇒ 𝑩) ⇒ (𝑨 ⇒ 𝑪)).
  axiom A3. 𝑨 ∧ 𝑩 ⇒ 𝑨.
  axiom A4. 𝑨 ∧ 𝑩 ⇒ 𝑩.
  axiom A5. 𝑨 ⇒ (𝑩 ⇒ (𝑨 ∧ 𝑩)).
  axiom A6. 𝑨 ⇒ 𝑨 ∨ 𝑩.
  axiom A7. 𝑩 ⇒ 𝑨 ∨ 𝑩.
  axiom A8. (𝑨 ⇒ 𝑪) ⇒ ((𝑩 ⇒ 𝑪) ⇒ (𝑨 ∨ 𝑩 ⇒ 𝑪)).
  axiom A9. (𝑨 ⇒ 𝑩) ⇒ ((𝑨 ⇒ ¬𝑩) ⇒ ¬𝑨).
  axiom A10. ¬𝑨 ⇒ (𝑨 ⇒ 𝑩).

  — Modus ponens
  rule MP. 𝑨, 𝑨 ⇒ 𝑩 ⊢ 𝑩.

  — Deduction theorem
  postulate DT. formula sequence 𝜞 formula 𝑨, 𝑩. 𝜞, 𝑨 ⊢ 𝑩 ⊩ 𝜞 ⊢ 𝑨 ⇒ 𝑩.

  definition D1. 𝑨 ⇔ 𝑩 ≔ (𝑨 ⇒ 𝑩) ∧ (𝑩 ⇒ 𝑨).
  axiom D2. 𝕥.
  axiom D3. 𝕗 ⇒ 𝑨.

  end formal system.

end theory LI.

