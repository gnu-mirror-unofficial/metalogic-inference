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


theory LLT. — Logic: Propositional calculus by Łukasiewicz and Tarski.

  formal system.
    atom 𝕗, 𝕥. — False, true. Not in core of theory.
    formula 𝑨, 𝑩, 𝑪, 𝑫, 𝑬, 𝑭, 𝑮, 𝑯.

  axiom A1. ((𝑨 ⇒ (𝑩 ⇒ 𝑨)) ⇒ (((¬𝑪 ⇒ (𝑫 ⇒ ¬𝑬)) ⇒ ((𝑪 ⇒ (𝑫 ⇒ 𝑭)) ⇒ ((𝑬 ⇒ 𝑫) ⇒ (𝑬 ⇒ 𝑭)))) ⇒ 𝑮)) ⇒ (𝑯 ⇒ 𝑮).

  — Modus ponens
  rule MP. 𝑨, 𝑨 ⇒ 𝑩 ⊢ 𝑩.

  — Deduction theorem
  postulate DT. formula sequence 𝜞 formula 𝑨, 𝑩. 𝜞, 𝑨 ⊢ 𝑩 ⊩ 𝜞 ⊢ 𝑨 ⇒ 𝑩.

  definition D1. 𝑨 ∧ 𝑩 ≔ ¬(𝑨 ⇒ ¬𝑩).  
  definition D2. 𝑨 ∨ 𝑩 ≔ ¬𝑨 ⇒ 𝑩.
  definition D3. 𝑨 ⇔ 𝑩 ≔ (𝑨 ⇒ 𝑩) ∧ (𝑩 ⇒ 𝑨).
  axiom D4. 𝕥.
  definition D5. 𝕗 ≔ ¬𝕥.

  end formal system.

end theory LLT.

