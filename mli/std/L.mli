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

theory L. -- Propositional calculus (Logic), Mendelson, p.31:

  formal system.
    atom 𝕗, 𝕥. -- False, true. Not in core of theory L.
  
    formula A, B, C.

  -- These axioms are called A1-A3 in Mendelson:
  axiom L1. A ⇒ (B ⇒ A).
  axiom L2. (A ⇒ (B ⇒ C)) ⇒ ((A ⇒ B) ⇒ (A ⇒ C)).
  axiom L3. (¬ B ⇒ ¬ A) ⇒ ((¬ B ⇒ A) ⇒ B).
    
  -- Modus ponens:
  rule MP. A, A ⇒ B ⊢ B.

  -- “deduction theorem” “1.8”
  -- Entered as an axiom in the absence of the appropriate metatools.
  postulate DT. formula A, B. (A ⊢ B) ⊢ A ⇒ B.

  definition D1. A ∧ B ≔ ¬(A ⇒ ¬ B).  
  definition D2. A ∨ B ≔ (¬ A) ⇒ B.
  definition D3. A ⇔ B ≔ (A ⇒ B) ∧ (B ⇒ A).
  axiom D4. 𝕥.
  definition D5. 𝕗 ≔ ¬ 𝕥.

  rule A1. A, B ⊢ A ∧ B.  -- Test only.

  end formal system.

end theory L.
