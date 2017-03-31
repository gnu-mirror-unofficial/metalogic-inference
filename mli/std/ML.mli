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

theory ML. -- MetaLogic theory

[* Names starting with ~ indicates a metaquantity:
   ~predicate     metapredicate; accepts only formulas as argument.
*]
  formal system.
  -- binary infix ~predicate * ≡ *
  
[*
  -- Extension of premises and theory.
  -- “extension”.
  axiom ext. formula A theory T, U formulaset S, R.
    R ~⊂ S, U ~⊂ T, (R ⊢_U A) ⊢ (S ⊢_T A).
  
  -- Relation between body_X and head_X.
  axiom BH. rule X theory T formulaset S.
    (S ⊢_T body_X) ⊢ (S ⊢_T head_X).
  
  -- Formulaset recursion (not currently needed).
  axiom FS. formula A formulaset S, As rule X theory T.
    (S ⊢_T As use FS), (S ⊢_T A) ⊢ (S ⊢_T As:>A).
  
  
  -- Proof induction.
  axiom PI. theorem T, metapredicate P, postulate A.
    A ~in theory(T), (P(body_A) ⊢ P(head_A)), P(body_T) ⊢ P(head_T).
*]  


  -- Axioms for metaequality (MEQ) * ≡ * (a binary infix metapredicate):
  axiom ref. formula A.
    A ≡ A. -- Reflexivity.
  rule sub1. formula A, B ~formula P.
    A ≡ B, P(A, A) ⊢ P(A, B). -- Substitutivity.
[*
  rule sub2. formula A, B, X, Y ~formula P.
    A ≡ B, P[X.A, Y.A] ⊢ P[X.A, Y.B]. -- Substitutivity.
*]
  -- Prove left hand side:
  rule PL. formula A, B. B, A ≡ B ⊢ A. 
  -- Prove right hand side:
  rule PR. formula A, B. A, A ≡ B ⊢ B.
  
-- axiom P1. ~predicate P. P(X, Y) ≡ (Y ≡ X).

  end formal system.


[*
theorem sym. -- “symmetry”.
  formula A, B.
    A ≡ B ⊢ B ≡ A. -- Symmetry.
proof.
  1. A ≡ B by premise.
  2. formula X, Y. define P(X, Y) ≔ Y ≡ X.
  3. P(A, A) by ref.
  4. P(A, B) by sub; 1, 3.
  conclusion by 4.
∎
 
theorem tran. -- “transitivity”.
  formula A, B, C.
    A ≡ B, B ≡ C ⊢ A ≡ C. -- Transitivity.
proof.
  1. A ≡ B by premise.
  2. B ≡ C by premise.
  3. object X, Y. define P(X, Y) ≔ Y ≡ C.
  4. P(B, B) by 2.
  5. B ≡ A by sym; 1.
  6. P(B, A) by sub; 5, sub.
  conclusion by 6.
∎

theorem prov. -- “provability”
  formula A, B theory T formulaset S.
    A ≡ B, (S ⊢_T A) ⊢ (S ⊢_T B). -- Provability.
proof.
*]

end theory ML.

