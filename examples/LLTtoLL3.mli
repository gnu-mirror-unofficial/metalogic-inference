[— Copyright (C) 2017, 2021 Hans Åberg.

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

{— level max 100 —}
{— sublevel max 100 —}
{— unify count max 160000 —}


input std/LLT.mli


— Showing that the axioms of Łukasiewicz theory LL3 follows from the
— one axiom propositional calculus by Łukasiewicz and Tarski, theory LLT.
— Cf. Tanaka, "On Axiom Systems of Propositional Calculi. XIII".

theory LLTtoLL3.
  include theory LLT.

  — Showing that the axioms of Łukasiewicz theory LL3 follows from LLT.
  — The axioms to be showns are here named propositions LL3A1, LL3A2, and LL3A3.
  — The intermediate results are labelled lemmas.
  — By adding statements in the proof lines, one search for additional proofs.
  — The proof lines with semicolons

  — Using Łukasiewicz prefix notation:
  —   ŁC𝑨C𝑩C𝑪𝑩 same as 𝑨 ⇒ (𝑩 ⇒ (𝑪 ⇒ 𝑩)).
  —   ŁCpCqCrq, Ł⇒p⇒q⇒rq same as p ⇒ (q ⇒ (r ⇒ q)).

  — Use to show proof result in the .log file, including successive
  — reductions and substitutions:
{— trace result —}
{— trace unspecializable —}
{— trace variable label —}
—{— trace unify —}

  — Stop writing proof result to the .log file:
— {— untrace result —}

  — 2. ŁCpCqCrq.
  — ŁC𝑨C𝑩C𝑪𝑩.
  lemma TL2. formula 𝑨, 𝑩, 𝑪. 𝑨 ⇒ (𝑩 ⇒ (𝑪 ⇒ 𝑩))
  proof
    conclusion by MP: A1; A1.
—  conclusion by MP: A1.
—  conclusion by A1, MP.
  ∎


  — 3. ŁCpCqp.
  proposition LL3A1. formula 𝑨, 𝑩. 𝑨 ⇒ (𝑩 ⇒ 𝑨)
  proof
    conclusion by MP: TL2; TL2.
—  conclusion by MP: TL2.
—  conclusion by MP: A1, MP: A1.
—  conclusion by MP: A1, TL2.
—  conclusion by A1, MP.
—  conclusion by A1, TL2, MP.
  ∎


  — 4. ŁCCNrCsNtCCrCsuCCtsCtu.
  — ŁCCN𝑨C𝑩N𝑪CC𝑨C𝑩𝑫CC𝑪𝑩C𝑪𝑫.
  lemma TL4. formula 𝑨, 𝑩, 𝑪, 𝑫. (¬𝑨 ⇒ (𝑩 ⇒ ¬𝑪)) ⇒ ((𝑨 ⇒ (𝑩 ⇒ 𝑫)) ⇒ ((𝑪 ⇒ 𝑩) ⇒ (𝑪 ⇒ 𝑫)))
  proof
    conclusion by MP: A1; MP: MP; A1: TL2; A1.
—  conclusion by MP: A1, MP: A1, MP: TL2, A1.
—  conclusion by A1, TL2, LL3A1, MP.
—  conclusion by A1, LL3A1, TL2, MP.
  ∎


  — 5. ŁCCpCqrCCpqCpr.
  proposition LL3A2. formula 𝑨, 𝑩, 𝑪. (𝑨 ⇒ (𝑩 ⇒ 𝑪)) ⇒ ((𝑨 ⇒ 𝑩) ⇒ (𝑨 ⇒ 𝑪))
  proof
    conclusion by MP: LL3A1; TL4.
—  conclusion by MP: LL3A1, TL4.
—  conclusion by LL3A1, TL4, MP.
—  conclusion by A1, LL3A1, TL2, TL4, MP.
  ∎


  — 6. ŁCpp.
  lemma TL6. formula p. ŁCpp
  proof
    conclusion by MP: LL3A1; MP: LL3A1; LL3A2.
—  conclusion by MP: LL3A1, MP: LL3A1, LL3A2.
—  conclusion by LL3A1, LL3A2, MP.
—  conclusion by A1, LL3A1, LL3A2, TL2, TL4, MP.
  ∎


  — 7. ŁCCqrCCpCqrCCpqCpr.
  lemma TL7. formula p, q, r. ŁCCqrCCpCqrCCpqCpr
  proof
    conclusion by MP: LL3A2; LL3A1.
—  conclusion by MP: LL3A2, LL3A1.
—  conclusion by LL3A1, LL3A2, MP.
—  conclusion by A1, LL3A1, LL3A2, TL2, TL4, TL6, MP.
  ∎


  — 8. ŁCCqrCCpqCpr.
  lemma TL8. formula p, q, r. ŁCCqrCCpqCpr
  proof
    conclusion by MP: LL3A1; MP: TL7; LL3A2.
—  conclusion by MP: LL3A1, MP: TL7, LL3A2.
—  conclusion by LL3A1, LL3A2, TL7, MP.
—  conclusion by A1, LL3A1, LL3A2, TL2, TL4, TL6, TL7, MP.
  ∎


  — 9. ŁCCCqrCpqCCqrCpr.
  lemma TL9. formula p, q, r. ŁCCCqrCpqCCqrCpr
  proof
    conclusion by MP: TL8; LL3A2.
—  conclusion by MP: TL8, LL3A2.
—  conclusion by LL3A2, TL8, MP.
—  conclusion by A1, LL3A1, LL3A2, TL2, TL4, TL6, TL7, TL8, MP.
  ∎


  — 10. ŁCCpqCCCqrCpqCCqrCpr.
  lemma TL10. formula p, q, r. ŁCCpqCCCqrCpqCCqrCpr
  proof
    conclusion by MP: TL9; LL3A1.
—  conclusion by MP: TL9, LL3A1.
—  conclusion by LL3A1, TL9, MP.
—  conclusion by A1, LL3A1, LL3A2, TL2, TL4, TL6, TL7, TL8, TL9, MP.
  ∎


  — 11. ŁCCpqCCqrCpr.
  lemma TL11. formula p, q, r. ŁCCpqCCqrCpr
  proof
    conclusion by MP: LL3A1; MP: TL10; LL3A2.
—  conclusion by MP: LL3A1, MP: TL10, LL3A2.
—  conclusion by MP: LL3A1, MP: TL9, TL8.
—  conclusion by LL3A1, LL3A2, TL10, MP.
—  conclusion by A1, LL3A1, LL3A2, TL2, TL4, TL6, TL7, TL8, TL9, TL10, MP.
  ∎


  — 12. ŁCCCpqCprCqCpq.
  lemma TL12. formula p, q, r. ŁCCCpqCprCqCpq
  proof
    conclusion by MP: LL3A1; LL3A1.
—  conclusion by MP: LL3A1.
—  conclusion by TL2.
—  conclusion by LL3A1, MP.
—  conclusion by A1, LL3A1, LL3A2, TL2, TL4, TL6, TL7, TL8, TL9, TL10, MP.
  ∎


  — 13. ŁCCCpqCprCqCpr.
  lemma TL13. formula p, q, r. ŁCCCpqCprCqCpr
  proof
    conclusion by MP: TL12; MP: TL8; LL3A2.
—  conclusion by MP: TL12, MP: TL8, LL3A2.
—  conclusion by MP: LL3A1, TL11.
—  conclusion by MP: TL2, TL9.
—  conclusion by LL3A2, TL8, TL12, MP.
—  conclusion by A1, LL3A1, LL3A2, TL2, TL4, TL6, TL7, TL8, TL9, TL10, TL11, MP.
  ∎


  — Typo in paper: 13 and 3 (not 13).
  — 14. ŁCCpCqrCqCpr.
  lemma TL14. formula p, q, r. ŁCCpCqrCqCpr
  proof
    conclusion by MP: LL3A2; MP: MP; LL3A2: TL13; LL3A1.
—  conclusion by MP: LL3A2, MP: MP, LL3A2: TL13, LL3A1.
—  conclusion by MP: MP: LL3A2, LL3A1, TL11.
—  conclusion by MP: MP: LL3A2, TL11, TL2, TL9.
—  conclusion by MP: MP: LL3A2, TL11, TL12, TL9.
—  conclusion by LL3A1, LL3A2, TL13, MP.
—  conclusion by A1, LL3A1, LL3A2, TL2, TL4, TL6, TL7, TL8, TL9, TL10, TL11, TL12, MP.
  ∎


  — 15. ŁCCCpqrCqr.
  lemma TL15. formula p, q, r. ŁCCCpqrCqr
  proof
    conclusion by MP: LL3A1; TL11.
—  conclusion by MP: LL3A1, TL11.
—  conclusion by LL3A1, TL11, MP.
—  conclusion by A1, LL3A1, LL3A2, TL2, TL4, TL6, TL7, TL8, TL9, TL10, TL11, TL12, TL14, MP.
  ∎


  — 16. ŁCCNpCsNqCCqsCqp.
  lemma TL16. formula p, q, s. ŁCCNpCsNqCCqsCqp
  proof
    conclusion by MP: LL3A1; MP: TL4; TL14.
—  conclusion by MP: LL3A1, MP: TL4, TL14.
—  conclusion by LL3A1, TL4, TL14, MP.
—  conclusion by A1, LL3A1, LL3A2, TL2, TL4, TL6, TL7, TL8, TL9, TL10, TL11, TL12, TL14, TL15, MP.
  ∎


  — 17. ŁCCsCNpNqCCqsCqp.
  lemma TL17. formula p, q, s. ŁCCsCNpNqCCqsCqp
  proof
    conclusion by MP: TL16; MP: TL14; TL11.
—  conclusion by MP: TL16, MP: TL14, TL11.
—  conclusion by MP: TL14, MP: TL16, TL8.
—  conclusion by TL11, TL14, TL16, MP.
—  conclusion by A1, LL3A1, LL3A2, TL2, TL4, TL6, TL7, TL8, TL9, TL10, TL11, TL12, TL14, TL15, TL16, MP.
  ∎


  — Typo in paper: 6 (not 14) and 17: 17 s/CNpNq * 6 p/CNpNq.
  — 18. ŁCCqCNpNqCqp.
  lemma TL18. formula p, q. ŁCCqCNpNqCqp
  proof
    conclusion by MP: TL6; TL17.
—  conclusion by MP: TL6, TL17.
—  conclusion by A1, LL3A1, LL3A2, TL2, TL4, TL6, TL7, TL8, TL9, TL10, TL11, TL12, TL14, TL15, TL16, TL17, MP.
  ∎


  proposition LL3A3. formula 𝑨, 𝑩. (¬𝑨 ⇒ ¬𝑩) ⇒ (𝑩 ⇒ 𝑨)
  proof
    conclusion by MP: TL18; TL15.
—  conclusion by MP: TL18, TL15.
—  conclusion by MP: MP, TL15: TL6, TL17.
—  conclusion by A1, LL3A1, LL3A2, TL2, TL4, TL6, TL7, TL8, TL9, TL10, TL11, TL12, TL14, TL15, TL16, TL17, TL18, MP.
  ∎

end theory LLTtoLL3.
