[— Copyright (C) 2017, 2021-2022 Hans Åberg.

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
{— sublevel max 10000 —}
{— unify count max 600000 —}


input std/SM.mli
input std/Eq.mli
input std/IR.mli


theory TS1.  — Test theory S (number theory).
  include theory SM.
  include theory Eq.
  include theory IR.

{— thread count 0 —}

{— trace result —}
{— trace unspecializable —}
{— trace variable label —}
—{— trace unify —}

  function constant s.

  lemma T1a. object 𝒙.
    𝒙 = 𝒙
[—
  by MP: S5; MP: S5; S1.
—]
  proof
    1. 𝒙 + 0 = 𝒙 by S5.
    2. 𝒙 + 0 = 𝒙 ⇒ (𝒙 + 0 = 𝒙 ⇒ 𝒙 = 𝒙) by S1.
    3. 𝒙 + 0 = 𝒙 ⇒ 𝒙 = 𝒙 by MP: 1; 2.
    by MP: 1; 3.
  ∎


  lemma T1b. object 𝒙, 𝒚.
    𝒙 = 𝒚 ⇒ 𝒚 = 𝒙
—  by MP: T1a; PI: S1.
  — Proof alternative forms:
— by MP: T1a; PI: S1.
— by MP: T1a; PI: S1.
  result by MP: T1a; PI: S1.
[—
  proof
    1. 𝒙 = 𝒚 ⇒ (𝒙 = 𝒙 ⇒ 𝒚 = 𝒙) by S1.
    2. 𝒙 = 𝒙 ⇒ (𝒙 = 𝒚 ⇒ 𝒚 = 𝒙) by PI: 1.
    by MP: T1a; 2.
  ∎
—]

  lemma T1B. object 𝒙, 𝒚.
    𝒙 = 𝒚 ⊢ 𝒚 = 𝒙
  by MP: premise T1B; T1b. — T1b, MP, premise.


  lemma T1c. object 𝒙, 𝒚, 𝒛.
    𝒙 = 𝒚 ⇒ (𝒚 = 𝒛 ⇒ 𝒙 = 𝒛)
  by ICh: T1b; S1.
[—
  proof
    1. 𝒚 = 𝒙 ⇒ (𝒚 = 𝒛 ⇒ 𝒙 = 𝒛) by S1
    2. 𝒙 = 𝒚 ⇒ 𝒚 = 𝒙 by T1b
    by ICh: 2; 1.
  ∎
—]

  lemma T1C. object 𝒙, 𝒚, 𝒛.
    𝒙 = 𝒚, 𝒚 = 𝒛 ⊢ 𝒙 = 𝒛
  by MP: premise T1C; MP: premise T1C; T1c. — premise, T1c, MP.


  lemma T1d. object 𝒙, 𝒚, 𝒛.
    𝒙 = 𝒛 ⇒ (𝒚 = 𝒛 ⇒ 𝒙 = 𝒚)
  by PI: ICh: T1b; PI: T1c.
[—
  proof
    1. 𝒙 = 𝒛 ⇒ (𝒛 = 𝒚 ⇒ 𝒙 = 𝒚) by T1c.
    2. 𝒛 = 𝒚 ⇒ (𝒙 = 𝒛 ⇒ 𝒙 = 𝒚) by PI: 1.
    3. 𝒚 = 𝒛 ⇒ 𝒛 = 𝒚 by T1b.
    4. 𝒚 = 𝒛 ⇒ (𝒙 = 𝒛 ⇒ 𝒙 = 𝒚) by ICh: 3; 2.
    by PI: 4.
  ∎
—]


  lemma T1D. object 𝒙, 𝒚, 𝒛.
    𝒙 = 𝒛, 𝒚 = 𝒛 ⊢ 𝒙 = 𝒚
  by MP: premise T1D; MP: premise T1D; T1d. — T1d, MP, premise.


  — Induction Rule.

  lemma IR1. object °𝑥 predicate variable 𝑷.
    𝑷(0), ∀𝑥: 𝑷(𝑥) ⇒ 𝑷(s(𝑥)) ⊢ ∀𝑥 𝑷(𝑥)
  by MP: CI; S9a. — MP: CI, S9a.

  {— expand_implicit_premise —}

  lemma IR2. predicate variable 𝑷 object °𝒙.
    𝑷(0), 𝑷(𝒙) ⇒ 𝑷(s(𝒙)) ⊢⁽¹𝒙⁾ 𝑷(𝒙)
  by K1: IR1: Gen. — K1, Gen, IR1, premise.

  — Induction Rule
  lemma IR. predicate variable 𝑷 object °𝒙.
    𝑷(0); 𝑷(𝒙) ⊢ 𝑷(s(𝒙)) ⊩ 𝑷(𝒙)
  by IR2: premise ⊢₀; DT: premise ⊢₁. — IR2, DT.
[—
  lemma IR. predicate variable 𝑷 formula sequence 𝜞 object °𝒙.
    𝒙 not free in 𝜞; 𝜞 ⊢ 𝑷(0); 𝜞, 𝑷(𝒙) ⊢₁ 𝑷(s(𝒙)) ⊩ 𝜞 ⊢ 𝑷(𝒙)
    𝜞 ⊢ 𝑷(0); 𝜞, 𝑷(𝒙) ⊢₁ 𝑷(s(𝒙)) ⊩ 𝜞 ⊢⁽𝒙⁾ 𝑷(𝒙)

—]

{— trace result —}
{— trace unspecializable —}
{— trace variable label —}

  lemma T1e. object 𝒕, 𝒓, 𝒔.
    𝒕 = 𝒓 ⇒ 𝒕 + 𝒔 = 𝒓 + 𝒔
  proof
    — Use mathematical induction:
    definition D. predicate constant 𝐴 object 𝒙, 𝒚, 𝒛.
      𝐴(𝒛) ≔ 𝒙 = 𝒚 ⇒ 𝒙 + 𝒛 = 𝒚 + 𝒛.

    — Initial case:
    i. predicate constant 𝐴. 𝐴(0)
    proof

      object 𝒙, 𝒚, 𝒛.
      1. 𝒙 + 0 = 𝒙 by S5.
      2. 𝒚 + 0 = 𝒚 by S5.

      a. 𝒙 = 𝒚 ⊢ 𝒙 + 0 = 𝒚 + 0
      proof
        a3. 𝒙 = 𝒚 by premise.
        a4. 𝒙 + 0 = 𝒚 by T1C: 1; a3. — MP: a3; MP: 1; T1c. — 1, a3, T1c, MP.
        by T1D: a4; 2. — 2, a4, T1D. — MP: 2; MP: a4; T1d. — 2, a4, T1d, MP.
      ∎

      by DT, D: a. — DT, a, D.

      — One line proof:
—      by DT, D: T1D: S5; T1D: S5; premise ⊢. — DT, D, T1D, S5.
    ∎

    — Induction case:
    ii. object 𝒛 predicate constant 𝐴.
      𝐴(𝒛) ⊢ 𝐴(s(𝒛))
    proof
      object 𝒙, 𝒚.
      1. 𝒙 = 𝒚 ⇒ 𝒙 + 𝒛 = 𝒚 + 𝒛 by premise ii, D. — D, premise.
      2. 𝒙 = 𝒚 ⊢ 𝒙 + 𝒛 = 𝒚 + 𝒛 by MP: premise ⊢; 1. — MP: 1; 1.
      3. 𝒙 + s(𝒛) = s(𝒙 + 𝒛) by S6.
      4. 𝒚 + s(𝒛) = s(𝒚 + 𝒛) by S6.

      a. 𝒙 = 𝒚 ⊢ 𝒙 + s(𝒛) = 𝒚 + s(𝒛)
      proof
[—
        a2. 𝒙 = 𝒚 by premise a. — premise.
        a5. 𝒙 + 𝒛 = 𝒚 + 𝒛 by 2: premise a. — 2, premise. — MP: a2; 1. — 1, a2, MP.
        a6. s(𝒙 + 𝒛) = s(𝒚 + 𝒛) by S2a: a5. — S2a, a5. — MP: a5; S2. — a5, S2, MP.
        a7. 𝒙 + s(𝒛) = s(𝒚 + 𝒛) by T1C: 3; a6. — a6, 3, T1C. — MP: a6; MP: 3; T1c. — 3, a6, T1c, MP.
        by T1D: a7; 4. — 4, a7, T1D.
        by T1D: S6; T1D: 4; a6.
—]
        by T1D: T1C; S6: S6; S2a: 2. — T1D, S6, T1C, S2a, 2.
      ∎

      8. 𝒙 = 𝒚 ⇒ 𝒙 + s(𝒛) = 𝒚 + s(𝒛) by DT: a. — a, DT.
      9. 𝐴(s(𝒛)) by 8, D.
      by DT, D: a: premise ⊢₁. — a, DT, D.

—      by DT, D: T1D: T1C; S6: S6; S2a: 2: premise ⊢. — DT, D, T1D, S6, T1C, S2a, 2.
—      by DT, D: T1D: T1C; S6: S6; S2a: MP, D, premise ⊢. — DT, D, T1D, S6, T1C, S2a, 2.
—      by DT, D: T1D: T1C; S6: S6; S2a: MP: premise ⊢; premise ⊢, D.
    ∎

    by OVS: IR, D: i; ii. — OVS: IR, D, i, ii.
  ∎


  lemma T1E. object 𝒕, 𝒓, 𝒔.
    𝒕 = 𝒓 ⊢ 𝒕 + 𝒔 = 𝒓 + 𝒔
  by MP: premise T1E; T1e. — premise, T1e, MP.


  lemma T1f. object 𝒕.
    𝒕 = 0 + 𝒕
  proof
    definition D. predicate constant 𝐴  object 𝒙.
      𝐴(𝒙) ≔ 𝒙 = 0 + 𝒙.

    — Initial case:
    i.  predicate constant 𝐴. 𝐴(0) by MP: S5; T1b, D.

    — Induction case:
    ii. object 𝒙 predicate constant 𝐴.
      𝐴(𝒙) ⊢ 𝐴(s(𝒙))
    proof 
      1. 𝒙 = 0 + 𝒙 by premise, D.
      2. 0 + s(𝒙) = s(0 + 𝒙) by S6.
      3. s(𝒙) = s(0 + 𝒙) by S2a: 1. — S2a, 1. — MP: 1; S2.
      4. s(𝒙) = 0 + s(𝒙) by T1D: 3; 2. — T1D, 2, 3. — MP: 2; MP: 3; T1d.
      by 4, D.
    ∎

    by OVS: IR, D: i; ii. — OVS: IR, D, i, ii.
  ∎


  lemma T1g. object 𝒓, 𝒕.
    s(𝒕) + 𝒓 = s(𝒕 + 𝒓)
  proof
    definition D. predicate constant 𝐴  object 𝒙, 𝒚.
      𝐴(𝒚) ≔ s(𝒙) + 𝒚 = s(𝒙 + 𝒚).

    — Initial case:
    i. predicate constant 𝐴.
      𝐴(0)
    proof
      object 𝒙, 𝒚.
      1. s(𝒙) + 0 = s(𝒙) by S5.
      2. 𝒙 + 0 = 𝒙 by S5.
      3. s(𝒙 + 0) = s(𝒙) by S2a, 2. — MP: 2; S2. — 2, S2, MP.
—      by MP, D: 3; MP: 1; T1d. — D, 1, 3, T1d, MP.
      by T1D, D: 1; 3. — D, 3, 1, T1D.
    ∎
 
    — Induction case:
    ii. object 𝒚 predicate constant 𝐴.
      𝐴(𝒚) ⊢ 𝐴(s(𝒚))
    proof
      object 𝒙.
      1. s(𝒙) + 𝒚 = s(𝒙 + 𝒚) by premise ii, D. — premise, D.
      2. s(𝒙) + s(𝒚) = s(s(𝒙) + 𝒚) by S6.
      3. s(s(𝒙) + 𝒚) = s(s(𝒙 + 𝒚)) by S2a: 1. — MP: 1; S2. — 1, S2, MP.
      4. s(𝒙) + s(𝒚) = s(s(𝒙 + 𝒚)) by T1C: 2; 3. — 2, 3, T1C. — MP: 3; MP: 2; T1c. — 2, 3, T1c, MP.
      5. 𝒙 + s(𝒚) = s(𝒙 + 𝒚) by S6.
      6. s(𝒙 + s(𝒚)) = s(s(𝒙 + 𝒚)) by S2a: 5. — MP: 5; S2. — 5, S2, MP.
      7. s(𝒙) + s(𝒚) = s(𝒙 + s(𝒚)) by T1D: 4; 6. — MP: 6; MP: 4; T1d. — 4, 6, T1d, MP.
      by 7, D.
    ∎
    by OVS: IR, D: i; ii. — OVS: IR, D, i, ii.
  ∎


  lemma T1h. object 𝒕, 𝒓.
    𝒕 + 𝒓 = 𝒓 + 𝒕
  proof
    definition D. predicate constant 𝐴  object 𝒙, 𝒚.
      𝐴(𝒚) ≔ 𝒙 + 𝒚 = 𝒚 + 𝒙.

    — Initial case:
    i. predicate constant 𝐴.
      𝐴(0)
    proof
      object 𝒙, 𝒚.
      1. 𝒙 + 0 = 𝒙 by S5.
      2. 𝒙 = 0 + 𝒙 by T1f.
—      by MP, D: 2; MP: 1; T1c. — D, 1, 2, T1c, MP.
      by T1C, D: 1; 2. — T1C, D: 1, 2.
    ∎


    — Induction case:
    ii. object 𝒚 predicate constant 𝐴.
      𝐴(𝒚) ⊢ 𝐴(s(𝒚))
    proof
      object 𝒙.
      1. 𝒙 + 𝒚 = 𝒚 + 𝒙 by premise ii, D. — premise, D.
      2. 𝒙 + s(𝒚) = s(𝒙 + 𝒚) by S6.
      3. s(𝒚) + 𝒙 = s(𝒚 + 𝒙) by T1g.
      4. s(𝒙 + 𝒚) = s(𝒚 + 𝒙) by S2a: 1. — MP: 1; S2. — 1, S2, MP.
      5. 𝒙 + s(𝒚) = s(𝒚 + 𝒙) by T1C: 2; 4. — T1C: 2, 4. — MP: 4; MP: 2; T1c. — 2, 4, T1c, MP.
      6. 𝒙 + s(𝒚) = s(𝒚) + 𝒙 by T1D: 5; 3. — T1D: 3, 5. — MP: 3; MP: 5; T1d. — 3, 5, T1d, MP.
      by 6, D.
    ∎

    by OVS: IR, D: i; ii. — OVS: IR, D, i, ii.
  ∎


  lemma T1i. object 𝒔, 𝒕, 𝒓.
    𝒕 = 𝒓 ⇒ 𝒔 + 𝒕 = 𝒔 + 𝒓
  proof
    1. 𝒕 = 𝒓 ⇒ 𝒕 + 𝒔 = 𝒓 + 𝒔 by T1e.
    2. 𝒕 + 𝒔 = 𝒔 + 𝒕 by T1h.
    3. 𝒓 + 𝒔 = 𝒔 + 𝒓 by T1h.

    a. 𝒕 = 𝒓 ⊢ 𝒔 + 𝒕 = 𝒔 + 𝒓
    proof
      4. 𝒕 = 𝒓 by premise.
      5. 𝒕 + 𝒔 = 𝒓 + 𝒔 by MP: 4; 1. — 1, 4, MP.
      6. 𝒔 + 𝒕 = 𝒓 + 𝒔 by S1a: 2; 5. — S1a: 2, 5. — MP: 5; MP: 2; S1. — 2, 5, S1, MP.
      by T1C: 6; 3. — T1C: 3, 6. — MP: 3; MP: 6; T1c. — 3, 6, T1c, MP.
    ∎

    by DT: a. — a, DT.
  ∎


  lemma T1I. object 𝒔, 𝒕, 𝒓.
    𝒕 = 𝒓 ⊢ 𝒔 + 𝒕 = 𝒔 + 𝒓
  by MP: premise ⊢; T1i. — T1i, MP.


  lemma T1j. object 𝒕, 𝒓, 𝒔.
    (𝒕 + 𝒓) + 𝒔 = 𝒕 + (𝒓 + 𝒔)
  proof
    definition D. predicate constant 𝐴  object 𝒙, 𝒚, 𝒛.
      𝐴(𝒛) ≔ (𝒙 + 𝒚) + 𝒛 = 𝒙 + (𝒚 + 𝒛).

    — Initial case:
    i. predicate constant 𝐴.
      𝐴(0)
    proof
      object 𝒙, 𝒚, 𝒛.
      1. (𝒙 + 𝒚) + 0 = 𝒙 + 𝒚 by S5.
      2. 𝒚 + 0 = 𝒚 by S5.
      3. 𝒙 + (𝒚 + 0) = 𝒙 + 𝒚 by T1I: 2. — MP: 2; T1i. — T1i, 2, MP.
—      by MP, D: 3; MP: 1; T1d. — D, 1, 3, T1d, MP.
      by T1D, D: 1; 3. — T1D, D: 3, 1.
    ∎

    — Induction case:
    ii. object 𝒛 predicate constant 𝐴.
      𝐴(𝒛) ⊢ 𝐴(s(𝒛))
    proof
      object 𝒙, 𝒚.
      1. (𝒙 + 𝒚) + 𝒛 = 𝒙 + (𝒚 + 𝒛) by premise ii, D. — premise, D.
      2. (𝒙 + 𝒚) + s(𝒛) = s((𝒙 + 𝒚) + 𝒛) by S6.
      3. s((𝒙 + 𝒚) + 𝒛) = s(𝒙 + (𝒚 + 𝒛)) by S2a: 1. — MP: 1; S2. — 1, S2, MP.
      4. (𝒙 + 𝒚) + s(𝒛) = s(𝒙 + (𝒚 + 𝒛)) by T1C: 2; 3. — T1C: 2, 3. — MP: 3; MP: 2; T1c. — 2, 3, T1c, MP.
      5. 𝒚 + s(𝒛) = s(𝒚 + 𝒛) by S6.
      6. 𝒙 + (𝒚 + s(𝒛)) = 𝒙 + s(𝒚 + 𝒛) by T1I: 5. — MP: 5; T1i. — 5, T1i, MP.
      7. 𝒙 + s(𝒚 + 𝒛) = s(𝒙 + (𝒚 + 𝒛)) by S6.
      8. 𝒙 + (𝒚 + s(𝒛)) = s(𝒙 + (𝒚 + 𝒛)) by T1C: 6; 7. — T1C: 6, 7. — MP: 7; MP: 6; T1c. — 6, 7, T1c, MP.
—      by MP, D: 8; MP: 4; T1d. — 4, 8, T1d, D, MP.
      by T1D, D: 4; 8. — T1D, D: 4, 8.
    ∎

    by OVS: IR, D: i; ii. — OVS: IR, D, i, ii.
  ∎


  lemma T1k. object 𝒕, 𝒓, 𝒔.
    𝒕 = 𝒓 ⇒ 𝒕⋅𝒔 = 𝒓⋅𝒔
  proof
    definition D. predicate constant 𝐴  object 𝒙, 𝒚, 𝒛.
      𝐴(𝒛) ≔ 𝒙 = 𝒚 ⇒ 𝒙⋅𝒛 = 𝒚⋅𝒛.

    — Initial case:
    i. predicate constant 𝐴.
      𝐴(0)
    proof
[—
      object 𝒙, 𝒚.
      a. 𝒙 = 𝒚 ⊢ 𝒙⋅0 = 𝒚⋅0
      proof
        1. 𝒙 = 𝒚 by premise.
        2. 0 = 0 by T1a.
        3. 𝒙⋅0 = 0 by S7.
        4. 𝒚⋅0 = 0 by S7.
        by 3, 4, T1d, MP.
      ∎
—]
—      by DT, D: MP: S7; MP: S7; T1d. — D, DT, S7, T1d, MP.
      by DT, D: T1D: S7; S7. — D, DT, S7, T1D.
    ∎

    — Induction case:
    ii. object 𝒛 predicate constant 𝐴.
      𝐴(𝒛) ⊢ 𝐴(s(𝒛))
    proof
      object 𝒙, 𝒚.
      1. 𝒙 = 𝒚 ⇒ 𝒙⋅𝒛 = 𝒚⋅𝒛 by premise, D.
      a. 𝒙 = 𝒚 ⊢ 𝒙⋅s(𝒛) = 𝒚⋅s(𝒛)
      proof
        1a. 𝒙 = 𝒚 by premise a. — premise.
        1b. 𝒚 = 𝒙 by MP: 1a; T1b. — T1b, 1a, MP.
        2. 𝒙⋅𝒛 = 𝒚⋅𝒛 by MP: premise a; 1. — 1, premise, MP.
        3. 𝒙⋅s(𝒛) = 𝒙⋅𝒛 + 𝒙 by S8.
        4. 𝒚⋅s(𝒛) = 𝒚⋅𝒛 + 𝒚 by S8.
        5. 𝒙⋅𝒛 + 𝒙 = 𝒙⋅𝒛 + 𝒚 by T1I: 1a. — MP: 1a; T1i. — T1i, 1a, MP.
        6. 𝒙⋅𝒛 + 𝒚 = 𝒚⋅𝒛 + 𝒚 by T1E: 2. — MP: 2; T1e. — T1e, 2, MP.
        7. 𝒙⋅𝒛 + 𝒙 = 𝒚⋅𝒛 + 𝒚 by T1C: 5; 6. — T1C: 5, 6. — MP: 6; MP: 5; T1c. — 5, 6, T1c, MP.
—        by MP: MP; MP: 3; T1d; 7; MP: 4; T1d. — 7, 3, 4, T1d, D, MP.
        by T1D: 3; T1D: 4; 7. — T1D, 3, 4, 7.
      ∎
—      by DT, D: a. — 1, a, D, DT.
      by DT, D: a: premise ⊢₁.
    ∎

    by OVS: IR, D: i; ii. — OVS: IR, D, i, ii.
  ∎


  lemma T1K. object 𝒕, 𝒓, 𝒔.
    𝒕 = 𝒓 ⊢ 𝒕⋅𝒔 = 𝒓⋅𝒔
   by MP: premise ⊢; T1k. — T1k, MP.


  lemma T1l. object 𝒕.
    0⋅𝒕 = 0
  proof
    definition D. predicate constant 𝐴 object 𝒛.
      𝐴(𝒛) ≔ 0⋅𝒛 = 0.

    — Initial case:
    i. predicate constant 𝐴. 𝐴(0) by D, S7.

    — Induction case:
    ii. object 𝒛 predicate constant 𝐴.
      𝐴(𝒛) ⊢ 𝐴(s(𝒛))
    proof
      object 𝒙, 𝒚.
      1. 0⋅𝒛 = 0 by premise ii, D. — D, premise.
      2. 0⋅s(𝒛) = 0⋅𝒛 + 0 by S8.
      3. 0⋅𝒛 + 0 = 0⋅𝒛 by S5.
—      by MP: MP; MP: 2; T1c, D; 1, D; MP: 3; T1c, D. — D, 1, 2, 3, T1c, MP.
      by T1C, D: 2; T1C: 3; premise ⊢, D. — T1C, D, 1, 2, 3.
    ∎

    by OVS: IR, D: i; ii. — OVS: IR, D, i, ii.
  ∎


  lemma T1m. object 𝒕, 𝒓.
    s(𝒕)⋅𝒓 = 𝒕⋅𝒓 + 𝒓
  proof
    definition D. predicate constant 𝐴  object 𝒙, 𝒚.
      𝐴(𝒚) ≔ s(𝒙)⋅𝒚 = 𝒙⋅𝒚 + 𝒚.

    — Initial case:
    i. predicate constant 𝐴.
      𝐴(0)
    proof
      object 𝒙.
      1. s(𝒙)⋅0 = 0 by S7.
      2. 𝒙⋅0 = 0 by S7.
      3. 𝒙⋅0 + 0 = 𝒙⋅0 by S5.
      4. s(𝒙)⋅0 = 𝒙⋅0 + 0 by T1D: T1D; 3: 1; 2. — 1, 2, 3, T1D. — MP: MP; MP: 1; T1d; 2; MP: 3; T1c. — 1, 2, 3, T1d, MP.
—      by D, 4.
      by 4, D.
    ∎

    — Induction case:
    ii. object 𝒚 predicate constant 𝐴.
      𝐴(𝒚) ⊢ 𝐴(s(𝒚))
    proof
      object 𝒙.
      1. s(𝒙)⋅𝒚 = 𝒙⋅𝒚 + 𝒚 by premise ii, D. — D, premise.

      2. s(𝒙)⋅s(𝒚) = s(𝒙)⋅𝒚 + s(𝒙) by S8.
      3. s(𝒙)⋅𝒚 + s(𝒙) = (𝒙⋅𝒚 + 𝒚) + s(𝒙) by T1E: 1. — MP: 1; T1e. — 1, T1e, MP.
      4. (𝒙⋅𝒚 + 𝒚) + s(𝒙) = 𝒙⋅𝒚 + (𝒚 + s(𝒙)) by T1j.
      5. 𝒚 + s(𝒙) = s(𝒚 + 𝒙) by S6.
      6. 𝒙⋅𝒚 + (𝒚 + s(𝒙)) = 𝒙⋅𝒚 + s(𝒚 + 𝒙) by T1I: 5. — MP: 5; T1i. — 5, T1i, MP.
      7. s(𝒙)⋅s(𝒚) = (𝒙⋅𝒚 + 𝒚) + s(𝒙) by T1C: 2; 3. — T1C: 2, 3. — MP: 3; MP: 2; T1c. — 2, 3, T1c, MP.
      8. s(𝒙)⋅s(𝒚) = 𝒙⋅𝒚 + (𝒚 + s(𝒙)) by T1C: 7; 4. — T1C: 4, 7. — MP: 4; MP: 7; T1c. — 7, 4, T1c, MP.
      9. s(𝒙)⋅s(𝒚) = 𝒙⋅𝒚 + s(𝒚 + 𝒙) by T1C: 8; 6. — T1C: 6, 8. — MP: 6; MP: 8; T1c. — 8, 6, T1c, MP.

     10. s(𝒙 + 𝒚) = s(𝒚 + 𝒙) by S2a: T1h. — T1h, S2a. — MP: T1h; S2. — T1h, S2, MP.

     11. 𝒙⋅s(𝒚) + s(𝒚) = (𝒙⋅𝒚 + 𝒙) + s(𝒚) by T1E: S8. — MP: S8; T1e. — S8, T1e, MP.
     12. (𝒙⋅𝒚 + 𝒙) + s(𝒚) = 𝒙⋅𝒚 + (𝒙 + s(𝒚)) by T1j.
     13. 𝒙⋅𝒚 + (𝒙 + s(𝒚)) = 𝒙⋅𝒚 + s(𝒙 + 𝒚) by T1I: S6. — MP: S6; T1i. — S6, T1i, MP.
     14. 𝒙⋅𝒚 + s(𝒙 + 𝒚) = 𝒙⋅𝒚 + s(𝒚 + 𝒙) by T1I: 10. — MP: 10; T1i. — 10, T1i, MP.
     15. 𝒙⋅s(𝒚) + s(𝒚) = 𝒙⋅𝒚 + s(𝒙 + 𝒚) by T1C: 11; T1C: 12; 13. — T1C, 11, 12, 13. — MP: MP; MP: 11; T1c; 13; MP: 12; T1c. — 11, 12, 13, 14, T1c, MP.
     16. 𝒙⋅s(𝒚) + s(𝒚) = 𝒙⋅𝒚 + s(𝒚 + 𝒙) by T1C: 15; 14. — T1C, 14, 15. — MP: 14; MP: 15; T1c. — 15, 14, T1c, MP.

     17. s(𝒙)⋅s(𝒚) = 𝒙⋅s(𝒚) + s(𝒚) by T1D: 9; 16. — T1D: 9, 16. — MP: 16; MP: 9; T1d. — 9, 16, T1d, MP.
      by 17, D.
      by 17, D.
    ∎
 
    by OVS: IR, D: i; ii. — OVS: IR, D, i, ii.
  ∎


  lemma T1n. object 𝒕, 𝒓.
    𝒕⋅𝒓 = 𝒓⋅𝒕
  proof
    definition D. predicate constant 𝐴  object 𝒙, 𝒚.
      𝐴(𝒚) ≔ 𝒙⋅𝒚 = 𝒚⋅𝒙.

    — Initial case:
—    i. object 𝒙. 𝒙⋅0 = 0⋅𝒙 by MP: T1l; MP: S7; T1d. — S7, T1l, T1d, MP.

    — (fixed) Leads to erroneous proof, by the hidden variable substitution [𝒙 ↦ 0]
—    i. predicate constant 𝐴. 𝐴(0) by MP, D: T1l; MP: S7; T1d. — S7, T1l, T1d, MP, D.
    i. predicate constant 𝐴. 𝐴(0) by T1D, D: S7; T1l. — S7, T1l, T1D, D.

    — Induction case:
    ii. object 𝒚 predicate constant 𝐴.
      𝐴(𝒚) ⊢ 𝐴(s(𝒚))
    proof
      object 𝒙.
      1. 𝒙⋅𝒚 = 𝒚⋅𝒙 by premise ii, D. — premise, D.
      2. 𝒙⋅s(𝒚) = 𝒙⋅𝒚 + 𝒙 by S8.
      3. s(𝒚)⋅𝒙 = 𝒚⋅𝒙 + 𝒙 by T1m.
      4. 𝒙⋅𝒚 + 𝒙 = 𝒚⋅𝒙 + 𝒙 by T1E: 1. — MP: 1; T1e. — 1, T1e, MP.
      5. 𝒙⋅s(𝒚) = s(𝒚)⋅𝒙 by T1C: 2; T1D: 4; 3. — T1C, T1D, 2, 3, 4. — MP: MP; MP: 2; T1c; 3; MP: 4; T1d. — 2, 3, 4, T1d, T1c, MP.
      by 5, D.
    ∎

    by OVS: IR, D: i; ii. — OVS: IR, D, i, ii.
  ∎


  lemma T1o. object 𝒕, 𝒓, 𝒔.
    𝒕 = 𝒓 ⇒ 𝒔⋅𝒕 = 𝒔⋅𝒓
  proof
    definition D. predicate constant 𝐴  object 𝒙, 𝒚, 𝒛.
      𝐴(𝒛) ≔ 𝒙 = 𝒚 ⇒ 𝒛⋅𝒙 = 𝒛⋅𝒚.

    — Initial case:
    i. predicate constant 𝐴.
      𝐴(0)
    proof
      object 𝒙, 𝒚.
      1. 0⋅𝒙 = 0⋅𝒚 by T1D, T1l. — MP: T1l; MP: T1l; T1d. — T1l, T1a, T1d, MP.
      2. 𝒙 = 𝒚 ⇒ 0⋅𝒙 = 0⋅𝒚 by DT: 1. — 1, DT.
      by D, 2.
    ∎
   

    — Induction case:
    ii. object 𝒛 predicate constant 𝐴.
      𝐴(𝒛) ⊢ 𝐴(s(𝒛))
    proof
      object 𝒙, 𝒚.
      1. 𝒙 = 𝒚 ⇒ 𝒛⋅𝒙 = 𝒛⋅𝒚 by D, premise.
      a. 𝒙 = 𝒚 ⊢ s(𝒛)⋅𝒙 = s(𝒛)⋅𝒚
      proof
        a1. s(𝒛)⋅𝒙 = 𝒛⋅𝒙 + 𝒙 by T1m. 
        a2. s(𝒛)⋅𝒚 = 𝒛⋅𝒚 + 𝒚 by T1m. 
        a3. 𝒛⋅𝒙 = 𝒛⋅𝒚 by MP: premise a; 1. — premise, 1, MP.
        a4. 𝒛⋅𝒙 + 𝒙 = 𝒛⋅𝒚 + 𝒚 by T1C: T1I; T1E: premise a; a3. — T1C, a3, T1E, premise a, T1I.
—        by MP: MP; MP: a1; T1c; a2; MP: a4; T1d. — a1, a2, a4, T1d, T1c, MP.
        by T1C: a1; T1D: a4; a2. — a1, a2, a4, T1C, T1D.
      ∎

—      by DT, D: a: premise ⊢. — D, a, 1, DT.
      by DT, D: a: premise ⊢₁. — D, a, 1, DT.
    ∎

    by OVS: IR, D: i; ii. — OVS: IR, D, i, ii.
  ∎


  lemma T1O. object 𝒕, 𝒓, 𝒔.
    𝒕 = 𝒓 ⊢ 𝒔⋅𝒕 = 𝒔⋅𝒓
  by MP: premise ⊢; T1o. — MP, T1o.


  — Left distributive law.
  lemma T2a. object 𝒕, 𝒓, 𝒔.
    𝒕⋅(𝒓 + 𝒔) = 𝒕⋅𝒓 + 𝒕⋅𝒔
  proof
    definition D. predicate constant 𝐴  object 𝒙, 𝒚, 𝒛.
      𝐴(𝒛) ≔ 𝒙⋅(𝒚 + 𝒛) = 𝒙⋅𝒚 + 𝒙⋅𝒛.

    — Initial case:
    i. predicate constant 𝐴.
      𝐴(0)
    proof
      object 𝒙, 𝒚.
      1. 𝒚 + 0 = 𝒚 by S5.
      2. 𝒙⋅0 = 0 by S7.
      3. 𝒙⋅(𝒚 + 0) = 𝒙⋅𝒚 by T1O: 1. — MP: 1; T1o. — T1o, MP, 1.
      4. 𝒙⋅𝒚 + 𝒙⋅0 = 𝒙⋅𝒚 by T1C: T1I; S5: 2. — 2, S5, T1C, T1I. — MP: S5; MP: MP; T1c: 2; T1i. — 2, S5, T1c, T1i, MP.
      5. 𝒙⋅(𝒚 + 0) = 𝒙⋅𝒚 + 𝒙⋅0 by T1D: 3; 4. — 3, 4, T1D. — MP: 4; MP: 3; T1d. — 3, 4, T1d, MP.
—      by D, 5.
      by 5, D.
    ∎

    — Induction case:
    ii. object 𝒛 predicate constant 𝐴.
      𝐴(𝒛) ⊢ 𝐴(s(𝒛))
    proof
      object 𝒙, 𝒚.
      1. 𝒙⋅(𝒚 + 𝒛) = 𝒙⋅𝒚 + 𝒙⋅𝒛 by D, premise.
      2. 𝒚 + s(𝒛) = s(𝒚 + 𝒛) by S6.
      3. 𝒙⋅(𝒚 + s(𝒛)) = 𝒙⋅s(𝒚 + 𝒛) by T1O: 2. — MP: 2; T1o. — 2, T1o, MP.
      4. 𝒙⋅s(𝒚 + 𝒛) = 𝒙⋅(𝒚 + 𝒛) + 𝒙 by S8.
      5. 𝒙⋅(𝒚 + 𝒛) + 𝒙 = (𝒙⋅𝒚 + 𝒙⋅𝒛) + 𝒙 by T1E: 1. — MP: 1; T1e. — 1, T1e, MP.
      6. 𝒙⋅𝒚 + 𝒙⋅s(𝒛) = 𝒙⋅𝒚 + (𝒙⋅𝒛 + 𝒙) by T1I: S8. — MP: S8; T1i. — S8, T1i, MP.
      7. (𝒙⋅𝒚 + 𝒙⋅𝒛) + 𝒙 = 𝒙⋅𝒚 + (𝒙⋅𝒛 + 𝒙) by T1j.
      8. 𝒙⋅(𝒚 + s(𝒛)) = (𝒙⋅𝒚 + 𝒙⋅𝒛) + 𝒙 by T1C: T1C; 5: 3; 4. — 3, 4, 5, T1C. — MP: MP; MP: 3; T1c; 5; MP: 4; T1c. — 3, 4, 5, T1c, MP.
      9. 𝒙⋅𝒚 + 𝒙⋅s(𝒛) = (𝒙⋅𝒚 + 𝒙⋅𝒛) + 𝒙 by T1D: 6; 7. — 6, 7, T1D. —  MP: 7; MP: 6; T1d. — 6, 7, T1d, MP.
      10. 𝒙⋅(𝒚 + s(𝒛)) = 𝒙⋅𝒚 + 𝒙⋅s(𝒛) by T1D: 8; 9. — 8, 9, T1D. — MP: 9; MP: 8; T1d. — 8, 9, T1d, MP.
—      by D, 10.
      by 10, D.
    ∎

    by OVS: IR, D: i; ii. — OVS: IR, D, i, ii.
  ∎


  — Right distributive law.
  lemma T2b. object 𝒕, 𝒓, 𝒔.
    (𝒓 + 𝒔)⋅𝒕 = 𝒓⋅𝒕 + 𝒔⋅𝒕
  proof
    1. (𝒓 + 𝒔)⋅𝒕 = 𝒕⋅𝒓 + 𝒕⋅𝒔 by T1C: T1n; T2a. — T1n, T2a. — MP: T2a; MP: T1n; T1c.
    2. 𝒓⋅𝒕 + 𝒔⋅𝒕 = 𝒕⋅𝒓 + 𝒔⋅𝒕 by T1E: T1n. — T1n, T1E. — MP: T1n; T1e. — T1n, T1e, MP.
    3. 𝒕⋅𝒓 + 𝒔⋅𝒕 = 𝒕⋅𝒓 + 𝒕⋅𝒔 by T1I: T1n. — T1n, T1I. — MP: T1n; T1i. — T1n, T1i, MP.
—    by MP: MP; MP: 1; T1d; 3; MP: 2; T1c. — 1, 2, 3, MP, T1c, T1d.
    by T1D: T1D; 2: 1; 3. — 1, 2, 3, T1C, T1D.
  ∎


  — Associativity of multiplication.
  lemma T2c. object 𝒕, 𝒓, 𝒔.
    (𝒕⋅𝒓)⋅𝒔 = 𝒕⋅(𝒓⋅𝒔)
  proof
    definition D. predicate constant 𝐴  object 𝒙, 𝒚, 𝒛.
      𝐴(𝒛) ≔ (𝒙⋅𝒚)⋅𝒛 = 𝒙⋅(𝒚⋅𝒛).

    — Initial case:
    i. predicate constant 𝐴.
      𝐴(0)
    proof
      object 𝒙, 𝒚.
      1. (𝒙⋅𝒚)⋅0 = 0 by S7.
      2. 𝒚⋅0 = 0 by S7.
      3. 𝒙⋅(𝒚⋅0) = (𝒚⋅0)⋅𝒙 by T1n.
      4. (𝒚⋅0)⋅𝒙 = 0⋅𝒙 by T1K: 2. — MP: 2; T1k. — 2, T1k, MP.
      5. 0⋅𝒙 = 0 by T1C: T1n; S7. — S7, T1n, T1C. — MP: S7; MP: T1n; T1c. — S7, T1n, T1c, MP.
      6. 𝒙⋅(𝒚⋅0) = 0 by T1C: T1C; 5: 3; 4. — 3, 4, 5, T1C. — MP: MP; MP: 3; T1c; 5; MP: 4; T1c. — 3, 4, 5, T1c, MP.
      7. (𝒙⋅𝒚)⋅0 = 𝒙⋅(𝒚⋅0) by T1D: 1; 6. — 1, 6, T1D. — MP: 6; MP: 1; T1d. — 1, 6, T1d, MP.
—      by D, 7.
      by 7, D.
    ∎

    — Induction case:
    ii. object 𝒛 predicate constant 𝐴.
      𝐴(𝒛) ⊢ 𝐴(s(𝒛))
    proof
      object 𝒙, 𝒚.
      1. (𝒙⋅𝒚)⋅𝒛 = 𝒙⋅(𝒚⋅𝒛) by D, premise.
      2. (𝒙⋅𝒚)⋅s(𝒛) = (𝒙⋅𝒚)⋅𝒛 + 𝒙⋅𝒚 by S8.
      3. (𝒙⋅𝒚)⋅𝒛 + 𝒙⋅𝒚 = 𝒙⋅(𝒚⋅𝒛) + 𝒙⋅𝒚 by T1E: 1. — 1, T1E. — MP: 1; T1e. — 1, T1e, MP.

      4. 𝒚⋅s(𝒛) = 𝒚⋅𝒛 + 𝒚 by S8.
      5. 𝒙⋅(𝒚⋅𝒛 + 𝒚) = 𝒙⋅(𝒚⋅𝒛) + 𝒙⋅𝒚 by T2a.
      6. 𝒙⋅(𝒚⋅s(𝒛)) = 𝒙⋅(𝒚⋅𝒛 + 𝒚) by T1O: 4. — 4, T1O. — MP: 4; T1o. — 4, T1o, MP.
      7. 𝒙⋅(𝒚⋅s(𝒛)) = 𝒙⋅(𝒚⋅𝒛) + 𝒙⋅𝒚 by T1C: 6; 5. — 5, 6, T1C. — MP: 5; MP: 6; T1c. — 5, 6, T1c, MP.

      8. (𝒙⋅𝒚)⋅s(𝒛) = 𝒙⋅(𝒚⋅s(𝒛)) by T1C: 2; T1D: 3; 7. — 2, 3, 7, T1C, T1D. — MP: MP; MP: 2; T1d; 3; MP: 7; T1d. — 2, 3, 7, T1c, T1d, MP.
—      by D, 8.
      by 8, D.
    ∎

    by OVS: IR, D: i; ii. — OVS: IR, D, i, ii.
  ∎


  — Cancellation law for addition.
  lemma T2d. object 𝒕, 𝒓, 𝒔.
    𝒕 + 𝒔 = 𝒓 + 𝒔 ⇒ 𝒕 = 𝒓
  proof
    predicate constant 𝐴.

    definition D. object 𝒙, 𝒚, 𝒛.
      𝐴(𝒛) ≔ 𝒙 + 𝒛 = 𝒚 + 𝒛 ⇒ 𝒙 = 𝒚.

    — Initial case:
    i. 𝐴(0)
    proof
      object 𝒙, 𝒚.
      a. 𝒙 + 0 = 𝒚 + 0 ⊢ 𝒙 = 𝒚
      proof
—        by MP: S5; MP: MP; T1c: premise a; MP: MP; T1c: S5; T1b. — S5, T1b, T1c, MP, premise.
        by T1C: T1C; S5: T1B: S5. — S5, T1B, T1C.
      ∎
      1. 𝒙 + 0 = 𝒚 + 0 ⇒ 𝒙 = 𝒚 by DT: a. — a, DT.
—      by D, 1.
      by 1, D.
    ∎

    — Induction case:
    ii. object 𝒛.
      𝐴(𝒛) ⊢ 𝐴(s(𝒛))
    proof
      object 𝒙, 𝒚.
      1. 𝒙 + 𝒛 = 𝒚 + 𝒛 ⇒ 𝒙 = 𝒚 by D, premise.
      a. 𝒙 + s(𝒛) = 𝒚 + s(𝒛) ⊢ 𝒙 = 𝒚
      proof
        a0. 𝒙 + s(𝒛) = 𝒚 + s(𝒛) by premise.
        a1. s(𝒙 + 𝒛) = 𝒙 + s(𝒛) by T1B: S6. — S6, T1B. — MP: S6; T1b. — S6, T1b, MP.
        a2. 𝒚 + s(𝒛) = s(𝒚 + 𝒛) by S6.
        a3. s(𝒙 + 𝒛) = s(𝒚 + 𝒛) by T1C: T1C; a2: a1; a0. — a0, a1, a2, T1C. — MP: MP; MP: a1; T1c; a2; MP: a0; T1c. — a0, a1, a2, T1c, MP.
—        by 1, a3, S4, MP.
        by MP: S4a; 1: a3. — 1, a3, S4a, MP.
      ∎

      2. 𝒙 + s(𝒛) = 𝒚 + s(𝒛) ⇒ 𝒙 = 𝒚 by DT: a. — a, DT.
      by D, 2.
    ∎

    by OVS: IR, D: i; ii. — OVS: IR, D, i, ii.
  ∎


  — Cancellation law for addition.
  lemma T2D. object 𝒕, 𝒓, 𝒔.
    𝒕 + 𝒔 = 𝒓 + 𝒔 ⊢ 𝒕 = 𝒓
  by MP: premise ⊢; T2d. — MP, T2d.



  lemma T3a. object 𝒕.
    𝒕 + 1 = s(𝒕)
  by T1C: S6, n1; S2a: S5. — S6, S5, S2a, T1C, n1. — MP: MP; MP: S6; T1c, n1; S5; S2. — S6, S5, S2, T1c, n1, MP.


  lemma T3b. object 𝒕.
    𝒕⋅1 = 𝒕
   by T1C: T1C; T1B: S8, n1; T1E; T1f: S7. — Forward order
—  by MP: MP; MP: S8; T1c, n1; MP; MP: MP; T1c; T1f; T1b: S7; T1e. — S8, S7, T1e, T1c, T1b, T1f, n1, MP.
—   by T1C: T1C; T1B: T1f; S8, n1; T1E: S7. — S8, S7, T1E, T1C, T1B, T1f, n1.
[—
  proof
    1. 𝒕⋅s(0) = 𝒕⋅0 + 𝒕 by S8.
    2. 𝒕⋅0 = 0 by S7.
    3. 𝒕⋅0 + 𝒕 = 0 + 𝒕 by MP: 2; T1e. — 2, T1e, MP.
    4. 𝒕⋅s(0) = 0 + 𝒕 by MP: 3; MP: 1; T1c. — 1, 3, T1c, MP.
    5. 0 + 𝒕 = 𝒕 by MP: T1f; T1b. — T1f, T1b, MP.
    6. 𝒕⋅s(0) = 𝒕 by MP: 5; MP: 4; T1c. — 4, 5, T1c, MP.
    by 6, n1.
  ∎
—]


  lemma T3c. object 𝒕.
    𝒕⋅2 = 𝒕 + 𝒕
  by T1C: S8, n2; T1E: T3b. — S8, T3b, T1E, T1C, n1, n2.



  lemma T3d. object 𝒕, 𝒔.
    𝒕 + 𝒔 = 0 ⇒ 𝒕 = 0 ∧ 𝒔 = 0
  proof
—    predicate constant 𝐴.

    definition D. predicate constant 𝐴 object 𝒙, 𝒚.
      𝐴(𝒚) ≔ 𝒙 + 𝒚 = 0 ⇒ 𝒙 = 0 ∧ 𝒚 = 0.

    — Initial case:
    i. predicate constant 𝐴. 𝐴(0)
    by DT, D: CI: T1D; T1a: T1B; T1B: S5. — T1a, T1B, T1D, S5, DT, D, CI.
    —by DT, D: CI: T1D; T1a: T1B; T1B: premise ⊢; S5. — Reverse order.
[—
    proof
      1. object 𝒙. 𝒙 + 0 = 0 ⊢ 𝒙 = 0 ∧ 0 = 0
      proof
        a1. 𝒙 + 0 = 0 by premise.
        a2. 𝒙 + 0 = 𝒙 by S5.
        a3. 𝒙 = 0 by a1, a2, T1B, T1D.
        a4. 0 = 0 by T1a.
        by CI, a3, a4.
      ∎
      2. object 𝒙. 𝒙 + 0 = 0 ⇒ 𝒙 = 0 ∧ 0 = 0
      by 1, DT.
[—
      proof
        by 1, DT.
      ∎
—]
      by D, 2.
    ∎
—]

    ii. predicate constant 𝐴 object 𝒚.
      𝐴(𝒚) ⊢ 𝐴(s(𝒚))
—    by premise, T1B, S3, NE, S6, NC.
    proof
      1. object 𝒙. s(𝒙 + 𝒚) ≠ 0 by MP, NE: S3, NE; IC: T1b. — S3, NE, T1b, IC, MP.
      2. object 𝒙. s(𝒙 + 𝒚) ≠ 0 ⇒ 𝒙 + s(𝒚) ≠ 0 by IC, NE: DT: T1C: T1B: S6. — S6, IC, NE, T1B, T1C, T1D, DT.
      3. object 𝒙. 𝒙 + s(𝒚) ≠ 0 by MP: 1; 2. — 1, 2, MP.
      by DT, D: NC: 3, NE. — D, 3, NE, NC, DT.
    ∎

    by OVS: IR, D: i; ii. — OVS: IR, D, i, ii.
  ∎


  lemma T3D. object 𝒕, 𝒔.
    𝒕 + 𝒔 = 0 ⊢ 𝒕 = 0 ∧ 𝒔 = 0
  by MP: premise ⊢; T3d. — T3d, MP, premise.

  lemma T3e. object 𝒕, 𝒔.
    𝒕⋅𝒔 = 0 ⇒ 𝒕 = 0 ∨ 𝒔 = 0
  proof
    definition D. predicate constant 𝐴 object 𝒙, 𝒚.
      𝐴(𝒚) ≔ 𝒙⋅𝒚 = 0 ⇒ 𝒙 = 0 ∨ 𝒚 = 0.

    i. predicate constant 𝐴. 𝐴(0)
    by DT, D: DI2: T1a. — D, T1a, DT, DI2.

    ii. predicate constant 𝐴 object 𝒚.
      𝐴(𝒚) ⊢ 𝐴(s(𝒚))
    proof
      1. object 𝒙. 𝒙⋅s(𝒚) = 0 ⇒ 𝒙⋅𝒚 + 𝒙 = 0 by DT: T1C: T1D: T1a; S8. — S8, DT, T1a, T1C, T1D.
      2. object 𝒙. 𝒙⋅𝒚 + 𝒙 = 0 ⇒ 𝒙 = 0 by DT: CE2: T3D. — T3D, DT, CE2.
      3. object 𝒙. 𝒙 = 0 ⇒ 𝒙 = 0 ∨ s(𝒚) = 0 by DT: DI1. — DT, DI1.
      4. object 𝒙. 𝒙⋅s(𝒚) = 0 ⇒ 𝒙 = 0 ∨ s(𝒚) = 0 by ICh: ICh; 3: 1; 2. — 1, 2, 3, ICh.
      by 4, D. — D, 4.
    ∎

—    5. 𝒕⋅𝒔 = 0 ⇒ 𝒕 = 0 ∨ 𝒔 = 0 by IR2, D: i; DT, D: ii, D: premise ⊢.
—    6. 𝒕⋅𝒔 = 0 ⇒ 𝒕 = 0 ∨ 𝒔 = 0 by S5. — by IR2, D: i; DT, D: ii, D: premise ⊢.
—    7. 𝒕⋅𝒔 = 0 by S5.
    by OVS: IR, D: i; ii. — OVS: IR, D, i, ii.
—    result by S5.
—    result by IR2, i, ii, D, DT.
  ∎


  lemma T3E. object 𝒕, 𝒔.
    𝒕⋅𝒔 = 0 ⊢ 𝒕 = 0 ∨ 𝒔 = 0
  by MP: premise ⊢; T3e. — MP: T3e.


  lemma T3Ea. object 𝒕, 𝒔.
    𝒕 ≠ 0, 𝒕⋅𝒔 = 0 ⊢ 𝒔 = 0
  by DS1, NE: T3E. — T3E, NE, DS1.



  lemma T3Eb. object 𝒕, 𝒔.
    𝒔 ≠ 0, 𝒕⋅𝒔 = 0 ⊢ 𝒕 = 0
  by DS2: T3E; premise ⊢₀, NE: premise ⊢₁. — T3E, NE, DS1.



—{— trace result —}


  lemma T3f. object 𝒕, 𝒔.
    𝒕 + 𝒔 = 1 ⇒ (𝒕 = 0 ∧ 𝒔 = 1) ∨ (𝒕 = 1 ∧ 𝒔 = 0)
  proof
—    predicate constant 𝐴.

    definition D. predicate constant 𝐴 object 𝒙, 𝒚.
      𝐴(𝒚) ≔ 𝒙 + 𝒚 = 1 ⇒ (𝒙 = 0 ∧ 𝒚 = 1) ∨ (𝒙 = 1 ∧ 𝒚 = 0).

    — Initial case:
    i. predicate constant 𝐴. 𝐴(0)
—    by DT, D: DI2: CI: T1D; T1a: T1B; T1B: premise ⊢; S5. — D, DT, CI, DI2, S5, T1a, T1B, T1D.
    —by D, DT, CI, DI2, S5, T1a, T1B, T1D. — DT, D: DI2: CI: premise ⊢; T1a.
    by DT, D: DI2: CI: T1D; T1a: T1B; T1B: S5.

[—
    proof
      1. object 𝒙. 𝒙 + 0 = 1 ⊢ 𝒙 = 1 by T1D: T1B; T1B: premise ⊢; S5. — S5, T1a, T1B, T1D.
      by DT, D: DI: CI: 1; T1a: premise ⊢. — D, 1, DT, CI, DI1, DI2, T1a.
    ∎
—]

    ii. predicate constant 𝐴 object 𝒚.
      𝐴(𝒚) ⊢ 𝐴(s(𝒚))
—    by premise, T1B, S3, NE, S6, NC.
    proof
      1. object 𝒙. 𝒙 + s(𝒚) = 1 ⊢ s(𝒙 + 𝒚) = 1 by T1C: T1B: S6. — S6, T1B, T1C.
      2. object 𝒙. s(𝒙 + 𝒚) = 1 ⊢ 𝒙 + 𝒚 = 0 by MP: premise ⊢; S4, n1. — n1, S4, MP.
      3. object 𝒙. 𝒙 + 𝒚 = 0 ⊢ 𝒙 = 0 ∧ 𝒚 = 0 by T3D. — T3D.
      4. 𝒚 = 0 ⊢ s(𝒚) = 1 by MP: premise ⊢; S2, n1. — n1, S2, MP.
      5. object 𝒙. 𝒙 = 0, 𝒚 = 0 ⊢ (𝒙 = 0 ∧ s(𝒚) = 1) ∨ (𝒙 = 1 ∧ s(𝒚) = 0)
        by DI: CI: 4. — 4, CI, DI.
      6. object 𝒙. 𝒙 + 𝒚 = 0 ⊢ (𝒙 = 0 ∧ s(𝒚) = 1) ∨ (𝒙 = 1 ∧ s(𝒚) = 0)
        by 5: CE; CE: 3; 3. — 1, 2, 3, 4, 5, CE.
      7. object 𝒙. 𝒙 + s(𝒚) = 1 ⊢ 𝒙 + 𝒚 = 0 by 2: 1. — 1, 2.
      by DT, D: 6: 7. — DT, D, 6, 7.
    ∎

    by OVS: IR, D: i; ii. — OVS: IR, D, i, ii.
  ∎


  lemma T3F. object 𝒕, 𝒔.
    𝒕 + 𝒔 = 1 ⊢ (𝒕 = 0 ∧ 𝒔 = 1) ∨ (𝒕 = 1 ∧ 𝒔 = 0)
  by MP: premise ⊢; T3f. — MP, T3f.



  — Equality reflexive, with negation.
  lemma EqRN. object 𝒙, 𝒚.
    𝒙 ≠ 𝒚 ⊢ 𝒚 ≠ 𝒙
  proof
    1. 𝒚 = 𝒙 ⇒ 𝒙 = 𝒚 by T1b.
    2. 𝒙 ≠ 𝒚 ⇒ 𝒚 ≠ 𝒙 by IC, NE: 1. — IC, NE, 1.
    by MP: premise ⊢; 2. — 2, MP.
  ∎


  — Equality transitive, with negation.
  lemma EqTrN. object 𝒙, 𝒚, 𝒛.
    𝒙 = 𝒚, 𝒚 ≠ 𝒛 ⊢ 𝒙 ≠ 𝒛
  proof
    — Proof by contradiction: Assume 𝒙 = 𝒛, and show that both
    — ¬𝒚 = 𝒛 and 𝒚 = 𝒛 hold. Then ¬𝒙 = 𝒛 must hold.
    0. 𝒙 = 𝒚 by premise.
    1. ¬𝒚 = 𝒛 by premise, NE.
    2. 𝒙 = 𝒛 ⊢ ¬𝒚 = 𝒛 by 1.
    3. 𝒙 = 𝒛 ⊢ 𝒚 = 𝒛 by T1D: T1D; T1D: T1a; 0; T1a. — 0, T1a, T1D.
    — by T1D: T1D; T1D: T1a; T1a; premise ⊢. — Forward order
    — by T1D: T1D; T1D: T1a; T1a; 0. — Reverse order.
                       — T1D: T1D; T1D: T1a; premise ⊢; T1a; 0. — 0, T1a, T1D.
    4. ¬𝒙 = 𝒛 by RA: 3; 2. — 2, 3, RA.
               — RA: 3; 2: premise ⊢; premise ⊢. — 2, 3, RA.
    by 4, NE.
  ∎


  lemma T3g. object 𝒕, 𝒔.
    𝒕⋅𝒔 = 1 ⇒ 𝒕 = 1 ∧ 𝒔 = 1
  proof
    definition D. predicate constant 𝐴 object 𝒙, 𝒚.
      𝐴(𝒚) ≔ 𝒙⋅𝒚 = 1 ⇒ 𝒙 = 1 ∧ 𝒚 = 1.

    i. predicate constant 𝐴.
      𝐴(0)
    proof
      by IRP1, D: MT: DT; S3, NE: T1D, n1: T1B; T1B: S7.
     — IRP1, D: MT: S7, S3, n1, NE, T1D, T1B, DT.
  —by IRP1, D: MT: DT; S3, n1, NE: T1D, n1: T1B; T1B: S7; premise ⊢, n1.
   —by IRP1, D: MT: DT; S3, n1, NE: T1D, n1: T1B; T1B: premise ⊢, n1; S7. — Reverse.
      1. object 𝒙. 𝒙⋅0 = 0 by S7.
      2a. object 𝒙. 𝒙⋅0 ≠ 1 by EqTrN: 1; S3, n1. — 1, S3, n1, EqTrN.
      by IRP1, D: 2a, NE. — D, 2a, IRP1, NE.

      2. ¬0 = 1 by S3, n1, NE.
      3. object 𝒙. 𝒙⋅0 = 1 ⊢ 0 = 1 by T1D: T1B; T1B: 1. — 1, T1D, T1B.
       — T1D: T1B; T1B: premise ⊢; 1. — Reverse.
      4. object 𝒙. ¬𝒙⋅0 = 1 by MT: DT; 2: 3. — 2, 3, MT, DT.
      by IRP1, D: 4. — D, 4, IRP1.
    ∎

    ii. predicate constant 𝐴 object 𝒚.
      𝐴(𝒚) ⊢ 𝐴(s(𝒚))
    proof
      1. object 𝒙. 𝒙⋅𝒚 = 1 ⇒ 𝒙 = 1 ∧ 𝒚 = 1 by D, premise.

      a. object 𝒙. 𝒙⋅s(𝒚) = 1 ⊢ 𝒙 = 1
      proof
        a0. 𝒙⋅s(𝒚) = 1 by premise.
        a1. 𝒙⋅s(𝒚) = 𝒙⋅𝒚 + 𝒙 by S8.
        a2. 𝒙⋅𝒚 + 𝒙 = 1 by T1D: T1B; T1B: a1; a0. — a0, a1, T1B, T1D.
          — T1D: T1B; T1B: a0; a1. — Reverse.
        a3. (𝒙⋅𝒚 = 0 ∧ 𝒙 = 1) ∨ (𝒙⋅𝒚 = 1 ∧ 𝒙 = 0) by MP: a2; T3f. — a2, T3f, MP.
        a4. 𝒙⋅𝒚 = 1 ⊢ 𝒙 = 1 by CE1: MP: premise ⊢; 1. — 1, MP, CE1.
        a4a. 1 ≠ 0 by EqRN: S3, n1. — S3, n1, EqRN.
        a5. 𝒙 = 1 ⊢ 𝒙 ≠ 0 by EqTrN: premise ⊢; a4a. — a4a, EqTrN.
        a6. 𝒙⋅𝒚 = 1 ⊢ ¬𝒙 = 0 by a5, NE: a4. — a4, a5, NE.
        a7. 𝒙⋅𝒚 = 1 ⇒ ¬𝒙 = 0 by DT: a6. — a6, DT.
        a8. formula 𝑨, 𝑩. (𝑨 ⇒ ¬𝑩) ⇒ ¬(𝑨 ∧ 𝑩) by CE: 58b, EQ. — 58b, EQ, CE.
        a9. ¬(𝒙⋅𝒚 = 1 ∧ 𝒙 = 0) by MP: a7; a8. — a7, a8, MP.
        a10. 𝒙⋅𝒚 = 0 ∧ 𝒙 = 1 by DS2: a3; a9. — DS2: a3; a9. — a3, a9, DS2.
        by CE: a10. — a10, CE.
      ∎

      b. object 𝒙. 𝒙⋅s(𝒚) = 1 ⊢ s(𝒚) = 1
      proof
        b0. 𝒙⋅s(𝒚) = 1 by premise.
        b1. 𝒙 = 1 by a: b0. — b0, a.
        b2. 𝒙⋅s(𝒚) = 1⋅s(𝒚) by MP: b1; T1k. — b1, T1k, MP.
        b3. 1⋅s(𝒚) = s(𝒚)⋅1 by T1n.
        b4. s(𝒚)⋅1 = s(𝒚) by T3b.
        b5. 𝒙⋅s(𝒚) = s(𝒚) by T1C: T1C; b4: b2; b3. — b2, b3, b4, T1C.
        by T1C: T1B: b5. — b0, b5, T1B, T1C.
      ∎

      by DT, D: CI: a; b. — D, DT, a, b, CI.
    ∎

    by OVS: IR, D: i; ii. — OVS: IR, D, i, ii.
  ∎


  lemma T3G. object 𝒕, 𝒔.
    𝒕⋅𝒔 = 1 ⊢ 𝒕 = 1 ∧ 𝒔 = 1
  by MP: premise ⊢; T3g. — T3g, MP.


  — Note that the following statement is false in a syntactic theory, as
  — when the object variable 𝒕 is substituted by the object variable 𝑦, the latter becomes
  — bound, yielding the false statement ∃𝑦: 𝑦 = s(𝑦).
  — In MLI, bound variables are kept distinct from free variables, so 𝒕
  — can never be substituted so as to containing the bound variable ∃𝑦, which
  — internally is marked different from the free variable named 𝑦, and the
  — free for metacondition is thus not needed. Further the concept of terms have
  — been unified into the behavior of object variables, so object variables are
  — resulting in a simpler formulation, though as general.
  lemma T3h. object 𝒕.
    𝒕 ≠ 0 ⇒ ∃𝑦: 𝒕ₓ₍𝑦₎ = s(𝑦)
  proof
    definition D. predicate constant 𝐴 object 𝒙.
      𝐴(𝒙) ≔ 𝒙 ≠ 0 ⇒ ∃𝑤: 𝒙 = s(𝑤).

    i. predicate constant 𝐴.
      𝐴(0)
    by IRP2, NE, D: T1a. — T1a, IRP2, D, NE.

    ii. predicate constant 𝐴 object 𝒙.
      𝐴(𝒙) ⊢ 𝐴(s(𝒙))
      proof
      — Show s(𝒙) ≠ 0 ⇒ ∃𝑤: s(𝒙) = s(𝑤)
      1. 𝒙 = 0 ∨ 𝒙 ≠ 0 by EML, NE.
      2. 𝒙 = 0 ⊢ ∃𝑤: s(𝒙) = s(𝑤) by ExIa: S2a. — ExI, S2a.

      a. 𝒙 ≠ 0 ⊢ ∃𝑤: s(𝒙) = s(𝑤)
      proof
        a1. ∃𝑤: 𝒙 = s(𝑤) by MP: premise a; premise ii, D. — MP: D, premise ii, premise a.

        a2. object 𝒚.
          𝒙 = s(𝒚) ⊢ s(𝒙) = s(s(𝒚)) by S2a. — S2a, premise. — MP: premise ⊢; S2. — S2, MP.

        a3. object 𝒚.
          𝒙 = s(𝒚) ⊢ ∃𝑤: s(𝒙) = s(𝑤) by ExIa: a2. — ExI, a2.

        a4. ∃𝑤: 𝒙 = s(𝑤) ⊢ ∃𝑤: s(𝒙) = s(𝑤) by ExE: a3. — by ExEa, a3.
          — by ExEa: premise ⊢; a3.

        by a4: a1. — a1, a4.
      ∎

      b. 𝒙 = 0 ∨ 𝒙 ≠ 0 ⊢ ∃𝑤: s(𝒙) = s(𝑤) by PCa: 2; a. — by 2, a, PCa.
        — by PCa: premise ⊢; 2; a: premise ⊢; premise ⊢. —
      c. ∃𝑤: s(𝒙) = s(𝑤) by b: 1. — 1, b.
      by IPC, D: c. — c, D, IPC.
    ∎

    by OVS: IR, D: i; ii. — OVS: IR, D, i, ii.
  ∎


  lemma T3H. object 𝒕.
    𝒕 ≠ 0 ⊢ ∃𝑦: 𝒕ₓ₍𝑦₎ = s(𝑦)
  by MP: premise ⊢; T3h.


[—
  lemma T3i. object 𝒕, 𝒔, 𝒓.
    𝒔 ≠ 0 ⇒ (𝒕⋅𝒔 = 𝒓⋅𝒔 ⇒ 𝒕 = 𝒓)
  proof
    definition D. predicate constant 𝐴 object 𝒙, 𝒚, 𝒛.
      𝐴(𝒚) ≔ 𝒛 ≠ 0 ⇒ (𝒙⋅𝒛 = 𝒚⋅𝒛 ⇒ 𝒙 = 𝒚).

    i. predicate constant 𝐴.
      𝐴(0)
    proof
      a. object 𝒙, 𝒛. 𝒛 ≠ 0, 𝒙⋅𝒛 = 0⋅𝒛 ⊢ 𝒙 = 0
      proof
        3. 0⋅𝒛 = 0 by T1l.
        4. 𝒙⋅𝒛 = 0 by T1C: premise a; 3. — T1C, 3, premise.
        5. 𝒙 = 0 by T3Eb, 4, premise a.
      ∎
      by DT, D: DT: a: premise ⊢; premise ⊢. — DT, a, D.
    ∎

    ii. predicate constant 𝐴 object 𝒚.
      𝐴(𝒚) ⊢ 𝐴(s(𝒚))
    proof
      a. object 𝒙, 𝒚, 𝒛. 𝒛 ≠ 0, 𝒙⋅𝒛 = 𝒚⋅𝒛 ⊢ 𝒙 = 𝒚
      proof


      ∎

    ∎

  ∎
—]

end theory TS1.



