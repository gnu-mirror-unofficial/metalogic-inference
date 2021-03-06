[β Copyright (C) 2017, 2021-2022 Hans Γberg.

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
   along with this program.  If not, see <http://www.gnu.org/licenses/>.  β]

input std/SM.mli

theory TS1.  β Test theory S (number theory).
  include theory SM.

  formal system.
  rule TA1. formula π¨. π¨ β’ π¨ β§ π¨.
  rule TA2. formula π¨, π©, πͺ. π©, π¨ β§ π© β πͺ β’ π¨ β πͺ.

  rule CI. formula π¨, π©. π¨, π© β’ π¨ β§ π©. β Conjunction introduction.


  β Course-of-values induction
  rule CVIA. formula π¨ object Β°π, Β°π predicate π·: π β¦ π¨ function constant s.
    π·(0), (βπ: π β€ π β π·(π)) β π·(s(π)) β’β½ΒΉπβΎ π·(π).

  rule CVIr. formula π© object Β°π, Β°π, Β°π, π predicate π·: π β¦ π© function constant s formula sequence π.
    (π β’ π·(0); (π, π β€ π β’βπβ π·(π) β©β½πβΎβπβ π  β’ π·(s(π)))) β©ΒΉ π β’ π·(π).


  rule CVI2. formula π¨ object Β°π, Β°π predicate variable π· function constant s.
    π·(0), (βπ: π β€ π β π·(π)) β π·(s(π)) β’β½ΒΉπβΎ π·(π).


  rule IR. formula π¨ predicate π·: π β¦ π¨
    object Β°π, π function constant s formula sequence π.
      π β’ π·(0); π, π·(π) β’βπβ π·(s(π)) β© π β’ π·(π).

  rule IRz. formula π¨ object Β°π, π function constant s formula sequence π.
    π β’ (π β¦ π¨)(0); π, π¨ β’βπβ (π β¦ π¨)(s(π)) β© π β’ (π β¦ π¨)(π).
  β Gives the same result:
  β π β’ (π β¦ π¨)(0); π, (π β¦ π¨)(π) β’βπβ (π β¦ π¨)(s(π)) β© π β’ (π β¦ π¨)(π).


  β Inequality β€ reflexive.
  axiom ineqr. object π₯. π₯ β€ π₯.

  rule S1b. object π₯, π¦, π§.
    π₯ = π¦, π¦ = π§ β’ π₯ = π§.

  rule S2b. object π₯, π¦ function constant s. π₯ = π¦ β’ s(π₯) = s(π¦).

  axiom S5. object π₯. π₯ + 0 = π₯.
  axiom S6. object π₯, π¦ function constant s. π₯ + s(π¦) = s(π₯ + π¦).


  end formal system.

{β trace result β}
{β trace unspecializable β}
{β trace variable label β}


  lemma T1. object x function constant s. x = x
  proof
    by MP, TA1, S1, S5. β MP: S5; MP: S5; S1. β MP, TA1, S1, S5.
  β

  {β unexpand_implicit_premise β}
  
  lemma T2. object x, y function constant s. x = y β y = x
  by DT: MP: T1; MP: S1. β DT, T1, MP, S1.

  β Course-of-values induction

  {β expand_implicit_premise β}

  β Induction proof, using course-of-values induction.
  β Fully automated, does not require an explicit predicate to
  β be defined, nor how the statements used should be applied:
  lemma X0CV. object π₯. 0 + π₯ = π₯
  proof
    by CVIr: S5; S1b: S6; S2b: premise β’: ineqr.
    βby CVIr, S5, S1b, S6, S2b, ineqr.
  β

  {β unexpand_implicit_premise β}

  β Using predicate:
  lemma CVIq. formula π© object Β°π, Β°π, π predicate π·: π β¦ π© function constant s formula sequence π.
    π β’ π·(0); π, βπ: π β€ π β π·(π) β’βπβ π·(s(π)) β© π β’ π·(π)
  proof
    by CVIA: DT.
  β


  β Using predicate variable (uninterpreted):
  lemma CVIs. formula π¨ object Β°π, Β°π, π predicate variable π· function constant s formula sequence π.
    π β’ π·(0); π, βπ: π β€ π β π·(π) β’βπβ π·(s(π)) β© π β’ π·(π)
  proof
    by CVI2: DT.
  β


  β Should be:
  β A(0), βx: A(x) β A(s(x)) β’ βx A(x).
  lemma IRa. β Induction Rule.
    predicate variable A function constant s.
    A(0) β§ βx: A(x) β A(s(x)) β’ βx A(x)
  by MP: S9a.

  [β
  proof by MP: premise, S9a. β
  proof
    P1. A(0) β§ (βx: A(x) β A(s(x))) by premise.
    by MP, S9a, P1.
  β
  β]

[β
{β trace result β}  {β trace proof β}  {β trace variable type β}  {β trace bind β}
 {β trace unify β}  {β trace substitute β}
β]

  β Changes β§ of IRa to a formula set comma:
  lemma IR1.
    predicate variable A function constant s.
    A(0), βx: A(x) β A(s(x)) β’ βx A(x)
  proof
[β
    1. A(0) by premise.
    2. βx: A(x) β A(s(x)) by premise.
    3. A(0) β§ (βx: A(x) β A(s(x))) by CI: 1; 2. β 1, 2, CI.
β]
    by IRa: CI. β IRa, 3.
  β

[β
{β trace result β}  {β trace proof β}  {β trace unify β}  {β trace substitute β}
{β trace variable type β}  {β trace bind β}
β]


β  {β trace result β}
β  {β trace proof β}
β {β trace variable type β}  {β trace bind β}
[β {β trace unify β}
 {β trace substitute β}  {β trace split β}
β]

β{β conditional proof β}
{β strict proof β}

  β Induction proof, fully automated, does not require an explicit predicate to
  β be defined, nor how the statements used should be applied:
  β IRz, S5, S1b, S6, S2b. βIRz: S5; S1b: S6; S2b.
  lemma X. object x. 0 + x = x
  proof
    by IR: S5; S1b: S6; S2b.
    βby IR, S5, S1b, S6, S2b.
  β


  β Induction proof, fully automated, does not require an explicit predicate to
  β be defined, nor how the statements used should be applied:
  β IRz, S5, S1b, S6, S2b. βIRz: S5; S1b: S6; S2b.
  lemma X0. object x. 0 + x = x
  proof
    by IRz: S5; S1b: S6; S2b.
    βby IRz, S5, S1b, S6, S2b.
  β


  β Induction proof, fully automated, does not require an explicit predicate to
  β be defined, nor how the statements used should be applied:
  β S9c, S5, Gen, DT, S1b, S6, MP, S2. β S9c: S5; Gen: DT: S1b: S6; MP: S2.
  β This version uses Gen and DT, requiring a more extensive proof search.
  β
  β The transitive rule axiom S1b π₯ = π¦, π¦ = π§ β’ π₯ = π§ is used, as the
  β asymmetrical axiom S1 π₯ = π¦ β (π₯ = π§ β π¦ = π§) requires a longer proof.
  lemma X1. βx: 0 + x = x
  proof
    by S9c: S5; Gen: DT: S1b: S6; MP: S2.
  β  by S9c, S5, Gen, DT, S1b, S6, MP, S2. β S9c: S5; Gen: DT: S1b: S6; MP: S2.

    definition D5. predicate constant B object t.
      B(t) β 0 + t = t.

    1. predicate constant B. B(0) by D5, S5.

    a. object x predicate constant B function constant s. B(x) β’ B(s(x))
    proof
      a1. 0 + x = x by D5, premise.
      a2. 0 + s(x) = s(0 + x) by S6.
      a3. s(0 + x) = s(x) by MP: S2, a1.
      β S1a is π₯ = π¦, π₯ = π§ β’ π¦ = π§; must have S1b π₯ = π¦, π¦ = π§ β’ π₯ = π§.
      a4. 0 + s(x) = s(x) by a2, a3, S1b. β MP: S1a, S2, a1, S6.
      by D5, a4.
    β

    by IR1, D5: 1; Gen: DT: a.
    βby D5, IR1, 1, Gen, DT, a. β IR1βD5β: 1; Gen: DT: a.

    β Original, deterministic proof:
    2. object x predicate constant B function constant s. B(x) β B(s(x)) by DT, a.
    3. predicate constant B function constant s. βx: B(x) β B(s(x)) by Gen, 2.
    4. predicate constant B.βx B(x) by IR1, 1, 3.
    by D5, 4.
  β


β{β untrace all β}

{β trace all β}
{β untrace all β}

end theory TS1.

