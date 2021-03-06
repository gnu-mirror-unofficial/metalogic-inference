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
  end formal system.

{β trace result β}


  lemma T1. object x function s. x = x
  proof
    by MP, TA1, S1, S5. β MP: S5; MP: S5; S1. β MP, TA1, S1, S5.
  β

  lemma T2. object x, y function s. x = y β y = x
  proof
    1. x = y β (x = x β y = x) by S1.
    a. x = y β’ y = x
    proof
     a1. x = x β y = x by 1, premise, MP.
     conclusion by a1, T1, MP.
    β

β    conclusion by DT, a.
    conclusion by DT: MP: T1; MP: premise β’β; S1. β DT, T1, MP, S1.
  β

[β
  π©, x = y β§ π© β y = x β’ x = y β y = x.
β]

  β Should be:
  β A(0), βx: A(x) β A(s(x)) β’ βx A(x).
  lemma IR. β Induction Rule.
    predicate variable A function s.
    A(0) β§ (βx: A(x) β A(s(x))) β’ βx A(x)
  proof conclusion by MP: premise, S9a.
  β
  [β
  proof conclusion by MP: premise, S9a. β
  proof
    P1. A(0) β§ (βx: A(x) β A(s(x))) by premise.
    conclusion by MP, S9a, P1.
  β
  β]

[β
{β trace result β}  {β trace proof β}  {β trace variable type β}  {β trace bind β}
 {β trace unify β}  {β trace substitute β}
β]


  lemma IR1.
    predicate variable A function s.
    A(0), (βx: A(x) β A(s(x))) β’ βx A(x)
  proof
    1. A(0) by premise.
    2. βx: A(x) β A(s(x)) by premise.
    3. A(0) β§ (βx: A(x) β A(s(x))) by CI: 1; 2. β 1, 2, CI.
    conclusion by IR: 3. β IR, 3.
  β

[β
{β trace result β}  {β trace proof β}  {β trace unify β}  {β trace substitute β}
{β trace variable type β}  {β trace bind β}
β]

  lemma IR2.
    predicate variable A function s.
    A(0), (βx: A(x) β A(s(x))) β’ βx A(x)
  proof
    1. A(0) by premise.
    2. βx: A(x) β A(s(x)) by premise.
    3. A(0) β§ (βx: A(x) β A(s(x))) by CI, 1, 2.
    conclusion by IR, 3.
  β


β  {β trace result β}
β  {β trace proof β}
β {β trace variable type β}  {β trace bind β}
[β {β trace unify β}
 {β trace substitute β}  {β trace split β}
β]

β{β conditional proof β}
{β strict proof β}


lemma X1. βx: 0 + x = x
proof
β  conclusion by S9c: S5, Gen: DT: MP: A1, S1: S6, MP, S2.
β  conclusion by S9c: S5, Gen: DT: MP: A1, S1b: S6, MP: S2.
β  conclusion by S9c: S5, Gen: DT: A1, S1b, S6, MP, S2. β At 5 MB memory.
β  conclusion by S9c: S5, Gen: DT, A1, S1b, S6, MP, S2. β At 20 MB memory.
β  conclusion by S9c: S5, Gen, DT, A1, S1b, S6, MP, S2. β At 20 MB memory.

  definition D5. predicate B object t.
    B(t) β 0 + t = t.
  1. predicate B. B(0) by D5, S5.

  a. object x predicate B function s. B(x) β’ B(s(x))
  proof
    a1. 0 + x = x by D5, premise.
    a4. 0 + s(x) = s(x) by MP: S1a, S2, a1, S6.
    conclusion by D5, a4.
[β
  β Works when weight increases by product of size of alternatives β§
  β number of metaand goals:
    a1. 0 + x = x by D5, premise.
    a4. 0 + s(x) = s(x) by MP, A1, S1b, S2, a1, S6.
    conclusion by D5, a4.
  β Does not work (too much memory).
    conclusion by D5, MP, A1, S1b, S2, premise, S6.
  β Can be handled if a {β metaand sort β}() is implemented.
    a3. s(0 + x) = s(x) by MP, S2, D5, premise.
    conclusion by D5, MP, A1, S1b, a3, S6.
  β Original, deterministic proof.
    a1. 0 + x = x by D5, premise.
    a2. 0 + s(x) = s(0 + x) by S6.
    a3. s(0 + x) = s(x) by MP: S2, a1.
    a4. 0 + s(x) = s(x) by MP: A1, S1b, a3, a2.
    conclusion by D5, a4.
β]
  β
  β Works when weight increases by product of size of alternatives β§
  β number of metaand goals:
  conclusion by D5, IR1, 1, Gen, DT, a.
[β
  4. βx B(x) by IR1, 1, Gen, DT, a.
  conclusion by D5, 4.
  β Original, deterministic proof:
  2. object x. B(x) β B(s(x)) by DT, a.
  3. βx: B(x) β B(s(x)) by Gen, 2.
  4. βx B(x) by IR1, 1, 3.
  conclusion by D5, 4.
β]
β


β{β untrace all β}

{β trace all β}
{β untrace all β}

end theory TS1.

