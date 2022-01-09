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
{— sublevel max 100 —}
{— unify count max 60000 —}


—input std/IR.mli


theory TG.  — Test Generalization.
—  include theory IR.

{— thread count 0 —}

  formal system.
[—
    rule MP. formula 𝑨, 𝑩. 𝑨, 𝑨 ⇒ 𝑩 ⊢ 𝑩.

    rule CI. formula 𝑨, 𝑩. 𝑨, 𝑩 ⊢ 𝑨 ∧ 𝑩.

    rule Gen. formula 𝑨 object °𝒙.
     𝑨 ⊢ ∀𝒙 𝑨.
—]
    rule GenA. formula 𝑨 object °𝒙.
     𝑨 ⊢ ∀𝒙 𝑨.

    rule K1. formula 𝑨 object 𝒕 object °𝒙. 𝒕 free for 𝒙 in 𝑨 ⊩ ∀𝒙 𝑨 ⊢ 𝑨[𝒙⤇𝒕].
    rule K1a. formula 𝑨 object 𝒕 object °𝒙. ∀𝒙 𝑨 ⊢ 𝑨[𝒙⤇𝒕].

    rule K1b. formula 𝑨 object 𝒕 object °𝒙. ∀𝒙 𝑨 ⊢ 𝑨[𝒙⤇𝒕].
    rule K1c. formula 𝑨 object °𝒙, 𝑡. ∀𝒙 𝑨 ⊢ 𝑨[𝒙⤇𝑡].

    axiom Id. ∀𝑥: 𝑥 = 𝑥.
    axiom IdA. object 𝑥. 𝑥 = 𝑥.

—    axiom S4A. object 𝑥, 𝑦 function s. s(𝑥) = s(𝑦) ⇒ 𝑥 = 𝑦.

  end formal system.

{— trace result —}
{— trace unspecializable —}
{— trace variable label —}
—{— trace null —}
—{— trace unify —}
—{— trace substitute —}

  lemma A. object 𝑥, 𝑦.
    𝑥 + 𝑦 = 𝑥 + 𝑦
  proof
    by IdA, K1c.
  ∎

  lemma B. object 𝒙, 𝒚.
    𝒙 + 𝒚 = 𝒙 + 𝒚
  proof
    by IdA.
  ∎

  lemma C. object 𝑦.
    ∀𝑥: 𝑥 + 𝑦 = 𝑥 + 𝑦
  proof
    by IdA, GenA.
  ∎


[—
  lemma S4B. object 𝒙, 𝒚 function s.
    s(𝒙) = s(𝒚) ⇒ 𝒙 = 𝒚
  proof
    by S4A.
  ∎

  lemma GK. formula 𝑨 object 𝒕 object °𝒙.
    𝑨 ⊢ 𝑨[𝒙⤇𝒕]
  by GenA, K1b.

  lemma S4B. object 𝒙, 𝒚.
    s(𝒙) = s(𝒚) ⇒ 𝒙 = 𝒚
  proof
    1. object 𝑦. s(𝒙) = s(𝑦) ⇒ 𝒙 = 𝑦 by K1c: GenA: S4A. — GenA, K1a, S4A.
    2. ∀𝑦: s(𝒙) = s(𝑦) ⇒ 𝒙 = 𝑦 by GenA: 1. — 1, Gen.
—    by K1b: GenA: 1. — 1, K1b, GenA.
    by K1b: GenA: K1b: GenA: S4A.
—    by K1b: GenA: S4A, K1b, GenA.
—    by K1b, GenA, S4A.
—    by S4A, GK.
  ∎

  lemma S5B. object 𝒙.
    𝒙 + 0 = 𝒙
  by GenA, K1b, S5A.

—]

end theory.



