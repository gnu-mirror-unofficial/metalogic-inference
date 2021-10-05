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


input std/KM.mli


theory ZF. — Zermelo-Fraenkel set theory. Shoenfield, p.239.
  include theory KM.

  formal system.
    — Predefined symbols:
    — binary infix =, ∈.
    — constant ∅.
    — predicate Set↓𝑥 𝑨, meaning the existence of the set {𝑥|𝑨}.
  

    [— Extensionality axiom: Sets with equal members are equal. —]
    axiom Ext. object 𝑥, 𝑦.
      (∀𝑧: 𝑧 ∈ 𝑥 ⇔ 𝑧 ∈ 𝑦) ⇒ 𝑥 = 𝑦.


    — Regularity axiom: If a set 𝑥 has a member,
    — then it also has a member 𝑦 disjoint from 𝑥.
    axiom Reg. object 𝑥.
      ∃𝑦: 𝑦 ∈ 𝑥 ⇒ ∃𝑦: 𝑦 ∈ 𝑥 ∧ ¬∃𝑧: 𝑧 ∈ 𝑥 ∧ 𝑧 ∈ 𝑦.


    [— Subset axiom: Given set 𝒚 and formula 𝑨, the set 𝒛 ≔ {𝒙|𝒙 ∈ 𝒚 ∧ 𝑨} = {𝒙 ∈ 𝒚|𝑨} exists. —]
    rule Sub. object °𝒙, °𝒚, °𝒛 formula 𝑨.
      𝒚 not free in 𝑨, 𝒛 not free in 𝑨,
      𝒙 ≢ 𝒚, 𝒙 ≢ 𝒛, 𝒚 ≢ 𝒛
      ⊢ ∃𝒛 ∀𝒙: 𝒙 ∈ 𝒛 ⇔ 𝒙 ∈ 𝒚 ∧ 𝑨.


    — Definition of Set₍𝒙₎ 𝑨 symbol: There is a set 𝒚 containing ∀𝒙 satisfying 𝑨(𝒙).
    definition IsSet. object °𝒙 formula 𝑨.
      Set₍𝒙₎ 𝑨 ≔ ∃𝒚 ∀𝒙: 𝑨 ⇒ 𝒙 ∈ 𝒚.

  [—
    [— Definition of Set↓𝒙 𝑨 symbol: There is a set 𝒚 containing ∀𝒙 satisfying 𝑨(𝒙). —]
    rule IsSet.
      object °𝒙, °𝒚  formula 𝑨.
        𝒚 not free in 𝑨, 𝒙 ≢ 𝒚 ⊢
          Set↓𝒙 𝑨 ≔ ∃𝒚 ∀𝒙: 𝑨 ⇒ 𝒙 ∈ 𝒚.
  —]


    — Replacement axiom: If, for ∀𝒙, given a set 𝒛↓𝒙 ≔ {𝒚|𝑨(𝒙, 𝒚)},
    — then for a given set 𝒘, the subset {𝒚|∃𝒙: 𝒙 ∈ 𝒘 ∧ 𝑨(𝒙, 𝒚)} exists.
    rule Rep.
      object °𝒙, °𝒚, °𝒛, °𝒘  formula 𝑨.
        𝒛 not free in 𝑨, 𝒘 not free in 𝑨,
        𝒙 ≢ 𝒚, 𝒙 ≢ 𝒛, 𝒙 ≢ 𝒘, 𝒚 ≢ 𝒛, 𝒚 ≢ 𝒘, 𝒛 ≢ 𝒘
        ⊢ (∀𝒙 ∃𝒛 ∀𝒚: 𝑨 ⇔ 𝒚 ∈ 𝒛) ⇒ Set₍𝒚₎ ∃𝒙: 𝒙 ∈ 𝒘 ∧ 𝑨.


    [— Power set axiom: Given a set 𝑥, there is a set containing all subsets of 𝑥. —]
    axiom Pw. object 𝑥.
      Set₍𝑦₎ ∀𝑧: 𝑧 ∈ 𝑦 ⇒ 𝑧 ∈ 𝑥.


    [— Axiom of infinity: There is a set 𝑥 containing the empty set ∅, and such that
      if 𝑦 ∈ 𝑥, then also the set 𝑦 ∪ {𝑦} is in 𝑥. —]
    axiom Inf.
      ∃𝑥:
        (∃𝑦: 𝑦 ∈ 𝑥 ∧ ∀𝑧: ¬𝑧 ∈ 𝑦) — 𝑥 contains the empty set.
        ∧
        ∀𝑦: 𝑦 ∈ 𝑥 ⇒ ∃𝑧: 𝑧 ∈ 𝑥
          ∧ ∀𝑤: 𝑤 ∈ 𝑧 ⇔ 𝑤 ∈ 𝑦 ∨ 𝑤 = 𝑦.


    — Defining axiom:
    rule SetSymb. — Set notation.
      predicate variable 𝑨.
        Set₍𝒙₎ 𝑨(𝒙) ⊢ ∀𝒙: 𝒙 ∈ {𝒙|𝑨(𝒙)} ⇔ 𝑨(𝒙).

[—
    — Set builder notation.
    𝒂 ∈ {𝒙|𝑨} ≔ 𝑨[𝒙 ⤇ 𝒂].
    𝒂 ∈ {𝒙|𝑨(𝒙)} ≔ 𝑨(𝒂).
—]

    definition EmptySet. object 𝑥.
      ∅ ≔ {𝑥|¬𝑥 = 𝑥}.

    definition EmptySet2.
      {} ≔ ∅.

    definition UnitSet. object 𝑥.
      {𝑥} ≔ {𝑧|𝑧 = 𝑥}.

    — Unordered pair.
    definition SetPair. object 𝑥, 𝑦.
      {𝑥, 𝑦} ≔ {𝑧|𝑧 = 𝑥 ∨ 𝑧 = 𝑦}.



    rule ImplicitSet.
      object °x, 𝑦 object f formula 𝑨.
      𝑦 not free in f, 𝑦 not free in 𝑨
        ⊢ {₍𝑥₎ f|𝑨} = {𝑦|∃𝑥: 𝑦 = f ∧ 𝑨}.

  end formal system.

end theory ZF.

