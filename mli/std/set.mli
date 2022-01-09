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


theory set. — Set notation.

  formal system.
    — Predefined symbols:
    — binary infix =, ∈.
    — constant ∅.


    — Definition of not in symbol ∉.
    definition NI. object 𝒙, 𝑨. 𝒙 ∉ 𝑨 ≔ ¬𝒙 ∈ 𝑨.

    — Empty set.
    axiom E. object 𝒙. 𝒙 ∉ ∅.

    definition E1. {} ≔ ∅.

    — Definition of singleton (unit) set.
    definition S1. object 𝒙, 𝒛.
      {𝒙} ≔ {𝒛|𝒛 = 𝒙}.

    — Unordered pair.
    definition U2. object 𝒙, 𝒚, 𝒛.
      {𝒙, 𝒚} ≔ {𝒛|𝒛 = 𝒙 ∨ 𝒛 = 𝒚}.


    — Set-builder notation.
    definition SB1. object 𝒂, 𝒙 formula 𝑨.
      𝒂 ∈ {𝒙|𝑨} ≔ 𝑨[𝒙 ⤇ 𝒂].

    definition SB2. object 𝒂, 𝒙 predicate 𝑨.
      𝒂 ∈ {𝒙|𝑨(𝒙)} ≔ 𝑨(𝒂).


    — Implicit set definition
    definition IS. object 𝒚, 𝒇 formula 𝑨.
      {↓𝑥 𝒇|𝑨} ≔ {𝒚|∃𝑥: 𝒚 = 𝒇 ∧ 𝑨}.

    — Subset definition.
    definition S. object °𝒙 object 𝑨, 𝑩, 𝑪 formula 𝑷.
—      {𝒙 ∈ 𝑨|𝑷} ≔ {𝒙|𝒙 ∈ 𝑨 ∧ 𝑷}.
      {𝒙|𝑷} ≔ {𝒙|𝒙 ∈ ⋃𝑨 ∪ ∩(𝑩 ∩ ∁𝑪) ∧ 𝑷}.

[—  Suffices with implicit set definition IS above.
    rule ImplicitSet.
      object 𝑦 object f formula 𝑨.
      𝑦 not free in f, 𝑦 not free in 𝑨
        ⊢ {↓𝑥 f|𝑨} = {𝑦|∃𝑥: 𝑦 = f ∧ 𝑨}.
—]

  end formal system.

end theory set.

