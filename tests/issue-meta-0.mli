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


—input std/SM.mli
—input std/IR.mli


theory TM.  — Test meta.
—  include theory SM.
—  include theory IR.
  formal system.

  postulate PCa. formula 𝑨, 𝑩, 𝑪.
    𝑨 ⊢ 𝑪; 𝑩 ⊢ 𝑪 ⊩ 𝑨 ∨ 𝑩 ⊢ 𝑪.

  rule 2. object 𝒙 function constant s.
    𝒙 = 0 ⊢ ∃𝑤: s(𝒙) = s(𝑤).

  rule a. object 𝒙 function constant s.
    𝒙 ≠ 0 ⊢ ∃𝑤: s(𝒙) = s(𝑤).

  end formal system.

{— thread count 0 —}

{— trace result —}
{— trace unspecializable —}
{— trace variable label —}
—{— trace unify —}


  lemma b. object 𝒙 function constant s.
    𝒙 = 0 ∨ 𝒙 ≠ 0 ⊢ ∃𝑤: s(𝒙) = s(𝑤)
  proof
    by PCa: 2, a. — PCa: 2; a.
  ∎


end theory.



