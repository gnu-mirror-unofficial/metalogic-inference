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

insert std/S.mli

theory TD1. -- Test definitions.
  include theory S.

definition D6. function f  term t.
  f(t) ≔ t + 0.
definition D7. function g  term u.
  g(u) ≔ 0 + u.

lemma Xf. object x.
  f(0) = g(0).
proof.
  conclusion by D6, D7, S5a.
∎

-- Should fail, as not true for every choice of t:
lemma Xs. term t.
  t + 0 = t ⊢ 0 + 0 = 0.
proof.
  conclusion by premise.
∎

end theory TD1.
