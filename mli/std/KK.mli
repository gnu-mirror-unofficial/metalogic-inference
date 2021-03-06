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


input std/LM.mli


theory KK. β Quantification: Predicate calculus by Kleene, p. 82.
  include theory LM.

  formal system. 
    formula π¨, π©  object π  object Β°π.

  [β Axioms 1-3 of Mendelson, p.57, are here included from theory L
     where they are named A1, A2, A3. Modus ponens (MP) is likewise
     included from theory L. Mendelson axioms 4 (resp. 5)
     are here called K1 (resp. K2). β]


  β Treated as axioms in Mendelson:
  rule A9. π not free in π¨, π¨ β π© β’ π¨ β βπ π©.   β Generalization.
  rule A10. π free for π in π¨ β’ βπ π¨ β π¨[πβ€π].    β Specialization

  rule A11. π free for π in π¨ β’ π¨[πβ€π] β βπ π¨.  β Existence.
  rule A12. π not free in π©, π¨ β π© β’ βπ π¨ β π©. β Existence.

  end formal system.

end theory KK.

