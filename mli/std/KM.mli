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


theory KM. β Quantification: Predicate calculus by Mendelson.
  include theory LM.

  formal system. 
    formula π¨, π© object π object Β°π.

  [β Axioms 1-3 of Mendelson, p.57, are here included from theory L
     where they are named A1, A2, A3. Modus ponens (MP) is likewise
     included from theory L. Mendelson axioms 4 (resp. 5)
     are here called K1 (resp. K2). β]


  β Treated as axioms in Mendelson:

[β
  axiom K1. π free for π in π¨ β© (βπ π¨) β π¨[πβ€π].
β  rule K1a. π free for π in π¨ β© βπ π¨ β’ π¨[πβ€π].   β Not in Mendelson theory.
  rule K1a. βπ π¨ β’ π¨[πβ€π].   β Not in Mendelson theory.
  rule K1b. formula π¨ object π object Β°π. βπ π¨ β’ π¨[πβ€π].
β]

  β Specialization or particularization:
  rule K1. formula π¨ object Β°π object π‘. βπ π¨ β’ π¨[πβ€π‘].

  axiom K2. π not free in π¨ β© (βπ: π¨ β π©) β (π¨ β βπ π©).
  
  rule Gen. formula π¨ object Β°π.
    π¨ β’β½πβΎ βπ π¨.

  β Not in Mendelson theory.
  rule Ex. π free for π in π¨ β© π¨[πβ€π] β’ βπ π¨. β Existence.
  postulate K3. formula sequence π formula π¨, π©. π, π¨ β’ π© β© π, βπ π¨ β’ π©.

  end formal system.

end theory KM.

