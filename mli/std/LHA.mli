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


theory LHA. β Logic: Propositional calculus by Hilbert-Ackerman, cf. Mendelson, p. 40.

  formal system.
    atom π, π₯. β False, true. Not in core of theory.
    formula π¨, π©, πͺ.

  β In the following axioms, β should be expanded using this definition:
  definition D1. π¨ β π© β (Β¬π¨) β¨ π©.

  axiom A1. π¨ β¨ π¨ β π¨.
  axiom A2. π¨ β π¨ β¨ π©.
  axiom A3. π¨ β¨ π© β π© β¨ π¨.
  axiom A4. (π© β πͺ) β (π¨ β¨ π© β π¨ β¨ πͺ).

  β Modus ponens
  rule MP. π¨, π¨ β π© β’ π©.

  β Deduction theorem
  postulate DT. formula sequence π formula π¨, π©. π, π¨ β’ π© β© π β’ π¨ β π©.


  definition D2. π¨ β§ π© β Β¬(Β¬π¨ β¨ Β¬π©).
  definition D3. π¨ β π© β (π¨ β π©) β§ (π© β π¨).
  axiom D4. π₯.
  definition D5. π β Β¬π₯.

  end formal system.

end theory LHA.

