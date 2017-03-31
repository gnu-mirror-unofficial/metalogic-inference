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

insert std/K.mli


theory ZF. -- Zermelo-Fraenkel set theory. Shoenfield, p.239.
  include theory K.

  formal system.
    -- binary infix =, ∈.
    constant empty.
  
  axiom Ext. -- Extensionality axiom.
    object x, y.
      (∀z: z ∈ x ⇔ z ∈ y) ⇒ x = y.
  [* Sets with equal members are equal. *]
  
  axiom Reg. -- Regularity axiom.
    object x.
      (∃y: y ∈ x) ⇒
        ∃y: y ∈ x ∧ ¬ ∃z: z ∈ x ∧ z ∈ y.
  [* If a set x has a member, then it also has a member y
     disjoint from x. *]
  
  rule Sub. -- Subset axiom.
    metaobject x, y, z  formula A.
      y not free in A, z not free in A,
      x =/= y, x =/= z, y =/= z
      ⊢ ∃z ∀x: x ∈ z ⇔ x ∈ y ∧ A.
  [* Given y, A, the set {x| x ∈ y ∧ A(x)} exists. *]

  rule IsSet. -- Definition of Set_x A symbol.
    metaobject x, y  formula A.
      y not free in A ⊢
        Set_x A ≔ ∃y ∀x: A ⇒ x ∈ y.
  [* There is a set y containing ∀x satisfying A(x). *]

-- trace_type trace_bind

  rule Rep. -- Replacement axiom.
    metaobject x, y, z, w  formula A.
      z not free in A, w not free in A ⊢
      (∀x ∃z ∀y: A ⇔ y ∈ z)
        ⇒ Set_y ∃x: x ∈ w ∧ A.
  [* Given, for ∀x, z_x ≔ {y| A(y)}, there is a set u (depending
     on w) containing ∀y such that A(x, y) for some x ∈ w. *]
  
  axiom Pow. -- Power set axiom.
    object x.
      Set_y ∀z: z ∈ y ⇒ z ∈ x.
  [* Given a set x, there is a set containing all subsets of x. *]

  axiom Inf. -- Axiom of infinity.
    ∃x:
      (∃y: y ∈ x ∧ ∀z: ¬ z ∈ y) -- x contains empty.
      ∧
      ∀y: y ∈ x ⇒ ∃z: z ∈ x
        ∧ ∀w: w ∈ z ⇔ w ∈ y ∨ w = y.
   [* There is a set x containing the empty set, ∧ such that
      if y ∈ x, then also the set y union {y} is ∈ x. *]

  -- Defining axiom:
  rule SetSymb. -- Set notation.
    formula A.
      Set_x A(x) ⊢ ∀x: x ∈ {x| A(x)} ⇔ A(x).

  definition SetPair.
    object x, y.
    {x, y} ≔ {z| z = x ∨ z = y}.

  definition UnitSet.
    object x. {x} ≔ {z| z = x}.
  
  definition EmptySet.
    ∅ ≔ {x| ¬ x = x}.

  definition EmptySet2.
    {} ≔ ∅.

  rule ImplicitSet.
    object y  term f  formula A.
    y not free in f, y not free in A
      ⊢ {_x f| A} = {y| ∃x: y = f ∧ A}.

  end formal system.

end theory ZF.

