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


theory IR. β Logic: Inference rules. Cf. Kleene, p. 98-99.

  formal system.
    formula π¨, π©, πͺ.

    β Implication, Conditionals.

    β Modus ponens, Implication elimination, Conditional elimination, Detachment.
    rule MP. π¨, π¨ β π© β’ π©.

    β Modus tollens
    rule MT. π¨ β π©, Β¬π© β’ Β¬π¨.

    β Deduction theorem, Implication introduction, Conditional introduction.

    β No theory indicated:
    postulate DT1. formula sequence π formula π¨, π©.
      π, π¨ β’ π© β© π β’ π¨ β π©.

[β
    β With theory explicitly indicated:
    postulate DT2. theory π― formula sequence π formula π¨, π©.
      π, π¨ β’βπ―β π© β© π β’βπ―β π¨ β π©.

    β With metatheory explicitly indicated
    postulate DT3. metatheory π theory π― formula sequence π formula π¨, π©.
      π, π¨ β’βπ―β π© β©βπβ π β’βπ―β π¨ β π©.
β]

    β Conjunction

    β Conjunction introduction, Adjunction:
    rule CI. π¨, π© β’ π¨ β§ π©.

    β Conjunction elimination, Simplification:
    rule CE1. π¨ β§ π© β’ π¨.
    rule CE2. π¨ β§ π© β’ π©.
    rule CE. π¨ β§ π© β’ π¨, π©.  β Conclusion is formula set {π¨, π©}.


    β Disjunction

    β Disjunction introduction, Addition:
    rule DI1. π¨ β’ π¨ β¨ π©.
    rule DI2. π© β’ π¨ β¨ π©.
    postulate DI. π¨ β’ π¨ β¨ π©; π© β’ π¨ β¨ π©. β Metaformula sequence.


    β Proof by cases, disjunction elimination.
    postulate PC. formula sequence π formula π¨, π©, πͺ.
      π, π¨ β’ πͺ; π, π© β’ πͺ β© π, π¨ β¨ π© β’ πͺ.

    postulate PCa. formula π¨, π©, πͺ.
      π¨ β’ πͺ; π© β’ πͺ β© π¨ β¨ π© β’ πͺ.


    β Case analysis; variation of proof by cases without DT:
    rule CA. formula π¨, π©, πͺ.
      π¨ β πͺ, π© β πͺ, π¨ β¨ π© β’ πͺ.

    β Disjunctive syllogism, modus tollendo ponens:
    rule DS1. formula π¨, π©.
      π¨ β¨ π©, Β¬π¨ β’ π©.

    rule DS2. formula π¨, π©.
      π¨ β¨ π©, Β¬π© β’ π¨.

    β Constructive dilemma:
    rule CD. formula π¨, π©, πͺ, π«.
      π¨ β πͺ, π© β π«, π¨ β¨ π© β’ πͺ β¨ π«.

    β Destructive dilemma:
    rule DD. formula π¨, π©, πͺ, π«.
      π¨ β πͺ, π© β π«, Β¬πͺ β¨ Β¬π« β’ Β¬π¨ β¨ Β¬π©.


    β Negation:

    β Reductio ad absurdum, Negation introduction.
    postulate RA. formula sequence π formula π¨, π©.
      π, π¨ β’ π©; π, π¨ β’ Β¬π© β© π β’ Β¬π¨.


    β Reductio ad absurdum with negation.
    β Not valid in intuitionistic logic: requires excluded middle.
    postulate RAN. formula sequence π formula π¨, π©.
      π, Β¬π¨ β’ π©; π, Β¬π¨ β’ Β¬π© β© π β’ π¨.


    β Double negation elimination, not valid in intuitionistic logic.
    rule DNE. Β¬Β¬π¨ β’ π¨.

    β Double negation introduction.
    rule DNI. π¨ β’ Β¬Β¬π¨.


    β Noncontradiction, Weak Β¬-elimination, Consistency; cf. Kleene. p. 101, Mendelson, p. 34.
    rule NC. formula π¨, π©. Β¬π¨, π¨ β’ π©.


    β Generality, Universal quantifier

    β Generalization, Universal introduction:
    rule Gen. formula π¨ object Β°π.
     π¨ β’β½πβΎ βπ π¨.

    β Specialization, Universal instantiation/specification/elimination:
    β Named K1 and K1a in KM.mli.

    rule Spec. formula π¨ object π object Β°π.
      π free for π in π¨, βπ π¨ β’ π¨[π β€ π].


    β Strong universal quantifier (β-) introduction, cf. Kleene, p. 105.
    β π free for π in π¨, π not free in π¨ β© π¨[π β€ π] β’ βπ π¨

    β Universal quantifier change of variable:
    rule UV. formula π¨ object Β°π, Β°π.
      π free for π in π¨, π not free in π¨, βπ π¨ β’ βπ: π¨[π β€ π].
    β π free for π in π¨ β© βπ π¨ β’β½πβΎ βπ: π¨[π β€ π].

    β Substitution.

    β Object variable substitution, cf. Kleene p. 101:
    rule Sub. formula π¨ object π object Β°π.
    β  π free for π in π¨, π¨ β’ π¨[π β€ π].
     π free for π in π¨ β© π¨ β’β½πβΎ π¨[π β€ π].


    rule OVS. formula πͺ object Β°π object π.
    πͺ β’ πͺ[π β€ π].


    β Existence, Existential quantifier

    β Existential introduction:
    rule ExI. formula π¨ object π object Β°π.
      π¨[π β€ π] β’ βπ π¨.

    β Existential elimination:
    postulate ExE. formula sequence π formula π¨, π© object Β°π.
      π not free in π©; π, π¨ β’ π© β© π, βπ π¨ β’β½πβΎ π©.


    β Existential quantifier change of variable
    rule ExV. formula π¨ object Β°π, Β°π.
  β    π free for π in π¨, π not free in π¨ β© βπ π¨ β’ βπ: π¨[π β€ π].
  β    π free for π in π¨ β© βπ π¨ β’β½πβΎ βπ: π¨[π β€ π].
  β    π free for π in π¨, π not free in π¨, βπ π¨ β’ βπ: π¨[π β€ π].
  β     π free for π in π¨, βπ π¨ β’ βπ: π¨[π β€ π].
      π not free in π¨, βπ π¨ β’ βπ: π¨[π β€ π].
  β    βπ π¨ β’ βπ: π¨[π β€ π].


    β Biconditionals, Equivalence.

    β Equivalence reflexive, symmetric, and transitive properties.
    axiom EqR. π¨ β π¨.
    rule EqS. π¨ β π© β’ π© β π¨.
    rule EqT. π¨ β π©, π© β πͺ β’ π¨ β πͺ.


    β Equivalence (biconditional) introduction:
    rule EqI. π¨ β π©, π© β π¨ β’ π¨ β π©.

    β Equivalence (biconditional) elimination:

    rule EqE1. π¨ β π© β’ π¨ β π©.
    rule EqE2. π¨ β π© β’ π© β π¨.

    rule EqE3. π¨ β π©, π¨ β’ π©.
    rule EqE4. π¨ β π©, π© β’ π¨.

    β Equivalence (biconditional) negation elimination:
    rule EqNE1. π¨ β π©, Β¬π¨ β’ Β¬π©.
    rule EqNE2. π¨ β π©, Β¬π© β’ Β¬π¨.

    β Equivalence (biconditional) disjunction elimination:
    rule EqDE1. π¨ β π©, π¨ β¨ π© β’ π¨ β§ π©.
    rule EqDE2. π¨ β π©, Β¬π¨ β¨ Β¬π© β’ Β¬π¨ β§ Β¬π©.


    β Other rules, cf. Kleene, p. 113.

    β Identity:
    axiom Id. formula π¨. π¨ β π¨.
    axiom ID. formula π¨. π¨ β π¨.

    β Chain inference:
    rule ICh. formula π¨, π©, πͺ.
      π¨ β π©, π© β πͺ β’ π¨ β πͺ.
  β    π¨ β π¨β, β¦, π¨βnβ β π© β’ π¨ β π©.

    β Premises interchange:
    rule PI. π¨ β (π© β πͺ) β’ π© β (π¨ β πͺ).

    β Importation:
    rule Imp. π¨ β (π© β πͺ) β’ π¨ β§ π© β πͺ.

    β Exportation
    rule Exp. π¨ β§ π© β πͺ β’ π¨ β (π© β πͺ).


    β Introduction into an implication:

    rule ICI. π¨ β π© β’ (π© β πͺ) β (π¨ β πͺ).  β Implication conclusion introduction.
    rule IPI. π¨ β π© β’ (πͺ β π¨) β (πͺ β π©).  β Implication premise introduction.

    β Conjunctive member introduction:
    rule CMI1. π¨ β π© β’ π¨ β§ πͺ β π© β§ πͺ.
    rule CMI2. π¨ β π© β’ πͺ β§ π¨ β πͺ β§ π©.

    β Disjunctive member introduction.
    rule DMI1. π¨ β π© β’ π¨ β¨ πͺ β π© β¨ πͺ.
    rule DMI2. π¨ β π© β’ πͺ β¨ π¨ β πͺ β¨ π©.


    β Implication demonstration by refuting the premise:
    rule IRP1. formula π¨, π©. Β¬π¨ β’ π¨ β π©.
    rule IRP2. formula π¨, π©. π¨ β’ Β¬π¨ β π©.

    β Implication demonstration by proving the conclusion:
    rule IPC. formula π¨, π©. π© β’ π¨ β π©.


    β Implication contraposition:
    rule IC. π¨ β π© β’ Β¬π© β Β¬π¨.
    rule ICN. π¨ β Β¬π© β’ π© β Β¬π¨.

    β Implication contraposition with double negation suppressed.
    β Not valid in intuitionistic logic.
    rule ICDN1. Β¬π¨ β π© β’ Β¬π© β π¨.
    rule ICDN2. Β¬π¨ β Β¬π© β’ π© β π¨.


    β Supplemental rules for intuitionistic logic:
    rule IL1. π¨ β (π© β πͺ), Β¬Β¬π¨, Β¬Β¬π© β’ Β¬Β¬πͺ.
    rule IL2. Β¬Β¬(π¨ β π©) β’ Β¬Β¬π¨ β Β¬Β¬π©.
    rule IL3. Β¬Β¬(π¨ β π©), Β¬Β¬(π© β πͺ) β’ Β¬Β¬(π¨ β πͺ).
    axiom IL4. Β¬Β¬(π¨ β§ π©) β Β¬Β¬π¨ β§ Β¬Β¬π©.
    axiom IL5. Β¬Β¬(π¨ β π©) β Β¬Β¬(π¨ β π©) β§ Β¬Β¬(π© β π¨).

  end formal system.

end theory IR.

