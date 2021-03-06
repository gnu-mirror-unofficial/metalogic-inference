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


theory Eq. β Logic: Equivalence formulas. Cf. Kleene, p. 118-119.

  formal system.
    formula π¨, π©, πͺ.

  definition EQ. π¨ β π© β (π¨ β π©) β§ (π© β π¨).

  β Associative, commutative, distributive, idempotent and eleminiation laws.

  β Conjunction:
  axiom Cas. (π¨ β§ π©) β§ πͺ β π¨ β§ (π© β§ πͺ).
  axiom Ccm. π¨ β§ π© β π© β§ π¨.
  axiom Cds. π¨ β§ (π© β¨ πͺ) β (π¨ β§ π©) β¨ (π¨ β§ πͺ).
  axiom Cid. π¨ β§ π¨ β π¨.
  axiom Cel. π¨ β§ (π¨ β¨ π©) β π¨.

  β Disjunction
  axiom Das. (π¨ β¨ π©) β¨ πͺ β π¨ β¨ (π© β¨ πͺ).
  axiom Dcm. π¨ β¨ π© β π© β¨ π¨.
  axiom Dds. π¨ β¨ (π© β§ πͺ) β (π¨ β¨ π©) β§ (π¨ β¨ πͺ).
  axiom Did. π¨ β¨ π¨ β π¨.
  axiom Del. π¨ β¨ (π¨ β§ π©) β π¨.


  β Inference rules for special cases of implication, conjunction, and disjunction.
  rule Impre. π¨ β’ π¨ β π© β π©.
  rule Imcon. π© β’ π¨ β π© β π©.
  rule ImNpre. Β¬π¨ β’ π¨ β π© β Β¬π¨.
  rule ImNcon. Β¬π© β’ π¨ β π© β Β¬π¨.

  rule Cpre. π© β’ π¨ β§ π© β π¨.
  rule CNpre. Β¬π© β’ π¨ β§ π© β π©.
  rule Dpre. π© β’ π¨ β¨ π© β π¨.
  rule DNpre. Β¬π© β’ π¨ β¨ π© β π©.


  β Double negation law, denial of contradiction law, excluded middle law.
  rule DNL. β’ Β¬Β¬π¨ β π¨.
  rule DCL. β’ Β¬(π¨ β§ Β¬π¨) β π¨.
  rule EML. β’ π¨ β¨ Β¬π¨.


  β For simplifying a disjunction of conjunctions, or a conjunction of disjunctions.)
  rule SCD. β’ π¨ β§ (π© β¨ Β¬π©) β π¨.    β Not valid in intuitionstic logic.
  rule SDC. β’ π¨ β¨ (π© β§ Β¬π©) β π¨.
  rule SC. β’ π¨ β§ π© β§ Β¬π© β π© β§ Β¬π©.
  rule SD. β’ π¨ β¨ π© β¨ Β¬π© β π© β¨ Β¬π©.  β Not valid in intuitionstic logic.


  β Each two of β, β§, β¨ in terms of the other and Β¬. Not valid in intuitionstic logic.
  rule 56. β’ π¨ β¨ π© β Β¬(Β¬π¨ β§ Β¬π©).
  rule 57. β’ π¨ β§ π© β Β¬(Β¬π¨ β¨ Β¬π©).
  rule 58. β’ π¨ β π© β Β¬(π¨ β§ Β¬π©).
  rule 59. β’ π¨ β π© β Β¬π¨ β¨ π©.
  rule 60. β’ π¨ β§ π© β Β¬(π¨ β Β¬π©).
  rule 61. β’ π¨ β¨ π© β Β¬π¨ β π©.


  β Transfer of Β¬ across β§ and β¨ (De Morganβs laws, 1847).
  rule 62. β’ Β¬(π¨ β§ π©) β Β¬π¨ β¨ Β¬π©.  β Not valid in intuitionstic logic.
  rule 63. β’ Β¬(π¨ β¨ π©) β Β¬π¨ β§ Β¬π©.


  β π¨dditional results of interest for the intuitionistic system.
  rule 49a. β’ π¨ β Β¬Β¬π¨.
  rule 49b. β’ Β¬Β¬Β¬π¨ β Β¬π¨.
  rule 49c. β’ π¨ β¨ Β¬π¨ β (Β¬Β¬π¨ β π¨).
  rule 49d. β’ π¨ β¨ Β¬π¨ β (Β¬Β¬π¨ β π¨).

  rule 50a. β’ Β¬(π¨ β Β¬π¨).
  rule 51a. β’ Β¬Β¬(π¨ β¨ Β¬π¨).
  rule 51b. β’ Β¬Β¬(Β¬Β¬π¨ β π¨).

  rule 56a. β’ π¨ β¨ π© β Β¬(Β¬π¨ β§ Β¬π©).
  rule 56b. β’ Β¬π¨ β¨ π© β Β¬(π¨ β§ Β¬π©).

  rule 57a. β’ π¨ β§ π© β Β¬(Β¬π¨ β¨ Β¬π©).
  rule 57b. β’ π¨ β§ Β¬π© β Β¬(Β¬π¨ β¨ π©).

  rule 58a. β’ (π¨ β π©) β Β¬(π¨ β§ Β¬π©).
  rule 58b. β’ π¨ β Β¬π© β Β¬(π¨ β§ π©).

β  rule 58bβd. β’ π¨ β Β¬π© β Β¬(π¨ β§ π©) β Β¬Β¬π¨ β Β¬π© β Β¬Β¬(Β¬π¨ β¨ Β¬π©).

β  rule 58e,f. Β¬Β¬π© β π© β’ Β¬Β¬π¨ β π© β π¨ β π© β Β¬(π¨ β§ Β¬π©).
  rule 58g. β’ (Β¬Β¬π¨ β π©) β Β¬(π¨ β§ Β¬π©).

  rule 59a. β’ Β¬π¨ β¨ π© β (π¨ β π©).
  rule 59b. β’ (π¨ β π©) β Β¬Β¬(Β¬π¨ β¨ π©).
  rule 59c. β’ (Β¬π¨ β π©) β Β¬Β¬(π¨ β¨ π©).

  rule 60a. β’ π¨ β§ π© β Β¬(π¨ β Β¬ π©).
  rule 60b. β’ π¨ β§ Β¬π© β Β¬(π¨ β π©).
  rule 60c. β’ Β¬Β¬π¨ β§ π© β Β¬(π¨ β Β¬π©).

  rule 6la. β’ π¨ β¨ π© β (Β¬π¨ β π©).
β  rule 60d-f. β’ Β¬Β¬π¨ β§ Β¬π© β Β¬(π¨ β π©) β Β¬(Β¬π¨ β¨ π©) β Β¬Β¬(π¨ β§ Β¬π©).
β  rule 60g-i. β’ Β¬Β¬(π¨ β π©) β Β¬(π¨ β§ Β¬π©) β π¨ β Β¬Β¬π© β Β¬Β¬π¨ β Β¬Β¬π©.

  rule 61b. β’ Β¬(π¨ β¨ π©) β Β¬(Β¬π¨ β π©).
  rule 62a. β’ Β¬π¨ β¨ Β¬π© β Β¬(π¨ β§ π©).

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


  β Disjunction

  β Disjunction introduction, Addition:
  rule DI1. π¨ β’ π¨ β¨ π©.
  rule DI2. π© β’ π¨ β¨ π©.


  β Proof by cases, disjunction elimination.
  postulate PC. formula sequence π formula π¨, π©, πͺ.
    π, π¨ β’ πͺ; π, π© β’ πͺ β© π, π¨ β¨ π© β’ πͺ.

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

  β Reductio ad absurdum, proof by contradiction, negation introduction.
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
  rule Gen. formula π¨ object Β°π, Β°π.
   π¨ β’β½πβΎ βπ π¨.

  β Specialization, particularization, Universal instantiation/specification/elimination:
  β Named K1 and K1a in KM.mli.

  rule Spec. formula π¨ object π object Β°π.
    π free for π in π¨, βπ π¨ β’ π¨[π β€ π].

  β Substitution.
  rule Sub. formula π¨ object π object Β°π.
    π free for π in π¨, π¨ β’β½πβΎ π¨[π β€ π].


  β Existence, Existential quantifier

  β Existential introduction:
  rule ExI. formula π¨ object π object Β°π.
    π free for π in π¨, π¨[π β€ π] β’ βπ π¨.
[β
  rule ExIb. formula π¨ object π object Β°π.
    π free for π in π¨ β© π¨[π β€ π] β’ βπ π¨.
β]

  rule ExIa. formula π¨ object π object Β°π.
    π¨[π β€ π] β’ βπ π¨.


  β Existential elimination:
  postulate ExE. formula sequence π formula π¨, π© object Β°π.
    π not free in π©; π, π¨ β’ π© β© π, βπ π¨ β’β½πβΎ π©.


  β Biconditionals, Equivalence.

  β Equivalence reflexive, symmetric, and transitive properties.
  axiom EqR. π¨ β π¨.
  rule EqS. π¨ β π© β’ π© β π¨.
  rule EqT. π¨ β π©, π© β πͺ  β’ π¨ β πͺ.


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

  β Chain inference:
  rule ICh. formula π¨, π©, πͺ.
    π¨ β π©, π© β πͺ β’ π¨ β πͺ.
β    π¨ β π¨, β¦, π¨βnβ β π© β’ π¨ β π©.

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

end theory Eq.

