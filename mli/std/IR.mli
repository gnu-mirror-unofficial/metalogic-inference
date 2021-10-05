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


theory IR. — Logic: Inference rules. Cf. Kleene, p. 98-99.

  formal system.
    formula 𝑨, 𝑩, 𝑪.

    — Implication, Conditionals.

    — Modus ponens, Implication elimination, Conditional elimination, Detachment.
    rule MP. 𝑨, 𝑨 ⇒ 𝑩 ⊢ 𝑩.

    — Modus tollens
    rule MT. 𝑨 ⇒ 𝑩, ¬𝑩 ⊢ ¬𝑨.

    — Deduction theorem, Implication introduction, Conditional introduction.

    — No theory indicated:
    postulate DT1. formula sequence 𝜞 formula 𝑨, 𝑩.
      𝜞, 𝑨 ⊢ 𝑩 ⊩ 𝜞 ⊢ 𝑨 ⇒ 𝑩.

[—
    — With theory explicitly indicated:
    postulate DT2. theory 𝒯 formula sequence 𝜞 formula 𝑨, 𝑩.
      𝜞, 𝑨 ⊢₍𝒯₎ 𝑩 ⊩ 𝜞 ⊢₍𝒯₎ 𝑨 ⇒ 𝑩.

    — With metatheory explicitly indicated
    postulate DT3. metatheory 𝓜 theory 𝒯 formula sequence 𝜞 formula 𝑨, 𝑩.
      𝜞, 𝑨 ⊢₍𝒯₎ 𝑩 ⊩₍𝓜₎ 𝜞 ⊢₍𝒯₎ 𝑨 ⇒ 𝑩.
—]

    — Conjunction

    — Conjunction introduction, Adjunction:
    rule CI. 𝑨, 𝑩 ⊢ 𝑨 ∧ 𝑩.

    — Conjunction elimination, Simplification:
    rule CE1. 𝑨 ∧ 𝑩 ⊢ 𝑨.
    rule CE2. 𝑨 ∧ 𝑩 ⊢ 𝑩.
    rule CE. 𝑨 ∧ 𝑩 ⊢ 𝑨, 𝑩.  — Conclusion is formula set {𝑨, 𝑩}.


    — Disjunction

    — Disjunction introduction, Addition:
    rule DI1. 𝑨 ⊢ 𝑨 ∨ 𝑩.
    rule DI2. 𝑩 ⊢ 𝑨 ∨ 𝑩.
    postulate DI. 𝑨 ⊢ 𝑨 ∨ 𝑩; 𝑩 ⊢ 𝑨 ∨ 𝑩. — Metaformula sequence.


    — Proof by cases, disjunction elimination.
    postulate PC. formula sequence 𝜞 formula 𝑨, 𝑩, 𝑪.
      𝜞, 𝑨 ⊢ 𝑪; 𝜞, 𝑩 ⊢ 𝑪 ⊩ 𝜞, 𝑨 ∨ 𝑩 ⊢ 𝑪.

    postulate PCa. formula 𝑨, 𝑩, 𝑪.
      𝑨 ⊢ 𝑪; 𝑩 ⊢ 𝑪 ⊩ 𝑨 ∨ 𝑩 ⊢ 𝑪.


    — Case analysis; variation of proof by cases without DT:
    rule CA. formula 𝑨, 𝑩, 𝑪.
      𝑨 ⇒ 𝑪, 𝑩 ⇒ 𝑪, 𝑨 ∨ 𝑩 ⊢ 𝑪.

    — Disjunctive syllogism, modus tollendo ponens:
    rule DS1. formula 𝑨, 𝑩.
      𝑨 ∨ 𝑩, ¬𝑨 ⊢ 𝑩.

    rule DS2. formula 𝑨, 𝑩.
      𝑨 ∨ 𝑩, ¬𝑩 ⊢ 𝑨.

    — Constructive dilemma:
    rule CD. formula 𝑨, 𝑩, 𝑪, 𝑫.
      𝑨 ⇒ 𝑪, 𝑩 ⇒ 𝑫, 𝑨 ∨ 𝑩 ⊢ 𝑪 ∨ 𝑫.

    — Destructive dilemma:
    rule DD. formula 𝑨, 𝑩, 𝑪, 𝑫.
      𝑨 ⇒ 𝑪, 𝑩 ⇒ 𝑫, ¬𝑪 ∨ ¬𝑫 ⊢ ¬𝑨 ∨ ¬𝑩.


    — Negation:

    — Reductio ad absurdum, Negation introduction.
    postulate RA. formula sequence 𝜞 formula 𝑨, 𝑩.
      𝜞, 𝑨 ⊢ 𝑩; 𝜞, 𝑨 ⊢ ¬𝑩 ⊩ 𝜞 ⊢ ¬𝑨.


    — Reductio ad absurdum with negation.
    — Not valid in intuitionistic logic: requires excluded middle.
    postulate RAN. formula sequence 𝜞 formula 𝑨, 𝑩.
      𝜞, ¬𝑨 ⊢ 𝑩; 𝜞, ¬𝑨 ⊢ ¬𝑩 ⊩ 𝜞 ⊢ 𝑨.


    — Double negation elimination, not valid in intuitionistic logic.
    rule DNE. ¬¬𝑨 ⊢ 𝑨.

    — Double negation introduction.
    rule DNI. 𝑨 ⊢ ¬¬𝑨.


    — Noncontradiction, Weak ¬-elimination, Consistency; cf. Kleene. p. 101, Mendelson, p. 34.
    rule NC. formula 𝑨, 𝑩. ¬𝑨, 𝑨 ⊢ 𝑩.


    — Generality, Universal quantifier

    — Generalization, Universal introduction:
    rule Gen. formula 𝑨 object °𝒙.
     𝑨 ⊢⁽𝒙⁾ ∀𝒙 𝑨.

    — Specialization, Universal instantiation/specification/elimination:
    — Named K1 and K1a in KM.mli.

    rule Spec. formula 𝑨 object 𝒕 object °𝒙.
      𝒕 free for 𝒙 in 𝑨, ∀𝒙 𝑨 ⊢ 𝑨[𝒙 ⤇ 𝒕].


    — Strong universal quantifier (∀-) introduction, cf. Kleene, p. 105.
    — 𝒚 free for 𝒙 in 𝑨, 𝒚 not free in 𝑨 ⊩ 𝑨[𝒙 ⤇ 𝒚] ⊢ ∀𝒙 𝑨

    — Universal quantifier change of variable:
    rule UV. formula 𝑨 object °𝒙, °𝒚.
      𝒚 free for 𝒙 in 𝑨, 𝒚 not free in 𝑨, ∀𝒙 𝑨 ⊢ ∀𝒚: 𝑨[𝒙 ⤇ 𝒚].
    — 𝒚 free for 𝒙 in 𝑨 ⊩ ∀𝒙 𝑨 ⊢⁽𝒚⁾ ∀𝒚: 𝑨[𝒙 ⤇ 𝒚].

    — Substitution.

    — Object variable substitution, cf. Kleene p. 101:
    rule Sub. formula 𝑨 object 𝒕 object °𝒙.
    —  𝒕 free for 𝒙 in 𝑨, 𝑨 ⊢ 𝑨[𝒙 ⤇ 𝒕].
     𝒕 free for 𝒙 in 𝑨 ⊩ 𝑨 ⊢⁽𝒙⁾ 𝑨[𝒙 ⤇ 𝒕].


    rule OVS. formula 𝑪 object °𝒛 object 𝒖.
    𝑪 ⊢ 𝑪[𝒛 ⤇ 𝒖].


    — Existence, Existential quantifier

    — Existential introduction:
    rule ExI. formula 𝑨 object 𝒕 object °𝒙.
      𝑨[𝒙 ⤇ 𝒕] ⊢ ∃𝒙 𝑨.

    — Existential elimination:
    postulate ExE. formula sequence 𝜞 formula 𝑨, 𝑩 object °𝒙.
      𝒙 not free in 𝑩; 𝜞, 𝑨 ⊢ 𝑩 ⊩ 𝜞, ∃𝒙 𝑨 ⊢⁽𝒙⁾ 𝑩.


    — Existential quantifier change of variable
    rule ExV. formula 𝑨 object °𝒙, °𝒚.
  —    𝒚 free for 𝒙 in 𝑨, 𝒚 not free in 𝑨 ⊩ ∃𝒙 𝑨 ⊢ ∃𝒚: 𝑨[𝒙 ⤇ 𝒚].
  —    𝒚 free for 𝒙 in 𝑨 ⊩ ∃𝒙 𝑨 ⊢⁽𝒚⁾ ∃𝒚: 𝑨[𝒙 ⤇ 𝒚].
  —    𝒚 free for 𝒙 in 𝑨, 𝒚 not free in 𝑨, ∃𝒙 𝑨 ⊢ ∃𝒚: 𝑨[𝒙 ⤇ 𝒚].
  —     𝒚 free for 𝒙 in 𝑨, ∃𝒙 𝑨 ⊢ ∃𝒚: 𝑨[𝒙 ⤇ 𝒚].
      𝒚 not free in 𝑨, ∃𝒙 𝑨 ⊢ ∃𝒚: 𝑨[𝒙 ⤇ 𝒚].
  —    ∃𝒙 𝑨 ⊢ ∃𝒚: 𝑨[𝒙 ⤇ 𝒚].


    — Biconditionals, Equivalence.

    — Equivalence reflexive, symmetric, and transitive properties.
    axiom EqR. 𝑨 ⇔ 𝑨.
    rule EqS. 𝑨 ⇔ 𝑩 ⊢ 𝑩 ⇔ 𝑨.
    rule EqT. 𝑨 ⇔ 𝑩, 𝑩 ⇔ 𝑪 ⊢ 𝑨 ⇔ 𝑪.


    — Equivalence (biconditional) introduction:
    rule EqI. 𝑨 ⇒ 𝑩, 𝑩 ⇒ 𝑨 ⊢ 𝑨 ⇔ 𝑩.

    — Equivalence (biconditional) elimination:

    rule EqE1. 𝑨 ⇔ 𝑩 ⊢ 𝑨 ⇒ 𝑩.
    rule EqE2. 𝑨 ⇔ 𝑩 ⊢ 𝑩 ⇒ 𝑨.

    rule EqE3. 𝑨 ⇔ 𝑩, 𝑨 ⊢ 𝑩.
    rule EqE4. 𝑨 ⇔ 𝑩, 𝑩 ⊢ 𝑨.

    — Equivalence (biconditional) negation elimination:
    rule EqNE1. 𝑨 ⇔ 𝑩, ¬𝑨 ⊢ ¬𝑩.
    rule EqNE2. 𝑨 ⇔ 𝑩, ¬𝑩 ⊢ ¬𝑨.

    — Equivalence (biconditional) disjunction elimination:
    rule EqDE1. 𝑨 ⇔ 𝑩, 𝑨 ∨ 𝑩 ⊢ 𝑨 ∧ 𝑩.
    rule EqDE2. 𝑨 ⇔ 𝑩, ¬𝑨 ∨ ¬𝑩 ⊢ ¬𝑨 ∧ ¬𝑩.


    — Other rules, cf. Kleene, p. 113.

    — Identity:
    axiom Id. formula 𝑨. 𝑨 ⇒ 𝑨.
    axiom ID. formula 𝑨. 𝑨 ⇒ 𝑨.

    — Chain inference:
    rule ICh. formula 𝑨, 𝑩, 𝑪.
      𝑨 ⇒ 𝑩, 𝑩 ⇒ 𝑪 ⊢ 𝑨 ⇒ 𝑪.
  —    𝑨 ⇒ 𝑨₁, …, 𝑨₍n₎ ⇒ 𝑩 ⊢ 𝑨 ⇒ 𝑩.

    — Premises interchange:
    rule PI. 𝑨 ⇒ (𝑩 ⇒ 𝑪) ⊢ 𝑩 ⇒ (𝑨 ⇒ 𝑪).

    — Importation:
    rule Imp. 𝑨 ⇒ (𝑩 ⇒ 𝑪) ⊢ 𝑨 ∧ 𝑩 ⇒ 𝑪.

    — Exportation
    rule Exp. 𝑨 ∧ 𝑩 ⇒ 𝑪 ⊢ 𝑨 ⇒ (𝑩 ⇒ 𝑪).


    — Introduction into an implication:

    rule ICI. 𝑨 ⇒ 𝑩 ⊢ (𝑩 ⇒ 𝑪) ⇒ (𝑨 ⇒ 𝑪).  — Implication conclusion introduction.
    rule IPI. 𝑨 ⇒ 𝑩 ⊢ (𝑪 ⇒ 𝑨) ⇒ (𝑪 ⇒ 𝑩).  — Implication premise introduction.

    — Conjunctive member introduction:
    rule CMI1. 𝑨 ⇒ 𝑩 ⊢ 𝑨 ∧ 𝑪 ⇒ 𝑩 ∧ 𝑪.
    rule CMI2. 𝑨 ⇒ 𝑩 ⊢ 𝑪 ∧ 𝑨 ⇒ 𝑪 ∧ 𝑩.

    — Disjunctive member introduction.
    rule DMI1. 𝑨 ⇒ 𝑩 ⊢ 𝑨 ∨ 𝑪 ⇒ 𝑩 ∨ 𝑪.
    rule DMI2. 𝑨 ⇒ 𝑩 ⊢ 𝑪 ∨ 𝑨 ⇒ 𝑪 ∨ 𝑩.


    — Implication demonstration by refuting the premise:
    rule IRP1. formula 𝑨, 𝑩. ¬𝑨 ⊢ 𝑨 ⇒ 𝑩.
    rule IRP2. formula 𝑨, 𝑩. 𝑨 ⊢ ¬𝑨 ⇒ 𝑩.

    — Implication demonstration by proving the conclusion:
    rule IPC. formula 𝑨, 𝑩. 𝑩 ⊢ 𝑨 ⇒ 𝑩.


    — Implication contraposition:
    rule IC. 𝑨 ⇒ 𝑩 ⊢ ¬𝑩 ⇒ ¬𝑨.
    rule ICN. 𝑨 ⇒ ¬𝑩 ⊢ 𝑩 ⇒ ¬𝑨.

    — Implication contraposition with double negation suppressed.
    — Not valid in intuitionistic logic.
    rule ICDN1. ¬𝑨 ⇒ 𝑩 ⊢ ¬𝑩 ⇒ 𝑨.
    rule ICDN2. ¬𝑨 ⇒ ¬𝑩 ⊢ 𝑩 ⇒ 𝑨.


    — Supplemental rules for intuitionistic logic:
    rule IL1. 𝑨 ⇒ (𝑩 ⇒ 𝑪), ¬¬𝑨, ¬¬𝑩 ⊢ ¬¬𝑪.
    rule IL2. ¬¬(𝑨 ⇒ 𝑩) ⊢ ¬¬𝑨 ⇒ ¬¬𝑩.
    rule IL3. ¬¬(𝑨 ⇒ 𝑩), ¬¬(𝑩 ⇒ 𝑪) ⊢ ¬¬(𝑨 ⇒ 𝑪).
    axiom IL4. ¬¬(𝑨 ∧ 𝑩) ⇔ ¬¬𝑨 ∧ ¬¬𝑩.
    axiom IL5. ¬¬(𝑨 ⇔ 𝑩) ⇔ ¬¬(𝑨 ⇒ 𝑩) ∧ ¬¬(𝑩 ⇒ 𝑨).

  end formal system.

end theory IR.

