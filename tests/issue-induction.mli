
{— level max 100 —}
{— sublevel max 10000 —}
{— unify count max 600000 —}


—input std/SM.mli
—input std/IR.mli


theory TS1.  — Test theory S (number theory).
—  include theory SM.
—  include theory IR.
  formal system.
  rule MP. formula 𝑨, 𝑩. 𝑨, 𝑨 ⇒ 𝑩 ⊢ 𝑩.

  rule CI. formula 𝑨, 𝑩. 𝑨, 𝑩 ⊢ 𝑨 ∧ 𝑩.


—  axiom K0. formula 𝑩 object 𝒕, °𝒚. (∀𝒚 𝑩) ⇒ 𝑩[𝒚 ⤇ 𝒕].
  axiom K0. formula 𝑩 object °𝒚 object 𝒕. (∀𝒚 𝑩) ⇒ 𝑩[𝒚 ⤇ 𝒕].

—  rule K1. formula 𝑨 object 𝑡, °𝒙. ∀𝒙 𝑨 ⊢ 𝑨[𝒙 ⤇ 𝑡].
  rule K1. formula 𝑨 object °𝒙 object 𝒕. ∀𝒙 𝑨 ⊢ 𝑨[𝒙 ⤇ 𝒕].

  rule Gen. formula 𝑩 object °𝒚. 𝑩 ⊢⁽𝒚⁾ ∀𝒚 𝑩.

—  rule Ex. formula 𝑩 object °𝒚, 𝒕. 𝑩[𝒚 ⤇ 𝒕] ⊢ ∃𝒚 𝑩.
  rule Ex. formula 𝑩 object °𝒚 object 𝒕. 𝑩[𝒚 ⤇ 𝒕] ⊢ ∃𝒚 𝑩.

  — Object variable substitution, Kleene p. 101:
  rule OVS. formula 𝑪 object °𝒛 object 𝒖.
    𝑪 ⊢⁽𝒛⁾ 𝑪[𝒛 ⤇ 𝒖]. — 𝒛 is varied in deduction

  rule IR1. predicate variable 𝑷 function constant s.
    𝑷(0), ∀𝑥: 𝑷(𝑥) ⇒ 𝑷(s(𝑥)) ⊢ ∀𝑦 𝑷(𝑦).

  — Since 𝑥 is declared, it is the same named variable in both quantifiers.
  rule IR1x. object °𝑥 predicate variable 𝑷 function constant s.
    𝑷(0), ∀𝑥: 𝑷(𝑥) ⇒ 𝑷(s(𝑥)) ⊢ ∀𝑥 𝑷(𝑥).


  axiom S9a. predicate variable 𝑷 function constant s.
    𝑷(0) ∧ (∀𝑥: 𝑷(𝑥) ⇒ 𝑷(s(𝑥))) ⇒ ∀𝑦 𝑷(𝑦).

  axiom S9b. predicate variable 𝑷 function constant s.
    𝑷(0) ∧ (∀𝑥: 𝑷(𝑥) ⇒ 𝑷(s(𝑥))) ⇒ ∀𝑥 𝑷(𝑥).


  axiom S9c. object °𝑥 predicate variable 𝑷 function constant s.
    𝑷(0) ∧ (∀𝑥: 𝑷(𝑥) ⇒ 𝑷(s(𝑥))) ⇒ ∀𝑥 𝑷(𝑥).



  axiom A. object 𝑡 function constant s.
    𝑡 ≠ 0 ⇒ ∃𝑦: s(𝑦) = 𝑡.

  axiom B. function constant s.
    ∀𝑦: s(𝑦) ≠ 0.

  axiom C. object 𝑡 function constant s.
    s(𝑡) ≠ 0.

  axiom D. object °𝒙 function constant s.
    s(𝒙) ≠ 0.



  axiom IB. predicate constant 𝑃.
    ∀𝑦: 𝑃(𝑦, 𝑦).

  axiom IF. object 𝑡  predicate constant 𝑃.
    𝑃(𝑡, 𝑡).

  axiom IL. object °𝒙  predicate constant 𝑃.
    𝑃(𝒙, 𝒙).

  axiom JB. predicate constant 𝑃.
    ∀𝑥, 𝑦: 𝑃(𝑥, 𝑦).

  axiom JF. object 𝑡, 𝑢 predicate constant 𝑃.
    𝑃(𝑡, 𝑢).

  axiom JL. object °𝒙, °𝒚 predicate constant 𝑃.
    𝑃(𝒙, 𝒚).

  rule E. predicate variable 𝑷.
    ∀𝒚: 𝑷(𝒚) ⊢ ∀𝒙 𝑷(𝒙).


  axiom T8a. object °𝒙, °𝒚, °𝒛 function constant s.
    𝒙 = 𝒚 ⇒ 𝒙 + s(𝒛) = 𝒚 + s(𝒛).

  axiom T8b. object 𝒙, 𝒚, 𝒛 function constant s.
    𝒙 = 𝒚 ⇒ 𝒙 + s(𝒛) = 𝒚 + s(𝒛).


  end formal system.

{— thread count 0 —}

{— trace result —}
{— trace unspecializable —}
{— trace variable label —}

  definition Da. predicate constant 𝐴 object °𝒙, °𝒚 object 𝒛.
    𝐴(𝒛) ≔ 𝒙 = 𝒚 ⇒ 𝒙 + 𝒛 = 𝒚 + 𝒛.

  definition Db. predicate constant 𝐴 object 𝒙, 𝒚 object 𝒛.
    𝐴(𝒛) ≔ 𝒙 = 𝒚 ⇒ 𝒙 + 𝒛 = 𝒚 + 𝒛.

  — In iia, if the definition Da is changed from object to term 𝒙, 𝒚, then
  — then these become unspecialized implicit parameters in the proof that
  — must unify with the variables in axiom T8a, so if these are not terms
  — as well, the proof will fail.
  — True.
  lemma iia. object °𝒛 predicate constant 𝐴 function constant s.
    𝐴(𝒛) ⊢ 𝐴(s(𝒛))
—    𝐴(s(𝒛))
  proof
—    8. object 𝒙, 𝒚, 𝒛. 𝒙 = 𝒚 ⇒ 𝒙 + s(𝒛) = 𝒚 + s(𝒛) by T8a.
    9. 𝐴(s(𝒛)) by T8a, Da.
  ∎


  — True.
  lemma iib. object 𝒛 predicate constant 𝐴 function constant s.
    𝐴(𝒛) ⊢ 𝐴(s(𝒛))
—    𝐴(s(𝒛))
  proof
—    8. object 𝒙, 𝒚, 𝒛. 𝒙 = 𝒚 ⇒ 𝒙 + s(𝒛) = 𝒚 + s(𝒛) by T8b.
    9. 𝐴(s(𝒛)) by T8b, Db.
  ∎

[—
  — Converting object variables to term variables with OVS is expensive.
  — True.
  lemma iii. object 𝒙 object 𝒚 object 𝒛 function constant s.
    𝒙 = 𝒚 ⇒ 𝒙 + s(𝒛) = 𝒚 + s(𝒛)
  proof
    by T8a.
    — by OVS: OVS: OVS: T8a. — Time 23s.
    — T8a, OVS. — Time 39s.
  ∎
—]

{— expand_implicit_premise —}

  — This proof uses [°𝒙 ↦ '°𝒙] when the premise is lifted out.
  — The feature allows limited variables to behave synonymously with universally
  — quantified (∀) variables.
  lemma iv. object °𝒙 function constant s.
    ∃𝑤: 𝒙 = s(𝑤) ⊢ ∃𝑦: 𝒙 = s(𝑦)
  by premise iv.

  — In this proof, '𝒙 remains unspecialized when used as a premise.
  — This feature makes ordinary object variables behave as terms, and
  — not specialize in proof, thus allowing any value be substituted after
  — the proof.
  lemma ivb. object 𝒙 function constant s.
    ∃𝑤: 𝒙 = s(𝑤) ⊢ ∃𝑦: 𝒙 = s(𝑦)
  by premise ⊢.


  — True
  lemma SaO. object °𝒖 function constant s.
    s(𝒖) ≠ 0 ⊢⁽𝒖⁾ s(0) ≠ 0
  by OVS: premise.

  — False: premise term variables behave as though having an existential quantifier.
  lemma SaT. object 𝒕 function constant s.
    s(𝒕) ≠ 0 ⊢ s(0) ≠ 0
  by premise.

  — True if free variables do not unify with terms in the premise.
  lemma Sa. object °𝑥 function constant s.
    s(𝑥) ≠ 0 ⊢⁽𝑥⁾ s(0) ≠ 0
  by OVS: premise ⊢.


  — True: A specialization of K1.
  lemma Sb. function constant s.
    ∀𝑥: s(𝑥) ≠ 0 ⊢ s(0) ≠ 0
  by K1.

  — True
  lemma IR1a. object °𝑥 predicate variable 𝑷 function constant s.
    𝑷(0), ∀𝑥: 𝑷(𝑥) ⇒ 𝑷(s(𝑥)) ⊢ ∀𝑥 𝑷(𝑥)
  by MP: CI; S9a. — MP: CI, S9a.
  —by MP: CI, S9a.

  — True
  lemma IR1b. predicate variable 𝑷 function constant s.
    𝑷(0), ∀𝑥: 𝑷(𝑥) ⇒ 𝑷(s(𝑥)) ⊢ ∀𝑥 𝑷(𝑥)
  by MP: CI; S9a. — MP: CI, S9a.

  — True
  lemma IR1c. predicate variable 𝑷 function constant s.
    𝑷(0), ∀𝑥: 𝑷(𝑥) ⇒ 𝑷(s(𝑥)) ⊢ ∀𝑦 𝑷(𝑦)
  by MP: CI; S9a. — MP: CI, S9a.

—{— trace proof —}


  — True: The limited variable °𝒛 remains a variable, and therefore keeps generality.
  lemma IR2a. predicate variable 𝑷 object °𝒛 function constant s.
    𝑷(0), 𝑷(𝒛) ⇒ 𝑷(s(𝒛)) ⊢⁽¹ 𝒛⁾ 𝑷(𝒛)
  by K1: IR1: Gen. — K1, Gen, IR1, premise.

  — False. P(𝑥, 𝑥) ⊢ P('𝑥, '𝑦)
  lemma Q1. object °𝒙, °𝒚 predicate variable 𝑃.
    𝑃(𝒙, 𝒙) ⊢ 𝑃(𝒙, 𝒚)
  result by premise.

  — False. P(𝑥, 𝑥) ⊢ P('𝑦, '𝑥)
  lemma Q2. object °𝒙, °𝒚 predicate constant 𝑃.
    𝑃(𝒙, 𝒙) ⊢ 𝑃(𝒚, 𝒙)
  result by premise.



  — True: The ordinary object variable 𝒛 cannot be substituted with a non-variable
  — term, which would cause the formula to become more special.
  lemma IR2b. predicate variable 𝑷 object °𝒛 function constant s.
    𝑷(0), 𝑷(𝒛) ⇒ 𝑷(s(𝒛)) ⊢⁽¹ 𝒛⁾ 𝑷(𝒛)
  by K1: IR1: Gen. — K1, Gen, IR1, premise.


  — False: Though the limited variable °𝒛 remains a variable, and therefore keeps
  — generality, there is no variation of 𝒛 indicated (comes from the removal of the
  — universal quantifier in the premise IR1x).
  lemma IR2x. predicate variable 𝑷 object °𝒛 function constant s.
    𝑷(0), 𝑷(𝒛) ⇒ 𝑷(s(𝒛)) ⊢ 𝑷(𝒛)
  by K1: IR1x: Gen:. — K1, Gen, IR1, premise.


  — False: the term can be specialised, becoming a more specific statement, e.g.
  — 𝑃(0) ⊢ 𝑃(𝑡)
  lemma Q. object 𝑡, 𝑢 predicate constant 𝑃.
    𝑃(𝑢) ⊢ 𝑃(𝑡)
  by K1: Gen: premise ⊢. — E, Gen, K1.

  — True
  lemma Q0. object °𝒙, °𝒚 predicate constant 𝑃.
    𝑃(𝒙, 𝒚) ⊢ 𝑃(𝒙, 𝒚)
  result by premise.


—{— trace unify —}


[—
  — True: The limited variable °𝒙 remains a variable, and therefore keeps generality.
  lemma Q1. object °𝒙, 𝒕 predicate constant 𝑃.
    𝑃(𝒙) ⊢ 𝑃(𝒕)
  proof
    1. 𝑃(𝒙) by premise.
    2a. ∀𝒙 𝑃(𝒙) by Gen: 1.
    2b. ∀𝑥 𝑃(𝑥) by Gen: 1.
    2c. ∀𝑥 𝑃(𝑥) by 2a.
    3. 𝑃(𝒕) by K1: 2a.
—    by K1: Gen: premise ⊢. — E, Gen, K1.
  ∎


  — True: Ordinary object variable 𝑥 does not unify with terms, thus not
  — becoming more special.
  lemma Q2. object °𝑥 object 𝒕 predicate constant 𝑃.
    𝑃(𝑥) ⊢ 𝑃(𝒕)
  proof
    1. 𝑃(𝑥) by premise.
    2. ∀𝑥 𝑃(𝑥) by Gen: 1.
    3. 𝑃(𝒕) by K1: 2.
—    by K1: Gen: premise ⊢. — E, Gen, K1.
  ∎
—]
[—
  — Moved to issue-induction-2.mli
  — True
  lemma Q2a. object °𝑥 object 𝒕 predicate constant 𝑃.
    𝑃(𝑥) ⊢ 𝑃(𝒕)
  by OVS, premise.


  — True
  lemma Q2b. object °𝑥, °𝑦 object 𝒕 predicate constant 𝑃.
    𝑃(𝑥, 𝑦) ⊢ 𝑃(𝒕, 𝒕)
  by OVS, premise.

  — Without explicit premise:

  — True
  lemma Q2c. object °𝑥 object 𝒕 predicate constant 𝑃.
    𝑃(𝑥) ⊢ 𝑃(𝒕)
  by OVS.


  — True
  lemma Q2d. object °𝑥, °𝑦 object 𝒕 predicate constant 𝑃.
    𝑃(𝑥, 𝑦) ⊢ 𝑃(𝒕, 𝒕)
  by OVS.
—]

  — Instead of Q2, one has the following, where a term and be replaced by
  — an existential quantifier.
  lemma Q3. object 𝒕 predicate constant 𝑃.
    𝑃(𝒕) ⊢ ∃𝑥 𝑃(𝑥)
  proof
    1. 𝑃(𝒕) by premise.
    2. ∃𝑥 𝑃(𝑥) by Ex, 1.
    by Ex. — E, Gen, K1.
  ∎


[—
  lemma Q1a. object 𝑡, °𝑢 predicate constant 𝑃.
    𝑃(𝑢) ⊢ 𝑃(𝑡)
  proof
    1. 𝑃(𝑢) by premise.
    2. ∀𝑢 𝑃(𝑢) by Gen, 1.
    3. 𝑃(𝑡) by K1, 2.
    by K1: Gen: premise ⊢. — E, Gen, K1.
  ∎

  lemma Q2a. object 𝑡, 𝑢 predicate constant 𝑃.
    𝑃(𝑢) ⊢ 𝑃(𝑡)
  proof
    1. 𝑃(𝑢) by premise.
    2. ∀𝑢 𝑃(𝑢) by Gen; 1.
—    3. 𝑃(𝑡) by K1; 2.
—    by K1: Gen: premise ⊢. — E, Gen, K1.
  ∎
—]


  — True
  lemma K. formula 𝑨 object 𝑡, °𝒙. ∀𝒙 𝑨 ⊢ 𝑨[𝒙 ⤇ 𝑡]
  by K0, MP.


  — True, u(𝑦, °𝒙) = [𝑦 ↦ °𝒙], 𝑦 bound of B, °𝒙 of K1.
  lemma S. object 𝑡 function constant s.
    s(𝑡) ≠ 0
  by K1: B. — B, K1.

  — True, u(𝑡, '°𝒙) = [𝑡 ↦ '°𝒙], 𝑡 free of C, '°𝒙 of Gen.
  lemma T. function constant s.
    ∀𝑦: s(𝑦) ≠ 0
  by Gen: C. — Gen, C.

  — True, u(°𝑡, '°𝒙₁₀) = ∅.
  lemma X. object °𝑡 function constant s.
    s(𝑡) ≠ 0 ⊢⁽𝑡⁾ ∀𝑦: s(𝑦) ≠ 0
  by Gen, premise.

  — True, u('°𝑡, '°𝒙) = ∅, '°𝑡 of Y, '°𝒙 of Gen.
  lemma Y. object °𝑡 function constant s.
    s(𝑡) ≠ 0 ⊢⁽𝑡⁾ ∀𝑦: s(𝑦) ≠ 0
  by Gen, premise.

  — True, u('°𝑡, '°𝑡) = I, u(°𝒙₁₀, '°𝑡) = [°𝒙₁₀ ↦ '°𝑡], '°𝑡 of Z, °𝒙₁₀ of Gen.
  lemma Z. object °𝑡 function constant s.
    s(𝑡) ≠ 0 ⊢⁽𝑡⁾ ∀𝑡: s(𝑡) ≠ 0
  by Gen.

  — False. object 𝑡 indicates a term in a premise.
  lemma Z1. object 𝑡 function constant s.
    s(𝑡) ≠ 0 ⊢ ∀𝑡: s(𝑡) ≠ 0
  by Gen, premise.

  — True. object 𝑡 indicates a term in a premise, quantified as existence.
  lemma Z2. object 𝑡 function constant s.
    s(𝑡) ≠ 0 ⊢ ∃𝑡: s(𝑡) ≠ 0
  by Ex.

  — False
  lemma KB. predicate constant 𝑃.
    ∀𝑥, 𝑦: 𝑃(𝑥, 𝑦)
  by IB.

  — False
  lemma KF. object 𝑡, 𝑢 predicate constant 𝑃.
    𝑃(𝑡, 𝑢)
  by IF.

  — False
  lemma KL. object °𝒙, °𝒚 predicate constant 𝑃.
    𝑃(𝒙, 𝒚)
  by IL.


  — True
  lemma LB. predicate constant 𝑃.
    ∀𝑥, 𝑦: 𝑃(𝑥, 𝑦)
  by JB.

  — True
  lemma LF. object 𝑡, 𝑢 predicate constant 𝑃.
    𝑃(𝑡, 𝑢)
  by JF.

  — True
  lemma LL. object °𝒙, °𝒚 predicate constant 𝑃.
    𝑃(𝒙, 𝒚)
  by JL.


  — True
  lemma MB. predicate constant 𝑃.
    ∀𝑥: 𝑃(𝑥, 𝑥)
  by IB.

  — True
  lemma MF. object 𝑡 predicate constant 𝑃.
    𝑃(𝑡, 𝑡)
  by IF.

  — True
  lemma ML. object °𝒙 predicate constant 𝑃.
    𝑃(𝒙, 𝒙)
  by IL.


  — Induction Rule.

[—
  — True, as 𝑡 is limited, and thefore is the same named variable
  — in the premise and the conclusion of the inference statement.
  — Explicitly, the statement is
  —   °𝑡 ≠ 0 ⊢ ∀°𝑡 ∃𝑦: s(𝑦) = °𝑡
  lemma X. object °𝑡 function constant s.
    𝑡 ≠ 0 ⊢ ∀𝑡 ∃𝑦: s(𝑦) = 𝑡
  proof
    by Gen: MP: premise ⊢; A. — Gen, A, MP.
    1. 𝑡 ≠ 0 by premise.
    2. ∃𝑦: s(𝑦) = 𝑡 by MP: 1; A. — 1, MP, A.
    3. ∀𝑡 ∃𝑦: s(𝑦) = 𝑡 by Gen: 2. — Gen, 2.
  ∎

  — False, as 𝑡 is declared an ordinary object variable, and therefore
  — only appears in the free occurrences of the statement, which is the
  — premise. The variables 𝑡 and 𝑦 in the conclusion are bound, and have
  — different names internally, using a placeholder symbol #:
  —   #¹ and #²
  —   #₁ and #₂
  — Using that explicitly, the statement is
  —   𝑡 ≠ 0 ⊢ ∀#¹ ∃#²: #² = #¹
  —   𝑡 ≠ 0 ⊢ ∀#₁ ∃#₂: #₂ = #₁
  lemma Y. object 𝑡 function constant s.
    𝑡 ≠ 0 ⊢ ∀𝑡 ∃𝑦: s(𝑦) = 𝑡
  proof
    by Gen: MP: premise ⊢; A. — Gen, A, MP.
    1. 𝑡 ≠ 0 by premise.
    2. ∃𝑦: s(𝑦) = 𝑡 by MP: 1; A. — 1, MP, A.
    3. ∀𝑡 ∃𝑦: s(𝑦) = 𝑡 by Gen: 2. — Gen, 2.
  ∎
—]



{— trace result —}
{— trace unspecializable —}
—{— trace variable label —}


  — False. Mixes 𝑥 and 𝒙:
  lemma U. predicate variable 𝑷 object °𝒙 function constant s.
    𝑷(0), ∀𝑥: 𝑷(𝒙) ⇒ 𝑷(s(𝒙)) ⊢ ∀𝑥 𝑷(𝑥)
  proof
    4b. ∀𝑥 𝑷(𝑥) by IR1, premise.
  ∎


  — False. Mixes 𝑥 and 𝒙:
  lemma W. predicate variable 𝑷 object °𝒙 function constant s.
    𝑷(0), ∀𝑥: 𝑷(𝒙) ⇒ 𝑷(s(𝒙)) ⊢ ∀𝑥 𝑷(𝑥)
  proof
    1. 𝑷(0) by premise.
    2. ∀𝑥: 𝑷(𝒙) ⇒ 𝑷(s(𝒙)) by premise.
    3. ∀𝑥 𝑷(𝑥) by IR1, 1, 2.
—    4b. ∀𝑥 𝑷(𝑥) by IR1, premise.
    
  ∎


  — True: The limited object variable °𝒙 keeps the generality in the premise,
  — As it only is substituted with other at least general variables.
  lemma IR2. predicate variable 𝑷 object °𝒙 function constant s.
    𝑷(0), 𝑷(𝒙) ⇒ 𝑷(s(𝒙)) ⊢⁽¹ 𝒙⁾ 𝑷(𝒙)
  proof
    by K1: IR1: Gen. — K1, Gen, IR1, premise.
—    by K1: Gen, IR1, premise.
    1. 𝑷(0) by premise.
    2. 𝑷(𝒙) ⇒ 𝑷(s(𝒙)) by premise.
    3. ∀𝒙: 𝑷(𝒙) ⇒ 𝑷(s(𝒙)) by Gen, 2.
[—
    — True: u('𝑥, 𝒙) = ['𝑥 ↦ °𝒙], '𝑥 bound of 3a, °𝒙 of Gen.
    —       u(°𝒙, '°𝒙) = [°𝒙 ↦ '°𝒙], °𝒙 of Gen, '°𝒙 of 2.
    3a. ∀𝑥: 𝑷(𝑥) ⇒ 𝑷(s(𝑥)) by Gen, 2.

    — Correct, but not useful:
    3b. ∀𝑥: 𝑷(𝒙) ⇒ 𝑷(s(𝒙)) by Gen, 2.
    4b. ∀𝑥 𝑷(𝑥) by IR1: 1; 3b. — 1, 3, IR1.

    3c. ∀𝑥: 𝑷(𝑥) ⇒ 𝑷(s(𝑥)) by Gen, 2.
—]
    4. ∀𝑥 𝑷(𝑥) by IR1: 1; 3. — 1, 3, IR1.

    5. 𝑷(𝒙) by K1: 4. — 4, K1.

    7. 𝑷(𝒙) by K1: IR1: premise; Gen: premise IR2. —
—    8. 𝑷(𝒙) by K1: IR1: premise IR2; Gen: premise IR2.
  ∎

{— strict proof —}
—{— conditional proof —}

  — False: The term variable 𝒛 can be substituted with a non-variable
  — term, causing the formula to become more special.
  lemma IR3. predicate variable 𝑷 object 𝒛 function constant s.
    𝑷(0), 𝑷(𝒛) ⇒ 𝑷(s(𝒛)) ⊢ 𝑷(𝒛)
  proof
    — False if u(°𝒛, '𝒛) = ∅.
—    by K1: IR1: premise IR3; Gen: premise IR3. — K1, Gen, IR1, premise.

    1. 𝑷(0) by premise.
    2. 𝑷(𝒛) ⇒ 𝑷(s(𝒛)) by premise.
—    2a. object °𝒚. 𝑷(𝒚) ⇒ 𝑷(s(𝒚)) by 2.
    3. ∀𝑥: 𝑷(𝑥) ⇒ 𝑷(s(𝑥)) by Gen, 2.
[—
    3a. ∀𝒛: 𝑷(𝒛) ⇒ 𝑷(s(𝒛)) by Gen, 2.

    — Erroneously passes, or maybe correct, but not useful:
    3b. ∀𝑥: 𝑷(𝒛) ⇒ 𝑷(s(𝒛)) by Gen, 2.
    4b. ∀𝑥 𝑷(𝒛) by IR1: 1; 3b. — 1, 3, IR1.

    3c. ∀𝑥: 𝑷(𝑥) ⇒ 𝑷(s(𝑥)) by Gen, 2.
—]

    4. ∀𝑥 𝑷(𝑥) by IR1: 1; 3. — 1, 3, IR1.

    5. 𝑷(𝒛) by K1: 4. — 4, K1.
  ∎


end theory TS1.



