
{— level max 100 —}
{— sublevel max 10000 —}
{— unify count max 600000 —}


—input std/SM.mli
—input std/IR.mli


theory TM.  — Test meta.
—  include theory SM.
—  include theory IR.
  formal system.


  definition NE. object 𝑥, 𝑦.
    𝑥 ≠ 𝑦 ≔ ¬𝑥 = 𝑦.

  axiom T1a. object 𝒙.
    𝒙 = 𝒙.

  rule T1D. object 𝒙, 𝒚, 𝒛.
    𝒙 = 𝒛, 𝒚 = 𝒛 ⊢ 𝒙 = 𝒚.

  postulate RAa. formula 𝑨, 𝑩.
    𝑨 ⊢ 𝑩; 𝑨 ⊢ ¬𝑩 ⊩ ¬𝑨.

  end formal system.

{— thread count 0 —}

{— trace result —}
{— trace unspecializable —}
{— trace variable label —}
—{— trace unify trace solve trace substitute —}
—{— trace solve —}

  lemma EqTrN. object 𝒙, 𝒚, 𝒛.
    𝒙 = 𝒚, 𝒚 ≠ 𝒛 ⊢ 𝒙 ≠ 𝒛
  proof
    — Proof by contradiction: Assume 𝒙 = 𝒛, and show that both
    — ¬𝒚 = 𝒛 and 𝒚 = 𝒛 hold. Then ¬𝒙 = 𝒛 must hold.
    0. 𝒙 = 𝒚 by premise.
[—
    1. ¬𝒚 = 𝒛 by premise, NE.
    2. 𝒙 = 𝒛 ⊢ ¬𝒚 = 𝒛 by 1.

    3. 𝒙 = 𝒛 ⊢ 𝒚 = 𝒛 by 0, T1a, T1D.       — T1D: T1D; T1D: T1a; premise ⊢; T1a; 0.
    3a. 𝒙 = 𝒛 ⊢ 𝒚 = 𝒛 by T1D: 0, T1a, T1D. — T1D: T1D; T1D: T1a; premise ⊢; T1a; 0.
—]
—    3b. 𝒙 = 𝒛 ⊢ 𝒚 = 𝒛 by T1D: T1D; T1D: T1a. [—unproved—]
—    3b0. 𝒙 = 𝒛 ⊢ 𝒚 = 𝒛 by T1D: T1D; T1D: T1a, premise EqTrN. — T1D: T1D; T1D: T1a; premise EqTrN; T1a; premise ⊢.

    3e0. 𝒙 = 𝒛 ⊢ 𝒚 = 𝒛 by T1D: T1D; T1D: T1a; 0; T1a.
    3e1. 𝒙 = 𝒛 ⊢ 𝒚 = 𝒛 by T1D: T1D; T1D: T1a; premise EqTrN₀; T1a.

    3e2. 𝒙 = 𝒛 ⊢ 𝒚 = 𝒛
    — Does not recognize 'premise 3e2'; requires an explicit 'proof … ∎' statement.
    —  by T1D: T1D; T1D: T1a; 0; T1a; premise 3e2. — T1D: T1D; T1D: T1a; 0; T1a; premise ⊢.
    proof
      by T1D: T1D; T1D: T1a; 0; T1a.
    ∎

    3e3. 𝒙 = 𝒛 ⊢ 𝒚 = 𝒛
    — Does not recognize 'premise 3e3'; requires an explicit 'proof … ∎' statement, as in 3e2.
    —  by T1D: T1D; T1D: T1a; premise EqTrN; T1a; premise 3e3. — T1D: T1D; T1D: T1a; 0; T1a; premise ⊢.
    proof
      by T1D: T1D; T1D: T1a; premise EqTrN₀; T1a.
    ∎



—     3e3. 𝒙 = 𝒛 ⊢ 𝒚 = 𝒛 by T1D: T1D; T1D: T1a; 0; T1a; premise 3e3. — T1D: T1D; T1D: T1a; 0; T1a; premise ⊢.

[—
    3b1. 𝒙 = 𝒛 ⊢ 𝒚 = 𝒛 by T1D: T1D; T1D: 0, T1a. — T1D: T1D; T1D: T1a; premise ⊢; T1a; 0.
    3b2. 𝒙 = 𝒛 ⊢ 𝒚 = 𝒛 by T1D: T1D; T1D: T1a, premise ⊢. [—unproved—]
    3b3. 𝒙 = 𝒛 ⊢ 𝒚 = 𝒛 by T1D: T1D; T1D: T1a, premise EqTrN. — T1D: T1D; T1D: T1a; premise ⊢; T1a; premise EqTrN.

    3c0. 𝒙 = 𝒛 ⊢ 𝒚 = 𝒛 by T1D: T1D; T1D: T1a; 0; T1a; 0.
    3c1. 𝒙 = 𝒛 ⊢ 𝒚 = 𝒛 by T1D: T1D; T1D: T1a; 0; T1a; premise ⊢. [—unproved—]
    3c2. 𝒙 = 𝒛 ⊢ 𝒚 = 𝒛 by T1D: T1D; T1D: T1a; premise ⊢; T1a; 0. — T1D: T1D; T1D: T1a; premise ⊢; T1a; 0.
    3c3. 𝒙 = 𝒛 ⊢ 𝒚 = 𝒛 by T1D: T1D; T1D: T1a; premise ⊢; T1a; premise ⊢. [—unproved—]

    3d0. 𝒙 = 𝒛 ⊢ 𝒚 = 𝒛 by T1D: T1D; T1D: T1a; 0; T1a; 0. — T1D: T1D; T1D: T1a; premise ⊢; T1a; 0.
    3d1. 𝒙 = 𝒛 ⊢ 𝒚 = 𝒛 by T1D: T1D; T1D: T1a; 0; T1a; premise EqTrN. — T1D: T1D; T1D: T1a; premise ⊢; T1a; premise EqTrN.
    3d2. 𝒙 = 𝒛 ⊢ 𝒚 = 𝒛 by T1D: T1D; T1D: T1a; premise EqTrN; T1a; 0. — T1D: T1D; T1D: T1a; premise ⊢; T1a; 0.
    3d3. 𝒙 = 𝒛 ⊢ 𝒚 = 𝒛 by T1D: T1D; T1D: T1a; premise EqTrN; T1a; premise EqTrN. — T1D: T1D; T1D: T1a; premise ⊢; T1a; premise EqTrN.
—]

[—
    3m. 𝒙 = 𝒛 ⊢ 𝒚 = 𝒛 by T1D: T1D; T1D: T1a; premise ⊢; T1a; 0.
    3n. 𝒙 = 𝒛 ⊢ 𝒚 = 𝒛 by T1D: T1D; T1D: T1a; 0; T1a; premise ⊢.
    3l. 𝒙 = 𝒛 ⊢ 𝒚 = 𝒛 by T1D: T1D; T1D: T1a.
    3a. 𝒙 = 𝒛 ⊢ 𝒚 = 𝒛 by T1D: T1D; T1D: T1a; T1a; 0.
    3b. 𝒙 = 𝒛 ⊢ 𝒚 = 𝒛 by T1D: T1D; T1D: T1a; T1a; premise ⊢.
    3d. 𝒙 = 𝒛 ⊢ 𝒚 = 𝒛 by T1D: T1D; T1D: 0; T1a; 0; T1a.
    3e. 𝒙 = 𝒛 ⊢ 𝒚 = 𝒛 by T1D: T1D; T1D: T1a; premise ⊢; T1a; premise ⊢.
    3f. 𝒙 = 𝒛 ⊢ 𝒚 = 𝒛 by T1D: T1D; T1D: premise ⊢; T1a; premise ⊢; T1a.
    3g. 𝒙 = 𝒛 ⊢ 𝒚 = 𝒛 by T1D: T1D; T1D: T1a, premise ⊢.
    3ga. 𝒙 = 𝒛 ⊢ 𝒚 = 𝒛 by T1D: T1D; T1D: T1a, 0.
—]
    — by T1D: T1D; T1D: T1a; T1a; premise ⊢. — Forward order
    — by T1D: T1D; T1D: T1a; T1a; 0. — Reverse order.
                       — T1D: T1D; T1D: T1a; premise ⊢; T1a; 0. — 0, T1a, T1D.
—  4. ¬𝒙 = 𝒛 by RAa: 3; 2: premise ⊢; premise ⊢. — 2, 3, RAa.
               — RAa: 3; 2: premise ⊢; premise ⊢. — 2, 3, RAa.
—    by 4, NE.
  ∎


end theory.



