
{— level max 100 —}
{— sublevel max 100 —}
{— unify count max 60000 —}


—input std/IR.mli


theory TG.  — Test Generalization.
—  include theory IR.

{— thread count 0 —}

  formal system.

    axiom I1. object °𝒙.
      𝒙 = 𝒙.

    axiom I2. object 𝒙.
      𝒙 = 𝒙.

    axiom P1. object °𝒙, °𝒚.
      𝒙 = 𝒚.

    axiom P2. object 𝒙, 𝒚.
      𝒙 = 𝒚.

  end formal system.

—{— trace result —}
{— trace unspecializable —}
{— trace variable label —}
—{— trace null —}
—{— trace unify —}
—{— trace substitute —}

[—
  lemma T1. function s.
    ∀𝑥: s(𝑥) > 0
  proof
    by GenA, Pos.
  ∎
—]

{— trace result —}

  — Using I1, I2:

  lemma A11. object °𝑥. — True.
    𝑥 = 𝑥
  proof
    by I1.
  ∎

  lemma A12. object 𝑥. — False.
    𝑥 = 𝑥
  proof
    by I1.
  ∎

  lemma A21. object °𝑥. — True.
    𝑥 = 𝑥
  proof
    by I2.
  ∎

  lemma A22. object 𝑥. — True.
    𝑥 = 𝑥
  proof
    by I2.
  ∎


  lemma B11. object °𝑥, °𝑦. — False.
    𝑥 = 𝑦
  proof
    by I1.
  ∎

  lemma B12. object 𝑥, 𝑦. — False.
    𝑥 = 𝑦
  proof
    by I1.
  ∎

  lemma B21. object °𝑥, °𝑦. — False.
    𝑥 = 𝑦
  proof
    by I2.
  ∎

  lemma B22. object 𝑥, 𝑦. — False.
    𝑥 = 𝑦
  proof
    by I2.
  ∎


  — Using I1, I2:

  lemma C11. object °𝑥. — True.
    𝑥 = 𝑥
  proof
    by P1.
  ∎

  lemma C12. object 𝑥. — False.
    𝑥 = 𝑥
  proof
    by P1.
  ∎

  lemma C21. object °𝑥. — True.
    𝑥 = 𝑥
  proof
    by P2.
  ∎

  lemma C22. object 𝑥. — True.
    𝑥 = 𝑥
  proof
    by P2.
  ∎


  lemma D11. object °𝑥, °𝑦.
    𝑥 = 𝑦
  proof
    by P1.
  ∎

  lemma D12. object 𝑥, 𝑦.
    𝑥 = 𝑦
  proof
    by P2.
  ∎

  lemma D21. object °𝑥, °𝑦.
    𝑥 = 𝑦
  proof
    by P2.
  ∎

  lemma D22. object 𝑥, 𝑦.
    𝑥 = 𝑦
  proof
    by P2.
  ∎

end theory.



