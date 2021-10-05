
{— level max 100 —}
{— sublevel max 100 —}
{— unify count max 60000 —}


—input std/IR.mli


theory TG.  — Test Generalization.
—  include theory IR.

{— thread count 0 —}

  formal system.
[—
    rule Gen. formula 𝑨 object °𝒙.
     𝑨 ⊢ ∀𝒙 𝑨.
—]

    rule GenA. formula 𝑨 object °𝒙.
     𝑨 ⊢ ∀𝒙 𝑨.

    axiom I. object °𝒙.
      𝒙 = 𝒙.

    axiom P. object 𝒙, 𝒚.
      𝒙 = 𝒚.

    axiom Q. predicate variable 𝑷 object 𝒕.
      𝑷(𝒕).

  end formal system.

{— trace result —}
{— trace unspecializable —}
{— trace variable label —}
—{— trace null —}
—{— trace unify —}
—{— trace substitute —}
[—
  lemma G. predicate variable 𝑷 object 𝒕.
    𝑷(𝒕) ⊢ ∀𝑥: 𝑷(𝑥)
  by GenA.

  lemma H. predicate variable 𝑷 object °𝑥.
    𝑷(𝑥) ⊢ ∀𝑥: 𝑷(𝑥)
  by GenA.

  lemma J. predicate variable 𝑷 object 𝒕.
    ∀𝑥: 𝑷(𝑥)
  by GenA, Q.


  lemma A. object 𝑥.
    𝑥 = 𝑥
  proof
    by I.
  ∎

  lemma B. object 𝑥, 𝑦.
    𝑥 = 𝑦
  proof
    by I.
  ∎
—]

  lemma C. object °𝑥, °𝑦 function constant s.
    s(𝑥) ≠ 0 ⊢⁽𝑥⁾ s(𝑦) ≠ 0
  proof
    by premise.
  ∎

end theory.



