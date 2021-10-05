
{— level max 100 —}
{— sublevel max 10000 —}
{— unify count max 600000 —}


—input std/SM.mli
—input std/IR.mli


theory TM.  — Test meta.
—  include theory SM.
—  include theory IR.
  formal system.

  postulate DT. formula 𝑨, 𝑩.
    𝑨 ⊢ 𝑩 ⊩ 𝑨 ⇒ 𝑩.

  rule IR2. predicate variable 𝑷 object °𝒙 function constant s.
    𝑷(0), 𝑷(𝒙) ⇒ 𝑷(s(𝒙)) ⊢ 𝑷(𝒙).

  end formal system.

{— thread count 0 —}

{— trace result —}
{— trace unspecializable —}
{— trace variable label —}
—{— trace proof —}
—{— trace unify —} {— trace solve —}


{— expand_implicit_premise —}

  — Induction Rule
  lemma IR. predicate variable 𝑷 object °𝒙 function constant s.
    𝑷(0); 𝑷(𝒙) ⊢ 𝑷(s(𝒙)) ⊩ 𝑷(𝒙)
  —by IR2: premise ⊢; DT: premise ⊢: premise ⊢. — IR2, DT.
  —by IR2, DT. — IR2: premise ⊢; DT: premise ⊢.
  —by IR2: premise ⊢; DT: premise ⊢: premise ⊢.
  —by IR2: premise ⊢; DT: premise ⊢.
  by IR2: premise ⊢₀; DT: premise ⊢₁.

end theory.



