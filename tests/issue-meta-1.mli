
{— level max 100 —}
{— sublevel max 10000 —}
{— unify count max 600000 —}


—input std/SM.mli
—input std/IR.mli


theory TM.  — Test meta.
—  include theory SM.
—  include theory IR.
  formal system.

  rule MP. formula 𝑨, 𝑩. 𝑨, 𝑨 ⇒ 𝑩 ⊢ 𝑩.

  postulate DT. formula sequence 𝜞 formula 𝑨, 𝑩.
    𝜞, 𝑨 ⊢ 𝑩 ⊩ 𝜞 ⊢ 𝑨 ⇒ 𝑩.

  rule IR2. predicate variable 𝑷 object °𝒙 function constant s.
    𝑷(0), 𝑷(𝒙) ⇒ 𝑷(s(𝒙)) ⊢ 𝑷(𝒙).

  end formal system.

{— thread count 0 —}

{— trace result —}
{— trace unspecializable —}
{— trace variable label —}
—{— trace unify —} {— trace empty —} {— trace solve —}
—{— trace substitute —}
—{— trace null —} — variable_substitution::substitute_variable


—{— expand implicit premise —}
{— expand_implicit_premise —}


  corollary A. formula 𝑨, 𝑩, 𝑪.
    𝑨 ⇒ 𝑩, 𝑩 ⇒ 𝑪 ⊢ 𝑨 ⇒ 𝑪
  by
  — DT: MP, premise.
   DT: MP. — DT: MP: MP; premise ⊢₁: premise ⊢₂; premise ⊢₀.



  corollary B. formula 𝑨, 𝑩, 𝑪.
    𝑨 ⇒ 𝑩, 𝑩 ⇒ 𝑪, 𝑨 ⊢ 𝑪
—  by MP: MP; premise ⊢: premise ⊢; premise ⊢.
 by MP.
— by MP. — MP: MP; premise ⊢₁: premise ⊢₂; premise ⊢₀.

  — Induction Rule without premises.
  lemma IR0. predicate variable 𝑷 object °𝒙 function constant s.
    𝑷(0); 𝑷(𝒙) ⊢ 𝑷(s(𝒙)) ⊩ 𝑷(𝒙)
  —by IR2: premise ⊢; DT: premise ⊢: premise ⊢. — IR2, DT.
  by IR2: premise ⊢₀; DT: premise ⊢₁. — IR2, DT.
  —by IR2, DT. — IR2: premise ⊢₀; DT: premise ⊢₁.

end theory.



