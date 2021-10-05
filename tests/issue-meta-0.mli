
{— level max 100 —}
{— sublevel max 10000 —}
{— unify count max 600000 —}


—input std/SM.mli
—input std/IR.mli


theory TM.  — Test meta.
—  include theory SM.
—  include theory IR.
  formal system.

  postulate PCa. formula 𝑨, 𝑩, 𝑪.
    𝑨 ⊢ 𝑪; 𝑩 ⊢ 𝑪 ⊩ 𝑨 ∨ 𝑩 ⊢ 𝑪.

  rule 2. object 𝒙 function constant s.
    𝒙 = 0 ⊢ ∃𝑤: s(𝒙) = s(𝑤).

  rule a. object 𝒙 function constant s.
    𝒙 ≠ 0 ⊢ ∃𝑤: s(𝒙) = s(𝑤).

  end formal system.

{— thread count 0 —}

{— trace result —}
{— trace unspecializable —}
{— trace variable label —}
—{— trace unify —}


  lemma b. object 𝒙 function constant s.
    𝒙 = 0 ∨ 𝒙 ≠ 0 ⊢ ∃𝑤: s(𝒙) = s(𝑤)
  proof
    by PCa: 2, a. — PCa: 2; a.
  ∎


end theory.



