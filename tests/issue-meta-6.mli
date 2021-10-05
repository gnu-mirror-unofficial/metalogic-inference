
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

  axiom K0. formula 𝑩 object °𝒚 object 𝒕. (∀𝒚 𝑩) ⇒ 𝑩[𝒚 ⤇ 𝒕].

  end formal system.

{— thread count 0 —}

{— trace result —}
{— trace unspecializable —}
{— trace variable label —}
—{— trace unify trace solve trace substitute —}

  {— expand_implicit_premise —}

  lemma K. formula 𝑨 object 𝑡, °𝒙.
    ∀𝒙 𝑨 ⊢ 𝑨[𝒙 ⤇ 𝑡]
  by MP: premise ⊢; K0. — K0, MP.


end theory.



