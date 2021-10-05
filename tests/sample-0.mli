
{— level max 100 —}
{— sublevel max 100 —}
{— unify count max 600000 —}

—input test-LI.mli
—input std/IR.mli


theory Smp. — Sample.
—  include theory IR.

  formal system.

  rule MP. formula 𝑨, 𝑩. 𝑨, 𝑨 ⇒ 𝑩 ⊢ 𝑩.

  rule CE1. formula 𝑨, 𝑩. 𝑨 ∧ 𝑩 ⊢ 𝑨.
  rule CE2. formula 𝑨, 𝑩. 𝑨 ∧ 𝑩 ⊢ 𝑩.

  rule DI1. formula 𝑨, 𝑩. 𝑨 ⊢ 𝑨 ∨ 𝑩.
  rule DI2. formula 𝑨, 𝑩. 𝑩 ⊢ 𝑨 ∨ 𝑩.

  rule DS1. formula 𝑨, 𝑩. 𝑨 ∨ 𝑩, ¬𝑨 ⊢ 𝑩.

  end formal system.


{— trace result —}

{— thread count 0 —}


  lemma “S1a”. formula 𝑨, 𝑩, 𝑪, 𝑫, 𝑬, 𝑭.
    (𝑨 ∨ 𝑩) ∧ ¬𝑪, ¬𝑪 ⇒ (𝑫 ∧ ¬𝑨), 𝑩 ⇒ (𝑨 ∨ 𝑬) ⊢ 𝑬 ∨ 𝑭
  proof
    by DI1: DS1: MP; CE2: DS1; MP: CE1; CE2; CE2: MP: CE2. —0.28s
  ∎

end theory Smp.

