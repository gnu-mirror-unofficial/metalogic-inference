
{— level max 100 —}
{— sublevel max 10000 —}
{— unify count max 600000 —}


—input std/SM.mli
—input std/IR.mli


theory TM.  — Test meta.
—  include theory SM.
—  include theory IR.
  formal system.

  
  axiom S6. object 𝑥, 𝑦 function constant s. 𝑥 + s(𝑦) = s(𝑥 + 𝑦).
  rule S2a. object 𝑥, 𝑦 function constant s. 𝑥 = 𝑦 ⊢ s(𝑥) = s(𝑦).

  axiom S7. object 𝑥. 𝑥 ⋅ 0 = 0.

  axiom S8. object 𝑥, 𝑦 function constant s. 𝑥 ⋅ s(𝑦) = 𝑥 ⋅ 𝑦 + 𝑥.

  definition n1. function constant s. 1 ≔ s(0).

  rule T1B. object 𝒙, 𝒚.
    𝒙 = 𝒚 ⊢ 𝒚 = 𝒙.

  rule T1C. object 𝒙, 𝒚, 𝒛.
    𝒙 = 𝒚, 𝒚 = 𝒛 ⊢ 𝒙 = 𝒛.

  rule T1D. object 𝒙, 𝒚, 𝒛.
    𝒙 = 𝒛, 𝒚 = 𝒛 ⊢ 𝒙 = 𝒚.

  rule T1E. object 𝒓, 𝒔, 𝒕.
  𝒕 = 𝒓 ⊢ 𝒕 + 𝒔 = 𝒓 + 𝒔.

  axiom T1f. object 𝒕.
    𝒕 = 0 + 𝒕.

  end formal system.

{— thread count 0 —}

{— trace result —}
{— trace unspecializable —}
{— trace variable label —}
—{— trace unify —}

  — Comparing forward and reverse order goal concatenation of
  — alternative operator*(const alternative& x, const alternative& y)
  lemma T3b. object 𝒕.
    𝒕⋅1 = 𝒕
   —by T1C: T1C; T1B: T1f; S8, n1; T1E: S7. — Original reversed order
   by T1C: T1C; T1B: S8, n1; T1E; T1f: S7. — Forward order
   —by T1C: T1C; T1B: S8; T1E, n1; T1f: S7. — Forward order with definiton in reverse order.

   —by T1C: T1C; T1B: S8, n1; T1E, T1f: S7. — Sublevel set written in forward order

   —by T1C: T1C; T1B: S8, S7, T1E, T1f, n1. — T1C: T1C; T1B: T1f; S8, n1; T1E: S7.
   —by S8, S7, T1E, T1C, T1B, T1f, n1. — T1C: T1C; T1B: T1f; S8, n1; T1E: S7.


end theory.



