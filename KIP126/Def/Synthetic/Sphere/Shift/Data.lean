module

public import KIP126.Def.Synthetic.Sphere.Shift.UnderlyingEquivalence.Proofs

@[expose] public section

/-! Additive bigraded suspension equivalences, with the existing underlying
Hom maps and separately stated additivity properties. -/

namespace KIP126.Synthetic.Context

open CategoryTheory

universe u v

variable {Syn : Type u} [SyntheticCategory.{u, v} Syn]

/-- Additive enhancement of the existing `susp_invariance`, with exactly
the same underlying equivalence. -/
noncomputable def suspInvarianceAddEquiv (m n k l : ℤ) (X : Syn) :
    BiHom m n X ≃+
      BiHom (m + k) (n + l) ((SyntheticCategory.biShift (k, l)).obj X) where
  toEquiv := susp_invariance m n k l X
  map_add' := susp_invariance_add m n k l X

/-- The additive reindexing of an ordinary suspension of a vertical shift:
`[S^(n,w), Σ Σ^(0,-q) Q] ≃+ [S^(n-1,w+q), Q]`. -/
noncomputable def biSuspensionHomEquiv (n w q : ℤ) (Q : Syn) :
    BiHom n w (((SyntheticCategory.biShift (0, -q)).obj Q)⟦(1 : ℤ)⟧) ≃+
      BiHom (n - 1) (w + q) Q where
  toEquiv := biSuspensionHomUnderlyingEquiv n w q Q
  map_add' := biSuspensionHomUnderlyingEquiv_add n w q Q

end KIP126.Synthetic.Context
