module

public import KIP126.Def.Synthetic.ExtensionSS.Proofs

@[expose] public section

/-! Index transport from an ESS target to the underlying filtered complex.
Keeping this operation generic avoids unfolding a concrete convergence family
while Lean checks the associated-graded target. -/

namespace KIP126.Synthetic.SpectralSequence.SyntheticExtensionData
open CategoryTheory KIP126.Synthetic.Context
universe u v
variable {Syn : Type u} [SyntheticCategory.{u, v} Syn]
  {F : SyntheticAdamsFamily Syn} {X Y : Syn} {g : X ⟶ Y}

/-- Transport a target label along the actual ESS differential index. -/
noncomputable def targetClass (D : SyntheticExtensionData F g)
    (degree : ℤ × ℤ) (n s : ℤ) {T : ModuleCat.{v} ℤ}
    (y : T ⟶ ((D.ess degree).ssData ((s, 1) + (D.ess degree).diffDeg n)).V) :
    T ⟶ (D.complex degree).assocGraded (s + n) 0 := by
  change T ⟶ ((D.ess degree).ssData (s + n, 0)).V
  exact y ≫ eqToHom (congrArg (fun p => ((D.ess degree).ssData p).V)
    (D.target_index degree n s))

end KIP126.Synthetic.SpectralSequence.SyntheticExtensionData
