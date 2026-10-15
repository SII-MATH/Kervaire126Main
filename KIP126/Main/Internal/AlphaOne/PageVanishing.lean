module
public import KIP126.Main.Conditions

/-! Generic page-vanishing transport used by the original AlphaOne proof.
Source: bbac1fc05843, Def/ClassicalAdams/TowerVanishing/Proofs.lean (MIT). -/
@[expose] section
namespace KIP126.Main.Internal.AlphaOne
open CategoryTheory CategoryTheory.Limits KIP126.Core.SpectralSequence
noncomputable section
universe v
set_option backward.isDefEq.respectTransparency false

private theorem page_subsingleton_of_le
    (E : KIP126.Core.SpectralSequence (ModuleCat.{v} ℤ) (ℤ×ℤ))
    (r t : ℤ) (p : ℤ×ℤ) (_hr : E.r₀ ≤ r) (hrt : r≤t)
    (hzero : Subsingleton (E.Page r p)) : Subsingleton (E.Page t p) := by
  let A := E.ssData p
  let n : WithTop ℕ := ↑(r-E.r₀).toNat
  let m : WithTop ℕ := ↑(t-E.r₀).toNat
  have hnm : n≤m := by
    dsimp only [n,m]
    exact_mod_cast Int.toNat_le_toNat (by omega : r-E.r₀≤t-E.r₀)
  have hz (z : (Subobject.underlying.obj (A.Z m) : ModuleCat ℤ)) : A.pageπ m z=0 := by
    let i := Subobject.ofLE (A.Z m) (A.Z n) (A.Z_anti hnm)
    have hzn : A.pageπ n (i z)=0 := hzero.elim _ _
    have hb := (subobject_cokernel_π_eq_zero_iff (A.B n) (A.Z n) (A.B_le_Z n) (i z)).mp hzn
    change (i ≫ (A.Z n).arrow) z ∈ _ at hb
    simp only [i,Subobject.ofLE_arrow] at hb
    apply (subobject_cokernel_π_eq_zero_iff (A.B m) (A.Z m) (A.B_le_Z m) z).mpr
    exact (ModuleCat.subobjectModule A.V).monotone (A.B_mono hnm) hb
  haveI : Epi (A.pageπ m) := inferInstanceAs (Epi (cokernel.π _))
  have hall (x : E.Page t p) : x=0 := by
    obtain ⟨z,rfl⟩ := (ModuleCat.epi_iff_surjective (A.pageπ m)).mp inferInstance x
    exact hz z
  exact ⟨fun x y => (hall x).trans (hall y).symm⟩

end
end KIP126.Main.Internal.AlphaOne
end
