module
import all KIP126.Def.ProofTools.GeneralizedMahowald.SphereMayActual

@[expose] section
namespace KIP126.ProofTools.Internal.Mahowald
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Core.SpectralSequence KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Standard KIP126.Literature
open KIP126.ProofTools.Internal
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/- The corrected May target uses the inclusion of the infinite normalized
source label. The finite-edge decoder uses finiteNuLabel. They are exactly
the same label; this bridge changes no representative or quotient length. -/
private theorem normalized_included_source_label
    (X Y : ClassicalObject) (g : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (q : ℕ) (s t : ℤ) (x : Ambient model X (s,t)) :
    familyPageMap model.family
      (XModLambdaN.incl ((extensionSourceObject model X Y g).obj model.nu model.auxiliary) q)
      2 (s,t,t+normalizedExponent model.classicalTower g)
      (regradeE2 (by simp) (infiniteSourceForExtension model X Y g s t x)) =
    regradeE2 (by simp)
      (finiteNuLabel model X q (normalizedExponent model.classicalTower g) s t 0 x) := by
  unfold infiniteSourceForExtension finiteNuLabel
  rw [page_regrade]
  have trans {E : SyntheticAdamsSS} {p q r : Tridegree}
      (hpq : p=q) (hqr : q=r) (a : E.E₂ p) :
      regradeE2 hqr (regradeE2 hpq a)=regradeE2 (hpq.trans hqr) a := by
    subst q; subst r; rfl
  rw [trans]
  rfl

private theorem corrected_second_image_finite_label
    (X Y : ClassicalObject) (g : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (q : ℕ) (s t : ℤ) (x : Ambient model X (s,t))
    (D : SyntheticObject)
    (J : XModLambdaN ((extensionSourceObject model X Y g).obj model.nu model.auxiliary) q ⟶
      D.obj model.nu model.auxiliary)
    (u : BiHom (t-s) (t+normalizedExponent model.classicalTower g)
      (D.obj model.nu model.auxiliary))
    (hu : Detects (model.convergence D) (s,t,t+normalizedExponent model.classicalTower g)
      (familyPageMap model.family J 2 (s,t,t+normalizedExponent model.classicalTower g)
        (familyPageMap model.family
          (XModLambdaN.incl ((extensionSourceObject model X Y g).obj model.nu model.auxiliary) q)
          2 (s,t,t+normalizedExponent model.classicalTower g)
          (regradeE2 (by simp) (infiniteSourceForExtension model X Y g s t x)))) u) :
    Detects (model.convergence D) (s,t,t+normalizedExponent model.classicalTower g)
      (familyPageMap model.family J 2 (s,t,t+normalizedExponent model.classicalTower g)
        (regradeE2 (by simp)
          (finiteNuLabel model X q (normalizedExponent model.classicalTower g) s t 0 x))) u := by
  rw [normalized_included_source_label] at hu
  exact hu

private theorem finite_edge_detection_source_length
    (X Y : ClassicalObject) (g : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (j q : ℕ) (hj : j=q) (s t : ℤ) (x : Ambient model X (s,t))
    (D : SyntheticObject)
    (J : XModLambdaN ((extensionSourceObject model X Y g).obj model.nu model.auxiliary) j ⟶
      D.obj model.nu model.auxiliary)
    (u : BiHom (t-s) (t+normalizedExponent model.classicalTower g)
      (D.obj model.nu model.auxiliary))
    (hu : Detects (model.convergence D) (s,t,t+normalizedExponent model.classicalTower g)
      (familyPageMap model.family (by simpa only [hj,extensionSourceObject,SyntheticObject.obj] using J) 2
        (s,t,t+normalizedExponent model.classicalTower g)
        (regradeE2 (by simp)
          (finiteNuLabel model X q (normalizedExponent model.classicalTower g) s t 0 x))) u) :
    Detects (model.convergence D) (s,t,t+normalizedExponent model.classicalTower g)
      (familyPageMap model.family J 2 (s,t,t+normalizedExponent model.classicalTower g)
        (regradeE2 (by simp)
          (finiteNuLabel model X j (normalizedExponent model.classicalTower g) s t 0 x))) u := by
  subst j
  exact hu

private theorem finite_native_bottom_detection_reindex_exists
    (X : ClassicalObject) (q j : ℕ) (hj : q=j) (e s t : ℤ)
    (x : Ambient model X (s,t))
    (a : BiHom (t-s) (t+e)
      ((SyntheticObject.quotient q (.shift (0,e) (.nu X))).obj model.nu model.auxiliary))
    (ha : Detects (model.convergence (.quotient q (.shift (0,e) (.nu X)))) (s,t,t+e)
      (regradeE2 (by simp) (finiteNuLabel model X q e s t 0 x)) a) :
    ∃ a' : BiHom (t-s) (t+e)
        ((SyntheticObject.quotient j (.shift (0,e) (.nu X))).obj model.nu model.auxiliary),
      Detects (model.convergence (.quotient j (.shift (0,e) (.nu X)))) (s,t,t+e)
        (regradeE2 (by simp) (finiteNuLabel model X j e s t 0 x)) a' := by
  subst j
  exact ⟨a,ha⟩

end
end KIP126.ProofTools.Internal.Mahowald
