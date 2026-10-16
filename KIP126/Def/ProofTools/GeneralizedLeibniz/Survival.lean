module
import all KIP126.Def.ProofTools.GeneralizedLeibniz.Boundary

/-! The survival implication in the absolute-boundary comparison of AimPaper
Proposition `prop:6de7d130`. A high-filtration absolute boundary is divisible
by the exact λ power that vanishes in the complementary quotient. Exactness
then lifts the specified source through the higher quotient; the fixed BHS
finite-lift criterion identifies its original classical label as a cycle. -/

@[expose] section
namespace KIP126.ProofTools.Internal.Leibniz
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.Classical.Adams KIP126.AdamsSynthetic KIP126.Core.SpectralSequence
open KIP126.Kervaire.Route KIP126.Literature KIP126.AdamsSynthetic.Standard
open KIP126.ProofTools.Internal.Mahowald
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000

private theorem lambdaMultiply_quotient_zero (A : SyntheticSpectrum)
    (n : ℕ) (m w : ℤ) (a : BiHom m w A) :
    lambdaMultiply n a ≫ XModLambdaN.incl A n = 0 := by
  have hz : lambdaPow n (Smn m w) ≫ a ≫ XModLambdaN.incl A n = 0 := by
    rw [←Category.assoc]
    erw [←lambdaPow_naturality n a]
    rw [Category.assoc,XModLambdaN.lambdaPow_comp_incl,comp_zero]
  simp only [lambdaMultiply,Category.assoc,hz,comp_zero]

private theorem absolute_boundary_filtration_lift (X : ClassicalObject)
    (i j : ℕ) (hi : 0 < i) (hij : i < j) (s t : ℤ)
    (a : BiHom (t-s) t (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) i))
    (hfil : FiltrationAtLeast model.syntheticTower (s+j+1)
      (biSuspensionHomEquiv (t-s) t i (model.nu.functor.obj (X.obj model.auxiliary))
        (a ≫ XModLambdaN.proj _ i))) :
    ∃ b : BiHom (t-s) t (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) j),
      b ≫ (model.quotients.tower _).rho i j hij.le = a := by
  let A := model.nu.functor.obj (X.obj model.auxiliary)
  let α := biSuspensionHomEquiv (t-s) t i A (a ≫ XModLambdaN.proj A i)
  obtain ⟨β,hβ⟩ := (KIP126.Literature.Standard.selected_filtration_lambda X
    (t-s-1) (t+i) (s+j+1) (by omega) α).mp hfil
  have hexp : ((t-s-1)+(s+j+1)-(t+i)).toNat = j-i := by omega
  have hzero : α ≫ XModLambdaN.incl A (j-i) = 0 := by
    rw [←hβ]
    have hz (n q : ℕ) (hn : n = q) : lambdaMultiply n β ≫ XModLambdaN.incl A q = 0 := by
      subst q
      exact lambdaMultiply_quotient_zero A n _ _ β
    simp only [regrade_precomp,Category.assoc,hz _ _ hexp,comp_zero]
  let T := (model.quotients.tower A).triangle hi hij
  have hz : a ≫ T.delta = 0 := by
    apply (biSuspensionHomEquiv (t-s) t i (XModLambdaN A (j-i))).injective
    rw [map_zero,cofiber_boundary_projection]
    exact hzero
  obtain ⟨b,hb⟩ := (Triangle.mk T.lambdaMap T.rho T.delta).coyoneda_exact₃ T.distinguished a hz
  refine ⟨b,?_⟩
  simpa only [T,Triangle.mk,(model.quotients.tower A).triangle_rho hi hij] using hb.symm

private theorem first_label_lift_cycles (X : ClassicalObject)
    (j : ℕ) (hj : 0 < j) (s t : ℤ) (x : Ambient model X (s,t))
    (a : BiHom (t-s) t (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) j))
    (ha : a ≫ (model.quotients.tower _).rho 1 j hj =
      firstLabel model X s t x ≫ XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1) :
    x ∈ cycles model X j (s,t) := by
  let A := model.nu.functor.obj (X.obj model.auxiliary)
  let inv : A ⟶ nuZero model X := SyntheticCategory.biShift_zero.inv.app A
  have hfirst : (a ≫ XModLambdaN.map inv j) ≫ (model.quotients.tower _).rho 1 j hj =
      firstLabel model X s t x := by
    rw [Category.assoc,←(model.quotients.natural inv).rho_naturality hj,←Category.assoc,ha,
      Category.assoc,←model.quotients.functoriality.map_comp]
    simp only [inv,A,Iso.hom_inv_id_app,model.quotients.functoriality.map_id,Category.comp_id]
  have hx := (KIP126.Literature.Standard.bhs_finite_lift X j hj s t x).mpr
    ⟨a ≫ XModLambdaN.map inv j,hfirst⟩
  have hc := ((isCycle_iff_reaches model X (j+1) (by omega) (s,t) x).mpr hx).2
  simpa only [add_sub_cancel_right] using hc

private theorem absolute_boundary_filtration_cycles (X : ClassicalObject)
    (i j : ℕ) (hi : 0 < i) (hij : i ≤ j) (s t : ℤ) (x : Ambient model X (s,t))
    (a : BiHom (t-s) t (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) i))
    (ha : a ≫ (model.quotients.tower _).rho 1 i hi =
      firstLabel model X s t x ≫ XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1)
    (hfil : FiltrationAtLeast model.syntheticTower (s+j+1)
      (biSuspensionHomEquiv (t-s) t i (model.nu.functor.obj (X.obj model.auxiliary))
        (a ≫ XModLambdaN.proj _ i))) :
    x ∈ cycles model X j (s,t) := by
  rcases hij.eq_or_lt with rfl | hij
  · exact first_label_lift_cycles X i hi s t x a ha
  obtain ⟨b,hb⟩ := absolute_boundary_filtration_lift X i j hi hij s t a hfil
  apply first_label_lift_cycles X j (by omega) s t x b
  rw [←(model.quotients.tower _).rho_comp hi hij.le,←Category.assoc,hb]
  exact ha

end
end KIP126.ProofTools.Internal.Leibniz
