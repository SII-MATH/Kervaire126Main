module
public import KIP126.ProofTools.Laws
import all KIP126.ProofTools.GeneralizedMahowald.Coherence
import all KIP126.ProofTools.GeneralizedMahowald.Filtration
import all KIP126.ProofTools.DetectionOperations
import all KIP126.ProofTools.StretchingRepresentatives

/-! Boundary annihilation in the finite λ triangle. The argument adapts
GeneralizedMahowald/Proofs.lean:705–766,856–966 at bbac1fc05843 (MIT).
The window presentation and shift naturality are the fixed upstream interfaces. -/
@[expose] section
namespace KIP126.ProofTools.Internal.Mahowald
open CategoryTheory CategoryTheory.Limits
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Core.SpectralSequence KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Standard KIP126.Literature
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

theorem quotient_map_class_eq_zero {R : Type*} [Ring R] {V : Type*}
    [AddCommGroup V] [Module R V] {Z Z' B B' : Submodule R V}
    (hZ : Z ≤ Z') (hB : B ≤ B') (y : Z) (hy : y.val ∈ B') :
    subquotientMap hZ hB (subquotientClass Z B y) = 0 := by
  exact (Submodule.Quotient.mk_eq_zero _).mpr hy

public theorem finite_target_label_iff (X : ClassicalObject) (q : ℕ) (hq : 0 < q)
    (s t : ℤ) (k : ℕ) (hk : k < q)
    (y : cycles model X ((q:ℤ)-t+(t-k)) (s,t))
    (e : ((model.family.quotient (model.nu.functor.obj (X.obj model.auxiliary)) q).sequence.ssData
      (s,t,t-k)).eInfty) :
    HasInfinityRepresentative _ 2 (s,t,t-k) (finiteTargetLabel model X q s t k y.val) e ↔
      KIP126.Literature.Standard.infinityFiniteWindow X q hq (s,t) (t-k) (by omega) e =
        subquotientClass (cycles model X ((q:ℤ)-t+(t-k)) (s,t))
          (boundaries model X (1+t-(t-k)) (s,t)) y := by
  have hlabel : nuWeightLabel model X s t (t-k) (by omega) y.val =
      targetNuLabel model X s t k y.val := by
    have hk' : (t-(t-k)).toNat = k := by omega
    have transport (a b : ℕ) (hab : a=b)
        (h : (s,t,t-a)=(s,t,t-b)) :
        regradeE2 h (targetNuLabel model X s t a y.val) = targetNuLabel model X s t b y.val := by
      subst b
      rfl
    exact transport _ k hk' _
  have h := KIP126.Literature.Standard.eInfinity_finite_labels X q hq s t (t-k)
    (by omega) y.val e
  rw [hlabel] at h
  change HasInfinityRepresentative _ 2 (s,t,t-k) (finiteTargetLabel model X q s t k y.val) e ↔ _ at h
  exact h.trans ⟨fun ⟨_,he⟩ => he, fun he => ⟨y.property,he⟩⟩

theorem detected_map_zero_above_shifted_finite_top
    (A : SyntheticObject) (X : ClassicalObject) (r : ℕ) (hr : 0 < r)
    (i s t w : ℤ) (htop : (r:ℤ) ≤ t+1-(w-i))
    (h : A.obj model.nu model.auxiliary ⟶ (SyntheticCategory.biShift (0,i)).obj
      (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) r))
    (x : (model.family.obj (A.obj model.nu model.auxiliary)).E₂ (s,t,w))
    (a : BiHom (t-s) w (A.obj model.nu model.auxiliary))
    (ha : Detects (model.convergence A) (s,t,w) x a)
    (e : ((model.family.obj (A.obj model.nu model.auxiliary)).sequence.ssData (s,t,w)).eInfty)
    (he : HasInfinityRepresentative _ 2 (s,t,w) x e)
    (hzero : (model.family.map h).eInftyMap (s,t,w) e = 0) : a ≫ h = 0 := by
  let B : SyntheticObject := .shift (0,i) (.quotient r (.nu X))
  have hm := detects_map A B h (s,t,w) x a ha
  have hz := family_infinity_representative_map h (s,t,w) x e he
  rw [hzero] at hz
  have hf := detects_zero_infinity_filtration (model.convergence B) (s,t,w) hm hz
  exact shifted_finite_high_filtration_zero X r hr i (t-s) w (s+1) (by omega) (a ≫ h) hf

theorem weight_shift_lower_kernel_via_transpose
    (A B Y : SyntheticObject) (i : ℕ) (p : ℤ×ℤ) (w : ℤ)
    (h : A.obj model.nu model.auxiliary ⟶ B.obj model.nu model.auxiliary)
    (ε : (SyntheticCategory.biShift (0,-(i:ℤ))).obj (B.obj model.nu model.auxiliary) ≅
      Y.obj model.nu model.auxiliary)
    (g : (SyntheticCategory.biShift (0,-(i:ℤ))).obj (A.obj model.nu model.auxiliary) ⟶
      Y.obj model.nu model.auxiliary)
    (hg : (SyntheticCategory.biShift (0,-(i:ℤ))).map h ≫ ε.hom = g)
    (e : ((model.family.obj (A.obj model.nu model.auxiliary)).sequence.ssData (p.1,p.2,w)).eInfty) :
    (model.family.map g).eInftyMap (p.1,p.2,w-i)
      ((infinityShift model KIP126.Literature.Standard.infinityShift_comparison A i p w).hom e) = 0 ↔
      (model.family.map h).eInftyMap (p.1,p.2,w) e = 0 := by
  let V (j : Tridegree) : SyntheticSpectrum ⥤ ModuleCat ℤ := model.family.functor ⋙
    { obj := fun E => (E.ssData j).eInfty
      map := fun f => f.eInftyMap j
      map_id := fun E => SpectralSequenceMorphism.eInftyMap_id E j
      map_comp := fun f g => SpectralSequenceMorphism.eInftyMap_comp f g j }
  have hs := ConcreteCategory.congr_hom
    (KIP126.Literature.Standard.infinityShift_natural A B h i p w) e
  simp only [ModuleCat.comp_apply] at hs
  have hz : (model.family.map ((SyntheticCategory.biShift (0,-(i:ℤ))).map h)).eInftyMap
      (p.1,p.2,w-i) ((infinityShift model KIP126.Literature.Standard.infinityShift_comparison A i p w).hom e) = 0 ↔
      (model.family.map h).eInftyMap (p.1,p.2,w) e = 0 := by
    exact (congrArg (fun z => z = 0) hs.symm).to_iff.trans
      ((infinityShift model KIP126.Literature.Standard.infinityShift_comparison B i p w).toLinearEquiv.map_eq_zero_iff)
  change (V (p.1,p.2,w-i)).map g
    ((infinityShift model KIP126.Literature.Standard.infinityShift_comparison A i p w).hom e) = 0 ↔ _
  rw [←hg,Functor.map_comp,ModuleCat.comp_apply]
  exact (((V (p.1,p.2,w-i)).mapIso ε).toLinearEquiv.map_eq_zero_iff).trans hz

theorem finite_target_boundary_lambda_zero (X : ClassicalObject)
    (r i : ℕ) (hi : 0 < i) (hir : i < r) (s t : ℤ)
    (y : cycles model X ((r-i:ℕ)-t+(t-(r-i-1:ℕ))) (s,t))
    (hy : y.val ∈ boundaries model X r (s,t))
    (b : BiHom (t-s) (t-(r-i-1:ℕ))
      (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) (r-i)))
    (hb : Detects (model.convergence (.quotient (r-i) (.nu X)))
      (s,t,t-(r-i-1:ℕ)) (finiteTargetLabel model X (r-i) s t (r-i-1) y.val) b) :
    (SyntheticCategory.biShift (0,-(i:ℤ))).map b ≫
      ((model.quotients.tower (model.nu.functor.obj (X.obj model.auxiliary))).triangle hi hir).lambdaMap = 0 := by
  let Q := XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) (r-i)
  let Y := XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) r
  let T := (model.quotients.tower (model.nu.functor.obj (X.obj model.auxiliary))).triangle hi hir
  obtain ⟨e,he,ha⟩ := hb
  have hwin : 0 ≤ t-(t-(r-i-1:ℕ)) ∧ t-(t-(r-i-1:ℕ)) < (r-i:ℕ) := by omega
  have hlabel := (finite_target_label_iff X (r-i) (by omega) s t (r-i-1) (by omega) y e).mp he
  have hk := KIP126.Literature.Standard.eInfinity_lambda_finite X r i hir (s,t)
    (t-(r-i-1:ℕ)) hwin e
  rw [hlabel] at hk
  have hk0 : KIP126.Literature.Standard.infinityFiniteLambda X r i hir (s,t)
      (t-(r-i-1:ℕ)) e = 0 := by
    apply (KIP126.Literature.Standard.infinityFiniteWindow X r (by omega)
      (s,t) ((t-(r-i-1:ℕ))-i) (by constructor <;> omega)).injective
    rw [map_zero,hk]
    unfold quotientMap
    refine quotient_map_class_eq_zero
      (cycles_antitone model X (s,t) (by omega))
      (boundaries_monotone model X (s,t) (by omega)) y ?_
    change y.val ∈ boundaries model X (1+t-((t-(r-i-1:ℕ))-i)) (s,t)
    convert hy using 1 <;> congr 1 <;> omega
  let ε : (SyntheticCategory.biShift (0,-(i:ℤ))).obj
      ((SyntheticCategory.biShift (0,(i:ℤ))).obj Y) ≅ Y :=
    (SyntheticCategory.biShift_comp (0,(i:ℤ)) (0,-(i:ℤ))).app Y ≪≫
      eqToIso (congrArg (fun k => (SyntheticCategory.biShift k).obj Y)
        (show (0,(i:ℤ))+(0,-(i:ℤ))=(0,0) by ext <;> simp)) ≪≫
      SyntheticCategory.biShift_zero.app Y
  let h : Q ⟶ (SyntheticCategory.biShift (0,(i:ℤ))).obj Y :=
    (SyntheticCategory.biShift_fullyFaithful (0,-(i:ℤ))).preimage (T.lambdaMap ≫ ε.inv)
  have hh : (SyntheticCategory.biShift (0,-(i:ℤ))).map h ≫ ε.hom = T.lambdaMap := by
    rw [show (SyntheticCategory.biShift (0,-(i:ℤ))).map h = T.lambdaMap ≫ ε.inv from
      (SyntheticCategory.biShift_fullyFaithful (0,-(i:ℤ))).map_preimage _,
      Category.assoc,ε.inv_hom_id,Category.comp_id]
  have hzero : (model.family.map h).eInftyMap (s,t,t-(r-i-1:ℕ)) e = 0 := by
    apply (weight_shift_lower_kernel_via_transpose (.quotient (r-i) (.nu X))
      (.shift (0,(i:ℤ)) (.quotient r (.nu X))) (.quotient r (.nu X))
      i (s,t) (t-(r-i-1:ℕ)) h ε T.lambdaMap hh e).mp
    simpa only [KIP126.Literature.Standard.infinityFiniteLambda,
      InfinityShiftCoordinates.finiteLambdaMap, dif_neg (Nat.ne_of_gt hi),
      KIP126.Literature.Standard.infinityShiftData, InfinityShiftCoordinates.shift,
      ModuleCat.comp_apply,T,SyntheticObject.obj,SyntheticAdamsFamily.quotient] using hk0
  have hb0 : b ≫ h = 0 := detected_map_zero_above_shifted_finite_top
    (.quotient (r-i) (.nu X)) X r (by omega) i s t (t-(r-i-1:ℕ)) (by omega)
    h (finiteTargetLabel model X (r-i) s t (r-i-1) y.val) b ⟨e,he,ha⟩ e he hzero
  exact (shifted_composite_zero_of_conjugate (i:ℤ) b h T.lambdaMap ε hh).mpr hb0

end
end KIP126.ProofTools.Internal.Mahowald
