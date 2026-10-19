module

public import KIP126.ProofTools.Language
public import KIP126.Literature.LambdaInversionAdams
import all KIP126.ProofTools.Paper.ExtensionRepresentatives
import all KIP126.ProofTools.FiltrationOperations
import all KIP126.ProofTools.Paper.ClassicalKernelCompactness
import all KIP126.ProofTools.DetectionOperations

/-! Representative statements from AimPaper, with explicit convergence and
realization hypotheses where the general model requires them.

The first eight statements use the actual classical Adams filtration on
homotopy groups. At fixed stem `d`, filtration `s` means bidegree `(s,d+s)`;
thus all original `(s,t)` coordinates are retained with `d = t-s`.
The representative relation is the one in AimPaper Definition 2.3 and
Proposition 2.5(1). The relation permits a signed target-source difference: when it is
negative, a filtration-preserving map can only have zero target grade.

The finite representative arguments prove 2.6, 2.12, 2.15--2.19.
Proposition 2.20 is proved with completeness of the source homotopy
filtration, finite filtration quotients and separation of the target
filtration. A finite inverse system and the canonical completion cone
produce one kernel representative, to which homotopy exactness applies.
Proposition 5.14 is proved from the specified realization coordinates and
an actual lambda-inversion Adams-tower comparison. Detection transports the
same representative, including zero and boundary labels. Constructing that
comparison for the fixed Standard model remains an upstream task.
The original Proposition 5.10 remains a registered proof obligation; its
interface has not been strengthened with the kernel-crossing condition of
finiteLambdaDivision.
-/
namespace KIP126.ProofTools.Paper
open CategoryTheory CategoryTheory.Limits
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.Classical.Adams KIP126.AdamsSynthetic KIP126.Core.SpectralSequence
open KIP126.Kervaire.Route KIP126.Literature
noncomputable section
universe u v w
variable {C : Type u} [StableHomotopyCategory.{u,v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w,v} Syn]
  [HasFunctorialCofiber (C := Syn)] (D : Model C Syn)
set_option backward.isDefEq.respectTransparency false

/-- The actual classical Adams E∞ component in bidegree (s,d+s), not an
E₂ cycle label or a synthetic grade. The convergence is used only below to
specify its homotopy representatives. -/
public abbrev ClassicalGrade (X : ClassicalObject) (s d : ℤ) :=
  (((D.classical.obj (X.obj D.auxiliary)).ssData (s,d+s)).eInfty :
    ModuleCat.{v} ℤ)

/-- The set {x} of homotopy representatives of a classical E∞ class. -/
public def ClassicalRepresents (X : ClassicalObject) (s d : ℤ)
    (x : ClassicalGrade D X s d) (a : HomotopyGroup d (X.obj D.auxiliary)) : Prop :=
  ∃ ar : (Subobject.underlying.obj
      ((D.classicalTower.tower (X.obj D.auxiliary)).filtration.F s d) : ModuleCat.{v} ℤ),
    ((D.classicalTower.tower (X.obj D.auxiliary)).filtration.F s d).arrow ar = a ∧
    (D.classicalTower.tower (X.obj D.auxiliary)).filtration.toAssociatedGraded s d ar =
      (eqToHom (congrArg
        (fun k => (D.classicalTower.tower (X.obj D.auxiliary)).filtration.associatedGraded s k)
        (show (d+s)-s = d by omega)))
        (((D.classicalConvergence X).identification (s,d+s)).hom x)

/-- Classical f-extension from filtration s to filtration t, with complete
representative ambiguity. Its length is t-s; essentiality is not imposed. -/
public def ClassicalExtension (X Y : ClassicalObject)
    (f : X.obj D.auxiliary ⟶ Y.obj D.auxiliary) (d s t : ℤ)
    (x : ClassicalGrade D X s d) (y : ClassicalGrade D Y t d) : Prop :=
  ∃ a : HomotopyGroup d (X.obj D.auxiliary),
    ClassicalRepresents D X s d x a ∧ ClassicalRepresents D Y t d y (a ≫ f)

/-- Definition 2.7: a nonzero competing target, with higher source filtration,
hitting the specified target-filtration interval. -/
public def ClassicalNoCrossingRange (X Y : ClassicalObject)
    (f : X.obj D.auxiliary ⟶ Y.obj D.auxiliary) (d s t threshold : ℤ) : Prop :=
  ¬ ∃ a b : ℤ, s < a ∧ a ≤ b ∧ threshold ≤ b ∧ b ≤ t ∧
    ∃ (x : ClassicalGrade D X a d) (y : ClassicalGrade D Y b d),
      y ≠ 0 ∧ ClassicalExtension D X Y f d a b x y

public def ClassicalNoCrossing (X Y : ClassicalObject)
    (f : X.obj D.auxiliary ⟶ Y.obj D.auxiliary) (d s t : ℤ) : Prop :=
  ClassicalNoCrossingRange D X Y f d s t (s+1)

/-- Source permanence in the g-ESS: every outgoing differential is zero.
Representatives may depend on the page; a single kernel representative is
not built into this definition or silently assumed in Proposition 2.20. -/
public def ClassicalPermanent (X Y : ClassicalObject)
    (g : X.obj D.auxiliary ⟶ Y.obj D.auxiliary) (d s : ℤ)
    (x : ClassicalGrade D X s d) : Prop :=
  ∀ n : ℕ, ClassicalExtension D X Y g d s (s+n) x 0

/-- E₀=Eᵣ in an extension sequence: all earlier differentials vanish.
The target is the original associated grade; earlier boundaries vanish too
under this all-earlier-pages condition. -/
public def ClassicalESSStable (X Y : ClassicalObject)
    (f : X.obj D.auxiliary ⟶ Y.obj D.auxiliary) (r : ℕ) : Prop :=
  ∀ i : ℕ, i < r → ∀ d s : ℤ,
    ∀ (x : ClassicalGrade D X s d) (y : ClassicalGrade D Y (s+i) d),
      ClassicalExtension D X Y f d s (s+i) x y → y = 0

/-- A homogeneous map of the two-column ESS in its representative presentation.
The additive E₀ maps preserve every differential relation, hence the source
cycle subgroups and target boundary subgroups on every page. This specifies
the whole induced ESS map, not just a commuting square on Adams E∞.
The degree-r maps are required below to be exactly dᵖᵣ and dᑫᵣ. -/
public def ClassicalESSInducedMap (X Y Z W : ClassicalObject)
    (f : X.obj D.auxiliary ⟶ Y.obj D.auxiliary)
    (g : Z.obj D.auxiliary ⟶ W.obj D.auxiliary)
    (p : X.obj D.auxiliary ⟶ Z.obj D.auxiliary)
    (q : Y.obj D.auxiliary ⟶ W.obj D.auxiliary) (r : ℕ) : Prop :=
  ∃ (a : ∀ d s : ℤ, ClassicalGrade D X s d →+ ClassicalGrade D Z (s+r) d)
    (b : ∀ d s : ℤ, ClassicalGrade D Y s d →+ ClassicalGrade D W (s+r) d),
    (∀ d s x y, ClassicalExtension D X Z p d s (s+r) x y ↔ a d s x = y) ∧
    (∀ d s x y, ClassicalExtension D Y W q d s (s+r) x y ↔ b d s x = y) ∧
    ∀ d s t : ℤ, s ≤ t →
      ∀ (x : ClassicalGrade D X s d) (y : ClassicalGrade D Y t d),
        ClassicalExtension D X Y f d s t x y →
        ClassicalExtension D Z W g d (s+r) (t+r) (a d s x) (b d t y)

/-! The following private bridge specializes the proved filtered-group
representative criterion to the actual classical Adams tower. It uses finite
filtration intervals only; no synthetic-to-classical or ESS convergence
assumption is introduced. -/

private def classical_gradeIso (X : ClassicalObject) (s d : ℤ) :
    ClassicalGrade D X s d ≅
      (D.classicalTower.tower (X.obj D.auxiliary)).filtration.associatedGraded s d :=
  ((D.classicalConvergence X).identification (s,d+s)) ≪≫
    eqToIso (congrArg
      (fun k => (D.classicalTower.tower (X.obj D.auxiliary)).filtration.associatedGraded s k)
      (show (d+s)-s = d by omega))

private theorem classical_represents_mem (X : ClassicalObject) (s d : ℤ)
    (x : ClassicalGrade D X s d) (a : HomotopyGroup d (X.obj D.auxiliary))
    (ha : ClassicalRepresents D X s d x a) :
    a ∈ (D.classicalTower.tower (X.obj D.auxiliary)).filtrationSubmodule s d := by
  obtain ⟨ar,har,_⟩ := ha
  rw [←har]
  have h : ((D.classicalTower.tower (X.obj D.auxiliary)).filtration.F s d).arrow ar ∈
      ModuleCat.subobjectModule _
        ((D.classicalTower.tower (X.obj D.auxiliary)).filtration.F s d) := ⟨ar,rfl⟩
  simpa only [AbstractAdamsTower.filtration,OrderIso.apply_symm_apply] using h

private theorem classical_representatives_difference (X : ClassicalObject) (s d : ℤ)
    (x : ClassicalGrade D X s d) (a b : HomotopyGroup d (X.obj D.auxiliary))
    (ha : ClassicalRepresents D X s d x a)
    (hb : ClassicalRepresents D X s d x b) :
    a-b ∈ (D.classicalTower.tower (X.obj D.auxiliary)).filtrationSubmodule (s+1) d := by
  obtain ⟨ar,har,hax⟩ := ha
  obtain ⟨br,hbr,hbx⟩ := hb
  have h := (Internal.element_grade_equal_iff
    (D.classicalTower.tower (X.obj D.auxiliary)).filtration s d ar br).mp
      (hax.trans hbx.symm)
  rw [har,hbr] at h
  simpa only [AbstractAdamsTower.filtration,OrderIso.apply_symm_apply] using h

private theorem classical_represents_of_difference (X : ClassicalObject) (s d : ℤ)
    (x : ClassicalGrade D X s d) (a b : HomotopyGroup d (X.obj D.auxiliary))
    (hb : ClassicalRepresents D X s d x b)
    (hdiff : a-b ∈ (D.classicalTower.tower (X.obj D.auxiliary)).filtrationSubmodule (s+1) d) :
    ClassicalRepresents D X s d x a := by
  let T := D.classicalTower.tower (X.obj D.auxiliary)
  have ha : a ∈ T.filtrationSubmodule s d := by
    have hh := (T.filtrationSubmodule s d).add_mem
      (T.filtrationSubmodule_antitone d (show s ≤ s+1 by omega) hdiff)
      (classical_represents_mem D X s d x b hb)
    simpa only [sub_add_cancel] using hh
  have ha' : a ∈ ModuleCat.subobjectModule _ (T.filtration.F s d) := by
    simpa only [AbstractAdamsTower.filtration,OrderIso.apply_symm_apply] using ha
  obtain ⟨ar,har⟩ := ha'
  obtain ⟨br,hbr,hbx⟩ := hb
  refine ⟨ar,har,?_⟩
  apply Eq.trans ?_ hbx
  apply (Internal.element_grade_equal_iff T.filtration s d ar br).mpr
  rw [har,hbr]
  simpa only [AbstractAdamsTower.filtration,OrderIso.apply_symm_apply] using hdiff

private theorem classical_represents_zero_iff (X : ClassicalObject) (s d : ℤ)
    (a : HomotopyGroup d (X.obj D.auxiliary)) :
    ClassicalRepresents D X s d 0 a ↔
      a ∈ (D.classicalTower.tower (X.obj D.auxiliary)).filtrationSubmodule (s+1) d := by
  have hz : ClassicalRepresents D X s d 0 (0 : HomotopyGroup d (X.obj D.auxiliary)) :=
    ⟨0, by simp only [map_zero], by simp only [map_zero]⟩
  constructor
  · intro ha
    simpa only [sub_zero] using classical_representatives_difference D X s d 0 a 0 ha hz
  · intro ha
    exact classical_represents_of_difference D X s d 0 a 0 hz
      (by simpa only [sub_zero] using ha)

private theorem classical_map_mem (X Y : ClassicalObject)
    (f : X.obj D.auxiliary ⟶ Y.obj D.auxiliary) (d s : ℤ)
    (a : HomotopyGroup d (X.obj D.auxiliary))
    (ha : a ∈ (D.classicalTower.tower (X.obj D.auxiliary)).filtrationSubmodule s d) :
    a ≫ f ∈ (D.classicalTower.tower (Y.obj D.auxiliary)).filtrationSubmodule s d := by
  obtain ⟨ar,rfl⟩ := ha
  refine ⟨ar ≫ (D.classicalTower.map f).stage s.toNat, ?_⟩
  change (ar ≫ (D.classicalTower.map f).stage s.toNat) ≫
      (D.classicalTower.tower (Y.obj D.auxiliary)).projection s =
    (ar ≫ (D.classicalTower.tower (X.obj D.auxiliary)).projection s) ≫ f
  rw [Category.assoc,(D.classicalTower.map f).projection s,←Category.assoc]

private theorem classical_noCrossing_to_filtered (X Y : ClassicalObject)
    (f : X.obj D.auxiliary ⟶ Y.obj D.auxiliary) (d s t threshold : ℤ)
    (hnc : ClassicalNoCrossingRange D X Y f d s t threshold) :
    FilteredNoCrossingRange (inducedMap f d)
      (fun u => ((D.classicalTower.tower (X.obj D.auxiliary)).filtrationSubmodule u d).toAddSubgroup)
      (fun u => ((D.classicalTower.tower (Y.obj D.auxiliary)).filtrationSubmodule u d).toAddSubgroup)
      s (t-s) threshold := by
  intro u v hsu huv htv hvs a ha hfa
  let TX := D.classicalTower.tower (X.obj D.auxiliary)
  let TY := D.classicalTower.tower (Y.obj D.auxiliary)
  change a ∈ TX.filtrationSubmodule u d at ha
  change a ≫ f ∈ TY.filtrationSubmodule v d at hfa
  have ha' : a ∈ ModuleCat.subobjectModule _ (TX.filtration.F u d) := by
    simpa only [AbstractAdamsTower.filtration,OrderIso.apply_symm_apply] using ha
  have hfa' : a ≫ f ∈ ModuleCat.subobjectModule _ (TY.filtration.F v d) := by
    simpa only [AbstractAdamsTower.filtration,OrderIso.apply_symm_apply] using hfa
  obtain ⟨ar,har⟩ := ha'
  obtain ⟨br,hbr⟩ := hfa'
  let x := (classical_gradeIso D X u d).inv (TX.filtration.toAssociatedGraded u d ar)
  let y := (classical_gradeIso D Y v d).inv (TY.filtration.toAssociatedGraded v d br)
  have hx : ClassicalRepresents D X u d x a := by
    refine ⟨ar,har,?_⟩
    change TX.filtration.toAssociatedGraded u d ar = (classical_gradeIso D X u d).hom x
    exact ((classical_gradeIso D X u d).toLinearEquiv.apply_symm_apply _).symm
  have hy : ClassicalRepresents D Y v d y (a≫f) := by
    refine ⟨br,hbr,?_⟩
    change TY.filtration.toAssociatedGraded v d br = (classical_gradeIso D Y v d).hom y
    exact ((classical_gradeIso D Y v d).toLinearEquiv.apply_symm_apply _).symm
  have hy0 : y = 0 := by
    by_contra hne
    exact hnc ⟨u,v,hsu,huv,htv,(by omega),x,y,hne,a,hx,hy⟩
  have hzero : TY.filtration.toAssociatedGraded v d br = 0 := by
    have hh := hy
    obtain ⟨br',hbr',hgrade⟩ := hh
    have heq : br = br' :=
      (ModuleCat.mono_iff_injective (TY.filtration.F v d).arrow).mp inferInstance
        (hbr.trans hbr'.symm)
    rw [heq,hgrade,hy0,map_zero,map_zero]
  have h := (TY.filtration.toAssociatedGraded_eq_zero_iff v d br).mp hzero
  rw [hbr] at h
  change a ≫ f ∈ TY.filtrationSubmodule (v+1) d
  simpa only [AbstractAdamsTower.filtration,OrderIso.apply_symm_apply] using h

private theorem classical_extension_range_universal (X Y : ClassicalObject)
    (f : X.obj D.auxiliary ⟶ Y.obj D.auxiliary) (d s t threshold : ℤ)
    (x : ClassicalGrade D X s d) (y : ClassicalGrade D Y t d)
    (he : ClassicalExtension D X Y f d s t x y)
    (hnc : ClassicalNoCrossingRange D X Y f d s t threshold) (ht : threshold ≤ t) :
    ∀ a : HomotopyGroup d (X.obj D.auxiliary),
      ClassicalRepresents D X s d x a →
      a≫f ∈ (D.classicalTower.tower (Y.obj D.auxiliary)).filtrationSubmodule threshold d →
      ClassicalRepresents D Y t d y (a≫f) := by
  obtain ⟨a0,hx0,hy0⟩ := he
  let TX := D.classicalTower.tower (X.obj D.auxiliary)
  let TY := D.classicalTower.tower (Y.obj D.auxiliary)
  let F := fun u => (TX.filtrationSubmodule u d).toAddSubgroup
  let G := fun u => (TY.filtrationSubmodule u d).toAddSubgroup
  have hall := (filtered_extension_noCrossingRange_iff (inducedMap f d) F G
    (fun i j hij z hz => TX.filtrationSubmodule_antitone d hij hz)
    (fun i j hij z hz => TY.filtrationSubmodule_antitone d hij hz)
    (fun u a ha => classical_map_mem D X Y f d u a ha)
    s (t-s) threshold (by omega) a0
    (classical_represents_mem D X s d x a0 hx0)
    (by
      change a0≫f ∈ TY.filtrationSubmodule (s+(t-s)) d
      simpa only [add_sub_cancel] using classical_represents_mem D Y t d y (a0≫f) hy0)).mp
    (classical_noCrossing_to_filtered D X Y f d s t threshold hnc)
  intro a ha hfa
  apply classical_represents_of_difference D Y t d y (a≫f) (a0≫f) hy0
  have hdiff := (hall a (classical_represents_mem D X s d x a ha)
    (classical_representatives_difference D X s d x a a0 ha hx0) hfa).2
  change a≫f-a0≫f ∈ TY.filtrationSubmodule (s+(t-s)+1) d at hdiff
  simpa only [add_sub_cancel] using hdiff

private theorem classical_extension_universal (X Y : ClassicalObject)
    (f : X.obj D.auxiliary ⟶ Y.obj D.auxiliary) (d s t : ℤ)
    (x : ClassicalGrade D X s d) (y : ClassicalGrade D Y t d)
    (he : ClassicalExtension D X Y f d s t x y)
    (hnc : ClassicalNoCrossing D X Y f d s t) :
    ∀ a : HomotopyGroup d (X.obj D.auxiliary),
      ClassicalRepresents D X s d x a → ClassicalRepresents D Y t d y (a≫f) := by
  have hc : ClassicalNoCrossingRange D X Y f d s t (min s t) := by
    rintro ⟨u,v,hsu,huv,htv,hvt,xx,yy,hne,he'⟩
    exact hnc ⟨u,v,hsu,huv,(by omega),hvt,xx,yy,hne,he'⟩
  intro a ha
  exact classical_extension_range_universal D X Y f d s t (min s t) x y he hc
    (min_le_right s t) a ha
    ((D.classicalTower.tower (Y.obj D.auxiliary)).filtrationSubmodule_antitone d
      (min_le_left s t)
      (classical_map_mem D X Y f d s a (classical_represents_mem D X s d x a ha)))

open CategoryTheory.MonoidalCategory

omit [HasFunctorialCofiber (C := C)] in
private theorem classical26_unit_natural {H X Y : C} (unit : SphereSpectrum ⟶ H) (f : X ⟶ Y) :
    f ≫ (λ_ Y).inv ≫ unit ▷ Y =
      (λ_ X).inv ≫ unit ▷ X ≫ H ◁ f := by
  rw [leftUnitor_inv_naturality_assoc, whisker_exchange]

private theorem classical26_shifted_tower_lift {H : C} {unit : SphereSpectrum ⟶ H}
    {X Y : C} (T : AbstractAdamsTower unit X) (U : AbstractAdamsTower unit Y)
    (k : ℕ) (b : X ⟶ U.stage k) :
    ∀ n : ℕ, ∃ c : T.stage n ⟶ U.stage (k+n),
      c ≫ U.projection ((k+n : ℕ) : ℤ) = T.projection (n : ℤ) ≫ b ≫ U.projection (k : ℤ) := by
  intro n
  induction n with
  | zero =>
    refine ⟨T.zeroIso.hom ≫ b, ?_⟩
    have hT0 : T.projection 0 = T.zeroIso.hom := by
      simp only [AbstractAdamsTower.projection, AbstractAdamsTower.map_self]
      exact Category.id_comp _
    change (T.zeroIso.hom ≫ b) ≫ U.projection (k : ℤ) =
      T.projection 0 ≫ b ≫ U.projection (k : ℤ)
    rw [hT0, Category.assoc]
  | succ n ih =>
    obtain ⟨c,hc⟩ := ih
    let a := T.map (Nat.le_succ n) ≫ c
    have hz : a ≫ HasFunctorialCofiber.cofibι (U.map (Nat.le_succ (k+n))) = 0 := by
      apply (cancel_mono (U.layerIso (k+n)).hom).mp
      rw [Category.assoc, U.layer_unit]
      dsimp only [a]
      rw [Category.assoc, classical26_unit_natural]
      calc
        T.map (Nat.le_succ n) ≫ (λ_ (T.stage n)).inv ≫ unit ▷ T.stage n ≫ H ◁ c =
            T.map (Nat.le_succ n) ≫
              (HasFunctorialCofiber.cofibι (T.map (Nat.le_succ n)) ≫ (T.layerIso n).hom) ≫ H ◁ c := by
          rw [T.layer_unit]
          simp only [Category.assoc]
        _ = 0 ≫ (U.layerIso (k+n)).hom := by
          have hzero : T.map (Nat.le_succ n) ≫
              HasFunctorialCofiber.cofibι (T.map (Nat.le_succ n)) = 0 :=
            Pretriangulated.comp_distTriang_mor_zero₁₂
              _ (HasFunctorialCofiber.cofib_distinguished (T.map (Nat.le_succ n)))
          rw [← Category.assoc, ← Category.assoc, hzero]
          simp only [zero_comp]
    obtain ⟨c',hc'⟩ := Pretriangulated.Triangle.coyoneda_exact₂
      _ (HasFunctorialCofiber.cofib_distinguished (U.map (Nat.le_succ (k+n)))) a hz
    change a = c' ≫ U.map (Nat.le_succ (k+n)) at hc'
    refine ⟨c', ?_⟩
    change c' ≫ U.projection (((k+n)+1 : ℕ) : ℤ) = _
    have hproj : U.map (Nat.le_succ (k+n)) ≫ U.projection ((k+n : ℕ) : ℤ) =
        U.projection (((k+n)+1 : ℕ) : ℤ) := by
      exact U.projection_compat (show ((k+n : ℕ) : ℤ) ≤ ((k+n+1 : ℕ) : ℤ) by omega)
    have hprojT : T.map (Nat.le_succ n) ≫ T.projection (n : ℤ) =
        T.projection ((n+1 : ℕ) : ℤ) := by
      exact T.projection_compat (show (n : ℤ) ≤ ((n+1 : ℕ) : ℤ) by omega)
    calc
      c' ≫ U.projection (((k+n)+1 : ℕ) : ℤ) =
          (c' ≫ U.map (Nat.le_succ (k+n))) ≫ U.projection ((k+n : ℕ) : ℤ) := by
        rw [Category.assoc, hproj]
      _ = a ≫ U.projection ((k+n : ℕ) : ℤ) := by rw [← hc']
      _ = T.projection ((n+1 : ℕ) : ℤ) ≫ b ≫ U.projection (k : ℤ) := by
        dsimp only [a]
        rw [Category.assoc, hc, ← Category.assoc, ← Category.assoc, hprojT, Category.assoc]


private theorem classical26_tower_filtration_composition {H : C} {unit : SphereSpectrum ⟶ H}
    {A : ClassicalAdamsFamily C} (P : ClassicalTowerPresentation unit A)
    {X Y : C} (f : X ⟶ Y) (k : ℕ)
    (hf : MapFiltrationAtLeast P f k) (s d : ℤ)
    (a : HomotopyGroup d X) (ha : a ∈ (P.tower X).filtrationSubmodule s d) :
    a ≫ f ∈ (P.tower Y).filtrationSubmodule (s+k) d := by
  obtain ⟨b,hb⟩ := hf
  by_cases hs : 0 ≤ s
  · have hsn : (s.toNat : ℤ) = s := Int.toNat_of_nonneg hs
    have haN : a ∈ (P.tower X).filtrationSubmodule (s.toNat : ℤ) d := by
      simpa only [hsn] using ha
    obtain ⟨ar,har⟩ := haN
    change ar ≫ (P.tower X).projection (s.toNat : ℤ) = a at har
    obtain ⟨c,hc⟩ := classical26_shifted_tower_lift (P.tower X) (P.tower Y) k b s.toNat
    have hsum : ((k+s.toNat : ℕ) : ℤ) = s+k := by omega
    have haF : a ≫ f ∈ (P.tower Y).filtrationSubmodule ((k+s.toNat : ℕ) : ℤ) d := by
      refine ⟨ar ≫ c, ?_⟩
      change (ar ≫ c) ≫ (P.tower Y).projection ((k+s.toNat : ℕ) : ℤ) = a ≫ f
      rw [Category.assoc, hc, ← Category.assoc ar, har, hb]
    simpa only [hsum] using haF
  · apply (P.tower Y).filtrationSubmodule_antitone d (show s+k ≤ (k : ℤ) by omega)
    refine ⟨a ≫ b, ?_⟩
    change (a ≫ b) ≫ (P.tower Y).projection (k : ℤ) = a ≫ f
    rw [Category.assoc, hb]

/-- AimPaper Corollary 2.6, original statement. The full Adams filtration k
is used; normalizedExponent, which only takes values 0 and 1, is not used. -/
public theorem adamsFiltrationVanishing (X Y : ClassicalObject)
    (f : X.obj D.auxiliary ⟶ Y.obj D.auxiliary) (k : ℕ)
    (hf : ExactMapAdamsFiltration D.classicalTower f k) :
    ∀ i : ℕ, i < k → ∀ d s : ℤ,
      ∀ (x : ClassicalGrade D X s d) (y : ClassicalGrade D Y (s+i) d),
        ClassicalExtension D X Y f d s (s+i) x y → y = 0 := by
  intro i hi d s x y hext
  dsimp only [ClassicalExtension, ClassicalRepresents] at hext
  rcases hext with ⟨a,ha,hb⟩
  rcases ha with ⟨ar,har,hgr⟩
  rcases hb with ⟨br,hbr,hgbr⟩
  have hmem : a ∈ (D.classicalTower.tower (X.obj D.auxiliary)).filtrationSubmodule s d := by
    have hmem : a ∈ ModuleCat.subobjectModule _
        ((D.classicalTower.tower (X.obj D.auxiliary)).filtration.F s d) := ⟨ar,har⟩
    simpa only [AbstractAdamsTower.filtration, OrderIso.apply_symm_apply] using hmem
  have hdeep := classical26_tower_filtration_composition D.classicalTower f k hf.1 s d a hmem
  have hnext : a ≫ f ∈
      (D.classicalTower.tower (Y.obj D.auxiliary)).filtrationSubmodule (s+i+1) d :=
    (D.classicalTower.tower (Y.obj D.auxiliary)).filtrationSubmodule_antitone d
      (show s+i+1 ≤ s+k by omega) hdeep
  have hz : (D.classicalTower.tower (Y.obj D.auxiliary)).filtration.toAssociatedGraded
      (s+i) d br = 0 := by
    apply ((D.classicalTower.tower (Y.obj D.auxiliary)).filtration.toAssociatedGraded_eq_zero_iff
      (s+i) d br).mpr
    rw [hbr]
    simpa only [AbstractAdamsTower.filtration, OrderIso.apply_symm_apply] using hnext
  let I := (D.classicalConvergence Y).identification (s+i,d+(s+i)) ≪≫
    eqToIso (congrArg
      (fun k => (D.classicalTower.tower (Y.obj D.auxiliary)).filtration.associatedGraded (s+i) k)
      (show (d+(s+i))-(s+i) = d by omega))
  apply (ModuleCat.mono_iff_injective I.hom).mp inferInstance
  change I.hom y = I.hom 0
  rw [map_zero]
  exact hgbr.symm.trans hz


/-- AimPaper Theorem 2.12, including the original weaker threshold crossing
condition and the zero right-edge extension of length k-1. -/
public theorem extensionSquare (X Y Z W : ClassicalObject)
    (f : X.obj D.auxiliary ⟶ Y.obj D.auxiliary)
    (p : X.obj D.auxiliary ⟶ Z.obj D.auxiliary)
    (g : Z.obj D.auxiliary ⟶ W.obj D.auxiliary)
    (q : Y.obj D.auxiliary ⟶ W.obj D.auxiliary)
    (hcomm : f ≫ q = p ≫ g)
    (m n l k s d : ℤ) (hm : 0 ≤ m) (hn : 0 ≤ n) (hl : 0 ≤ l)
    (hk : 0 < k) (hkl : k ≤ m+l-n)
    (x : ClassicalGrade D X s d) (y : ClassicalGrade D Y (s+n) d)
    (z : ClassicalGrade D Z (s+m) d) (w : ClassicalGrade D W (s+m+l) d)
    (hf : ClassicalExtension D X Y f d s (s+n) x y)
    (hp : ClassicalExtension D X Z p d s (s+m) x z)
    (hnc : ClassicalNoCrossing D X Y f d s (s+n) ∨
      ClassicalNoCrossing D X Z p d s (s+m))
    (hg : ClassicalExtension D Z W g d (s+m) (s+m+l) z w)
    (hgnc : ClassicalNoCrossingRange D Z W g d (s+m) (s+m+l) (s+n+k))
    (hq : ClassicalExtension D Y W q d (s+n) (s+n+k-1) y 0)
    (hqnc : ClassicalNoCrossing D Y W q d (s+n) (s+n+k-1)) :
    ClassicalExtension D Y W q d (s+n) (s+m+l) y w := by
  have common : ∃ a : HomotopyGroup d (X.obj D.auxiliary),
      ClassicalRepresents D Y (s+n) d y (a ≫ f) ∧
      ClassicalRepresents D Z (s+m) d z (a ≫ p) := by
    rcases hnc with hfnc | hpnc
    · obtain ⟨a,hax,haz⟩ := hp
      exact ⟨a,classical_extension_universal D X Y f d s (s+n) x y hf hfnc a hax,haz⟩
    · obtain ⟨a,hax,hay⟩ := hf
      exact ⟨a,hay,classical_extension_universal D X Z p d s (s+m) x z hp hpnc a hax⟩
  obtain ⟨a,hay,haz⟩ := common
  have hqzero := classical_extension_universal D Y W q d (s+n) (s+n+k-1) y 0 hq hqnc (a ≫ f) hay
  have hhigh := (classical_represents_zero_iff D W (s+n+k-1) d _).mp hqzero
  have hhigh' : (a ≫ p) ≫ g ∈
      (D.classicalTower.tower (W.obj D.auxiliary)).filtrationSubmodule (s+n+k) d := by
    simpa only [Category.assoc, hcomm, sub_add_cancel] using hhigh
  refine ⟨a ≫ f, hay, ?_⟩
  have hw := classical_extension_range_universal D Z W g d (s+m) (s+m+l)
    (s+n+k) z w hg hgnc (by omega) (a ≫ p) haz hhigh'
  simpa only [Category.assoc, ←hcomm] using hw

/-- AimPaper Corollary 2.15. No right-edge extension or right-edge crossing
hypothesis is added; the lower edge has full no-crossing as in the paper. -/
public theorem noCrossingExtensionSquare (X Y Z W : ClassicalObject)
    (f : X.obj D.auxiliary ⟶ Y.obj D.auxiliary)
    (p : X.obj D.auxiliary ⟶ Z.obj D.auxiliary)
    (g : Z.obj D.auxiliary ⟶ W.obj D.auxiliary)
    (q : Y.obj D.auxiliary ⟶ W.obj D.auxiliary)
    (hcomm : f ≫ q = p ≫ g)
    (m n l s d : ℤ) (hm : 0 ≤ m) (hn : 0 ≤ n) (hl : 0 ≤ l)
    (x : ClassicalGrade D X s d) (y : ClassicalGrade D Y (s+n) d)
    (z : ClassicalGrade D Z (s+m) d) (w : ClassicalGrade D W (s+m+l) d)
    (hf : ClassicalExtension D X Y f d s (s+n) x y)
    (hp : ClassicalExtension D X Z p d s (s+m) x z)
    (hnc : ClassicalNoCrossing D X Y f d s (s+n) ∨
      ClassicalNoCrossing D X Z p d s (s+m))
    (hg : ClassicalExtension D Z W g d (s+m) (s+m+l) z w)
    (hgnc : ClassicalNoCrossing D Z W g d (s+m) (s+m+l)) :
    ClassicalExtension D Y W q d (s+n) (s+m+l) y w := by
  have common : ∃ a : HomotopyGroup d (X.obj D.auxiliary),
      ClassicalRepresents D Y (s+n) d y (a≫f) ∧
      ClassicalRepresents D Z (s+m) d z (a≫p) := by
    rcases hnc with hfnc | hpnc
    · obtain ⟨a,hax,haz⟩ := hp
      exact ⟨a,classical_extension_universal D X Y f d s (s+n) x y hf hfnc a hax,haz⟩
    · obtain ⟨a,hax,hay⟩ := hf
      exact ⟨a,hay,classical_extension_universal D X Z p d s (s+m) x z hp hpnc a hax⟩
  obtain ⟨a,hay,haz⟩ := common
  refine ⟨a≫f,hay,?_⟩
  have hw := classical_extension_universal D Z W g d (s+m) (s+m+l) z w hg hgnc (a≫p) haz
  simpa only [Category.assoc,←hcomm] using hw

/-- AimPaper Corollary 2.16. The target filtration is s+m, so the
conclusion's length is m-n; no extra inequality m≥n is imposed. -/
public theorem extensionTriangle (X Y Z : ClassicalObject)
    (f : X.obj D.auxiliary ⟶ Y.obj D.auxiliary)
    (p : X.obj D.auxiliary ⟶ Z.obj D.auxiliary)
    (q : Y.obj D.auxiliary ⟶ Z.obj D.auxiliary) (hcomm : f ≫ q = p)
    (n m s d : ℤ) (hn : 0 ≤ n) (hm : 0 ≤ m)
    (x : ClassicalGrade D X s d) (y : ClassicalGrade D Y (s+n) d)
    (z : ClassicalGrade D Z (s+m) d)
    (hf : ClassicalExtension D X Y f d s (s+n) x y)
    (hp : ClassicalExtension D X Z p d s (s+m) x z)
    (hnc : ClassicalNoCrossing D X Y f d s (s+n) ∨
      ClassicalNoCrossing D X Z p d s (s+m)) :
    ClassicalExtension D Y Z q d (s+n) (s+m) y z := by
  rcases hnc with hfnc | hpnc
  · obtain ⟨a,hax,haz⟩ := hp
    refine ⟨a ≫ f, classical_extension_universal D X Y f d s (s+n) x y hf hfnc a hax, ?_⟩
    simpa only [Category.assoc, hcomm] using haz
  · obtain ⟨a,hax,hay⟩ := hf
    refine ⟨a ≫ f, hay, ?_⟩
    have haz := classical_extension_universal D X Z p d s (s+m) x z hp hpnc a hax
    simpa only [Category.assoc, hcomm] using haz

/-- AimPaper Corollary 2.17. The print uses Y for the object of z although
the diagram puts z in Z, and lists n,m≥0 although the lengths are m,l.
The diagram determines the type of z. The unused n and the printed n,m≥0
are retained exactly; no additional l≥0 premise is imposed. The object-name
printing discrepancy is recorded in corrections.yaml. -/
public theorem extensionComposition (X Z W : ClassicalObject)
    (p : X.obj D.auxiliary ⟶ Z.obj D.auxiliary)
    (g : Z.obj D.auxiliary ⟶ W.obj D.auxiliary)
    (q : X.obj D.auxiliary ⟶ W.obj D.auxiliary) (hcomm : p ≫ g = q)
    (n m l s d : ℤ) (hn : 0 ≤ n) (hm : 0 ≤ m)
    (x : ClassicalGrade D X s d) (z : ClassicalGrade D Z (s+m) d)
    (w : ClassicalGrade D W (s+m+l) d)
    (hp : ClassicalExtension D X Z p d s (s+m) x z)
    (hg : ClassicalExtension D Z W g d (s+m) (s+m+l) z w)
    (hgnc : ClassicalNoCrossing D Z W g d (s+m) (s+m+l)) :
    ClassicalExtension D X W q d s (s+m+l) x w := by
  obtain ⟨a,hax,haz⟩ := hp
  refine ⟨a,hax,?_⟩
  have haw := classical_extension_universal D Z W g d (s+m) (s+m+l) z w hg hgnc (a ≫ p) haz
  simpa only [Category.assoc, hcomm] using haw


private theorem classical_ess_reps_iff (X : ClassicalObject) (s d : ℤ)
    (x : ClassicalGrade D X s d) (a : HomotopyGroup d (X.obj D.auxiliary)) :
    ClassicalRepresents D X s d x a ↔
      ∃ ar : (Subobject.underlying.obj (((D.classicalTower.tower (X.obj D.auxiliary)).filtration).F s d) : ModuleCat.{v} ℤ),
        (((D.classicalTower.tower (X.obj D.auxiliary)).filtration).F s d).arrow ar = a ∧ ((D.classicalTower.tower (X.obj D.auxiliary)).filtration).toAssociatedGraded s d ar = (classical_gradeIso D X s d).hom x := by
  rfl

private theorem classical_ess_lift_mem (X : ClassicalObject) (s d : ℤ)
    (a : HomotopyGroup d (X.obj D.auxiliary)) (ha : a ∈ (D.classicalTower.tower (X.obj D.auxiliary)).filtrationSubmodule s d) :
    ∃ ar : (Subobject.underlying.obj (((D.classicalTower.tower (X.obj D.auxiliary)).filtration).F s d) : ModuleCat.{v} ℤ),
      (((D.classicalTower.tower (X.obj D.auxiliary)).filtration).F s d).arrow ar = a := by
  have h : a ∈ ModuleCat.subobjectModule _ (((D.classicalTower.tower (X.obj D.auxiliary)).filtration).F s d) := by
    simpa only [AbstractAdamsTower.filtration, OrderIso.apply_symm_apply] using ha
  exact h

private theorem classical_ess_label_exists (X : ClassicalObject) (s d : ℤ)
    (a : HomotopyGroup d (X.obj D.auxiliary)) (ha : a ∈ (D.classicalTower.tower (X.obj D.auxiliary)).filtrationSubmodule s d) :
    ∃ x : ClassicalGrade D X s d, ClassicalRepresents D X s d x a := by
  obtain ⟨ar,har⟩ := classical_ess_lift_mem D X s d a ha
  refine ⟨(classical_gradeIso D X s d).inv (((D.classicalTower.tower (X.obj D.auxiliary)).filtration).toAssociatedGraded s d ar), ?_⟩
  apply (classical_ess_reps_iff D X s d _ _).mpr
  exact ⟨ar,har,((classical_gradeIso D X s d).toLinearEquiv.apply_symm_apply _).symm⟩

private theorem classical_ess_rep_exists (X : ClassicalObject) (s d : ℤ) (x : ClassicalGrade D X s d) :
    ∃ a : HomotopyGroup d (X.obj D.auxiliary), ClassicalRepresents D X s d x a := by
  haveI : Epi (((D.classicalTower.tower (X.obj D.auxiliary)).filtration).toAssociatedGraded s d) := inferInstanceAs (Epi (cokernel.π _))
  obtain ⟨ar,har⟩ := (ModuleCat.epi_iff_surjective (((D.classicalTower.tower (X.obj D.auxiliary)).filtration).toAssociatedGraded s d)).mp inferInstance ((classical_gradeIso D X s d).hom x)
  exact ⟨(((D.classicalTower.tower (X.obj D.auxiliary)).filtration).F s d).arrow ar, (classical_ess_reps_iff D X s d _ _).mpr ⟨ar,rfl,har⟩⟩

private theorem classical_ess_stable_image_mem (X Y : ClassicalObject)
    (f : X.obj D.auxiliary ⟶ Y.obj D.auxiliary) (r : ℕ)
    (hf : ClassicalESSStable D X Y f r) (s d : ℤ)
    (a : HomotopyGroup d (X.obj D.auxiliary)) (ha : a ∈ (D.classicalTower.tower (X.obj D.auxiliary)).filtrationSubmodule s d) :
    a ≫ f ∈ (D.classicalTower.tower (Y.obj D.auxiliary)).filtrationSubmodule (s+r) d := by
  have aux : ∀ R : ℕ, ClassicalESSStable D X Y f R →
      a ≫ f ∈ (D.classicalTower.tower (Y.obj D.auxiliary)).filtrationSubmodule (s+R) d := by
    intro R
    induction R with
    | zero =>
      intro h
      simpa only [Nat.cast_zero, add_zero] using classical_map_mem D X Y f d s a ha
    | succ R ih =>
      intro h
      have hm := ih (fun i hi => h i (by omega))
      obtain ⟨x,hx⟩ := classical_ess_label_exists D X s d a ha
      obtain ⟨y,hy⟩ := classical_ess_label_exists D Y (s+R) d (a≫f) hm
      have hy0 : y=0 := h R (by omega) d s x y ⟨a,hx,hy⟩
      subst y
      have hh := (classical_represents_zero_iff D Y (s+R) d _).mp hy
      simpa only [Nat.cast_succ, add_assoc] using hh
  exact aux r hf

private theorem classical_ess_labels_eq_of_difference (X : ClassicalObject) (s d : ℤ)
    (x y : ClassicalGrade D X s d) (a b : HomotopyGroup d (X.obj D.auxiliary))
    (hx : ClassicalRepresents D X s d x a) (hy : ClassicalRepresents D X s d y b)
    (hdiff : a-b ∈ (D.classicalTower.tower (X.obj D.auxiliary)).filtrationSubmodule (s+1) d) : x=y := by
  obtain ⟨ar,har,hax⟩ := (classical_ess_reps_iff D X s d _ _).mp hx
  obtain ⟨br,hbr,hby⟩ := (classical_ess_reps_iff D X s d _ _).mp hy
  apply (classical_gradeIso D X s d).toLinearEquiv.injective
  change (classical_gradeIso D X s d).hom x = (classical_gradeIso D X s d).hom y
  rw [←hax,←hby]
  apply (Internal.element_grade_equal_iff ((D.classicalTower.tower (X.obj D.auxiliary)).filtration) s d ar br).mpr
  rw [har,hbr]
  simpa only [AbstractAdamsTower.filtration, OrderIso.apply_symm_apply] using hdiff

private theorem classical_ess_reps_add (X : ClassicalObject) (s d : ℤ)
    (x y : ClassicalGrade D X s d) (a b : HomotopyGroup d (X.obj D.auxiliary))
    (hx : ClassicalRepresents D X s d x a) (hy : ClassicalRepresents D X s d y b) :
    ClassicalRepresents D X s d (x+y) (a+b) := by
  obtain ⟨ar,har,hax⟩ := (classical_ess_reps_iff D X s d _ _).mp hx
  obtain ⟨br,hbr,hby⟩ := (classical_ess_reps_iff D X s d _ _).mp hy
  apply (classical_ess_reps_iff D X s d _ _).mpr
  exact ⟨ar+br,by rw [map_add,har,hbr],by rw [map_add,map_add,hax,hby]⟩

private theorem classical_ess_extension_add (X Y : ClassicalObject)
    (f : X.obj D.auxiliary ⟶ Y.obj D.auxiliary) (s t d : ℤ)
    (x x' : ClassicalGrade D X s d) (y y' : ClassicalGrade D Y t d)
    (h : ClassicalExtension D X Y f d s t x y)
    (h' : ClassicalExtension D X Y f d s t x' y') :
    ClassicalExtension D X Y f d s t (x+x') (y+y') := by
  obtain ⟨a,ha,hfa⟩ := h
  obtain ⟨b,hb,hfb⟩ := h'
  exact ⟨a+b,classical_ess_reps_add D X s d x x' a b ha hb,
    by simpa only [Preadditive.add_comp] using classical_ess_reps_add D Y t d y y' (a≫f) (b≫f) hfa hfb⟩

private theorem classical_ess_stable_extension_unique (X Y : ClassicalObject)
    (f : X.obj D.auxiliary ⟶ Y.obj D.auxiliary) (r : ℕ)
    (hf : ClassicalESSStable D X Y f r) (s d : ℤ)
    (x : ClassicalGrade D X s d) :
    ∃! y : ClassicalGrade D Y (s+r) d, ClassicalExtension D X Y f d s (s+r) x y := by
  obtain ⟨a,ha⟩ := classical_ess_rep_exists D X s d x
  obtain ⟨y,hy⟩ := classical_ess_label_exists D Y (s+r) d (a≫f)
    (classical_ess_stable_image_mem D X Y f r hf s d a (classical_represents_mem D X s d x a ha))
  refine ⟨y,⟨a,ha,hy⟩,?_⟩
  rintro z ⟨b,hb,hz⟩
  apply classical_ess_labels_eq_of_difference D Y (s+r) d z y (b≫f) (a≫f) hz hy
  have hh := classical_ess_stable_image_mem D X Y f r hf (s+1) d (b-a)
    (classical_representatives_difference D X s d x b a hb ha)
  simpa only [Preadditive.sub_comp, add_assoc,add_comm,add_left_comm] using hh

private def classical_ess_stableMap (X Y : ClassicalObject)
    (f : X.obj D.auxiliary ⟶ Y.obj D.auxiliary) (r : ℕ)
    (hf : ClassicalESSStable D X Y f r) (d s : ℤ) :
    ClassicalGrade D X s d →+ ClassicalGrade D Y (s+r) d where
  toFun x := (classical_ess_stable_extension_unique D X Y f r hf s d x).choose
  map_zero' := by
    symm
    apply (classical_ess_stable_extension_unique D X Y f r hf s d 0).choose_spec.2
    exact ⟨0,(classical_represents_zero_iff D X s d 0).mpr (Submodule.zero_mem _),
      by simpa only [zero_comp] using (classical_represents_zero_iff D Y (s+r) d 0).mpr (Submodule.zero_mem _)⟩
  map_add' x x' := by
    symm
    apply (classical_ess_stable_extension_unique D X Y f r hf s d (x+x')).choose_spec.2
    exact classical_ess_extension_add D X Y f s (s+r) d x x' _ _
      (classical_ess_stable_extension_unique D X Y f r hf s d x).choose_spec.1
      (classical_ess_stable_extension_unique D X Y f r hf s d x').choose_spec.1

private theorem classical_ess_stableMap_graph (X Y : ClassicalObject)
    (f : X.obj D.auxiliary ⟶ Y.obj D.auxiliary) (r : ℕ)
    (hf : ClassicalESSStable D X Y f r) (d s : ℤ)
    (x : ClassicalGrade D X s d) (y : ClassicalGrade D Y (s+r) d) :
    ClassicalExtension D X Y f d s (s+r) x y ↔ classical_ess_stableMap D X Y f r hf d s x=y := by
  constructor
  · intro he
    exact ((classical_ess_stable_extension_unique D X Y f r hf s d x).choose_spec.2 y he).symm
  · intro he
    rw [←he]
    exact (classical_ess_stable_extension_unique D X Y f r hf s d x).choose_spec.1

private theorem classical_ess_stableMap_represents (X Y : ClassicalObject)
    (f : X.obj D.auxiliary ⟶ Y.obj D.auxiliary) (r : ℕ)
    (hf : ClassicalESSStable D X Y f r) (d s : ℤ)
    (x : ClassicalGrade D X s d) (a : HomotopyGroup d (X.obj D.auxiliary))
    (ha : ClassicalRepresents D X s d x a) :
    ClassicalRepresents D Y (s+r) d (classical_ess_stableMap D X Y f r hf d s x) (a≫f) := by
  obtain ⟨y,hy⟩ := classical_ess_label_exists D Y (s+r) d (a≫f)
    (classical_ess_stable_image_mem D X Y f r hf s d a (classical_represents_mem D X s d x a ha))
  have h := (classical_ess_stableMap_graph D X Y f r hf d s x y).mp ⟨a,ha,hy⟩
  rwa [h]

/-- AimPaper Corollary 2.18: dᵖᵣ and dᑫᵣ induce a map of the f- and
 g-extension spectral sequences on every page, with their exact degree r. -/
public theorem extensionSpectralSequenceMorphism (X Y Z W : ClassicalObject)
    (f : X.obj D.auxiliary ⟶ Y.obj D.auxiliary)
    (p : X.obj D.auxiliary ⟶ Z.obj D.auxiliary)
    (g : Z.obj D.auxiliary ⟶ W.obj D.auxiliary)
    (q : Y.obj D.auxiliary ⟶ W.obj D.auxiliary)
    (hcomm : f ≫ q = p ≫ g) (r : ℕ)
    (hp : ClassicalESSStable D X Z p r) (hq : ClassicalESSStable D Y W q r) :
    ClassicalESSInducedMap D X Y Z W f g p q r := by
  refine ⟨classical_ess_stableMap D X Z p r hp,classical_ess_stableMap D Y W q r hq,
    classical_ess_stableMap_graph D X Z p r hp,classical_ess_stableMap_graph D Y W q r hq,?_⟩
  intro d s t hst x y he
  obtain ⟨a,hax,hay⟩ := he
  refine ⟨a≫p,classical_ess_stableMap_represents D X Z p r hp d s x a hax,?_⟩
  have hh := classical_ess_stableMap_represents D Y W q r hq d t y (a≫f) hay
  simpa only [Category.assoc,hcomm] using hh


/-- AimPaper Corollary 2.19. Permanence is in the g-extension sequence,
not in the Adams sequence of Y. No no-crossing premise is introduced. -/
public theorem permanentCycle_of_nullComposite (X Y Z : ClassicalObject)
    (f : X.obj D.auxiliary ⟶ Y.obj D.auxiliary)
    (g : Y.obj D.auxiliary ⟶ Z.obj D.auxiliary) (hzero : f ≫ g = 0)
    (n s d : ℤ) (hn : 0 ≤ n)
    (x : ClassicalGrade D X s d) (y : ClassicalGrade D Y (s+n) d)
    (hf : ClassicalExtension D X Y f d s (s+n) x y) :
    ClassicalPermanent D Y Z g d (s+n) y := by
  obtain ⟨a, _, hy⟩ := hf
  intro m
  refine ⟨a ≫ f, hy, ?_⟩
  rw [Category.assoc, hzero, Limits.comp_zero]
  refine ⟨0, ?_, ?_⟩
  · simp
  · simp

/-! Separate the finite algebra in Proposition 2.20 from its convergence
step.  The following lemmas do not interchange page-dependent witnesses.
In particular, a common kernel representative is not a consequence recorded
by `ClassicalTowerConvergence`. -/

private theorem classical_permanent_iff_approximate_kernel (Y Z : ClassicalObject)
    (g : Y.obj D.auxiliary ⟶ Z.obj D.auxiliary) (d s : ℤ)
    (y : ClassicalGrade D Y s d) :
    ClassicalPermanent D Y Z g d s y ↔
      ∀ n : ℕ, ∃ a : HomotopyGroup d (Y.obj D.auxiliary),
        ClassicalRepresents D Y s d y a ∧
          a ≫ g ∈ (D.classicalTower.tower (Z.obj D.auxiliary)).filtrationSubmodule
            (s+n+1) d := by
  constructor
  · intro h n
    obtain ⟨a, ha, hga⟩ := h n
    exact ⟨a, ha, (classical_represents_zero_iff D Z (s+n) d (a≫g)).mp hga⟩
  · intro h n
    obtain ⟨a, ha, hga⟩ := h n
    exact ⟨a, ha, (classical_represents_zero_iff D Z (s+n) d (a≫g)).mpr hga⟩

private theorem classical_boundary_of_kernel_representative (X Y Z : ClassicalObject)
    (f : X.obj D.auxiliary ⟶ Y.obj D.auxiliary)
    (g : Y.obj D.auxiliary ⟶ Z.obj D.auxiliary)
    (hexact : ∀ d : ℤ, ∀ a : HomotopyGroup d (Y.obj D.auxiliary),
      a ≫ g = 0 ↔ ∃ b : HomotopyGroup d (X.obj D.auxiliary), b ≫ f = a)
    (d s : ℤ) (y : ClassicalGrade D Y s d)
    (hkernel : ∃ a : HomotopyGroup d (Y.obj D.auxiliary),
      ClassicalRepresents D Y s d y a ∧ a ≫ g = 0) :
    ∃ a : ℤ, a ≤ s ∧ ∃ x : ClassicalGrade D X a d,
      ClassicalExtension D X Y f d a s x y := by
  obtain ⟨a, ha, hga⟩ := hkernel
  obtain ⟨b, hbf⟩ := (hexact d a).mp hga
  let k : ℤ := min 0 s
  have hk : k.toNat = 0 := Int.toNat_eq_zero.mpr (min_le_left 0 s)
  have hb : b ∈ (D.classicalTower.tower (X.obj D.auxiliary)).filtrationSubmodule k d := by
    change ∃ z : HomotopyGroup d
        ((D.classicalTower.tower (X.obj D.auxiliary)).stage k.toNat),
      z ≫ ((D.classicalTower.tower (X.obj D.auxiliary)).map (Nat.zero_le k.toNat) ≫
        (D.classicalTower.tower (X.obj D.auxiliary)).zeroIso.hom) = b
    rw [hk]
    refine ⟨b ≫ (D.classicalTower.tower (X.obj D.auxiliary)).zeroIso.inv, ?_⟩
    simp only [AbstractAdamsTower.map_self, Category.id_comp, Category.assoc,
      Iso.inv_hom_id, Category.comp_id]
  obtain ⟨x, hx⟩ := classical_ess_label_exists D X k d b hb
  exact ⟨k, min_le_right 0 s, x, b, hx, hbf.symm ▸ ha⟩

/-- AimPaper Proposition 2.20, with the source profinite compactness and
target separation hypotheses explicit. Exactness is only required at the
middle homotopy group; no chosen kernel representative is assumed. -/
public theorem extensionBoundary_of_exact (X Y Z : ClassicalObject)
    (f : X.obj D.auxiliary ⟶ Y.obj D.auxiliary)
    (g : Y.obj D.auxiliary ⟶ Z.obj D.auxiliary)
    (hYcomplete : ∀ d : ℤ, Nonempty (Filtration.CompletionWitness
      (D.classicalTower.tower (Y.obj D.auxiliary)).filtration d))
    (hYfinite : ∀ (d : ℤ) (n : ℕ), Finite
      (HomotopyGroup d (Y.obj D.auxiliary) ⧸
        (D.classicalTower.tower (Y.obj D.auxiliary)).filtrationSubmodule n d))
    (hZsep : ∀ (d : ℤ) (a : HomotopyGroup d (Z.obj D.auxiliary)),
      (∀ n : ℕ, a ∈
        (D.classicalTower.tower (Z.obj D.auxiliary)).filtrationSubmodule n d) → a = 0)
    (hexact : ∀ d : ℤ, ∀ a : HomotopyGroup d (Y.obj D.auxiliary),
      a ≫ g = 0 ↔ ∃ b : HomotopyGroup d (X.obj D.auxiliary), b ≫ f = a) :
    ∀ d s : ℤ, ∀ y : ClassicalGrade D Y s d,
      ClassicalPermanent D Y Z g d s y →
      ∃ a : ℤ, a ≤ s ∧ ∃ x : ClassicalGrade D X a d,
        ClassicalExtension D X Y f d a s x y := by
  intro d s y hpermanent
  apply classical_boundary_of_kernel_representative D X Y Z f g hexact d s y
  let TY := D.classicalTower.tower (Y.obj D.auxiliary)
  let TZ := D.classicalTower.tower (Z.obj D.auxiliary)
  have hfinite : ∀ n : ℕ, Finite (TY.filtration.quotientAt n d) := by
    intro n
    letI : Finite (HomotopyGroup d (Y.obj D.auxiliary) ⧸
        ModuleCat.subobjectModule _ (TY.filtration.F n d)) := by
      simpa only [AbstractAdamsTower.filtration, OrderIso.apply_symm_apply]
        using hYfinite d n
    exact finite_quotientAt_of_submodule TY.filtration d n
  let S : ℤ → Set (HomotopyGroup d (Y.obj D.auxiliary)) := fun k =>
    {a | ClassicalRepresents D Y s d y a ∧ a ≫ g ∈ TZ.filtrationSubmodule k d}
  have hS : Antitone S := by
    intro k l hkl a ha
    exact ⟨ha.1, TZ.filtrationSubmodule_antitone d hkl ha.2⟩
  have hne : ∀ k : ℤ, (S k).Nonempty := by
    intro k
    let n := (k-s-1).toNat
    obtain ⟨a, ha, hga⟩ := hpermanent n
    have hga' : a≫g ∈ TZ.filtrationSubmodule (s+n+1) d :=
      (classical_represents_zero_iff D Z (s+n) d (a≫g)).mp hga
    refine ⟨a, ha, TZ.filtrationSubmodule_antitone d ?_ hga'⟩
    dsimp only [n]
    omega
  obtain ⟨a, ha⟩ := finite_filtration_compactness TY.filtration d
    (hYcomplete d).some (finite_quotientAt_int TY.filtration d hfinite) S hS hne
  have hrep : ClassicalRepresents D Y s d y a := by
    obtain ⟨b, hb, hab⟩ := ha (s+1)
    apply classical_represents_of_difference D Y s d y a b hb.1
    have hh := (quotientProjection_eq_iff_sub_mem TY.filtration d (s+1) a b).mp hab
    simpa only [AbstractAdamsTower.filtration, OrderIso.apply_symm_apply] using hh
  refine ⟨a, hrep, hZsep d (a≫g) (fun n => ?_)⟩
  obtain ⟨b, hb, hab⟩ := ha n
  have hh := (quotientProjection_eq_iff_sub_mem TY.filtration d n a b).mp hab
  have hdiff : a-b ∈ TY.filtrationSubmodule n d := by
    simpa only [AbstractAdamsTower.filtration, OrderIso.apply_symm_apply] using hh
  have himage := classical_map_mem D Y Z g d n (a-b) hdiff
  rw [Preadditive.sub_comp] at himage
  have hsum := (TZ.filtrationSubmodule n d).add_mem himage hb.2
  simpa only [sub_add_cancel] using hsum

/-- AimPaper Proposition 5.10, original finite-page crossing equivalence.
The competing synthetic extension is in the same actual quotient and weight.
The extra target-kernel crossing exclusion of the revised division theorem
is deliberately absent. The original source issue remains unresolved. -/
public theorem finiteCrossing_iff_syntheticCrossing (X Y : ClassicalObject)
    (f : X.obj D.auxiliary ⟶ Y.obj D.auxiliary)
    (r : ℕ) (n s t : ℤ)
    (x : Ambient D X (s,t)) (y : Ambient D Y (s+n,t+n))
    (he : FiniteExtension D X Y f r n s t x y) :
    FiniteHasCrossing D X Y f r n s t ↔
      ∃ a b : ℤ, s < a ∧ a ≤ b ∧ b ≤ s+n ∧
        ∃ (source : ((D.family.obj
          ((SyntheticObject.quotient (r-1) (extensionSourceObject D X Y f)).obj
            D.nu D.auxiliary)).sequence.ssData
          (a,(t-s)+a,t+normalizedExponent D.classicalTower f)).eInfty)
          (target : ((D.family.obj
          ((SyntheticObject.quotient (r-1) (.nu Y)).obj D.nu D.auxiliary)).sequence.ssData
          (a+(b-a),(t-s)+(a+(b-a)),t+normalizedExponent D.classicalTower f)).eInfty),
          target ≠ 0 ∧ TowerExtensionEquation
            (D.convergentMap (.quotient (r-1) (extensionSourceObject D X Y f))
              (.quotient (r-1) (.nu Y)) (finiteExtensionMap D X Y f (r-1)))
            (t-s,t+normalizedExponent D.classicalTower f) a (b-a) source target := by
  sorry

private theorem paper_detects_transport (U : SyntheticObject) {i j : Tridegree} (h : i=j)
    (x : (D.family.obj (U.obj D.nu D.auxiliary)).E₂ i)
    (a : BiHom (i.2.1-i.1) i.2.2 (U.obj D.nu D.auxiliary))
    (ha : Detects (D.convergence U) i x a) :
    Detects (D.convergence U) j (regradeE2 h x)
      (homotopyRegrade (congrArg (fun k : Tridegree => k.2.1-k.1) h)
        (congrArg (fun k : Tridegree => k.2.2) h) a) := by
  subst j
  exact ha

private theorem paper_e2_regrade_comp {A : SyntheticAdamsSS.{v}}
    {i j k : Tridegree} (hij : i=j) (hjk : j=k) (z : A.E₂ i) :
    regradeE2 hjk (regradeE2 hij z)=regradeE2 (hij.trans hjk) z := by
  subst j
  subst k
  rfl

private theorem paper_homotopy_regrade_comp {A : Syn} {m m' m'' w w' w'' : ℤ}
    (hm : m=m') (hm' : m'=m'') (hw : w=w') (hw' : w'=w'') (a : BiHom m w A) :
    homotopyRegrade hm' hw' (homotopyRegrade hm hw a) =
      homotopyRegrade (hm.trans hm') (hw.trans hw') a := by
  subst m'
  subst m''
  subst w'
  subst w''
  rfl

private theorem paper_e2Map_regrade {R : RealizationCoordinates D}
    {U : SyntheticObject} {X : ClassicalObject}
    (K : LambdaInversionAdamsObjectComparison D R U X)
    (s t w w' : ℤ) (hw : w=w') (h : (s,t,w)=(s,t,w'))
    (x : (D.family.obj (U.obj D.nu D.auxiliary)).E₂ (s,t,w)) :
    K.e2Map w' (s,t) (regradeE2 h x)=K.e2Map w (s,t) x := by
  subst w'
  rfl

private theorem realization_homotopy_regrade (R : RealizationCoordinates D)
    {U : Syn} (m m' w : ℤ) (hm : m=m') (a : BiHom m w U) :
    (R.sphere m' w).hom ≫ D.recovery.realization.map (homotopyRegrade hm rfl a) =
      eqToHom (congrArg (Sphere (C := C)) hm.symm) ≫
        (R.sphere m w).hom ≫ D.recovery.realization.map a := by
  subst m'
  simp only [homotopyRegrade,eqToHom_refl,Category.id_comp]

private theorem normalized_realization_square (R : RealizationCoordinates D)
    (K : LambdaInversionAdamsComparison D R) (X Y : ClassicalObject)
    (f : X.obj D.auxiliary ⟶ Y.obj D.auxiliary) :
    D.recovery.realization.map (D.normalizedMap X Y f).map ≫ (K.nu Y).target.hom =
      (K.shiftedNu X (normalizedExponent D.classicalTower f)).target.hom ≫ f := by
  let L := D.recovery.realization
  let e := normalizedExponent D.classicalTower f
  let l := L.map (lambdaToPositivePow e (D.nu.functor.obj (X.obj D.auxiliary)))
  have hl : l ≫ (K.shiftedNu X e).target.hom = (K.nu X).target.hom :=
    K.shiftedNu_target X e
  have hliso : IsIso l := by
    have heq : l = (K.nu X).target.hom ≫ (K.shiftedNu X e).target.inv := by
      rw [←hl]
      simp only [Category.assoc,Iso.hom_inv_id,Category.comp_id]
    rw [heq]
    infer_instance
  letI := hliso
  apply (cancel_epi l).mp
  rw [←Category.assoc,←L.map_comp,(D.normalizedMap X Y f).factorization]
  simp only [K.nu_target] at hl ⊢
  have hn := D.recovery.nuRealizationIso.hom.naturality f
  dsimp only [Functor.comp_map,Functor.id_map] at hn
  change L.map (D.nu.functor.map f) ≫
      D.recovery.nuRealizationIso.hom.app (Y.obj D.auxiliary) = _
  rw [hn,←hl,Category.assoc]

/-- AimPaper Proposition 5.14. ClassicalDetects factors through the original
Z∞/B∞ classes; neither essentiality nor nonzero labels are required.
The printed B∞ index on Y is (s,t), although y has degree (s+n,t+n);
the typed target uses the latter degree, as recorded in corrections.yaml. -/
public theorem infiniteExtension_to_classicalExtension (R : RealizationCoordinates D)
    (hcomp : LambdaInversionAdamsComparison D R) (X Y : ClassicalObject)
    (f : X.obj D.auxiliary ⟶ Y.obj D.auxiliary) (n s t : ℤ)
    (x : permanentCycles D X (s,t)) (y : permanentCycles D Y (s+n,t+n))
    (he : InfiniteExtension D X Y f n s t x.val y.val) :
    ∃ a : HomotopyGroup (t-s) (X.obj D.auxiliary),
      ClassicalDetects (D.classicalConvergence X) (s,t) x.val a ∧
      ClassicalDetects (D.classicalConvergence Y) (s+n,t+n) y.val
        (eqToHom (congrArg (Sphere (C := C))
          (show (t+n)-(s+n) = t-s by omega)) ≫ a ≫ f) := by
  obtain ⟨W⟩ := he
  let e := normalizedExponent D.classicalTower f
  let w : ℤ := t+e
  let p : ℤ × ℤ := (t-s,w)
  let U := extensionSourceObject D X Y f
  let g := (D.normalizedMap X Y f).map
  obtain ⟨_,ar,br,hab,hax,hby⟩ :=
    (Internal.tower_extension_iff (D.convergentMap U (.nu Y) g)
      p s n W.source W.target).mp W.equation
  let beta : BiHom (t-s) w (U.obj D.nu D.auxiliary) :=
    ((D.syntheticTower.filtration (U.obj D.nu D.auxiliary)).F s p).arrow ar
  have hs := Internal.source_frame_detects (D.convergence U) p s W.source
    (infiniteSourceForExtension D X Y f s t x.val) W.source_rep ar hax
  have hsource : Detects (D.convergence U) (s,t,w)
      (regradeE2 (show (s,t,t+(e:ℤ)-(0:ℕ))=(s,t,w) by simp [w])
        (D.comparison.nuE2 X e s t 0 x.val)) beta := by
    have H := paper_detects_transport D U
      (show (s,p.1+s,p.2)=(s,t,w) by ext <;> dsimp [p] <;> omega) _ _ hs
    dsimp only [infiniteSourceForExtension] at H
    rw [paper_e2_regrade_comp,paper_homotopy_regrade_comp] at H
    exact H
  let a : HomotopyGroup (t-s) (X.obj D.auxiliary) :=
    (R.sphere (t-s) w).hom ≫ D.recovery.realization.map beta ≫
      (hcomp.shiftedNu X e).target.hom
  have hclassSource := (hcomp.shiftedNu X e).detects s t w _ beta hsource
  have ha : ClassicalDetects (D.classicalConvergence X) (s,t) x.val a := by
    rw [paper_e2Map_regrade D _ s t (t+(e:ℤ)-(0:ℕ)) w (by simp [w]),
      hcomp.shiftedNu_e2] at hclassSource
    exact hclassSource
  have ht := Internal.source_frame_detects (D.convergence (.nu Y)) p (s+n) W.target
    (infiniteTargetForExtension D X Y f n s t W.length_lower y.val) W.target_rep br hby
  have hstem : t-s = (t+n)-(s+n) := by omega
  have hindex : t-s+(s+n)=t+n := by omega
  have hweight : (t+n)-((n-(e:ℤ)).toNat:ℤ)=w := by
    rw [Int.toNat_of_nonneg (by have h := W.length_lower; dsimp [e] at *; omega)]
    dsimp [w]
    omega
  have htarget : Detects (D.convergence (.nu Y)) (s+n,t+n,w)
      (regradeE2 (show (s+n,t+n,(t+n)-((n-(e:ℤ)).toNat:ℤ))=(s+n,t+n,w) by rw [hweight])
        (targetNuLabel D Y (s+n) (t+n) (n-(e:ℤ)).toNat y.val))
      (homotopyRegrade hstem rfl (beta ≫ g)) := by
    rw [←hab] at ht
    have H := paper_detects_transport D (.nu Y)
      (show (s+n,p.1+(s+n),p.2)=(s+n,t+n,w) by ext <;> dsimp [p] <;> omega) _ _ ht
    dsimp only [infiniteTargetForExtension] at H
    rw [paper_e2_regrade_comp,paper_homotopy_regrade_comp] at H
    exact H
  have hclassTarget := (hcomp.nu Y).detects (s+n) (t+n) w _
    (homotopyRegrade hstem rfl (beta ≫ g)) htarget
  refine ⟨a,ha,?_⟩
  have htclass : ClassicalDetects (D.classicalConvergence Y) (s+n,t+n) y.val
      ((R.sphere ((t+n)-(s+n)) w).hom ≫
        D.recovery.realization.map (homotopyRegrade hstem rfl (beta ≫ g)) ≫
          (hcomp.nu Y).target.hom) := by
    rw [paper_e2Map_regrade D _ (s+n) (t+n) _ w hweight,hcomp.nu_e2] at hclassTarget
    exact hclassTarget
  convert htclass using 1
  symm
  calc
    _ = (eqToHom (congrArg (Sphere (C := C)) hstem.symm) ≫
        (R.sphere (t-s) w).hom ≫ D.recovery.realization.map (beta ≫ g)) ≫
          (hcomp.nu Y).target.hom := by
      simpa only [Category.assoc] using congrArg
        (fun z => z ≫ (hcomp.nu Y).target.hom)
        (realization_homotopy_regrade D R (t-s) ((t+n)-(s+n)) w hstem (beta ≫ g))
    _ = _ := by
      dsimp only [a,g]
      rw [Functor.map_comp]
      simp only [Category.assoc]
      rw [normalized_realization_square D R hcomp X Y f]


/-- The individual classical detection lift for Proposition 5.14 exists
without essentiality or a nonzero label. The proposition additionally needs
compatibility of ONE such lift with the given synthetic extension and f;
that comparison is not supplied by this individual existence lemma. -/
private theorem classical_detection_exists_of_permanent_label (X : ClassicalObject)
    (s t : ℤ) (x : permanentCycles D X (s,t)) :
    ∃ a : HomotopyGroup (t-s) (X.obj D.auxiliary),
      ClassicalDetects (D.classicalConvergence X) (s,t) x.val a := by
  obtain ⟨z,hz⟩ := x.property
  let F := (D.classicalTower.tower (X.obj D.auxiliary)).filtration
  let e := (((D.classical.obj (X.obj D.auxiliary)).ssData (s,t)).pageπ ⊤) z
  haveI : Epi (F.toAssociatedGraded s (t-s)) := inferInstanceAs (Epi (cokernel.π _))
  obtain ⟨b,hb⟩ := (ModuleCat.epi_iff_surjective (F.toAssociatedGraded s (t-s))).mp
    inferInstance (((D.classicalConvergence X).identification (s,t)).hom e)
  refine ⟨(F.F s (t-s)).arrow b,z,?_,b,rfl,hb.symm⟩
  have h0 : (D.classical.obj (X.obj D.auxiliary)).r₀ = 2 := D.classical.firstPage _
  apply eq_of_heq
  apply HEq.trans ?_ (heq_of_eq hz)
  have hindex : (↑(2-(D.classical.obj (X.obj D.auxiliary)).r₀).toNat : WithTop ℕ) = 0 := by
    rw [h0]; rfl
  unfold cycleLabel
  dsimp only
  have app_heq : ∀ {A B : ModuleCat.{v} ℤ} (h : A=B) (a : A),
      HEq ((eqToHom h) a) a := by
    intro A B h a
    subst B
    rfl
  change HEq _ (((eqToHom (by simp [Page,h0])) :
      ((D.classical.obj (X.obj D.auxiliary)).ssData (s,t)).page 0 ⟶
        (D.classical.obj (X.obj D.auxiliary)).Page 2 (s,t)) ((Subobject.ofLE _ _ _ ≫
    ((D.classical.obj (X.obj D.auxiliary)).ssData (s,t)).pageπ 0) z))
  apply HEq.trans ?_ (app_heq _ _).symm
  let g (k : WithTop ℕ) : (((D.classical.obj (X.obj D.auxiliary)).ssData (s,t)).page k : ModuleCat.{v} ℤ) :=
    (Subobject.ofLE _ _ (((D.classical.obj (X.obj D.auxiliary)).ssData (s,t)).Z_anti le_top) ≫
      ((D.classical.obj (X.obj D.auxiliary)).ssData (s,t)).pageπ k) z
  change HEq (g _) (g 0)
  have aux : ∀ k l : WithTop ℕ, k=l → HEq (g k) (g l) := by
    intro k l h
    subst l
    rfl
  exact aux _ _ hindex

end
end KIP126.ProofTools.Paper
