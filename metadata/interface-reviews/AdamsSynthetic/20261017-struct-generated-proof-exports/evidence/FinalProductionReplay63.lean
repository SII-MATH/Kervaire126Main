module
import Lean

public import KIP126.AdamsSynthetic.Standard.Filtration
public import KIP126.AdamsSynthetic.MappingEnrichment
public import KIP126.AdamsSynthetic.Enrichment
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.RingHom
public import KIP126.AdamsSynthetic.ESSShift
public import KIP126.AdamsSynthetic.Weight
public import KIP126.AdamsSynthetic.PageExtensions
public import KIP126.AdamsSynthetic.ConsumerOperations

/-! Fixed composition, enrichment and ESS transport. Each mathematical
operation and compatibility theorem is declared separately, then assembled
for reuse by the already proved generic operation lemmas. -/

@[expose] section
namespace KIP126.AdamsSynthetic.Standard
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open KIP126.StableHomotopy KIP126.Classical.Adams KIP126.Core.SpectralSequence
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence KIP126.Kervaire.Route
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

public abbrev FiniteSpectrum := MappingObject (IsFiniteSpectrum (C := Spectrum))

/-- Fixed MappingComposition.pairing; construction or proof deferred to its owning module. -/
public def mapping_pairing : ∀ X Y Z : MappingObject (IsFiniteSpectrum (C := Spectrum)),
    ConvergingSSPairing (mappingSystem.hom X Y).underlying (mappingSystem.hom Y Z).underlying (mappingSystem.hom X Z).underlying := by sorry

/-- Fixed MappingComposition.parity; construction or proof deferred to its owning module. -/
public theorem mapping_parity : ∀ X Y Z, (mapping_pairing X Y Z).ssPairing.parity = adamsStemParity := by sorry

/-- Fixed MappingComposition.abutment_compatible; construction or proof deferred to its owning module. -/
public theorem mapping_abutment_compatible : ∀ (X Y Z : MappingObject (IsFiniteSpectrum (C := Spectrum))) (a b : ℤ)
      (x : (mappingSystem.hom X Y).underlying.A a) (y : (mappingSystem.hom Y Z).underlying.A b),
    mappingHomotopyEquiv closedBackground (a + b) X.val Z.val ((mapping_pairing X Y Z).abutmentPair a b x y) =
      (shiftFunctorAdd Spectrum a b).hom.app X.val ≫
        (shiftFunctor Spectrum b).map (mappingHomotopyEquiv closedBackground a X.val Y.val x) ≫
        mappingHomotopyEquiv closedBackground b Y.val Z.val y := by sorry

/-- Fixed MappingComposition.page_associative; construction or proof deferred to its owning module. -/
public theorem mapping_page_associative : ∀ (W X Y Z : MappingObject (IsFiniteSpectrum (C := Spectrum))) (r : ℤ) (i j k : ℤ × ℤ)
      (x : (mappingSystem.hom W X).underlying.E.Page r i)
      (y : (mappingSystem.hom X Y).underlying.E.Page r j)
      (z : (mappingSystem.hom Y Z).underlying.E.Page r k),
    HEq ((mapping_pairing W Y Z).ssPairing.pair r (i + j) k
      ((mapping_pairing W X Y).ssPairing.pair r i j x y) z)
      ((mapping_pairing W X Z).ssPairing.pair r i (j + k) x
        ((mapping_pairing X Y Z).ssPairing.pair r j k y z)) := by sorry

/-- Fixed MappingComposition.identity; construction or proof deferred to its owning module. -/
public def mapping_identity : ∀ X : MappingObject (IsFiniteSpectrum (C := Spectrum)), ConvergingSSUnit (mappingSystem.hom X X).underlying rfl := by sorry

/-- Fixed MappingComposition.identity_actual; construction or proof deferred to its owning module. -/
public theorem mapping_identity_actual : ∀ X : MappingObject (IsFiniteSpectrum (C := Spectrum)),
    mappingHomotopyZeroEquiv closedBackground X.val X.val (mapping_identity X).abutment = 𝟙 X.val := by sorry

/-- Fixed MappingComposition.page_left_unital; construction or proof deferred to its owning module. -/
public theorem mapping_page_left_unital : ∀ (X Y : MappingObject (IsFiniteSpectrum (C := Spectrum))) (r : ℤ) (k : ℤ × ℤ)
      (x : (mappingSystem.hom X Y).underlying.E.Page r k),
    HEq ((mapping_pairing X X Y).ssPairing.pair r (0,0) k ((mapping_identity X).page r) x) x := by sorry

/-- Fixed MappingComposition.page_right_unital; construction or proof deferred to its owning module. -/
public theorem mapping_page_right_unital : ∀ (X Y : MappingObject (IsFiniteSpectrum (C := Spectrum))) (r : ℤ) (k : ℤ × ℤ)
      (x : (mappingSystem.hom X Y).underlying.E.Page r k),
    HEq ((mapping_pairing X Y Y).ssPairing.pair r k (0,0) x ((mapping_identity Y).page r)) x := by sorry

public def mappingComposition : MappingComposition mappingSystem where
  pairing := mapping_pairing
  parity := mapping_parity
  abutment_compatible := mapping_abutment_compatible
  page_associative := mapping_page_associative
  identity := mapping_identity
  identity_actual := mapping_identity_actual
  page_left_unital := mapping_page_left_unital
  page_right_unital := mapping_page_right_unital

/-- Fixed MappingEnrichment.monoidal; construction or proof deferred to its owning module. -/
@[implicit_reducible] public def mappingEnriched_monoidal : MonoidalCategory (ConvergingSequence.{0,0} ℤ) := by sorry

/-- Fixed MappingEnrichment.enriched; construction or proof deferred to its owning module. -/
@[implicit_reducible] public def mappingEnriched_enriched : @EnrichedCategory (ConvergingSequence.{0,0} ℤ) _ mappingEnriched_monoidal (MappingObject (IsFiniteSpectrum (C := Spectrum))) := by sorry

/-- Fixed MappingEnrichment.hom_eq; construction or proof deferred to its owning module. -/
public theorem mappingEnriched_hom_eq : ∀ X Y : MappingObject (IsFiniteSpectrum (C := Spectrum)), mappingEnriched_enriched.Hom X Y = mappingSystem.hom X Y := by sorry

/-- Fixed MappingEnrichment.tensorPairing; construction or proof deferred to its owning module. -/
public def mappingEnriched_tensorPairing : letI := mappingEnriched_monoidal
    ∀ X Y Z : MappingObject (IsFiniteSpectrum (C := Spectrum)),
      ConvergingSSPairing (mappingSystem.hom X Y).underlying (mappingSystem.hom Y Z).underlying
        ((mappingSystem.hom X Y ⊗ mappingSystem.hom Y Z).underlying) := by sorry

/-- Fixed MappingEnrichment.composition_page; construction or proof deferred to its owning module. -/
public theorem mappingEnriched_composition_page : letI := mappingEnriched_monoidal
    ∀ (X Y Z : MappingObject (IsFiniteSpectrum (C := Spectrum))) (r : ℤ) (i j : ℤ × ℤ)
      (x : (mappingSystem.hom X Y).underlying.E.Page r i)
      (y : (mappingSystem.hom Y Z).underlying.E.Page r j),
      let f : (mappingSystem.hom X Y ⊗ mappingSystem.hom Y Z) ⟶ mappingSystem.hom X Z :=
        eqToHom (congrArg₂ (fun A B : ConvergingSequence.{0,0} ℤ => A ⊗ B)
          (mappingEnriched_hom_eq X Y).symm (mappingEnriched_hom_eq Y Z).symm) ≫ mappingEnriched_enriched.comp X Y Z ≫
            eqToHom (mappingEnriched_hom_eq X Z)
      f.sequence.pageMap r (i+j) ((mappingEnriched_tensorPairing X Y Z).ssPairing.pair r i j x y) =
        (mappingComposition.pairing X Y Z).ssPairing.pair r i j x y := by sorry

private theorem infinityToPageAt_naturality
    {D D' : (ℤ × ℤ) → SSData (ModuleCat.{0} ℤ)}
    (g : SSDataMorphism (ℤ × ℤ) D D') (p : ℤ × ℤ)
    (n m : WithTop ℕ) (hn : n = m)
    (z : (Subobject.underlying.obj ((D p).Z ⊤) : ModuleCat ℤ)) :
    (g.pageMap p n ≫ eqToHom (congrArg (D' p).page hn))
      ((Subobject.ofLE _ _ ((D p).Z_anti (le_top : n ≤ ⊤)) ≫ (D p).pageπ n) z) =
      (Subobject.ofLE _ _ ((D' p).Z_anti (le_top : m ≤ ⊤)) ≫ (D' p).pageπ m)
        (g.cycleMap p ⊤ z) := by
  subst m
  simp only [eqToHom_refl, Category.comp_id]
  have h : (Subobject.ofLE _ _ ((D p).Z_anti (le_top : n ≤ ⊤)) ≫
      (D p).pageπ n) ≫ g.pageMap p n =
      g.cycleMap p ⊤ ≫ Subobject.ofLE _ _ ((D' p).Z_anti (le_top : n ≤ ⊤)) ≫
        (D' p).pageπ n := by
    rw [Category.assoc, g.pageπ_pageMap, ← Category.assoc,
      g.cycleMap_ofLE p (le_top : n ≤ ⊤)]
    exact Category.assoc _ _ _
  exact congrArg (fun m => m z) h

private theorem infinityToPage_naturality
    {E E' : KIP126.Core.SpectralSequence (ModuleCat.{0} ℤ) (ℤ × ℤ)}
    (f : E ⟶ E') (r : ℤ) (p : ℤ × ℤ) (z : InfiniteCycles E p) :
    f.pageMap r p (infinityToPage E r p z) =
      infinityToPage E' r p (f.toSSDataMorphism.cycleMap p ⊤ z) := by
  exact infinityToPageAt_naturality f.toSSDataMorphism p
    ↑(r - E.r₀).toNat ↑(r - E'.r₀).toNat (by rw [f.r₀_eq]) z

/-- Enriched composition agrees at E∞ by its page law on common infinite cycles. -/
public theorem mappingEnriched_composition_eInfty : letI := mappingEnriched_monoidal
    ∀ (X Y Z : MappingObject (IsFiniteSpectrum (C := Spectrum))) (i j : ℤ × ℤ)
      (x : ((mappingSystem.hom X Y).underlying.E.ssData i).eInfty)
      (y : ((mappingSystem.hom Y Z).underlying.E.ssData j).eInfty),
      let f : (mappingSystem.hom X Y ⊗ mappingSystem.hom Y Z) ⟶ mappingSystem.hom X Z :=
        eqToHom (congrArg₂ (fun A B : ConvergingSequence.{0,0} ℤ => A ⊗ B)
          (mappingEnriched_hom_eq X Y).symm (mappingEnriched_hom_eq Y Z).symm) ≫ mappingEnriched_enriched.comp X Y Z ≫
            eqToHom (mappingEnriched_hom_eq X Z)
      f.sequence.eInftyMap (i+j) ((mappingEnriched_tensorPairing X Y Z).eInftyPair i j x y) =
        (mappingComposition.pairing X Y Z).eInftyPair i j x y := by
  letI := mappingEnriched_monoidal
  intro X Y Z i j x y
  let f : (mappingSystem.hom X Y ⊗ mappingSystem.hom Y Z) ⟶ mappingSystem.hom X Z :=
    eqToHom (congrArg₂ (fun A B : ConvergingSequence.{0,0} ℤ => A ⊗ B)
      (mappingEnriched_hom_eq X Y).symm (mappingEnriched_hom_eq Y Z).symm) ≫
        mappingEnriched_enriched.comp X Y Z ≫ eqToHom (mappingEnriched_hom_eq X Z)
  let P := mappingEnriched_tensorPairing X Y Z
  let Q := mappingComposition.pairing X Y Z
  haveI : Epi (((mappingSystem.hom X Y).underlying.E.ssData i).pageπ ⊤) :=
    inferInstanceAs (Epi (cokernel.π _))
  haveI : Epi (((mappingSystem.hom Y Z).underlying.E.ssData j).pageπ ⊤) :=
    inferInstanceAs (Epi (cokernel.π _))
  obtain ⟨a, rfl⟩ := (ModuleCat.epi_iff_surjective
    (((mappingSystem.hom X Y).underlying.E.ssData i).pageπ ⊤)).mp inferInstance x
  obtain ⟨b, rfl⟩ := (ModuleCat.epi_iff_surjective
    (((mappingSystem.hom Y Z).underlying.E.ssData j).pageπ ⊤)).mp inferInstance y
  have h₀ (U V : MappingObject (IsFiniteSpectrum (C := Spectrum))) :
      (mappingSystem.hom U V).underlying.E.r₀ ≤ 2 :=
    le_of_eq (classical.firstPage _)
  have hT : (mappingSystem.hom X Y ⊗ mappingSystem.hom Y Z).underlying.E.r₀ ≤ 2 :=
    f.sequence.r₀_eq.le.trans (h₀ X Z)
  have h := mappingEnriched_composition_page X Y Z 2 i j
    (infinityToPage _ 2 i a) (infinityToPage _ 2 j b)
  change f.sequence.pageMap 2 (i+j)
      (P.ssPairing.pair 2 i j (infinityToPage _ 2 i a) (infinityToPage _ 2 j b)) =
    Q.ssPairing.pair 2 i j (infinityToPage _ 2 i a) (infinityToPage _ 2 j b) at h
  rw [P.finitePagePair_compatible 2 i j (h₀ X Y) (h₀ Y Z) hT,
    infinityToPage_naturality,
    Q.finitePagePair_compatible 2 i j (h₀ X Y) (h₀ Y Z) (h₀ X Z)] at h
  have hinf := ((mappingSystem.hom X Z).underlying.E.ssData (i+j)).infinity_projection_eq_of_page_projection_eq
    ↑(2 - (mappingSystem.hom X Z).underlying.E.r₀).toNat
    (f.sequence.toSSDataMorphism.cycleMap (i+j) ⊤ (P.cyclePairAtInfinity i j a b))
    (Q.cyclePairAtInfinity i j a b) h
  have htop := congrArg (fun m => m (P.cyclePairAtInfinity i j a b))
    (f.sequence.toSSDataMorphism.pageπ_pageMap (i+j) ⊤)
  change f.sequence.eInftyMap (i+j)
      (P.eInftyPair i j (((mappingSystem.hom X Y).underlying.E.ssData i).pageπ ⊤ a)
        (((mappingSystem.hom Y Z).underlying.E.ssData j).pageπ ⊤ b)) =
    Q.eInftyPair i j (((mappingSystem.hom X Y).underlying.E.ssData i).pageπ ⊤ a)
      (((mappingSystem.hom Y Z).underlying.E.ssData j).pageπ ⊤ b)
  rw [← P.eInftyPair_induced, ← Q.eInftyPair_induced]
  exact htop.trans hinf

/-- Fixed MappingEnrichment.composition_abutment; construction or proof deferred to its owning module. -/
public theorem mappingEnriched_composition_abutment : letI := mappingEnriched_monoidal
    ∀ (X Y Z : MappingObject (IsFiniteSpectrum (C := Spectrum))) (i j : ℤ)
      (x : (mappingSystem.hom X Y).underlying.A i) (y : (mappingSystem.hom Y Z).underlying.A j),
      let f : (mappingSystem.hom X Y ⊗ mappingSystem.hom Y Z) ⟶ mappingSystem.hom X Z :=
        eqToHom (congrArg₂ (fun A B : ConvergingSequence.{0,0} ℤ => A ⊗ B)
          (mappingEnriched_hom_eq X Y).symm (mappingEnriched_hom_eq Y Z).symm) ≫ mappingEnriched_enriched.comp X Y Z ≫
            eqToHom (mappingEnriched_hom_eq X Z)
      f.convergence.aMap (i+j) ((mappingEnriched_tensorPairing X Y Z).abutmentPair i j x y) =
        (mappingComposition.pairing X Y Z).abutmentPair i j x y := by sorry

/-- Fixed MappingEnrichment.unit_reindex; construction or proof deferred to its owning module. -/
public theorem mappingEnriched_unit_reindex : mappingEnriched_monoidal.tensorUnit.underlying.conv.reindex (0,0) = (0,0) := by sorry

/-- Fixed MappingEnrichment.unit_data; construction or proof deferred to its owning module. -/
public def mappingEnriched_unit_data : ConvergingSSUnit mappingEnriched_monoidal.tensorUnit.underlying mappingEnriched_unit_reindex := by sorry

/-- Fixed MappingEnrichment.identity_page; construction or proof deferred to its owning module. -/
public theorem mappingEnriched_identity_page : letI := mappingEnriched_monoidal
    ∀ (X : MappingObject (IsFiniteSpectrum (C := Spectrum))) (r : ℤ),
      let f : 𝟙_ (ConvergingSequence.{0,0} ℤ) ⟶ mappingSystem.hom X X :=
        mappingEnriched_enriched.id X ≫ eqToHom (mappingEnriched_hom_eq X X)
      f.sequence.pageMap r (0,0) (mappingEnriched_unit_data.page r) = (mappingComposition.identity X).page r := by sorry

/-- The enriched identity agrees at E∞ by its page law on the same infinite cycle. -/
public theorem mappingEnriched_identity_eInfty : letI := mappingEnriched_monoidal
    ∀ X : MappingObject (IsFiniteSpectrum (C := Spectrum)),
      let f : 𝟙_ (ConvergingSequence.{0,0} ℤ) ⟶ mappingSystem.hom X X :=
        mappingEnriched_enriched.id X ≫ eqToHom (mappingEnriched_hom_eq X X)
      f.sequence.eInftyMap (0,0) mappingEnriched_unit_data.eInfty = (mappingComposition.identity X).eInfty := by
  letI := mappingEnriched_monoidal
  intro X
  let f : 𝟙_ (ConvergingSequence.{0,0} ℤ) ⟶ mappingSystem.hom X X :=
    mappingEnriched_enriched.id X ≫ eqToHom (mappingEnriched_hom_eq X X)
  have h := mappingEnriched_identity_page X 2
  change f.sequence.pageMap 2 (0,0)
      (infinityToPage _ 2 (0,0) mappingEnriched_unit_data.cycle) =
    infinityToPage _ 2 (0,0) (mappingComposition.identity X).cycle at h
  rw [infinityToPage_naturality] at h
  have hinf := ((mappingSystem.hom X X).underlying.E.ssData (0,0)).infinity_projection_eq_of_page_projection_eq
      ↑(2 - (mappingSystem.hom X X).underlying.E.r₀).toNat
      (f.sequence.toSSDataMorphism.cycleMap (0,0) ⊤ mappingEnriched_unit_data.cycle)
      (mappingComposition.identity X).cycle h
  have htop := congrArg (fun m => m mappingEnriched_unit_data.cycle)
    (f.sequence.toSSDataMorphism.pageπ_pageMap (0,0) ⊤)
  exact htop.trans hinf

/-- Fixed MappingEnrichment.identity_abutment; construction or proof deferred to its owning module. -/
public theorem mappingEnriched_identity_abutment : letI := mappingEnriched_monoidal
    ∀ X : MappingObject (IsFiniteSpectrum (C := Spectrum)),
      let f : 𝟙_ (ConvergingSequence.{0,0} ℤ) ⟶ mappingSystem.hom X X :=
        mappingEnriched_enriched.id X ≫ eqToHom (mappingEnriched_hom_eq X X)
      f.convergence.aMap 0 mappingEnriched_unit_data.abutment = (mappingComposition.identity X).abutment := by sorry

public def mappingEnrichment : MappingEnrichment mappingComposition where
  monoidal := mappingEnriched_monoidal
  enriched := mappingEnriched_enriched
  hom_eq := mappingEnriched_hom_eq
  tensorPairing := mappingEnriched_tensorPairing
  composition_page := mappingEnriched_composition_page
  composition_eInfty := mappingEnriched_composition_eInfty
  composition_abutment := mappingEnriched_composition_abutment
  unit_reindex := mappingEnriched_unit_reindex
  unit_data := mappingEnriched_unit_data
  identity_page := mappingEnriched_identity_page
  identity_eInfty := mappingEnriched_identity_eInfty
  identity_abutment := mappingEnriched_identity_abutment

/-- Fixed GradedLambdaEnrichment.coherence; construction or proof deferred to its owning module. -/
public theorem biShift_associativity : ∀ (a b c ab bc total : ℤ × ℤ)
      (hab : a + b = ab) (hbc : b + c = bc)
      (habc : ab + c = total) (habc' : a + bc = total) (X : SyntheticSpectrum),
    (SyntheticCategory.biShift c).map ((biShiftAddIso a b ab hab).hom.app X) ≫
        (biShiftAddIso ab c total habc).hom.app X =
      (biShiftAddIso b c bc hbc).hom.app ((SyntheticCategory.biShift a).obj X) ≫
        (biShiftAddIso a bc total habc').hom.app X := quotients.coherence.associativity

public theorem biShift_left_unit : ∀ (a : ℤ × ℤ) (X : SyntheticSpectrum),
    (biShiftAddIso 0 a a (zero_add a)).hom.app X =
      (SyntheticCategory.biShift a).map (SyntheticCategory.biShift_zero.hom.app X) := quotients.coherence.left_unit

public theorem biShift_right_unit : ∀ (a : ℤ × ℤ) (X : SyntheticSpectrum),
    (biShiftAddIso a 0 a (add_zero a)).hom.app X =
      SyntheticCategory.biShift_zero.hom.app ((SyntheticCategory.biShift a).obj X) := quotients.coherence.right_unit

public theorem biShift_lambda_comm : ∀ (a : ℤ × ℤ) (X : SyntheticSpectrum),
    SyntheticCategory.lam.app ((SyntheticCategory.biShift a).obj X) =
      (biShiftAddIso a (0, -1) (a + (0, -1)) rfl).hom.app X ≫
        (biShiftAddIso (0, -1) a (a + (0, -1)) (add_comm _ _)).inv.app X ≫
        (SyntheticCategory.biShift a).map (SyntheticCategory.lam.app X) := quotients.coherence.lambda_comm

public theorem graded_coherence : BiShiftCoherence SyntheticSpectrum := quotients.coherence

/-- Fixed GradedLambdaEnrichment.shiftAdditive; construction or proof deferred to its owning module. -/
public theorem graded_shiftAdditive : ∀ p : ℤ × ℤ, (SyntheticCategory.biShift p : SyntheticSpectrum ⥤ SyntheticSpectrum).Additive := exactness.shiftAdditive

/-! The total λ map is the direct-sum extension of actual precomposition.
The polynomial action evaluates at this same map, with no new graded object. -/

private def totalLambda (X Y : SyntheticSpectrum) :
    TotalWeightHom X Y →ₗ[ℤ] TotalWeightHom X Y :=
  (DirectSum.toAddMonoid fun w =>
    (weightHomInclusion (w-1)).comp
      (Preadditive.leftComp Y
        (weightHomLambda (X := X) (𝟙 ((SyntheticCategory.biShift (0,w)).obj X))))).toIntLinearMap

private theorem totalLambda_of (X Y : SyntheticSpectrum) (w : ℤ) (f : WeightHom X Y w) :
    totalLambda X Y (weightHomInclusion w f) =
      weightHomInclusion (w-1) (weightHomLambda f) := by
  change DirectSum.toAddMonoid
    (fun v : ℤ => (DirectSum.of (WeightHom X Y) (v-1)).comp
      (Preadditive.leftComp Y
        (weightHomLambda (X := X) (𝟙 ((SyntheticCategory.biShift (0,v)).obj X)))))
    (DirectSum.of (WeightHom X Y) w f) =
      DirectSum.of (WeightHom X Y) (w-1) (weightHomLambda f)
  rw [DirectSum.toAddMonoid_of]
  change DirectSum.of (WeightHom X Y) (w-1)
      ((weightHomLambda (X := X) (𝟙 ((SyntheticCategory.biShift (0,w)).obj X))) ≫ f) =
    DirectSum.of (WeightHom X Y) (w-1) (weightHomLambda f)
  apply congrArg (DirectSum.of (WeightHom X Y) (w-1))
  dsimp only [weightHomLambda, Functor.id_obj, Functor.comp_obj]
  rw [Category.comp_id, Category.assoc]

/-- The polynomial action obtained by evaluating X at actual graded λ. -/
@[implicit_reducible] public def graded_module : ∀ X Y : SyntheticSpectrum, Module (Polynomial ℤ) (TotalWeightHom X Y) := by
  intro X Y
  exact
    (fun (M : Type) [AddCommGroup M] (D : M →+ M) =>
      let A := Module.End ℤ M
      letI : Ring A := inferInstance
      let ring : NonAssocRing A := inferInstance
      letI : Module A M := inferInstance
      let L : A := D.toIntLinearMap
      let hom : Polynomial ℤ →+* A :=
        Polynomial.eval₂RingHom' (Int.castRingHom A) L
          (fun a => @Int.cast_commute A ring a L)
      Module.compHom M hom)
      (TotalWeightHom X Y)
      (DirectSum.toAddMonoid fun w =>
        (weightHomInclusion (w-1)).comp
          (Preadditive.leftComp Y
            (weightHomLambda (X := X) (𝟙 ((SyntheticCategory.biShift (0,w)).obj X)))))


/-- The polynomial generator acts by the specified degree-lowering λ map. -/
public theorem graded_lambda_smul : ∀ (X Y : SyntheticSpectrum) (w : ℤ) (f : WeightHom X Y w),
    letI := graded_module X Y
    (Polynomial.X : Polynomial ℤ) • weightHomInclusion w f =
      weightHomInclusion (w-1) (weightHomLambda f) := by
  intro X Y w f
  letI := graded_module X Y
  change (Polynomial.eval₂ (Int.castRingHom _) (totalLambda X Y) Polynomial.X) _ = _
  rw [Polynomial.eval₂_X]
  exact totalLambda_of X Y w f

/-- Fixed GradedLambdaEnrichment.compose; construction or proof deferred to its owning module. -/
public def graded_compose : ∀ X Y Z : SyntheticSpectrum,
    letI := graded_module X Y
    letI := graded_module Y Z
    letI := graded_module X Z
    TotalWeightHom Y Z →ₗ[Polynomial ℤ]
      TotalWeightHom X Y →ₗ[Polynomial ℤ] TotalWeightHom X Z := by sorry

/-- Fixed GradedLambdaEnrichment.compose_homogeneous; construction or proof deferred to its owning module. -/
public theorem graded_compose_homogeneous : ∀ (X Y Z : SyntheticSpectrum) (a b : ℤ)
      (f : WeightHom X Y a) (g : WeightHom Y Z b),
    graded_compose X Y Z (weightHomInclusion b g) (weightHomInclusion a f) =
      weightHomInclusion (a+b) (weightHomComp f g) := by sorry

public def gradedEnrichment : GradedLambdaEnrichment SyntheticSpectrum where
  coherence := graded_coherence
  shiftAdditive := graded_shiftAdditive
  module := graded_module
  lambda_smul := graded_lambda_smul
  compose := graded_compose
  compose_homogeneous := graded_compose_homogeneous

/-- Fixed NuInfinityWeightMaps.map; construction or proof deferred to its owning module. -/
public def weight_map : ∀ (X : ClassicalObject) (s t w₁ w₂ : ℤ) (_hw : w₁ ≤ w₂) (_ht : w₂ ≤ t),
    ((model.family.obj (model.nu.functor.obj (X.obj model.auxiliary))).sequence.ssData (s,t,w₂)).eInfty ⟶
      ((model.family.obj (model.nu.functor.obj (X.obj model.auxiliary))).sequence.ssData (s,t,w₁)).eInfty := by sorry

/-- Fixed NuInfinityWeightMaps.map_self; construction or proof deferred to its owning module. -/
public theorem weight_map_self : ∀ (X : ClassicalObject) (s t w : ℤ) (hw : w ≤ t),
    weight_map X s t w w le_rfl hw = 𝟙 _ := by sorry

/-- Fixed NuInfinityWeightMaps.map_comp; construction or proof deferred to its owning module. -/
public theorem weight_map_comp : ∀ (X : ClassicalObject) (s t w₁ w₂ w₃ : ℤ)
      (h₁₂ : w₁ ≤ w₂) (h₂₃ : w₂ ≤ w₃) (h₃ : w₃ ≤ t),
    weight_map X s t w₂ w₃ h₂₃ h₃ ≫ weight_map X s t w₁ w₂ h₁₂ (h₂₃.trans h₃) =
      weight_map X s t w₁ w₃ (h₁₂.trans h₂₃) h₃ := by sorry

/-- Fixed NuInfinityWeightMaps.naturality; construction or proof deferred to its owning module. -/
public theorem weight_naturality : ∀ (X Y : ClassicalObject) (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
      (s t w₁ w₂ : ℤ) (hw : w₁ ≤ w₂) (ht : w₂ ≤ t),
    (model.family.map (model.nu.functor.map f)).eInftyMap (s,t,w₂) ≫ weight_map Y s t w₁ w₂ hw ht =
      weight_map X s t w₁ w₂ hw ht ≫ (model.family.map (model.nu.functor.map f)).eInftyMap (s,t,w₁) := by sorry

/-- Fixed NuInfinityWeightMaps.representative; construction or proof deferred to its owning module. -/
public theorem weight_representative : ∀ (X : ClassicalObject) (s t w₁ w₂ : ℤ)
      (hw : w₁ ≤ w₂) (ht : w₂ ≤ t)
      (x : (model.classical.obj (X.obj model.auxiliary)).Page 2 (s,t))
      (z : ((model.family.obj (model.nu.functor.obj (X.obj model.auxiliary))).sequence.ssData (s,t,w₂)).eInfty),
    HasInfinityRepresentative _ 2 (s,t,w₂) (nuWeightLabel model X s t w₂ ht x) z →
      HasInfinityRepresentative _ 2 (s,t,w₁) (nuWeightLabel model X s t w₁ (hw.trans ht) x)
        (weight_map X s t w₁ w₂ hw ht z) := by sorry

public def weightMaps : NuInfinityWeightMaps model where
  map := weight_map
  map_self := weight_map_self
  map_comp := weight_map_comp
  naturality := weight_naturality
  representative := weight_representative

public def shift_filtered (δ : ℤ × ℤ) : ∀ (X : SyntheticObject) (p : ℤ × ℤ),
    FilteredPieceIso (model.convergence X).filtration
      (model.convergence (.shift δ X)).filtration p (p+δ) := by sorry

public theorem shift_ambient_eq (δ : ℤ × ℤ) : ∀ (X : SyntheticObject) (p : ℤ × ℤ)
      (a : BiHom p.1 p.2 (X.obj model.nu model.auxiliary)),
    ((shift_filtered δ) X p).ambient.hom a = shiftHomotopyClass δ p a := by sorry

public def shift_page (δ : ℤ × ℤ) : ∀ (X : SyntheticObject) (r : ℤ) (_hr : 2 ≤ r) (p : ℤ × ℤ) (s : ℤ),
    (model.family.obj (X.obj model.nu model.auxiliary)).Page r (s,p.1+s,p.2) ≅
      (model.family.obj ((SyntheticObject.shift δ X).obj model.nu model.auxiliary)).Page r
        (s,(p+δ).1+s,(p+δ).2) := by sorry

public theorem shift_representative_iff (δ : ℤ × ℤ) : ∀ (X : SyntheticObject) (r : ℤ) (hr : 2 ≤ r)
      (p : ℤ × ℤ) (s : ℤ)
      (x : (model.family.obj (X.obj model.nu model.auxiliary)).Page r (s,p.1+s,p.2))
      (z : ((model.family.obj (X.obj model.nu model.auxiliary)).sequence.ssData (s,p.1+s,p.2)).eInfty),
    HasInfinityRepresentative _ r (s,p.1+s,p.2) x z ↔
      HasInfinityRepresentative _ r (s,(p+δ).1+s,(p+δ).2)
        (((shift_page δ) X r hr p s).hom x)
        ((towerInfinityIso (model.convergence X) (model.convergence (.shift δ X))
          ((shift_filtered δ) X p) s).hom z) := by sorry

public def essShift (δ : ℤ × ℤ) : SyntheticESSShiftComparison model δ where
  filtered := shift_filtered δ
  ambient_eq := shift_ambient_eq δ
  page := shift_page δ
  representative_iff := shift_representative_iff δ

public def essShiftSystem : SyntheticAdamsESSShiftSystem model := ⟨fun n => essShift (1,-(n:ℤ))⟩


/-- The fixed mapping-sphere multiplication is the already selected sphere E₂ product. -/
public theorem mapping_sphere_product (p q : ℤ × ℤ)
    (x : (mappingSystem.hom ⟨SphereSpectrum, IsFiniteSpectrum.sphere⟩
      ⟨SphereSpectrum, IsFiniteSpectrum.sphere⟩).underlying.E.Page 2 p)
    (y : (mappingSystem.hom ⟨SphereSpectrum, IsFiniteSpectrum.sphere⟩
      ⟨SphereSpectrum, IsFiniteSpectrum.sphere⟩).underlying.E.Page 2 q) :
    (sphereMappingAdamsIso closedBackground classical).hom.pageMap 2 (p + q)
      ((mapping_pairing ⟨SphereSpectrum, IsFiniteSpectrum.sphere⟩
        ⟨SphereSpectrum, IsFiniteSpectrum.sphere⟩
        ⟨SphereSpectrum, IsFiniteSpectrum.sphere⟩).ssPairing.pair 2 p q x y) =
      sphereAlgebra.product p q
        ((sphereMappingAdamsIso closedBackground classical).hom.pageMap 2 p x)
        ((sphereMappingAdamsIso closedBackground classical).hom.pageMap 2 q y) := by sorry

public theorem mapping_sphere_unit :
    (sphereMappingAdamsIso closedBackground classical).hom.pageMap 2 (0,0)
      ((mapping_identity ⟨SphereSpectrum, IsFiniteSpectrum.sphere⟩).page 2) =
        sphereAlgebra.unit := by sorry

public theorem graded_associative (W X Y Z : SyntheticSpectrum)
    (f : TotalWeightHom W X) (g : TotalWeightHom X Y) (h : TotalWeightHom Y Z) :
    graded_compose W Y Z h (graded_compose W X Y g f) =
      graded_compose W X Z (graded_compose X Y Z h g) f :=
  gradedEnrichment.assoc W X Y Z f g h

public theorem graded_left_unit (X Y : SyntheticSpectrum) (f : TotalWeightHom X Y) :
    graded_compose X Y Y
      (weightHomInclusion 0 (SyntheticCategory.biShift_zero.hom.app Y)) f = f :=
  gradedEnrichment.left_unit X Y f

public theorem graded_right_unit (X Y : SyntheticSpectrum) (f : TotalWeightHom X Y) :
    graded_compose X X Y f
      (weightHomInclusion 0 (SyntheticCategory.biShift_zero.hom.app X)) = f :=
  gradedEnrichment.right_unit X Y f

end
end KIP126.AdamsSynthetic.Standard

open Lean Elab Command
set_option maxHeartbeats 0
set_option pp.universes true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.deepTerms true
run_cmd do
  let env ← getEnv
  let exported := env.setExporting true
  let mut rows : Array Json := #[]
  for (n, ci) in env.constants.toList do
    if (`KIP126.AdamsSynthetic.Standard.graded_module).isPrefixOf n || (`KIP126.AdamsSynthetic.Standard.graded_compose).isPrefixOf n || n == `KIP126.AdamsSynthetic.Standard.graded_lambda_smul || n == `KIP126.AdamsSynthetic.Standard.graded_compose_homogeneous then
      unless !isPrivateName n && (exported.find? n).isSome do continue
      let ty ← liftTermElabM <| Meta.ppExpr ci.type
      let axioms ← collectAxioms n
      rows := rows.push <| Json.mkObj [
        ("name", toJson n.toString), ("full_type", toJson ty.pretty),
        ("raw_kernel_type", toJson (toString ci.type)),
        ("universes", toJson (ci.levelParams.map Name.toString)),
        ("type_fingerprint", toJson (toString (hash (toString ci.type)))),
        ("direct_sorry", toJson (ci.type.hasSorry || (ci.value? (allowOpaque := true)).any (·.hasSorry))),
        ("axioms", toJson (axioms.map Name.toString))]
  liftIO <| IO.FS.writeFile "/inspire/hdd/global_user/czxs25250150/Kervaire126Main/metadata/interface-reviews/AdamsSynthetic/20261017-struct-generated-proof-exports/evidence/FinalProductionReplay63.json" (Json.arr rows).pretty
  logInfo m!"reporter capture count={rows.size}"
