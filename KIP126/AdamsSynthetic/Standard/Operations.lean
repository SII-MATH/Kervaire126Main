module

public import KIP126.AdamsSynthetic.Standard.Filtration
import all KIP126.AdamsSynthetic.Standard.Background
public import KIP126.AdamsSynthetic.MappingEnrichment
public import KIP126.AdamsSynthetic.Enrichment
import all KIP126.AdamsSynthetic.Enrichment
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.RingHom
public import KIP126.AdamsSynthetic.ESSShift
public import KIP126.AdamsSynthetic.Weight
public import KIP126.AdamsSynthetic.PageExtensions
public import KIP126.AdamsSynthetic.ConsumerOperations
import KIP126.SpectralSequence.FinitePageCalculus.Proofs

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

private theorem pageSubsingletonOfAmbient
    (D : SSData (ModuleCat.{0} ℤ)) (r : WithTop ℕ) [Subsingleton D.V] :
    Subsingleton (D.page r) := by
  have hV : IsZero D.V := ModuleCat.isZero_of_subsingleton D.V
  have hZ : IsZero (Subobject.underlying.obj (D.Z r)) :=
    IsZero.of_mono (D.Z r).arrow hV
  letI : Epi (D.pageπ r) := coequalizer.π_epi
  exact ModuleCat.subsingleton_of_isZero (IsZero.of_epi (D.pageπ r) hZ)

private theorem classicalPageNegativeGeneral (M : Spectrum) (r s t : ℤ)
    (hs : s < 0) : Subsingleton ((classical.obj M).Page r (s,t)) := by
  let T := classicalTower.tower M
  have hi (a b : ℕ) (hab : a ≤ b) (h : a = b) : IsIso (T.map hab) := by
    subst b
    rw [T.map_self]
    infer_instance
  let f := T.mapAt (show s ≤ s+1 by omega)
  haveI : IsIso f := hi s.toNat (s+1).toNat (by omega) (by omega)
  have hLayer : IsZero (T.layer s) :=
    Pretriangulated.Triangle.isZero₃_of_isIso₁
      (Pretriangulated.Triangle.mk f (HasFunctorialCofiber.cofibι f)
        (HasFunctorialCofiber.cofibδ f))
      (HasFunctorialCofiber.cofib_distinguished f) (show IsIso f from inferInstance)
  letI : Subsingleton (T.FirstPage (s,t)) := ⟨fun a b => hLayer.eq_of_tgt a b⟩
  let D := (classical.obj M).ssData (s,t)
  letI : Subsingleton D.V :=
    (classicalTower.sequence M).ambient (s,t) |>.toLinearEquiv.injective.subsingleton
  exact pageSubsingletonOfAmbient D _

private theorem boundariesAtZeroStable (M : Spectrum) :
    ((classical.obj M).ssData (0,0)).B ⊤ = ((classical.obj M).ssData (0,0)).B 0 := by
  have h := boundaries_top_eq_of_d_eq_zero (classical.obj M) 2
    (le_of_eq (classical.firstPage M)) (0,0) ?_
  · simpa only [classical.firstPage, sub_self, Int.toNat_zero, Nat.cast_zero] using h
  intro r hr
  have hs : (((0 : ℤ), (0 : ℤ)) - (classical.obj M).diffDeg r).1 < 0 := by
    rw [classical.differentialDegree]
    dsimp
    omega
  letI := classicalPageNegativeGeneral M r
    (((0 : ℤ), (0 : ℤ)) - (classical.obj M).diffDeg r).1
    (((0 : ℤ), (0 : ℤ)) - (classical.obj M).diffDeg r).2 hs
  ext a
  have ha : a = 0 := Subsingleton.elim _ _
  simp only [ha, map_zero]

private theorem zeroInfinityEqDeterminesAllPages (M : Spectrum) (r : ℤ)
    (z z' : InfiniteCycles (classical.obj M) (0,0))
    (h : ((classical.obj M).ssData (0,0)).pageπ ⊤ z =
      ((classical.obj M).ssData (0,0)).pageπ ⊤ z') :
    infinityToPage (classical.obj M) r (0,0) z =
      infinityToPage (classical.obj M) r (0,0) z' := by
  let D := (classical.obj M).ssData (0,0)
  let n : WithTop ℕ := ↑(r-(classical.obj M).r₀).toNat
  have hB : D.B ⊤ = D.B n :=
    le_antisymm ((boundariesAtZeroStable M).le.trans (D.B_mono (show 0 ≤ n from zero_le)))
      (D.B_mono le_top)
  exact FinitePageCalculus.same_boundaries_projection_eq D n ⊤ le_top hB z z' h

set_option backward.privateInPublic true in
private def mappingIdentityWitness
    (X : MappingObject (IsFiniteSpectrum (C := Spectrum))) :
    { U : ConvergingSSUnit (mappingSystem.hom X X).underlying rfl //
      mappingHomotopyZeroEquiv closedBackground X.val X.val U.abutment = 𝟙 X.val } := by
  classical
  apply Classical.choice
  let M := mappingSpectrum closedBackground X.val X.val
  let T := classicalTower.tower M
  let c := mappingConvergence X.val X.val X.property X.property
  let a := (mappingHomotopyZeroEquiv closedBackground X.val X.val).symm (𝟙 X.val)
  have ha : a ∈ T.filtrationSubmodule 0 0 := by
    refine ⟨a ≫ T.zeroIso.inv, ?_⟩
    change (a ≫ T.zeroIso.inv) ≫ T.projection 0 = a
    have hproj : T.projection 0 = T.zeroIso.hom := by
      change T.map (Nat.zero_le 0) ≫ T.zeroIso.hom = T.zeroIso.hom
      rw [T.map_self, Category.id_comp]
    rw [hproj, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hmem : a ∈ ModuleCat.subobjectModule _ (T.filtration.F 0 0) := by
    simpa only [AbstractAdamsTower.filtration, OrderIso.apply_symm_apply] using ha
  change ∃ b, (T.filtration.F 0 0).arrow.hom b = a at hmem
  obtain ⟨b, hb⟩ := hmem
  let e := (c.identification (0,0)).inv (T.filtration.toAssociatedGraded 0 0 b)
  haveI : Epi (((classical.obj M).ssData (0,0)).pageπ ⊤) :=
    inferInstanceAs (Epi (cokernel.π _))
  obtain ⟨z, hz⟩ := (ModuleCat.epi_iff_surjective
    (((classical.obj M).ssData (0,0)).pageπ ⊤)).mp inferInstance e
  let U : ConvergingSSUnit (mappingSystem.hom X X).underlying rfl :=
    { cycle := z
      filtered := b
      compatible := by
        change T.filtration.transportGraded rfl
          ((c.identification (0,0)).hom (((classical.obj M).ssData (0,0)).pageπ ⊤ z)) =
          T.filtration.toAssociatedGraded 0 0 b
        rw [Filtration.transportGraded_self, ModuleCat.id_apply, hz]
        change ((c.identification (0,0)).inv ≫ (c.identification (0,0)).hom) _ = _
        rw [Iso.inv_hom_id]
        rfl }
  refine ⟨⟨U, ?_⟩⟩
  change mappingHomotopyZeroEquiv closedBackground X.val X.val
    ((T.filtration.F 0 0).arrow b) = 𝟙 X.val
  rw [hb]
  exact (mappingHomotopyZeroEquiv closedBackground X.val X.val).apply_symm_apply _

set_option backward.privateInPublic true in
/-- The fixed mapping identity, with one common infinite cycle and the actual identity abutment. -/
public def mapping_identity :
    ∀ X : MappingObject (IsFiniteSpectrum (C := Spectrum)),
      ConvergingSSUnit (mappingSystem.hom X X).underlying rfl :=
  fun X => (mappingIdentityWitness X).val

/-- The fixed mapping identity abuts to the actual identity morphism. -/
public theorem mapping_identity_actual :
    ∀ X : MappingObject (IsFiniteSpectrum (C := Spectrum)),
      mappingHomotopyZeroEquiv closedBackground X.val X.val
        (mapping_identity X).abutment = 𝟙 X.val :=
  fun X => (mappingIdentityWitness X).property

private theorem actualIdentityDeterminesPages
    (X : MappingObject (IsFiniteSpectrum (C := Spectrum)))
    (U V : ConvergingSSUnit (mappingSystem.hom X X).underlying rfl)
    (hU : mappingHomotopyZeroEquiv closedBackground X.val X.val U.abutment = 𝟙 X.val)
    (hV : mappingHomotopyZeroEquiv closedBackground X.val X.val V.abutment = 𝟙 X.val)
    (r : ℤ) : U.page r = V.page r := by
  let F := (mappingSystem.hom X X).underlying.F
  have hf : U.filtered = V.filtered := by
    apply (ModuleCat.mono_iff_injective (F.F 0 0).arrow).mp inferInstance
    apply (mappingHomotopyZeroEquiv closedBackground X.val X.val).injective
    exact hU.trans hV.symm
  have hu := U.compatible
  have hv := V.compatible
  simp only [Filtration.transportGraded_self] at hu hv
  have he : U.eInfty = V.eInfty := by
    apply ((mappingSystem.hom X X).underlying.conv.iso (0,0)).toLinearEquiv.injective
    exact hu.trans ((congrArg (F.toAssociatedGraded 0 0) hf).trans hv.symm)
  exact zeroInfinityEqDeterminesAllPages
    (mappingSpectrum closedBackground X.val X.val) r U.cycle V.cycle he

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

/-- The enriched identity fixes the mapping system degree at the unit. -/
public theorem mappingEnriched_unit_reindex : mappingEnriched_monoidal.tensorUnit.underlying.conv.reindex (0,0) = (0,0) := by
  letI := mappingEnriched_monoidal
  let X : MappingObject (IsFiniteSpectrum (C := Spectrum)) :=
    ⟨SphereSpectrum, IsFiniteSpectrum.sphere⟩
  let f : 𝟙_ (ConvergingSequence.{0,0} ℤ) ⟶ mappingSystem.hom X X :=
    mappingEnriched_enriched.id X ≫ eqToHom (mappingEnriched_hom_eq X X)
  exact congrFun f.convergence.reindex_eq (0,0)


/-- Fixed MappingEnrichment.unit_data; construction or proof deferred to its owning module. -/
public def mappingEnriched_unit_data : ConvergingSSUnit mappingEnriched_monoidal.tensorUnit.underlying mappingEnriched_unit_reindex := by sorry

/-- Fixed MappingEnrichment.identity_abutment; construction or proof deferred to its owning module. -/
public theorem mappingEnriched_identity_abutment : letI := mappingEnriched_monoidal
    ∀ X : MappingObject (IsFiniteSpectrum (C := Spectrum)),
      let f : 𝟙_ (ConvergingSequence.{0,0} ℤ) ⟶ mappingSystem.hom X X :=
        mappingEnriched_enriched.id X ≫ eqToHom (mappingEnriched_hom_eq X X)
      f.convergence.aMap 0 mappingEnriched_unit_data.abutment = (mappingComposition.identity X).abutment := by sorry

private theorem inducedAssocGradedMapTransport
    {A₁ A₂ : ℤ → ModuleCat.{0} ℤ}
    {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    (aMap : ∀ k, A₁ k ⟶ A₂ k)
    (hcompat : ∀ s k, ∃ φ : FiltrationPiece F₁ s k ⟶ FiltrationPiece F₂ s k,
      φ ≫ (F₂.F s k).arrow = (F₁.F s k).arrow ≫ aMap k)
    {p q : ℤ × ℤ} (hpq : p = q) :
    Filtration.inducedAssocGradedMap aMap hcompat p.1 p.2 ≫ F₂.transportGraded hpq =
      F₁.transportGraded hpq ≫ Filtration.inducedAssocGradedMap aMap hcompat q.1 q.2 := by
  subst q
  simp only [Filtration.transportGraded_self, Category.comp_id, Category.id_comp]

private theorem unitMorphismInfinity
    (X : MappingObject (IsFiniteSpectrum (C := Spectrum)))
    {A : ConvergingSequence.{0,0} ℤ}
    (hA : A.underlying.conv.reindex (0,0) = (0,0))
    (U : ConvergingSSUnit A.underlying hA)
    (V : ConvergingSSUnit (mappingSystem.hom X X).underlying rfl)
    (f : A ⟶ mappingSystem.hom X X)
    (hab : f.convergence.aMap 0 U.abutment = V.abutment) :
    f.sequence.eInftyMap (0,0) U.eInfty = V.eInfty := by
  let Fs := A.underlying.F
  let Ft := (mappingSystem.hom X X).underlying.F
  let g := f.convergence
  let hc := g.filtration_compat 0 0
  have hb : hc.choose U.filtered = V.filtered := by
    apply (ModuleCat.mono_iff_injective (Ft.F 0 0).arrow).mp inferInstance
    have hm := ConcreteCategory.congr_hom hc.choose_spec U.filtered
    exact hm.trans hab
  have hm := g.iso_compat (0,0)
  have hm' := congrArg (fun k => k ≫ Ft.transportGraded hA) hm
  change (g.eMap (0,0) ≫ ((mappingSystem.hom X X).underlying.conv.iso (0,0)).hom ≫
      Ft.transportGraded hA.symm) ≫ Ft.transportGraded hA =
    ((A.underlying.conv.iso (0,0)).hom ≫
      Filtration.inducedAssocGradedMap g.aMap g.filtration_compat
        (A.underlying.conv.reindex (0,0)).1 (A.underlying.conv.reindex (0,0)).2) ≫
          Ft.transportGraded hA at hm'
  simp only [Category.assoc, Filtration.transportGraded_trans,
    Filtration.transportGraded_self] at hm'
  rw [inducedAssocGradedMapTransport g.aMap g.filtration_compat hA] at hm'
  have he := ConcreteCategory.congr_hom hm' U.eInfty
  change ((mappingSystem.hom X X).underlying.conv.iso (0,0)).hom (g.eMap (0,0) U.eInfty) =
    Filtration.inducedAssocGradedMap g.aMap g.filtration_compat 0 0
      (Fs.transportGraded hA ((A.underlying.conv.iso (0,0)).hom U.eInfty)) at he
  have hu : Fs.transportGraded hA ((A.underlying.conv.iso (0,0)).hom U.eInfty) =
      Fs.toAssociatedGraded 0 0 U.filtered := U.compatible
  have he₁ := he.trans
    (congrArg (Filtration.inducedAssocGradedMap g.aMap g.filtration_compat 0 0) hu)
  have hq : Fs.toAssociatedGraded 0 0 ≫
      Filtration.inducedAssocGradedMap g.aMap g.filtration_compat 0 0 =
        hc.choose ≫ Ft.toAssociatedGraded 0 0 := by
    exact cokernel.π_desc _ _ _
  have he' := he₁.trans (ConcreteCategory.congr_hom hq U.filtered)
  have he'' := he'.trans (congrArg (Ft.toAssociatedGraded 0 0) hb)
  have hv := V.compatible
  simp only [Filtration.transportGraded_self] at hv
  apply ((mappingSystem.hom X X).underlying.conv.iso (0,0)).toLinearEquiv.injective
  rw [← f.eInfty_compatible]
  exact he''.trans hv.symm

/-- The enriched identity has the specified representative on every page. -/
public theorem mappingEnriched_identity_page : letI := mappingEnriched_monoidal
    ∀ (X : MappingObject (IsFiniteSpectrum (C := Spectrum))) (r : ℤ),
      let f : 𝟙_ (ConvergingSequence.{0,0} ℤ) ⟶ mappingSystem.hom X X :=
        mappingEnriched_enriched.id X ≫ eqToHom (mappingEnriched_hom_eq X X)
      f.sequence.pageMap r (0,0) (mappingEnriched_unit_data.page r) = (mappingComposition.identity X).page r := by
  letI := mappingEnriched_monoidal
  intro X r
  let f : 𝟙_ (ConvergingSequence.{0,0} ℤ) ⟶ mappingSystem.hom X X :=
    mappingEnriched_enriched.id X ≫ eqToHom (mappingEnriched_hom_eq X X)
  have hi := unitMorphismInfinity X mappingEnriched_unit_reindex
    mappingEnriched_unit_data (mappingComposition.identity X) f
    (mappingEnriched_identity_abutment X)
  have htop := congrArg (fun m => m mappingEnriched_unit_data.cycle)
    (f.sequence.toSSDataMorphism.pageπ_pageMap (0,0) ⊤)
  change f.sequence.pageMap r (0,0)
    (infinityToPage _ r (0,0) mappingEnriched_unit_data.cycle) =
      infinityToPage _ r (0,0) (mappingComposition.identity X).cycle
  rw [infinityToPage_naturality]
  exact zeroInfinityEqDeterminesAllPages
    (mappingSpectrum closedBackground X.val X.val) r _ _ (htop.symm.trans hi)


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

/-- Preserve the previously exported commutation witness at its original name and type. -/
public theorem graded_compose._proof_1 (X Z : SyntheticSpectrum) :
    @SMulCommClass (Polynomial ℤ) (Polynomial ℤ) (TotalWeightHom X Z)
      (@SemigroupAction.toSMul _ _ (@Monoid.toSemigroup (Polynomial ℤ) (@CommMonoid.toMonoid (Polynomial ℤ) (@CommRing.toCommMonoid (Polynomial ℤ) (@Polynomial.commRing ℤ Int.instCommRing)))) (@MulAction.toSemigroupAction _ _ (@CommMonoid.toMonoid (Polynomial ℤ) (@CommRing.toCommMonoid (Polynomial ℤ) (@Polynomial.commRing ℤ Int.instCommRing)))
        (@DistribMulAction.toMulAction _ _ (@CommMonoid.toMonoid (Polynomial ℤ) (@CommRing.toCommMonoid (Polynomial ℤ) (@Polynomial.commRing ℤ Int.instCommRing))) _ (@Module.toDistribMulAction _ _ _ _ (graded_module X Z)))))
      (@SemigroupAction.toSMul _ _ (@Monoid.toSemigroup (Polynomial ℤ) (@CommMonoid.toMonoid (Polynomial ℤ) (@CommRing.toCommMonoid (Polynomial ℤ) (@Polynomial.commRing ℤ Int.instCommRing)))) (@MulAction.toSemigroupAction _ _ (@CommMonoid.toMonoid (Polynomial ℤ) (@CommRing.toCommMonoid (Polynomial ℤ) (@Polynomial.commRing ℤ Int.instCommRing)))
        (@DistribMulAction.toMulAction _ _ (@CommMonoid.toMonoid (Polynomial ℤ) (@CommRing.toCommMonoid (Polynomial ℤ) (@Polynomial.commRing ℤ Int.instCommRing))) _ (@Module.toDistribMulAction _ _ _ _ (graded_module X Z))))) := by
  letI := graded_module X Z
  exact smulCommClass_self _ _

private def totalComp (X Y Z : SyntheticSpectrum) :
    TotalWeightHom Y Z →+ (TotalWeightHom X Y →+ TotalWeightHom X Z) := by
  letI : ∀ p : ℤ × ℤ,
      (SyntheticCategory.biShift p : SyntheticSpectrum ⥤ SyntheticSpectrum).Additive :=
    exactness.shiftAdditive
  exact DirectSum.toAddMonoid fun b =>
    { toFun := fun g => DirectSum.toAddMonoid fun a =>
        { toFun := fun f => weightHomInclusion (a+b) (weightHomComp f g)
          map_zero' := by
            dsimp only [weightHomComp]
            rw [Functor.map_zero, Limits.zero_comp, Limits.comp_zero, map_zero]
          map_add' := by
            intro f f'
            dsimp only [weightHomComp]
            rw [Functor.map_add, Preadditive.add_comp, Preadditive.comp_add, map_add] }
      map_zero' := by
        apply DirectSum.addHom_ext
        intro a f
        change (DirectSum.toAddMonoid (γ := TotalWeightHom X Z) _)
          (DirectSum.of (WeightHom X Y) a f) = 0
        rw [DirectSum.toAddMonoid_of]
        change weightHomInclusion (a+b) (weightHomComp f (0 : WeightHom Y Z b)) = 0
        dsimp only [weightHomComp]
        rw [Limits.comp_zero, Limits.comp_zero, map_zero]
      map_add' := by
        intro g g'
        apply DirectSum.addHom_ext
        intro a f
        rw [AddMonoidHom.add_apply]
        change (DirectSum.toAddMonoid (γ := TotalWeightHom X Z) _)
          (DirectSum.of (WeightHom X Y) a f) =
          (DirectSum.toAddMonoid (γ := TotalWeightHom X Z) _)
            (DirectSum.of (WeightHom X Y) a f) +
          (DirectSum.toAddMonoid (γ := TotalWeightHom X Z) _)
            (DirectSum.of (WeightHom X Y) a f)
        rw [DirectSum.toAddMonoid_of, DirectSum.toAddMonoid_of, DirectSum.toAddMonoid_of]
        change weightHomInclusion (a+b) (weightHomComp f (g+g')) =
          weightHomInclusion (a+b) (weightHomComp f g) +
          weightHomInclusion (a+b) (weightHomComp f g')
        dsimp only [weightHomComp]
        rw [Preadditive.comp_add, Preadditive.comp_add, map_add] }

private theorem totalComp_of (X Y Z : SyntheticSpectrum) (a b : ℤ)
    (f : WeightHom X Y a) (g : WeightHom Y Z b) :
    totalComp X Y Z (weightHomInclusion b g) (weightHomInclusion a f) =
      weightHomInclusion (a+b) (weightHomComp f g) := by
  change (DirectSum.toAddMonoid (γ := TotalWeightHom X Y →+ TotalWeightHom X Z) _)
    (DirectSum.of (WeightHom Y Z) b g) (weightHomInclusion a f) = _
  rw [DirectSum.toAddMonoid_of]
  change (DirectSum.toAddMonoid (γ := TotalWeightHom X Z) _)
    (DirectSum.of (WeightHom X Y) a f) = _
  rw [DirectSum.toAddMonoid_of]
  rfl

private theorem totalComp_assoc (W X Y Z : SyntheticSpectrum)
    (f : TotalWeightHom W X) (g : TotalWeightHom X Y) (h : TotalWeightHom Y Z) :
    totalComp W Y Z h (totalComp W X Y g f) =
      totalComp W X Z (totalComp X Y Z h g) f := by
  induction f using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | add f f' hf hf' => simp only [map_add, hf, hf']
  | of a f =>
    induction g using DirectSum.induction_on with
    | zero => simp only [map_zero, AddMonoidHom.zero_apply]
    | add g g' hg hg' => simp only [map_add, AddMonoidHom.add_apply, hg, hg']
    | of b g =>
      induction h using DirectSum.induction_on with
      | zero => simp only [map_zero, AddMonoidHom.zero_apply]
      | add h h' hh hh' => simp only [map_add, AddMonoidHom.add_apply, hh, hh']
      | of c h =>
        change totalComp W Y Z (weightHomInclusion c h)
          (totalComp W X Y (weightHomInclusion b g) (weightHomInclusion a f)) =
          totalComp W X Z (totalComp X Y Z (weightHomInclusion c h) (weightHomInclusion b g))
            (weightHomInclusion a f)
        rw [totalComp_of, totalComp_of, totalComp_of, totalComp_of]
        exact homogeneous_assoc quotients.coherence a b c f g h

private theorem lambda_comm_named (a c : ℤ × ℤ)
    (hac : a + (0,-1) = c) (hca : (0,-1) + a = c) (X : SyntheticSpectrum) :
    SyntheticCategory.lam.app ((SyntheticCategory.biShift a).obj X) =
      (biShiftAddIso a (0,-1) c hac).hom.app X ≫
        (biShiftAddIso (0,-1) a c hca).inv.app X ≫
          (SyntheticCategory.biShift a).map (SyntheticCategory.lam.app X) := by
  cases hac
  exact quotients.coherence.lambda_comm a X

private theorem totalComp_lambda_central (X Y : SyntheticSpectrum) (f : TotalWeightHom X Y) :
    totalComp X X Y f (weightHomInclusion (-1) (SyntheticCategory.lam.app X)) =
      totalComp X Y Y (weightHomInclusion (-1) (SyntheticCategory.lam.app Y)) f := by
  induction f using DirectSum.induction_on with
  | zero => simp only [map_zero, AddMonoidHom.zero_apply]
  | add f f' hf hf' => simp only [map_add, AddMonoidHom.add_apply, hf, hf']
  | of w f =>
    change totalComp X X Y (weightHomInclusion w f) _ = totalComp X Y Y _ (weightHomInclusion w f)
    rw [totalComp_of, totalComp_of]
    rw [homogeneous_regrade (-1) w (w-1) (by omega), homogeneous_regrade w (-1) (w-1) (by omega)]
    apply congrArg (weightHomInclusion (w-1))
    rw [SyntheticCategory.lam.naturality]
    rw [lambda_comm_named (0,w) (0,w-1) (by ext <;> simp [sub_eq_add_neg]) (by ext <;> simp [sub_eq_add_neg, add_comm]) X]
    repeat rw [Category.assoc]
    rw [Iso.inv_hom_id_app_assoc, Functor.id_map]

private def compLambda (X Y : SyntheticSpectrum) :
    TotalWeightHom X Y →ₗ[ℤ] TotalWeightHom X Y :=
  (totalComp X Y Y (weightHomInclusion (-1) (SyntheticCategory.lam.app Y))).toIntLinearMap

private theorem compLambda_of (X Y : SyntheticSpectrum) (w : ℤ) (f : WeightHom X Y w) :
    compLambda X Y (weightHomInclusion w f) =
      weightHomInclusion (w-1) (weightHomLambda f) := by
  simp only [compLambda, AddMonoidHom.coe_toIntLinearMap]
  rw [totalComp_of]
  change weightHomInclusion (w + -1)
    ((biShiftAddIso (0,w) (0,-1) (0,w + -1) _).inv.app X ≫
      (SyntheticCategory.biShift (0,-1)).map f ≫ SyntheticCategory.lam.app Y) = _
  rw [SyntheticCategory.lam.naturality]
  rfl

private theorem totalComp_lambda_left (X Y Z : SyntheticSpectrum)
    (f : TotalWeightHom X Y) (g : TotalWeightHom Y Z) :
    totalComp X Y Z (compLambda Y Z g) f =
      compLambda X Z (totalComp X Y Z g f) := by
  simpa only [compLambda, AddMonoidHom.coe_toIntLinearMap] using
    (totalComp_assoc X Y Z Z f g (weightHomInclusion (-1) (SyntheticCategory.lam.app Z))).symm

private theorem totalComp_lambda_right (X Y Z : SyntheticSpectrum)
    (f : TotalWeightHom X Y) (g : TotalWeightHom Y Z) :
    totalComp X Y Z g (compLambda X Y f) =
      compLambda X Z (totalComp X Y Z g f) := by
  simp only [compLambda, AddMonoidHom.coe_toIntLinearMap]
  rw [totalComp_assoc, totalComp_lambda_central]
  exact (totalComp_assoc X Y Z Z f g (weightHomInclusion (-1) (SyntheticCategory.lam.app Z))).symm

private theorem additive_polynomial_smul {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module (Polynomial ℤ) M] [Module (Polynomial ℤ) N]
    (f : M →+ N)
    (hX : ∀ m, f ((Polynomial.X : Polynomial ℤ) • m) = (Polynomial.X : Polynomial ℤ) • f m)
    (p : Polynomial ℤ) (m : M) : f (p • m) = p • f m := by
  induction p using Polynomial.induction_on generalizing m with
  | C a =>
    have ha : (Polynomial.C a : Polynomial ℤ) = (a : Polynomial ℤ) := Polynomial.C_eq_intCast a
    rw [ha]
    exact map_intCast_smul f (Polynomial ℤ) (Polynomial ℤ) a m
  | add p q hp hq => simp only [add_smul, map_add, hp, hq]
  | monomial n a ih =>
    rw [pow_succ, ← mul_assoc]
    rw [mul_smul, ih, hX]
    simp only [mul_smul]

private theorem totalLambda_eq_compLambda (X Y : SyntheticSpectrum) :
    totalLambda X Y = compLambda X Y := by
  apply LinearMap.ext
  intro f
  induction f using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | add f g hf hg => simp only [map_add, hf, hg]
  | of w f =>
    change totalLambda X Y (weightHomInclusion w f) = compLambda X Y (weightHomInclusion w f)
    rw [totalLambda_of, compLambda_of]

private theorem graded_X_smul (X Y : SyntheticSpectrum) (f : TotalWeightHom X Y) :
    letI := graded_module X Y
    (Polynomial.X : Polynomial ℤ) • f = compLambda X Y f := by
  letI := graded_module X Y
  change (Polynomial.eval₂ (Int.castRingHom _) (totalLambda X Y) Polynomial.X) f = _
  rw [Polynomial.eval₂_X, totalLambda_eq_compLambda]

/-- Actual shifted composition, extended bilinearly over the polynomial action. -/
@[no_expose] public def graded_compose : ∀ X Y Z : SyntheticSpectrum,
    letI := graded_module X Y
    letI := graded_module Y Z
    letI := graded_module X Z
    TotalWeightHom Y Z →ₗ[Polynomial ℤ]
      TotalWeightHom X Y →ₗ[Polynomial ℤ] TotalWeightHom X Z := by
  intro X Y Z
  letI := graded_module X Y
  letI := graded_module Y Z
  letI := graded_module X Z
  let C : TotalWeightHom Y Z →+ (TotalWeightHom X Y →+ TotalWeightHom X Z) :=
    totalComp X Y Z
  let F : TotalWeightHom Y Z →+ (TotalWeightHom X Y →ₗ[Polynomial ℤ] TotalWeightHom X Z) :=
    { toFun := fun g =>
        { toFun := C g
          map_add' := (C g).map_add
          map_smul' := by
            intro p f
            apply additive_polynomial_smul (C g) (fun f => ?_) p f
            change totalComp X Y Z g ((Polynomial.X : Polynomial ℤ) • f) =
              (Polynomial.X : Polynomial ℤ) • totalComp X Y Z g f
            rw [graded_X_smul, graded_X_smul]
            exact totalComp_lambda_right X Y Z f g }
      map_zero' := by
        apply LinearMap.ext
        intro f
        exact congrArg (fun h : TotalWeightHom X Y →+ TotalWeightHom X Z => h f) (map_zero (totalComp X Y Z))
      map_add' := by
        intro g g'
        apply LinearMap.ext
        intro f
        exact congrArg (fun h : TotalWeightHom X Y →+ TotalWeightHom X Z => h f) ((totalComp X Y Z).map_add g g') }
  exact
    { toFun := F
      map_add' := F.map_add
      map_smul' := by
        intro p g
        apply additive_polynomial_smul F (fun g => ?_) p g
        apply LinearMap.ext
        intro f
        change totalComp X Y Z ((Polynomial.X : Polynomial ℤ) • g) f =
          (Polynomial.X : Polynomial ℤ) • totalComp X Y Z g f
        rw [graded_X_smul, graded_X_smul]
        exact totalComp_lambda_left X Y Z f g }

/-- The extension agrees with actual composition on homogeneous maps. -/
public theorem graded_compose_homogeneous : ∀ (X Y Z : SyntheticSpectrum) (a b : ℤ)
      (f : WeightHom X Y a) (g : WeightHom Y Z b),
    graded_compose X Y Z (weightHomInclusion b g) (weightHomInclusion a f) =
      weightHomInclusion (a+b) (weightHomComp f g) := by
  intro X Y Z a b f g
  exact totalComp_of X Y Z a b f g

public def gradedEnrichment : GradedLambdaEnrichment SyntheticSpectrum where
  coherence := graded_coherence
  shiftAdditive := graded_shiftAdditive
  module := graded_module
  lambda_smul := graded_lambda_smul
  compose := graded_compose
  compose_homogeneous := graded_compose_homogeneous

public def shift_filtered (δ : ℤ × ℤ) : ∀ (X : SyntheticObject) (p : ℤ × ℤ),
    FilteredPieceIso (model.convergence X).filtration
      (model.convergence (.shift δ X)).filtration p (p+δ) := by sorry


set_option backward.privateInPublic true in
private def weightMapImplementation : ∀ (X : ClassicalObject) (s t w₁ w₂ : ℤ) (_hw : w₁ ≤ w₂) (_ht : w₂ ≤ t),
    ((model.family.obj (model.nu.functor.obj (X.obj model.auxiliary))).sequence.ssData (s,t,w₂)).eInfty ⟶
      ((model.family.obj (model.nu.functor.obj (X.obj model.auxiliary))).sequence.ssData (s,t,w₁)).eInfty := by
  intro X s t w₁ w₂ hw ht
  let k : ℕ := (w₂-w₁).toNat
  let δ : ℤ × ℤ := (0,-(k:ℤ))
  let p : ℤ × ℤ := (t-s,w₂)
  let A := model.nu.functor.obj (X.obj model.auxiliary)
  have hk : w₂ - (k:ℤ) = w₁ := by
    dsimp only [k]
    rw [Int.toNat_of_nonneg (sub_nonneg.mpr hw)]
    omega
  let sh := towerInfinityIso (model.convergence (.nu X))
    (model.convergence (.shift δ (.nu X))) (shift_filtered δ (.nu X) p) s
  have hsrc : (s,p.1+s,p.2) = (s,t,w₂) := by
    dsimp only [p]
    ext <;> simp
  have htgt : (s,(p+δ).1+s,(p+δ).2) = (s,t,w₁) := by
    dsimp only [p, δ, Prod.fst_add, Prod.snd_add]
    ext <;> simp_all only [add_zero, sub_add_cancel]
    omega
  let e : ((model.family.obj A).sequence.ssData (s,t,w₂)).eInfty ≅
      ((model.family.obj ((SyntheticCategory.biShift δ).obj A)).sequence.ssData (s,t,w₁)).eInfty :=
    eqToIso (congrArg (fun q => ((model.family.obj A).sequence.ssData q).eInfty) hsrc.symm) ≪≫
      sh ≪≫
        eqToIso (congrArg (fun q =>
          ((model.family.obj ((SyntheticCategory.biShift δ).obj A)).sequence.ssData q).eInfty) htgt)
  exact e.hom ≫ (model.family.map (lambdaPow k A)).eInftyMap (s,t,w₁)


set_option backward.privateInPublic true in
/-- Actual weight lowering: shift the fixed filtered homotopy, then apply the same λ power. -/
public def weight_map : ∀ (X : ClassicalObject) (s t w₁ w₂ : ℤ) (_hw : w₁ ≤ w₂) (_ht : w₂ ≤ t),
    ((model.family.obj (model.nu.functor.obj (X.obj model.auxiliary))).sequence.ssData (s,t,w₂)).eInfty ⟶
      ((model.family.obj (model.nu.functor.obj (X.obj model.auxiliary))).sequence.ssData (s,t,w₁)).eInfty := weightMapImplementation

/-- Fixed NuInfinityWeightMaps.representative; construction or proof deferred to its owning module. -/
public theorem weight_representative : ∀ (X : ClassicalObject) (s t w₁ w₂ : ℤ)
      (hw : w₁ ≤ w₂) (ht : w₂ ≤ t)
      (x : (model.classical.obj (X.obj model.auxiliary)).Page 2 (s,t))
      (z : ((model.family.obj (model.nu.functor.obj (X.obj model.auxiliary))).sequence.ssData (s,t,w₂)).eInfty),
    HasInfinityRepresentative _ 2 (s,t,w₂) (nuWeightLabel model X s t w₂ ht x) z →
      HasInfinityRepresentative _ 2 (s,t,w₁) (nuWeightLabel model X s t w₁ (hw.trans ht) x)
        (weight_map X s t w₁ w₂ hw ht z) := by sorry

private def weightRawPageIso
    {E F : KIP126.Core.SpectralSequence (ModuleCat.{0} ℤ) Tridegree}
    (e : E ≅ F) (r : ℤ) (p : Tridegree) : E.Page r p ≅ F.Page r p where
  hom := e.hom.pageMap r p
  inv := e.inv.pageMap r p
  hom_inv_id := by
    rw [← SpectralSequenceMorphism.pageMap_comp, e.hom_inv_id,
      SpectralSequenceMorphism.pageMap_id]
  inv_hom_id := by
    rw [← SpectralSequenceMorphism.pageMap_comp, e.inv_hom_id,
      SpectralSequenceMorphism.pageMap_id]

private theorem weightLabelBijective (X : ClassicalObject) (s t w : ℤ) (hw : w ≤ t) :
    Function.Bijective (nuWeightLabel model X s t w hw) := by
  let zeroIso := SyntheticCategory.biShift_zero.app
    (model.nu.functor.obj (X.obj model.auxiliary))
  let zeroPage := weightRawPageIso (model.family.functor.mapIso zeroIso) 2
    (s,t,t-(t-w).toNat)
  have hzero : Function.Bijective zeroPage.hom := ConcreteCategory.bijective_of_isIso _
  change Function.Bijective (fun x => nuWeightLabel model X s t w hw x)
  dsimp only [nuWeightLabel, regradeE2, targetNuLabel]
  apply Function.Bijective.comp
  · exact ConcreteCategory.bijective_of_isIso _
  · apply Function.Bijective.comp
    · exact hzero
    · change Function.Bijective
        ((fun z : (model.family.obj ((SyntheticCategory.biShift (0,0)).obj
            (model.nu.functor.obj (X.obj model.auxiliary)))).E₂
              (s,t,t+0-(t-w).toNat) =>
          Eq.mp (by simp only [add_zero]) z) ∘
            (model.comparison.nuE2 X 0 s t (t-w).toNat))
      exact (Equiv.cast _).bijective.comp
        (model.comparison.nuE2 X 0 s t (t-w).toNat).bijective

private theorem infinityHasWeightLabel (X : ClassicalObject) (s t w : ℤ) (hw : w ≤ t)
    (z : ((model.family.obj (model.nu.functor.obj (X.obj model.auxiliary))).sequence.ssData
      (s,t,w)).eInfty) :
    ∃ x, HasInfinityRepresentative _ 2 (s,t,w) (nuWeightLabel model X s t w hw x) z := by
  let A := model.family.obj (model.nu.functor.obj (X.obj model.auxiliary))
  haveI : Epi ((A.sequence.ssData (s,t,w)).pageπ ⊤) :=
    inferInstanceAs (Epi (cokernel.π _))
  obtain ⟨a, ha⟩ := (ModuleCat.epi_iff_surjective
    ((A.sequence.ssData (s,t,w)).pageπ ⊤)).mp inferInstance z
  obtain ⟨x, hx⟩ := (weightLabelBijective X s t w hw).surjective
    ((Subobject.ofLE _ _ ((A.sequence.ssData (s,t,w)).Z_anti le_top) ≫
      (A.sequence.ssData (s,t,w)).pageπ
        (↑(2-A.sequence.r₀).toNat : WithTop ℕ)) a)
  exact ⟨x, by omega, a, hx.symm, ha⟩

private theorem familyPageMapCast
    {U V : SyntheticSpectrum} (g : U ⟶ V) {p q : Tridegree} (h : p = q)
    (x : (model.family.obj U).E₂ p) :
    model.family.pageMap g 2 q
      (Eq.mp (congrArg (fun a : Tridegree => ((model.family.obj U).E₂ a : Type)) h) x) =
      Eq.mp (congrArg (fun a : Tridegree => ((model.family.obj V).E₂ a : Type)) h)
        (model.family.pageMap g 2 p x) := by
  subst q
  rfl

private theorem targetNuLabelNatural
    (X Y : ClassicalObject) (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (s t : ℤ) (k : ℕ) (x : (model.classical.obj (X.obj model.auxiliary)).Page 2 (s,t)) :
    model.family.pageMap (model.nu.functor.map f) 2 (s,t,t-k)
      (targetNuLabel model X s t k x) =
    targetNuLabel model Y s t k ((model.classical.map f).pageMap 2 (s,t) x) := by
  let p : Tridegree := (s,t,t-k)
  let nuf := model.nu.functor.map f
  let x₀ : (model.family.obj ((SyntheticCategory.biShift (0,0)).obj
      (model.nu.functor.obj (X.obj model.auxiliary)))).E₂ p := by
    simpa only [add_zero] using model.comparison.nuE2 X 0 s t k x
  let y₀ : (model.family.obj ((SyntheticCategory.biShift (0,0)).obj
      (model.nu.functor.obj (Y.obj model.auxiliary)))).E₂ p := by
    simpa only [add_zero] using model.comparison.nuE2 Y 0 s t k
      ((model.classical.map f).pageMap 2 (s,t) x)
  have hxy : model.family.pageMap ((SyntheticCategory.biShift (0,0)).map nuf) 2 p x₀ = y₀ := by
    have hdeg : (s,t,t+0-(k : ℤ)) = p := by dsimp [p]; simp only [add_zero]
    have hraw := model.comparison.nu_natural X Y f 0 s t k x
    have hc := familyPageMapCast ((SyntheticCategory.biShift (0,0)).map nuf) hdeg
      (model.comparison.nuE2 X 0 s t k x)
    exact hc.trans (congrArg
      (fun z => Eq.mp (congrArg (fun a : Tridegree =>
        ((model.family.obj ((SyntheticCategory.biShift (0,0)).obj
          (model.nu.functor.obj (Y.obj model.auxiliary)))).E₂ a : Type)) hdeg) z) hraw)
  let zx := SyntheticCategory.biShift_zero.hom.app
    (model.nu.functor.obj (X.obj model.auxiliary))
  let zy := SyntheticCategory.biShift_zero.hom.app
    (model.nu.functor.obj (Y.obj model.auxiliary))
  have hn : (SyntheticCategory.biShift (0,0)).map nuf ≫ zy = zx ≫ nuf :=
    SyntheticCategory.biShift_zero.hom.naturality nuf
  change model.family.pageMap nuf 2 p (model.family.pageMap zx 2 p x₀) =
    model.family.pageMap zy 2 p y₀
  calc
    _ = model.family.pageMap (zx ≫ nuf) 2 p x₀ :=
      (ConcreteCategory.congr_hom (familyPageMap_comp model.family zx nuf 2 p) x₀).symm
    _ = model.family.pageMap ((SyntheticCategory.biShift (0,0)).map nuf ≫ zy) 2 p x₀ :=
      congrArg (fun g => model.family.pageMap g 2 p x₀) hn.symm
    _ = model.family.pageMap zy 2 p
        (model.family.pageMap ((SyntheticCategory.biShift (0,0)).map nuf) 2 p x₀) :=
      ConcreteCategory.congr_hom
        (familyPageMap_comp model.family ((SyntheticCategory.biShift (0,0)).map nuf) zy 2 p) x₀
    _ = _ := congrArg (model.family.pageMap zy 2 p) hxy

private theorem familyPageMapRegrade
    {U V : SyntheticSpectrum} (g : U ⟶ V) {p q : Tridegree} (h : p = q)
    (x : (model.family.obj U).E₂ p) :
    model.family.pageMap g 2 q (regradeE2 h x) =
      regradeE2 h (model.family.pageMap g 2 p x) := by
  subst q
  rfl

private theorem weightLabelNatural
    (X Y : ClassicalObject) (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (s t w : ℤ) (hw : w ≤ t)
    (x : (model.classical.obj (X.obj model.auxiliary)).Page 2 (s,t)) :
    model.family.pageMap (model.nu.functor.map f) 2 (s,t,w)
      (nuWeightLabel model X s t w hw x) =
    nuWeightLabel model Y s t w hw ((model.classical.map f).pageMap 2 (s,t) x) := by
  unfold nuWeightLabel
  rw [familyPageMapRegrade, targetNuLabelNatural]

/-- The fixed weight maps preserve identities. -/
public theorem weight_map_self : ∀ (X : ClassicalObject) (s t w : ℤ) (hw : w ≤ t),
    weight_map X s t w w le_rfl hw = 𝟙 _ := by
  intro X s t w hw
  ext z
  obtain ⟨x, hx⟩ := infinityHasWeightLabel X s t w hw z
  have hm := weight_representative X s t w w le_rfl hw x z hx
  exact HasInfinityRepresentative.unique hm hx


/-- The fixed weight maps compose along increasing weights. -/
public theorem weight_map_comp : ∀ (X : ClassicalObject) (s t w₁ w₂ w₃ : ℤ)
      (h₁₂ : w₁ ≤ w₂) (h₂₃ : w₂ ≤ w₃) (h₃ : w₃ ≤ t),
    weight_map X s t w₂ w₃ h₂₃ h₃ ≫ weight_map X s t w₁ w₂ h₁₂ (h₂₃.trans h₃) =
      weight_map X s t w₁ w₃ (h₁₂.trans h₂₃) h₃ := by
  intro X s t w₁ w₂ w₃ h₁₂ h₂₃ h₃
  ext z
  obtain ⟨x, hx⟩ := infinityHasWeightLabel X s t w₃ h₃ z
  have h₂ := weight_representative X s t w₂ w₃ h₂₃ h₃ x z hx
  have h₁ := weight_representative X s t w₁ w₂ h₁₂ (h₂₃.trans h₃) x _ h₂
  have h₁' := weight_representative X s t w₁ w₃ (h₁₂.trans h₂₃) h₃ x z hx
  exact HasInfinityRepresentative.unique h₁ h₁'


/-- The fixed weight maps commute with maps induced by nu. -/
public theorem weight_naturality : ∀ (X Y : ClassicalObject) (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
      (s t w₁ w₂ : ℤ) (hw : w₁ ≤ w₂) (ht : w₂ ≤ t),
    (model.family.map (model.nu.functor.map f)).eInftyMap (s,t,w₂) ≫ weight_map Y s t w₁ w₂ hw ht =
      weight_map X s t w₁ w₂ hw ht ≫ (model.family.map (model.nu.functor.map f)).eInftyMap (s,t,w₁) := by
  intro X Y f s t w₁ w₂ hw ht
  ext z
  obtain ⟨x, hx⟩ := infinityHasWeightLabel X s t w₂ ht z
  have hy := infinity_rep_map (model.nu.functor.map f) (s,t,w₂) hx
  rw [weightLabelNatural] at hy
  have hleft := weight_representative Y s t w₁ w₂ hw ht
    ((model.classical.map f).pageMap 2 (s,t) x) _ hy
  have hlow := weight_representative X s t w₁ w₂ hw ht x z hx
  have hright := infinity_rep_map (model.nu.functor.map f) (s,t,w₁) hlow
  rw [weightLabelNatural] at hright
  exact HasInfinityRepresentative.unique hleft hright


public def weightMaps : NuInfinityWeightMaps model where
  map := weight_map
  map_self := weight_map_self
  map_comp := weight_map_comp
  naturality := weight_naturality
  representative := weight_representative


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
        sphereAlgebra.unit := by
  let S : FiniteSpectrum := ⟨SphereSpectrum, IsFiniteSpectrum.sphere⟩
  let e := sphereMappingAdamsIso closedBackground classical
  let u := e.inv.pageMap 2 (0,0) sphereAlgebra.unit
  have hu : e.hom.pageMap 2 (0,0) u = sphereAlgebra.unit := by
    have h := congrArg (fun f => f sphereAlgebra.unit)
      (congrArg (fun f => f.pageMap 2 (0,0)) e.inv_hom_id)
    simpa only [SpectralSequenceMorphism.pageMap_comp,
      SpectralSequenceMorphism.pageMap_id, ModuleCat.comp_apply,
      ModuleCat.id_apply] using h
  have h := mapping_sphere_product (0,0) (0,0) ((mapping_identity S).page 2) u
  have hleft := eq_of_heq (mapping_page_left_unital S S 2 (0,0) u)
  rw [hleft] at h
  change e.hom.pageMap 2 (0,0) u = sphereAlgebra.product (0,0) (0,0)
    (e.hom.pageMap 2 (0,0) ((mapping_identity S).page 2))
    (e.hom.pageMap 2 (0,0) u) at h
  rw [hu] at h
  exact (eq_of_heq (sphereAlgebra.unit_right (0,0)
    (e.hom.pageMap 2 (0,0) ((mapping_identity S).page 2)))).symm.trans h.symm

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
