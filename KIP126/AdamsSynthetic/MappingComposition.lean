module

public import KIP126.AdamsSynthetic.Mapping
public import KIP126.SpectralSequence.MultiplicativeCategory

@[expose] section

/-! Composition of actual mapping Adams systems. The paired systems, identity
classes, and actual shifted-map composition all belong to the same background
and the same tower. Sources: KIPBase `multiplicativeSS/Adams.lean`, fixed
baseline 5aa845241533. No concrete composition producer is constructed here. -/
namespace KIP126.AdamsSynthetic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open KIP126.StableHomotopy KIP126.Classical.Adams KIP126.Core.SpectralSequence
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] {H : C} {unit : SphereSpectrum ⟶ H}
  {A : ClassicalAdamsFamily C} {B : ClosedSymmetricTensorTriangulated C}
  {P : ClassicalTowerPresentation unit A} {scope : C → Prop}

public abbrev MappingObject (scope : C → Prop) := { X : C // scope X }

public def MappingSpectrumSystem.hom (S : MappingSpectrumSystem B P scope)
    (X Y : MappingObject scope) : ConvergingSequence.{0,v} ℤ :=
  ⟨S.converging X.val Y.val X.property Y.property⟩

/-- Adams parity is the parity of the stem `t-s`. -/
public def adamsStemParity : GradingParity where
  toFun p := ((p.2 - p.1 : ℤ) : ZMod 2)
  map_zero' := by simp
  map_add' p q := by
    simp only [Prod.fst_add, Prod.snd_add, Int.cast_sub, Int.cast_add]
    ring

/-- All coherence laws on composition. The page, E∞, and filtered-target
products are already related by `ConvergingSSPairing`; units are obtained from
one common infinite-cycle representative and the actual identity map. -/
public structure MappingComposition (S : MappingSpectrumSystem B P scope) where
  pairing : ∀ X Y Z : MappingObject scope,
    ConvergingSSPairing (S.hom X Y).underlying (S.hom Y Z).underlying (S.hom X Z).underlying
  parity : ∀ X Y Z, (pairing X Y Z).ssPairing.parity = adamsStemParity
  abutment_compatible : ∀ (X Y Z : MappingObject scope) (a b : ℤ)
      (x : (S.hom X Y).underlying.A a) (y : (S.hom Y Z).underlying.A b),
    mappingHomotopyEquiv B (a + b) X.val Z.val ((pairing X Y Z).abutmentPair a b x y) =
      (shiftFunctorAdd C a b).hom.app X.val ≫
        (shiftFunctor C b).map (mappingHomotopyEquiv B a X.val Y.val x) ≫
        mappingHomotopyEquiv B b Y.val Z.val y
  page_associative : ∀ (W X Y Z : MappingObject scope) (r : ℤ) (i j k : ℤ × ℤ)
      (x : (S.hom W X).underlying.E.Page r i)
      (y : (S.hom X Y).underlying.E.Page r j)
      (z : (S.hom Y Z).underlying.E.Page r k),
    HEq ((pairing W Y Z).ssPairing.pair r (i + j) k
      ((pairing W X Y).ssPairing.pair r i j x y) z)
      ((pairing W X Z).ssPairing.pair r i (j + k) x
        ((pairing X Y Z).ssPairing.pair r j k y z))
  identity : ∀ X : MappingObject scope, ConvergingSSUnit (S.hom X X).underlying rfl
  identity_actual : ∀ X : MappingObject scope,
    mappingHomotopyZeroEquiv B X.val X.val (identity X).abutment = 𝟙 X.val
  page_left_unital : ∀ (X Y : MappingObject scope) (r : ℤ) (k : ℤ × ℤ)
      (x : (S.hom X Y).underlying.E.Page r k),
    HEq ((pairing X X Y).ssPairing.pair r (0,0) k ((identity X).page r) x) x
  page_right_unital : ∀ (X Y : MappingObject scope) (r : ℤ) (k : ℤ × ℤ)
      (x : (S.hom X Y).underlying.E.Page r k),
    HEq ((pairing X Y Y).ssPairing.pair r k (0,0) x ((identity Y).page r)) x
private theorem infinity_heq_of_page_heq
    (E : KIP126.Core.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ))
    (p q : ℤ × ℤ) (hpq : p = q) (r : ℤ)
    (x : InfiniteCycles E p) (y : InfiniteCycles E q)
    (h : HEq (infinityToPage E r p x) (infinityToPage E r q y)) :
    HEq ((E.ssData p).pageπ ⊤ x) ((E.ssData q).pageπ ⊤ y) := by
  subst q
  exact heq_of_eq ((E.ssData p).infinity_projection_eq_of_page_projection_eq
    ↑(r-E.r₀).toNat x y (eq_of_heq h))

private theorem MappingComposition.page_pair_infinity
    {S : MappingSpectrumSystem B P scope} (M : MappingComposition S)
    (X Y Z : MappingObject scope) (i j : ℤ × ℤ)
    (x : InfiniteCycles (S.hom X Y).underlying.E i)
    (y : InfiniteCycles (S.hom Y Z).underlying.E j) :
    (M.pairing X Y Z).ssPairing.pair 2 i j
      (infinityToPage (S.hom X Y).underlying.E 2 i x)
      (infinityToPage (S.hom Y Z).underlying.E 2 j y) =
    infinityToPage (S.hom X Z).underlying.E 2 (i+j)
      ((M.pairing X Y Z).cyclePairAtInfinity i j x y) :=
  (M.pairing X Y Z).finitePagePair_compatible 2 i j
    (le_of_eq (A.firstPage _)) (le_of_eq (A.firstPage _))
    (le_of_eq (A.firstPage _)) x y

/-- The E∞ associativity law follows from page associativity on common
infinite cycles and equality of their infinite quotient classes. -/
public theorem MappingComposition.eInfty_associative
    {S : MappingSpectrumSystem B P scope} (M : MappingComposition S)
    (W X Y Z : MappingObject scope) (i j k : ℤ × ℤ)
    (x : ((S.hom W X).underlying.E.ssData i).eInfty)
    (y : ((S.hom X Y).underlying.E.ssData j).eInfty)
    (z : ((S.hom Y Z).underlying.E.ssData k).eInfty) :
    HEq ((M.pairing W Y Z).eInftyPair (i+j) k
      ((M.pairing W X Y).eInftyPair i j x y) z)
      ((M.pairing W X Z).eInftyPair i (j+k) x
        ((M.pairing X Y Z).eInftyPair j k y z)) := by
  haveI : Epi (((S.hom W X).underlying.E.ssData i).pageπ ⊤) :=
    inferInstanceAs (Epi (cokernel.π _))
  haveI : Epi (((S.hom X Y).underlying.E.ssData j).pageπ ⊤) :=
    inferInstanceAs (Epi (cokernel.π _))
  haveI : Epi (((S.hom Y Z).underlying.E.ssData k).pageπ ⊤) :=
    inferInstanceAs (Epi (cokernel.π _))
  obtain ⟨a,rfl⟩ := (ModuleCat.epi_iff_surjective
    (((S.hom W X).underlying.E.ssData i).pageπ ⊤)).mp inferInstance x
  obtain ⟨b,rfl⟩ := (ModuleCat.epi_iff_surjective
    (((S.hom X Y).underlying.E.ssData j).pageπ ⊤)).mp inferInstance y
  obtain ⟨c,rfl⟩ := (ModuleCat.epi_iff_surjective
    (((S.hom Y Z).underlying.E.ssData k).pageπ ⊤)).mp inferInstance z
  have h := M.page_associative W X Y Z 2 i j k
    (infinityToPage _ 2 i a) (infinityToPage _ 2 j b) (infinityToPage _ 2 k c)
  simp only [MappingComposition.page_pair_infinity] at h
  have hi := infinity_heq_of_page_heq (S.hom W Z).underlying.E
    ((i+j)+k) (i+(j+k)) (add_assoc i j k) 2 _ _ h
  simpa only [ConvergingSSPairing.eInftyPair_induced] using hi

/-- The E∞ left unit is inherited from the page unit on the same common
infinite-cycle representative. -/
public theorem MappingComposition.eInfty_left_unital
    {S : MappingSpectrumSystem B P scope} (M : MappingComposition S)
    (X Y : MappingObject scope) (k : ℤ × ℤ)
    (x : ((S.hom X Y).underlying.E.ssData k).eInfty) :
    HEq ((M.pairing X X Y).eInftyPair (0,0) k (M.identity X).eInfty x) x := by
  haveI : Epi (((S.hom X Y).underlying.E.ssData k).pageπ ⊤) :=
    inferInstanceAs (Epi (cokernel.π _))
  obtain ⟨a,rfl⟩ := (ModuleCat.epi_iff_surjective
    (((S.hom X Y).underlying.E.ssData k).pageπ ⊤)).mp inferInstance x
  have h := M.page_left_unital X Y 2 k (infinityToPage _ 2 k a)
  simp only [ConvergingSSUnit.page, MappingComposition.page_pair_infinity] at h
  have hi := infinity_heq_of_page_heq (S.hom X Y).underlying.E
    ((0,0)+k) k (zero_add k) 2 _ _ h
  simpa only [ConvergingSSPairing.eInftyPair_induced, ConvergingSSUnit.eInfty] using hi

/-- The E∞ right unit is inherited from the same page and cycle data. -/
public theorem MappingComposition.eInfty_right_unital
    {S : MappingSpectrumSystem B P scope} (M : MappingComposition S)
    (X Y : MappingObject scope) (k : ℤ × ℤ)
    (x : ((S.hom X Y).underlying.E.ssData k).eInfty) :
    HEq ((M.pairing X Y Y).eInftyPair k (0,0) x (M.identity Y).eInfty) x := by
  haveI : Epi (((S.hom X Y).underlying.E.ssData k).pageπ ⊤) :=
    inferInstanceAs (Epi (cokernel.π _))
  obtain ⟨a,rfl⟩ := (ModuleCat.epi_iff_surjective
    (((S.hom X Y).underlying.E.ssData k).pageπ ⊤)).mp inferInstance x
  have h := M.page_right_unital X Y 2 k (infinityToPage _ 2 k a)
  simp only [ConvergingSSUnit.page, MappingComposition.page_pair_infinity] at h
  have hi := infinity_heq_of_page_heq (S.hom X Y).underlying.E
    (k+(0,0)) k (add_zero k) 2 _ _ h
  simpa only [ConvergingSSPairing.eInftyPair_induced, ConvergingSSUnit.eInfty] using hi

namespace MappingComposition

omit [HasFunctorialCofiber (C := C)] in
private theorem homHEq {X X' Y : C} (h : X = X') {f : X ⟶ Y} {g : X' ⟶ Y}
    (hh : f = eqToHom h ≫ g) : HEq f g := by
  cases h
  simpa using hh

private theorem equivHEq {α β : ℤ → Type v} (e : ∀ n, α n ≃ β n)
    {m n : ℤ} (h : m = n) {x : α m} {y : α n}
    (hh : HEq (e m x) (e n y)) : HEq x y := by
  cases h
  exact heq_of_eq ((e m).injective (eq_of_heq hh))

omit [HasFunctorialCofiber (C := C)] in
private theorem shiftedLeftUnit {X Y : C} (n : ℤ) (f : (shiftFunctor C n).obj X ⟶ Y) :
    HEq ((shiftFunctorAdd C 0 n).hom.app X ≫
      (shiftFunctor C n).map ((shiftFunctorZero C ℤ).hom.app X) ≫ f) f := by
  apply homHEq (congrArg (fun i => (shiftFunctor C i).obj X) (zero_add n))
  rw [shiftFunctorAdd_zero_add_hom_app]
  simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id_app,
    Functor.id_obj]
  rw [(shiftFunctor C n).map_id X, Category.id_comp]

omit [HasFunctorialCofiber (C := C)] in
private theorem shiftedRightUnit {X Y : C} (n : ℤ) (f : (shiftFunctor C n).obj X ⟶ Y) :
    HEq ((shiftFunctorAdd C n 0).hom.app X ≫
      (shiftFunctor C (0:ℤ)).map f ≫ (shiftFunctorZero C ℤ).hom.app Y) f := by
  apply homHEq (congrArg (fun i => (shiftFunctor C i).obj X) (add_zero n))
  rw [shiftFunctorAdd_add_zero_hom_app]
  simp only [Category.assoc, (shiftFunctorZero C ℤ).hom.naturality,
    Iso.inv_hom_id_app_assoc, Functor.id_map]

omit [HasFunctorialCofiber (C := C)] in
private theorem shiftedAssoc {W X Y Z : C} (i j k : ℤ)
    (f : (shiftFunctor C i).obj W ⟶ X) (g : (shiftFunctor C j).obj X ⟶ Y)
    (h : (shiftFunctor C k).obj Y ⟶ Z) :
    HEq ((shiftFunctorAdd C (i+j) k).hom.app W ≫
      (shiftFunctor C k).map ((shiftFunctorAdd C i j).hom.app W ≫
        (shiftFunctor C j).map f ≫ g) ≫ h)
      ((shiftFunctorAdd C i (j+k)).hom.app W ≫
        (shiftFunctor C (j+k)).map f ≫
          (shiftFunctorAdd C j k).hom.app X ≫ (shiftFunctor C k).map g ≫ h) := by
  apply homHEq (congrArg (fun a => (shiftFunctor C a).obj W) (add_assoc i j k))
  simp only [Functor.map_comp, Category.assoc]
  rw [← Category.assoc ((shiftFunctorAdd C (i+j) k).hom.app W)
    ((shiftFunctor C k).map ((shiftFunctorAdd C i j).hom.app W))]
  rw [shiftFunctorAdd_assoc_hom_app]
  simp only [shiftFunctorAdd', Iso.trans_hom, NatTrans.comp_app, eqToIso.hom,
    eqToHom_app, Category.assoc]
  rw [(shiftFunctorAdd C j k).hom.naturality_assoc]
  rfl

variable {S : MappingSpectrumSystem B P scope} (M : MappingComposition S)

private theorem identityShift (X : MappingObject scope) :
    mappingHomotopyEquiv B 0 X.val X.val (M.identity X).abutment =
      (shiftFunctorZero C ℤ).hom.app X.val := by
  apply (Iso.homCongr ((shiftFunctorZero C ℤ).app X.val) (Iso.refl X.val)).injective
  simpa [mappingHomotopyZeroEquiv, Iso.homCongr] using M.identity_actual X

/-- The left abutment unit is the actual identity map under the same closed comparison. -/
public theorem abutment_left_unital (X Y : MappingObject scope) (n : ℤ)
    (x : (S.hom X Y).underlying.A n) :
    HEq ((M.pairing X X Y).abutmentPair 0 n (M.identity X).abutment x) x := by
  apply equivHEq (fun n => mappingHomotopyEquiv B n X.val Y.val) (zero_add n)
  rw [M.abutment_compatible, identityShift M]
  exact shiftedLeftUnit n _

/-- The right abutment unit follows from the actual identity and shift coherence. -/
public theorem abutment_right_unital (X Y : MappingObject scope) (n : ℤ)
    (x : (S.hom X Y).underlying.A n) :
    HEq ((M.pairing X Y Y).abutmentPair n 0 x (M.identity Y).abutment) x := by
  apply equivHEq (fun n => mappingHomotopyEquiv B n X.val Y.val) (add_zero n)
  rw [M.abutment_compatible, identityShift M]
  exact shiftedRightUnit n _

/-- Abutment associativity follows from actual shifted-map composition and shift coherence. -/
public theorem abutment_associative (W X Y Z : MappingObject scope) (i j k : ℤ)
    (x : (S.hom W X).underlying.A i) (y : (S.hom X Y).underlying.A j)
    (z : (S.hom Y Z).underlying.A k) :
    HEq ((M.pairing W Y Z).abutmentPair (i+j) k ((M.pairing W X Y).abutmentPair i j x y) z)
      ((M.pairing W X Z).abutmentPair i (j+k) x ((M.pairing X Y Z).abutmentPair j k y z)) := by
  apply equivHEq (fun n => mappingHomotopyEquiv B n W.val Z.val) (add_assoc i j k)
  rw [M.abutment_compatible, M.abutment_compatible, M.abutment_compatible, M.abutment_compatible]
  exact shiftedAssoc i j k _ _ _
end MappingComposition

public theorem MappingComposition.parity_apply {S : MappingSpectrumSystem B P scope}
    (M : MappingComposition S) (X Y Z : MappingObject scope) (s t : ℤ) :
    (M.pairing X Y Z).ssPairing.parity (s,t) = ((t-s : ℤ) : ZMod 2) := by
  rw [M.parity]
  rfl

/-- The composition multiplication on sphere mappings agrees with the
previously supplied sphere E₂ algebra, through the canonical mapping-sphere
comparison. It is not a second freely chosen sphere multiplication. -/
public structure MappingSphereCompatibility {S : MappingSpectrumSystem B P scope}
    (M : MappingComposition S) (E₂ : SphereE2Algebra A) (hSphere : scope SphereSpectrum) : Prop where
  product : ∀ (p q : ℤ × ℤ)
      (x : (S.hom ⟨SphereSpectrum,hSphere⟩ ⟨SphereSpectrum,hSphere⟩).underlying.E.Page 2 p)
      (y : (S.hom ⟨SphereSpectrum,hSphere⟩ ⟨SphereSpectrum,hSphere⟩).underlying.E.Page 2 q),
    (sphereMappingAdamsIso B A).hom.pageMap 2 (p + q)
      ((M.pairing ⟨SphereSpectrum,hSphere⟩ ⟨SphereSpectrum,hSphere⟩
        ⟨SphereSpectrum,hSphere⟩).ssPairing.pair 2 p q x y) =
      E₂.product p q ((sphereMappingAdamsIso B A).hom.pageMap 2 p x)
        ((sphereMappingAdamsIso B A).hom.pageMap 2 q y)
  unit : (sphereMappingAdamsIso B A).hom.pageMap 2 (0,0)
      ((M.identity ⟨SphereSpectrum,hSphere⟩).page 2) = E₂.unit
end
end KIP126.AdamsSynthetic
