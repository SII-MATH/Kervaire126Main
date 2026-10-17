import KIP126.ProofTools.Operations

open CategoryTheory KIP126.StableHomotopy
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Core.SpectralSequence KIP126.Kervaire.Route

namespace Prop620IndependentReview
universe u v w

section Domain
variable {C : Type u} [StableHomotopyCategory.{u,v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w,v} Syn]
  [HasFunctorialCofiber (C := Syn)] (D : Model C Syn)

/-- The missing earlier-page bound is necessary for any actual witness,
independently of its extension equation or labels. -/
theorem earlier_domain_necessary (X Y : ClassicalObject)
    (f : X.obj D.auxiliary ⟶ Y.obj D.auxiliary)
    (r : ℕ) (n s t : ℤ)
    (x : (D.classical.obj (X.obj D.auxiliary)).Page 2 (s,t))
    (y : (D.classical.obj (Y.obj D.auxiliary)).Page 2 (s+n,t+n))
    (h : FiniteExtension D X Y f r n s t x y) :
    n ≤ (r : ℤ) - 2 + normalizedExponent D.classicalTower f := by
  obtain ⟨W⟩ := h
  exact W.length_upper

theorem no_extension_outside_domain (X Y : ClassicalObject)
    (f : X.obj D.auxiliary ⟶ Y.obj D.auxiliary)
    (r : ℕ) (n s t : ℤ)
    (x : (D.classical.obj (X.obj D.auxiliary)).Page 2 (s,t))
    (y : (D.classical.obj (Y.obj D.auxiliary)).Page 2 (s+n,t+n))
    (hn : (r : ℤ) - 2 + normalizedExponent D.classicalTower f < n) :
    ¬ FiniteExtension D X Y f r n s t x y := by
  intro h
  exact (not_le_of_gt hn) (earlier_domain_necessary D X Y f r n s t x y h)
end Domain

section ExactTarget
variable {Acat : Type u} [Category.{v} Acat] [Abelian Acat]
  {ω : Type w} {A B : ω → Acat}
  {F : Filtration A} {G : Filtration B}

/-- With the original equation fixed, inessentiality concerns the zero
member of this target's own complete coset. -/
theorem inessential_iff_zero_in_same_target_coset
    (f : FilteredMorphism F G) (k : ω) (s n : ℤ) {T : Acat}
    (x : T ⟶ F.associatedGraded s k)
    (y : T ⟶ G.associatedGraded (s+n) k)
    (h : FilteredMapExtension.Relation f k s n x y) :
    ¬ FilteredMapExtension.Essential f k s n x y ↔
      (0 : T ⟶ G.associatedGraded (s+n) k) ∈
        FilteredMapExtension.TargetCoset f k s n y := by
  classical
  simp only [FilteredMapExtension.Essential, h, true_and, not_not]

/-- Equivalent exact-target version: the original target is an actual
homogeneous ambiguity, rather than just some unrelated shorter target. -/
theorem inessential_iff_zero_source_same_target
    (f : FilteredMorphism F G) (k : ω) (s n : ℤ) {T : Acat}
    (x : T ⟶ F.associatedGraded s k)
    (y : T ⟶ G.associatedGraded (s+n) k)
    (h : FilteredMapExtension.Relation f k s n x y) :
    ¬ FilteredMapExtension.Essential f k s n x y ↔
      FilteredMapExtension.Relation f k s n 0 y := by
  classical
  constructor
  · intro hne
    have hz : FilteredMapExtension.Relation f k s n x 0 := by
      by_contra hnz
      exact hne ((FilteredMapExtension.essential_iff h).mpr hnz)
    simpa only [sub_self, sub_zero] using h.sub hz
  · intro hz he
    have hh : FilteredMapExtension.Relation f k s n x 0 := by
      simpa only [sub_zero, sub_self] using h.sub hz
    exact ((FilteredMapExtension.essential_iff h).mp he) hh
end ExactTarget

section TowerExactTarget
variable {Syn : Type u} [SyntheticCategory.{u,v} Syn]
  [HasFunctorialCofiber (C := Syn)]
  {H : Syn} {unit : S_0_0 ⟶ H} {F : SyntheticAdamsFamily Syn}
  {P : SyntheticTowerPresentation unit F} {X Y : Syn} {g : X ⟶ Y}
  {cx : SyntheticTowerConvergence P X} {cy : SyntheticTowerConvergence P Y}

private theorem elementMap_zero {A : ModuleCat.{v} ℤ} :
    elementMap (0 : A) = 0 := by
  ext z
  simp [elementMap]

/-- This checks the worker's exact-target formula in the existing public
tower language; it is evidence here, not an added production interface. -/
theorem tower_inessential_iff_zero_source_same_target
    (M : ConvergentMap F g cx.toConvergence cy.toConvergence)
    (p : ℤ × ℤ) (s n : ℤ)
    (x : ((F.obj X).sequence.ssData (s,p.1+s,p.2)).eInfty)
    (y : ((F.obj Y).sequence.ssData (s+n,p.1+(s+n),p.2)).eInfty)
    (h : TowerExtensionEquation M p s n x y) :
    ¬ TowerEssentialExtension M p s n x y ↔
      TowerExtensionEquation M p s n 0 y := by
  unfold TowerEssentialExtension TowerExtensionEquation
    ConvergentMap.EssentialExtension ConvergentMap.ExtensionEquation
  rw [elementMap_zero]
  simp only [toGraded, Limits.zero_comp]
  exact inessential_iff_zero_source_same_target _ _ _ _ _ _ h
end TowerExactTarget

#print axioms earlier_domain_necessary
#print axioms no_extension_outside_domain
#print axioms inessential_iff_zero_in_same_target_coset
#print axioms inessential_iff_zero_source_same_target
#print axioms tower_inessential_iff_zero_source_same_target
end Prop620IndependentReview
