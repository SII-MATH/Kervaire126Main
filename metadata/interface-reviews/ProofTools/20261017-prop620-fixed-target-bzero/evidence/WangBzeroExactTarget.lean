module

public import KIP126.ProofTools.Operations
import all KIP126.ProofTools.ConvergenceOperations

/-! Local evidence for the fixed-target part of Proposition 6.20.
The results below do not assert the nonliftability of the correcting source,
nor do they prove the general-b to b=0 reduction. -/

@[expose] section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace Prop620WangBzeroEvidence
open CategoryTheory CategoryTheory.Limits KIP126.StableHomotopy
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Core.SpectralSequence KIP126.Kervaire.Route
noncomputable section
universe u v w

section Filtered
variable {Acat : Type u} [Category.{v} Acat] [Abelian Acat]
  {ι : Type w} {A B : ι → Acat} {F : Filtration A} {G : Filtration B}

/-- Inessentiality for a known equation means that the same target is a
homogeneous solution for the same filtered map. -/
public theorem inessential_iff_zero_source_same_target
    (f : FilteredMorphism F G) (k : ι) (s n : ℤ) {T : Acat}
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

/-- This is the actual higher-source representative form: the specified
target is retained, with a source lift in filtration s+1. -/
public theorem inessential_iff_higher_source_same_target
    (f : FilteredMorphism F G) (k : ι) (s n : ℤ) {T : Acat}
    (x : T ⟶ F.associatedGraded s k)
    (y : T ⟶ G.associatedGraded (s+n) k)
    (h : FilteredMapExtension.Relation f k s n x y) :
    ¬ FilteredMapExtension.Essential f k s n x y ↔
      0 ≤ n ∧ ∃ (a : T ⟶ Subobject.underlying.obj (F.F (s+1) k))
        (b : T ⟶ Subobject.underlying.obj (G.F (s+n) k)),
        b ≫ G.toAssociatedGraded (s+n) k = y ∧
        a ≫ (F.F (s+1) k).arrow ≫ f.map k =
          b ≫ (G.F (s+n) k).arrow := by
  rw [inessential_iff_zero_source_same_target f k s n x y h]
  exact FilteredMapExtension.mem_indeterminacy_iff
end Filtered

section Tower
variable {Syn : Type u} [SyntheticCategory.{u,v} Syn]
  [HasFunctorialCofiber (C := Syn)]
  {H : Syn} {unit : S_0_0 ⟶ H} {F : SyntheticAdamsFamily Syn}
  {P : SyntheticTowerPresentation unit F} {X Y : Syn} {g : X ⟶ Y}
  {cx : SyntheticTowerConvergence P X} {cy : SyntheticTowerConvergence P Y}

private theorem elementMap_zero {A : ModuleCat.{v} ℤ} :
    elementMap (0 : A) = 0 := by
  ext z
  simp [elementMap]

private theorem elementMap_one {A : ModuleCat.{v} ℤ} (a : A) :
    elementMap a (ULift.up (1 : ℤ)) = a := by
  simp [elementMap, one_smul]

/-- Same-map, same-degree, same-target criterion in the actual tower language. -/
public theorem tower_inessential_iff_zero_source_same_target
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

/-- Actual homotopy representatives realizing the fixed target y, with the
source strictly above s. There is no arbitrary or unrelated target y'. -/
public theorem tower_inessential_iff_higher_source_same_target
    (M : ConvergentMap F g cx.toConvergence cy.toConvergence)
    (p : ℤ × ℤ) (s n : ℤ)
    (x : ((F.obj X).sequence.ssData (s,p.1+s,p.2)).eInfty)
    (y : ((F.obj Y).sequence.ssData (s+n,p.1+(s+n),p.2)).eInfty)
    (h : TowerExtensionEquation M p s n x y) :
    ¬ TowerEssentialExtension M p s n x y ↔
      0 ≤ n ∧ ∃
        (a : (Subobject.underlying.obj ((P.filtration X).F (s+1) p) : ModuleCat.{v} ℤ))
        (b : (Subobject.underlying.obj ((P.filtration Y).F (s+n) p) : ModuleCat.{v} ℤ)),
        ((P.filtration X).F (s+1) p).arrow a ≫ g =
          ((P.filtration Y).F (s+n) p).arrow b ∧
        (P.filtration Y).toAssociatedGraded (s+n) p b =
          (KIP126.ProofTools.Operations.infinityGradedIso cy p (s+n)).hom y := by
  have hrel : FilteredMapExtension.Relation M.filteredMap p s n
      (toGraded cx.toConvergence (by simp [SyntheticTowerConvergence.toConvergence])
        (elementMap x))
      (toGraded cy.toConvergence (by simp [SyntheticTowerConvergence.toConvergence])
        (elementMap y)) := h
  rw [show (¬ TowerEssentialExtension M p s n x y) ↔ _ from
    inessential_iff_higher_source_same_target _ _ _ _ _ _ hrel]
  simp only [KIP126.ProofTools.Internal.toGraded_element]
  constructor
  · rintro ⟨hn,a,b,hb,he⟩
    refine ⟨hn,a (ULift.up 1),b (ULift.up 1),?_,?_⟩
    · have hh := ConcreteCategory.congr_hom he (ULift.up (1 : ℤ))
      have hf := ConcreteCategory.congr_hom (M.filteredMap_map p)
        (((P.filtration X).F (s+1) p).arrow (a (ULift.up 1)))
      exact hf.symm.trans hh
    · have hh := ConcreteCategory.congr_hom hb (ULift.up (1 : ℤ))
      change (P.filtration Y).toAssociatedGraded (s+n) p (b (ULift.up 1)) =
        elementMap ((KIP126.ProofTools.Internal.infinityGradedIso cy p (s+n)).hom y)
          (ULift.up (1 : ℤ)) at hh
      rw [elementMap_one] at hh
      exact hh
  · rintro ⟨hn,a,b,he,hb⟩
    refine ⟨hn,elementMap a,elementMap b,?_,?_⟩
    · rw [← KIP126.AdamsSynthetic.elementMap_comp]
      exact congrArg elementMap hb
    · rw [← Category.assoc,← KIP126.AdamsSynthetic.elementMap_comp,
        ← KIP126.AdamsSynthetic.elementMap_comp,
        ← KIP126.AdamsSynthetic.elementMap_comp]
      have hf := ConcreteCategory.congr_hom (M.filteredMap_map p)
        (((P.filtration X).F (s+1) p).arrow a)
      exact congrArg elementMap (hf.trans he)
end Tower

section FiniteWitness
variable {C : Type u} [StableHomotopyCategory.{u,v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w,v} Syn]
  [HasFunctorialCofiber (C := Syn)] (D : Model C Syn)

/-- Specialization to the actual finite-page witness. Both sides use its
precise quotient map, tridegrees and target; D remains a model parameter. -/
public theorem finite_witness_inessential_iff_zero_source_same_target
    (X Y : ClassicalObject) (f : X.obj D.auxiliary ⟶ Y.obj D.auxiliary)
    (r : ℕ) (n s t : ℤ) (x y)
    (W : FiniteExtensionWitness D X Y f r n s t x y) :
    ¬ W.Essential ↔ TowerExtensionEquation
      (D.convergentMap (.quotient (r-1) (extensionSourceObject D X Y f))
        (.quotient (r-1) (.nu Y)) (finiteExtensionMap D X Y f (r-1)))
      (t-s,t+normalizedExponent D.classicalTower f) s n 0 W.target := by
  exact tower_inessential_iff_zero_source_same_target _ _ _ _ _ _ W.equation
end FiniteWitness

#print axioms inessential_iff_zero_source_same_target
#print axioms inessential_iff_higher_source_same_target
#print axioms tower_inessential_iff_zero_source_same_target
#print axioms tower_inessential_iff_higher_source_same_target
#print axioms finite_witness_inessential_iff_zero_source_same_target
end
end Prop620WangBzeroEvidence
