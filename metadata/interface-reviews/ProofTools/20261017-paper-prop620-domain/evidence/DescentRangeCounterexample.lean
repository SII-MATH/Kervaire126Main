import KIP126.ProofTools.Operations

open CategoryTheory CategoryTheory.Limits KIP126.StableHomotopy
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Core.SpectralSequence KIP126.Kervaire.Route
open KIP126.ProofTools.Operations

namespace AimPaperCounteraudit
universe u v w
variable {C : Type u} [StableHomotopyCategory.{u,v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w,v} Syn]
  [HasFunctorialCofiber (C := Syn)] (D : Model C Syn)
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

private theorem module_map_zero {A B : ModuleCat.{v} ℤ} (f : A ⟶ B) : f (0 : A) = 0 := f.hom.map_zero

private theorem regrade_zero {A : SyntheticAdamsSS.{v}} {i j : Tridegree}
    (h : i = j) : regradeE2 h (0 : A.E₂ i) = 0 := by
  subst j
  rfl

private theorem target_label_zero (Y : ClassicalObject) (s t : ℤ) (k : ℕ) :
    targetNuLabel D Y s t k 0 = 0 := by
  have cast_zero (A : SyntheticAdamsSS.{v}) (s t w w' : ℤ) (hw : w=w')
      (he : (A.E₂ (s,t,w) : Type v) = (A.E₂ (s,t,w') : Type v)) : he.mp 0 = 0 := by
    subst w'
    rfl
  simp only [targetNuLabel, map_zero]
  rw [cast_zero _ s t (t+0-k) (t-k) (by simp)]
  exact map_zero _

/-- Every valid position admits its zero extension in the same supplied model. -/
def zero_witness (X Y : ClassicalObject)
    (f : X.obj D.auxiliary ⟶ Y.obj D.auxiliary)
    (r : ℕ) (n s t : ℤ) (hr : 2 ≤ r)
    (hl : (normalizedExponent D.classicalTower f : ℤ) ≤ n)
    (hu : n ≤ (r:ℤ)-2+normalizedExponent D.classicalTower f) :
    FiniteExtensionWitness D X Y f r n s t 0 0 := by
  refine {
    page_ge_two := hr
    length_lower := hl
    length_upper := hu
    source_cycle := ⟨0, RepresentsOnPage.zero (by exact_mod_cast hr)⟩
    target_cycle := ⟨0, RepresentsOnPage.zero (by omega)⟩
    source := 0
    target := 0
    source_rep := ?_
    target_rep := ?_
    equation := ?_ }
  · have hz : finiteSourceForExtension D X Y f (r-1) s t 0 = 0 := by
      simp only [finiteSourceForExtension, finiteNuLabel, map_zero, module_map_zero, module_map_zero, regrade_zero]
    rw [hz]
    exact HasInfinityRepresentative.zero _ 2 (by decide) _
  · have hz : finiteTargetForExtension D X Y f (r-1) n s t hl 0 = 0 := by
      simp only [finiteTargetForExtension, finiteTargetLabel, target_label_zero,
        map_zero, module_map_zero, module_map_zero, regrade_zero]
    rw [hz]
    exact HasInfinityRepresentative.zero _ 2 (by decide) _
  · apply (tower_extension_iff _ _ _ _ _ _).mpr
    refine ⟨by omega, 0, 0, ?_, ?_, ?_⟩
    · simp only [map_zero, Limits.zero_comp]
    · simp only [map_zero]
    · simp only [map_zero]

/-- Literal all-earlier-page descent already fails for zero representatives. -/
theorem all_earlier_descent_counterexample (X Y : ClassicalObject)
    (f : X.obj D.auxiliary ⟶ Y.obj D.auxiliary) (s t : ℤ) :
    FiniteExtension D X Y f 3 (normalizedExponent D.classicalTower f + 1) s t 0 0 ∧
    ¬ FiniteExtension D X Y f 2 (normalizedExponent D.classicalTower f + 1) s t 0 0 := by
  constructor
  · exact ⟨zero_witness D X Y f 3 _ s t (by decide) (by omega) (by omega)⟩
  · rintro ⟨W⟩
    have hu := W.length_upper
    omega

#print axioms AimPaperCounteraudit.zero_witness
#print axioms AimPaperCounteraudit.all_earlier_descent_counterexample
end
end AimPaperCounteraudit
