module

public import KIP126.AdamsSynthetic.AdamsFiltration
public import KIP126.AdamsSynthetic.Mapping

@[expose] section

/-! Detection of maps belongs to their actual mapping spectrum. This corrects
the old unqualified assertion about the target spectrum of an arbitrary map.
Finite exact filtration uses the explicit separation obligation; an odd-torsion
nonzero map is not silently treated as a nonzero E∞ class. -/

namespace KIP126.AdamsSynthetic
open CategoryTheory CategoryTheory.Limits
open KIP126.StableHomotopy KIP126.Classical.Adams KIP126.Core.SpectralSequence
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {C : Type u} [StableHomotopyCategory.{u,v} C]
  [HasFunctorialCofiber (C := C)]
  {H : ModTwoCoefficients C} {A : ClassicalAdamsFamily C}
  {P : ClassicalTowerPresentation H.unit A}

/-- One common Z∞ representative with its nonzero E∞ image, and its image
under the actual convergence identification. -/
public structure NonzeroClassicalDetection {X : C} (c : ClassicalTowerConvergence P X)
    (p : ℤ × ℤ) (a : HomotopyGroup (p.2-p.1) X) where
  representative : (Subobject.underlying.obj (((A.obj X).ssData p).Z ⊤) : ModuleCat ℤ)
  nonzero : (((A.obj X).ssData p).pageπ ⊤) representative ≠ 0
  filteredClass : (Subobject.underlying.obj ((P.tower X).filtration.F p.1 (p.2-p.1)) : ModuleCat ℤ)
  homotopy_eq : ((P.tower X).filtration.F p.1 (p.2-p.1)).arrow filteredClass = a
  comparison_eq : (c.identification p).hom (((A.obj X).ssData p).pageπ ⊤ representative) =
    (P.tower X).filtration.toAssociatedGraded p.1 (p.2-p.1) filteredClass

public def NonzeroClassicalDetection.pageElement {X : C} {c : ClassicalTowerConvergence P X}
    {p : ℤ × ℤ} {a : HomotopyGroup (p.2-p.1) X} (w : NonzeroClassicalDetection c p a) :
    (A.obj X).Page 2 p :=
  (Subobject.ofLE _ _ (((A.obj X).ssData p).Z_anti le_top) ≫
    ((A.obj X).ssData p).pageπ (↑(2-(A.obj X).r₀).toNat : WithTop ℕ)) w.representative

public theorem NonzeroClassicalDetection.detects {X : C} {c : ClassicalTowerConvergence P X}
    {p : ℤ × ℤ} {a : HomotopyGroup (p.2-p.1) X} (w : NonzeroClassicalDetection c p a) :
    ClassicalDetects c p w.pageElement a :=
  ⟨w.representative, rfl, w.filteredClass, w.homotopy_eq, w.comparison_eq⟩

/-- Exact actual filtration yields a nonzero E∞ representative under the
given convergence. This is a consequence of the quotient and comparison,
not an additional existence assumption. -/
public theorem nonzeroClassicalDetection_of_exact {X : C}
    (c : ClassicalTowerConvergence P X) (p : ℤ × ℤ)
    (a : HomotopyGroup (p.2-p.1) X)
    (ha : a ∈ (P.tower X).filtrationSubmodule p.1 (p.2-p.1))
    (ha' : a ∉ (P.tower X).filtrationSubmodule (p.1+1) (p.2-p.1)) :
    Nonempty (NonzeroClassicalDetection c p a) := by
  have hmem : a ∈ ModuleCat.subobjectModule _
      ((P.tower X).filtration.F p.1 (p.2-p.1)) := by
    simpa only [AbstractAdamsTower.filtration, OrderIso.apply_symm_apply] using ha
  change ∃ b, ((P.tower X).filtration.F p.1 (p.2-p.1)).arrow.hom b = a at hmem
  obtain ⟨b,hb⟩ := hmem
  have hgraded : (P.tower X).filtration.toAssociatedGraded p.1 (p.2-p.1) b ≠ 0 := by
    intro hz
    have hnext := ((P.tower X).filtration.toAssociatedGraded_eq_zero_iff
      p.1 (p.2-p.1) b).mp hz
    apply ha'
    change ((P.tower X).filtration.F p.1 (p.2-p.1)).arrow.hom b ∈
      ModuleCat.subobjectModule _ ((P.tower X).filtration.F (p.1+1) (p.2-p.1)) at hnext
    rw [hb] at hnext
    simpa only [AbstractAdamsTower.filtration, OrderIso.apply_symm_apply] using hnext
  let e := (c.identification p).inv
    ((P.tower X).filtration.toAssociatedGraded p.1 (p.2-p.1) b)
  have he : (c.identification p).hom e =
      (P.tower X).filtration.toAssociatedGraded p.1 (p.2-p.1) b := by
    change ((c.identification p).inv ≫ (c.identification p).hom) _ = _
    rw [Iso.inv_hom_id]
    rfl
  have hene : e ≠ 0 := by
    intro hezero
    apply hgraded
    rw [← he, hezero, map_zero]
  haveI : Epi (((A.obj X).ssData p).pageπ ⊤) :=
    inferInstanceAs (Epi (cokernel.π _))
  obtain ⟨z,hz⟩ := (ModuleCat.epi_iff_surjective
    (((A.obj X).ssData p).pageπ ⊤)).mp inferInstance e
  exact ⟨⟨z, by simpa only [hz] using hene, b, hb, by rw [hz]; exact he⟩⟩

/-- Actual stable maps are represented in the internal hom, with degree
transport made explicit at the diagonal Adams bidegree. -/
public def mappingClass (B : ClosedSymmetricTensorTriangulated C)
    {X Y : C} (f : X ⟶ Y) (s : ℤ) :
    HomotopyGroup (s-s) (mappingSpectrum B X Y) :=
  eqToHom (congrArg (Sphere (C := C)) (sub_self s)) ≫
    (mappingHomotopyZeroEquiv B X Y).symm f

private theorem homotopy_filtration_transport {X : C}
    (n m s : ℤ) (h : n = m) (a : HomotopyGroup m X) :
    eqToHom (congrArg (Sphere (C := C)) h) ≫ a ∈
        (P.tower X).filtrationSubmodule s n ↔
      a ∈ (P.tower X).filtrationSubmodule s m := by
  subst m
  simp

/-- The nonzero detection witness is derived from exact filtration through
the same mapping-spectrum comparison and canonical convergence. -/
public theorem nonzeroClassicalDetection_of_exact_map
    {B : ClosedSymmetricTensorTriangulated C}
    {S : MappingSpectrumSystem B P (IsFiniteSpectrum (C := C))}
    (comparison : ∀ {X Y : C}, IsFiniteSpectrum X → IsFiniteSpectrum Y →
      ∀ (f : X ⟶ Y) (s : ℤ), MapAdamsFiltration P f s ↔
        (mappingHomotopyZeroEquiv B X Y).symm f ∈
          (P.tower (mappingSpectrum B X Y)).filtrationSubmodule s 0)
    {X Y : C} (hX : IsFiniteSpectrum X) (hY : IsFiniteSpectrum Y)
    (f : X ⟶ Y) (s : ℤ) (hs : ExactMapAdamsFiltration P f s) :
    Nonempty (NonzeroClassicalDetection (S.convergence X Y hX hY) (s,s) (mappingClass B f s)) := by
  apply nonzeroClassicalDetection_of_exact
  · have ha := (comparison hX hY f s).mp hs.1
    exact (homotopy_filtration_transport (P := P) (s-s) 0 s (sub_self s) _).mpr ha
  · intro ha
    apply hs.2
    apply (comparison hX hY f (s+1)).mpr
    exact (homotopy_filtration_transport (P := P) (s-s) 0 (s+1) (sub_self s) _).mp ha

/-- The revised nonzero-map statement requires non-odd-torsion and finite
objects; its nonzero E∞ class detects that very map in its mapping spectrum. -/
public theorem nonzeroClassicalDetection_of_not_odd_map
    {B : ClosedSymmetricTensorTriangulated C}
    {S : MappingSpectrumSystem B P (IsFiniteSpectrum (C := C))}
    (comparison : ∀ {X Y : C}, IsFiniteSpectrum X → IsFiniteSpectrum Y →
      ∀ (f : X ⟶ Y) (s : ℤ), MapAdamsFiltration P f s ↔
        (mappingHomotopyZeroEquiv B X Y).symm f ∈
          (P.tower (mappingSpectrum B X Y)).filtrationSubmodule s 0)
    (separation : FiniteMapSeparation P)
    {X Y : C} (hX : IsFiniteSpectrum X) (hY : IsFiniteSpectrum Y)
    (f : X ⟶ Y) (hf : ¬ IsOddTorsionMap f) :
    ∃ s : ℤ, ExactMapAdamsFiltration P f s ∧
      Nonempty (NonzeroClassicalDetection (S.convergence X Y hX hY) (s,s) (mappingClass B f s)) := by
  obtain ⟨s,hs⟩ := finite_filtration_of_not_odd P separation hX hY f hf
  exact ⟨s,hs,nonzeroClassicalDetection_of_exact_map comparison hX hY f s hs⟩

end
end KIP126.AdamsSynthetic
