module

public import KIP126.Def.ClassicalAdams.TowerNaturality.Morphism.Proofs
public import KIP126.Def.SpectralSequence.Computation.Morphism.Proofs

@[expose] public section

namespace KIP126.Classical.Adams
open CategoryTheory MonoidalCategory KIP126.StableHomotopy
set_option backward.isDefEq.respectTransparency false
universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] {H : C} (unit : 𝟙_ C ⟶ H)
  {X Y : C} (f : X ⟶ Y)

/-- Downstream representative calculations use the genuine layer map. -/
theorem adamsPageInduced_mkQ (r : ℕ) (hr : 1 ≤ r) (s t : ℤ)
    (a : adamsCycles unit X r hr s t) :
    adamsPageInduced unit f r hr s t
        ((adamsCycleBoundaries unit X r hr s t).mkQ a) =
      (adamsCycleBoundaries unit Y r hr s t).mkQ
        (adamsCycleInduced unit f r hr s t a) := rfl

/-- The SSData E₂ map agrees with the constructed quotient-page map. -/
theorem adamsInternalE2Induced_coordinates (p : ℤ × ℤ)
    (x : (adamsTowerInternalSpectralSequence unit X).Page 2 p) :
    (adamsTowerSSDataPageIso unit Y p.1 p.2 0).hom
        (adamsInternalE2Induced unit f p x) =
      adamsPageInduced unit f 2 (by decide) p.1 p.2
        ((adamsTowerSSDataPageIso unit X p.1 p.2 0).hom x) := by
  change (adamsTowerSSDataPageIso unit Y p.1 p.2 0).toLinearEquiv
    ((adamsTowerSSDataPageIso unit Y p.1 p.2 0).toLinearEquiv.symm _) = _
  exact LinearEquiv.apply_symm_apply _ _

/-- Differential equations between actual Adams E₂ representatives are
natural under a spectrum map. The image of either representative may be zero;
this theorem does not preserve nonzero differentials.

The proved layer, cycle and quotient-page maps give a morphism of the
existing internal Adams spectral sequences. Its E₂ map is the specified
`adamsInternalE2Induced`, so representative naturality applies. -/
theorem adamsInternalE2Induced_hasDifferential
    {r : ℤ} {p q : ℤ × ℤ}
    {x : (adamsTowerInternalSpectralSequence unit X).Page 2 p}
    {y : (adamsTowerInternalSpectralSequence unit X).Page 2 q}
    (h : KIP126.SpectralSequence.HasDifferential
      (adamsTowerInternalSpectralSequence unit X) r p q x y) :
    KIP126.SpectralSequence.HasDifferential
      (adamsTowerInternalSpectralSequence unit Y) r p q
      (adamsInternalE2Induced unit f p x)
      (adamsInternalE2Induced unit f q y) := by
  obtain ⟨F, hF⟩ := adamsTowerSSDataMorphism_exists unit f
  obtain ⟨G, hG⟩ := adamsTowerSpectralSequenceMorphism_exists unit f F hF
  have he (p : ℤ × ℤ) (a : (adamsTowerInternalSpectralSequence unit X).Page 2 p) :
      G.pageMap 2 p a = adamsInternalE2Induced unit f p a := by
    apply (adamsTowerSSDataPageIso unit Y p.1 p.2 0).toLinearEquiv.injective
    change (adamsTowerSSDataPageIso unit Y p.1 p.2 0).hom _ =
      (adamsTowerSSDataPageIso unit Y p.1 p.2 0).hom _
    rw [adamsInternalE2Induced_coordinates]
    change (adamsTowerSSDataPageIso unit Y p.1 p.2 0).hom
      (G.toSSDataMorphism.pageMap p (0 : WithTop ℕ) a) = _
    rw [hG]
    exact congrArg (fun k => k a)
      (adamsTowerSSDataMorphism_page_comparison unit f F hF p 0)
  simpa only [he] using G.hasDifferential h

end KIP126.Classical.Adams
