module

public import KIP126.Def.Synthetic.Detection.Predicates
public import KIP126.Def.SpectralSequence.Convergence.Vanishing.Proofs

@[expose] public section

/-! The graded-vanishing argument on the same actual Adams tower used by
detection. Finite intervals need only convergence; a zero tail additionally
uses separation of actual homotopy classes. -/

namespace KIP126.Synthetic.SpectralSequence

open CategoryTheory CategoryTheory.Limits KIP126.SpectralSequence
open KIP126.StableHomotopy KIP126.Synthetic.Context

universe u v
variable {Syn : Type u} [SyntheticCategory.{u, v} Syn]
  [HasFunctorialCofiber (C := Syn)] {H : Syn} {unit : S_0_0 ⟶ H}
  {F : SyntheticAdamsFamily Syn} {X : Syn}

/-- Convert infinity-page vanishing through the specified convergence
identification, retaining both the actual stem and weight. -/
theorem TowerConvergence.associatedGraded_isZero_of_eInfty_isZero
    (c : TowerConvergence unit F X) (s m w : ℤ)
    (h : IsZero (((F.obj X).sequence.ssData (s, m + s, w)).eInfty)) :
    IsZero ((towerFiltration unit X).associatedGraded s (m, w)) := by
  have h' := h.of_iso (c.identification (s, m + s, w)).symm
  simpa only [add_sub_cancel_right] using h'

/-- A gap in the infinity page identifies filtration membership at its
two endpoints, including zero classes and all higher-filtration errors. -/
theorem TowerConvergence.filtrationAtLeast_iff_of_eInfty_isZero
    (c : TowerConvergence unit F X) (s t m w : ℤ) (hst : s ≤ t)
    (h : ∀ j : ℤ, s ≤ j → j < t →
      IsZero (((F.obj X).sequence.ssData (j, m + j, w)).eInfty))
    (a : BiHom m w X) :
    FiltrationAtLeast unit s a ↔ FiltrationAtLeast unit t a := by
  have heq := (towerFiltration unit X).eq_of_associatedGraded_isZero
    s t (m, w) hst (fun j hj ht =>
      c.associatedGraded_isZero_of_eInfty_isZero j m w (h j hj ht))
  have hsub := congrArg (ModuleCat.subobjectModule (syntheticHomotopy X (m, w))) heq
  simp only [towerFiltration, OrderIso.apply_symm_apply] at hsub
  change a ∈ towerFiltrationSubmodule unit X s (m, w) ↔
    a ∈ towerFiltrationSubmodule unit X t (m, w)
  rw [hsub]

/-- A whole zero infinity-page tail forces an actual class to vanish
when the same homotopy filtration is separated. The hypothesis does not
assert that any finite filtration layer is zero. -/
theorem TowerConvergence.eq_zero_of_eInfty_isZero_ge
    (c : TowerConvergence unit F X) (s : ℕ) (m w : ℤ)
    (hsep : ∀ a : BiHom m w X,
      (∀ j : ℕ, FiltrationAtLeast unit j a) → a = 0)
    (h : ∀ j : ℤ, (s : ℤ) ≤ j →
      IsZero (((F.obj X).sequence.ssData (j, m + j, w)).eInfty))
    (a : BiHom m w X) (ha : FiltrationAtLeast unit s a) : a = 0 := by
  apply hsep a
  intro j
  by_cases hj : s ≤ j
  · exact (c.filtrationAtLeast_iff_of_eInfty_isZero s j m w (by omega)
      (fun q hq _ => h q hq) a).mp ha
  · exact towerFiltrationSubmodule_antitone unit X (m, w) (by omega) ha

end KIP126.Synthetic.SpectralSequence
