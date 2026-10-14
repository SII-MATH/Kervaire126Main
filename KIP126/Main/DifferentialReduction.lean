module

public import KIP126.Main.H6SquarePermanent
import all KIP126.Main.Internal.PageCalculus

/-! The actual-model target recorded in
Main/Solution/DifferentialReduction/only_d12_differential_reduction at
bbac1fc05843 (MIT; see the retained source LICENSE). Here it is a downstream corollary of Theorem 7.1,
not an input used to prove that theorem. No additional proof hole is needed. -/

@[expose] section
namespace KIP126.Main
open KIP126.Core.SpectralSequence
open KIP126.AdamsSynthetic.Standard (model)

/-- No nonzero differential leaves the standard product h6*h6. -/
public theorem h6_square_no_outgoing (r : ℤ) (hr : 2 ≤ r)
    (q : ℤ × ℤ) (y : model.classical.sphere.Page 2 q) :
    ¬ HasNonzeroDifferential model.classical.sphere r (2,128) q
      model.standardClasses.standardH6Square y := by
  intro hd
  apply Internal.nonzero_differential_not_permanent (E := model.classical.sphere)
    (by rw [model.classical.firstPage KIP126.StableHomotopy.SphereSpectrum]; exact hr)
    hd h6_sq_permanent

/-- The former differential-reduction target, on the fixed standard system.
The proof follows the final theorem and is not part of its dependency chain. -/
public theorem only_d12_differential_reduction :
    (∀ (r : ℤ), 2 ≤ r → r ≠ 12 →
      ∀ y : model.classical.sphere.Page 2 (2+r,127+r),
        ¬ HasNonzeroDifferential model.classical.sphere r (2,128) (2+r,127+r)
          model.standardClasses.standardH6Square y) ∧
    ((∃ y : model.classical.sphere.Page 2 (14,139),
      HasNonzeroDifferential model.classical.sphere 12 (2,128) (14,139)
        model.standardClasses.standardH6Square y) ↔ D12) ∧
    (¬ D12 ↔ H6SquarePermanent) := by
  have hn : ¬ D12 := fun hd => (d12_necessary hd).1 h6_sq_permanent
  refine ⟨fun r hr _ y => h6_square_no_outgoing r hr _ y, ?_, ?_⟩
  · constructor
    · rintro ⟨y, hy⟩
      exact False.elim (h6_square_no_outgoing 12 (by decide) _ y hy)
    · intro hd
      exact False.elim (hn hd)
  · exact ⟨fun _ => h6_sq_permanent, fun _ => hn⟩

end KIP126.Main
