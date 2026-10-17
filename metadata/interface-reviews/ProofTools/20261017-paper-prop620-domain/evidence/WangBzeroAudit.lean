import KIP126.ProofTools.Operations

open CategoryTheory KIP126.StableHomotopy
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Core.SpectralSequence KIP126.Kervaire.Route

namespace WangBzeroIndependentAudit

/-- For the same boundary denominator, a class lifts precisely when its
actual representative belongs to the later cycle subgroup. -/
theorem quotient_range_iff
    {R A : Type*} [Ring R] [AddCommGroup A] [Module R A]
    (L E B : Submodule R A) (hLE : L ≤ E) (hBL : B ≤ L) (x : E) :
    KIP126.Literature.subquotientClass E B x ∈
      Set.range (KIP126.Literature.subquotientMap hLE (le_rfl : B ≤ B)) ↔
      x.val ∈ L := by
  constructor
  · rintro ⟨z, hz⟩
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    change Submodule.Quotient.mk (Submodule.inclusion hLE a) =
      Submodule.Quotient.mk x at hz
    have hz0 : Submodule.Quotient.mk (Submodule.inclusion hLE a - x) =
        (0 : E ⧸ B.comap E.subtype) := by
      rw [Submodule.Quotient.mk_sub, hz, sub_self]
    have hdiff := (Submodule.Quotient.mk_eq_zero _).mp hz0
    change a.val - x.val ∈ B at hdiff
    have hh := L.sub_mem a.property (hBL hdiff)
    simpa only [sub_sub_cancel] using hh
  · intro hx
    refine ⟨KIP126.Literature.subquotientClass L B ⟨x.val,hx⟩, ?_⟩
    rfl

universe u v w
variable {C : Type u} [StableHomotopyCategory.{u,v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w,v} Syn]
  [HasFunctorialCofiber (C := Syn)] (D : Model C Syn)

/-- This specializes the quotient calculation to actual classical cycles
and boundaries in the given model, without assuming a new presentation. -/
theorem actual_cycle_quotient_range_iff
    (X : ClassicalObject) (p : KIP126.Classical.Adams.Bidegree) (early late b : ℤ)
    (hle : early ≤ late)
    (x : KIP126.Literature.cycles D X early p) :
    KIP126.Literature.subquotientClass
      (KIP126.Literature.cycles D X early p)
      (KIP126.Literature.boundaries D X b p) x ∈
      Set.range (KIP126.Literature.quotientMap D X hle (le_rfl : b ≤ b) p) ↔
      x.val ∈ KIP126.Literature.cycles D X late p := by
  exact quotient_range_iff _ _ _
    (KIP126.Literature.cycles_antitone D X p hle)
    (KIP126.ProofTools.Operations.boundaries_le_cycles D X p b late) x

#print axioms quotient_range_iff
#print axioms actual_cycle_quotient_range_iff

end WangBzeroIndependentAudit
