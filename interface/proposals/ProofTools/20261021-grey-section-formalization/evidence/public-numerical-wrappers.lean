module

public import KIP126.ProofTools.Language
public import KIP126.E2Computation.Standard
import all KIP126.ProofTools.Paper.NumericalExamples

/-! Scheme B: unapproved mathematical labels and exact numerical conclusions.
Only this review evidence contains the public declarations. The four labels
come from the fixed sphere archive and its actual E2 comparison. -/

@[expose] section
namespace KIP126.ProofTools.Standard
open CategoryTheory KIP126.Classical.Adams KIP126.Core.SpectralSequence
open KIP126.StableHomotopy KIP126.AdamsSynthetic KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Standard (model)
open KIP126.Computation KIP126.Computation.Standard
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- The specified archive generator named p at (4,37), in actual sphere E2. -/
@[no_expose] public def p : model.classical.sphere.Page 2 (4,37) :=
  KIP126.ProofTools.Paper.NumericalExamples.p

/-- The specified archive generator named d_0 at (4,18), in actual sphere E2. -/
@[no_expose] public def d0 : model.classical.sphere.Page 2 (4,18) :=
  KIP126.ProofTools.Paper.NumericalExamples.d0

/-- The actual product of the specified standard h0 and archived p. -/
public def h0p : model.classical.sphere.Page 2 (5,38) := product h0 p

/-- The actual product of the specified standard h0 and archived d0. -/
public def h0d0 : model.classical.sphere.Page 2 (5,19) := product h0 d0

/-- Exact, nonzero classical conclusion of Example 6.7. The proof uses the
registered independent literature d3 and the one-dimensional E2 target. -/
public theorem paper6_7_classical_d3 :
    HasNonzeroDifferential model.classical.sphere 3 (2,36) (5,38)
      (KIP126.Literature.Standard.hiProduct 2 5) h0p := by
  change HasNonzeroDifferential model.classical.sphere 3 (2,36) (5,38)
    (KIP126.Literature.Standard.hiProduct 2 5)
    KIP126.ProofTools.Paper.NumericalExamples.h0p
  exact KIP126.ProofTools.Paper.NumericalExamples.paper6_7_classical_d3

/-- Only the actual nonzero d3 in Example 6.8; this does not assert its
infinite extension witnesses, essential crossing, or two full lifts. -/
public theorem paper6_8_classical_d3 :
    HasNonzeroDifferential model.classical.sphere 3 (2,17) (5,19)
      (KIP126.Literature.Standard.hiProduct 0 4) h0d0 := by
  change HasNonzeroDifferential model.classical.sphere 3 (2,17) (5,19)
    (KIP126.Literature.Standard.hiProduct 0 4)
    KIP126.ProofTools.Paper.NumericalExamples.h0d0
  exact KIP126.ProofTools.Paper.NumericalExamples.paper6_8_classical_d3

-- Independent checks of the mathematical names and their fixed archive IDs.
example : archive.generators.record (⟨26,by decide⟩ : Fin archive.generators.count) =
    ("p",4,37) := by rfl
example : archive.generators.record (⟨8,by decide⟩ : Fin archive.generators.count) =
    ("d_0",4,18) := by rfl

-- The complete original classical conclusion, obtained without a new API root.
example : KIP126.ProofTools.DifferentialAt model .sphere 3 (2,36) (5,38)
    (KIP126.Literature.Standard.hiProduct 2 5) h0p :=
  ⟨by decide, paper6_7_classical_d3.toHasDifferential⟩

-- The locally refuted zero conclusion, obtained without a duplicate API root.
example : ¬ KIP126.ProofTools.DifferentialAt model .sphere 3 (2,17) (5,19)
    (KIP126.Literature.Standard.hiProduct 0 4) 0 :=
  by
    rintro ⟨_,hzero⟩
    change HasDifferential model.classical.sphere 3 (2,17) (5,19)
      (KIP126.Literature.Standard.hiProduct 0 4) 0 at hzero
    obtain ⟨hdeg,xr,yr,hx,_,hd,hyne⟩ := paper6_8_classical_d3
    obtain ⟨hdeg0,xr0,yr0,hx0,hy0,hd0⟩ := hzero
    have hxx : xr = xr0 := hx.unique hx0
    have hyy : yr = yr0 := hd.symm.trans (by simpa only [hxx] using hd0)
    exact hyne (hyy.trans (hy0.unique (RepresentsOnPage.zero hy0.1)))

end
end KIP126.ProofTools.Standard
end

set_option pp.universes true
#check KIP126.ProofTools.Standard.p
#print axioms KIP126.ProofTools.Standard.p
#check KIP126.ProofTools.Standard.d0
#print axioms KIP126.ProofTools.Standard.d0
#check KIP126.ProofTools.Standard.h0p
#print axioms KIP126.ProofTools.Standard.h0p
#check KIP126.ProofTools.Standard.h0d0
#print axioms KIP126.ProofTools.Standard.h0d0
#check KIP126.ProofTools.Standard.paper6_7_classical_d3
#print axioms KIP126.ProofTools.Standard.paper6_7_classical_d3
#check KIP126.ProofTools.Standard.paper6_8_classical_d3
#print axioms KIP126.ProofTools.Standard.paper6_8_classical_d3
