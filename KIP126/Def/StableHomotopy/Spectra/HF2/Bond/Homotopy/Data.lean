module

public import KIP126.Def.StableHomotopy.Spectra.HF2.Bond.CubicalComparison
public import KIP126.Def.StableHomotopy.Spectra.HF2.Bond.DegreeZero
public import KIP126.Def.StableHomotopy.Spectra.HF2.Bond.Connected.Proofs
public import KIP126.Def.StableHomotopy.Spectra.Prespectrum.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Spectra.HF2Bond
open CategoryTheory Opposite
open scoped unitInterval
set_option backward.isDefEq.respectTransparency false

variable (hb : ∀ n r, Function.Bijective (bondHomotopyMap n r))

/-- The actual diagonal homotopy groups, calculated by inverse structure maps
and the specified degree-zero coefficient equivalence. The hypothesis concerns
the already constructed structure maps, not an independent homotopy model. -/
noncomputable def coefficientDiagonalEquiv : (n : ℕ) →
    HomotopyGroup.Pi n (hf2RealizationLevel n) (hf2RealizationLevel n).point ≃ ZMod 2
  | 0 => coefficientZeroPiZeroEquiv
  | n+1 => (Equiv.ofBijective (bondHomotopyMap n n) (hb n n)).symm.trans
      (coefficientDiagonalEquiv n)

noncomputable def coefficientDiagonalRepresentative
    (a : Prespectrum.Representative hf2RealizationPrespectrum 0) : ZMod 2 := by
  obtain ⟨n,r,hr,p⟩ := a
  have h : r = n := by omega
  subst r
  exact coefficientDiagonalEquiv hb n ⟦p⟧

/-- The canonical inclusion of a diagonal level homotopy class into the
actual stable quotient. -/
noncomputable def coefficientDiagonalClass (n : ℕ) :
    HomotopyGroup.Pi n (hf2RealizationLevel n) (hf2RealizationLevel n).point →
      Prespectrum.StableHomotopy hf2RealizationPrespectrum 0 :=
  Quotient.lift (fun p => Prespectrum.loopClass hf2RealizationPrespectrum 0 n n (by omega) p)
    (fun p q h => Prespectrum.loopClass_eq_of_homotopic (X := hf2RealizationPrespectrum) (d := 0) n n (by omega) p q h)

end KIP126.StableHomotopy.Spectra.HF2Bond
