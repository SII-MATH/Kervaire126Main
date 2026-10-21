module

public import KIP126.ProofTools.Language

/-!
# Mahowald--Leibniz composition under finite-layer surjectivity

These definitions specify Mahowald--Leibniz composition under finite-layer surjectivity
in the fixed model; they do not prove it.
The boundary is constructed from the selected normalized map, rather than
supplied as a free operation. Its identification with the Ext boundary of
the homology short exact sequence remains a separate comparison.
-/

@[expose] section
namespace KIP126.ProofTools.Standard
open CategoryTheory
open KIP126.StableHomotopy KIP126.Synthetic.Context
open KIP126.Synthetic.SpectralSequence KIP126.AdamsSynthetic
open KIP126.AdamsSynthetic.Standard KIP126.Kervaire.Route
open KIP126.Literature
noncomputable section

/-- The first-quotient operation of the selected normalized f with e(f)=1.
This is not the ordinary E₂ page map of f. Calling it the Ext connecting
homomorphism additionally requires the triangle/Ext comparison. -/
public def cofiberFirstQuotientBoundary
    (T : TriangleData model.auxiliary)
    (hef : normalizedExponent model.classicalTower T.f = 1)
    (s t : ℤ) (x : Ambient model T.X (s,t)) :
    Ambient model T.Y (s+1,t+1) :=
  let F : (SyntheticCategory.biShift (Syn := SyntheticSpectrum) (0,1)).obj
      (model.nu.functor.obj (T.X.obj model.auxiliary)) ⟶
      model.nu.functor.obj (T.Y.obj model.auxiliary) := by
    simpa only [hef, Nat.cast_one] using (model.normalizedMap T.X T.Y T.f).map
  let a := (model.firstQuotient T.X 1 s t).symm x
  let b := a ≫ XModLambdaN.map F 1 ≫
    XModLambdaN.map (SyntheticCategory.biShift_zero.inv.app
      (model.nu.functor.obj (T.Y.obj model.auxiliary))) 1
  model.firstQuotient T.Y 0 (s+1) (t+1)
    (homotopyRegrade (by omega) (by omega) b)

/-- The finite-layer surjectivity condition for Mahowald--Leibniz composition,
using the actual h page
map and the fixed tower suspension comparison. All boundary denominators
are R+j-1, including the final j=K-1 layer. -/
public def MahowaldLeibnizFiniteLayerSurjectivity
    (T : TriangleData model.auxiliary) (R K : ℕ) (s t : ℤ) : Prop :=
  ∀ j : ℕ, 1 ≤ j → j < K →
    ∀ a : Ambient model T.X (s+R+j,t+R+j-1),
      IsCycle model T.X ((K:ℤ)-j) _ a →
      ∃ z : Ambient model T.Z (s+R+j,t+R+j),
        IsCycle model T.Z ((K:ℤ)-j) _ z ∧
        ∃ b : Ambient model T.X (s+R+j,t+R+j-1),
          (model.classicalSuspension T.X).DesuspendsClass (s+R+j) (t+R+j)
            ((model.classical.functor.map T.h).pageMap 2 (s+R+j,t+R+j) z) b ∧
          Congruent model T.X ((R:ℤ)+j-1) _ a b

/-- The complete fixed-model Mahowald--Leibniz proposition under finite-layer surjectivity,
allowing y=0. The selected
normalized triangle must be compatible; no f-extension, source nonvanishing,
output survival, or target permanence is an input. This definition supplies
no proof. It ranges over the project's classical object family, and uses the
actual first-quotient boundary, not an independently supplied Ext operation. -/
public def FiniteLayerSurjectivityMahowaldLeibnizStatement
    (T : TriangleData model.auxiliary)
    (hef : normalizedExponent model.classicalTower T.f = 1)
    (heg : normalizedExponent model.classicalTower T.g = 0)
    (heh : normalizedExponent model.classicalTower T.h = 0) : Prop :=
  ∀ (_hT : NormalizedTriangleCompatible model T (by simp [hef, heg, heh]))
    (R K : ℕ), 2 ≤ R → 2 ≤ K → ∀ (s t : ℤ)
    (x : Ambient model T.X (s,t))
    (z : Ambient model T.Z (s+R,t+R))
    (v : Ambient model T.Y (s+R+K,t+R+K-1)),
    IsCycle model T.X ((R:ℤ)-1) _ x →
    IsCycle model T.Z ((K:ℤ)-1) _ z →
    (∃ u : Ambient model T.X (s+R,t+R-1),
      (model.classicalSuspension T.X).DesuspendsClass (s+R) (t+R)
        ((model.classical.functor.map T.h).pageMap 2 (s+R,t+R) z) u ∧
      DifferentialAt model T.X R (s,t) (s+R,t+R-1) x u) →
    DifferentialAt model T.Z K (s+R,t+R) (s+R+K,t+R+K-1) z
      ((model.classical.functor.map T.g).pageMap 2 (s+R+K,t+R+K-1) v) →
    MahowaldLeibnizFiniteLayerSurjectivity T R K s t →
    let y := cofiberFirstQuotientBoundary T hef s t x
    IsCycle model T.Y ((R:ℤ)+K-2) (s+1,t+1) y ∧
    DifferentialAt model T.Y ((R:ℤ)+K-1)
      (s+1,t+1) (s+R+K,t+R+K-1) y v

end
end KIP126.ProofTools.Standard
