module

public import KIP126.Def.StableHomotopy.Spectra.PointSet

@[expose] public section

namespace KIP126.StableHomotopy.Spectra.Prespectrum
open CategoryTheory Topology
open scoped unitInterval
universe u

/-- The actual path prespectrum, with pointwise structure maps. -/
def pathPrespectrum (X : Prespectrum.{u}) : Prespectrum.{u} where
  level n := { space := TopCat.of C(I,X.level n), point := ContinuousMap.const _ (X.level n).point }
  bond n := (⟨fun z : (C(I,X.level n) × I) × I => X.bond n (z.1.1 z.2,z.1.2),
    (X.bond n).continuous.comp
      ((continuous_fst.fst.eval continuous_snd).prodMk continuous_fst.snd)⟩ :
      C((C(I,X.level n) × I) × I,X.level (n+1))).curry
  bond_point n t := by
    apply ContinuousMap.ext
    intro s
    exact X.bond_point n t
  bond_zero n p := by
    apply ContinuousMap.ext
    intro s
    exact X.bond_zero n (p s)
  bond_one n p := by
    apply ContinuousMap.ext
    intro s
    exact X.bond_one n (p s)

/-- The inclusion of constant paths in every level. -/
def pathConstant (X : Prespectrum.{u}) : X ⟶ pathPrespectrum X where
  level n := (⟨Prod.fst,continuous_fst⟩ : C(X.level n × I,X.level n)).curry
  point _ := rfl
  bond _ _ _ := rfl

/-- Evaluation at a specified parameter commutes strictly with the bonds. -/
def pathEvaluation (X : Prespectrum.{u}) (s : I) : pathPrespectrum X ⟶ X where
  level n := ⟨fun p : C(I,X.level n) => p s,
    (show Continuous (fun p : C(I,X.level n) => p s) from continuous_id.eval continuous_const)⟩
  point _ := rfl
  bond _ _ _ := rfl

end KIP126.StableHomotopy.Spectra.Prespectrum
