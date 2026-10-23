module

public import KIP126.AdamsComputation.Standard
public import KIP126.AdamsComputation.Table.Data
public import KIP126.AdamsComputation.Table.Dimensions

/-! Fixed finite-table delivery on the existing actual objects. The bounded
rows and coordinate obligations come from bbac1fc05843,
LinProgram/Interpretation/Route/{Data,Predicates,Certification}.lean (MIT).
The paper calls these declarations directly. No result package is an input.
Sphere coordinates use the same previously fixed archive and comparison. -/
@[expose] section
namespace KIP126.Computation.Table
open CategoryTheory KIP126.StableHomotopy KIP126.Core.SpectralSequence
open KIP126.AdamsSynthetic.Standard
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

public def object : Raw.Spectrum → Spectrum
  | .sphere => SphereSpectrum
  | .nuCofiber => HasFunctorialCofiber.cofib model.auxiliary.nuMap

public abbrev sequence (o : Raw.Spectrum) := model.classical.obj (object o)
public abbrev Page (o : Raw.Spectrum) (s t : ℕ) := (sequence o).Page 2 (s,t)

public def sphereBasis (s t i : ℕ) : model.classical.sphere.Page 2 (s,t) :=
  if ht : t ≤ 261 then
    if hi : i < Standard.archive.basisCount s t then
      (Standard.coordinates s t ht).symm (Finsupp.single ⟨i,hi⟩ 1)
    else 0
  else 0

/-- The actual Cν basis; the following original table bindings constrain it. -/
public def cofiberBasis (s t i : ℕ) : Page .nuCofiber s t := by
  sorry

public def basis : (o : Raw.Spectrum) → (s t i : ℕ) → Page o s t
  | .sphere, s, t, i => sphereBasis s t i
  | .nuCofiber, s, t, i => cofiberBasis s t i

public def decode (o : Raw.Spectrum) (s t : ℕ) (indices : List ℕ) :
    Option (Page o s t) :=
  if Raw.coordinatesValid Raw.degrees o s t indices then
    some ((indices.map (basis o s t)).sum)
  else none

public def BasisCorrect (d : Raw.Degree) : Prop :=
  ∃ e : Page d.spectrum d.s d.t ≃ₗ[ℤ] (Fin d.monomials.length →₀ ZMod 2),
    ∀ i, e.symm (Finsupp.single i 1) = basis d.spectrum d.s d.t i.val

/-- Exact original finite catalogue lengths, on the existing sphere archive. -/
public theorem basis_count (d : Raw.Degree) (hd : d ∈ Raw.degrees)
    (hs : d.spectrum = .sphere) :
    Standard.archive.basisCount d.s d.t = d.monomials.length := by
  have hbound : ∀ d ∈ Raw.degrees, d.t ≤ 261 := by decide
  rw [archive_dimension d.s d.t (hbound d hd)]
  have hlength : ∀ d ∈ Raw.degrees, d.spectrum = .sphere →
      basisDimension d.s d.t = d.monomials.length := by decide
  exact hlength d hd hs

public theorem cofiber_basis_correct (d : Raw.Degree) (hd : d ∈ Raw.degrees)
    (hs : d.spectrum = .nuCofiber) : BasisCorrect d := by
  sorry

set_option maxRecDepth 10000 in
private theorem table_degree_bound (d : Raw.Degree) (hd : d ∈ Raw.degrees) : d.t ≤ 261 := by
  have all : ∀ d ∈ Raw.degrees, d.t ≤ 261 := by decide
  exact all d hd

public theorem basis_correct (d : Raw.Degree) (hd : d ∈ Raw.degrees) : BasisCorrect d := by
  rcases d with ⟨o,s,t,ms⟩
  cases o with
  | sphere =>
    have hc := basis_count ⟨.sphere,s,t,ms⟩ hd rfl
    have ht := table_degree_bound ⟨.sphere,s,t,ms⟩ hd
    dsimp only at hc ht
    change ∃ e : model.classical.sphere.Page 2 (s,t) ≃ₗ[ℤ] (Fin ms.length →₀ ZMod 2),
      ∀ i, e.symm (Finsupp.single i 1) = sphereBasis s t i.val
    rw [← hc]
    refine ⟨Standard.coordinates s t ht, ?_⟩
    intro i
    simp only [sphereBasis, dif_pos ht, dif_pos i.isLt]
  | nuCofiber => exact cofiber_basis_correct ⟨.nuCofiber,s,t,ms⟩ hd rfl

end
end KIP126.Computation.Table
