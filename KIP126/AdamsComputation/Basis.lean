module

public import KIP126.AdamsComputation.Source

/-! Mathematical archive coordinates without importing a raw CSV or checker.
The project archive is fixed in Computation.Standard. These support types retain
all generator addresses and degrees, every bounded basis monomial and full linear
coordinate equivalences. Mere revision metadata cannot construct these proofs.
Adapted from SphereBasisInterface in Interface/Challenge/Computation/Delivery at
bbac1fc05843bdf2d56057e6114a38839e939378. -/

@[expose] section
namespace KIP126.Computation
open CategoryTheory KIP126.StableHomotopy KIP126.Synthetic.Context
open KIP126.Kervaire.Route KIP126.Classical.Adams
universe u v w

/-- Complete generator catalogue of an archived sphere calculation.
The fixed project list is exposed by Standard.generators; these are source
coordinates rather than a second set of actual page classes. -/
public structure GeneratorCatalogue where
  count : ℕ
  record : Fin count → String × ℕ × ℕ

public abbrev GeneratorCatalogue.degree (G : GeneratorCatalogue) (i : Fin G.count) : ℕ × ℕ :=
  (G.record i).2

/-- A degree-checked source monomial. Both multiplication order and every
factor refer to the same complete generator catalogue. -/
public inductive SourceMonomial (G : GeneratorCatalogue) : ℕ → ℕ → Type
  | one : SourceMonomial G 0 0
  | generator (i : Fin G.count) : SourceMonomial G (G.degree i).1 (G.degree i).2
  | mul {s t s' t' : ℕ} : SourceMonomial G s t → SourceMonomial G s' t' →
      SourceMonomial G (s+s') (t+t')

/-- One mathematical description of the archived data. A producer must supply
its complete lists from the pinned source. All selected names retain the exact
archived id, name and degree, rather than merely an arbitrary name string. -/
public structure SphereArchive where
  generators : GeneratorCatalogue
  atomIndex : Atom → Fin generators.count
  atom_record : ∀ a : Atom, ((atomIndex a).val, generators.record (atomIndex a)) = a.record
  basisCount : ℕ → ℕ → ℕ
  basisMonomial : ∀ s t : ℕ, Fin (basisCount s t) → SourceMonomial generators s t

public theorem SphereArchive.atom_degree (A : SphereArchive) (a : Atom) :
    A.generators.degree (A.atomIndex a) = a.degree :=
  congrArg (fun r : ℕ × String × ℕ × ℕ => r.2.2) (A.atom_record a)

/-- Evaluate each displayed source monomial using this very source product
and unit. No independent evaluation function or actual-page value is chosen. -/
public noncomputable def SourceMonomial.value {G : GeneratorCatalogue}
    (P : ProgramData.{v}) (generator : ∀ i : Fin G.count,
      P.component (G.degree i).1 (G.degree i).2) :
    ∀ {s t : ℕ}, SourceMonomial G s t → P.component s t
  | _, _, .one => P.unit
  | _, _, .generator i => generator i
  | _, _, .mul (s := s) (t := t) (s' := s') (t' := t') a b =>
      P.product s t s' t' (a.value P generator) (b.value P generator)

/-- Full bounded basis correctness on one data presentation and one archive.
The equivalence proves spanning and independence of all coordinate vectors;
`basis_values` fixes every unit vector to the archived source monomial. -/
public structure SourceBasisSpecification (P : ProgramData.{v}) (A : SphereArchive) where
  generator : ∀ i : Fin A.generators.count,
    P.component (A.generators.degree i).1 (A.generators.degree i).2
  atom_agrees : ∀ a : Atom,
    (eqToHom (congrArg (fun d : ℕ × ℕ => P.component d.1 d.2) (A.atom_degree a)))
      (generator (A.atomIndex a)) = P.atom a
  coordinates : ∀ s t : ℕ, t ≤ 261 →
    P.component s t ≃ₗ[ℤ] (Fin (A.basisCount s t) →₀ ZMod 2)
  basis_values : ∀ (s t : ℕ) (ht : t ≤ 261) (i : Fin (A.basisCount s t)),
    (coordinates s t ht).symm (Finsupp.single i 1) =
      (A.basisMonomial s t i).value P generator

variable {C : Type u} [StableHomotopyCategory.{u,v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w,v} Syn]
  [HasFunctorialCofiber (C := Syn)]
  {D : Model C Syn} {P : ProgramData.{v}} {A : SphereArchive}

namespace SpherePresentation

/-- Complete coordinates on the same actual sphere E₂, derived by composing
the one source basis and the one comparison. This is the original cm1 contract. -/
public noncomputable def coordinates (e : SpherePresentation D P)
    (S : SourceBasisSpecification P A) (s t : ℕ) (ht : t ≤ 261) :
    D.classical.sphere.Page 2 (s,t) ≃ₗ[ℤ] (Fin (A.basisCount s t) →₀ ZMod 2) :=
  (e.comparison s t ht).symm.trans (S.coordinates s t ht)

/-- Every actual coordinate unit vector is the image of the same archived
monomial, not a freshly selected basis of the same dimension. -/
public theorem coordinates_basis (e : SpherePresentation D P)
    (S : SourceBasisSpecification P A) (s t : ℕ) (ht : t ≤ 261)
    (i : Fin (A.basisCount s t)) :
    (e.coordinates S s t ht).symm (Finsupp.single i 1) =
      e.comparison s t ht ((A.basisMonomial s t i).value P S.generator) := by
  change e.comparison s t ht ((S.coordinates s t ht).symm (Finsupp.single i 1)) = _
  rw [S.basis_values]

/-- Original cm1's pullback formulation, derived without another input. -/
public theorem comparison_symm_coordinates_basis (e : SpherePresentation D P)
    (S : SourceBasisSpecification P A) (s t : ℕ) (ht : t ≤ 261)
    (i : Fin (A.basisCount s t)) :
    (e.comparison s t ht).symm ((e.coordinates S s t ht).symm (Finsupp.single i 1)) =
      (A.basisMonomial s t i).value P S.generator := by
  rw [e.coordinates_basis S s t ht i]
  exact (e.comparison s t ht).symm_apply_apply _
end SpherePresentation
end KIP126.Computation
