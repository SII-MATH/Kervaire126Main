module

import all KIP126.SpectralSequence.BoundedExtension.Square.Proofs
import all KIP126.SpectralSequence.BoundedExtension.Morphism.Construction.Data

@[expose] section

namespace KIP126.Core.SpectralSequence
open CategoryTheory
universe u v w
variable {C : Type u} [Category.{v} C] [Abelian C]
  {ι : Type w} {A₁ A₂ B₁ B₂ : ι → C}
  {F₁ : Filtration A₁} {F₂ : Filtration A₂}
  {G₁ : Filtration B₁} {G₂ : Filtration B₂}

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- A commuting square of actual filtered morphisms induces its actual
two-term filtered chain map. No map of pages is chosen independently. -/
noncomputable def underlyingComplexMap
    (f : KIP126.Core.SpectralSequence.FilteredMorphism F₁ F₂)
    (g : KIP126.Core.SpectralSequence.FilteredMorphism G₁ G₂)
    (a : KIP126.Core.SpectralSequence.FilteredMorphism F₁ G₁)
    (b : KIP126.Core.SpectralSequence.FilteredMorphism F₂ G₂)
    (h : ∀ i, a.map i ≫ g.map i = f.map i ≫ b.map i) (i : ι) :
    FilteredComplex.Morphism (underlyingComplex f.map f.compat i)
      (underlyingComplex g.map g.compat i) :=
  FilteredComplexMorphism.mk (BoundedExtension.twoTermMap (a.map i) (b.map i))
    (fun k => by
      simpa only [FilteredComplex.d, underlyingComplex,
        BoundedExtension.twoTermComplex_d] using
          BoundedExtension.twoTermMap_comm (f.map i) (g.map i) (a.map i) (b.map i) (h i) k)
    (fun s k => by
      by_cases hk : k = 1
      · subst k
        refine ⟨(a.compat s i).choose, ?_⟩
        simpa [underlyingComplex, FilteredComplex.fil, FilteredComplex.A,
          twoTermFil, BoundedExtension.twoTermFil, BoundedExtension.twoTermObj,
          BoundedExtension.twoTermMap] using (a.compat s i).choose_spec
      · by_cases hk₀ : k = 0
        · subst k
          refine ⟨(b.compat s i).choose, ?_⟩
          simpa [underlyingComplex, FilteredComplex.fil, FilteredComplex.A,
            twoTermFil, BoundedExtension.twoTermFil, BoundedExtension.twoTermObj,
            BoundedExtension.twoTermMap] using (b.compat s i).choose_spec
        · refine ⟨0, ?_⟩
          simp [underlyingComplex, BoundedExtension.twoTermMap, hk, hk₀])

end KIP126.Core.SpectralSequence
