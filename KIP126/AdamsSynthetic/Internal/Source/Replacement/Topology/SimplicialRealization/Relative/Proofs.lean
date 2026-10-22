module

import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.Relative.Data
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.HomotopyExtension.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.CWComplex.ClosedEmbedding.Proofs
import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal

@[expose] section

namespace KIP126.Topology.SimplicialRealization

open CategoryTheory CategoryTheory.Limits Simplicial Opposite
open scoped unitInterval

universe u

/-- Every actual realized simplicial monomorphism has homotopy extension. -/
theorem realization_mono_hasHomotopyExtension {X Y : SSet.{u}} (i : X ⟶ Y) [Mono i] :
    HomotopyExtension.HasHomotopyExtension (SSet.toTop.map i) :=
  HomotopyExtension.relativeCWComplex_hasHomotopyExtension (relativeCWComplex i)

/-- The inclusion of any vertex of an actual realization has full
homotopy extension, with the vertex represented by its zero-simplex. -/
theorem vertex_homotopy_extension (X : SSet.{u}) (x : X.obj (op ⦋0⦌))
    (Y : TopCat.{u}) (f : C(|X|, Y)) (p : C(I, Y))
    (hp : p 0 = f (SSet.toTop.map (SSet.const x : Δ[0] ⟶ X) default)) :
    ∃ H : C(|X| × I, Y), (∀ y, H (y, 0) = f y) ∧
      (∀ t, H (SSet.toTop.map (SSet.const x : Δ[0] ⟶ X) default, t) = p t) := by
  let i : (Δ[0] : SSet.{u}) ⟶ X := SSet.const x
  letI : IsSplitMono i := SSet.stdSimplex.isTerminalObj₀.isSplitMono_from i
  obtain ⟨H, hH0, hHi⟩ := realization_mono_hasHomotopyExtension i Y f
    (p.comp ContinuousMap.snd) (by
      intro a
      rw [Subsingleton.elim a (default : |(Δ[0] : SSet.{u})|)]
      exact hp)
  exact ⟨H, hH0, hHi default⟩



/-- The geometric vertex agrees exactly with the vertex selected by the realization adjunction. -/
theorem realization_vertex_eq_unit (X : SSet.{u}) (x : X.obj (op ⦋0⦌)) :
    SSet.toTop.map (SSet.const x : Δ[0] ⟶ X) default =
      TopCat.toSSetObj₀Equiv ((sSetTopAdj.unit.app X).app (op ⦋0⦌) x) := by
  let i : (Δ[0] : SSet.{u}) ⟶ X := SSet.const x
  let a : (Δ[0] : SSet.{u}).obj (op ⦋0⦌) := SSet.yonedaEquiv (𝟙 _)
  have h := ConcreteCategory.congr_hom
    (NatTrans.congr_app (sSetTopAdj.unit.naturality i) (op ⦋0⦌)) a
  have hi : i.app (op ⦋0⦌) a = x := by
    change X.map (SimplexCategory.const ⦋0⦌ ⦋0⦌ 0).op x = x
    have hc : SimplexCategory.const ⦋0⦌ ⦋0⦌ 0 = 𝟙 _ := Subsingleton.elim _ _
    simp [hc]
  change (sSetTopAdj.unit.app X).app (op ⦋0⦌) (i.app (op ⦋0⦌) a) = _ at h
  rw [hi] at h
  have he := congrArg TopCat.toSSetObj₀Equiv h
  change TopCat.toSSetObj₀Equiv ((sSetTopAdj.unit.app X).app (op ⦋0⦌) x) =
    SSet.toTop.map i (TopCat.toSSetObj₀Equiv
      ((sSetTopAdj.unit.app (Δ[0] : SSet.{u})).app (op ⦋0⦌) a)) at he
  rw [Subsingleton.elim (TopCat.toSSetObj₀Equiv
    ((sSetTopAdj.unit.app (Δ[0] : SSet.{u})).app (op ⦋0⦌) a)) default] at he
  exact he.symm

/-- A simplicial monomorphism realizes to an actual closed embedding. -/
theorem realization_mono_isClosedEmbedding {X Y : SSet.{u}} (i : X ⟶ Y) [Mono i] :
    _root_.Topology.IsClosedEmbedding (SSet.toTop.map i) :=
  relativeCWComplex_isClosedEmbedding (relativeCWComplex i)

/-- Every geometric vertex is closed in the actual realization. -/
theorem vertex_isClosed (X : SSet.{u}) (x : X.obj (op ⦋0⦌)) :
    IsClosed ({SSet.toTop.map (SSet.const x : Δ[0] ⟶ X) default} : Set |X|) := by
  let i : (Δ[0] : SSet.{u}) ⟶ X := SSet.const x
  letI : IsSplitMono i := SSet.stdSimplex.isTerminalObj₀.isSplitMono_from i
  have hr : Set.range (SSet.toTop.map i) =
      {SSet.toTop.map i (default : |(Δ[0] : SSet.{u})|)} := by
    ext y
    constructor
    · rintro ⟨a,rfl⟩
      exact congrArg (SSet.toTop.map i) (Subsingleton.elim a default)
    · rintro rfl
      exact ⟨default,rfl⟩
  rw [← hr]
  exact (realization_mono_isClosedEmbedding i).isClosed_range

end KIP126.Topology.SimplicialRealization
