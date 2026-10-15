module

public import KIP126.Def.Topology.SimplicialRealization.Pullback.StandardSimplex.Data
public import KIP126.Def.Topology.SimplicialRealization.Pullback.Identification.Proofs

@[expose] public section

namespace KIP126.Topology.SimplicialRealization
open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open scoped MonoidalCategory
universe u
set_option backward.isDefEq.respectTransparency false

@[simp] theorem standardSimplexPullbackHomeomorph_fst {X Y : SSet.{u}}
    (f : X ⟶ Y) (n : ℕ) (b : (Δ[n] : SSet.{u}) ⟶ Y) (x : |pullback f b|) :
    (standardSimplexPullbackHomeomorph f n b x).val.1 = SSet.toTop.map (pullback.fst f b) x :=
  pullbackRealizationHomeomorph_fst f b _ _ _ x

@[simp] theorem standardSimplexPullbackHomeomorph_snd {X Y : SSet.{u}}
    (f : X ⟶ Y) (n : ℕ) (b : (Δ[n] : SSet.{u}) ⟶ Y) (x : |pullback f b|) :
    (standardSimplexPullbackHomeomorph f n b x).val.2 = SSet.toTop.map (pullback.snd f b) x :=
  pullbackRealizationHomeomorph_snd f b _ _ _ x

/-- The original realized standard-simplex pullback square satisfies the
actual topological universal property. -/
theorem realization_standardSimplex_isPullback {X Y : SSet.{u}}
    (f : X ⟶ Y) (n : ℕ) (b : (Δ[n] : SSet.{u}) ⟶ Y) :
    IsPullback (SSet.toTop.map (pullback.fst f b)) (SSet.toTop.map (pullback.snd f b))
      (SSet.toTop.map f) (SSet.toTop.map b) :=
  realization_isPullback_of_product_homeomorph f b
    (realizationStandardSimplexProductHomeomorph X n) (fun _ => rfl) (fun _ => rfl)

end KIP126.Topology.SimplicialRealization
