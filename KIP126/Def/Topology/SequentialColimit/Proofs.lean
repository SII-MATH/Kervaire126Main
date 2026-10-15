module

public import KIP126.Def.Topology.Pushout.Proofs
public import Mathlib.CategoryTheory.Limits.Types.Filtered

@[expose] public section

namespace KIP126.Topology

open CategoryTheory CategoryTheory.Limits _root_.Topology Set

universe u

set_option backward.isDefEq.respectTransparency false

/-- A sequential colimit of closed embeddings contains each of its stages
as an actual closed subspace. The proof uses the colimit topology and the
finite-stage equality criterion for the underlying sets. -/
theorem isClosedEmbedding_nat_colimit_of_maps
    (F : ℕ ⥤ TopCat.{u}) (c : Cocone F) (hc : IsColimit c)
    (hF : ∀ {n m : ℕ} (h : n ≤ m), IsClosedEmbedding (F.map (homOfLE h))) (n : ℕ) :
    IsClosedEmbedding (c.ι.app n) := by
  have hc' := isColimitOfPreserves (forget TopCat) hc
  have hι (m : ℕ) : Function.Injective (c.ι.app m) := by
    intro x y hxy
    obtain ⟨k,f,hf⟩ := (Types.FilteredColimit.isColimit_eq_iff' hc' x y).mp hxy
    exact (hF (leOfHom f)).injective hf
  apply IsClosedEmbedding.of_continuous_injective_isClosedMap
    (c.ι.app n).hom.continuous (hι n)
  intro K hK
  apply (TopCat.isClosed_iff_of_isColimit c hc _).mpr
  intro m
  let kn : n ⟶ max n m := homOfLE (le_max_left n m)
  let km : m ⟶ max n m := homOfLE (le_max_right n m)
  have hn (x : F.obj n) : c.ι.app (max n m) (F.map kn x) = c.ι.app n x :=
    ConcreteCategory.congr_hom (c.w kn) x
  have hm (x : F.obj m) : c.ι.app (max n m) (F.map km x) = c.ι.app m x :=
    ConcreteCategory.congr_hom (c.w km) x
  have he : c.ι.app m ⁻¹' (c.ι.app n '' K) = F.map km ⁻¹' (F.map kn '' K) := by
    ext y
    constructor
    · rintro ⟨x,hx,hxy⟩
      refine ⟨x,hx,(hι (max n m)) ?_⟩
      exact (hn x).trans (hxy.trans (hm y).symm)
    · rintro ⟨x,hx,hxy⟩
      exact ⟨x,hx,(hn x).symm.trans ((congrArg (c.ι.app (max n m)) hxy).trans (hm y))⟩
  rw [he]
  exact ((hF (le_max_left n m)).isClosedMap _ hK).preimage (F.map km).hom.continuous

/-- Closed embeddings on successor maps give closed embeddings on every
map of the sequential diagram. -/
theorem isClosedEmbedding_nat_map_of_succ (F : ℕ ⥤ TopCat.{u})
    (hF : ∀ n, IsClosedEmbedding (F.map (homOfLE (Nat.le_succ n))))
    {n m : ℕ} (h : n ≤ m) : IsClosedEmbedding (F.map (homOfLE h)) := by
  induction m, h using Nat.le_induction with
  | base => simpa using (IsClosedEmbedding.id : IsClosedEmbedding (id : F.obj n → F.obj n))
  | succ m h ih =>
    have he : homOfLE (by omega : n ≤ m+1) = homOfLE h ≫ homOfLE (Nat.le_succ m) := rfl
    rw [he,Functor.map_comp]
    exact (hF m).comp ih

/-- Successive closed embeddings suffice for every structural map into
the actual sequential colimit to be a closed embedding. -/
theorem isClosedEmbedding_nat_colimit
    (F : ℕ ⥤ TopCat.{u}) (c : Cocone F) (hc : IsColimit c)
    (hF : ∀ n, IsClosedEmbedding (F.map (homOfLE (Nat.le_succ n)))) (n : ℕ) :
    IsClosedEmbedding (c.ι.app n) :=
  isClosedEmbedding_nat_colimit_of_maps F c hc
    (fun h => isClosedEmbedding_nat_map_of_succ F hF h) n

end KIP126.Topology
