module

public import KIP126.Def.Topology.SimplicialRealization.OrderComplex.Sigma.Data
public import KIP126.Def.Topology.SimplicialRealization.OrderComplex.MappingCone.Proofs
public import Mathlib.CategoryTheory.Limits.Types.Coproducts
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

@[expose] public section

namespace KIP126.Topology.SimplicialRealization

open CategoryTheory CategoryTheory.Limits Simplicial Opposite

universe u

set_option backward.isDefEq.respectTransparency false

variable {ι : Type u} (P : ι → Type u) [∀ j, PartialOrder (P j)]

/-- Every simplex in a disjoint union of orders lies in exactly one
summand; consequently the nerve is an actual simplicial coproduct. -/
noncomputable def orderSigmaCofan_isColimit : IsColimit (orderSigmaCofan P) := by
  classical
  apply evaluationJointlyReflectsColimits
  intro d
  let c : Cofan (fun j => (nerve (P j)).obj d) :=
    Cofan.mk ((nerve (Σ k, P k)).obj d) (fun j => (orderSigmaInclusion P j).app d)
  have hc : Nonempty (IsColimit c) := by
    apply (Cofan.nonempty_isColimit_iff_bijective_fromSigma c).mpr
    constructor
    · rintro ⟨j,s⟩ ⟨k,t⟩ h
      have hjk : j = k := congrArg (fun z : (nerve (Σ k, P k)).obj d => (z.obj 0).1) h
      subst k
      congr 1
      exact CategoryTheory.Functor.ext (fun l => sigma_mk_injective
        (congrArg (fun z : (nerve (Σ k, P k)).obj d => z.obj l) h))
    · intro s
      let j := (s.obj 0).1
      have hs : s ∈ Set.range ((orderSigmaInclusion P j).app d) := by
        apply (nerveMap_orderEmbedding_range_iff (orderSigmaEmbedding P j) d s).mpr
        intro k
        have hk : j = (s.obj k).1 := (Sigma.le_def.mp (s.monotone (Fin.zero_le k))).choose
        rcases hsk : s.obj k with ⟨l,p⟩
        rw [hsk] at hk
        dsimp only at hk
        subst l
        exact ⟨p,rfl⟩
      obtain ⟨t,ht⟩ := hs
      exact ⟨⟨j,t⟩,ht⟩
  exact (Cofan.isColimitMapCoconeEquiv ((evaluation SimplexCategoryᵒᵖ (Type u)).obj d)
    (fun j => nerve (P j)) (orderSigmaCofan P)).symm hc.some


/-- Realization of a disjoint union of orders is its actual topological coproduct. -/
noncomputable def orderSigmaRealizationCofan_isColimit : IsColimit (orderSigmaRealizationCofan P) :=
  (Cofan.isColimitMapCoconeEquiv SSet.toTop (fun j => nerve (P j)) (orderSigmaCofan P))
    (isColimitOfPreserves SSet.toTop (orderSigmaCofan_isColimit P))


/-- All cone bases together form a lower induced suborder; each attached
cone keeps its own apex. -/
theorem orderSigmaConeEmbedding_isLowerSet : IsLowerSet (Set.range (orderSigmaConeEmbedding P)) := by
  rintro y x hxy ⟨⟨j,p⟩,rfl⟩
  obtain ⟨k,q⟩ := x
  have hkj : k = j := (Sigma.le_def.mp hxy).choose
  subst k
  have hqp : q ≤ (p : WithTop (P j)) := Sigma.mk_le_mk_iff.mp hxy
  cases q with
  | top => simp at hqp
  | coe q => exact ⟨⟨j,q⟩,rfl⟩


/-- The actual order-nerve coproduct is homeomorphic to the disjoint
union of its realized summands, with the exact summand formulas. -/
theorem exists_orderSigmaRealization_homeomorph :
    ∃ e : |nerve (Σ j, P j)| ≃ₜ (Σ j, |nerve (P j)|),
      ∀ j (x : |nerve (P j)|), e (SSet.toTop.map (orderSigmaInclusion P j) x) = ⟨j,x⟩ := by
  let h := orderSigmaRealizationCofan_isColimit P
  let e := h.coconePointUniqueUpToIso
    (TopCat.sigmaCofanIsColimit (fun j => SSet.toTop.obj (nerve (P j))))
  refine ⟨TopCat.homeoOfIso e,?_⟩
  intro j x
  exact ConcreteCategory.congr_hom
    (h.fac (TopCat.sigmaCofan (fun j => SSet.toTop.obj (nerve (P j)))) ⟨j⟩) x


/-- The assembled order map restricts to the given actual map on each summand. -/
theorem orderSigmaInclusion_map {Q : Type u} [PartialOrder Q] (f : ∀ j, P j →o Q) (j : ι) :
    orderSigmaInclusion P j ≫ nerveMap (orderSigmaMap P f).monotone.functor =
      nerveMap (f j).monotone.functor := rfl


end KIP126.Topology.SimplicialRealization
