module

public import Mathlib.GroupTheory.QuotientGroup.Basic

/-! The additive-group comparison at the final ambiguity layer.  The source
group is the entire homogeneous E₂ group, rather than a chosen subgroup of
cycles.  The maps and boundary groups are kept fixed throughout. -/

@[expose] section
namespace KIP126.ProofTools
noncomputable section

private theorem last_layer_image_criterion
    {A H B : Type*} [AddCommGroup A] [AddCommGroup H] [AddCommGroup B]
    (h : H →+ A) (f : A →+ B) (hexact : f.ker = h.range)
    (BX : AddSubgroup A) :
    (∀ a : A, ∃ z : H, ∃ b : A, b ∈ BX ∧ a = h z + b) ↔
      f.range = BX.map f := by
  constructor
  · intro hsurj
    apply le_antisymm
    · rintro y ⟨a, rfl⟩
      obtain ⟨z, b, hb, rfl⟩ := hsurj a
      have hz : f (h z) = 0 := by
        apply AddMonoidHom.mem_ker.mp
        rw [hexact]
        exact ⟨z, rfl⟩
      exact AddSubgroup.mem_map.mpr ⟨b, hb, by simp only [map_add, hz, zero_add]⟩
    · rintro y ⟨a, _, rfl⟩
      exact ⟨a, rfl⟩
  · intro himage a
    obtain ⟨b, hb, hba⟩ := AddSubgroup.mem_map.mp
      (himage ▸ (show f a ∈ f.range from ⟨a, rfl⟩))
    have hab : a - b ∈ h.range := by
      rw [← hexact]
      change f (a - b) = 0
      rw [map_sub, hba, sub_self]
    obtain ⟨z, hz⟩ := hab
    exact ⟨z, b, hb, by rw [hz, sub_add_cancel]⟩

/-- At the final layer, surjectivity modulo the fixed source boundaries is
equality of the actual images.  It implies the target-boundary condition.
Under that weaker condition, its exact additional requirement is lifting all
target boundaries in the image through the same source-boundary subgroup. -/
private theorem lastLayerComparison
    {A H B : Type*} [AddCommGroup A] [AddCommGroup H] [AddCommGroup B]
    (h : H →+ A) (f : A →+ B) (hexact : f.ker = h.range)
    (BX : AddSubgroup A) (BY : AddSubgroup B)
    (hboundary : BX.map f ≤ BY) :
    ((∀ a : A, ∃ z : H, ∃ b : A, b ∈ BX ∧ a = h z + b) ↔
      f.range = BX.map f) ∧
    ((∀ a : A, ∃ z : H, ∃ b : A, b ∈ BX ∧ a = h z + b) →
      f.range ≤ BY) ∧
    (f.range ≤ BY →
      ((∀ a : A, ∃ z : H, ∃ b : A, b ∈ BX ∧ a = h z + b) ↔
        f.range ⊓ BY = BX.map f)) := by
  have hiff := last_layer_image_criterion h f hexact BX
  refine ⟨hiff, ?_, ?_⟩
  · intro hs
    rw [hiff.mp hs]
    exact hboundary
  · intro hNC
    simpa only [inf_eq_left.mpr hNC] using hiff

private def lastLayerRestrictedImage
    {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (f : A →+ B) (BY : AddSubgroup B) :
    BY.comap f →+ ↥(f.range ⊓ BY) where
  toFun a := ⟨f a, ⟨⟨a, rfl⟩, a.property⟩⟩
  map_zero' := Subtype.ext (map_zero f)
  map_add' a b := Subtype.ext (map_add f (a : A) (b : A))

private theorem lastLayerRestrictedImage_surjective
    {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (f : A →+ B) (BY : AddSubgroup B) :
    Function.Surjective (lastLayerRestrictedImage f BY) := by
  rintro ⟨b, hb⟩
  obtain ⟨a, ha⟩ := hb.1
  refine ⟨⟨a, ?_⟩, Subtype.ext ha⟩
  change f a ∈ BY
  rw [ha]
  exact hb.2

private theorem lastLayerObstruction_kernel
    {A H B : Type*} [AddCommGroup A] [AddCommGroup H] [AddCommGroup B]
    (h : H →+ A) (f : A →+ B) (hexact : f.ker = h.range)
    (BX : AddSubgroup A) (BY : AddSubgroup B) :
    ((QuotientAddGroup.mk' ((BX.map f).addSubgroupOf (f.range ⊓ BY))).comp
      (lastLayerRestrictedImage f BY)).ker =
      (h.range ⊔ BX).addSubgroupOf (BY.comap f) := by
  ext a
  change
    QuotientAddGroup.mk' ((BX.map f).addSubgroupOf (f.range ⊓ BY))
      (lastLayerRestrictedImage f BY a) = 0 ↔
      (a : A) ∈ h.range ⊔ BX
  rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
  change f a ∈ BX.map f ↔ (a : A) ∈ h.range ⊔ BX
  constructor
  · rintro ⟨b, hb, hba⟩
    have hab : (a : A) - b ∈ h.range := by
      rw [← hexact]
      change f ((a : A) - b) = 0
      rw [map_sub, hba, sub_self]
    exact AddSubgroup.mem_sup.mpr
      ⟨(a : A) - b, hab, b, hb, sub_add_cancel _ _⟩
  · intro ha
    obtain ⟨z, hz, b, hb, hzb⟩ := AddSubgroup.mem_sup.mp ha
    have hfz : f z = 0 := by
      apply AddMonoidHom.mem_ker.mp
      rwa [hexact]
    exact AddSubgroup.mem_map.mpr
      ⟨b, hb, by rw [← hzb, map_add, hfz, zero_add]⟩

/-- The exact obstruction between the two final-layer conditions.  This is
the isomorphism induced by the fixed map `f`, not only an equality of the
orders or dimensions of the two quotient groups.  `addSubgroupOf` expresses the
displayed denominators inside their respective numerator groups. -/
private def last_layer_obstruction_equiv
    {A H B : Type*} [AddCommGroup A] [AddCommGroup H] [AddCommGroup B]
    (h : H →+ A) (f : A →+ B) (hexact : f.ker = h.range)
    (BX : AddSubgroup A) (BY : AddSubgroup B)
    (_hboundary : BX.map f ≤ BY) :
    (BY.comap f ⧸ (h.range ⊔ BX).addSubgroupOf (BY.comap f)) ≃+
      (↥(f.range ⊓ BY) ⧸ (BX.map f).addSubgroupOf (f.range ⊓ BY)) := by
  let ψ := (QuotientAddGroup.mk'
    ((BX.map f).addSubgroupOf (f.range ⊓ BY))).comp
      (lastLayerRestrictedImage f BY)
  have hψ : Function.Surjective ψ :=
    (QuotientAddGroup.mk'_surjective _).comp
      (lastLayerRestrictedImage_surjective f BY)
  exact (QuotientAddGroup.quotientAddEquivOfEq
    (lastLayerObstruction_kernel h f hexact BX BY).symm).trans
      (QuotientAddGroup.quotientKerEquivOfSurjective ψ hψ)

/-- The two quotient obstruction groups are isomorphic by the map induced
by the fixed `f`. This theorem concerns the full quotient groups, not just
their individual elements. -/
private theorem lastLayerObstructionIsomorphism
    {A H B : Type*} [AddCommGroup A] [AddCommGroup H] [AddCommGroup B]
    (h : H →+ A) (f : A →+ B) (hexact : f.ker = h.range)
    (BX : AddSubgroup A) (BY : AddSubgroup B)
    (hboundary : BX.map f ≤ BY) :
    Nonempty ((BY.comap f ⧸ (h.range ⊔ BX).addSubgroupOf (BY.comap f)) ≃+
      (↥(f.range ⊓ BY) ⧸ (BX.map f).addSubgroupOf (f.range ⊓ BY))) := by
  exact ⟨last_layer_obstruction_equiv h f hexact BX BY hboundary⟩

/-- On an intermediate layer the NC condition gives the required
cycle-qualified preimage by taking that preimage to be zero. -/
private theorem intermediateLayerSurjectivity
    {A H : Type*} [AddCommGroup A] [AddCommGroup H]
    (h : H →+ A) (C BX : AddSubgroup A) (L : AddSubgroup H)
    (hNC : C ≤ BX) :
    ∀ a : A, a ∈ C → ∃ z : H, z ∈ L ∧ a - h z ∈ BX := by
  intro a ha
  exact ⟨0, L.zero_mem, by simpa only [map_zero, sub_zero] using hNC ha⟩

/-- The intermediate Surj condition does not conversely imply NC: an
arbitrary nonboundary element can have its own cycle-qualified preimage.
This is an additive-group example; it makes no identification with a
particular selected spectrum. -/
public theorem intermediateLayerSurjectivity_not_converse :
    (∀ a : ℤ, a ∈ (⊤ : AddSubgroup ℤ) →
      ∃ z : ℤ, z ∈ (⊤ : AddSubgroup ℤ) ∧
        a - (AddMonoidHom.id ℤ) z ∈ (⊥ : AddSubgroup ℤ)) ∧
    ¬ ((⊤ : AddSubgroup ℤ) ≤ ⊥) := by
  constructor
  · intro a _
    exact ⟨a, AddSubgroup.mem_top a, by simp⟩
  · intro hle
    have hone := hle (AddSubgroup.mem_top (1 : ℤ))
    exact one_ne_zero (by simpa only [AddSubgroup.mem_bot] using hone)

end
end KIP126.ProofTools
