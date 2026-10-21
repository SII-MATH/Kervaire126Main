module

import KIP126.ProofTools.FiniteFiltration

/-!
# Finite residual correction for Mahowald--Leibniz composition

These internal lemmas concern actual additive maps and finite filtrations.
They do not construct the finite-quotient groups, their classical graded
comparisons, the two prescribed representatives, or the output differential.
Those geometric and spectral-sequence constructions must be supplied in an
application to the fixed model. No infinite lift or cancellation of lambda
is used in this finite argument.
-/

@[expose] section
namespace KIP126.ProofTools.Internal.MahowaldLeibniz

/-- Finite residual correction annihilates the entire initial ambiguity
subgroup. Each step either corrects by an actual h-image or already has zero
f-image. The correction remains in the specified initial filtration. -/
private theorem finite_residual_image_zero
    {A H B : Type*} [AddCommGroup A] [AddCommGroup H] [AddCommGroup B]
    (h : H →+ A) (f : A →+ B)
    (E : ℤ → AddSubgroup A) (L : ℤ → AddSubgroup H)
    (hL : Antitone L) (hfh : ∀ b : H, f (h b) = 0)
    (s : ℤ) (N : ℕ)
    (hstep : ∀ k : ℤ, s ≤ k → k < s + N → ∀ a : A, a ∈ E k →
      (∃ b : H, b ∈ L k ∧ a - h b ∈ E (k + 1)) ∨ f a = 0)
    (hend : ∀ a : A, a ∈ E (s + N) → f a = 0)
    (a : A) (ha : a ∈ E s) : f a = 0 := by
  obtain ⟨b, _, hb⟩ := KIP126.ProofTools.finite_filtration_correction
    h f E L (⊥ : AddSubgroup B) hL s N
    (fun k hk hkN a ha => by
      rcases hstep k hk hkN a ha with hcorrect | hzero
      · exact Or.inl hcorrect
      · exact Or.inr (by simpa only [AddSubgroup.mem_bot] using hzero))
    (fun a ha => by simpa only [AddSubgroup.mem_bot] using hend a ha)
    a 0 (by simpa only [map_zero, sub_zero] using ha)
  have hz : f (a - h b) = 0 := by
    simpa only [AddSubgroup.mem_bot] using hb
  simpa only [map_sub, hfh, sub_zero] using hz

/-- Two specified representatives have the same actual image once their
residual is eliminated by finite correction. Neither representative is
replaced, and the conclusion is an equality in the original target group. -/
private theorem finite_representative_image_eq
    {A H B : Type*} [AddCommGroup A] [AddCommGroup H] [AddCommGroup B]
    (h : H →+ A) (f : A →+ B)
    (E : ℤ → AddSubgroup A) (L : ℤ → AddSubgroup H)
    (hL : Antitone L) (hfh : ∀ b : H, f (h b) = 0)
    (s : ℤ) (N : ℕ)
    (hstep : ∀ k : ℤ, s ≤ k → k < s + N → ∀ a : A, a ∈ E k →
      (∃ b : H, b ∈ L k ∧ a - h b ∈ E (k + 1)) ∨ f a = 0)
    (hend : ∀ a : A, a ∈ E (s + N) → f a = 0)
    (uδ uM : A) (hresidual : uδ - uM ∈ E s) :
    f uδ = f uM := by
  have hz := finite_residual_image_zero h f E L hL hfh s N hstep hend
    (uδ - uM) hresidual
  exact sub_eq_zero.mp (by simpa only [map_sub] using hz)

/-- Surjectivity of each successive graded h-map, with a zero terminal
filtration, eliminates the residual without cancelling any layer. -/
private theorem finite_surjective_layers_image_eq
    {A H B : Type*} [AddCommGroup A] [AddCommGroup H] [AddCommGroup B]
    (h : H →+ A) (f : A →+ B)
    (E : ℤ → AddSubgroup A) (L : ℤ → AddSubgroup H)
    (hL : Antitone L) (hfh : ∀ b : H, f (h b) = 0)
    (s : ℤ) (N : ℕ)
    (hsurj : ∀ k : ℤ, s ≤ k → k < s + N → ∀ a : A, a ∈ E k →
      ∃ b : H, b ∈ L k ∧ a - h b ∈ E (k + 1))
    (hend : E (s + N) = ⊥)
    (uδ uM : A) (hresidual : uδ - uM ∈ E s) :
    f uδ = f uM := by
  apply finite_representative_image_eq h f E L hL hfh s N
    (fun k hk hkN a ha => Or.inl (hsurj k hk hkN a ha))
    (fun a ha => ?_) uδ uM hresidual
  have ha0 : a = 0 := by
    simpa only [hend, AddSubgroup.mem_bot] using ha
  simp only [ha0, map_zero]

/-- Vanishing of the intermediate grades pushes the residual to the last
layer. Only that last layer is required to have zero f-image; the layer
itself need not vanish or come from h. -/
private theorem finite_collapsed_layers_image_eq
    {A H B : Type*} [AddCommGroup A] [AddCommGroup H] [AddCommGroup B]
    (h : H →+ A) (f : A →+ B)
    (E : ℤ → AddSubgroup A) (L : ℤ → AddSubgroup H)
    (hL : Antitone L) (hfh : ∀ b : H, f (h b) = 0)
    (s : ℤ) (N : ℕ)
    (hcollapse : ∀ k : ℤ, s ≤ k → k < s + N → E k ≤ E (k + 1))
    (hlast : ∀ a : A, a ∈ E (s + N) → f a = 0)
    (uδ uM : A) (hresidual : uδ - uM ∈ E s) :
    f uδ = f uM := by
  apply finite_representative_image_eq h f E L hL hfh s N
    (fun k hk hkN a ha => ?_) hlast uδ uM hresidual
  exact Or.inl ⟨0, (L k).zero_mem,
    by simpa only [map_zero, sub_zero] using hcollapse k hk hkN ha⟩

/-- The Surj specialization with the composition theorem's exact layer
numbering: the corrected layers are S+1 through S+K-1, and the terminal
zero subgroup is E(S+K). -/
private theorem finite_level_surjectivity_image_eq
    {A H B : Type*} [AddCommGroup A] [AddCommGroup H] [AddCommGroup B]
    (h : H →+ A) (f : A →+ B)
    (E : ℤ → AddSubgroup A) (L : ℤ → AddSubgroup H)
    (hL : Antitone L) (hfh : ∀ b : H, f (h b) = 0)
    (S : ℤ) (K : ℕ) (hK : 2 ≤ K)
    (hsurj : ∀ j : ℤ, 1 ≤ j → j < K → ∀ a : A, a ∈ E (S + j) →
      ∃ b : H, b ∈ L (S + j) ∧ a - h b ∈ E (S + j + 1))
    (hend : E (S + K) = ⊥)
    (uδ uM : A) (hresidual : uδ - uM ∈ E (S + 1)) :
    f uδ = f uM := by
  exact finite_surjective_layers_image_eq h f E L hL hfh (S + 1) (K - 1)
    (fun k hk hkN a ha => by
      have heq : S + (k - S) = k := by omega
      simpa only [heq] using hsurj (k - S) (by omega) (by omega) a
        (by simpa only [heq] using ha))
    (by
      have heq : S + 1 + ((K - 1 : ℕ) : ℤ) = S + K := by omega
      simpa only [heq] using hend) uδ uM hresidual

/-- The PDF specialization with the same layer numbering. NC1 removes
only the intermediate grades S+1 through S+K-2; NC2 must annihilate the
remaining whole layer E(S+K-1). For K=2 the intermediate family is empty. -/
private theorem finite_level_collapsed_image_eq
    {A H B : Type*} [AddCommGroup A] [AddCommGroup H] [AddCommGroup B]
    (h : H →+ A) (f : A →+ B)
    (E : ℤ → AddSubgroup A) (L : ℤ → AddSubgroup H)
    (hL : Antitone L) (hfh : ∀ b : H, f (h b) = 0)
    (S : ℤ) (K : ℕ) (hK : 2 ≤ K)
    (hcollapse : ∀ j : ℤ, 1 ≤ j → j < (K : ℤ) - 1 →
      E (S + j) ≤ E (S + j + 1))
    (hlast : ∀ a : A, a ∈ E (S + K - 1) → f a = 0)
    (uδ uM : A) (hresidual : uδ - uM ∈ E (S + 1)) :
    f uδ = f uM := by
  apply finite_collapsed_layers_image_eq h f E L hL hfh (S + 1) (K - 2)
    (fun k hk hkN => ?_) (fun a ha => ?_) uδ uM hresidual
  · have heq : S + (k - S) = k := by omega
    simpa only [heq] using hcollapse (k - S) (by omega) (by omega)
  · apply hlast a
    have heq : S + 1 + ((K - 2 : ℕ) : ℤ) = S + K - 1 := by omega
    simpa only [heq] using ha

/-- The image equality retains an independently constructed target exactly. -/
private theorem finite_representative_prescribed_image
    {A H B : Type*} [AddCommGroup A] [AddCommGroup H] [AddCommGroup B]
    (h : H →+ A) (f : A →+ B)
    (E : ℤ → AddSubgroup A) (L : ℤ → AddSubgroup H)
    (hL : Antitone L) (hfh : ∀ b : H, f (h b) = 0)
    (s : ℤ) (N : ℕ)
    (hstep : ∀ k : ℤ, s ≤ k → k < s + N → ∀ a : A, a ∈ E k →
      (∃ b : H, b ∈ L k ∧ a - h b ∈ E (k + 1)) ∨ f a = 0)
    (hend : ∀ a : A, a ∈ E (s + N) → f a = 0)
    (uδ uM : A) (v : B) (hresidual : uδ - uM ∈ E s)
    (hM : f uM = v) : f uδ = v :=
  (finite_representative_image_eq h f E L hL hfh s N hstep hend
    uδ uM hresidual).trans hM

/-- The same finite induction constructs an actual preimage in the initial
filtration, not just a sequence of associated-graded preimages. -/
private theorem finite_surjective_layers_lift
    {A H : Type*} [AddCommGroup A] [AddCommGroup H]
    (h : H →+ A) (E : ℤ → AddSubgroup A) (L : ℤ → AddSubgroup H)
    (hL : Antitone L) (s : ℤ) (N : ℕ)
    (hsurj : ∀ k : ℤ, s ≤ k → k < s + N → ∀ a : A, a ∈ E k →
      ∃ b : H, b ∈ L k ∧ a - h b ∈ E (k + 1))
    (hend : E (s + N) = ⊥)
    (a : A) (ha : a ∈ E s) : ∃ b : H, b ∈ L s ∧ h b = a := by
  obtain ⟨b, hb, hab⟩ := KIP126.ProofTools.finite_filtration_correction
    h (AddMonoidHom.id A) E L (⊥ : AddSubgroup A) hL s N
    (fun k hk hkN a ha => Or.inl (hsurj k hk hkN a ha))
    (fun a ha => by
      have ha0 : a = 0 := by simpa only [hend, AddSubgroup.mem_bot] using ha
      simpa only [AddMonoidHom.id_apply, ha0] using
        (⊥ : AddSubgroup A).zero_mem)
    a 0 (by simpa only [map_zero, sub_zero] using ha)
  refine ⟨b, by simpa only [sub_zero] using hb, ?_⟩
  have hz : a - h b = 0 := by
    simpa only [AddMonoidHom.id_apply, AddSubgroup.mem_bot] using hab
  exact (sub_eq_zero.mp hz).symm

/-- If ker(f)=im(h), equality of f-images modulo source boundaries is
exactly the existence of an h-preimage modulo those same boundaries.
The boundary subgroup is not replaced by target boundaries. -/
private theorem image_eq_boundary_iff_lift_mod_boundary
    {A H B : Type*} [AddCommGroup A] [AddCommGroup H] [AddCommGroup B]
    (h : H →+ A) (f : A →+ B)
    (hexact : ∀ a : A, f a = 0 ↔ ∃ z : H, h z = a)
    (BX : AddSubgroup A) (a : A) :
    (∃ b : A, b ∈ BX ∧ f a = f b) ↔
      ∃ z : H, ∃ b : A, b ∈ BX ∧ a = h z + b := by
  constructor
  · rintro ⟨b, hb, hab⟩
    have hz : f (a - b) = 0 := by rw [map_sub, hab, sub_self]
    obtain ⟨z, hz⟩ := (hexact (a - b)).mp hz
    refine ⟨z, b, hb, ?_⟩
    rw [hz, sub_add_cancel]
  · rintro ⟨z, b, hb, rfl⟩
    refine ⟨b, hb, ?_⟩
    have hz : f (h z) = 0 := (hexact (h z)).mpr ⟨z, rfl⟩
    rw [map_add, hz, zero_add]

/-- The last-layer surjectivity condition implies target-boundary
annihilation when the actual map preserves the specified boundary cutoff. -/
private theorem last_layer_surjectivity_implies_target_boundary
    {A H B : Type*} [AddCommGroup A] [AddCommGroup H] [AddCommGroup B]
    (h : H →+ A) (f : A →+ B)
    (U BX : AddSubgroup A) (BY : AddSubgroup B)
    (hfh : ∀ z : H, f (h z) = 0)
    (hboundary : ∀ b : A, b ∈ BX → f b ∈ BY)
    (hsurj : ∀ a : A, a ∈ U →
      ∃ z : H, ∃ b : A, b ∈ BX ∧ a = h z + b) :
    ∀ a : A, a ∈ U → f a ∈ BY := by
  intro a ha
  obtain ⟨z, b, hb, rfl⟩ := hsurj a ha
  simpa only [map_add, hfh, zero_add] using hboundary b hb

/-- The reverse last-layer implication additionally needs lifting of those
target boundaries through the fixed source boundary subgroup. -/
private theorem last_layer_target_boundary_implies_surjectivity
    {A H B : Type*} [AddCommGroup A] [AddCommGroup H] [AddCommGroup B]
    (h : H →+ A) (f : A →+ B)
    (U BX : AddSubgroup A) (BY : AddSubgroup B)
    (hexact : ∀ a : A, f a = 0 ↔ ∃ z : H, h z = a)
    (hlift : ∀ a : A, a ∈ U → f a ∈ BY →
      ∃ b : A, b ∈ BX ∧ f a = f b)
    (hzero : ∀ a : A, a ∈ U → f a ∈ BY) :
    ∀ a : A, a ∈ U → ∃ z : H, ∃ b : A, b ∈ BX ∧ a = h z + b := by
  intro a ha
  exact (image_eq_boundary_iff_lift_mod_boundary h f hexact BX a).mp
    (hlift a ha (hzero a ha))

/-- Exactness decides whether at least one representative in the prescribed
coset a₀ + V lifts. It does not assert that the originally chosen a₀ lifts,
or that every representative in the coset does. In a finite quotient
application the subgroup V must be the actual ambiguity subgroup preserving
the required detection. No permanence of a target is assumed. -/
private theorem representative_family_has_lift_iff_boundary_mem
    {D A C : Type*} [AddCommGroup D] [AddCommGroup A] [AddCommGroup C]
    (q : D →+ A) (δ : A →+ C)
    (hexact : ∀ a : A, δ a = 0 ↔ ∃ d : D, q d = a)
    (V : AddSubgroup A) (a₀ : A) :
    (∃ v : A, v ∈ V ∧ ∃ d : D, q d = a₀ + v) ↔ δ a₀ ∈ V.map δ := by
  constructor
  · rintro ⟨v, hv, d, hd⟩
    have hz : δ (a₀ + v) = 0 := (hexact (a₀ + v)).mpr ⟨d, hd⟩
    have hsum : δ a₀ + δ v = 0 := by simpa only [map_add] using hz
    refine AddSubgroup.mem_map.mpr ⟨-v, V.neg_mem hv, ?_⟩
    rw [map_neg]
    exact (eq_neg_of_add_eq_zero_left hsum).symm
  · intro hmem
    obtain ⟨v, hv, hδv⟩ := AddSubgroup.mem_map.mp hmem
    refine ⟨-v, V.neg_mem hv, (hexact (a₀ + -v)).mp ?_⟩
    rw [map_add, map_neg, hδv, add_neg_cancel]

end KIP126.ProofTools.Internal.MahowaldLeibniz
