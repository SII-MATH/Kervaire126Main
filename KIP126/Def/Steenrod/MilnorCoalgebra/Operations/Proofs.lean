module

public import KIP126.Def.Steenrod.MilnorCoalgebra.Operations.Data
public import KIP126.Def.Steenrod.MilnorCobar.Polynomial.Monomials.Full.Proofs
public import KIP126.Def.Steenrod.MilnorCobar.Polynomial.Normalization.Proofs
public import KIP126.Def.Steenrod.MilnorCobar.Polynomial.Multiplication.Proofs
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.BigOperators.Intervals

@[expose] public section

namespace KIP126.Steenrod.Milnor.Coalgebra

open CategoryTheory MonoidalCategory KIP126.Algebra
  KIP126.Algebra.GradedVectorSpace

/-- Left counitality of the prescribed Milnor coproduct. -/
theorem comultiplication_counit_left :
    comultiplication ≫ counit ▷ dualSteenrodGraded =
      (λ_ dualSteenrodGraded).inv := by
  classical
  let e : ℕ ↪ Fin 2 × ℕ := ⟨fun j => (1,j), fun _ _ h => congrArg Prod.snd h⟩
  let E : TensorPower 2 →ₐ[F2] MvPolynomial ℕ F2 := MvPolynomial.killCompl e.injective
  have hE0 (j : ℕ) : E (MvPolynomial.X (0,j)) = 0 := by
    simp [E, MvPolynomial.killCompl, e]
  have hE1 (j : ℕ) : E (MvPolynomial.X (1,j)) = MvPolynomial.X j := by
    have h := MvPolynomial.killCompl_rename_app e.injective (MvPolynomial.X j : MvPolynomial ℕ F2)
    simpa [e] using h
  have hEa : E.comp (augmentSlot (0 : Fin 2)) = E := by
    ext a : 1
    rcases a with ⟨i,j⟩
    fin_cases i <;> simp [AlgHom.comp_apply, augmentSlot, hE0, hE1]
  have hEr : E.comp (MvPolynomial.rename (fun a : Fin 1 × ℕ => (1,a.2))) =
      MvPolynomial.rename Prod.snd := by
    ext a : 1
    simp [AlgHom.comp_apply,hE1]
  have hEs {n : ℤ} (m : MilnorMonomial n) : E (splitMonomial m) = MvPolynomial.monomial m.val 1 := by
    have h := augmentSlot_splitSlot_left (0 : Fin 1) (monomialPolynomial m)
    have h' := congrArg E h
    change (E.comp (augmentSlot 0)) (splitMonomial m) = _ at h'
    rw [hEa] at h'
    have hf : (fun a : Fin 1 × ℕ => ((0 : Fin 1).castSucc.succAbove a.1, a.2)) =
        (fun a : Fin 1 × ℕ => (1,a.2)) := by
      funext ⟨i,j⟩
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      rfl
    change E (splitMonomial m) = E (MvPolynomial.rename _ (monomialPolynomial m)) at h'
    rw [hf] at h'
    change E (splitMonomial m) = (E.comp (MvPolynomial.rename (fun a : Fin 1 × ℕ => (1,a.2)))) (monomialPolynomial m) at h'
    rw [hEr] at h'
    rw [h']
    simp only [monomialPolynomial, MvPolynomial.rename_monomial]
    apply congrArg (fun d : ℕ →₀ ℕ => MvPolynomial.monomial d (1 : F2))
    ext j
    have hproj : Function.Injective (Prod.snd : Fin 1 × ℕ → ℕ) := by
      intro a b h
      exact Prod.ext (Subsingleton.elim _ _) h
    rw [show j = Prod.snd ((0 : Fin 1),j) from rfl, Finsupp.mapDomain_apply hproj]
    exact congrArg (fun f => f (0 : Fin 1) j) ((slotExponentsEquiv 1).apply_symm_apply (fun _ => m.val))
  have hEm (d : (Fin 2 × ℕ) →₀ ℕ) : E (MvPolynomial.monomial d 1) =
      if (slotWeight (slotExponentsEquiv 2 d 0) : ℤ) = 0 then
        MvPolynomial.monomial (slotExponentsEquiv 2 d 1) 1 else 0 := by
    have hs : (↑d.support : Set (Fin 2 × ℕ)) ⊆ Set.range e ↔
        slotExponentsEquiv 2 d 0 = 0 := by
      constructor
      · intro h
        ext j
        by_contra hj
        have hd : (0,j) ∈ d.support := Finsupp.mem_support_iff.mpr hj
        obtain ⟨k,hk⟩ := h hd
        have := congrArg Prod.fst hk
        norm_num [e] at this
      · intro h ⟨i,j⟩ hd
        fin_cases i
        · have hz := congrArg (fun f : ℕ →₀ ℕ => f j) h
          exact (Finsupp.mem_support_iff.mp hd hz).elim
        · exact ⟨j,rfl⟩
    have hw : (slotWeight (slotExponentsEquiv 2 d 0) : ℤ) = 0 ↔
        slotExponentsEquiv 2 d 0 = 0 := by
      rw [Nat.cast_eq_zero, slotWeight_eq_zero_iff]
    change (MvPolynomial.monomial d (1 : F2)).killCompl e.injective = _
    rw [MvPolynomial.killCompl_monomial]
    simp only [hs, hw]
    split_ifs
    · apply congrArg (fun d : ℕ →₀ ℕ => MvPolynomial.monomial d (1 : F2))
      ext j
      rfl
    · rfl
  have htensor {A B C D : ModuleCat F2} (f : A ⟶ B) (g : C ⟶ D) (x : A) (y : C) :
      (f ⊗ₘ g).hom (x ⊗ₜ[F2] y) = f.hom x ⊗ₜ[F2] g.hom y :=
    TensorProduct.map_tmul _ _ _ _
  have hT (a b n : ℤ) (h : a + b = n) (x : Carrier a) (y : Carrier b) :
      ((counit ▷ dualSteenrodGraded) n).hom
        ((GradedObject.Monoidal.ιTensorObj dualSteenrodGraded dualSteenrodGraded a b n h).hom
          (x ⊗ₜ[F2] y)) =
        (GradedObject.Monoidal.ιTensorObj (𝟙_ (GrVect F2)) dualSteenrodGraded a b n h).hom
          ((counit a).hom x ⊗ₜ[F2] y) := by
    have hh := GradedObject.Monoidal.ι_tensorHom counit (𝟙 dualSteenrodGraded) a b n h
    have hh' := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom hh) (x ⊗ₜ[F2] y)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hh'
    refine hh'.trans ?_
    exact congrArg (GradedObject.Monoidal.ιTensorObj (𝟙_ (GrVect F2)) dualSteenrodGraded a b n h).hom
      (htensor (counit a) (𝟙 (dualSteenrodGraded b)) x y)
  have hunitor {A B : ModuleCat F2} (f : ModuleCat.of F2 F2 ⟶ B) (y : A) :
      ((λ_ A).inv ≫ f ▷ A).hom y = f.hom 1 ⊗ₜ[F2] y := by
    change f.hom.rTensor A ((TensorProduct.lid F2 A).symm y) = _
    rfl
  have hc : (counit 0).hom (Finsupp.single zeroMilnorMonomial 1) =
      (show ModuleCat.of F2 F2 ⟶ (𝟙_ (GrVect F2)) 0 from
        GradedObject.Monoidal.tensorUnit₀.inv).hom 1 := by
    exact congrArg (show ModuleCat.of F2 F2 ⟶ (𝟙_ (GrVect F2)) 0 from
      GradedObject.Monoidal.tensorUnit₀.inv).hom (Finsupp.single_eq_same)
  have hunit (a b n : ℤ) (h : a + b = n) (m0 : MilnorMonomial a) (m1 : MilnorMonomial b) :
      ((counit ▷ dualSteenrodGraded) n).hom
        ((GradedObject.Monoidal.ιTensorObj dualSteenrodGraded dualSteenrodGraded a b n h).hom
          (Finsupp.single m0 1 ⊗ₜ[F2] Finsupp.single m1 1)) =
        ((λ_ dualSteenrodGraded).inv n).hom
          (if ha : a = 0 then Finsupp.single ⟨m1.val, by simpa [ha] using m1.property.trans (by omega)⟩ 1 else 0) := by
    rw [hT]
    by_cases ha : a = 0
    · subst a
      have hb : b = n := by omega
      subst b
      rw [milnorMonomial_zero_eq m0]
      change (GradedObject.Monoidal.ιTensorObj (𝟙_ (GrVect F2)) dualSteenrodGraded 0 n n h).hom
        ((counit 0).hom (Finsupp.single zeroMilnorMonomial 1) ⊗ₜ[F2] Finsupp.single m1 1) =
        ((GradedObject.Monoidal.leftUnitor dualSteenrodGraded).inv n).hom (Finsupp.single m1 1)
      rw [hc, GradedObject.Monoidal.leftUnitor_inv_apply]
      exact (congrArg
        (GradedObject.Monoidal.ιTensorObj (𝟙_ (GrVect F2)) dualSteenrodGraded 0 n n h).hom
        (hunitor (show ModuleCat.of F2 F2 ⟶ (𝟙_ (GrVect F2)) 0 from
          GradedObject.Monoidal.tensorUnit₀.inv) (Finsupp.single m1 1))).symm
    · simp [ha, counit]
  have hlinearSum {J : Type} {A B : ModuleCat F2} (f : A ⟶ B)
      (s : Finset J) (c : J → F2) (z : J → A) :
      ∑ x ∈ s, c x • f.hom (z x) = f.hom (∑ x ∈ s, c x • z x) := by
    simp

  have hb {n : ℤ} (m : MilnorMonomial n) :
      ((counit ▷ dualSteenrodGraded) n).hom (comultiplicationMonomial m) =
        ((λ_ dualSteenrodGraded).inv n).hom (Finsupp.single m 1) := by
    let Q : Carrier n →ₗ[F2] MvPolynomial ℕ F2 :=
      Finsupp.linearCombination F2 (fun m => MvPolynomial.monomial m.val 1)
    have hQ : Function.Injective Q :=
      ((MvPolynomial.basisMonomials ℕ F2).linearIndependent.comp _ Subtype.val_injective).finsuppLinearCombination_injective
    let z (d : {d // d ∈ (splitMonomial m).support}) : Carrier n :=
      if ha : (slotWeight (slotExponentsEquiv 2 d.val 0) : ℤ) = 0 then
        Finsupp.single ⟨slotExponentsEquiv 2 d.val 1, by
          have := splitMonomial_support_degree m d.val d.property
          simpa [ha] using this⟩ 1 else 0
    have hz (d : {d // d ∈ (splitMonomial m).support}) :
        Q (z d) = E (MvPolynomial.monomial d.val 1) := by
      rw [hEm]
      dsimp [z]
      split_ifs with h
      · simp [Q, Finsupp.linearCombination_single]
      · simp
    have hzsum : ∑ d ∈ (splitMonomial m).support.attach,
        MvPolynomial.coeff d.val (splitMonomial m) • z d = Finsupp.single m 1 := by
      apply hQ
      simp only [map_sum, map_smul, hz]
      simp only [← map_smul, ← map_sum, smul_eq_mul, mul_one]
      have hsum := (Finset.sum_attach (splitMonomial m).support
        (fun d => MvPolynomial.monomial d (MvPolynomial.coeff d (splitMonomial m)))).trans
        (MvPolynomial.support_sum_monomial_coeff (splitMonomial m))
      rw [hsum]
      rw [hEs]
      simp [Q, Finsupp.linearCombination_single]
    unfold comultiplicationMonomial
    simp only [map_sum, map_smul, hunit]
    change ∑ d ∈ (splitMonomial m).support.attach,
      MvPolynomial.coeff d.val (splitMonomial m) • ((λ_ dualSteenrodGraded).inv n).hom (z d) = _
    exact (hlinearSum ((λ_ dualSteenrodGraded).inv n) _ _ _).trans
      (congrArg ((λ_ dualSteenrodGraded).inv n).hom hzsum)
  funext n
  apply ModuleCat.hom_ext
  apply Finsupp.lhom_ext
  intro m r
  change ((counit ▷ dualSteenrodGraded) n).hom
      ((Finsupp.linearCombination F2 comultiplicationMonomial) (Finsupp.single m r)) =
    ((λ_ dualSteenrodGraded).inv n).hom (Finsupp.single m r)
  rw [Finsupp.linearCombination_single, map_smul, hb]
  have hh : r • Finsupp.single m (1 : F2) = Finsupp.single m r := by simp
  exact (((λ_ dualSteenrodGraded).inv n).hom.map_smul r (Finsupp.single m 1)).symm.trans
    (congrArg ((λ_ dualSteenrodGraded).inv n).hom hh)

/-- Right counitality of the prescribed Milnor coproduct. -/
theorem comultiplication_counit_right :
    comultiplication ≫ dualSteenrodGraded ◁ counit =
      (ρ_ dualSteenrodGraded).inv := by
  classical
  let e : ℕ ↪ Fin 2 × ℕ := ⟨fun j => (0,j), fun _ _ h => congrArg Prod.snd h⟩
  let E : TensorPower 2 →ₐ[F2] MvPolynomial ℕ F2 := MvPolynomial.killCompl e.injective
  have hE0 (j : ℕ) : E (MvPolynomial.X (1,j)) = 0 := by
    simp [E, MvPolynomial.killCompl, e]
  have hE1 (j : ℕ) : E (MvPolynomial.X (0,j)) = MvPolynomial.X j := by
    have h := MvPolynomial.killCompl_rename_app e.injective (MvPolynomial.X j : MvPolynomial ℕ F2)
    simpa [e] using h
  have hEa : E.comp (augmentSlot (1 : Fin 2)) = E := by
    ext a : 1
    rcases a with ⟨i,j⟩
    fin_cases i <;> simp [AlgHom.comp_apply, augmentSlot, hE0, hE1]
  have hEr : E.comp (MvPolynomial.rename (fun a : Fin 1 × ℕ => (0,a.2))) =
      MvPolynomial.rename Prod.snd := by
    ext a : 1
    simp [AlgHom.comp_apply,hE1]
  have hEs {n : ℤ} (m : MilnorMonomial n) : E (splitMonomial m) = MvPolynomial.monomial m.val 1 := by
    have h := augmentSlot_splitSlot_right (0 : Fin 1) (monomialPolynomial m)
    have h' := congrArg E h
    change (E.comp (augmentSlot 1)) (splitMonomial m) = _ at h'
    rw [hEa] at h'
    have hf : (fun a : Fin 1 × ℕ => ((0 : Fin 1).succ.succAbove a.1, a.2)) =
        (fun a : Fin 1 × ℕ => (0,a.2)) := by
      funext ⟨i,j⟩
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      rfl
    change E (splitMonomial m) = E (MvPolynomial.rename _ (monomialPolynomial m)) at h'
    rw [hf] at h'
    change E (splitMonomial m) = (E.comp (MvPolynomial.rename (fun a : Fin 1 × ℕ => (0,a.2)))) (monomialPolynomial m) at h'
    rw [hEr] at h'
    rw [h']
    simp only [monomialPolynomial, MvPolynomial.rename_monomial]
    apply congrArg (fun d : ℕ →₀ ℕ => MvPolynomial.monomial d (1 : F2))
    ext j
    have hproj : Function.Injective (Prod.snd : Fin 1 × ℕ → ℕ) := by
      intro a b h
      exact Prod.ext (Subsingleton.elim _ _) h
    rw [show j = Prod.snd ((0 : Fin 1),j) from rfl, Finsupp.mapDomain_apply hproj]
    exact congrArg (fun f => f (0 : Fin 1) j) ((slotExponentsEquiv 1).apply_symm_apply (fun _ => m.val))
  have hEm (d : (Fin 2 × ℕ) →₀ ℕ) : E (MvPolynomial.monomial d 1) =
      if (slotWeight (slotExponentsEquiv 2 d 1) : ℤ) = 0 then
        MvPolynomial.monomial (slotExponentsEquiv 2 d 0) 1 else 0 := by
    have hs : (↑d.support : Set (Fin 2 × ℕ)) ⊆ Set.range e ↔
        slotExponentsEquiv 2 d 1 = 0 := by
      constructor
      · intro h
        ext j
        by_contra hj
        have hd : (1,j) ∈ d.support := Finsupp.mem_support_iff.mpr hj
        obtain ⟨k,hk⟩ := h hd
        have := congrArg Prod.fst hk
        norm_num [e] at this
      · intro h ⟨i,j⟩ hd
        fin_cases i
        · exact ⟨j,rfl⟩
        · have hz := congrArg (fun f : ℕ →₀ ℕ => f j) h
          exact (Finsupp.mem_support_iff.mp hd hz).elim
    have hw : (slotWeight (slotExponentsEquiv 2 d 1) : ℤ) = 0 ↔
        slotExponentsEquiv 2 d 1 = 0 := by
      rw [Nat.cast_eq_zero, slotWeight_eq_zero_iff]
    change (MvPolynomial.monomial d (1 : F2)).killCompl e.injective = _
    rw [MvPolynomial.killCompl_monomial]
    simp only [hs, hw]
    split_ifs
    · apply congrArg (fun d : ℕ →₀ ℕ => MvPolynomial.monomial d (1 : F2))
      ext j
      rfl
    · rfl
  have htensor {A B C D : ModuleCat F2} (f : A ⟶ B) (g : C ⟶ D) (x : A) (y : C) :
      (f ⊗ₘ g).hom (x ⊗ₜ[F2] y) = f.hom x ⊗ₜ[F2] g.hom y :=
    TensorProduct.map_tmul _ _ _ _
  have hT (a b n : ℤ) (h : a + b = n) (x : Carrier a) (y : Carrier b) :
      ((dualSteenrodGraded ◁ counit) n).hom
        ((GradedObject.Monoidal.ιTensorObj dualSteenrodGraded dualSteenrodGraded a b n h).hom
          (x ⊗ₜ[F2] y)) =
        (GradedObject.Monoidal.ιTensorObj dualSteenrodGraded (𝟙_ (GrVect F2)) a b n h).hom
          (x ⊗ₜ[F2] (counit b).hom y) := by
    have hh := GradedObject.Monoidal.ι_tensorHom (𝟙 dualSteenrodGraded) counit a b n h
    have hh' := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom hh) (x ⊗ₜ[F2] y)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hh'
    refine hh'.trans ?_
    exact congrArg (GradedObject.Monoidal.ιTensorObj dualSteenrodGraded (𝟙_ (GrVect F2)) a b n h).hom
      (htensor (𝟙 (dualSteenrodGraded a)) (counit b) x y)
  have hunitor {A B : ModuleCat F2} (f : ModuleCat.of F2 F2 ⟶ B) (y : A) :
      ((ρ_ A).inv ≫ A ◁ f).hom y = y ⊗ₜ[F2] f.hom 1 := by
    change f.hom.lTensor A ((TensorProduct.rid F2 A).symm y) = _
    rfl
  have hc : (counit 0).hom (Finsupp.single zeroMilnorMonomial 1) =
      (show ModuleCat.of F2 F2 ⟶ (𝟙_ (GrVect F2)) 0 from
        GradedObject.Monoidal.tensorUnit₀.inv).hom 1 := by
    exact congrArg (show ModuleCat.of F2 F2 ⟶ (𝟙_ (GrVect F2)) 0 from
      GradedObject.Monoidal.tensorUnit₀.inv).hom (Finsupp.single_eq_same)
  have hunit (a b n : ℤ) (h : a + b = n) (m0 : MilnorMonomial a) (m1 : MilnorMonomial b) :
      ((dualSteenrodGraded ◁ counit) n).hom
        ((GradedObject.Monoidal.ιTensorObj dualSteenrodGraded dualSteenrodGraded a b n h).hom
          (Finsupp.single m0 1 ⊗ₜ[F2] Finsupp.single m1 1)) =
        ((ρ_ dualSteenrodGraded).inv n).hom
          (if hb : b = 0 then Finsupp.single ⟨m0.val, by simpa [hb] using m0.property.trans (by omega)⟩ 1 else 0) := by
    rw [hT]
    by_cases hb : b = 0
    · subst b
      have ha : a = n := by omega
      subst a
      rw [milnorMonomial_zero_eq m1]
      change (GradedObject.Monoidal.ιTensorObj dualSteenrodGraded (𝟙_ (GrVect F2)) n 0 n h).hom
        (Finsupp.single m0 1 ⊗ₜ[F2] (counit 0).hom (Finsupp.single zeroMilnorMonomial 1)) =
        ((GradedObject.Monoidal.rightUnitor dualSteenrodGraded).inv n).hom (Finsupp.single m0 1)
      rw [hc, GradedObject.Monoidal.rightUnitor_inv_apply]
      exact (congrArg
        (GradedObject.Monoidal.ιTensorObj dualSteenrodGraded (𝟙_ (GrVect F2)) n 0 n h).hom
        (hunitor (show ModuleCat.of F2 F2 ⟶ (𝟙_ (GrVect F2)) 0 from
          GradedObject.Monoidal.tensorUnit₀.inv) (Finsupp.single m0 1))).symm
    · simp [hb, counit]
  have hlinearSum {J : Type} {A B : ModuleCat F2} (f : A ⟶ B)
      (s : Finset J) (c : J → F2) (z : J → A) :
      ∑ x ∈ s, c x • f.hom (z x) = f.hom (∑ x ∈ s, c x • z x) := by
    simp

  have hb {n : ℤ} (m : MilnorMonomial n) :
      ((dualSteenrodGraded ◁ counit) n).hom (comultiplicationMonomial m) =
        ((ρ_ dualSteenrodGraded).inv n).hom (Finsupp.single m 1) := by
    let Q : Carrier n →ₗ[F2] MvPolynomial ℕ F2 :=
      Finsupp.linearCombination F2 (fun m => MvPolynomial.monomial m.val 1)
    have hQ : Function.Injective Q :=
      ((MvPolynomial.basisMonomials ℕ F2).linearIndependent.comp _ Subtype.val_injective).finsuppLinearCombination_injective
    let z (d : {d // d ∈ (splitMonomial m).support}) : Carrier n :=
      if ha : (slotWeight (slotExponentsEquiv 2 d.val 1) : ℤ) = 0 then
        Finsupp.single ⟨slotExponentsEquiv 2 d.val 0, by
          have := splitMonomial_support_degree m d.val d.property
          simpa [ha] using this⟩ 1 else 0
    have hz (d : {d // d ∈ (splitMonomial m).support}) :
        Q (z d) = E (MvPolynomial.monomial d.val 1) := by
      rw [hEm]
      dsimp [z]
      split_ifs with h
      · simp [Q, Finsupp.linearCombination_single]
      · simp
    have hzsum : ∑ d ∈ (splitMonomial m).support.attach,
        MvPolynomial.coeff d.val (splitMonomial m) • z d = Finsupp.single m 1 := by
      apply hQ
      simp only [map_sum, map_smul, hz]
      simp only [← map_smul, ← map_sum, smul_eq_mul, mul_one]
      have hsum := (Finset.sum_attach (splitMonomial m).support
        (fun d => MvPolynomial.monomial d (MvPolynomial.coeff d (splitMonomial m)))).trans
        (MvPolynomial.support_sum_monomial_coeff (splitMonomial m))
      rw [hsum]
      rw [hEs]
      simp [Q, Finsupp.linearCombination_single]
    unfold comultiplicationMonomial
    simp only [map_sum, map_smul, hunit]
    change ∑ d ∈ (splitMonomial m).support.attach,
      MvPolynomial.coeff d.val (splitMonomial m) • ((ρ_ dualSteenrodGraded).inv n).hom (z d) = _
    exact (hlinearSum ((ρ_ dualSteenrodGraded).inv n) _ _ _).trans
      (congrArg ((ρ_ dualSteenrodGraded).inv n).hom hzsum)
  funext n
  apply ModuleCat.hom_ext
  apply Finsupp.lhom_ext
  intro m r
  change ((dualSteenrodGraded ◁ counit) n).hom
      ((Finsupp.linearCombination F2 comultiplicationMonomial) (Finsupp.single m r)) =
    ((ρ_ dualSteenrodGraded).inv n).hom (Finsupp.single m r)
  rw [Finsupp.linearCombination_single, map_smul, hb]
  have hh : r • Finsupp.single m (1 : F2) = Finsupp.single m r := by simp
  exact (((ρ_ dualSteenrodGraded).inv n).hom.map_smul r (Finsupp.single m 1)).symm.trans
    (congrArg ((ρ_ dualSteenrodGraded).inv n).hom hh)

private theorem milnor_splitSlot_assoc (p : TensorPower 1) :
    splitSlot (s:=2) 1 (splitSlot (s:=1) 0 p) =
      splitSlot (s:=2) 0 (splitSlot (s:=1) 0 p) := by
  have hs (slot : Fin 2) (n : ℕ) : splitSlot slot (xi slot n) =
      ∑ r ∈ Finset.range (n+1), xi slot.castSucc (n-r) ^ (2^r) * xi slot.succ r := by
    cases n with
    | zero => simp [xi]
    | succ n => simp [xi, splitSlot, coproductGenerator]
  have h10 (n : ℕ) : splitSlot (s:=2) 1 (xi 0 n) = xi 0 n := by
    cases n <;> simp [xi, splitSlot]
  have h01 (n : ℕ) : splitSlot (s:=2) 0 (xi 1 n) = xi 2 n := by
    cases n <;> simp [xi, splitSlot]
  have h : (splitSlot (s:=2) 1).comp (splitSlot (s:=1) 0) =
      (splitSlot (s:=2) 0).comp (splitSlot (s:=1) 0) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨a,n⟩
    have ha : a = 0 := Subsingleton.elim _ _
    subst a
    simp only [AlgHom.comp_apply, splitSlot, MvPolynomial.aeval_X, if_true]
    change splitSlot (s:=2) 1 (∑ r ∈ Finset.range (n+2),
      xi (0 : Fin 2) (n+1-r) ^ (2^r) * xi 1 r) =
      splitSlot (s:=2) 0 (∑ r ∈ Finset.range (n+2),
      xi (0 : Fin 2) (n+1-r) ^ (2^r) * xi 1 r)
    simp only [map_sum, map_mul, map_pow, hs, h10, h01]
    simp only [Finset.mul_sum, sum_pow_char_pow, Finset.sum_mul, mul_pow]
    let f (u v : ℕ) : TensorPower 3 :=
      xi 0 (n+1-(u+v)) ^ (2^(u+v)) * xi 1 v ^ (2^u) * xi 2 u
    calc
      _ = ∑ r ∈ Finset.range (n+2), ∑ s ∈ Finset.range (r+1), f s (r-s) := by
        apply Finset.sum_congr rfl
        intro r hr
        apply Finset.sum_congr rfl
        intro s hs
        have hsr : s ≤ r := by simpa using hs
        simp only [f, Nat.add_sub_of_le hsr]
        exact (mul_assoc _ _ _).symm
      _ = ∑ r ∈ Finset.range (n+2), ∑ s ∈ Finset.range (n+2-r), f r s :=
        Finset.sum_range_diag_flip (n+2) f
      _ = _ := by
        apply Finset.sum_congr rfl
        intro r hr
        have hrn : r ≤ n+1 := by have := Finset.mem_range.mp hr; omega
        have he : n+2-r = n+1-r+1 := by omega
        rw [he]
        apply Finset.sum_congr rfl
        intro s hs
        dsimp [f]
        rw [← pow_mul, ← pow_add]
        simp only [Nat.sub_sub, add_comm r s]
  exact AlgHom.congr_fun h p


/-- Coassociativity, with the actual Cauchy tensor associator. -/
theorem comultiplication_assoc :
    comultiplication ≫ dualSteenrodGraded ◁ comultiplication =
      comultiplication ≫ (comultiplication ▷ dualSteenrodGraded) ≫
        (α_ dualSteenrodGraded dualSteenrodGraded dualSteenrodGraded).hom := by
  classical
  have hconstr {s : ℕ} {M : Type} [AddCommGroup M] [Module F2 M]
      (v : ((Fin s × ℕ) →₀ ℕ) → M) (d : (Fin s × ℕ) →₀ ℕ) (r : F2) :
      ((MvPolynomial.basisMonomials (Fin s × ℕ) F2).constr F2) v (MvPolynomial.monomial d r) = r • v d := by
    rw [show MvPolynomial.monomial d r = r • (MvPolynomial.basisMonomials (Fin s × ℕ) F2) d from by
      simp only [MvPolynomial.coe_basisMonomials, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]]
    simp only [map_smul, Module.Basis.constr_basis]
  let Q₃ (n : ℤ) : TensorPower 3 →ₗ[F2]
      ↑(GradedObject.Monoidal.tensorObj dualSteenrodGraded (GradedObject.Monoidal.tensorObj dualSteenrodGraded dualSteenrodGraded) n) :=
    ((MvPolynomial.basisMonomials (Fin 3 × ℕ) F2).constr F2) fun d =>
      if h : (slotWeight (slotExponentsEquiv 3 d 0) : ℤ) +
          (slotWeight (slotExponentsEquiv 3 d 1) : ℤ) +
          (slotWeight (slotExponentsEquiv 3 d 2) : ℤ) = n then
        (GradedObject.Monoidal.ιTensorObj₃ dualSteenrodGraded dualSteenrodGraded dualSteenrodGraded
          (slotWeight (slotExponentsEquiv 3 d 0) : ℤ)
          (slotWeight (slotExponentsEquiv 3 d 1) : ℤ)
          (slotWeight (slotExponentsEquiv 3 d 2) : ℤ) n h).hom
          ((Finsupp.single ⟨slotExponentsEquiv 3 d 0,rfl⟩ 1 : Carrier _) ⊗ₜ[F2]
            ((Finsupp.single ⟨slotExponentsEquiv 3 d 1,rfl⟩ 1 : Carrier _) ⊗ₜ[F2]
              (Finsupp.single ⟨slotExponentsEquiv 3 d 2,rfl⟩ 1 : Carrier _)))
      else 0
  let f₀ : ℕ → Fin 2 × ℕ := fun j => (0,j)
  let f₁ : ℕ → Fin 2 × ℕ := fun j => (1,j)
  have hf₀ : Function.Injective f₀ := fun _ _ h => congrArg Prod.snd h
  have hf₁ : Function.Injective f₁ := fun _ _ h => congrArg Prod.snd h
  have hd₂ (d : (Fin 2 × ℕ) →₀ ℕ) :
      d = (slotExponentsEquiv 2 d 0).mapDomain f₀ +
        (slotExponentsEquiv 2 d 1).mapDomain f₁ := by
    ext ⟨i,j⟩
    fin_cases i
    · change d (0,j) = ((slotExponentsEquiv 2 d 0).mapDomain f₀ + (slotExponentsEquiv 2 d 1).mapDomain f₁) (0,j)
      rw [Finsupp.add_apply, Finsupp.mapDomain_apply hf₀ _ j,
        Finsupp.mapDomain_notin_range _ _ (by simp [f₁])]
      rfl
    · change d (1,j) = ((slotExponentsEquiv 2 d 0).mapDomain f₀ + (slotExponentsEquiv 2 d 1).mapDomain f₁) (1,j)
      rw [Finsupp.add_apply, Finsupp.mapDomain_notin_range _ _ (by simp [f₀]),
        Finsupp.mapDomain_apply hf₁ _ j, zero_add]
      rfl
  let g₀ : ℕ → Fin 3 × ℕ := fun j => (0,j)
  let g₁₂ : Fin 2 × ℕ → Fin 3 × ℕ := fun a => (a.1.succ,a.2)
  have hg₀ : Function.Injective g₀ := fun _ _ h => congrArg Prod.snd h
  have hg₁₂ : Function.Injective g₁₂ := by
    intro a b h
    exact Prod.ext (Fin.succ_injective _ (congrArg Prod.fst h)) (congrArg (fun x : Fin 3 × ℕ => x.2) h)
  let joinL (d : ℕ →₀ ℕ) (e : (Fin 2 × ℕ) →₀ ℕ) := d.mapDomain g₀ + e.mapDomain g₁₂
  have hjoinL₀ (d : ℕ →₀ ℕ) (e : (Fin 2 × ℕ) →₀ ℕ) :
      slotExponentsEquiv 3 (joinL d e) 0 = d := by
    ext j
    change (d.mapDomain g₀ + e.mapDomain g₁₂) (0,j) = d j
    rw [Finsupp.add_apply, Finsupp.mapDomain_apply hg₀ _ j,
      Finsupp.mapDomain_notin_range _ _ (by simp [g₁₂])]
    simp
  have hjoinL₁₂ (d : ℕ →₀ ℕ) (e : (Fin 2 × ℕ) →₀ ℕ) (i : Fin 2) :
      slotExponentsEquiv 3 (joinL d e) i.succ = slotExponentsEquiv 2 e i := by
    ext j
    change (d.mapDomain g₀ + e.mapDomain g₁₂) (i.succ,j) = e (i,j)
    rw [Finsupp.add_apply, Finsupp.mapDomain_notin_range _ _ (by simp [g₀, Ne.symm (Fin.succ_ne_zero i)]),
      Finsupp.mapDomain_apply hg₁₂ _ (i,j)]
    simp
  let u : ℕ → Fin 1 × ℕ := fun j => (0,j)
  have hu : Function.Injective u := fun _ _ h => congrArg Prod.snd h
  have hmono {n : ℤ} (m : MilnorMonomial n) :
      monomialPolynomial m = MvPolynomial.rename u (MvPolynomial.monomial m.val 1) := by
    simp only [monomialPolynomial, MvPolynomial.rename_monomial]
    apply congrArg (fun d : (Fin 1 × ℕ) →₀ ℕ => MvPolynomial.monomial d (1 : F2))
    apply (slotExponentsEquiv 1).injective
    rw [Equiv.apply_symm_apply]
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    ext j
    exact (Finsupp.mapDomain_apply hu m.val j).symm
  have hsL₀ : (splitSlot (s := 2) 1).comp (MvPolynomial.rename f₀) =
      MvPolynomial.rename g₀ := by
    ext j : 1
    simp [AlgHom.comp_apply, splitSlot, f₀, g₀]
  have hsL₁ : (splitSlot (s := 2) 1).comp (MvPolynomial.rename f₁) =
      (MvPolynomial.rename g₁₂).comp ((splitSlot (s := 1) 0).comp (MvPolynomial.rename u)) := by
    ext j : 1
    simp only [AlgHom.comp_apply, MvPolynomial.rename_X]
    change (splitSlot (s := 2) 1) (MvPolynomial.X (1,j)) =
      MvPolynomial.rename g₁₂ ((splitSlot (s := 1) 0) (MvPolynomial.X (0,j)))
    simp only [splitSlot, MvPolynomial.aeval_X]
    exact (rename_coproductGenerator Fin.succ (0 : Fin 1) (1 : Fin 2) rfl rfl j).symm
  have hfactorL (d : (Fin 2 × ℕ) →₀ ℕ) :
      splitSlot (s := 2) 1 (MvPolynomial.monomial d 1) =
        MvPolynomial.rename g₀ (MvPolynomial.monomial (slotExponentsEquiv 2 d 0) 1) *
          MvPolynomial.rename g₁₂ (splitMonomial (slotMonomial d 1)) := by
    have hm : (MvPolynomial.monomial d (1 : F2)) =
        MvPolynomial.rename f₀ (MvPolynomial.monomial (slotExponentsEquiv 2 d 0) 1) *
          MvPolynomial.rename f₁ (MvPolynomial.monomial (slotExponentsEquiv 2 d 1) 1) := by
      simp only [MvPolynomial.rename_monomial, MvPolynomial.monomial_mul, one_mul]
      rw [← hd₂]
    rw [hm, map_mul]
    have hl := AlgHom.congr_fun hsL₀ (MvPolynomial.monomial (slotExponentsEquiv 2 d 0) 1)
    have hr := AlgHom.congr_fun hsL₁ (MvPolynomial.monomial (slotExponentsEquiv 2 d 1) 1)
    rw [AlgHom.comp_apply] at hl hr
    rw [hl, hr]
    rw [splitMonomial, hmono]
    rfl
  have hQ₃L {a b n : ℤ} (h : a + b = n) (m0 : MilnorMonomial a)
      (e : (Fin 2 × ℕ) →₀ ℕ)
      (he : (slotWeight (slotExponentsEquiv 2 e 0) : ℤ) +
        (slotWeight (slotExponentsEquiv 2 e 1) : ℤ) = b) :
      Q₃ n (MvPolynomial.monomial (joinL m0.val e) 1) =
        (GradedObject.Monoidal.ιTensorObj dualSteenrodGraded
          (GradedObject.Monoidal.tensorObj dualSteenrodGraded dualSteenrodGraded) a b n h).hom
          (Finsupp.single m0 1 ⊗ₜ[F2]
            (GradedObject.Monoidal.ιTensorObj dualSteenrodGraded dualSteenrodGraded
              (slotWeight (slotExponentsEquiv 2 e 0) : ℤ)
              (slotWeight (slotExponentsEquiv 2 e 1) : ℤ) b he).hom
              (Finsupp.single (slotMonomial e 0) 1 ⊗ₜ[F2]
                Finsupp.single (slotMonomial e 1) 1)) := by
    rcases m0 with ⟨d0,rfl⟩
    have he0 := hjoinL₀ d0 e
    have he1 := hjoinL₁₂ d0 e 0
    have he2 := hjoinL₁₂ d0 e 1
    change slotExponentsEquiv 3 (joinL d0 e) 1 = slotExponentsEquiv 2 e 0 at he1
    change slotExponentsEquiv 3 (joinL d0 e) 2 = slotExponentsEquiv 2 e 1 at he2
    dsimp only [Q₃]
    rw [hconstr, one_smul]
    generalize hx0 : slotExponentsEquiv 3 (joinL d0 e) 0 = a0 at he0 ⊢
    generalize hx1 : slotExponentsEquiv 3 (joinL d0 e) 1 = a1 at he1 ⊢
    generalize hx2 : slotExponentsEquiv 3 (joinL d0 e) 2 = a2 at he2 ⊢
    clear hx0 hx1 hx2
    subst a0 a1 a2
    rw [dif_pos (by omega)]
    rw [GradedObject.Monoidal.ιTensorObj₃_eq _ _ _ _ _ _ n _ b he]
    rfl
  have hblockL {a b n : ℤ} (h : a + b = n) (m0 : MilnorMonomial a) (m1 : MilnorMonomial b) :
      Q₃ n (MvPolynomial.rename g₀ (MvPolynomial.monomial m0.val 1) *
          MvPolynomial.rename g₁₂ (splitMonomial m1)) =
        (GradedObject.Monoidal.ιTensorObj dualSteenrodGraded
          (GradedObject.Monoidal.tensorObj dualSteenrodGraded dualSteenrodGraded) a b n h).hom
          (Finsupp.single m0 1 ⊗ₜ[F2] comultiplicationMonomial m1) := by
    let L : ↑(GradedObject.Monoidal.tensorObj dualSteenrodGraded dualSteenrodGraded b) →ₗ[F2]
        ↑(GradedObject.Monoidal.tensorObj dualSteenrodGraded
          (GradedObject.Monoidal.tensorObj dualSteenrodGraded dualSteenrodGraded) n) :=
      (GradedObject.Monoidal.ιTensorObj dualSteenrodGraded
        (GradedObject.Monoidal.tensorObj dualSteenrodGraded dualSteenrodGraded) a b n h).hom.comp
        (TensorProduct.mk F2 (Carrier a) _ (Finsupp.single m0 1))
    change _ = L (comultiplicationMonomial m1)
    have hs := (Finset.sum_attach (splitMonomial m1).support
      (fun d => MvPolynomial.monomial d (MvPolynomial.coeff d (splitMonomial m1)))).trans
      (MvPolynomial.support_sum_monomial_coeff (splitMonomial m1))
    conv_lhs => rw [← hs]
    simp only [map_sum, Finset.mul_sum]
    unfold comultiplicationMonomial
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro e he
    simp only [MvPolynomial.rename_monomial, MvPolynomial.monomial_mul, one_mul]
    have hh : MvPolynomial.monomial (joinL m0.val e.val)
        (MvPolynomial.coeff e.val (splitMonomial m1)) =
        MvPolynomial.coeff e.val (splitMonomial m1) • MvPolynomial.monomial (joinL m0.val e.val) 1 := by
      simp only [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
    change Q₃ n (MvPolynomial.monomial (joinL m0.val e.val) _) = _
    rw [hh, map_smul, hQ₃L h m0 e.val (splitMonomial_support_degree m1 e.val e.property)]
    exact (L.map_smul _ _).symm
  have htensor {A B C D : ModuleCat F2} (f : A ⟶ B) (g : C ⟶ D) (x : A) (y : C) :
      (f ⊗ₘ g).hom (x ⊗ₜ[F2] y) = f.hom x ⊗ₜ[F2] g.hom y :=
    TensorProduct.map_tmul _ _ _ _
  have hTL (a b n : ℤ) (h : a + b = n) (m0 : MilnorMonomial a) (m1 : MilnorMonomial b) :
      ((dualSteenrodGraded ◁ comultiplication) n).hom
        ((GradedObject.Monoidal.ιTensorObj dualSteenrodGraded dualSteenrodGraded a b n h).hom
          (Finsupp.single m0 1 ⊗ₜ[F2] Finsupp.single m1 1)) =
        (GradedObject.Monoidal.ιTensorObj dualSteenrodGraded
          (GradedObject.Monoidal.tensorObj dualSteenrodGraded dualSteenrodGraded) a b n h).hom
          (Finsupp.single m0 1 ⊗ₜ[F2] comultiplicationMonomial m1) := by
    have hh := GradedObject.Monoidal.ι_tensorHom (𝟙 dualSteenrodGraded) comultiplication a b n h
    have hh' := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom hh)
      (Finsupp.single m0 1 ⊗ₜ[F2] Finsupp.single m1 1)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hh'
    refine hh'.trans ?_
    have hc : (comultiplication b).hom (Finsupp.single m1 1) = comultiplicationMonomial m1 := by
      change (Finsupp.linearCombination F2 comultiplicationMonomial) (Finsupp.single m1 1) = _
      rw [Finsupp.linearCombination_single, one_smul]
    exact congrArg (GradedObject.Monoidal.ιTensorObj dualSteenrodGraded
      (GradedObject.Monoidal.tensorObj dualSteenrodGraded dualSteenrodGraded) a b n h).hom
      ((htensor (𝟙 (dualSteenrodGraded a)) (comultiplication b)
        (Finsupp.single m0 1) (Finsupp.single m1 1)).trans
        (congrArg (fun y : ↑(GradedObject.Monoidal.tensorObj dualSteenrodGraded dualSteenrodGraded b) =>
          (Finsupp.single m0 1 : Carrier a) ⊗ₜ[F2] y) hc))
  have hsideL {n : ℤ} (m : MilnorMonomial n) :
      Q₃ n (splitSlot (s := 2) 1 (splitMonomial m)) =
        ((dualSteenrodGraded ◁ comultiplication) n).hom (comultiplicationMonomial m) := by
    have hs := (Finset.sum_attach (splitMonomial m).support
      (fun d => MvPolynomial.monomial d (MvPolynomial.coeff d (splitMonomial m)))).trans
      (MvPolynomial.support_sum_monomial_coeff (splitMonomial m))
    conv_lhs => rw [← hs]
    simp only [map_sum]
    unfold comultiplicationMonomial
    simp only [map_sum, map_smul, hTL]
    apply Finset.sum_congr rfl
    intro d hd
    rw [show MvPolynomial.monomial d.val (MvPolynomial.coeff d.val (splitMonomial m)) =
        MvPolynomial.coeff d.val (splitMonomial m) • MvPolynomial.monomial d.val 1 from by
      simp only [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]]
    rw [map_smul, map_smul, hfactorL]
    exact congrArg (MvPolynomial.coeff d.val (splitMonomial m) • ·)
      (hblockL (splitMonomial_support_degree m d.val d.property)
        (slotMonomial d.val 0) (slotMonomial d.val 1))
  let g₀₁ : Fin 2 × ℕ → Fin 3 × ℕ := fun a => (a.1.castSucc,a.2)
  let g₂ : ℕ → Fin 3 × ℕ := fun j => (2,j)
  have hg₀₁ : Function.Injective g₀₁ := by
    intro a b h
    exact Prod.ext (Fin.castSucc_injective _ (congrArg Prod.fst h))
      (congrArg (fun x : Fin 3 × ℕ => x.2) h)
  have hg₂ : Function.Injective g₂ := fun _ _ h => congrArg Prod.snd h
  let joinR (e : (Fin 2 × ℕ) →₀ ℕ) (d : ℕ →₀ ℕ) := e.mapDomain g₀₁ + d.mapDomain g₂
  have hjoinR₀₁ (e : (Fin 2 × ℕ) →₀ ℕ) (d : ℕ →₀ ℕ) (i : Fin 2) :
      slotExponentsEquiv 3 (joinR e d) i.castSucc = slotExponentsEquiv 2 e i := by
    ext j
    change (e.mapDomain g₀₁ + d.mapDomain g₂) (i.castSucc,j) = e (i,j)
    rw [Finsupp.add_apply, Finsupp.mapDomain_apply hg₀₁ _ (i,j),
      Finsupp.mapDomain_notin_range _ _ (by
        rintro ⟨k,hk⟩
        have hi := congrArg (fun a : Fin 3 × ℕ => a.1.val) hk
        have := i.isLt
        dsimp [g₂] at hi
        omega), add_zero]
  have hjoinR₂ (e : (Fin 2 × ℕ) →₀ ℕ) (d : ℕ →₀ ℕ) :
      slotExponentsEquiv 3 (joinR e d) 2 = d := by
    ext j
    change (e.mapDomain g₀₁ + d.mapDomain g₂) (2,j) = d j
    rw [Finsupp.add_apply, Finsupp.mapDomain_notin_range _ _ (by
        rintro ⟨⟨i,k⟩,hk⟩
        have hi := congrArg (fun a : Fin 3 × ℕ => a.1.val) hk
        have := i.isLt
        dsimp [g₀₁] at hi
        omega), Finsupp.mapDomain_apply hg₂ _ j, zero_add]
  have hsR₀ : (splitSlot (s := 2) 0).comp (MvPolynomial.rename f₀) =
      (MvPolynomial.rename g₀₁).comp ((splitSlot (s := 1) 0).comp (MvPolynomial.rename u)) := by
    ext j : 1
    simp only [AlgHom.comp_apply, MvPolynomial.rename_X]
    change (splitSlot (s := 2) 0) (MvPolynomial.X (0,j)) =
      MvPolynomial.rename g₀₁ ((splitSlot (s := 1) 0) (MvPolynomial.X (0,j)))
    simp only [splitSlot, MvPolynomial.aeval_X]
    exact (rename_coproductGenerator Fin.castSucc (0 : Fin 1) (0 : Fin 2) rfl rfl j).symm
  have hsR₁ : (splitSlot (s := 2) 0).comp (MvPolynomial.rename f₁) =
      MvPolynomial.rename g₂ := by
    ext j : 1
    simp [AlgHom.comp_apply, splitSlot, f₁, g₂]
  have hfactorR (d : (Fin 2 × ℕ) →₀ ℕ) :
      splitSlot (s := 2) 0 (MvPolynomial.monomial d 1) =
        MvPolynomial.rename g₀₁ (splitMonomial (slotMonomial d 0)) *
          MvPolynomial.rename g₂ (MvPolynomial.monomial (slotExponentsEquiv 2 d 1) 1) := by
    have hm : (MvPolynomial.monomial d (1 : F2)) =
        MvPolynomial.rename f₀ (MvPolynomial.monomial (slotExponentsEquiv 2 d 0) 1) *
          MvPolynomial.rename f₁ (MvPolynomial.monomial (slotExponentsEquiv 2 d 1) 1) := by
      simp only [MvPolynomial.rename_monomial, MvPolynomial.monomial_mul, one_mul]
      rw [← hd₂]
    rw [hm, map_mul]
    have hl := AlgHom.congr_fun hsR₀ (MvPolynomial.monomial (slotExponentsEquiv 2 d 0) 1)
    have hr := AlgHom.congr_fun hsR₁ (MvPolynomial.monomial (slotExponentsEquiv 2 d 1) 1)
    rw [AlgHom.comp_apply] at hl hr
    rw [hl, hr]
    rw [splitMonomial, hmono]
    rfl
  have hAssoc (a0 a1 b a n : ℤ) (h : a0 + a1 + b = n) (he : a0 + a1 = a)
      (x0 : Carrier a0) (x1 : Carrier a1) (y : Carrier b) :
      (GradedObject.Monoidal.ιTensorObj₃ dualSteenrodGraded dualSteenrodGraded dualSteenrodGraded
        a0 a1 b n h).hom (x0 ⊗ₜ[F2] (x1 ⊗ₜ[F2] y)) =
        ((α_ dualSteenrodGraded dualSteenrodGraded dualSteenrodGraded).hom n).hom
          ((GradedObject.Monoidal.ιTensorObj
            (GradedObject.Monoidal.tensorObj dualSteenrodGraded dualSteenrodGraded)
            dualSteenrodGraded a b n (by omega)).hom
            ((GradedObject.Monoidal.ιTensorObj dualSteenrodGraded dualSteenrodGraded
              a0 a1 a he).hom (x0 ⊗ₜ[F2] x1) ⊗ₜ[F2] y)) := by
    have hh := GradedObject.Monoidal.ιTensorObj₃'_associator_hom
      dualSteenrodGraded dualSteenrodGraded dualSteenrodGraded a0 a1 b n h
    rw [GradedObject.Monoidal.ιTensorObj₃'_eq _ _ _ _ _ _ _ _ a he] at hh
    have hh' := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom hh)
      ((x0 ⊗ₜ[F2] x1) ⊗ₜ[F2] y)
    exact hh'.symm
  have hQ₃R {a b n : ℤ} (h : a + b = n) (m1 : MilnorMonomial b)
      (e : (Fin 2 × ℕ) →₀ ℕ)
      (he : (slotWeight (slotExponentsEquiv 2 e 0) : ℤ) +
        (slotWeight (slotExponentsEquiv 2 e 1) : ℤ) = a) :
      Q₃ n (MvPolynomial.monomial (joinR e m1.val) 1) =
        ((α_ dualSteenrodGraded dualSteenrodGraded dualSteenrodGraded).hom n).hom
          ((GradedObject.Monoidal.ιTensorObj
            (GradedObject.Monoidal.tensorObj dualSteenrodGraded dualSteenrodGraded)
            dualSteenrodGraded a b n h).hom
            ((GradedObject.Monoidal.ιTensorObj dualSteenrodGraded dualSteenrodGraded
              (slotWeight (slotExponentsEquiv 2 e 0) : ℤ)
              (slotWeight (slotExponentsEquiv 2 e 1) : ℤ) a he).hom
              (Finsupp.single (slotMonomial e 0) 1 ⊗ₜ[F2]
                Finsupp.single (slotMonomial e 1) 1) ⊗ₜ[F2] Finsupp.single m1 1)) := by
    rcases m1 with ⟨d1,rfl⟩
    have he0 := hjoinR₀₁ e d1 0
    have he1 := hjoinR₀₁ e d1 1
    have he2 := hjoinR₂ e d1
    change slotExponentsEquiv 3 (joinR e d1) 0 = slotExponentsEquiv 2 e 0 at he0
    change slotExponentsEquiv 3 (joinR e d1) 1 = slotExponentsEquiv 2 e 1 at he1
    dsimp only [Q₃]
    rw [hconstr, one_smul]
    generalize hx0 : slotExponentsEquiv 3 (joinR e d1) 0 = a0 at he0 ⊢
    generalize hx1 : slotExponentsEquiv 3 (joinR e d1) 1 = a1 at he1 ⊢
    generalize hx2 : slotExponentsEquiv 3 (joinR e d1) 2 = a2 at he2 ⊢
    clear hx0 hx1 hx2
    subst a0 a1 a2
    rw [dif_pos (by omega)]
    exact hAssoc _ _ _ a n (by omega) he _ _ _
  have hblockR {a b n : ℤ} (h : a + b = n) (m0 : MilnorMonomial a) (m1 : MilnorMonomial b) :
      Q₃ n (MvPolynomial.rename g₀₁ (splitMonomial m0) *
          MvPolynomial.rename g₂ (MvPolynomial.monomial m1.val 1)) =
        ((α_ dualSteenrodGraded dualSteenrodGraded dualSteenrodGraded).hom n).hom
          ((GradedObject.Monoidal.ιTensorObj
            (GradedObject.Monoidal.tensorObj dualSteenrodGraded dualSteenrodGraded)
            dualSteenrodGraded a b n h).hom
            (comultiplicationMonomial m0 ⊗ₜ[F2] Finsupp.single m1 1)) := by
    let L : ↑(GradedObject.Monoidal.tensorObj dualSteenrodGraded dualSteenrodGraded a) →ₗ[F2]
        ↑(GradedObject.Monoidal.tensorObj dualSteenrodGraded
          (GradedObject.Monoidal.tensorObj dualSteenrodGraded dualSteenrodGraded) n) :=
      ((α_ dualSteenrodGraded dualSteenrodGraded dualSteenrodGraded).hom n).hom.comp
        ((GradedObject.Monoidal.ιTensorObj
          (GradedObject.Monoidal.tensorObj dualSteenrodGraded dualSteenrodGraded)
          dualSteenrodGraded a b n h).hom.comp
          ((TensorProduct.mk F2 _ (Carrier b)).flip (Finsupp.single m1 1)))
    change _ = L (comultiplicationMonomial m0)
    have hs := (Finset.sum_attach (splitMonomial m0).support
      (fun d => MvPolynomial.monomial d (MvPolynomial.coeff d (splitMonomial m0)))).trans
      (MvPolynomial.support_sum_monomial_coeff (splitMonomial m0))
    conv_lhs => rw [← hs]
    simp only [map_sum, Finset.sum_mul]
    unfold comultiplicationMonomial
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro e he
    simp only [MvPolynomial.rename_monomial, MvPolynomial.monomial_mul, mul_one]
    have hh : MvPolynomial.monomial (joinR e.val m1.val)
        (MvPolynomial.coeff e.val (splitMonomial m0)) =
        MvPolynomial.coeff e.val (splitMonomial m0) • MvPolynomial.monomial (joinR e.val m1.val) 1 := by
      simp only [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
    change Q₃ n (MvPolynomial.monomial (joinR e.val m1.val) _) = _
    rw [hh, map_smul, hQ₃R h m1 e.val (splitMonomial_support_degree m0 e.val e.property)]
    exact (L.map_smul _ _).symm
  have hTR (a b n : ℤ) (h : a + b = n) (m0 : MilnorMonomial a) (m1 : MilnorMonomial b) :
      ((α_ dualSteenrodGraded dualSteenrodGraded dualSteenrodGraded).hom n).hom
        (((comultiplication ▷ dualSteenrodGraded) n).hom
          ((GradedObject.Monoidal.ιTensorObj dualSteenrodGraded dualSteenrodGraded a b n h).hom
            (Finsupp.single m0 1 ⊗ₜ[F2] Finsupp.single m1 1))) =
        ((α_ dualSteenrodGraded dualSteenrodGraded dualSteenrodGraded).hom n).hom
          ((GradedObject.Monoidal.ιTensorObj
            (GradedObject.Monoidal.tensorObj dualSteenrodGraded dualSteenrodGraded)
            dualSteenrodGraded a b n h).hom
            (comultiplicationMonomial m0 ⊗ₜ[F2] Finsupp.single m1 1)) := by
    apply congrArg ((α_ dualSteenrodGraded dualSteenrodGraded dualSteenrodGraded).hom n).hom
    have hh := GradedObject.Monoidal.ι_tensorHom comultiplication (𝟙 dualSteenrodGraded) a b n h
    have hh' := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom hh)
      (Finsupp.single m0 1 ⊗ₜ[F2] Finsupp.single m1 1)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hh'
    refine hh'.trans ?_
    have hc : (comultiplication a).hom (Finsupp.single m0 1) = comultiplicationMonomial m0 := by
      change (Finsupp.linearCombination F2 comultiplicationMonomial) (Finsupp.single m0 1) = _
      rw [Finsupp.linearCombination_single, one_smul]
    exact congrArg (GradedObject.Monoidal.ιTensorObj
      (GradedObject.Monoidal.tensorObj dualSteenrodGraded dualSteenrodGraded)
      dualSteenrodGraded a b n h).hom
      ((htensor (comultiplication a) (𝟙 (dualSteenrodGraded b))
        (Finsupp.single m0 1) (Finsupp.single m1 1)).trans
        (congrArg (fun x : ↑(GradedObject.Monoidal.tensorObj dualSteenrodGraded dualSteenrodGraded a) =>
          x ⊗ₜ[F2] (Finsupp.single m1 1 : Carrier b)) hc))
  have hsideR {n : ℤ} (m : MilnorMonomial n) :
      Q₃ n (splitSlot (s := 2) 0 (splitMonomial m)) =
        ((α_ dualSteenrodGraded dualSteenrodGraded dualSteenrodGraded).hom n).hom
          (((comultiplication ▷ dualSteenrodGraded) n).hom (comultiplicationMonomial m)) := by
    have hs := (Finset.sum_attach (splitMonomial m).support
      (fun d => MvPolynomial.monomial d (MvPolynomial.coeff d (splitMonomial m)))).trans
      (MvPolynomial.support_sum_monomial_coeff (splitMonomial m))
    conv_lhs => rw [← hs]
    simp only [map_sum]
    unfold comultiplicationMonomial
    simp only [map_sum, map_smul, hTR]
    apply Finset.sum_congr rfl
    intro d hd
    rw [show MvPolynomial.monomial d.val (MvPolynomial.coeff d.val (splitMonomial m)) =
        MvPolynomial.coeff d.val (splitMonomial m) • MvPolynomial.monomial d.val 1 from by
      simp only [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]]
    rw [map_smul, map_smul, hfactorR]
    exact congrArg (MvPolynomial.coeff d.val (splitMonomial m) • ·)
      (hblockR (splitMonomial_support_degree m d.val d.property)
        (slotMonomial d.val 0) (slotMonomial d.val 1))
  have hb {n : ℤ} (m : MilnorMonomial n) :
      ((dualSteenrodGraded ◁ comultiplication) n).hom (comultiplicationMonomial m) =
        ((α_ dualSteenrodGraded dualSteenrodGraded dualSteenrodGraded).hom n).hom
          (((comultiplication ▷ dualSteenrodGraded) n).hom (comultiplicationMonomial m)) :=
    (hsideL m).symm.trans
      ((congrArg (Q₃ n) (milnor_splitSlot_assoc (monomialPolynomial m))).trans (hsideR m))
  funext n
  apply ModuleCat.hom_ext
  apply Finsupp.lhom_ext
  intro m r
  change ((dualSteenrodGraded ◁ comultiplication) n).hom
      ((Finsupp.linearCombination F2 comultiplicationMonomial) (Finsupp.single m r)) =
    ((α_ dualSteenrodGraded dualSteenrodGraded dualSteenrodGraded).hom n).hom
      (((comultiplication ▷ dualSteenrodGraded) n).hom
        ((Finsupp.linearCombination F2 comultiplicationMonomial) (Finsupp.single m r)))
  rw [Finsupp.linearCombination_single, map_smul, map_smul, map_smul, hb]

/-- Extracting the constant coefficient of a constant returns that scalar. -/
theorem coaugmentationMap_counit :
    coaugmentationMap ≫ counit = 𝟙 (𝟙_ (GrVect F2)) := by
  classical
  funext n
  change coaugmentationMap n ≫ counit n = 𝟙 _
  by_cases hn : n = 0
  · subst n
    dsimp [coaugmentationMap, counit]
    have h : ModuleCat.ofHom (Finsupp.lsingle (R := F2) zeroMilnorMonomial) ≫
        ModuleCat.ofHom (Finsupp.lapply zeroMilnorMonomial) =
          𝟙 (ModuleCat.of F2 F2) := by
      ext
      simp
    simp only [Category.assoc]
    rw [← Category.assoc _ _ GradedObject.Monoidal.tensorUnit₀.inv]
    erw [h]
    rfl
  · exact (GradedObject.Monoidal.isInitialTensorUnitApply n hn).hom_ext _ _

/-- The actual constant polynomial is group-like. -/
theorem coaugmentationMap_comultiplication :
    coaugmentationMap ≫ comultiplication =
      (λ_ (𝟙_ (GrVect F2))).inv ≫
        (coaugmentationMap ⊗ₘ coaugmentationMap) := by
  classical
  funext n
  by_cases hn : n = 0
  · subst n
    change coaugmentationMap 0 ≫ comultiplication 0 = _
    apply (cancel_epi (show ModuleCat.of F2 F2 ⟶ (𝟙_ (GrVect F2)) 0 from
      GradedObject.Monoidal.tensorUnit₀.inv)).mp
    change GradedObject.Monoidal.tensorUnit₀.inv ≫ (coaugmentationMap 0 ≫ comultiplication 0) =
      GradedObject.Monoidal.tensorUnit₀.inv ≫
        ((GradedObject.Monoidal.leftUnitor (𝟙_ (GrVect F2))).inv 0 ≫
          GradedObject.Monoidal.tensorHom coaugmentationMap coaugmentationMap 0)
    rw [GradedObject.Monoidal.leftUnitor_inv_apply]
    simp only [Category.assoc, GradedObject.Monoidal.ι_tensorHom]
    ext
    change (Finsupp.linearCombination F2 comultiplicationMonomial)
      (Finsupp.single zeroMilnorMonomial (1 : F2)) = _
    rw [Finsupp.linearCombination_single, one_smul]
    have hz (s : ℕ) : slotExponentsEquiv s 0 = fun _ => 0 := by
      funext i
      ext j
      rfl
    have hzs : (slotExponentsEquiv 1).symm (fun _ => 0) = 0 := by
      apply (slotExponentsEquiv 1).injective
      rw [Equiv.apply_symm_apply, hz]
    have hzero : splitMonomial zeroMilnorMonomial = 1 := by
      simp [splitMonomial, monomialPolynomial, zeroMilnorMonomial, hzs]
    have hmem : (0 : (Fin 2 × ℕ) →₀ ℕ) ∈
        (splitMonomial zeroMilnorMonomial).support := by simp [hzero]
    unfold comultiplicationMonomial
    rw [Finset.sum_eq_single ⟨0, hmem⟩]
    · simp only [hzero, MvPolynomial.coeff_one]
      simp [slotMonomial, hz, slotWeight, coaugmentationMap, ModuleCat.hom_tensorHom,
        ModuleCat.hom_comp, ModuleCat.hom_whiskerRight]
      change (GradedObject.Monoidal.ιTensorObj dualSteenrodGraded dualSteenrodGraded
        0 0 0 (by omega)).hom
        (Finsupp.single zeroMilnorMonomial 1 ⊗ₜ[F2]
          Finsupp.single zeroMilnorMonomial 1) = _
      rfl
    · intro b hb hne
      exfalso
      apply hne
      apply Subtype.ext
      have := b.property
      simpa [hzero] using this
    · intro h
      exact (h (Finset.mem_attach _ _)).elim

  · exact (GradedObject.Monoidal.isInitialTensorUnitApply n hn).hom_ext _ _

end KIP126.Steenrod.Milnor.Coalgebra
