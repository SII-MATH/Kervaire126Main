module

public import KIP126.Def.Comparison.Cobar.Data
public import KIP126.Def.ClassicalAdams.MilnorCohomology.Comparison.Proofs
public import KIP126.Def.ClassicalAdams.MilnorCohomology.Multiplication.Proofs
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import KIP126.Def.Steenrod.MilnorExt.Cofree.Proofs
public import KIP126.Def.Steenrod.MilnorCobar.Polynomial.Monomials.Words.Realization.Proofs
public import KIP126.Def.Steenrod.MilnorCobar.Polynomial.Normalization.Proofs
public import KIP126.Def.ClassicalAdams.MilnorCooperations.Proofs
public import KIP126.Def.Steenrod.MilnorCobar.Polynomial.Multiplication.Proofs
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Algebra.Category.ModuleCat.Injective
public import Mathlib.RingTheory.SimpleModule.InjectiveProjective
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import KIP126.Def.ClassicalAdams.MilnorCohomology.Proofs

@[expose] public section

namespace KIP126.Comparison

open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology KIP126.Classical.Adams

universe u v

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  (H : Mod2EilenbergMacLane (C := C)) (M : MilnorCooperations H)

/-- The cobar comparison preserves the specified cocycle classes. -/
theorem cobarE2Comparison : KIP126.Comparison.CobarE2Comparison H M := by
  intro s t
  exact ⟨MilnorCohomology.comparison H M s t,
    fun x hx => MilnorCohomology.comparison_ofCocycle H M x hx⟩

section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open KIP126.Algebra KIP126.Algebra KIP126.Algebra.GradedVectorSpace
open KIP126.Algebra.GradedComodule KIP126.Steenrod.Milnor MvPolynomial
open CochainComplex.HomComplex
open scoped BigOperators TensorProduct

set_option maxHeartbeats 2000000 in
/-- The prescribed polynomial differential gives an injective cofree resolution;
its exactness is witnessed by deleting the last polynomial slot. -/
private theorem actualCobarResolution_exists {C : Type u} [StableHomotopyCategory.{u,v} C]
    [HasFunctorialCofiber (C := C)] (H : Mod2EilenbergMacLane (C := C))
    (M : MilnorCooperations H) : Nonempty Ext.CobarResolution := by
  classical
  set_option maxHeartbeats 2000000 in
    have partial_normalized_split {s : ℕ} (x : TensorPower (s+1))
        (hx : ∀ i : Fin s, augmentSlot i.castSucc x = 0)
        (j i : Fin (s+1)) :
        augmentSlot j.castSucc (splitSlot i x) =
          (if j.castSucc = i.castSucc then
            rename (fun a : Fin (s+1) × ℕ => (j.castSucc.succAbove a.1,a.2)) x else 0) +
          (if j.castSucc = i.succ then
            rename (fun a : Fin (s+1) × ℕ => (j.castSucc.succAbove a.1,a.2)) x else 0) := by
      by_cases h₁ : j.castSucc = i.castSucc
      · have hji : j = i := Fin.castSucc_injective _ h₁
        subst j
        have hne : i.castSucc ≠ i.succ := by
          intro h; have := congrArg Fin.val h; simp only [Fin.val_castSucc,Fin.val_succ] at this; omega
        simp [hne, augmentSlot_splitSlot_left]
      · by_cases h₂ : j.castSucc = i.succ
        · rw [h₂]
          have hne : i.succ ≠ i.castSucc := h₂ ▸ h₁
          simp [hne, augmentSlot_splitSlot_right]
        · simp only [if_neg h₁, if_neg h₂, zero_add]
          by_cases hlt : j.val < i.val
          · let k : Fin s := ⟨j.val, by have := i.isLt; omega⟩
            have hj : j = k.castSucc := Fin.ext rfl
            rw [hj, augmentSlot_splitSlot_of_lt i k.castSucc hlt, hx, map_zero]
          · have hji : j.val ≠ i.val := fun h => h₁ (Fin.ext h)
            have hji' : j.val ≠ i.val+1 := fun h => h₂ (Fin.ext h)
            let k : Fin s := ⟨j.val-1, by have := j.isLt; omega⟩
            have hj : j.castSucc = k.castSucc.succ := Fin.ext (by dsimp [k]; omega)
            have hk : i < k.castSucc := by change i.val < j.val-1; omega
            rw [hj, augmentSlot_splitSlot_of_gt i k.castSucc hk, hx, map_zero]

    have partial_normalized_insertLeft {s : ℕ} (x : TensorPower (s+1))
        (hx : ∀ i : Fin s, augmentSlot i.castSucc x = 0) (j : Fin (s+1)) :
        augmentSlot j.castSucc (insertLeft (s+1) x) =
          if j.castSucc = 0 then
            rename (fun a : Fin (s+1) × ℕ => (j.castSucc.succAbove a.1,a.2)) x else 0 := by
      refine Fin.cases ?_ (fun i => ?_) j
      · simpa [insertLeft] using
          augmentSlot_rename_disjoint Fin.succ 0 (fun i => Fin.succ_ne_zero i) x
      · have hi : i.succ.castSucc = i.castSucc.succ := rfl
        simp only [hi, insertLeft, augmentSlot_rename Fin.succ (Fin.succ_injective (s+1)),
          hx, map_zero, Fin.succ_ne_zero, if_false]

    have rawD_partial_normalized {s : ℕ} (x : TensorPower (s+1))
        (hx : ∀ i : Fin s, augmentSlot i.castSucc x = 0) (j : Fin (s+1)) :
        augmentSlot j.castSucc (Ext.Cofree.rawDifferential s x) = 0 := by
      classical
      let q := rename (fun a : Fin (s+1) × ℕ => (j.castSucc.succAbove a.1,a.2)) x
      have hleft : (if j.castSucc = 0 then q else 0) +
          ∑ i : Fin (s+1), (if j.castSucc = i.succ then q else 0) = q := by
        rw [← Fin.sum_univ_succ (fun k : Fin (s+2) => if j.castSucc = k then q else 0)]
        simp
      have hright : (∑ i : Fin (s+1), if j.castSucc = i.castSucc then q else 0) = q := by
        simp
      simp only [Ext.Cofree.rawDifferential, LinearMap.add_apply, LinearMap.sum_apply,
        AlgHom.toLinearMap_apply, map_add, map_sum,
        partial_normalized_insertLeft x hx, partial_normalized_split x hx, Finset.sum_add_distrib]
      change (if j.castSucc = 0 then q else 0) +
        ((∑ i : Fin (s+1), if j.castSucc = i.castSucc then q else 0) +
          ∑ i : Fin (s+1), if j.castSucc = i.succ then q else 0) = 0
      calc
        _ = (∑ i : Fin (s+1), if j.castSucc = i.castSucc then q else 0) +
          ((if j.castSucc = 0 then q else 0) +
            ∑ i : Fin (s+1), if j.castSucc = i.succ then q else 0) := by abel
        _ = q + q := by rw [hleft,hright]
        _ = 0 := CharTwo.add_self_eq_zero q

    have rawD_homogeneous {s t : ℕ} {x : TensorPower (s+1)} (hx : IsWeightedHomogeneous weight x t) :
        IsWeightedHomogeneous weight (Ext.Cofree.rawDifferential s x) t := by
      simp only [Ext.Cofree.rawDifferential, LinearMap.add_apply, LinearMap.sum_apply,
        AlgHom.toLinearMap_apply]
      exact (homogeneous_rename_slots Fin.succ hx).add
        (IsWeightedHomogeneous.sum Finset.univ (fun slot => splitSlot slot x) t
          (fun slot _ => homogeneous_splitSlot slot hx))

    have monomial_in_range (s : ℕ) (n : ℤ) (d : (Fin (s+1) × ℕ) →₀ ℕ)
        (hd : (Finsupp.weight weight d : ℤ) = n)
        (hu : ∀ i : Fin s, UsesSlot d i.castSucc) :
        MvPolynomial.monomial d (1 : F2) ∈ LinearMap.range (Ext.Cofree.termPolynomial s n) := by
      classical
      let w : MilnorWord s (wordDegree (fun i : Fin s => slotExponentsEquiv (s+1) d i.castSucc)) :=
        ⟨_, rfl, fun i => (usesSlot_iff_exponents_ne_zero d i.castSucc).mp (hu i)⟩
      let m : MilnorMonomial (slotWeight (slotExponentsEquiv (s+1) d (Fin.last s))) := ⟨_, rfl⟩
      have hsum : wordDegree w.val + (slotWeight m.val : ℤ) = n := by
        have hh := (wordDegree_slotExponents d).trans hd
        simpa only [wordDegree, Fin.sum_univ_castSucc] using hh
      let l : Fin s × ℕ → Fin (s+1) × ℕ := fun a => (a.1.castAdd 1,a.2)
      let r : Fin 1 × ℕ → Fin (s+1) × ℕ := fun a => (a.1.natAdd s,a.2)
      have hl : Function.Injective l := by
        rintro ⟨a,b⟩ ⟨c,e⟩ h
        exact Prod.ext (Fin.castAdd_injective s 1 (Prod.mk.inj h).1) (Prod.mk.inj h).2
      have hr : Function.Injective r := by
        rintro ⟨a,b⟩ ⟨c,e⟩ h
        exact Prod.ext (Fin.natAdd_injective 1 s (Prod.mk.inj h).1) (Prod.mk.inj h).2
      have disj (a : Fin s × ℕ) (b : Fin 1 × ℕ) : l a ≠ r b := by
        intro h
        have hh := congrArg (fun p : Fin (s+1) × ℕ => p.1.val) h
        change a.1.val = s + b.1.val at hh
        have := a.1.isLt
        omega
      let e := Finsupp.mapDomain l ((slotExponentsEquiv s).symm w.val) +
        Finsupp.mapDomain r ((slotExponentsEquiv 1).symm (fun _ => m.val))
      have he : e = d := by
        ext a
        rcases a with ⟨a,j⟩
        refine Fin.lastCases ?_ (fun i => ?_) a
        · change e (r (0,j)) = d (Fin.last s,j)
          have hz : Finsupp.mapDomain l ((slotExponentsEquiv s).symm w.val) (r (0,j)) = 0 :=
            Finsupp.mapDomain_notin_range _ _ (by rintro ⟨b,hb⟩; exact disj b (0,j) hb)
          simp only [e,Finsupp.add_apply,hz,Finsupp.mapDomain_apply hr,zero_add]
          change ((slotExponentsEquiv 1) ((slotExponentsEquiv 1).symm (fun _ => m.val))) 0 j = _
          rw [Equiv.apply_symm_apply]
          rfl
        · change e (l (i,j)) = d (i.castSucc,j)
          have hz : Finsupp.mapDomain r ((slotExponentsEquiv 1).symm (fun _ => m.val)) (l (i,j)) = 0 :=
            Finsupp.mapDomain_notin_range _ _ (by rintro ⟨b,hb⟩; exact disj (i,j) b hb.symm)
          simp only [e,Finsupp.add_apply,hz,Finsupp.mapDomain_apply hl,add_zero]
          change ((slotExponentsEquiv s) ((slotExponentsEquiv s).symm w.val)) i j = _
          rw [Equiv.apply_symm_apply]
          rfl
      let z : (Ext.Cofree.term s).A n :=
        (GradedObject.Monoidal.ιTensorObj (Ext.Cofree.wordSpace s) Coalgebra.dualSteenrod.X
          (wordDegree w.val) (slotWeight m.val) n hsum).hom
            (Finsupp.single w (1 : F2) ⊗ₜ[F2] Finsupp.single m (1 : F2))
      refine ⟨z, ?_⟩
      change (GradedObject.Monoidal.ιTensorObj (Ext.Cofree.wordSpace s) Coalgebra.dualSteenrod.X
        (wordDegree w.val) (slotWeight m.val) n hsum ≫
          GradedObject.Monoidal.tensorObjDesc (fun i j _ => Ext.Cofree.summandPolynomial s i j)).hom _ = _
      rw [GradedObject.Monoidal.ι_tensorObjDesc]
      dsimp only [Ext.Cofree.summandPolynomial, ModuleCat.hom_ofHom]
      erw [TensorProduct.lift.tmul]
      change MvPolynomial.rename l (milnorWordPolynomial s _ (Finsupp.single w 1)) *
        MvPolynomial.rename r (Coalgebra.polynomial _ (Finsupp.single m 1)) = _
      simp only [milnorWordPolynomial, Coalgebra.polynomial]
      erw [Finsupp.linearCombination_single, Finsupp.linearCombination_single]
      simpa [Coalgebra.monomialPolynomial, e, l, r, MvPolynomial.rename_monomial,
        MvPolynomial.monomial_mul] using congrArg (fun q => MvPolynomial.monomial q (1 : F2)) he

    have polynomial_in_range (s : ℕ) (n : ℤ) (p : TensorPower (s+1))
        (hp : ∀ d, MvPolynomial.coeff d p ≠ 0 →
          (Finsupp.weight weight d : ℤ) = n ∧ ∀ i : Fin s, UsesSlot d i.castSucc) :
        p ∈ LinearMap.range (Ext.Cofree.termPolynomial s n) := by
      classical
      have hd (d : (Fin (s+1) × ℕ) →₀ ℕ) (h : d ∈ p.support) :
          MvPolynomial.monomial d (MvPolynomial.coeff d p) ∈
            LinearMap.range (Ext.Cofree.termPolynomial s n) := by
        have hc : MvPolynomial.coeff d p ≠ 0 := Finsupp.mem_support_iff.mp h
        have hm := monomial_in_range s n d (hp d hc).1 (hp d hc).2
        have hh := (LinearMap.range (Ext.Cofree.termPolynomial s n)).smul_mem
          (MvPolynomial.coeff d p) hm
        simpa only [MvPolynomial.smul_monomial, smul_eq_mul, mul_one] using hh
      have h := Submodule.sum_mem (LinearMap.range (Ext.Cofree.termPolynomial s n)) hd
      simpa only [MvPolynomial.support_sum_monomial_coeff] using h

    have termPolynomial_condition (s : ℕ) (n : ℤ) (x : (Ext.Cofree.term s).A n) :
        ∀ d, MvPolynomial.coeff d (Ext.Cofree.termPolynomial s n x) ≠ 0 →
          (Finsupp.weight weight d : ℤ) = n ∧ ∀ i : Fin s, UsesSlot d i.castSucc := by
      classical
      let condition (d : (Fin (s+1) × ℕ) →₀ ℕ) :=
        (Finsupp.weight weight d : ℤ) = n ∧ ∀ i : Fin s, UsesSlot d i.castSucc
      let Q : Submodule F2 (TensorPower (s+1)) :=
        (Finsupp.supported F2 F2 {d | condition d}).comap
          (AddMonoidAlgebra.coeffLinearEquiv F2).toLinearMap
      have mono_mem (d : (Fin (s+1) × ℕ) →₀ ℕ) (hd : condition d) :
          MvPolynomial.monomial d (1 : F2) ∈ Q := by
        change _ ∈ Finsupp.supported F2 F2 {d | condition d}
        exact Finsupp.single_mem_supported F2 1 hd
      have hc : ModuleCat.ofHom (Q.mkQ.comp (Ext.Cofree.termPolynomial s n)) = 0 := by
        apply GradedObject.Monoidal.tensorObj_ext
        intro i j hij
        apply ModuleCat.hom_ext
        apply ((Finsupp.basisSingleOne : Module.Basis (MilnorWord s i) F2 (MilnorWord s i →₀ F2)).tensorProduct
          (Finsupp.basisSingleOne : Module.Basis (MilnorMonomial j) F2 (MilnorMonomial j →₀ F2))).ext
        rintro ⟨w,m⟩
        simp only [Module.Basis.tensorProduct_apply, Finsupp.coe_basisSingleOne]
        change Q.mkQ (Ext.Cofree.termPolynomial s n
          ((GradedObject.Monoidal.ιTensorObj (Ext.Cofree.wordSpace s) Coalgebra.dualSteenrod.X i j n hij).hom
            (Finsupp.single w (1:F2) ⊗ₜ[F2] Finsupp.single m (1:F2)))) = 0
        apply (Submodule.Quotient.mk_eq_zero Q).mpr
        let l : Fin s × ℕ → Fin (s+1) × ℕ := fun a => (a.1.castAdd 1,a.2)
        let r : Fin 1 × ℕ → Fin (s+1) × ℕ := fun a => (a.1.natAdd s,a.2)
        have hl : Function.Injective l := by
          rintro ⟨a,b⟩ ⟨c,e⟩ h
          exact Prod.ext (Fin.castAdd_injective s 1 (Prod.mk.inj h).1) (Prod.mk.inj h).2
        have hr : Function.Injective r := by
          rintro ⟨a,b⟩ ⟨c,e⟩ h
          exact Prod.ext (Fin.natAdd_injective 1 s (Prod.mk.inj h).1) (Prod.mk.inj h).2
        have disj (a : Fin s × ℕ) (b : Fin 1 × ℕ) : l a ≠ r b := by
          intro h
          have hh := congrArg (fun p : Fin (s+1) × ℕ => p.1.val) h
          change a.1.val = s+b.1.val at hh
          have := a.1.isLt
          omega
        let e := Finsupp.mapDomain l ((slotExponentsEquiv s).symm w.val) +
          Finsupp.mapDomain r ((slotExponentsEquiv 1).symm (fun _ => m.val))
        have heL (a : Fin s) : slotExponentsEquiv (s+1) e a.castSucc = w.val a := by
          ext k
          change e (l (a,k)) = w.val a k
          have hz : Finsupp.mapDomain r ((slotExponentsEquiv 1).symm (fun _ => m.val)) (l (a,k)) = 0 :=
            Finsupp.mapDomain_notin_range _ _ (by rintro ⟨b,hb⟩; exact disj (a,k) b hb.symm)
          simp only [e,Finsupp.add_apply,hz,Finsupp.mapDomain_apply hl,add_zero]
          change ((slotExponentsEquiv s) ((slotExponentsEquiv s).symm w.val)) a k = _
          rw [Equiv.apply_symm_apply]
        have heR : slotExponentsEquiv (s+1) e (Fin.last s) = m.val := by
          ext k
          change e (r (0,k)) = m.val k
          have hz : Finsupp.mapDomain l ((slotExponentsEquiv s).symm w.val) (r (0,k)) = 0 :=
            Finsupp.mapDomain_notin_range _ _ (by rintro ⟨b,hb⟩; exact disj b (0,k) hb)
          simp only [e,Finsupp.add_apply,hz,Finsupp.mapDomain_apply hr,zero_add]
          change ((slotExponentsEquiv 1) ((slotExponentsEquiv 1).symm (fun _ => m.val))) 0 k = _
          rw [Equiv.apply_symm_apply]
        have he : condition e := by
          constructor
          · rw [← wordDegree_slotExponents, wordDegree, Fin.sum_univ_castSucc]
            simp only [heL, heR]
            change wordDegree w.val + (slotWeight m.val : ℤ) = n
            rw [w.property.1, m.property, hij]
          · intro a
            rw [usesSlot_iff_exponents_ne_zero, heL]
            exact w.property.2 a
        have hp : Ext.Cofree.termPolynomial s n
            ((GradedObject.Monoidal.ιTensorObj (Ext.Cofree.wordSpace s) Coalgebra.dualSteenrod.X i j n hij).hom
              (Finsupp.single w (1:F2) ⊗ₜ[F2] Finsupp.single m (1:F2))) =
            MvPolynomial.monomial e (1:F2) := by
          change (GradedObject.Monoidal.ιTensorObj (Ext.Cofree.wordSpace s) Coalgebra.dualSteenrod.X i j n hij ≫
            GradedObject.Monoidal.tensorObjDesc (fun i j _ => Ext.Cofree.summandPolynomial s i j)).hom _ = _
          rw [GradedObject.Monoidal.ι_tensorObjDesc]
          dsimp only [Ext.Cofree.summandPolynomial,ModuleCat.hom_ofHom]
          erw [TensorProduct.lift.tmul]
          change MvPolynomial.rename l (milnorWordPolynomial s i (Finsupp.single w 1)) *
            MvPolynomial.rename r (Coalgebra.polynomial j (Finsupp.single m 1)) = _
          simp only [milnorWordPolynomial,Coalgebra.polynomial]
          erw [Finsupp.linearCombination_single,Finsupp.linearCombination_single]
          simp [Coalgebra.monomialPolynomial,e,l,r,MvPolynomial.rename_monomial,MvPolynomial.monomial_mul]
        rw [hp]
        exact mono_mem e he
      have hx : Ext.Cofree.termPolynomial s n x ∈ Q := by
        apply (Submodule.Quotient.mk_eq_zero Q).mp
        exact congrArg (fun f => f.hom x) hc
      intro d hd
      change (AddMonoidAlgebra.coeffLinearEquiv F2) (Ext.Cofree.termPolynomial s n x) ∈
        Finsupp.supported F2 F2 {d | condition d} at hx
      exact (Finsupp.mem_supported _ _).mp hx (Finsupp.mem_support_iff.mpr hd)

    have rawD_in_range (s : ℕ) (n : ℤ) (x : (Ext.Cofree.term s).A n) :
        Ext.Cofree.rawDifferential s (Ext.Cofree.termPolynomial s n x) ∈
          LinearMap.range (Ext.Cofree.termPolynomial (s+1) n) := by
      let p := Ext.Cofree.termPolynomial s n x
      have hc := termPolynomial_condition s n x
      have hn : ∀ i : Fin s, augmentSlot i.castSucc p = 0 := fun i =>
        (augmentSlot_eq_zero_iff _ _).mpr fun d hd => (hc d hd).2 i
      by_cases hnonneg : 0 ≤ n
      · have hdegree : MvPolynomial.IsWeightedHomogeneous weight p n.toNat := by
          intro d hd
          have hh := (hc d hd).1
          omega
        have hd' := rawD_homogeneous hdegree
        have hn' := rawD_partial_normalized p hn
        apply polynomial_in_range
        intro d hd
        constructor
        · have h := hd' hd
          omega
        · intro i
          exact (augmentSlot_eq_zero_iff _ _).mp (hn' i) d hd
      · have hp : p = 0 := by
          ext d
          rw [MvPolynomial.coeff_zero]
          by_contra hd
          have h := (hc d hd).1
          have : (0 : ℤ) ≤ Finsupp.weight weight d := Int.natCast_nonneg _
          omega
        change Ext.Cofree.rawDifferential s p ∈ _
        rw [hp,map_zero]
        exact Submodule.zero_mem _

    let actualD (s : ℕ) (n : ℤ) :
        (Ext.Cofree.term s).A n →ₗ[F2] (Ext.Cofree.term (s+1)).A n :=
      LinearMap.codRestrictOfInjective
        ((Ext.Cofree.rawDifferential s).comp (Ext.Cofree.termPolynomial s n))
        (Ext.Cofree.termPolynomial (s+1) n)
        (Ext.Cofree.termPolynomial_injective (s+1) n) (rawD_in_range s n)
    have actualD_polynomial (s : ℕ) (n : ℤ) (x : (Ext.Cofree.term s).A n) :
        Ext.Cofree.termPolynomial (s+1) n (actualD s n x) =
          Ext.Cofree.rawDifferential s (Ext.Cofree.termPolynomial s n x) :=
      LinearMap.codRestrictOfInjective_comp_apply _ _ _ _ x
    let deleteLast (s : ℕ) : TensorPower (s+1) →ₐ[F2] TensorPower s :=
      MvPolynomial.aeval fun a => Fin.lastCases 0 (fun i : Fin s => X (i,a.2)) a.1
    have deleteLast_castSucc (s : ℕ) (i : Fin s) (j : ℕ) :
        deleteLast s (X (i.castSucc,j)) = X (i,j) := by simp [deleteLast]
    have deleteLast_last (s j : ℕ) :
        deleteLast s (X (Fin.last s,j)) = 0 := by simp [deleteLast]
    have deleteLast_insertLeft (s : ℕ) (p : TensorPower (s+1)) :
        deleteLast (s+1) (insertLeft (s+1) p) = insertLeft s (deleteLast s p) := by
      have h : (deleteLast (s+1)).comp (insertLeft (s+1)) =
          (insertLeft s).comp (deleteLast s) := by
        ext a : 1
        rcases a with ⟨i,j⟩
        refine Fin.lastCases ?_ (fun i => ?_) i
        · simp [deleteLast, insertLeft]
        · simp [deleteLast, insertLeft, ← Fin.castSucc_succ]
      exact DFunLike.congr_fun h p

    have insertRight_deleteLast (s : ℕ) (p : TensorPower (s+1)) :
        insertRight s (deleteLast s p) = augmentSlot (Fin.last s) p := by
      have h : (insertRight s).comp (deleteLast s) = augmentSlot (Fin.last s) := by
        ext a : 1
        rcases a with ⟨i,j⟩
        refine Fin.lastCases ?_ (fun i => ?_) i
        · simp [deleteLast, augmentSlot]
        · simp [deleteLast, insertRight, augmentSlot]
      exact DFunLike.congr_fun h p
    have insertRight_injective (s : ℕ) : Function.Injective (insertRight s) := by
      apply MvPolynomial.rename_injective
      rintro ⟨i,j⟩ ⟨i',j'⟩ h
      exact Prod.ext (Fin.castSucc_injective _ (Prod.mk.inj h).1) (Prod.mk.inj h).2
    have deleteLast_splitLast (s : ℕ) (p : TensorPower (s+1)) :
        deleteLast (s+1) (splitSlot (Fin.last s) p) = p := by
      apply insertRight_injective (s+1)
      rw [insertRight_deleteLast]
      have hlast : Fin.last (s+1) = (Fin.last s).succ := rfl
      rw [hlast, augmentSlot_splitSlot_right]
      congr 2
      funext a
      apply Prod.ext
      · exact congrFun Fin.succAbove_last a.1
      · rfl
    have splitSlot_insertRight (s : ℕ) (i : Fin s) (p : TensorPower s) :
        splitSlot i.castSucc (insertRight s p) = insertRight (s+1) (splitSlot i p) := by
      apply splitSlot_rename Fin.castSucc Fin.castSucc i i.castSucc
      · intro a
        exact Fin.castSucc_inj
      · rfl
      · exact Fin.castSucc_succ i
      · intro a ha
        by_cases h : a < i <;> simp [h, ← Fin.castSucc_succ]
    have deleteLast_splitCastSucc (s : ℕ) (i : Fin s) (p : TensorPower (s+1)) :
        deleteLast (s+1) (splitSlot i.castSucc p) = splitSlot i (deleteLast s p) := by
      apply insertRight_injective (s+1)
      rw [insertRight_deleteLast]
      have hlast : Fin.last (s+1) = (Fin.last s).succ := rfl
      rw [hlast, augmentSlot_splitSlot_of_gt i.castSucc (Fin.last s) i.castSucc_lt_last]
      rw [← insertRight_deleteLast, splitSlot_insertRight]

    have rawDifferential_contract_succ (s : ℕ) (p : TensorPower (s+2)) :
        deleteLast (s+2) (Ext.Cofree.rawDifferential (s+1) p) +
          Ext.Cofree.rawDifferential s (deleteLast (s+1) p) = p := by
      simp only [Ext.Cofree.rawDifferential, LinearMap.add_apply, LinearMap.sum_apply,
        AlgHom.toLinearMap_apply, map_add, map_sum]
      rw [Fin.sum_univ_castSucc]
      simp_rw [deleteLast_insertLeft, deleteLast_splitCastSucc, deleteLast_splitLast]
      have h (a b : TensorPower (s+2)) : a + (b + p) + (a + b) = p := by
        calc
          a + (b+p) + (a+b) = (a+a)+(b+b)+p := by abel
          _ = p := by simp [CharTwo.add_self_eq_zero]
      exact h _ _
    have rawDifferential_contract_zero (p : TensorPower 1) :
        deleteLast 1 (Ext.Cofree.rawDifferential 0 p) + insertLeft 0 (deleteLast 0 p) = p := by
      simp only [Ext.Cofree.rawDifferential, LinearMap.add_apply, LinearMap.sum_apply,
        AlgHom.toLinearMap_apply, map_add, map_sum]
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.sum_univ_zero, zero_add]
      rw [deleteLast_insertLeft]
      change _ + deleteLast 1 (splitSlot (Fin.last 0) p) + _ = _
      rw [deleteLast_splitLast]
      rw [add_right_comm, CharTwo.add_self_eq_zero, zero_add]

    have rawDifferential_insertRight (s : ℕ) (p : TensorPower s) :
        Ext.Cofree.rawDifferential s (insertRight s p) =
          insertRight (s+1) (differentialPolynomial s p) := by
      have hleft : insertLeft (s+1) (insertRight s p) = insertRight (s+1) (insertLeft s p) := by
        simp only [insertLeft, insertRight, MvPolynomial.rename_rename]
        congr 2
      have hlast : splitSlot (Fin.last s) (insertRight s p) = insertRight (s+1) (insertRight s p) := by
        change splitSlot (Fin.last s) (rename (fun a : Fin s × ℕ => (a.1.castSucc,a.2)) p) = _
        rw [splitSlot_rename_disjoint Fin.castSucc (fun a : Fin s => a.castSucc.castSucc)
          (Fin.last s) (fun a => a.castSucc_ne_last)
          (fun a => by simp [a.castSucc_lt_last])]
        simp only [insertRight, rename_rename, Function.comp_def]
      simp only [Ext.Cofree.rawDifferential, differentialPolynomial, LinearMap.add_apply,
        LinearMap.sum_apply, AlgHom.toLinearMap_apply, map_add, map_sum]
      rw [Fin.sum_univ_castSucc]
      simp_rw [splitSlot_insertRight, hleft, hlast]
      abel

    have rawDifferential_eq_full_add_right (s : ℕ) (p : TensorPower (s+1)) :
        Ext.Cofree.rawDifferential s p = differentialPolynomial (s+1) p + insertRight (s+1) p := by
      simp only [Ext.Cofree.rawDifferential, differentialPolynomial, LinearMap.add_apply,
        LinearMap.sum_apply, AlgHom.toLinearMap_apply]
      have h (a b c : TensorPower (s+2)) : a+c = a+b+c+b := by
        calc
          a+c = (a+c)+(b+b) := by rw [CharTwo.add_self_eq_zero, add_zero]
          _ = a+b+c+b := by abel
      exact h _ _ _
    have rawDifferential_squared_eq_full (s : ℕ) (p : TensorPower (s+1)) :
        Ext.Cofree.rawDifferential (s+1) (Ext.Cofree.rawDifferential s p) =
          differentialPolynomial (s+2) (differentialPolynomial (s+1) p) := by
      rw [rawDifferential_eq_full_add_right s, map_add,
        rawDifferential_eq_full_add_right (s+1), rawDifferential_insertRight (s+1)]
      have h (a b : TensorPower (s+3)) : a+b+b=a := by
        rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
      exact h _ _


    have full_squared_monomial (s : ℕ) (d : (Fin s × ℕ) →₀ ℕ)
        (hu : ∀ i, UsesSlot d i) (r : F2) :
        differentialPolynomial (s+1) (differentialPolynomial s (monomial d r)) = 0 := by
      let t := Finsupp.weight weight d
      let x : cochains s t := ⟨monomial d r, monomial_mem_cochains d ⟨rfl,hu⟩ r⟩
      exact congrArg Subtype.val (milnor_differential_squared H M s t x)

    have raw_squared_monomial (s : ℕ) (d : (Fin (s+1) × ℕ) →₀ ℕ)
        (hu : ∀ i : Fin s, UsesSlot d i.castSucc) (r : F2) :
        Ext.Cofree.rawDifferential (s+1) (Ext.Cofree.rawDifferential s (monomial d r)) = 0 := by
      classical
      by_cases hlast : UsesSlot d (Fin.last s)
      · rw [rawDifferential_squared_eq_full]
        apply full_squared_monomial
        intro i
        exact Fin.lastCases hlast (fun j => hu j) i
      · let e : (Fin s × ℕ) →₀ ℕ :=
          (slotExponentsEquiv s).symm (fun i => slotExponentsEquiv (s+1) d i.castSucc)
        let f : Fin s × ℕ → Fin (s+1) × ℕ := fun a => (a.1.castSucc,a.2)
        have hf : Function.Injective f := by
          rintro ⟨a,b⟩ ⟨c,e⟩ h
          exact Prod.ext (Fin.castSucc_injective _ (Prod.mk.inj h).1) (Prod.mk.inj h).2
        have he (i : Fin s) (j : ℕ) : e (i,j) = d (i.castSucc,j) := by
          exact congrArg (fun z : Fin s → ℕ →₀ ℕ => z i j)
            ((slotExponentsEquiv s).apply_symm_apply
              (fun i => slotExponentsEquiv (s+1) d i.castSucc))
        have hmap : Finsupp.mapDomain f e = d := by
          ext a
          rcases a with ⟨i,j⟩
          refine Fin.lastCases ?_ (fun i => ?_) i
          · have hn : (Fin.last s,j) ∉ Set.range f := by
              rintro ⟨⟨i,k⟩,h⟩
              exact i.castSucc_ne_last (Prod.mk.inj h).1
            rw [Finsupp.mapDomain_notin_range _ _ hn]
            exact (not_ne_iff.mp (not_exists.mp hlast j)).symm
          · change Finsupp.mapDomain f e (f (i,j)) = _
            rw [Finsupp.mapDomain_apply hf, he]
        have hp : monomial d r = insertRight s (monomial e r) := by
          simp only [insertRight, rename_monomial]
          change monomial d r = monomial (Finsupp.mapDomain f e) r
          rw [hmap]
        rw [hp, rawDifferential_insertRight, rawDifferential_insertRight]
        rw [full_squared_monomial s e (fun i => ?_) r, map_zero]
        rcases hu i with ⟨j,hj⟩
        exact ⟨j, by simpa only [he] using hj⟩

    have raw_squared (s : ℕ) (p : TensorPower (s+1))
        (hu : ∀ i : Fin s, augmentSlot i.castSucc p = 0) :
        Ext.Cofree.rawDifferential (s+1) (Ext.Cofree.rawDifferential s p) = 0 := by
      classical
      rw [← support_sum_monomial_coeff p, map_sum, map_sum]
      apply Finset.sum_eq_zero
      intro d hd
      apply raw_squared_monomial
      intro i
      exact (augmentSlot_eq_zero_iff i.castSucc p).mp (hu i) d
        (Finsupp.mem_support_iff.mp hd)
    have actualD_squared (s : ℕ) (n : ℤ) :
        (actualD (s+1) n).comp (actualD s n) = 0 := by
      apply LinearMap.ext
      intro x
      apply Ext.Cofree.termPolynomial_injective (s+2) n
      change Ext.Cofree.termPolynomial (s+2) n (actualD (s+1) n (actualD s n x)) =
        Ext.Cofree.termPolynomial (s+2) n 0
      rw [map_zero, actualD_polynomial, actualD_polynomial]
      apply raw_squared
      intro i
      apply (augmentSlot_eq_zero_iff _ _).mpr
      intro d hd
      exact (termPolynomial_condition s n x d hd).2 i
    have deleteLast_augment (s : ℕ) (i : Fin s) (p : TensorPower (s+1)) :
        augmentSlot i (deleteLast s p) = deleteLast s (augmentSlot i.castSucc p) := by
      have h : (augmentSlot i).comp (deleteLast s) = (deleteLast s).comp (augmentSlot i.castSucc) := by
        ext a : 1
        rcases a with ⟨j,n⟩
        refine Fin.lastCases ?_ (fun j => ?_) j
        · simp [deleteLast, augmentSlot, Ne.symm i.castSucc_ne_last]
        · by_cases hji : j=i <;> simp [deleteLast, augmentSlot, hji]
      exact AlgHom.congr_fun h p

    have homogeneous_deleteLast (s t : ℕ) (p : TensorPower (s+1))
        (hp : IsWeightedHomogeneous weight p t) :
        IsWeightedHomogeneous weight (deleteLast s p) t := by
      apply homogeneous_aeval weight weight _ _ hp
      rintro ⟨i,j⟩
      refine Fin.lastCases ?_ (fun i => ?_) i
      · simp only [Fin.lastCases_last]
        exact isWeightedHomogeneous_zero F2 weight _
      · simp only [Fin.lastCases_castSucc]
        exact isWeightedHomogeneous_X (R := F2) weight (i,j)

    have deleteLast_preserves_condition (s : ℕ) (n : ℤ) (p : TensorPower (s+2))
        (hp : ∀ d, coeff d p ≠ 0 →
          (Finsupp.weight weight d : ℤ) = n ∧ ∀ i : Fin (s+1), UsesSlot d i.castSucc) :
        ∀ d, coeff d (deleteLast (s+1) p) ≠ 0 →
          (Finsupp.weight weight d : ℤ) = n ∧ ∀ i : Fin s, UsesSlot d i.castSucc := by
      have hnorm (i : Fin (s+1)) : augmentSlot i.castSucc p = 0 :=
        (augmentSlot_eq_zero_iff _ p).mpr (fun d hd => (hp d hd).2 i)
      have hnorm' (i : Fin s) : augmentSlot i.castSucc (deleteLast (s+1) p) = 0 := by
        rw [deleteLast_augment, hnorm i.castSucc, map_zero]
      by_cases hn : 0 ≤ n
      · have hw : IsWeightedHomogeneous weight p n.toNat := by
          intro d hd
          have he := (hp d hd).1
          omega
        have hw' := homogeneous_deleteLast (s+1) n.toNat p hw
        intro d hd
        refine ⟨?_,fun i => (augmentSlot_eq_zero_iff _ _).mp (hnorm' i) d hd⟩
        have hh := hw' hd
        omega
      · have hz : p=0 := by
          ext d
          by_contra h
          have he := (hp d (by simpa using h)).1
          have hh := Int.natCast_nonneg (Finsupp.weight weight d)
          omega
        intro d hd
        rw [hz, map_zero, coeff_zero] at hd
        exact (hd rfl).elim


    have actualD_exact (s : ℕ) (n : ℤ) (x : (Ext.Cofree.term (s+1)).A n)
        (hx : actualD (s+1) n x = 0) :
        ∃ y : (Ext.Cofree.term s).A n, actualD s n y = x := by
      have hp := deleteLast_preserves_condition s n
        (Ext.Cofree.termPolynomial (s+1) n x) (termPolynomial_condition (s+1) n x)
      obtain ⟨y,hy⟩ := polynomial_in_range s n _ hp
      refine ⟨y, ?_⟩
      apply Ext.Cofree.termPolynomial_injective (s+1) n
      rw [actualD_polynomial, hy]
      have h := rawDifferential_contract_succ s
        (Ext.Cofree.termPolynomial (s+1) n x)
      rw [← actualD_polynomial, hx, map_zero, map_zero, zero_add] at h
      exact h

    have actualD_exact_zero (f : Ext.trivialAt 0 ⟶ Ext.Cofree.term 0)
        (hf : Ext.Cofree.termPolynomial 0 0 ((f.f 0).hom (degreeLineGenerator F2 0)) = 1)
        (n : ℤ) (x : (Ext.Cofree.term 0).A n) (hx : actualD 0 n x = 0) :
        ∃ y : (Ext.trivialAt 0).A n, (f.f n).hom y = x := by
      classical
      let p := Ext.Cofree.termPolynomial 0 n x
      let a := MvPolynomial.coeff 0 (deleteLast 0 p)
      have hp : p = MvPolynomial.C a := by
        have h := rawDifferential_contract_zero p
        have hd : Ext.Cofree.rawDifferential 0 p = 0 := by
          rw [← actualD_polynomial, hx, map_zero]
        rw [hd, map_zero, zero_add, MvPolynomial.eq_C_of_isEmpty (deleteLast 0 p)] at h
        simpa only [insertLeft, MvPolynomial.rename_C] using h.symm
      by_cases hn : n = 0
      · subst n
        refine ⟨a • degreeLineGenerator F2 0, ?_⟩
        apply Ext.Cofree.termPolynomial_injective 0 0
        erw [map_smul, map_smul, hf]
        exact (MvPolynomial.C_eq_smul_one.symm.trans hp.symm)
      · have ha : a = 0 := by
          by_contra ha
          have hc : MvPolynomial.coeff 0 p ≠ 0 := by simpa [hp] using ha
          have hd := (termPolynomial_condition 0 n x 0 hc).1
          have hz : (Finsupp.weight weight (0 : (Fin 1 × ℕ) →₀ ℕ) : ℤ) = 0 := by simp
          rw [hz] at hd
          exact hn hd.symm
        have hpx : Ext.Cofree.termPolynomial 0 n x = 0 := by
          change p = 0
          rw [hp, ha, map_zero]
        have hxzero : x = 0 := Ext.Cofree.termPolynomial_injective 0 n (hpx.trans (map_zero _).symm)
        exact ⟨0, (map_zero _).trans hxzero.symm⟩
    have split_xi (s : ℕ) (slot : Fin s) (n : ℕ) :
        splitSlot slot (xi slot n) = ∑ r ∈ Finset.range (n+1),
          xi slot.castSucc (n-r) ^ (2^r) * xi slot.succ r := by
      cases n with
      | zero => simp [xi]
      | succ n => simp [xi, splitSlot, coproductGenerator]
    have split_xi_other (s : ℕ) (slot other : Fin s) (hne : other ≠ slot) (n : ℕ) :
        splitSlot slot (xi other n) = xi (if other < slot then other.castSucc else other.succ) n := by
      cases n <;> simp [xi, splitSlot, hne]
    have split_last_assoc (s : ℕ) (p : TensorPower (s+1)) :
        splitSlot (Fin.last (s+1)) (splitSlot (Fin.last s) p) =
          splitSlot (Fin.last s).castSucc (splitSlot (Fin.last s) p) := by
      let b : Fin (s+2) := (Fin.last s).castSucc
      let c : Fin (s+2) := Fin.last (s+1)
      have hbc : b < c := (Fin.last s).castSucc_lt_last
      have h10 (n : ℕ) : splitSlot c (xi b n) = xi b.castSucc n := by
        rw [split_xi_other _ c b (ne_of_lt hbc), if_pos hbc]
      have h01 (n : ℕ) : splitSlot b (xi c n) = xi c.succ n := by
        rw [split_xi_other _ b c (ne_of_gt hbc), if_neg (not_lt_of_ge hbc.le)]
      have hmid : b.succ = c.castSucc := Fin.ext rfl
      have h : (splitSlot (Fin.last (s+1))).comp (splitSlot (Fin.last s)) =
          (splitSlot (Fin.last s).castSucc).comp (splitSlot (Fin.last s)) := by
        apply MvPolynomial.algHom_ext
        rintro ⟨a,n⟩
        refine Fin.lastCases ?_ (fun a => ?_) a
        · simp only [AlgHom.comp_apply, splitSlot, MvPolynomial.aeval_X, if_true]
          change splitSlot c (∑ r ∈ Finset.range (n+2), xi b (n+1-r) ^ (2^r) * xi c r) =
            splitSlot b (∑ r ∈ Finset.range (n+2), xi b (n+1-r) ^ (2^r) * xi c r)
          simp only [map_sum, map_mul, map_pow, split_xi, h10, h01, hmid]
          simp only [Finset.mul_sum, sum_pow_char_pow, Finset.sum_mul, mul_pow]
          let f (u v : ℕ) : TensorPower (s+3) :=
            xi b.castSucc (n+1-(u+v)) ^ (2^(u+v)) * xi c.castSucc v ^ (2^u) * xi c.succ u
          calc
            _ = ∑ r ∈ Finset.range (n+2), ∑ q ∈ Finset.range (r+1), f q (r-q) := by
              apply Finset.sum_congr rfl
              intro r hr
              apply Finset.sum_congr rfl
              intro q hq
              have hqr : q ≤ r := by simpa using hq
              simp only [f, Nat.add_sub_of_le hqr]
              exact (mul_assoc _ _ _).symm
            _ = ∑ r ∈ Finset.range (n+2), ∑ q ∈ Finset.range (n+2-r), f r q :=
              Finset.sum_range_diag_flip (n+2) f
            _ = _ := by
              apply Finset.sum_congr rfl
              intro r hr
              have hrn : r ≤ n+1 := by have := Finset.mem_range.mp hr; omega
              have he : n+2-r = n+1-r+1 := by omega
              rw [he]
              apply Finset.sum_congr rfl
              intro q hq
              dsimp [f]
              rw [← pow_mul, ← pow_add]
              simp only [Nat.sub_sub, add_comm r q]
        · simp [splitSlot, a.castSucc_ne_last, a.castSucc_lt_last,
            show a.castSucc.castSucc ≠ (Fin.last s).castSucc by simp,
            show a.castSucc.castSucc < (Fin.last s).castSucc by simp]
      exact AlgHom.congr_fun h p

    have split_coproduct_other {s : ℕ} (i : Fin s) (k j : Fin (s+1))
        (h₁ : i.castSucc ≠ k) (h₂ : i.succ ≠ k)
        (h₃ : (if i.castSucc < k then i.castSucc.castSucc else i.castSucc.succ) = j.castSucc)
        (h₄ : (if i.succ < k then i.succ.castSucc else i.succ.succ) = j.succ) (n : ℕ) :
        splitSlot k (coproductGenerator i n) = coproductGenerator j n := by
      simp only [coproductGenerator, map_sum, map_mul, map_pow,
        split_xi_other _ k i.castSucc h₁, split_xi_other _ k i.succ h₂, h₃, h₄]
    have split_last_far (s : ℕ) (i : Fin s) (p : TensorPower (s+1)) :
        splitSlot (Fin.last (s+1)) (splitSlot i.castSucc p) =
          splitSlot i.castSucc.castSucc (splitSlot (Fin.last s) p) := by
      have h : (splitSlot (Fin.last (s+1))).comp (splitSlot i.castSucc) =
          (splitSlot i.castSucc.castSucc).comp (splitSlot (Fin.last s)) := by
        apply MvPolynomial.algHom_ext
        rintro ⟨a,n⟩
        refine Fin.lastCases ?_ (fun a => ?_) a
        · simp only [AlgHom.comp_apply, splitSlot, MvPolynomial.aeval_X]
          simp only [Ne.symm i.castSucc_ne_last, not_lt_of_ge i.castSucc_lt_last.le, ite_false, ite_true, aeval_X]
          simp only [Fin.succ_last, ite_true]
          change coproductGenerator (Fin.last (s+1)) n =
            splitSlot i.castSucc.castSucc (coproductGenerator (Fin.last s) n)
          symm
          apply split_coproduct_other
          · exact ne_of_gt (by simp)
          · exact ne_of_gt (by change i.val < s+1; omega)
          · rw [if_neg (not_lt_of_ge (by simpa using i.castSucc_lt_last.le))]
            rfl
          · rw [if_neg (not_lt_of_ge (by change i.val ≤ s+1; omega))]
            rfl
        · by_cases hai : a=i
          · subst a
            simp only [AlgHom.comp_apply, splitSlot, MvPolynomial.aeval_X]
            simp only [i.castSucc_ne_last, i.castSucc_lt_last, ite_false, ite_true, aeval_X]
            change splitSlot (Fin.last (s+1)) (coproductGenerator i.castSucc n) =
              coproductGenerator i.castSucc.castSucc n
            apply split_coproduct_other
            · exact i.castSucc.castSucc_ne_last
            · exact ne_of_lt (by change i.val+1 < s+1; omega)
            · rw [if_pos i.castSucc.castSucc_lt_last]
            · rw [if_pos (show i.castSucc.succ < Fin.last (s+1) by change i.val+1 < s+1; omega)]
              exact Fin.castSucc_succ _
          · have ha : a.castSucc ≠ i.castSucc := by simpa using hai
            by_cases hlt : a < i
            · simp [splitSlot, ha, a.castSucc_ne_last, a.castSucc_lt_last, hlt]
            · have hgt : i < a := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hai)
              simp [splitSlot, ha, a.castSucc_ne_last, a.castSucc_lt_last, hlt,
                ← Fin.castSucc_succ]
      exact AlgHom.congr_fun h p

    have split_last_insertLeft (s : ℕ) (p : TensorPower (s+1)) :
        splitSlot (Fin.last (s+1)) (insertLeft (s+1) p) =
          insertLeft (s+2) (splitSlot (Fin.last s) p) := by
      apply splitSlot_rename Fin.succ Fin.succ (Fin.last s) (Fin.last (s+1))
      · intro a
        change a.succ = (Fin.last s).succ ↔ a = Fin.last s
        exact Fin.succ_inj
      · exact (Fin.castSucc_succ _).symm
      · rfl
      · intro a ha
        have h : a < Fin.last s := Fin.lt_last_iff_ne_last.mpr ha
        have h' : a.succ < Fin.last (s+1) := by change a.val+1 < s+1; exact Nat.succ_lt_succ h
        simp [h, h', ← Fin.castSucc_succ]
    have rawDifferential_coaction (s : ℕ) (p : TensorPower (s+1)) :
        splitSlot (Fin.last (s+1)) (Ext.Cofree.rawDifferential s p) =
          insertLeft (s+2) (splitSlot (Fin.last s) p) +
            ∑ i : Fin (s+1), splitSlot i.castSucc (splitSlot (Fin.last s) p) := by
      have h (i : Fin (s+1)) :
          splitSlot (Fin.last (s+1)) (splitSlot i p) =
            splitSlot i.castSucc (splitSlot (Fin.last s) p) := by
        exact Fin.lastCases (split_last_assoc s p) (fun i => split_last_far s i p) i
      simp only [Ext.Cofree.rawDifferential, LinearMap.add_apply, LinearMap.sum_apply,
        AlgHom.toLinearMap_apply, map_add, map_sum, split_last_insertLeft, h]
    have cofree_double_injective :
        let P (s : ℕ) (n : ℤ) :
            ((Ext.Cofree.term s).A ⊗ Coalgebra.dualSteenrod.X) n →ₗ[F2] TensorPower (s+2) :=
          (GradedObject.Monoidal.tensorObjDesc
            (X₁ := (Ext.Cofree.term s).A) (X₂ := Coalgebra.dualSteenrod.X) (k := n)
            (fun i j _ => ModuleCat.ofHom (TensorProduct.lift
              ((Ext.Cofree.cupBilinear (s+1) 1).compl₁₂
                (Ext.Cofree.termPolynomial s i) (Coalgebra.polynomial j))))).hom
        ∀ s n, Function.Injective (P s n) := by
      let doubleTermPolynomial (s : ℕ) (n : ℤ) :
          ((Ext.Cofree.term s).A ⊗ Coalgebra.dualSteenrod.X) n →ₗ[F2] TensorPower (s+2) :=
        (GradedObject.Monoidal.tensorObjDesc
          (X₁ := (Ext.Cofree.term s).A) (X₂ := Coalgebra.dualSteenrod.X) (k := n)
          (fun i j _ => ModuleCat.ofHom (TensorProduct.lift
            ((Ext.Cofree.cupBilinear (s+1) 1).compl₁₂
              (Ext.Cofree.termPolynomial s i) (Coalgebra.polynomial j))))).hom
      change ∀ s n, Function.Injective (doubleTermPolynomial s n)
      let Idx (s : ℕ) (n : ℤ) :=
        Σ q : {p : ℤ × ℤ × ℤ // p.1 + p.2.1 + p.2.2 = n},
          MilnorWord s q.val.1 × MilnorMonomial q.val.2.1 × MilnorMonomial q.val.2.2
      let ex (s : ℕ) {n : ℤ} (d : Idx s n) : (Fin (s+2) × ℕ) →₀ ℕ :=
        Finsupp.mapDomain (fun a : Fin s × ℕ => (a.1.castAdd 2,a.2))
            ((slotExponentsEquiv s).symm d.2.1.val) +
          Finsupp.mapDomain (fun j : ℕ => ((⟨s,by omega⟩ : Fin (s+2)),j)) d.2.2.1.val +
          Finsupp.mapDomain (fun j : ℕ => (Fin.last (s+1),j)) d.2.2.2.val
      have ex_word (s : ℕ) {n : ℤ} (d : Idx s n) (i : Fin s) (j : ℕ) :
          ex s d (i.castAdd 2,j) = d.2.1.val i j := by
        classical
        have h0 : Function.Injective (fun a : Fin s × ℕ => (a.1.castAdd 2,a.2)) := by
          rintro ⟨a,b⟩ ⟨c,e⟩ h
          exact Prod.ext (Fin.castAdd_injective s 2 (Prod.mk.inj h).1) (Prod.mk.inj h).2
        have h1 : (i.castAdd 2,j) ∉ Set.range (fun k : ℕ => ((⟨s,by omega⟩ : Fin (s+2)),k)) := by
          rintro ⟨k,h⟩
          have hh := congrArg (fun a : Fin (s+2) × ℕ => a.1.val) h
          have := i.isLt
          simp only [Fin.val_castAdd] at hh
          omega
        have h2 : (i.castAdd 2,j) ∉ Set.range (fun k : ℕ => (Fin.last (s+1),k)) := by
          rintro ⟨k,h⟩
          have hh := congrArg (fun a : Fin (s+2) × ℕ => a.1.val) h
          have := i.isLt
          simp only [Fin.val_castAdd,Fin.val_last] at hh
          omega
        simp only [ex,Finsupp.add_apply,
          Finsupp.mapDomain_notin_range _ _ h1,Finsupp.mapDomain_notin_range _ _ h2,add_zero]
        rw [show (i.castAdd 2,j) = (fun a : Fin s × ℕ => (a.1.castAdd 2,a.2)) (i,j) from rfl, Finsupp.mapDomain_apply h0]
        have hv := congrArg (fun z : Fin s → ℕ →₀ ℕ => z i j) ((slotExponentsEquiv s).apply_symm_apply d.2.1.val)
        exact hv
      have ex_mid (s : ℕ) {n : ℤ} (d : Idx s n) (j : ℕ) :
          ex s d (⟨s,by omega⟩,j) = d.2.2.1.val j := by
        classical
        have h0 : ((⟨s,by omega⟩ : Fin (s+2)),j) ∉
            Set.range (fun a : Fin s × ℕ => (a.1.castAdd 2,a.2)) := by
          rintro ⟨⟨i,k⟩,h⟩
          have hh := congrArg (fun a : Fin (s+2) × ℕ => a.1.val) h
          have := i.isLt
          simp only [Fin.val_castAdd] at hh
          omega
        have h1 : Function.Injective (fun k : ℕ => ((⟨s,by omega⟩ : Fin (s+2)),k)) :=
          fun _ _ h => (Prod.mk.inj h).2
        have h2 : ((⟨s,by omega⟩ : Fin (s+2)),j) ∉ Set.range (fun k : ℕ => (Fin.last (s+1),k)) := by
          rintro ⟨k,h⟩
          have hh := congrArg (fun a : Fin (s+2) × ℕ => a.1.val) h
          simp only [Fin.val_last] at hh
          omega
        simp only [ex,Finsupp.add_apply,Finsupp.mapDomain_notin_range _ _ h0,
          Finsupp.mapDomain_apply h1,Finsupp.mapDomain_notin_range _ _ h2,zero_add,add_zero]
      have ex_last (s : ℕ) {n : ℤ} (d : Idx s n) (j : ℕ) :
          ex s d (Fin.last (s+1),j) = d.2.2.2.val j := by
        classical
        have h0 : (Fin.last (s+1),j) ∉
            Set.range (fun a : Fin s × ℕ => (a.1.castAdd 2,a.2)) := by
          rintro ⟨⟨i,k⟩,h⟩
          have hh := congrArg (fun a : Fin (s+2) × ℕ => a.1.val) h
          have := i.isLt
          simp only [Fin.val_castAdd,Fin.val_last] at hh
          omega
        have h1 : (Fin.last (s+1),j) ∉ Set.range (fun k : ℕ => ((⟨s,by omega⟩ : Fin (s+2)),k)) := by
          rintro ⟨k,h⟩
          have hh := congrArg (fun a : Fin (s+2) × ℕ => a.1.val) h
          simp only [Fin.val_last] at hh
          omega
        have h2 : Function.Injective (fun k : ℕ => (Fin.last (s+1),k)) := fun _ _ h => (Prod.mk.inj h).2
        simp only [ex,Finsupp.add_apply,Finsupp.mapDomain_notin_range _ _ h0,
          Finsupp.mapDomain_notin_range _ _ h1,Finsupp.mapDomain_apply h2,zero_add]
      have ex_injective (s : ℕ) (n : ℤ) : Function.Injective (ex s (n:=n)) := by
        rintro ⟨⟨⟨i,j,k⟩,hijk⟩,w,m,l⟩ ⟨⟨⟨i',j',k'⟩,hijk'⟩,w',m',l'⟩ h
        have hw : w.val = w'.val := by
          funext a
          ext b
          exact (ex_word s _ a b).symm.trans ((congrArg (fun e => e (a.castAdd 2,b)) h).trans (ex_word s _ a b))
        have hm : m.val = m'.val := by
          ext b
          exact (ex_mid s _ b).symm.trans ((congrArg (fun e => e (⟨s,by omega⟩,b)) h).trans (ex_mid s _ b))
        have hl : l.val = l'.val := by
          ext b
          exact (ex_last s _ b).symm.trans ((congrArg (fun e => e (Fin.last (s+1),b)) h).trans (ex_last s _ b))
        have hi : i=i' := w.property.1.symm.trans ((congrArg wordDegree hw).trans w'.property.1)
        have hj : j=j' := m.property.symm.trans ((congrArg (fun d => (slotWeight d : ℤ)) hm).trans m'.property)
        have hk : k=k' := l.property.symm.trans ((congrArg (fun d => (slotWeight d : ℤ)) hl).trans l'.property)
        subst i'; subst j'; subst k'
        have hw' : w=w' := Subtype.ext hw
        have hm' : m=m' := Subtype.ext hm
        have hl' : l=l' := Subtype.ext hl
        subst w'; subst m'; subst l'
        rfl

      let bas (s : ℕ) {n : ℤ} (d : Idx s n) :
          ((Ext.Cofree.term s).A ⊗ Coalgebra.dualSteenrod.X) n :=
        (GradedObject.Monoidal.ιTensorObj (Ext.Cofree.term s).A Coalgebra.dualSteenrod.X
          (d.1.val.1+d.1.val.2.1) d.1.val.2.2 n d.1.property).hom
            ((GradedObject.Monoidal.ιTensorObj (Ext.Cofree.wordSpace s) Coalgebra.dualSteenrod.X
              d.1.val.1 d.1.val.2.1 (d.1.val.1+d.1.val.2.1) rfl).hom
                (Finsupp.single d.2.1 (1:F2) ⊗ₜ[F2] Finsupp.single d.2.2.1 (1:F2)) ⊗ₜ[F2]
                  Finsupp.single d.2.2.2 (1:F2))

      have one_exp (m : ℕ →₀ ℕ) :
          (slotExponentsEquiv 1).symm (fun _ => m) = Finsupp.mapDomain (fun j : ℕ => ((0 : Fin 1),j)) m := by
        ext a
        rcases a with ⟨i,j⟩
        have hi : i = 0 := Subsingleton.elim _ _
        subst i
        rw [Finsupp.mapDomain_apply (fun _ _ h => (Prod.mk.inj h).2)]
        exact congrArg (fun z : Fin 1 → ℕ →₀ ℕ => z 0 j) ((slotExponentsEquiv 1).apply_symm_apply (fun _ => m))

      have double_bas (s : ℕ) {n : ℤ} (d : Idx s n) :
          doubleTermPolynomial s n (bas s d) = monomial (ex s d) (1:F2) := by
        change (GradedObject.Monoidal.ιTensorObj (Ext.Cofree.term s).A Coalgebra.dualSteenrod.X
          (d.1.val.1+d.1.val.2.1) d.1.val.2.2 n d.1.property ≫
            GradedObject.Monoidal.tensorObjDesc _).hom _ = _
        rw [GradedObject.Monoidal.ι_tensorObjDesc]
        dsimp only [ModuleCat.hom_ofHom]
        erw [TensorProduct.lift.tmul]
        change cupPolynomial (Ext.Cofree.termPolynomial s _ _) (Coalgebra.polynomial _ _) = _
        have ht : Ext.Cofree.termPolynomial s (d.1.val.1+d.1.val.2.1)
            ((GradedObject.Monoidal.ιTensorObj (Ext.Cofree.wordSpace s) Coalgebra.dualSteenrod.X
              d.1.val.1 d.1.val.2.1 (d.1.val.1+d.1.val.2.1) rfl).hom
                (Finsupp.single d.2.1 (1:F2) ⊗ₜ[F2] Finsupp.single d.2.2.1 (1:F2))) =
            cupPolynomial (milnorWordPolynomial s _ (Finsupp.single d.2.1 1))
              (Coalgebra.polynomial _ (Finsupp.single d.2.2.1 1)) := by
          change (GradedObject.Monoidal.ιTensorObj (Ext.Cofree.wordSpace s) Coalgebra.dualSteenrod.X
            d.1.val.1 d.1.val.2.1 (d.1.val.1+d.1.val.2.1) rfl ≫
              GradedObject.Monoidal.tensorObjDesc _).hom _ = _
          rw [GradedObject.Monoidal.ι_tensorObjDesc]
          dsimp only [Ext.Cofree.summandPolynomial,ModuleCat.hom_ofHom]
          erw [TensorProduct.lift.tmul]
          rfl
        rw [ht]
        simp only [milnorWordPolynomial,Coalgebra.polynomial]
        erw [Finsupp.linearCombination_single,Finsupp.linearCombination_single,Finsupp.linearCombination_single]
        simp only [one_smul,Coalgebra.monomialPolynomial,cupPolynomial,
          rename_monomial,monomial_mul,one_mul,one_exp,Finsupp.mapDomain_add,
          ← Finsupp.mapDomain_comp]
        apply congrArg (fun e => monomial e (1:F2))
        rfl

      have doubleTermPolynomial_injective (s : ℕ) (n : ℤ) :
          Function.Injective (doubleTermPolynomial s n) := by
        classical
        let back : TensorPower (s+2) →ₗ[F2] ((Ext.Cofree.term s).A ⊗ Coalgebra.dualSteenrod.X) n :=
          (MvPolynomial.basisMonomials (Fin (s+2) × ℕ) F2).constr F2
            (fun d => if h : ∃ a : Idx s n, ex s a = d then bas s h.choose else 0)
        have hb (a : Idx s n) : back (MvPolynomial.monomial (ex s a) 1) = bas s a := by
          have h : ∃ b : Idx s n, ex s b = ex s a := ⟨a,rfl⟩
          change back ((MvPolynomial.basisMonomials (Fin (s+2) × ℕ) F2) (ex s a)) = _
          simp only [back,Module.Basis.constr_basis,dif_pos h]
          exact congrArg (bas s) (ex_injective s n h.choose_spec)
        have hi : back.comp (doubleTermPolynomial s n) = LinearMap.id := by
          have hh : ModuleCat.ofHom (back.comp (doubleTermPolynomial s n)) =
              𝟙 (((Ext.Cofree.term s).A ⊗ Coalgebra.dualSteenrod.X) n) := by
            apply (cancel_epi ((α_ (Ext.Cofree.wordSpace s) Coalgebra.dualSteenrod.X
              Coalgebra.dualSteenrod.X).inv n)).mp
            apply GradedObject.Monoidal.tensorObj₃_ext
            intro i j k hijk
            change GradedObject.Monoidal.ιTensorObj₃ _ _ _ _ _ _ _ _ ≫
                (GradedObject.Monoidal.associator _ _ _).inv n ≫ _ = _
            rw [GradedObject.Monoidal.ιTensorObj₃_associator_inv_assoc]
            erw [Category.comp_id]
            change _ = GradedObject.Monoidal.ιTensorObj₃ _ _ _ _ _ _ _ _ ≫ (GradedObject.Monoidal.associator _ _ _).inv n
            rw [GradedObject.Monoidal.ιTensorObj₃_associator_inv]
            apply ModuleCat.hom_ext
            let bw : Module.Basis (MilnorWord s i) F2 (MilnorWord s i →₀ F2) := Finsupp.basisSingleOne
            let bm : Module.Basis (MilnorMonomial j) F2 (MilnorMonomial j →₀ F2) := Finsupp.basisSingleOne
            let bl : Module.Basis (MilnorMonomial k) F2 (MilnorMonomial k →₀ F2) := Finsupp.basisSingleOne
            apply (bw.tensorProduct (bm.tensorProduct bl)).ext
            rintro ⟨w,m,l⟩
            simp only [Module.Basis.tensorProduct_apply,Finsupp.coe_basisSingleOne,bw,bm,bl]
            let d : Idx s n := ⟨⟨(i,j,k),hijk⟩,(w,m,l)⟩
            change back (doubleTermPolynomial s n (bas s d)) = bas s d
            rw [double_bas,hb]
          exact congrArg ModuleCat.Hom.hom hh
        intro x y h
        have hh := congrArg back h
        simpa only [← LinearMap.comp_apply,hi,LinearMap.id_apply] using hh
      exact doubleTermPolynomial_injective

    have cofree_double_coaction :
        let P (s : ℕ) (n : ℤ) :
            ((Ext.Cofree.term s).A ⊗ Coalgebra.dualSteenrod.X) n →ₗ[F2] TensorPower (s+2) :=
          (GradedObject.Monoidal.tensorObjDesc
            (X₁ := (Ext.Cofree.term s).A) (X₂ := Coalgebra.dualSteenrod.X) (k := n)
            (fun i j _ => ModuleCat.ofHom (TensorProduct.lift
              ((Ext.Cofree.cupBilinear (s+1) 1).compl₁₂
                (Ext.Cofree.termPolynomial s i) (Coalgebra.polynomial j))))).hom
        ∀ s n (x : (Ext.Cofree.term s).A n),
          P s n (((Ext.Cofree.term s).a n).hom x) =
            splitSlot (Fin.last s) (Ext.Cofree.termPolynomial s n x) := by
      let doubleTermPolynomial (s : ℕ) (n : ℤ) :
          ((Ext.Cofree.term s).A ⊗ Coalgebra.dualSteenrod.X) n →ₗ[F2] TensorPower (s+2) :=
        (GradedObject.Monoidal.tensorObjDesc
          (X₁ := (Ext.Cofree.term s).A) (X₂ := Coalgebra.dualSteenrod.X) (k := n)
          (fun i j _ => ModuleCat.ofHom (TensorProduct.lift
            ((Ext.Cofree.cupBilinear (s+1) 1).compl₁₂
              (Ext.Cofree.termPolynomial s i) (Coalgebra.polynomial j))))).hom
      change ∀ s n (x : (Ext.Cofree.term s).A n),
          doubleTermPolynomial s n (((Ext.Cofree.term s).a n).hom x) =
            splitSlot (Fin.last s) (Ext.Cofree.termPolynomial s n x)
      have one_exp (m : ℕ →₀ ℕ) :
          (slotExponentsEquiv 1).symm (fun _ => m) = Finsupp.mapDomain (fun j : ℕ => ((0 : Fin 1),j)) m := by
        ext a
        rcases a with ⟨i,j⟩
        have hi : i = 0 := Subsingleton.elim _ _
        subst i
        rw [Finsupp.mapDomain_apply (fun _ _ h => (Prod.mk.inj h).2)]
        exact congrArg (fun z : Fin 1 → ℕ →₀ ℕ => z 0 j) ((slotExponentsEquiv 1).apply_symm_apply (fun _ => m))

      have cup_assoc_tail (s : ℕ) (x : TensorPower s) (y z : TensorPower 1) :
          cupPolynomial (cupPolynomial x y) z = cupPolynomial x (cupPolynomial y z) := by
        simp only [cupPolynomial_blocks,map_mul,blockRename_comp]
        simp only [zero_add,add_zero]
        exact mul_assoc _ _ _

      have split_last_cup (s : ℕ) (x : TensorPower s) (y : TensorPower 1) :
          splitSlot (Fin.last s) (cupPolynomial x y) = cupPolynomial x (splitSlot (0 : Fin 1) y) := by
        simp only [cupPolynomial_blocks,map_mul]
        rw [splitSlot_blockRename_after 0 (by omega) (Fin.last s) (by simp)]
        congr 1
        exact splitSlot_blockRename_inside s (by omega) (0 : Fin 1) y

      have term_summand (s : ℕ) {i j n : ℤ} (h : i+j=n)
          (x : Ext.Cofree.wordSpace s i) (y : Coalgebra.dualSteenrod.X j) :
          Ext.Cofree.termPolynomial s n
            ((GradedObject.Monoidal.ιTensorObj (Ext.Cofree.wordSpace s) Coalgebra.dualSteenrod.X i j n h).hom
              (x ⊗ₜ[F2] y)) = cupPolynomial (milnorWordPolynomial s i x) (Coalgebra.polynomial j y) := by
        change (GradedObject.Monoidal.ιTensorObj (Ext.Cofree.wordSpace s) Coalgebra.dualSteenrod.X i j n h ≫
          GradedObject.Monoidal.tensorObjDesc _).hom _ = _
        rw [GradedObject.Monoidal.ι_tensorObjDesc]
        dsimp only [Ext.Cofree.summandPolynomial,ModuleCat.hom_ofHom]
        erw [TensorProduct.lift.tmul]
        rfl

      have double_summand (s : ℕ) {i j n : ℤ} (h : i+j=n)
          (x : (Ext.Cofree.term s).A i) (y : Coalgebra.dualSteenrod.X j) :
          doubleTermPolynomial s n
            ((GradedObject.Monoidal.ιTensorObj (Ext.Cofree.term s).A Coalgebra.dualSteenrod.X i j n h).hom
              (x ⊗ₜ[F2] y)) = cupPolynomial (Ext.Cofree.termPolynomial s i x) (Coalgebra.polynomial j y) := by
        change (GradedObject.Monoidal.ιTensorObj (Ext.Cofree.term s).A Coalgebra.dualSteenrod.X i j n h ≫
          GradedObject.Monoidal.tensorObjDesc _).hom _ = _
        rw [GradedObject.Monoidal.ι_tensorObjDesc]
        dsimp only [ModuleCat.hom_ofHom]
        erw [TensorProduct.lift.tmul]
        rfl

      let twoPolynomial (n : ℤ) :
          (Coalgebra.dualSteenrod.X ⊗ Coalgebra.dualSteenrod.X) n →ₗ[F2] TensorPower 2 :=
        (GradedObject.Monoidal.tensorObjDesc
          (X₁ := Coalgebra.dualSteenrod.X) (X₂ := Coalgebra.dualSteenrod.X) (k := n)
          (fun i j _ => ModuleCat.ofHom (TensorProduct.lift
            ((Ext.Cofree.cupBilinear 1 1).compl₁₂ (Coalgebra.polynomial i) (Coalgebra.polynomial j))))).hom

      have two_summand {i j n : ℤ} (h : i+j=n)
          (x : Coalgebra.dualSteenrod.X i) (y : Coalgebra.dualSteenrod.X j) :
          twoPolynomial n
            ((GradedObject.Monoidal.ιTensorObj Coalgebra.dualSteenrod.X Coalgebra.dualSteenrod.X i j n h).hom
              (x ⊗ₜ[F2] y)) = cupPolynomial (Coalgebra.polynomial i x) (Coalgebra.polynomial j y) := by
        change (GradedObject.Monoidal.ιTensorObj Coalgebra.dualSteenrod.X Coalgebra.dualSteenrod.X i j n h ≫
          GradedObject.Monoidal.tensorObjDesc _).hom _ = _
        rw [GradedObject.Monoidal.ι_tensorObjDesc]
        dsimp only [ModuleCat.hom_ofHom]
        erw [TensorProduct.lift.tmul]
        rfl

      have two_factor (d : (Fin 2 × ℕ) →₀ ℕ) :
          cupPolynomial (Coalgebra.monomialPolynomial (Coalgebra.slotMonomial d 0))
            (Coalgebra.monomialPolynomial (Coalgebra.slotMonomial d 1)) = monomial d (1:F2) := by
        simp only [cupPolynomial,Coalgebra.monomialPolynomial,one_exp,rename_monomial,
          monomial_mul,one_mul, ← Finsupp.mapDomain_comp]
        apply congrArg (fun e => monomial e (1:F2))
        change Finsupp.mapDomain (fun j => ((0:Fin 2),j)) (slotExponentsEquiv 2 d 0) +
          Finsupp.mapDomain (fun j => ((1:Fin 2),j)) (slotExponentsEquiv 2 d 1) = d
        have h0 : Function.Injective (fun j : ℕ => ((0:Fin 2),j)) := fun _ _ h => (Prod.mk.inj h).2
        have h1 : Function.Injective (fun j : ℕ => ((1:Fin 2),j)) := fun _ _ h => (Prod.mk.inj h).2
        ext a
        rcases a with ⟨i,j⟩
        fin_cases i
        · change (Finsupp.mapDomain (fun j : ℕ => ((0:Fin 2),j)) (slotExponentsEquiv 2 d 0) +
            Finsupp.mapDomain (fun j : ℕ => ((1:Fin 2),j)) (slotExponentsEquiv 2 d 1)) (0,j) = d (0,j)
          rw [Finsupp.add_apply,Finsupp.mapDomain_apply h0 _ j,
            Finsupp.mapDomain_notin_range _ _ (by simp),add_zero]
          rfl
        · change (Finsupp.mapDomain (fun j : ℕ => ((0:Fin 2),j)) (slotExponentsEquiv 2 d 0) +
            Finsupp.mapDomain (fun j : ℕ => ((1:Fin 2),j)) (slotExponentsEquiv 2 d 1)) (1,j) = d (1,j)
          rw [Finsupp.add_apply,Finsupp.mapDomain_notin_range _ _ (by simp),
            Finsupp.mapDomain_apply h1 _ j,zero_add]
          rfl

      have two_comultiplication (n : ℤ) (x : Coalgebra.dualSteenrod.X n) :
          twoPolynomial n ((Coalgebra.comultiplication n).hom x) =
            splitSlot (0 : Fin 1) (Coalgebra.polynomial n x) := by
        have h : (twoPolynomial n).comp (Coalgebra.comultiplication n).hom =
            (splitSlot (0 : Fin 1)).toLinearMap.comp (Coalgebra.polynomial n) := by
          apply Finsupp.lhom_ext
          intro m r
          change twoPolynomial n ((Finsupp.linearCombination F2 Coalgebra.comultiplicationMonomial)
            (Finsupp.single m r)) = splitSlot (0:Fin 1)
              ((Finsupp.linearCombination F2 Coalgebra.monomialPolynomial) (Finsupp.single m r))
          rw [Finsupp.linearCombination_single,Finsupp.linearCombination_single]
          erw [map_smul,map_smul]
          congr 1
          have hs := (Finset.sum_attach (Coalgebra.splitMonomial m).support
            (fun d => monomial d (coeff d (Coalgebra.splitMonomial m)))).trans
            (support_sum_monomial_coeff (Coalgebra.splitMonomial m))
          change _ = Coalgebra.splitMonomial m
          rw [← hs]
          unfold Coalgebra.comultiplicationMonomial
          erw [map_sum]
          apply Finset.sum_congr rfl
          intro d hd
          erw [map_smul]
          erw [two_summand]
          simp only [Coalgebra.polynomial,Finsupp.linearCombination_single,one_smul,two_factor,
            MvPolynomial.smul_monomial,smul_eq_mul,mul_one]
        exact LinearMap.congr_fun h x

      have double_triple (s : ℕ) {i j k n : ℤ} (h : i+j+k=n)
          (x : Ext.Cofree.wordSpace s i) (y : Coalgebra.dualSteenrod.X j)
          (z : Coalgebra.dualSteenrod.X k) :
          doubleTermPolynomial s n
            (((α_ (Ext.Cofree.wordSpace s) Coalgebra.dualSteenrod.X Coalgebra.dualSteenrod.X).inv n).hom
              ((GradedObject.Monoidal.ιTensorObj₃ (Ext.Cofree.wordSpace s) Coalgebra.dualSteenrod.X
                Coalgebra.dualSteenrod.X i j k n h).hom (x ⊗ₜ[F2] (y ⊗ₜ[F2] z)))) =
            cupPolynomial (milnorWordPolynomial s i x)
              (cupPolynomial (Coalgebra.polynomial j y) (Coalgebra.polynomial k z)) := by
        change doubleTermPolynomial s n
          ((GradedObject.Monoidal.ιTensorObj₃ (Ext.Cofree.wordSpace s) Coalgebra.dualSteenrod.X
            Coalgebra.dualSteenrod.X i j k n h ≫
            (GradedObject.Monoidal.associator (Ext.Cofree.wordSpace s) Coalgebra.dualSteenrod.X
              Coalgebra.dualSteenrod.X).inv n).hom _) = _
        rw [GradedObject.Monoidal.ιTensorObj₃_associator_inv]
        change doubleTermPolynomial s n
          ((GradedObject.Monoidal.ιTensorObj (Ext.Cofree.term s).A Coalgebra.dualSteenrod.X
            (i+j) k n h).hom
            ((GradedObject.Monoidal.ιTensorObj (Ext.Cofree.wordSpace s) Coalgebra.dualSteenrod.X
              i j (i+j) rfl).hom (x ⊗ₜ[F2] y) ⊗ₜ[F2] z)) = _
        rw [double_summand,term_summand,cup_assoc_tail]

      have double_right_summand (s : ℕ) {i j n : ℤ} (h : i+j=n)
          (x : Ext.Cofree.wordSpace s i) (z : (Coalgebra.dualSteenrod.X ⊗ Coalgebra.dualSteenrod.X) j) :
          doubleTermPolynomial s n
            (((α_ (Ext.Cofree.wordSpace s) Coalgebra.dualSteenrod.X Coalgebra.dualSteenrod.X).inv n).hom
              ((GradedObject.Monoidal.ιTensorObj (Ext.Cofree.wordSpace s)
                (Coalgebra.dualSteenrod.X ⊗ Coalgebra.dualSteenrod.X) i j n h).hom (x ⊗ₜ[F2] z))) =
            cupPolynomial (milnorWordPolynomial s i x) (twoPolynomial j z) := by
        let L : (Coalgebra.dualSteenrod.X ⊗ Coalgebra.dualSteenrod.X) j →ₗ[F2] TensorPower (s+2) :=
          (doubleTermPolynomial s n).comp
            (((α_ (Ext.Cofree.wordSpace s) Coalgebra.dualSteenrod.X Coalgebra.dualSteenrod.X).inv n).hom.comp
              ((GradedObject.Monoidal.ιTensorObj (Ext.Cofree.wordSpace s)
                (Coalgebra.dualSteenrod.X ⊗ Coalgebra.dualSteenrod.X) i j n h).hom.comp
                  (TensorProduct.mk F2 _ _ x)))
        let R := ((Ext.Cofree.cupBilinear s 2) (milnorWordPolynomial s i x)).comp (twoPolynomial j)
        have hh : ModuleCat.ofHom L = ModuleCat.ofHom R := by
          apply GradedObject.Monoidal.tensorObj_ext
          intro a b hab
          apply ModuleCat.hom_ext
          apply TensorProduct.ext'
          intro y z
          change doubleTermPolynomial s n
            (((α_ (Ext.Cofree.wordSpace s) Coalgebra.dualSteenrod.X Coalgebra.dualSteenrod.X).inv n).hom
              ((GradedObject.Monoidal.ιTensorObj (Ext.Cofree.wordSpace s)
                (Coalgebra.dualSteenrod.X ⊗ Coalgebra.dualSteenrod.X) i j n h).hom
                (x ⊗ₜ[F2] ((GradedObject.Monoidal.ιTensorObj Coalgebra.dualSteenrod.X
                  Coalgebra.dualSteenrod.X a b j hab).hom (y ⊗ₜ[F2] z))))) =
            cupPolynomial (milnorWordPolynomial s i x)
              (twoPolynomial j ((GradedObject.Monoidal.ιTensorObj Coalgebra.dualSteenrod.X
                Coalgebra.dualSteenrod.X a b j hab).hom (y ⊗ₜ[F2] z)))
          rw [two_summand]
          have he := GradedObject.Monoidal.ιTensorObj₃_eq (Ext.Cofree.wordSpace s)
            Coalgebra.dualSteenrod.X Coalgebra.dualSteenrod.X i a b n (by omega) j hab
          have hv := congrArg (fun f => f.hom (x ⊗ₜ[F2] (y ⊗ₜ[F2] z))) he
          change (GradedObject.Monoidal.ιTensorObj₃ (Ext.Cofree.wordSpace s)
            Coalgebra.dualSteenrod.X Coalgebra.dualSteenrod.X i a b n _).hom _ =
              (GradedObject.Monoidal.ιTensorObj (Ext.Cofree.wordSpace s)
                (Coalgebra.dualSteenrod.X ⊗ Coalgebra.dualSteenrod.X) i j n h).hom
                (x ⊗ₜ[F2] ((GradedObject.Monoidal.ιTensorObj Coalgebra.dualSteenrod.X
                  Coalgebra.dualSteenrod.X a b j hab).hom (y ⊗ₜ[F2] z))) at hv
          rw [← hv]
          exact double_triple s (by omega) x y z
        exact congrArg (fun f => f.hom z) hh

      have double_coaction (s : ℕ) (n : ℤ) (x : (Ext.Cofree.term s).A n) :
          doubleTermPolynomial s n (((Ext.Cofree.term s).a n).hom x) =
            splitSlot (Fin.last s) (Ext.Cofree.termPolynomial s n x) := by
        have hh : ModuleCat.ofHom ((doubleTermPolynomial s n).comp ((Ext.Cofree.term s).a n).hom) =
            ModuleCat.ofHom ((splitSlot (Fin.last s)).toLinearMap.comp (Ext.Cofree.termPolynomial s n)) := by
          apply GradedObject.Monoidal.tensorObj_ext
          intro i j hij
          apply ModuleCat.hom_ext
          apply TensorProduct.ext'
          intro w m
          change doubleTermPolynomial s n
            (((α_ (Ext.Cofree.wordSpace s) Coalgebra.dualSteenrod.X Coalgebra.dualSteenrod.X).inv n).hom
              ((((Ext.Cofree.wordSpace s) ◁ Coalgebra.comultiplication) n).hom
                ((GradedObject.Monoidal.ιTensorObj (Ext.Cofree.wordSpace s)
                  Coalgebra.dualSteenrod.X i j n hij).hom (w ⊗ₜ[F2] m)))) = _
          have hn := GradedObject.Monoidal.ι_tensorHom (𝟙 (Ext.Cofree.wordSpace s))
            Coalgebra.comultiplication i j n hij
          have hv := congrArg (fun f => f.hom (w ⊗ₜ[F2] m)) hn
          change (((Ext.Cofree.wordSpace s) ◁ Coalgebra.comultiplication) n).hom
            ((GradedObject.Monoidal.ιTensorObj (Ext.Cofree.wordSpace s)
              Coalgebra.dualSteenrod.X i j n hij).hom (w ⊗ₜ[F2] m)) =
            (GradedObject.Monoidal.ιTensorObj (Ext.Cofree.wordSpace s)
              (Coalgebra.dualSteenrod.X ⊗ Coalgebra.dualSteenrod.X) i j n hij).hom
                (w ⊗ₜ[F2] ((Coalgebra.comultiplication j).hom m)) at hv
          rw [hv,double_right_summand,two_comultiplication]
          change _ = splitSlot (Fin.last s) (Ext.Cofree.termPolynomial s n
            ((GradedObject.Monoidal.ιTensorObj (Ext.Cofree.wordSpace s)
              Coalgebra.dualSteenrod.X i j n hij).hom (w ⊗ₜ[F2] m)))
          rw [term_summand,split_last_cup]
        exact congrArg (fun f => f.hom x) hh
      exact double_coaction
    have cofree_differential_comodule_h (s : ℕ)
        (d : (Ext.Cofree.term s).A ⟶ (Ext.Cofree.term (s+1)).A)
        (hD : ∀ n x, Ext.Cofree.termPolynomial (s+1) n ((d n).hom x) =
          Ext.Cofree.rawDifferential s (Ext.Cofree.termPolynomial s n x)) :
        (Ext.Cofree.term s).a ≫ (rightTensorComonad Coalgebra.dualSteenrod).map d =
          d ≫ (Ext.Cofree.term (s+1)).a := by
      let doubleTermPolynomial (s : ℕ) (n : ℤ) :
          ((Ext.Cofree.term s).A ⊗ Coalgebra.dualSteenrod.X) n →ₗ[F2] TensorPower (s+2) :=
        (GradedObject.Monoidal.tensorObjDesc
          (X₁ := (Ext.Cofree.term s).A) (X₂ := Coalgebra.dualSteenrod.X) (k := n)
          (fun i j _ => ModuleCat.ofHom (TensorProduct.lift
            ((Ext.Cofree.cupBilinear (s+1) 1).compl₁₂
              (Ext.Cofree.termPolynomial s i) (Coalgebra.polynomial j))))).hom

      have doubleTermPolynomial_injective (s : ℕ) (n : ℤ) :
          Function.Injective (doubleTermPolynomial s n) := cofree_double_injective s n
      have double_coaction (s : ℕ) (n : ℤ) (x : (Ext.Cofree.term s).A n) :
          doubleTermPolynomial s n (((Ext.Cofree.term s).a n).hom x) =
            splitSlot (Fin.last s) (Ext.Cofree.termPolynomial s n x) := cofree_double_coaction s n x
      have double_summand (s : ℕ) {i j n : ℤ} (h : i+j=n)
          (x : (Ext.Cofree.term s).A i) (y : Coalgebra.dualSteenrod.X j) :
          doubleTermPolynomial s n
            ((GradedObject.Monoidal.ιTensorObj (Ext.Cofree.term s).A Coalgebra.dualSteenrod.X i j n h).hom
              (x ⊗ₜ[F2] y)) = cupPolynomial (Ext.Cofree.termPolynomial s i x) (Coalgebra.polynomial j y) := by
        change (GradedObject.Monoidal.ιTensorObj (Ext.Cofree.term s).A Coalgebra.dualSteenrod.X i j n h ≫
          GradedObject.Monoidal.tensorObjDesc _).hom _ = _
        rw [GradedObject.Monoidal.ι_tensorObjDesc]
        dsimp only [ModuleCat.hom_ofHom]
        erw [TensorProduct.lift.tmul]
        rfl

      let extendedRawDifferential (s : ℕ) : TensorPower (s+2) →ₗ[F2] TensorPower (s+3) :=
        (insertLeft (s+2)).toLinearMap + ∑ i : Fin (s+1), (splitSlot i.castSucc).toLinearMap

      have insertLeft_cup_tail (s : ℕ) (p : TensorPower (s+1)) (q : TensorPower 1) :
          insertLeft (s+2) (cupPolynomial (s := s+1) (s' := 1) p q) = cupPolynomial (s := s+2) (s' := 1) (insertLeft (s+1) p) q := by
        simp only [cupPolynomial_blocks,map_mul,insertLeft_blockRename,blockRename_insertLeft,zero_add]

      have split_cup_tail (s : ℕ) (i : Fin (s+1))
          (p : TensorPower (s+1)) (q : TensorPower 1) :
          splitSlot i.castSucc (cupPolynomial (s := s+1) (s' := 1) p q) = cupPolynomial (s := s+2) (s' := 1) (splitSlot i p) q := by
        simp only [cupPolynomial_blocks,map_mul]
        rw [splitSlot_blockRename_before (s+1) (by omega) i.castSucc (by exact i.isLt)]
        congr 1
        have hh := splitSlot_blockRename_inside (s := s+1) (n := s+1+1) 0 (by omega) i p
        have hi : (⟨0+i.val, by have := i.isLt; omega⟩ : Fin (s+1+1)) = i.castSucc := by
          apply Fin.ext
          simp
        rw [hi] at hh
        exact hh

      have extendedRawDifferential_cup (s : ℕ) (p : TensorPower (s+1)) (q : TensorPower 1) :
          extendedRawDifferential s (cupPolynomial (s := s+1) (s' := 1) p q) =
            cupPolynomial (s := s+2) (s' := 1) (Ext.Cofree.rawDifferential s p) q := by
        simp only [extendedRawDifferential,LinearMap.add_apply,LinearMap.sum_apply,AlgHom.toLinearMap_apply]
        rw [insertLeft_cup_tail]
        simp_rw [split_cup_tail]
        simp only [Ext.Cofree.rawDifferential,LinearMap.add_apply,LinearMap.sum_apply,
          AlgHom.toLinearMap_apply,cupPolynomial,map_add,map_sum,add_mul,Finset.sum_mul]

      have double_tensor_d (s : ℕ)
          (d : (Ext.Cofree.term s).A ⟶ (Ext.Cofree.term (s+1)).A)
          (hD : ∀ n x, Ext.Cofree.termPolynomial (s+1) n ((d n).hom x) =
            Ext.Cofree.rawDifferential s (Ext.Cofree.termPolynomial s n x))
          (n : ℤ) (x : ((Ext.Cofree.term s).A ⊗ Coalgebra.dualSteenrod.X) n) :
          doubleTermPolynomial (s+1) n (((d ▷ Coalgebra.dualSteenrod.X) n).hom x) =
            extendedRawDifferential s (doubleTermPolynomial s n x) := by
        have hh : ModuleCat.ofHom ((doubleTermPolynomial (s+1) n).comp
            ((d ▷ Coalgebra.dualSteenrod.X) n).hom) =
            ModuleCat.ofHom ((extendedRawDifferential s).comp (doubleTermPolynomial s n)) := by
          apply GradedObject.Monoidal.tensorObj_ext
          intro i j hij
          apply ModuleCat.hom_ext
          apply TensorProduct.ext'
          intro w m
          have hn := GradedObject.Monoidal.ι_tensorHom d (𝟙 Coalgebra.dualSteenrod.X) i j n hij
          have hv := congrArg (fun f => f.hom (w ⊗ₜ[F2] m)) hn
          change ((d ▷ Coalgebra.dualSteenrod.X) n).hom
            ((GradedObject.Monoidal.ιTensorObj (Ext.Cofree.term s).A
              Coalgebra.dualSteenrod.X i j n hij).hom (w ⊗ₜ[F2] m)) =
            (GradedObject.Monoidal.ιTensorObj (Ext.Cofree.term (s+1)).A
              Coalgebra.dualSteenrod.X i j n hij).hom
                ((d i).hom w ⊗ₜ[F2] m) at hv
          change doubleTermPolynomial (s+1) n
            (((d ▷ Coalgebra.dualSteenrod.X) n).hom
              ((GradedObject.Monoidal.ιTensorObj (Ext.Cofree.term s).A
                Coalgebra.dualSteenrod.X i j n hij).hom (w ⊗ₜ[F2] m))) =
            extendedRawDifferential s (doubleTermPolynomial s n
              ((GradedObject.Monoidal.ιTensorObj (Ext.Cofree.term s).A
                Coalgebra.dualSteenrod.X i j n hij).hom (w ⊗ₜ[F2] m)))
          rw [hv,double_summand,hD,double_summand,extendedRawDifferential_cup]
        exact congrArg (fun f => f.hom x) hh

      funext n
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      apply doubleTermPolynomial_injective (s+1) n
      change doubleTermPolynomial (s+1) n
        (((d ▷ Coalgebra.dualSteenrod.X) n).hom (((Ext.Cofree.term s).a n).hom x)) =
        doubleTermPolynomial (s+1) n (((Ext.Cofree.term (s+1)).a n).hom ((d n).hom x))
      rw [double_tensor_d s d hD,double_coaction,double_coaction,hD]
      simpa only [extendedRawDifferential,LinearMap.add_apply,LinearMap.sum_apply,AlgHom.toLinearMap_apply]
        using (rawDifferential_coaction s (Ext.Cofree.termPolynomial s n x)).symm
    have degreeLine_hom_bijective (W : GrVect F2) (t : ℤ) :
        Function.Bijective (fun f : degreeLine F2 t ⟶ W =>
          (f t).hom (degreeLineGenerator F2 t)) := by
      classical
      let E : degreeLine F2 t t ≅ ModuleCat.of F2 F2 := GradedObject.singleObjApplyIso t (ModuleCat.of F2 F2)
      constructor
      · intro f g h
        funext n
        by_cases hn : n=t
        · subst n
          apply (cancel_epi E.inv).mp
          apply ModuleCat.hom_ext
          apply LinearMap.ext_ring
          exact h
        · exact (GradedObject.isInitialSingleObjApply t (ModuleCat.of F2 F2) n hn).isZero.eq_of_src _ _
      · intro x
        let f : degreeLine F2 t ⟶ W := fun n => if hn : n=t then by
          subst n
          exact E.hom ≫ ModuleCat.ofHom (LinearMap.toSpanSingleton F2 (W t) x)
          else 0
        refine ⟨f, ?_⟩
        simp only [f,dif_pos rfl, ModuleCat.hom_comp,LinearMap.comp_apply]
        change ((LinearMap.toSpanSingleton F2 (W t) x) ((E.inv ≫ E.hom).hom 1)) = x
        simp

    have cofree_hom_bijective (s : ℕ) (t : ℤ) :
        Function.Bijective (fun f : Ext.trivialAt t ⟶ Ext.Cofree.term s =>
          ((((rightTensorComonad Coalgebra.dualSteenrod).adj.homEquiv
            (Ext.trivialAt t) (Ext.Cofree.wordSpace s)).symm f) t).hom
              (degreeLineGenerator F2 t)) :=
      (degreeLine_hom_bijective (Ext.Cofree.wordSpace s) t).comp
        ((rightTensorComonad Coalgebra.dualSteenrod).adj.homEquiv
          (Ext.trivialAt t) (Ext.Cofree.wordSpace s)).symm.bijective
    have trivialCoaction_apply (W : GrVect F2) (n : ℤ) (x : W n) :
        (RightTensor.trivialCoaction Coalgebra.coaugmentation W n).hom x =
          (GradedObject.Monoidal.ιTensorObj W Coalgebra.dualSteenrod.X n 0 n (add_zero n)).hom
            (x ⊗ₜ[F2] Finsupp.single zeroMilnorMonomial (1:F2)) := by
      classical
      change (((GradedObject.Monoidal.rightUnitor W).inv n) ≫
        GradedObject.Monoidal.tensorHom (𝟙 W) Coalgebra.coaugmentationMap n).hom x = _
      rw [GradedObject.Monoidal.rightUnitor_inv_apply]
      rw [Category.assoc,Category.assoc,GradedObject.Monoidal.ι_tensorHom]
      simp only [ModuleCat.hom_comp,LinearMap.comp_apply]
      have hc : (Coalgebra.coaugmentationMap 0).hom
          ((GradedObject.Monoidal.tensorUnit₀.inv : ModuleCat.of F2 F2 ⟶ (𝟙_ (GrVect F2)) 0).hom 1) =
          Finsupp.single zeroMilnorMonomial (1:F2) := by
        change (GradedObject.Monoidal.tensorUnit₀.inv ≫ Coalgebra.coaugmentationMap 0).hom 1 = _
        simp only [Coalgebra.coaugmentationMap]
        rfl
      rw [ModuleCat.MonoidalCategory.rightUnitor_inv_apply]
      change (GradedObject.Monoidal.ιTensorObj W Coalgebra.dualSteenrod.X n 0 n (add_zero n)).hom
        ((𝟙 (W n) ⊗ₘ Coalgebra.coaugmentationMap 0).hom
          ((𝟙 (W n) ⊗ₘ GradedObject.Monoidal.tensorUnit₀.inv).hom (x ⊗ₜ[F2] (1:F2)))) = _
      erw [TensorProduct.map_tmul]
      change (GradedObject.Monoidal.ιTensorObj W Coalgebra.dualSteenrod.X n 0 n (add_zero n)).hom
        (x ⊗ₜ[F2] (Coalgebra.coaugmentationMap 0).hom ((show ModuleCat.of F2 F2 ⟶ (𝟙_ (GrVect F2)) 0 from GradedObject.Monoidal.tensorUnit₀.inv).hom 1)) = _
      rw [hc]
    have cofree_hom_polynomial (s : ℕ) (t : ℤ)
        (φ : degreeLine F2 t ⟶ Ext.Cofree.wordSpace s) :
        Ext.Cofree.termPolynomial s t
          ((((rightTensorComonad Coalgebra.dualSteenrod).adj.homEquiv
            (Ext.trivialAt t) (Ext.Cofree.wordSpace s) φ).f t).hom (degreeLineGenerator F2 t)) =
          insertRight s (milnorWordPolynomial s t ((φ t).hom (degreeLineGenerator F2 t))) := by
      let W := Ext.Cofree.wordSpace s
      have h : ((rightTensorComonad Coalgebra.dualSteenrod).adj.homEquiv
            (Ext.trivialAt t) W φ).f = φ ≫ RightTensor.trivialCoaction Coalgebra.coaugmentation W :=
        by
          rw [Adjunction.homEquiv_apply, Comonad.adj_unit]
          change RightTensor.trivialCoaction Coalgebra.coaugmentation (degreeLine F2 t) ≫
            (tensorRight Coalgebra.dualSteenrod.X).map φ = _
          exact RightTensor.trivial_naturality Coalgebra.coaugmentation φ
      rw [h]
      change Ext.Cofree.termPolynomial s t ((RightTensor.trivialCoaction Coalgebra.coaugmentation W t).hom
        ((φ t).hom (degreeLineGenerator F2 t))) = _
      rw [trivialCoaction_apply]
      change (GradedObject.Monoidal.ιTensorObj W Coalgebra.dualSteenrod.X t 0 t (add_zero t) ≫
        GradedObject.Monoidal.tensorObjDesc (fun i j _ => Ext.Cofree.summandPolynomial s i j)).hom _ = _
      rw [GradedObject.Monoidal.ι_tensorObjDesc]
      dsimp only [Ext.Cofree.summandPolynomial,ModuleCat.hom_ofHom]
      erw [TensorProduct.lift.tmul]
      have hz : (slotExponentsEquiv 1).symm (fun _ => (0 : ℕ →₀ ℕ)) = 0 := by
        apply (slotExponentsEquiv 1).injective
        rw [Equiv.apply_symm_apply]
        funext i
        ext j
        rfl
      have hc : Coalgebra.polynomial 0 (Finsupp.single zeroMilnorMonomial (1:F2)) = 1 := by
        simp only [Coalgebra.polynomial]
        rw [Finsupp.linearCombination_single]
        simp only [one_smul,Coalgebra.monomialPolynomial,zeroMilnorMonomial,hz]
        simp
      change MvPolynomial.rename (fun a : Fin s × ℕ => (a.1.castAdd 1,a.2))
        (milnorWordPolynomial s t ((φ t).hom (degreeLineGenerator F2 t))) *
        MvPolynomial.rename (fun a : Fin 1 × ℕ => (a.1.natAdd s,a.2))
          (Coalgebra.polynomial 0 (Finsupp.single zeroMilnorMonomial 1)) = _
      rw [hc,map_one,mul_one]
      rfl
    have augmentation_exists :
        ∃ f : Ext.trivialAt 0 ⟶ Ext.Cofree.term 0,
          Ext.Cofree.termPolynomial 0 0 ((f.f 0).hom (degreeLineGenerator F2 0)) = 1 := by
      let w : MilnorWord 0 0 := ⟨fun i => Fin.elim0 i, by
        constructor
        · simp [wordDegree]
        · intro i
          exact Fin.elim0 i⟩
      obtain ⟨φ,hφ⟩ := (degreeLine_hom_bijective (Ext.Cofree.wordSpace 0) 0).surjective
        (Finsupp.single w (1:F2))
      let f : Ext.trivialAt 0 ⟶ Ext.Cofree.term 0 :=
        (rightTensorComonad Coalgebra.dualSteenrod).adj.homEquiv _ _ φ
      refine ⟨f, ?_⟩
      apply (cofree_hom_polynomial 0 0 φ).trans
      dsimp only at hφ
      erw [hφ, milnorWordPolynomial_single]
      have hz : (slotExponentsEquiv 0).symm w.val = 0 := Subsingleton.elim _ _
      rw [hz]
      simp

    have augmentation_mono (f : Ext.trivialAt 0 ⟶ Ext.Cofree.term 0)
        (hf : Ext.Cofree.termPolynomial 0 0
          ((f.f 0).hom (degreeLineGenerator F2 0)) = 1) : Mono f := by
      classical
      let E : degreeLine F2 0 0 ≅ ModuleCat.of F2 F2 :=
        GradedObject.singleObjApplyIso 0 (ModuleCat.of F2 F2)
      let r : (Ext.Cofree.term 0).A ⟶ (Ext.trivialAt 0).A := fun n =>
        if hn : n=0 then by
          subst n
          exact ModuleCat.ofHom ((MvPolynomial.lcoeff (R:=F2) 0).comp
            (Ext.Cofree.termPolynomial 0 0)) ≫ E.inv
        else 0
      have hr : f.f ≫ r = 𝟙 (Ext.trivialAt 0).A := by
        funext n
        by_cases hn : n=0
        · subst n
          apply (cancel_epi E.inv).mp
          apply ModuleCat.hom_ext
          apply LinearMap.ext_ring
          change ((r 0).hom ((f.f 0).hom (degreeLineGenerator F2 0))) = E.inv.hom 1
          simp only [r,dif_pos rfl,ModuleCat.hom_comp,LinearMap.comp_apply]
          change E.inv.hom (MvPolynomial.coeff 0
            (Ext.Cofree.termPolynomial 0 0 ((f.f 0).hom (degreeLineGenerator F2 0)))) = _
          rw [hf]
          simp
        · exact (GradedObject.isInitialSingleObjApply 0 (ModuleCat.of F2 F2) n hn).isZero.eq_of_src _ _
      haveI : Mono f.f := (show SplitMono f.f from ⟨r,hr⟩).mono
      exact Comonad.algebra_mono_of_mono (rightTensorComonad Coalgebra.dualSteenrod) f

    have augmentation_comp_d_zero (f : Ext.trivialAt 0 ⟶ Ext.Cofree.term 0)
        (hf : Ext.Cofree.termPolynomial 0 0
          ((f.f 0).hom (degreeLineGenerator F2 0)) = 1)
        (d : Ext.Cofree.term 0 ⟶ Ext.Cofree.term 1)
        (hD : ∀ n x, Ext.Cofree.termPolynomial 1 n ((d.f n).hom x) =
          Ext.Cofree.rawDifferential 0 (Ext.Cofree.termPolynomial 0 n x)) :
        f ≫ d = 0 := by
      let E : degreeLine F2 0 0 ≅ ModuleCat.of F2 F2 :=
        GradedObject.singleObjApplyIso 0 (ModuleCat.of F2 F2)
      apply Comonad.Coalgebra.Hom.ext
      funext n
      by_cases hn : n=0
      · subst n
        apply (cancel_epi E.inv).mp
        apply ModuleCat.hom_ext
        apply LinearMap.ext_ring
        apply Ext.Cofree.termPolynomial_injective 1 0
        change Ext.Cofree.termPolynomial 1 0
          ((d.f 0).hom ((f.f 0).hom (degreeLineGenerator F2 0))) =
            Ext.Cofree.termPolynomial 1 0 0
        rw [hD,hf,map_zero]
        simp [Ext.Cofree.rawDifferential,CharTwo.add_self_eq_zero]
      · exact (GradedObject.isInitialSingleObjApply 0 (ModuleCat.of F2 F2) n hn).isZero.eq_of_src _ _

    have cofreeTerm_injective (s : ℕ) : Injective (KIP126.Steenrod.Milnor.Ext.Cofree.term s) := by
      have hg (X : GrVect F2) : Injective X := by
        constructor
        intro E Y f e he
        letI (n : ℤ) : Mono (e n) := by
          change Mono (((discreteEquivalence F2).functor.map e).app ⟨n⟩)
          infer_instance
        letI (n : ℤ) : Module.Injective F2 (X n) := Module.injective_of_isSemisimpleRing F2 (X n)
        letI (n : ℤ) : Injective (X n) := Module.injective_object_of_injective_module F2 (X n)
        exact ⟨fun n => Injective.factorThru (f n) (e n),
          funext fun n => Injective.comp_factorThru (f n) (e n)⟩
      let G := rightTensorComonad KIP126.Steenrod.Milnor.Coalgebra.dualSteenrod
      letI : PreservesFiniteLimits G.forget := ⟨fun J _ _ => inferInstance⟩
      exact G.adj.map_injective _ (hg _)
    have assembled_resolution : Nonempty Ext.CobarResolution := by
      set_option backward.isDefEq.respectTransparency false in
        classical
        let D (s : ℕ) : Ext.Cofree.term s ⟶ Ext.Cofree.term (s+1) :=
          { f := fun n => ModuleCat.ofHom (actualD s n)
            h := cofree_differential_comodule_h s _ (actualD_polynomial s) }
        have hD (s : ℕ) (n : ℤ) (x : (Ext.Cofree.term s).A n) :
            Ext.Cofree.termPolynomial (s+1) n ((D s).f n |>.hom <| x) =
              Ext.Cofree.rawDifferential s (Ext.Cofree.termPolynomial s n x) :=
          actualD_polynomial s n x
        have hsquare (s : ℕ) : D s ≫ D (s+1) = 0 := by
          apply Comonad.Coalgebra.Hom.ext
          funext n
          apply ModuleCat.hom_ext
          exact actualD_squared s n
        let K : CochainComplex Ext.RightComodule ℕ := CochainComplex.of Ext.Cofree.term D hsquare
        have hKd (s : ℕ) : K.d s (s+1) = D s := CochainComplex.of_d _ _ s
        obtain ⟨a,ha⟩ := augmentation_exists
        have haD : a ≫ K.d 0 1 = 0 := by
          rw [hKd]
          exact augmentation_comp_d_zero a ha (D 0) (hD 0)
        let ι : (CochainComplex.single₀ Ext.RightComodule).obj (Ext.trivialAt 0) ⟶ K :=
          (CochainComplex.fromSingle₀Equiv K (Ext.trivialAt 0)).symm ⟨a,haD⟩
        have hι : ι.f 0 = a := CochainComplex.fromSingle₀Equiv_symm_apply_f_zero _ _
        let E (n : ℤ) : GrVect F2 ⥤ ModuleCat F2 :=
          (GradedVectorSpace.discreteEquivalence F2).functor ⋙
            (evaluation (Discrete ℤ) (ModuleCat F2)).obj ⟨n⟩
        letI (n : ℤ) : (E n).Additive := by constructor; intro X Y f g; rfl
        letI (n : ℤ) : PreservesFiniteLimits (E n) := by dsimp [E]; infer_instance
        letI (n : ℤ) : PreservesFiniteColimits (E n) := by dsimp [E]; infer_instance
        let G := Comonad.forget (GradedComodule.rightTensorComonad Coalgebra.dualSteenrod)
        letI : PreservesFiniteLimits G := ⟨fun _ _ _ => inferInstance⟩
        have graded_exact (S : ShortComplex (GrVect F2))
            (hS : ∀ n : ℤ, (S.map (E n)).Exact) : S.Exact := by
          rw [ShortComplex.exact_iff_isZero_homology, IsZero.iff_id_eq_zero]
          funext n
          have hz := (ShortComplex.exact_iff_isZero_homology _).mp (hS n)
          have hh : IsZero ((E n).obj S.homology) :=
            ((S.mapHomologyIso (E n)).isZero_iff).mp hz
          exact hh.eq_of_src _ _
        have exact_of_pointwise {A B Z : Ext.RightComodule} (f : A ⟶ B) (g : B ⟶ Z)
            (w : f ≫ g = 0)
            (hw : ∀ n (x : B.A n), (g.f n).hom x = 0 → ∃ y, (f.f n).hom y = x) :
            (ShortComplex.mk f g w).Exact := by
          apply (ShortComplex.exact_map_iff_of_faithful _ G).mp
          apply graded_exact
          intro n
          apply (ShortComplex.moduleCat_exact_iff_range_eq_ker _).mpr
          change LinearMap.range (f.f n).hom = LinearMap.ker (g.f n).hom
          ext x
          constructor
          · rintro ⟨y,rfl⟩
            exact congrArg (fun k => (k.f n).hom y) w
          · intro hx
            exact hw n x hx
        have hzero : (ShortComplex.mk a (K.d 0 1) haD).Exact := by
          apply exact_of_pointwise
          intro n x hx
          rw [hKd] at hx
          exact actualD_exact_zero a ha n x hx
        have hpositive (s : ℕ) : (ShortComplex.mk (K.d s (s+1))
            (K.d (s+1) (s+2)) (K.d_comp_d s (s+1) (s+2))).Exact := by
          apply exact_of_pointwise
          intro n x hx
          rw [hKd] at hx ⊢
          exact actualD_exact s n x hx
        haveI : Mono a := augmentation_mono a ha
        haveI : QuasiIso ι := by
          constructor
          intro s
          cases s with
          | zero =>
            rw [CochainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros]
            · constructor
              · change (ShortComplex.mk (ι.f 0) (K.d 0 1) _).Exact
                simpa only [hι] using hzero
              · change Mono (ι.f 0)
                rw [hι]
                infer_instance
            · rfl
            · rfl
            · exact K.shape 0 0 (by simp)
          | succ s =>
            rw [quasiIsoAt_iff_exactAt _ _ (CochainComplex.exactAt_succ_single_obj _ _)]
            rw [HomologicalComplex.exactAt_iff' _ s (s+1) (s+2) (by simp) (by simp)]
            exact hpositive s
        refine ⟨{
          resolution := {
            cocomplex := K
            injective := cofreeTerm_injective
            ι := ι }
          termIso := fun _ => Iso.refl _
          differential := ?_
          augmentation := ?_ }⟩
        · intro s n x
          change Ext.Cofree.termPolynomial (s+1) n (((K.d s (s+1)).f n).hom x) = _
          rw [hKd]
          exact hD s n x
        · change Ext.Cofree.termPolynomial 0 0 (((ι.f 0).f 0).hom (degreeLineGenerator F2 0)) = 1
          rw [hι]
          exact ha
    exact assembled_resolution

set_option maxHeartbeats 1000000 in
/-- The actual cofree coordinates identify cocycles and boundaries with those
used by the injective resolution's `extMk`, including cohomological degree zero. -/
private theorem cobar_comparison_from_resolution
    {C : Type u} [StableHomotopyCategory.{u,v} C] [HasFunctorialCofiber (C := C)]
    (H : Mod2EilenbergMacLane (C := C)) (M : MilnorCooperations H)
    (R : Ext.CobarResolution) :
    ∃ e : ∀ s t : ℕ, MilnorCohomology.Cohomology H M s t ≃ₗ[F2] Ext.SphereExt s (t:ℤ),
      ∀ s t (x : cochains s t) (hx : differential s t x = 0),
        ∃ (f : Ext.trivialAt (t:ℤ) ⟶ R.resolution.cocomplex.X s)
          (hf : f ≫ R.resolution.cocomplex.d s (s+1) = 0),
          R.representativePolynomial f = insertRight s x.val ∧
          e s t (MilnorCohomology.ofCocycle H M x hx) = R.resolution.extMk f (s+1) rfl hf := by
  classical
  set_option maxHeartbeats 1000000 in
    have degreeLine_hom_bijective (W : GrVect F2) (t : ℤ) :
        Function.Bijective (fun f : degreeLine F2 t ⟶ W =>
          (f t).hom (degreeLineGenerator F2 t)) := by
      classical
      let E : degreeLine F2 t t ≅ ModuleCat.of F2 F2 := GradedObject.singleObjApplyIso t (ModuleCat.of F2 F2)
      constructor
      · intro f g h
        funext n
        by_cases hn : n=t
        · subst n
          apply (cancel_epi E.inv).mp
          apply ModuleCat.hom_ext
          apply LinearMap.ext_ring
          exact h
        · exact (GradedObject.isInitialSingleObjApply t (ModuleCat.of F2 F2) n hn).isZero.eq_of_src _ _
      · intro x
        let f : degreeLine F2 t ⟶ W := fun n => if hn : n=t then by
          subst n
          exact E.hom ≫ ModuleCat.ofHom (LinearMap.toSpanSingleton F2 (W t) x)
          else 0
        refine ⟨f, ?_⟩
        simp only [f,dif_pos rfl, ModuleCat.hom_comp,LinearMap.comp_apply]
        change ((LinearMap.toSpanSingleton F2 (W t) x) ((E.inv ≫ E.hom).hom 1)) = x
        simp

    have cofree_hom_bijective (s : ℕ) (t : ℤ) :
        Function.Bijective (fun f : Ext.trivialAt t ⟶ Ext.Cofree.term s =>
          ((((rightTensorComonad Coalgebra.dualSteenrod).adj.homEquiv
            (Ext.trivialAt t) (Ext.Cofree.wordSpace s)).symm f) t).hom
              (degreeLineGenerator F2 t)) :=
      (degreeLine_hom_bijective (Ext.Cofree.wordSpace s) t).comp
        ((rightTensorComonad Coalgebra.dualSteenrod).adj.homEquiv
          (Ext.trivialAt t) (Ext.Cofree.wordSpace s)).symm.bijective
    have trivialCoaction_apply (W : GrVect F2) (n : ℤ) (x : W n) :
        (RightTensor.trivialCoaction Coalgebra.coaugmentation W n).hom x =
          (GradedObject.Monoidal.ιTensorObj W Coalgebra.dualSteenrod.X n 0 n (add_zero n)).hom
            (x ⊗ₜ[F2] Finsupp.single zeroMilnorMonomial (1:F2)) := by
      classical
      change (((GradedObject.Monoidal.rightUnitor W).inv n) ≫
        GradedObject.Monoidal.tensorHom (𝟙 W) Coalgebra.coaugmentationMap n).hom x = _
      rw [GradedObject.Monoidal.rightUnitor_inv_apply]
      rw [Category.assoc,Category.assoc,GradedObject.Monoidal.ι_tensorHom]
      simp only [ModuleCat.hom_comp,LinearMap.comp_apply]
      have hc : (Coalgebra.coaugmentationMap 0).hom
          ((GradedObject.Monoidal.tensorUnit₀.inv : ModuleCat.of F2 F2 ⟶ (𝟙_ (GrVect F2)) 0).hom 1) =
          Finsupp.single zeroMilnorMonomial (1:F2) := by
        change (GradedObject.Monoidal.tensorUnit₀.inv ≫ Coalgebra.coaugmentationMap 0).hom 1 = _
        simp only [Coalgebra.coaugmentationMap]
        rfl
      rw [ModuleCat.MonoidalCategory.rightUnitor_inv_apply]
      change (GradedObject.Monoidal.ιTensorObj W Coalgebra.dualSteenrod.X n 0 n (add_zero n)).hom
        ((𝟙 (W n) ⊗ₘ Coalgebra.coaugmentationMap 0).hom
          ((𝟙 (W n) ⊗ₘ GradedObject.Monoidal.tensorUnit₀.inv).hom (x ⊗ₜ[F2] (1:F2)))) = _
      erw [TensorProduct.map_tmul]
      change (GradedObject.Monoidal.ιTensorObj W Coalgebra.dualSteenrod.X n 0 n (add_zero n)).hom
        (x ⊗ₜ[F2] (Coalgebra.coaugmentationMap 0).hom ((show ModuleCat.of F2 F2 ⟶ (𝟙_ (GrVect F2)) 0 from GradedObject.Monoidal.tensorUnit₀.inv).hom 1)) = _
      rw [hc]
    have cofree_hom_polynomial (s : ℕ) (t : ℤ)
        (φ : degreeLine F2 t ⟶ Ext.Cofree.wordSpace s) :
        Ext.Cofree.termPolynomial s t
          ((((rightTensorComonad Coalgebra.dualSteenrod).adj.homEquiv
            (Ext.trivialAt t) (Ext.Cofree.wordSpace s) φ).f t).hom (degreeLineGenerator F2 t)) =
          insertRight s (milnorWordPolynomial s t ((φ t).hom (degreeLineGenerator F2 t))) := by
      let W := Ext.Cofree.wordSpace s
      have h : ((rightTensorComonad Coalgebra.dualSteenrod).adj.homEquiv
            (Ext.trivialAt t) W φ).f = φ ≫ RightTensor.trivialCoaction Coalgebra.coaugmentation W :=
        by
          rw [Adjunction.homEquiv_apply, Comonad.adj_unit]
          change RightTensor.trivialCoaction Coalgebra.coaugmentation (degreeLine F2 t) ≫
            (tensorRight Coalgebra.dualSteenrod.X).map φ = _
          exact RightTensor.trivial_naturality Coalgebra.coaugmentation φ
      rw [h]
      change Ext.Cofree.termPolynomial s t ((RightTensor.trivialCoaction Coalgebra.coaugmentation W t).hom
        ((φ t).hom (degreeLineGenerator F2 t))) = _
      rw [trivialCoaction_apply]
      change (GradedObject.Monoidal.ιTensorObj W Coalgebra.dualSteenrod.X t 0 t (add_zero t) ≫
        GradedObject.Monoidal.tensorObjDesc (fun i j _ => Ext.Cofree.summandPolynomial s i j)).hom _ = _
      rw [GradedObject.Monoidal.ι_tensorObjDesc]
      dsimp only [Ext.Cofree.summandPolynomial,ModuleCat.hom_ofHom]
      erw [TensorProduct.lift.tmul]
      have hz : (slotExponentsEquiv 1).symm (fun _ => (0 : ℕ →₀ ℕ)) = 0 := by
        apply (slotExponentsEquiv 1).injective
        rw [Equiv.apply_symm_apply]
        funext i
        ext j
        rfl
      have hc : Coalgebra.polynomial 0 (Finsupp.single zeroMilnorMonomial (1:F2)) = 1 := by
        simp only [Coalgebra.polynomial]
        rw [Finsupp.linearCombination_single]
        simp only [one_smul,Coalgebra.monomialPolynomial,zeroMilnorMonomial,hz]
        simp
      change MvPolynomial.rename (fun a : Fin s × ℕ => (a.1.castAdd 1,a.2))
        (milnorWordPolynomial s t ((φ t).hom (degreeLineGenerator F2 t))) *
        MvPolynomial.rename (fun a : Fin 1 × ℕ => (a.1.natAdd s,a.2))
          (Coalgebra.polynomial 0 (Finsupp.single zeroMilnorMonomial 1)) = _
      rw [hc,map_one,mul_one]
      rfl
    have splitSlot_insertRight (s : ℕ) (i : Fin s) (p : TensorPower s) :
        splitSlot i.castSucc (insertRight s p) = insertRight (s+1) (splitSlot i p) := by
      apply splitSlot_rename Fin.castSucc Fin.castSucc i i.castSucc
      · intro a
        exact Fin.castSucc_inj
      · rfl
      · exact Fin.castSucc_succ i
      · intro a ha
        by_cases h : a < i <;> simp [h, ← Fin.castSucc_succ]
    have rawDifferential_insertRight (s : ℕ) (p : TensorPower s) :
        Ext.Cofree.rawDifferential s (insertRight s p) =
          insertRight (s+1) (differentialPolynomial s p) := by
      have hleft : insertLeft (s+1) (insertRight s p) = insertRight (s+1) (insertLeft s p) := by
        simp only [insertLeft, insertRight, MvPolynomial.rename_rename]
        congr 2
      have hlast : splitSlot (Fin.last s) (insertRight s p) = insertRight (s+1) (insertRight s p) := by
        change splitSlot (Fin.last s) (rename (fun a : Fin s × ℕ => (a.1.castSucc,a.2)) p) = _
        rw [splitSlot_rename_disjoint Fin.castSucc (fun a : Fin s => a.castSucc.castSucc)
          (Fin.last s) (fun a => a.castSucc_ne_last)
          (fun a => by simp [a.castSucc_lt_last])]
        simp only [insertRight, rename_rename, Function.comp_def]
      simp only [Ext.Cofree.rawDifferential, differentialPolynomial, LinearMap.add_apply,
        LinearMap.sum_apply, AlgHom.toLinearMap_apply, map_add, map_sum]
      rw [Fin.sum_univ_castSucc]
      simp_rw [splitSlot_insertRight, hleft, hlast]
      abel

    have exists_hom_cochains_equiv (R : Ext.CobarResolution) :
        ∃ E : ∀ s t : ℕ, (Ext.trivialAt (t:ℤ) ⟶ R.resolution.cocomplex.X s) ≃ₗ[F2] cochains s t,
          (∀ s t f, R.representativePolynomial f = insertRight s (E s t f).val) ∧
          (∀ s t f, E (s+1) t (f ≫ R.resolution.cocomplex.d s (s+1)) = differential s t (E s t f)) := by
      classical
      let Q (s t : ℕ) : (Ext.trivialAt (t:ℤ) ⟶ R.resolution.cocomplex.X s) →ₗ[F2]
          (Ext.Cofree.wordSpace s) (t:ℤ) :=
        AddMonoidHom.toZModLinearMap 2 {
          toFun := fun f =>
            ((((rightTensorComonad Coalgebra.dualSteenrod).adj.homEquiv
              (Ext.trivialAt (t:ℤ)) (Ext.Cofree.wordSpace s)).symm (f ≫ (R.termIso s).hom)) t).hom
                (degreeLineGenerator F2 t)
          map_zero' := by
            change (((rightTensorComonad Coalgebra.dualSteenrod).ε.app (Ext.Cofree.wordSpace s) t).hom
              (((R.termIso s).hom.f t).hom 0)) = 0
            erw [map_zero,map_zero]
          map_add' := fun f g => by
            change (((rightTensorComonad Coalgebra.dualSteenrod).ε.app (Ext.Cofree.wordSpace s) t).hom
              (((R.termIso s).hom.f t).hom
                (((f.f t).hom (degreeLineGenerator F2 t)) + ((g.f t).hom (degreeLineGenerator F2 t))))) = _
            erw [map_add,map_add]
            rfl }
      have hQ (s t : ℕ) : Function.Bijective (Q s t) := by
        constructor
        · intro f g h
          apply (cancel_mono (R.termIso s).hom).mp
          apply (cofree_hom_bijective s t).injective
          exact h
        · intro x
          obtain ⟨f,hf⟩ := (cofree_hom_bijective s t).surjective x
          refine ⟨f ≫ (R.termIso s).inv,?_⟩
          change ((((rightTensorComonad Coalgebra.dualSteenrod).adj.homEquiv
            (Ext.trivialAt (t:ℤ)) (Ext.Cofree.wordSpace s)).symm
              ((f ≫ (R.termIso s).inv) ≫ (R.termIso s).hom)) t).hom
                (degreeLineGenerator F2 t) = x
          rw [Category.assoc]
          erw [Iso.inv_hom_id,Category.comp_id]
          exact hf
      let E (s t : ℕ) := (LinearEquiv.ofBijective (Q s t) (hQ s t)).trans
        (cochainsWordEquiv s t).symm
      have rep (s t : ℕ) (f : Ext.trivialAt (t:ℤ) ⟶ R.resolution.cocomplex.X s) :
          R.representativePolynomial f = insertRight s (E s t f).val := by
        change R.representativePolynomial f = insertRight s ((cochainsWordEquiv s t).symm (Q s t f)).val
        rw [← milnorWordPolynomial_eq_cochainsWordEquiv_symm]
        let φ := ((rightTensorComonad Coalgebra.dualSteenrod).adj.homEquiv
          (Ext.trivialAt (t:ℤ)) (Ext.Cofree.wordSpace s)).symm (f ≫ (R.termIso s).hom)
        have hp := cofree_hom_polynomial s t φ
        dsimp only [φ] at hp
        rw [Equiv.apply_symm_apply] at hp
        exact hp
      refine ⟨E,rep,?_⟩
      intro s t f
      apply Subtype.ext
      apply (MvPolynomial.rename_injective (fun a : Fin (s+1) × ℕ => (a.1.castSucc,a.2)) (show Function.Injective
        (fun a : Fin (s+1) × ℕ => (a.1.castSucc,a.2)) from by
          rintro ⟨a,b⟩ ⟨c,e⟩ h
          exact Prod.ext (Fin.castSucc_injective _ (Prod.mk.inj h).1) (Prod.mk.inj h).2))
      change insertRight (s+1) (E (s+1) t (f ≫ R.resolution.cocomplex.d s (s+1))).val =
        insertRight (s+1) (differential s t (E s t f)).val
      rw [← rep]
      change Ext.Cofree.termPolynomial (s+1) t
        (((R.resolution.cocomplex.d s (s+1) ≫ (R.termIso (s+1)).hom).f t).hom
          ((f.f t).hom (degreeLineGenerator F2 t))) = _
      rw [R.differential]
      change Ext.Cofree.rawDifferential s (R.representativePolynomial f) = _
      rw [rep,rawDifferential_insertRight]
      rfl

    have cochains_ext_transfer
        {C : Type u} [StableHomotopyCategory.{u,v} C] [HasFunctorialCofiber (C := C)]
        (H : Mod2EilenbergMacLane (C := C)) (M : MilnorCooperations H)
        (R : Ext.CobarResolution) (t : ℕ)
        (E : ∀ s : ℕ, (Ext.trivialAt (t:ℤ) ⟶ R.resolution.cocomplex.X s) ≃ₗ[F2] cochains s t)
        (hE : ∀ s f, E (s+1) (f ≫ R.resolution.cocomplex.d s (s+1)) = differential s t (E s f)) :
        ∃ e : ∀ s : ℕ, MilnorCohomology.Cohomology H M s t ≃ₗ[F2] Ext.SphereExt s (t:ℤ),
          ∀ s (x : cochains s t) (hx : differential s t x = 0),
            ∃ hf : (E s).symm x ≫ R.resolution.cocomplex.d s (s+1) = 0,
              e s (MilnorCohomology.ofCocycle H M x hx) =
                R.resolution.extMk ((E s).symm x) (s+1) rfl hf := by
      classical
      have source_zero (f : Ext.trivialAt (t:ℤ) ⟶ R.resolution.cocomplex.X 0)
          (hf : f ≫ R.resolution.cocomplex.d 0 1 = 0) :
          R.resolution.extMk f 1 rfl hf = 0 ↔ f = 0 := by
        rw [← R.resolution.extEquivCohomologyClass.apply_eq_iff_eq,
          R.resolution.extEquivCohomologyClass_extMk,
          R.resolution.extEquivCohomologyClass_zero, CohomologyClass.mk_eq_zero_iff]
        rw [Cocycle.fromSingleMk_mem_coboundaries_iff _ _ _ _ _ (-1) (by omega)]
        constructor
        · rintro ⟨g,hg⟩
          have hz := CochainComplex.isZero_of_isStrictlyGE R.resolution.cochainComplex 0 (-1) (by omega)
          have hg0 : g = 0 := hz.eq_of_tgt _ _
          rw [hg0,zero_comp] at hg
          exact (cancel_mono (R.resolution.cochainComplexXIso 0 0 rfl).inv).mp (by simpa using hg.symm)
        · intro h
          subst f
          exact ⟨0,by simp⟩
      have hd (s : ℕ) (x : cochains s t) :
          (E (s+1)).symm (differential s t x) = (E s).symm x ≫ R.resolution.cocomplex.d s (s+1) := by
        apply (E (s+1)).injective
        rw [LinearEquiv.apply_symm_apply,hE,LinearEquiv.apply_symm_apply]
      have cyc (s : ℕ) (x : cochains s t) : differential s t x = 0 ↔
          (E s).symm x ≫ R.resolution.cocomplex.d s (s+1) = 0 := by
        rw [← hd, ← (E (s+1)).symm.map_zero, (E (s+1)).symm.injective.eq_iff]
      let a (s : ℕ) := MilnorCohomology.classOf H M s t
      let b (s : ℕ) : MilnorCohomology.cycles s t →ₗ[F2]
          CategoryTheory.Abelian.Ext (Ext.trivialAt (t:ℤ)) (Ext.trivialAt 0) s :=
        AddMonoidHom.toZModLinearMap 2 {
          toFun := fun x => R.resolution.extMk ((E s).symm x.val) (s+1) rfl ((cyc s x.val).mp x.property)
          map_zero' := by simp
          map_add' := fun x y => by
            simpa using (R.resolution.add_extMk ((E s).symm x.val) ((E s).symm y.val) (s+1) rfl
              ((cyc s x.val).mp x.property) ((cyc s y.val).mp y.property)).symm }
      have ha (s : ℕ) : Function.Surjective (a s) := by
        intro x
        exact Submodule.mkQ_surjective _ x
      have hb (s : ℕ) : Function.Surjective (b s) := by
        intro x
        obtain ⟨f,hf,h⟩ := R.resolution.extMk_surjective x (s+1) rfl
        have hf' : differential s t (E s f) = 0 := by rw [← hE,hf,map_zero]
        refine ⟨⟨E s f,hf'⟩,?_⟩
        change R.resolution.extMk ((E s).symm (E s f)) (s+1) rfl ((cyc s (E s f)).mp hf') = x
        simpa only [LinearEquiv.symm_apply_apply] using h
      have hk (s : ℕ) : LinearMap.ker (a s) = LinearMap.ker (b s) := by
        ext x
        change MilnorCohomology.ofCocycle H M x.val x.property = 0 ↔
          R.resolution.extMk ((E s).symm x.val) (s+1) rfl ((cyc s x.val).mp x.property) = 0
        cases s with
        | zero =>
          rw [MilnorCohomology.ofCocycle_zero_eq_zero_iff,source_zero,
            ← (E 0).symm.map_zero,(E 0).symm.injective.eq_iff]
        | succ s =>
          rw [MilnorCohomology.ofCocycle_succ_eq_zero_iff,
            R.resolution.extMk_eq_zero_iff _ _ _ _ s rfl]
          constructor
          · rintro ⟨y,hy⟩
            exact ⟨(E s).symm y,(hd s y).symm.trans (congrArg (E (s+1)).symm hy)⟩
          · rintro ⟨f,hf⟩
            refine ⟨E s f,?_⟩
            have h := congrArg (E (s+1)) hf
            simpa only [hE,LinearEquiv.apply_symm_apply] using h
      let e (s : ℕ) := ((a s).quotKerEquivOfSurjective (ha s)).symm |>.trans
        ((Submodule.quotEquivOfEq _ _ (hk s)).trans ((b s).quotKerEquivOfSurjective (hb s)))
      refine ⟨e,fun s x hx => ⟨(cyc s x).mp hx,?_⟩⟩
      change e s (a s ⟨x,hx⟩) = b s ⟨x,hx⟩
      simp [e]
    classical
    obtain ⟨E,hrep,hE⟩ := exists_hom_cochains_equiv R
    choose e he using fun t => cochains_ext_transfer H M R t (fun s => E s t) (fun s => hE s t)
    refine ⟨fun s t => e t s,?_⟩
    intro s t x hx
    obtain ⟨hf,hf'⟩ := he t s x hx
    refine ⟨(E s t).symm x,hf,?_,hf'⟩
    rw [hrep,LinearEquiv.apply_symm_apply]

end

/-- The derived-comodule Ext comparison preserves every specified cocycle
through the fixed polynomial cofree resolution and Mathlib's `extMk`. -/
theorem cobarDerivedExtComparison :
    Nonempty (KIP126.Comparison.CobarDerivedExtComparison H M) := by
  obtain ⟨R⟩ := actualCobarResolution_exists H M
  obtain ⟨e, he⟩ := cobar_comparison_from_resolution H M R
  exact ⟨{ cobarResolution := R, comparison := e, representatives := he }⟩

/-- The descended cup product agrees with the standard concatenation squares. -/
theorem cobarCupCalculus : KIP126.Comparison.CobarCupCalculus H M where
  representatives := MilnorCohomology.cup_ofCocycle H M
  standard_squares := MilnorCohomology.hiSquare_eq_cup H M

end KIP126.Comparison
