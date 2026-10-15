module

public import KIP126.Def.Steenrod.MilnorExt.Cofree.Data
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basis

@[expose] public section

/-! The prescribed polynomial coordinates do not forget comodule elements. -/

namespace KIP126.Steenrod.Milnor.Ext.Cofree

/-- Disjoint slot monomials and the Cauchy degree decomposition identify the
cofree term with its polynomial image; there is no coordinate quotient here. -/
theorem termPolynomial_injective (s : ℕ) (n : ℤ) :
    Function.Injective (termPolynomial s n) := by
  exact (open CategoryTheory MonoidalCategory KIP126.Algebra KIP126.Algebra.GradedVectorSpace in by
    set_option backward.isDefEq.respectTransparency false in
      classical
      let D := Σ q : {p : ℤ × ℤ // p.1+p.2=n}, MilnorWord s q.val.1 × MilnorMonomial q.val.2
      let l : Fin s × ℕ → Fin (s+1) × ℕ := fun a => (a.1.castAdd 1,a.2)
      let r : Fin 1 × ℕ → Fin (s+1) × ℕ := fun a => (a.1.natAdd s,a.2)
      have hl : Function.Injective l := by
        rintro ⟨a,b⟩ ⟨c,d⟩ h
        have hh := Prod.mk.inj h
        exact Prod.ext (Fin.castAdd_injective s 1 hh.1) hh.2
      have hr : Function.Injective r := by
        rintro ⟨a,b⟩ ⟨c,d⟩ h
        have hh := Prod.mk.inj h
        exact Prod.ext (Fin.natAdd_injective 1 s hh.1) hh.2
      have hd (a : Fin s × ℕ) (b : Fin 1 × ℕ) : l a ≠ r b := by
        intro h
        have hh := congrArg (fun p : Fin (s+1) × ℕ => p.1.val) h
        change a.1.val = s+b.1.val at hh
        have := a.1.isLt
        omega
      let ex (d : D) : (Fin (s+1) × ℕ) →₀ ℕ :=
        Finsupp.mapDomain l ((slotExponentsEquiv s).symm d.2.1.val) +
          Finsupp.mapDomain r ((slotExponentsEquiv 1).symm (fun _ => d.2.2.val))
      have he : Function.Injective ex := by
        rintro ⟨⟨⟨i,j⟩,hij⟩,w,m⟩ ⟨⟨⟨i',j'⟩,hij'⟩,w',m'⟩ h
        have hw : (slotExponentsEquiv s).symm w.val = (slotExponentsEquiv s).symm w'.val := by
          ext a
          have hh := congrArg (fun z => z (l a)) h
          have hz (v : (Fin 1 × ℕ) →₀ ℕ) : Finsupp.mapDomain r v (l a) = 0 :=
            Finsupp.mapDomain_notin_range _ _ (by rintro ⟨b,hb⟩; exact hd a b hb.symm)
          simpa only [ex, Finsupp.add_apply, Finsupp.mapDomain_apply hl, hz, add_zero] using hh
        have hm : (slotExponentsEquiv 1).symm (fun _ => m.val) =
            (slotExponentsEquiv 1).symm (fun _ => m'.val) := by
          ext b
          have hh := congrArg (fun z => z (r b)) h
          have hz (v : (Fin s × ℕ) →₀ ℕ) : Finsupp.mapDomain l v (r b) = 0 :=
            Finsupp.mapDomain_notin_range _ _ (by rintro ⟨a,ha⟩; exact hd a b ha)
          simpa only [ex, Finsupp.add_apply, hz, Finsupp.mapDomain_apply hr, zero_add] using hh
        have hw' := (slotExponentsEquiv s).symm.injective hw
        have hm' := congrFun ((slotExponentsEquiv 1).symm.injective hm) 0
        have hi : i=i' := w.property.1.symm.trans ((congrArg wordDegree hw').trans w'.property.1)
        have hj : j=j' := m.property.symm.trans ((congrArg (fun d => (slotWeight d : ℤ)) hm').trans m'.property)
        subst i'
        subst j'
        have hw'' : w=w' := Subtype.ext hw'
        have hm'' : m=m' := Subtype.ext hm'
        subst w'
        subst m'
        rfl
      let bas (d : D) : (term s).A n :=
        (GradedObject.Monoidal.ιTensorObj (wordSpace s) Coalgebra.dualSteenrod.X
          d.1.val.1 d.1.val.2 n d.1.property).hom
            (TensorProduct.tmul F2 (Finsupp.single d.2.1 1) (Finsupp.single d.2.2 1))
      let back : TensorPower (s+1) →ₗ[F2] (term s).A n :=
        (MvPolynomial.basisMonomials (Fin (s+1) × ℕ) F2).constr F2
          (fun d => if h : ∃ a, ex a = d then bas h.choose else 0)
      have hb (a : D) : back (MvPolynomial.monomial (ex a) 1) = bas a := by
        have h : ∃ b, ex b = ex a := ⟨a,rfl⟩
        change back ((MvPolynomial.basisMonomials (Fin (s+1) × ℕ) F2) (ex a)) = _
        simp only [back, Module.Basis.constr_basis, dif_pos h]
        exact congrArg bas (he h.choose_spec)
      have hf (a : D) : termPolynomial s n (bas a) = MvPolynomial.monomial (ex a) 1 := by
        change (CategoryStruct.comp
          (GradedObject.Monoidal.ιTensorObj (wordSpace s) Coalgebra.dualSteenrod.X
            a.1.val.1 a.1.val.2 n a.1.property)
          (GradedObject.Monoidal.tensorObjDesc (fun i j _ => summandPolynomial s i j))).hom _ = _
        rw [GradedObject.Monoidal.ι_tensorObjDesc]
        dsimp only [summandPolynomial, ModuleCat.hom_ofHom]
        erw [TensorProduct.lift.tmul]
        change MvPolynomial.rename l (milnorWordPolynomial s a.1.val.1 (Finsupp.single a.2.1 1)) *
          MvPolynomial.rename r (Coalgebra.polynomial a.1.val.2 (Finsupp.single a.2.2 1)) = _
        simp only [milnorWordPolynomial, Coalgebra.polynomial]
        erw [Finsupp.linearCombination_single, Finsupp.linearCombination_single]
        simp [Coalgebra.monomialPolynomial, ex, l, r, MvPolynomial.rename_monomial,
          MvPolynomial.monomial_mul]
      have hi : back.comp (termPolynomial s n) = LinearMap.id := by
        have hh : ModuleCat.ofHom (back.comp (termPolynomial s n)) = CategoryStruct.id ((term s).A n) := by
          apply GradedObject.Monoidal.tensorObj_ext
          intro i j hij
          apply ModuleCat.hom_ext
          apply ((Finsupp.basisSingleOne : Module.Basis (MilnorWord s i) F2 (MilnorWord s i →₀ F2)).tensorProduct
            (Finsupp.basisSingleOne : Module.Basis (MilnorMonomial j) F2 (MilnorMonomial j →₀ F2))).ext
          rintro ⟨w,m⟩
          simp only [Module.Basis.tensorProduct_apply, Finsupp.coe_basisSingleOne]
          let d : D := ⟨⟨(i,j),hij⟩,(w,m)⟩
          change back (termPolynomial s n (bas d)) = bas d
          rw [hf, hb]
        exact congrArg ModuleCat.Hom.hom hh
      intro x y h
      have hh := congrArg back h
      simpa only [← LinearMap.comp_apply, hi, LinearMap.id_apply] using hh)

end KIP126.Steenrod.Milnor.Ext.Cofree
