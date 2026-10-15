module

public import KIP126.Main.Conditions

/-! Finite-coordinate algebra retained from NuTargetHelpers.lean:141–275,
bbac1fc05843 (MIT). These are proofs about the stated coordinates, with no
new computation assumptions; the application uses the fixed archive rows. -/
@[expose] section
namespace KIP126.Main.SectionSeven.Internal
noncomputable section

private theorem binary_expansion {N : ℕ} (f : Fin N →₀ ZMod 2) :
    f = ∑ i : Fin N, if f i = 0 then 0 else Finsupp.single i 1 := by
  classical
  ext i
  simp only [Finsupp.finsetSum_apply]
  rw [Finset.sum_eq_single i]
  · generalize f i = b
    fin_cases b
    · change (0 : ZMod 2) = (if (0 : ZMod 2)=0 then 0 else Finsupp.single i 1) i
      simp
    · change (1 : ZMod 2) = (if (1 : ZMod 2)=0 then 0 else Finsupp.single i 1) i
      simp
  · intro j hj hji
    by_cases hf : f j = 0
    · simp [hf]
    · simp [hf,hji]
  · simp

private theorem two_coordinate_cosets {V : Type*} [AddCommGroup V] [Module ℤ V]
    (e : V ≃ₗ[ℤ] (Fin 2 →₀ ZMod 2)) (B : Submodule ℤ V)
    (hB : e.symm (Finsupp.single 0 1) + e.symm (Finsupp.single 1 1) ∈ B)
    (x : V) : x ∈ B ∨ x - e.symm (Finsupp.single 1 1) ∈ B := by
  classical
  have hn : -e.symm (Finsupp.single (1:Fin 2) 1) = e.symm (Finsupp.single (1:Fin 2) 1) := by
    rw [←map_neg]
    congr 1
    ext i
    simp
  let c : Fin 2 → ZMod 2 := e x
  have hx := congrArg e.symm (binary_expansion (e x))
  simp only [LinearEquiv.symm_apply_apply,map_sum,map_add,Fin.sum_univ_succ,apply_ite,map_zero] at hx
  change x = (if c 0=0 then 0 else e.symm (Finsupp.single 0 1)) +
    ((if c 1=0 then 0 else e.symm (Finsupp.single 1 1))+0) at hx
  simp only [add_zero] at hx
  by_cases h0 : c 0=0 <;> by_cases h1 : c 1=0
  · left
    rw [hx]
    simpa only [h0,h1,if_true,zero_add] using B.zero_mem
  · right
    rw [hx]
    simp only [h0,h1,if_false,if_true,zero_add,sub_self]
    exact B.zero_mem
  · right
    rw [hx]
    simpa only [h0,h1,if_false,if_true,add_zero,sub_eq_add_neg,hn] using hB
  · left
    rw [hx]
    simpa only [h0,h1,if_false] using hB

private theorem three_coordinate_cosets {V : Type*} [AddCommGroup V] [Module ℤ V]
    (e : V ≃ₗ[ℤ] (Fin 3 →₀ ZMod 2)) (B : Submodule ℤ V)
    (h1 : e.symm (Finsupp.single 1 1) ∈ B)
    (h2 : e.symm (Finsupp.single 2 1) ∈ B) (x : V) :
    x ∈ B ∨ x-e.symm (Finsupp.single 0 1) ∈ B := by
  classical
  have hif (c : ZMod 2) {a : V} (h : a ∈ B) : (if c=0 then 0 else a) ∈ B := by
    split
    · exact B.zero_mem
    · exact h
  let c : Fin 3 → ZMod 2 := e x
  have hx := congrArg e.symm (binary_expansion (e x))
  simp only [LinearEquiv.symm_apply_apply,map_sum,map_add,Fin.sum_univ_succ,apply_ite,map_zero] at hx
  change x = (if c 0=0 then 0 else e.symm (Finsupp.single 0 1)) +
    ((if c 1=0 then 0 else e.symm (Finsupp.single 1 1)) +
    ((if c 2=0 then 0 else e.symm (Finsupp.single 2 1))+0)) at hx
  simp only [add_zero] at hx
  have hm := B.add_mem (hif (c 1) h1) (hif (c 2) h2)
  by_cases h0 : c 0=0
  · left
    rw [hx]
    simpa only [h0,if_true,zero_add] using hm
  · right
    rw [hx]
    simp only [h0,if_false]
    convert hm using 1; first | rfl | abel

end
end KIP126.Main.SectionSeven.Internal
