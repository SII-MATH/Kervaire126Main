module

public import Mathlib.Data.ZMod.Basic

@[expose] public section

namespace KIP126.Algebra

/-- An equivalence from a group to the two-element field that sends identity
to zero necessarily preserves multiplication as addition. -/
theorem equivTwo_map_mul {G : Type*} [Group G] (e : G ≃ ZMod 2) (he : e 1 = 0)
    (a b : G) : e (a*b) = e a + e b := by
  have casesTwo (x : G) : x = 1 ∨ e x = 1 := by
    have hz : e x = 0 ∨ e x = 1 := (by decide : ∀ z : ZMod 2, z = 0 ∨ z = 1) (e x)
    exact hz.imp (fun h => e.injective (h.trans he.symm)) id
  rcases casesTwo a with rfl | ha
  · simp [he]
  rcases casesTwo b with rfl | hb
  · simp [he]
  have ha' : a ≠ 1 := by intro h; rw [h,he] at ha; exact zero_ne_one ha
  have hmul : a*b = 1 := by
    rcases casesTwo (a*b) with h | h
    · exact h
    · have : a*b = b := e.injective (h.trans hb.symm)
      exact False.elim (ha' (mul_right_cancel (this.trans (one_mul b).symm)))
  rw [hmul,he,ha,hb]
  decide

/-- Additive form of the two-element group calculation. -/
theorem equivTwo_map_add {G : Type*} [AddGroup G] (e : G ≃ ZMod 2) (he : e 0 = 0)
    (a b : G) : e (a+b) = e a + e b := by
  let e' : Multiplicative G ≃ ZMod 2 :=
    { toFun x := e x.toAdd
      invFun x := Multiplicative.ofAdd (e.symm x)
      left_inv x := e.symm_apply_apply x
      right_inv x := e.apply_symm_apply x }
  exact equivTwo_map_mul e' he (Multiplicative.ofAdd a) (Multiplicative.ofAdd b)

end KIP126.Algebra
