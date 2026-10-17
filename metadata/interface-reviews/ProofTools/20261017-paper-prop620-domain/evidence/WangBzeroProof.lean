module

import KIP126.ProofTools.Language

/-!
Coefficient checks for the HZ/16 candidate examined in wang-bzero-proof.md.
This file does not identify any Lean spectrum with these coefficient groups.
It proves only the integer/modulus calculations used after that identification.
All declarations are private evidence, with no production/API changes.
-/

namespace WangBzeroProof

private theorem early_kernel (v : ℤ) : (16 : ℤ) ∣ 8*v ↔ (2 : ℤ) ∣ v := by
  omega

private theorem late_kernel (v : ℤ) : (64 : ℤ) ∣ 8*v ↔ (8 : ℤ) ∣ v := by
  omega

/-- Early higher-source correction 2u-4v has no z-coordinate and hits -8y. -/
private theorem early_correction :
    2*(2 : ℤ)+(-4)=0 ∧ 2*(-4 : ℤ)=-8 := by
  norm_num

/-- Late F1 source elements have x-coordinate 2a and top-cell coordinate 8v;
their y-coordinate is always divisible by 16. -/
private theorem late_higher_y_divisible (a v : ℤ) :
    (16 : ℤ) ∣ 8*(2*a)+2*(8*v) := by
  exact ⟨a+v, by ring⟩

/-- Thus no late higher-source image can have the target's y-coordinate
8 modulo 64. -/
private theorem late_higher_misses_fixed_y (a v k : ℤ) :
    8*(2*a)+2*(8*v) ≠ 8+64*k := by
  omega

/-- At filtration 1 a nonliftable v-component has odd leading coefficient;
the z-coordinate cannot vanish even modulo 8. -/
private theorem nonlift_af1_misses_fixed_y (u v k : ℤ) (hv : Odd v) :
    2*(2*u+v) ≠ 8*k := by
  rcases hv with ⟨m, hm⟩
  omega

/-- The same obstruction at filtration 2. -/
private theorem nonlift_af2_misses_fixed_y (u v k : ℤ) (hv : Odd v) :
    4*(2*u+v) ≠ 8*k := by
  rcases hv with ⟨m, hm⟩
  omega

/-- A d4-top-cell label in source filtration a survives the early q=4
window, but fails the late q=6 window, exactly at a=1 or a=2. -/
private theorem nonlift_window (a : ℤ) (ha : 0<a) (ha3 : a≤3) :
    (4>4-a ∧ 4≤6-a) ↔ (a=1 ∨ a=2) := by
  omega

/-- The proposed extension length is legal on the early page r'=5. -/
private theorem legal_length :
    2≤(5 : ℤ) ∧ 5<7 ∧ 0≤(3 : ℤ) ∧ 3≤5-2 := by
  omega

#print axioms early_kernel
#print axioms late_kernel
#print axioms early_correction
#print axioms late_higher_y_divisible
#print axioms late_higher_misses_fixed_y
#print axioms nonlift_af1_misses_fixed_y
#print axioms nonlift_af2_misses_fixed_y
#print axioms nonlift_window
#print axioms legal_length

end WangBzeroProof
