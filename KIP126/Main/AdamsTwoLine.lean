module

public import KIP126.Main.H6SquarePermanent
public import KIP126.Literature
public import KIP126.AdamsComputation
public import KIP126.SSComputation
import all KIP126.Main.Internal.PageCalculus

/-! AimPaper Corollary 1.5, as a proposition on the actual sphere E₂ page.
The exhaustive classification is assembled from the separately tracked
classical literature, E₂ basis, and d₂-stage inputs. There is no local proof
placeholder and no result-package premise. -/

@[expose] section
namespace KIP126.Main
open CategoryTheory KIP126.Classical.Adams KIP126.Core.SpectralSequence
open KIP126.AdamsSynthetic.Standard (model)

/-- The list in Corollary 1.5, with equality in the actual E₂ module.
The degree equation prevents heterogeneous identifications between stems.
Indices are natural numbers, so the square branch includes h₀². -/
public def AdamsTwoLineListed (t : ℤ) (x : model.classical.sphere.Page 2 (2,t)) : Prop :=
  ∃ i j : ℕ,
    ((i = 0 ∧ j = 2) ∨ (i = 0 ∧ j = 3) ∨ (i = 2 ∧ j = 4) ∨
      (i = 1 ∧ 3 ≤ j) ∨ (i = j ∧ j ≤ 6)) ∧
    ∃ degree : hiDegree i + hiDegree j = (2,t),
      x = (eqToHom (congrArg (ActualE2At model.classical) degree))
        (model.sphereAlgebra.product (hiDegree i) (hiDegree j)
          (model.standardClasses.standardHi i) (model.standardClasses.standardHi j))

/-- Exact exhaustive classification target for AimPaper Corollary 1.5. Survival
retains a common Z∞ representative and a nonzero E∞ image. -/
public def AdamsTwoLineClassification : Prop :=
  ∀ (t : ℤ) (x : model.classical.sphere.Page 2 (2,t)),
    NonzeroSurvival model.classical.sphere (2,t) x ↔ AdamsTwoLineListed t x

private theorem square_listed (j : ℕ) (hj : j ≤ 6) :
    AdamsTwoLineListed ((2 ^ (j+1) : ℕ) : ℤ)
      (model.standardClasses.standardHiSquare j) := by
  refine ⟨j,j,Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl,hj⟩))),?_,?_⟩
  · ext <;> simp [hiDegree, pow_succ, mul_two]
  · rfl

/-- The two square cases already supported by the frozen upstream surface.
The j=5 branch uses Literature.h5Square_permanent; j=6 uses the main theorem.
This does not establish the other listed classes or exhaustiveness. -/
public theorem adams_two_line_known_squares (j : ℕ) (hj : j = 5 ∨ j = 6) :
    NonzeroSurvival model.classical.sphere (2,((2 ^ (j+1) : ℕ) : ℤ))
      (model.standardClasses.standardHiSquare j) ∧
    AdamsTwoLineListed ((2 ^ (j+1) : ℕ) : ℤ)
      (model.standardClasses.standardHiSquare j) := by
  rcases hj with rfl | rfl
  · exact ⟨KIP126.Literature.Standard.h5Square_permanent, square_listed 5 (by decide)⟩
  · exact ⟨h6_sq_permanent model.standardClasses, square_listed 6 (by decide)⟩

/-- In stem 126 the classification is already complete: the only nonzero
surviving E₂ class is h₆². This uses the fixed E₂ exhaustive-basis input. -/
public theorem adams_two_line_stem126 (x : model.classical.sphere.Page 2 (2,128)) :
    NonzeroSurvival model.classical.sphere (2,128) x ↔
      x = model.standardClasses.standardH6Square := by
  constructor
  · intro hx
    rcases KIP126.Computation.Standard.square_exhaustive x with hz | he
    · obtain ⟨z,hz',hnz⟩ := hx
      let D := model.classical.sphere.ssData (2,128)
      have h := D.infinity_projection_eq_of_page_projection_eq
        (↑(2-model.classical.sphere.r₀).toNat) z 0
        (by simpa only [map_zero] using hz'.trans hz)
      exact False.elim (hnz (by simpa only [map_zero] using h))
    · exact he
  · rintro rfl
    exact h6_sq_permanent model.standardClasses

private theorem survival_regrade {p q : ℤ × ℤ} (h : p = q)
    (x : ActualE2At model.classical p) :
    NonzeroSurvival model.classical.sphere q
      ((eqToHom (congrArg (ActualE2At model.classical) h)) x) ↔
    NonzeroSurvival model.classical.sphere p x := by
  subst q
  rfl

private theorem square_survival_iff (j : ℕ) :
    NonzeroSurvival model.classical.sphere (hiDegree j + hiDegree j)
      (KIP126.Literature.Standard.hiProduct j j) ↔
    NonzeroSurvival model.classical.sphere (2,((2^(j+1) : ℕ) : ℤ))
      (model.standardClasses.standardHiSquare j) := by
  have hd : hiDegree j + hiDegree j = (2,((2^(j+1) : ℕ) : ℤ)) := by
    ext <;> simp [hiDegree,pow_succ,mul_two]
  have hs : model.standardClasses.standardHiSquare j =
      (eqToHom (congrArg (ActualE2At model.classical) hd))
        (KIP126.Literature.Standard.hiProduct j j) := rfl
  rw [hs]
  exact (survival_regrade hd _).symm

private theorem survival_nonzero {p : ℤ × ℤ}
    {x : model.classical.sphere.Page 2 p}
    (hx : NonzeroSurvival model.classical.sphere p x) : x ≠ 0 := by
  intro hzero
  obtain ⟨z,hz,hnz⟩ := hx
  let D := model.classical.sphere.ssData p
  have h := D.infinity_projection_eq_of_page_projection_eq
    (↑(2-model.classical.sphere.r₀).toNat) z 0
    (by simpa only [map_zero] using hz.trans hzero)
  exact hnz (by simpa only [map_zero] using h)

private theorem survival_reaches_three {p : ℤ × ℤ}
    {x : model.classical.sphere.Page 2 p}
    (hx : NonzeroSurvival model.classical.sphere p x) :
    ReachesPage model.classical.sphere 3 p x := by
  obtain ⟨z,hz,_⟩ := hx
  let D := model.classical.sphere.ssData p
  let zr := (Subobject.ofLE (D.Z ⊤) (D.Z ↑(3-model.classical.sphere.r₀).toNat)
    (D.Z_anti le_top)) z
  refine ⟨D.pageπ _ zr,by decide,zr,?_,rfl⟩
  dsimp only [zr]
  rw [← CategoryTheory.comp_apply,← Category.assoc,Subobject.ofLE_comp_ofLE]
  exact hz

private theorem listed_pair_survives (i j : ℕ)
    (h : (i = 0 ∧ j = 2) ∨ (i = 0 ∧ j = 3) ∨ (i = 2 ∧ j = 4) ∨
      (i = 1 ∧ 3 ≤ j) ∨ (i = j ∧ j ≤ 6)) :
    NonzeroSurvival model.classical.sphere (hiDegree i + hiDegree j)
      (KIP126.Literature.Standard.hiProduct i j) := by
  rcases h with h02 | h03 | h24 | ⟨rfl,hj⟩ | ⟨heq,hj⟩
  · exact KIP126.Literature.Standard.may_two_line_products_permanent i j (Or.inl h02)
  · exact KIP126.Literature.Standard.may_two_line_products_permanent i j (Or.inr (Or.inl h03))
  · exact KIP126.Literature.Standard.may_two_line_products_permanent i j (Or.inr (Or.inr h24))
  · exact KIP126.Literature.Standard.mahowald_eta_family_permanent j hj
  · subst i
    apply (square_survival_iff j).mpr
    by_cases hlow : j ≤ 3
    · exact KIP126.Literature.Standard.may_low_squares_permanent j hlow
    · have hcases : j = 4 ∨ j = 5 ∨ j = 6 := by omega
      rcases hcases with rfl | rfl | rfl
      · exact KIP126.Literature.Standard.mahowald_tangora_h4_square_permanent
      · exact KIP126.Literature.Standard.h5Square_permanent
      · exact h6_sq_permanent model.standardClasses

private theorem surviving_pair_listed (i j : ℕ) (hij : i ≤ j)
    (hx : NonzeroSurvival model.classical.sphere (hiDegree i + hiDegree j)
      (KIP126.Literature.Standard.hiProduct i j)) :
    (i = 0 ∧ j = 2) ∨ (i = 0 ∧ j = 3) ∨ (i = 2 ∧ j = 4) ∨
      (i = 1 ∧ 3 ≤ j) ∨ (i = j ∧ j ≤ 6) := by
  have hc := KIP126.SSComputation.two_line_d2_candidates i j hij
    (survival_nonzero hx) (survival_reaches_three hx)
  rcases hc with h02 | h03 | h24 | heta | hsq | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ |
    ⟨rfl,rfl⟩
  · exact Or.inl h02
  · exact Or.inr (Or.inl h03)
  · exact Or.inr (Or.inr (Or.inl h24))
  · exact Or.inr (Or.inr (Or.inr (Or.inl heta)))
  · subst i
    have hj : j ≤ 6 := by
      by_contra hn
      exact KIP126.Literature.Standard.hhr_high_squares_not_permanent j (by omega)
        ((square_survival_iff j).mp hx)
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl,hj⟩)))
  · obtain ⟨y,hy⟩ := KIP126.Literature.Standard.mahowald_tangora_h2_h5_d3
    exact False.elim (Internal.nonzero_differential_not_permanent
      (by rw [model.classical.firstPage]; decide) hy hx)
  · obtain ⟨y,hy⟩ := KIP126.Literature.Standard.mahowald_tangora_h3_h5_d4
    exact False.elim (Internal.nonzero_differential_not_permanent
      (by rw [model.classical.firstPage]; decide) hy hx)
  · obtain ⟨y,hy⟩ := KIP126.Literature.Standard.iwx_h3_h6_d3
    exact False.elim (Internal.nonzero_differential_not_permanent
      (by rw [model.classical.firstPage]; decide) hy hx)
  · obtain ⟨y,hy⟩ := KIP126.Literature.Standard.iwx_h0_h4_d3
    exact False.elim (Internal.nonzero_differential_not_permanent
      (by rw [model.classical.firstPage]; decide) hy hx)

/-- AimPaper Corollary 1.5: the full second-line classification on the fixed
sphere. All external input obligations remain in their upstream modules. -/
public theorem adams_two_line_classification : AdamsTwoLineClassification := by
  intro t x
  constructor
  · intro hx
    obtain ⟨i,j,hij,degree,heq⟩ := KIP126.AdamsComputation.two_line_exhaustive t x
      (survival_nonzero hx)
    have hp := (survival_regrade degree (KIP126.Literature.Standard.hiProduct i j)).mp
      (heq ▸ hx)
    exact ⟨i,j,surviving_pair_listed i j hij hp,degree,heq⟩
  · rintro ⟨i,j,hij,degree,heq⟩
    rw [heq]
    exact (survival_regrade degree (KIP126.Literature.Standard.hiProduct i j)).mpr
      (listed_pair_survives i j hij)

end KIP126.Main
