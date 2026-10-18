module

public import KIP126.AdamsSynthetic.System
public import Mathlib.CategoryTheory.Triangulated.Triangulated
public import Mathlib.CategoryTheory.Triangulated.Yoneda

@[expose] section

/-! The actual cone-based Toda relation and its proved laws. Adapted from
Kervaire126 bbac1fc05843bdf2d56057e6114a38839e939378,
Def/StableHomotopy/Toda/{Predicates,Proofs,Coset,Juggling,Law}.
No bracket value or disappearance of indeterminacy is postulated. -/

namespace KIP126.StableHomotopy.Toda

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u v

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, Functor.Additive (shiftFunctor C n)] [Pretriangulated C]

/-- A shifted Toda representative obtained from a distinguished cofiber
triangle for `f`. The extension `gbar` of `g` composes with `h` through the
triangle's connecting map to give `x`. -/
public def Relation {X Y Z W : C} (x : X⟦(1 : ℤ)⟧ ⟶ W)
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W) : Prop :=
  ∃ (Q : C) (i : Y ⟶ Q) (p : Q ⟶ X⟦(1 : ℤ)⟧),
    Triangle.mk f i p ∈ distTriang C ∧
      ∃ gbar : Q ⟶ Z, i ≫ gbar = g ∧ p ≫ x = gbar ≫ h

end KIP126.StableHomotopy.Toda

namespace KIP126.Literature.Route

open CategoryTheory CategoryTheory.MonoidalCategory
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.AdamsSynthetic
open KIP126.Kervaire.Route

universe u v w
noncomputable section
variable {Syn : Type w} [SyntheticCategory.{w,v} Syn]

/-- The actual suspension comparison used for a synthetic triple bracket. -/
public def tripleTodaSource (a aw b bw c cw : ℤ) :
    Smn (Syn := Syn) (a + (b + c) + 1) (aw + (bw + cw)) ≅
      ((SyntheticCategory.biShift (b+c,bw+cw)).obj (Smn a aw))⟦(1 : ℤ)⟧ := by
  simpa only [Prod.mk_add_mk, add_zero, Smn, Functor.comp_obj] using
    ((SyntheticCategory.biShift_comp (a+(b+c),aw+(bw+cw)) (1,0)).app
      (S_0_0 : Syn)).symm ≪≫
    (SyntheticCategory.biShift (1,0)).mapIso
      ((SyntheticCategory.biShift_comp (a,aw) (b+c,bw+cw)).app S_0_0).symm ≪≫
    (SyntheticCategory.biShift_compat 1).app _

/-- Membership in the actual triangulated Toda bracket, including its
full indeterminacy; this is not a freely chosen ternary relation. -/
public def TripleToda {a aw b bw c cw : ℤ}
    (x : BiHom a aw (S_0_0 : Syn)) (y : BiHom b bw (S_0_0 : Syn))
    (z : BiHom c cw (S_0_0 : Syn))
    (value : BiHom (a+(b+c)+1) (aw+(bw+cw)) (S_0_0 : Syn)) : Prop :=
  KIP126.StableHomotopy.Toda.Relation
    ((tripleTodaSource a aw b bw c cw).inv ≫ value)
    ((SyntheticCategory.biShift (b+c,bw+cw)).map x)
    ((SyntheticCategory.biShift_comp (b,bw) (c,cw)).inv.app S_0_0 ≫
      (SyntheticCategory.biShift (c,cw)).map y) z

public def syntheticTwo : BiHom 0 0 (S_0_0 : Syn) :=
  SyntheticCategory.biShift_zero.hom.app S_0_0 ≫ (2 • 𝟙 _)

/-- The source's chosen synthetic lift of h₀. -/
public structure TodaSourceData where
  h0 : BiHom 0 1 (S_0_0 : Syn)

variable {C : Type u} [StableHomotopyCategory.{u,v} C]
  [HasFunctorialCofiber (C := C)] [HasFunctorialCofiber (C := Syn)]
  (D : Model C Syn)

/-- Low-degree Toda input from the fixed source. Every label and product
uses the same supplied synthetic sphere and first-quotient comparison. -/
private structure TodaSourceResults (η : BiHom 1 2 (S_0_0 : Syn))
    (S : TodaSourceData (Syn := Syn)) : Prop where
  h0_label : sphereFirstQuotient D.nu D.quotients.functoriality D.firstQuotient
    1 1 (quotientClass 1 S.h0) = D.standardClasses.standardHi 0
  lambda_h0 : lambdaMultiply 1 S.h0 = syntheticTwo
  h0_eta : sphereProduct S.h0 η = 0
  low_indeterminacy : ∀ a : BiHom 2 3 (S_0_0 : Syn), sphereProduct S.h0 a = 0

/-- The separate comparison/construction obligations used by the secondary
route. These are explicit inputs, not consequences of the low-degree source
results and not an asserted construction of the Toda witnesses. -/
private structure TodaSecondaryComparison (η : BiHom 1 2 (S_0_0 : Syn))
    (S : TodaSourceData (Syn := Syn)) where
  low_bracket : TripleToda S.h0 η S.h0 (by simpa using sphereProduct η η)
  twoStar : BiHom 1 0 (S_0_0 : Syn)
  symmetric : ∀ θ : BiHom 62 64 (S_0_0 : Syn), θ + θ = 0 →
    TripleToda syntheticTwo θ syntheticTwo (by simpa using sphereProduct twoStar θ)
  star_product : ∀ θ : BiHom 62 64 (S_0_0 : Syn),
    sphereProduct twoStar θ = lambdaMultiply 2 (sphereProduct η θ)

end
end KIP126.Literature.Route

namespace KIP126.StableHomotopy.Toda

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u v

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, Functor.Additive (shiftFunctor C n)] [Pretriangulated C]

/-- A Toda relation requires the two adjacent composites to vanish. -/
public theorem composable {X Y Z W : C} {x : X⟦(1 : ℤ)⟧ ⟶ W}
    {f : X ⟶ Y} {g : Y ⟶ Z} {h : Z ⟶ W}
    (hx : Relation x f g h) : f ≫ g = 0 ∧ g ≫ h = 0 := by
  rcases hx with ⟨Q, i, p, hT, gbar, hg, hx⟩
  let T := Triangle.mk f i p
  have hfi : f ≫ i = 0 := by
    have h := comp_distTriang_mor_zero₁₂ T hT
    dsimp only [T, Triangle.mk] at h
    exact h
  have hip : i ≫ p = 0 := by
    have h := comp_distTriang_mor_zero₂₃ T hT
    dsimp only [T, Triangle.mk] at h
    exact h
  constructor
  · calc
      f ≫ g = (f ≫ i) ≫ gbar := by rw [← hg, Category.assoc]
      _ = 0 := by rw [hfi, zero_comp]
  · calc
      g ≫ h = i ≫ (gbar ≫ h) := by rw [← hg, Category.assoc]
      _ = (i ≫ p) ≫ x := by rw [← hx, Category.assoc]
      _ = 0 := by rw [hip, zero_comp]

/-- Every pair of vanishing adjacent composites admits a Toda representative. -/
public theorem exists_relation {X Y Z W : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    (h : Z ⟶ W) (hfg : f ≫ g = 0) (hgh : g ≫ h = 0) :
    ∃ x : X⟦(1 : ℤ)⟧ ⟶ W, Relation x f g h := by
  obtain ⟨Q, i, p, hT⟩ := distinguished_cocone_triangle f
  let T := Triangle.mk f i p
  obtain ⟨gbar, hgbar⟩ := T.yoneda_exact₂ hT g hfg
  dsimp only [T, Triangle.mk] at hgbar
  have hzero : i ≫ (gbar ≫ h) = 0 := by
    calc
      i ≫ (gbar ≫ h) = (i ≫ gbar) ≫ h := by simp only [Category.assoc]
      _ = g ≫ h := by rw [hgbar]
      _ = 0 := hgh
  obtain ⟨x, hx⟩ := T.yoneda_exact₃ hT (gbar ≫ h) hzero
  exact ⟨x, Q, i, p, hT, gbar, hgbar.symm, hx.symm⟩

/-- Adding a left-indeterminacy term preserves the Toda relation. -/
private theorem indeterminacy_left {X Y Z W : C} {x : X⟦(1 : ℤ)⟧ ⟶ W}
    {f : X ⟶ Y} {g : Y ⟶ Z} {h : Z ⟶ W}
    (hx : Relation x f g h) (y : Y⟦(1 : ℤ)⟧ ⟶ W) :
    Relation (x + f⟦(1 : ℤ)⟧' ≫ y) f g h := by
  rcases hx with ⟨Q, i, p, hT, gbar, hg, hx⟩
  refine ⟨Q, i, p, hT, gbar, hg, ?_⟩
  have hpf : p ≫ f⟦(1 : ℤ)⟧' = 0 :=
    comp_distTriang_mor_zero₃₁ (Triangle.mk f i p) hT
  calc
    p ≫ (x + f⟦(1 : ℤ)⟧' ≫ y) = p ≫ x + p ≫ (f⟦(1 : ℤ)⟧' ≫ y) := by
      simp only [Preadditive.comp_add]
    _ = p ≫ x + (p ≫ f⟦(1 : ℤ)⟧') ≫ y := by rw [Category.assoc]
    _ = p ≫ x := by rw [hpf, zero_comp, add_zero]
    _ = gbar ≫ h := hx

/-- Adding a right-indeterminacy term preserves the Toda relation. -/
private theorem indeterminacy_right {X Y Z W : C} {x : X⟦(1 : ℤ)⟧ ⟶ W}
    {f : X ⟶ Y} {g : Y ⟶ Z} {h : Z ⟶ W}
    (hx : Relation x f g h) (z : X⟦(1 : ℤ)⟧ ⟶ Z) :
    Relation (x + z ≫ h) f g h := by
  rcases hx with ⟨Q, i, p, hT, gbar, hg, hx⟩
  refine ⟨Q, i, p, hT, gbar + p ≫ z, ?_, ?_⟩
  · have hip : i ≫ p = 0 :=
      comp_distTriang_mor_zero₂₃ (Triangle.mk f i p) hT
    calc
      i ≫ (gbar + p ≫ z) = i ≫ gbar + i ≫ (p ≫ z) := by
        simp only [Preadditive.comp_add]
      _ = g + (i ≫ p) ≫ z := by rw [hg, Category.assoc]
      _ = g := by rw [hip, zero_comp, add_zero]
  · calc
      p ≫ (x + z ≫ h) = p ≫ x + p ≫ (z ≫ h) := by
        simp only [Preadditive.comp_add]
      _ = gbar ≫ h + (p ≫ z) ≫ h := by rw [hx, Category.assoc]
      _ = (gbar + p ≫ z) ≫ h := by simp only [Preadditive.add_comp]

end KIP126.StableHomotopy.Toda

namespace KIP126.StableHomotopy.Toda

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u v

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, Functor.Additive (shiftFunctor C n)] [Pretriangulated C]

/-- Every difference of representatives is a sum of the two actual indeterminacy terms. -/
private theorem indeterminacy_complete {X Y Z W : C}
    {x₁ x₂ : X⟦(1 : ℤ)⟧ ⟶ W} {f : X ⟶ Y} {g : Y ⟶ Z} {h : Z ⟶ W}
    (hx₁ : Relation x₁ f g h) (hx₂ : Relation x₂ f g h) :
    ∃ (y : Y⟦(1 : ℤ)⟧ ⟶ W) (z : X⟦(1 : ℤ)⟧ ⟶ Z),
      x₁ - x₂ = f⟦(1 : ℤ)⟧' ≫ y + z ≫ h := by
  rcases hx₁ with ⟨Q₁, i₁, p₁, hT₁, g₁, hg₁, hx₁⟩
  rcases hx₂ with ⟨Q₂, i₂, p₂, hT₂, g₂, hg₂, hx₂⟩
  obtain ⟨c, hc₁, hc₂⟩ := complete_distinguished_triangle_morphism
    (Triangle.mk f i₁ p₁) (Triangle.mk f i₂ p₂) hT₁ hT₂
    (𝟙 X) (𝟙 Y) (by
      change f ≫ 𝟙 Y = 𝟙 X ≫ f
      simp only [Category.comp_id, Category.id_comp])
  dsimp only [Triangle.mk] at c hc₁ hc₂
  have hi : i₁ ≫ c = i₂ := by simpa using hc₁
  have hp : p₁ = c ≫ p₂ := by simpa using hc₂
  let δ : Q₁ ⟶ Z := g₁ - c ≫ g₂
  have hδ : i₁ ≫ δ = 0 := by
    dsimp [δ]
    rw [Preadditive.comp_sub, hg₁, ← Category.assoc, hi, hg₂, sub_self]
  obtain ⟨z, hz⟩ := (Triangle.mk f i₁ p₁).yoneda_exact₃ hT₁ δ hδ
  dsimp only [Triangle.mk] at z hz
  have hp₂x₂ : p₁ ≫ x₂ = (c ≫ g₂) ≫ h := by
    rw [hp, Category.assoc, hx₂, ← Category.assoc]
  have hpzh : p₁ ≫ (z ≫ h) = δ ≫ h := by
    rw [← Category.assoc, ← hz]
  let e : X⟦(1 : ℤ)⟧ ⟶ W := x₁ - x₂ - z ≫ h
  have he : p₁ ≫ e = 0 := by
    dsimp [e]
    rw [Preadditive.comp_sub, Preadditive.comp_sub, hx₁, hp₂x₂, hpzh]
    dsimp [δ]
    rw [Preadditive.sub_comp]
    abel
  have hrot : (Triangle.mk f i₁ p₁).rotate ∈ distTriang C :=
    rot_of_distTriang (Triangle.mk f i₁ p₁) hT₁
  obtain ⟨y₀, hy₀⟩ := (Triangle.mk f i₁ p₁).rotate.yoneda_exact₃ hrot e he
  dsimp only [Triangle.mk, Triangle.rotate] at y₀ hy₀
  refine ⟨-y₀, z, ?_⟩
  have hy₀' : e = f⟦(1 : ℤ)⟧' ≫ (-y₀) := by
    simpa [Triangle.rotate] using hy₀
  calc
    x₁ - x₂ = e + z ≫ h := by dsimp [e]; abel
    _ = f⟦(1 : ℤ)⟧' ≫ (-y₀) + z ≫ h := by rw [hy₀']

/-- With any chosen representative as origin, the Toda bracket is exactly
its coset by the full left and right indeterminacy. No uniqueness or vanishing
of either indeterminacy term is assumed. -/
public theorem relation_iff_indeterminacy {X Y Z W : C}
    {x₀ x : X⟦(1 : ℤ)⟧ ⟶ W} {f : X ⟶ Y} {g : Y ⟶ Z} {h : Z ⟶ W}
    (hx₀ : Relation x₀ f g h) :
    Relation x f g h ↔
      ∃ (y : Y⟦(1 : ℤ)⟧ ⟶ W) (z : X⟦(1 : ℤ)⟧ ⟶ Z),
        x - x₀ = f⟦(1 : ℤ)⟧' ≫ y + z ≫ h := by
  constructor
  · exact fun hx => indeterminacy_complete hx hx₀
  · rintro ⟨y, z, hx⟩
    have heq : x = (x₀ + f⟦(1 : ℤ)⟧' ≫ y) + z ≫ h := by
      calc
        x = (x - x₀) + x₀ := (sub_add_cancel x x₀).symm
        _ = (f⟦(1 : ℤ)⟧' ≫ y + z ≫ h) + x₀ := by rw [hx]
        _ = (x₀ + f⟦(1 : ℤ)⟧' ≫ y) + z ≫ h := by abel
    rw [heq]
    exact indeterminacy_right (indeterminacy_left hx₀ y) z

end

end KIP126.StableHomotopy.Toda

namespace KIP126.StableHomotopy.Toda

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u v

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, Functor.Additive (shiftFunctor C n)] [Pretriangulated C]

/-- Toda juggling with its shifted negative sign; this proof requires the octahedral axiom. -/
public theorem juggling [IsTriangulated C]
    {X Y Z W V : C} {x : X⟦(1 : ℤ)⟧ ⟶ W}
    {f : X ⟶ Y} {g : Y ⟶ Z} {h : Z ⟶ W} {d : W ⟶ V}
    (hx : Relation x f g h) (hhd : h ≫ d = 0) :
    ∃ y : Y⟦(1 : ℤ)⟧ ⟶ V,
      Relation y g h d ∧ x ≫ d = (-f⟦(1 : ℤ)⟧') ≫ y := by
  rcases hx with ⟨Q, i, p, hTf, gbar, hg, hx⟩
  let Tf := Triangle.mk f i p
  have hTfi : Tf.rotate ∈ distTriang C := rot_of_distTriang Tf hTf
  obtain ⟨K, v, w, hTbar⟩ := distinguished_cocone_triangle gbar
  obtain ⟨Qg, j, q, hTg⟩ := distinguished_cocone_triangle g
  let Tbar := Triangle.mk gbar v w
  let Tg := Triangle.mk g j q
  let O := CategoryTheory.Triangulated.someOctahedron hg hTfi hTbar hTg
  dsimp only [Tf, Tbar, Tg, Triangle.mk, Triangle.rotate] at O
  have hpm : p ≫ O.m₁ = gbar ≫ j := by
    simpa [Tf, Tbar, Tg, O] using O.comm₁
  have hmq : O.m₁ ≫ q = -f⟦(1 : ℤ)⟧' := by
    exact O.comm₂
  have hgh : g ≫ h = 0 := (composable ⟨Q, i, p, hTf, gbar, hg, hx⟩).2
  obtain ⟨hbar₀, hhbar₀⟩ := Tg.yoneda_exact₂ hTg h hgh
  dsimp only [Tg, Triangle.mk] at hbar₀ hhbar₀
  let δ : X⟦(1 : ℤ)⟧ ⟶ W := x - O.m₁ ≫ hbar₀
  have hpδ : p ≫ δ = 0 := by
    dsimp [δ]
    rw [Preadditive.comp_sub, hx, ← Category.assoc, hpm, Category.assoc,
      ← hhbar₀, sub_self]
  obtain ⟨a, ha⟩ := Tf.rotate.yoneda_exact₃ hTfi δ hpδ
  dsimp only [Tf, Triangle.mk, Triangle.rotate] at a ha
  let hbar : Qg ⟶ W := hbar₀ + q ≫ a
  have hjhbar : j ≫ hbar = h := by
    have hjq : j ≫ q = 0 := by
      have hzero := comp_distTriang_mor_zero₂₃ Tg hTg
      dsimp only [Tg, Triangle.mk] at hzero
      exact hzero
    dsimp [hbar]
    rw [Preadditive.comp_add, ← hhbar₀, ← Category.assoc, hjq, zero_comp, add_zero]
  have hmx : O.m₁ ≫ hbar = x := by
    dsimp [hbar]
    rw [Preadditive.comp_add, ← Category.assoc, hmq]
    rw [← ha]
    dsimp [δ]
    abel
  have hjhd : j ≫ (hbar ≫ d) = 0 := by
    rw [← Category.assoc, hjhbar, hhd]
  obtain ⟨y, hy⟩ := Tg.yoneda_exact₃ hTg (hbar ≫ d) hjhd
  dsimp only [Tg, Triangle.mk] at y hy
  refine ⟨y, ?_, ?_⟩
  · exact ⟨Qg, j, q, hTg, hbar, hjhbar, hy.symm⟩
  · calc
      x ≫ d = (O.m₁ ≫ hbar) ≫ d := by rw [hmx]
      _ = O.m₁ ≫ (hbar ≫ d) := Category.assoc _ _ _
      _ = O.m₁ ≫ (q ≫ y) := by rw [← hy]
      _ = (O.m₁ ≫ q) ≫ y := by rw [Category.assoc]
      _ = (-f⟦(1 : ℤ)⟧') ≫ y := by rw [hmq]


end

end KIP126.StableHomotopy.Toda

namespace KIP126.StableHomotopy.Toda

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.MonoidalCategory

set_option backward.isDefEq.respectTransparency false
universe u v u' v'

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, Functor.Additive (shiftFunctor C n)] [Pretriangulated C]

/-- Precomposition gives a containment, with the actual suspended map
on the Toda representative. -/
public theorem precompose {A X Y Z W : C} {x : X⟦(1 : ℤ)⟧ ⟶ W}
    {f : X ⟶ Y} {g : Y ⟶ Z} {h : Z ⟶ W}
    (hx : Relation x f g h) (a : A ⟶ X) :
    Relation (a⟦(1 : ℤ)⟧' ≫ x) (a ≫ f) g h := by
  obtain ⟨Q, i, p, hT, gbar, hg, hx⟩ := hx
  obtain ⟨Q', i', p', hT'⟩ := distinguished_cocone_triangle (a ≫ f)
  obtain ⟨c, hi, hp⟩ := complete_distinguished_triangle_morphism
    (Triangle.mk (a ≫ f) i' p') (Triangle.mk f i p) hT' hT a (𝟙 Y) (by
      change (a ≫ f) ≫ 𝟙 Y = a ≫ f
      exact Category.comp_id _)
  dsimp only [Triangle.mk] at hi hp
  refine ⟨Q', i', p', hT', c ≫ gbar, ?_, ?_⟩
  · rw [← Category.assoc, hi]
    simpa using hg
  · rw [← Category.assoc, hp, Category.assoc, hx, Category.assoc]

/-- Postcomposition gives a containment for the actual target map. -/
public theorem postcompose {X Y Z W V : C} {x : X⟦(1 : ℤ)⟧ ⟶ W}
    {f : X ⟶ Y} {g : Y ⟶ Z} {h : Z ⟶ W}
    (hx : Relation x f g h) (d : W ⟶ V) :
    Relation (x ≫ d) f g (h ≫ d) := by
  obtain ⟨Q, i, p, hT, gbar, hg, hx⟩ := hx
  refine ⟨Q, i, p, hT, gbar, hg, ?_⟩
  rw [← Category.assoc, hx, Category.assoc]

/-- Moving a factor from the first input into the middle input gives
this containment; its reverse is not asserted. -/
public theorem absorb_first {X Y Z W V : C} {x : X⟦(1 : ℤ)⟧ ⟶ V}
    {f : X ⟶ Y} {g : Y ⟶ Z} {h : Z ⟶ W} {d : W ⟶ V}
    (hx : Relation x (f ≫ g) h d) :
    Relation x f (g ≫ h) d := by
  obtain ⟨Q, i, p, hT, hbar, hh, hx⟩ := hx
  obtain ⟨Q', i', p', hT'⟩ := distinguished_cocone_triangle f
  obtain ⟨c, hi, hp⟩ := complete_distinguished_triangle_morphism
    (Triangle.mk f i' p') (Triangle.mk (f ≫ g) i p) hT' hT (𝟙 X) g (by
      change f ≫ g = 𝟙 X ≫ (f ≫ g)
      exact (Category.id_comp _).symm)
  dsimp only [Triangle.mk] at hi hp
  have hp' : p' = c ≫ p := by simpa using hp
  refine ⟨Q', i', p', hT', c ≫ hbar, ?_, ?_⟩
  · rw [← Category.assoc, hi, Category.assoc, hh]
  · rw [hp', Category.assoc, hx, Category.assoc]

/-- Moving a factor from the last input into the middle input gives
this containment; its reverse is not asserted. -/
public theorem absorb_last {X Y Z W V : C} {x : X⟦(1 : ℤ)⟧ ⟶ V}
    {f : X ⟶ Y} {g : Y ⟶ Z} {h : Z ⟶ W} {d : W ⟶ V}
    (hx : Relation x f g (h ≫ d)) :
    Relation x f (g ≫ h) d := by
  obtain ⟨Q, i, p, hT, gbar, hg, hx⟩ := hx
  refine ⟨Q, i, p, hT, gbar ≫ h, ?_, ?_⟩
  · rw [← Category.assoc, hg]
  · simpa only [Category.assoc] using hx

/-- The four-map shuffle identifies the two sets of products, with the
shifted negative sign. It does not equate arbitrary representatives of
the two Toda brackets. The octahedral hypothesis is the one required
by the underlying juggling law. -/
public theorem shuffle_iff [IsTriangulated C] {X Y Z W V : C}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W) (d : W ⟶ V)
    (hfg : f ≫ g = 0) (hgh : g ≫ h = 0) (hhd : h ≫ d = 0)
    (z : X⟦(1 : ℤ)⟧ ⟶ V) :
    (∃ x : X⟦(1 : ℤ)⟧ ⟶ W, Relation x f g h ∧ x ≫ d = z) ↔
      ∃ y : Y⟦(1 : ℤ)⟧ ⟶ V,
        Relation y g h d ∧ (-f⟦(1 : ℤ)⟧') ≫ y = z := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨y, hy, he⟩ := juggling hx hhd
    exact ⟨y, hy, he.symm⟩
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨x₀, hx₀⟩ := exists_relation f g h hfg hgh
    obtain ⟨y₀, hy₀, hxy₀⟩ := juggling hx₀ hhd
    obtain ⟨u, v, huv⟩ := indeterminacy_complete hy hy₀
    refine ⟨x₀ + f⟦(1 : ℤ)⟧' ≫ (-v), indeterminacy_left hx₀ (-v), ?_⟩
    have hzero : f⟦(1 : ℤ)⟧' ≫ g⟦(1 : ℤ)⟧' = 0 := by
      rw [← Functor.map_comp, hfg, Functor.map_zero]
    have he := congrArg (fun k => f⟦(1 : ℤ)⟧' ≫ k) huv
    simp only [Preadditive.comp_sub, Preadditive.comp_add, ← Category.assoc,
      hzero, zero_comp, zero_add] at he
    simp only [Preadditive.add_comp, Preadditive.comp_neg, Preadditive.neg_comp]
    rw [hxy₀]
    simp only [Preadditive.neg_comp]
    rw [← he]
    abel

private theorem shifted_triangle_distinguished (n : ℤ) {X Y Q : C}
    (f : X ⟶ Y) (i : Y ⟶ Q) (p : Q ⟶ X⟦(1 : ℤ)⟧)
    (hT : Triangle.mk f i p ∈ distTriang C) :
    Triangle.mk (f⟦n⟧') (i⟦n⟧')
      (n.negOnePow • p⟦n⟧' ≫ (shiftFunctorComm C (1 : ℤ) n).hom.app X) ∈ distTriang C := by
  let e : Y⟦n⟧ ≅ Y⟦n⟧ :=
    { hom := n.negOnePow • 𝟙 _
      inv := n.negOnePow • 𝟙 _
      hom_inv_id := by simp [Linear.comp_units_smul, smul_smul]
      inv_hom_id := by simp [Linear.comp_units_smul, smul_smul] }
  apply isomorphic_distinguished _ (Triangle.shift_distinguished _ hT n)
  refine Triangle.isoMk _ _ (Iso.refl _) e (Iso.refl _) ?_ ?_ ?_
  · simp [Triangle.shiftFunctor, Triangle.mk, Category.id_comp, Category.comp_id, e, Linear.comp_units_smul]
  · simp [Triangle.shiftFunctor, Triangle.mk, Category.id_comp, Category.comp_id, e, Linear.units_smul_comp, Linear.comp_units_smul, smul_smul]
  · simp [Triangle.shiftFunctor, Triangle.mk]

omit [HasZeroObject C] [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C] in
private theorem shifted_connecting_comp (n : ℤ) {X Q W : C}
    (p : Q ⟶ X⟦(1 : ℤ)⟧) (x : X⟦(1 : ℤ)⟧ ⟶ W) :
    (n.negOnePow • p⟦n⟧' ≫ (shiftFunctorComm C (1 : ℤ) n).hom.app X) ≫
      (n.negOnePow • ((shiftFunctorComm C (1 : ℤ) n).inv.app X ≫ x⟦n⟧')) =
        (p ≫ x)⟦n⟧' := by
  simp only [Linear.units_smul_comp, Linear.comp_units_smul, smul_smul,
    Int.units_mul_self, one_smul, Category.assoc, Iso.hom_inv_id_app_assoc,
    Functor.map_comp]

/-- Suspension transports the entire Toda relation with its forced
`(-1)^n` sign and the actual comparison of the two iterated shifts. -/
public theorem suspension_iff (n : ℤ) {X Y Z W : C}
    {x : X⟦(1 : ℤ)⟧ ⟶ W} {f : X ⟶ Y} {g : Y ⟶ Z} {h : Z ⟶ W} :
    Relation
      (n.negOnePow • ((shiftFunctorComm C (1 : ℤ) n).inv.app X ≫ x⟦n⟧'))
      (f⟦n⟧') (g⟦n⟧') (h⟦n⟧') ↔ Relation x f g h := by
  constructor
  · rintro ⟨Q', i', p', hT', gbar', hg', hx'⟩
    obtain ⟨Q, i, p, hT⟩ := distinguished_cocone_triangle f
    let δ := n.negOnePow • p⟦n⟧' ≫ (shiftFunctorComm C (1 : ℤ) n).hom.app X
    obtain ⟨c, hi, hp⟩ := complete_distinguished_triangle_morphism
      (Triangle.mk (f⟦n⟧') (i⟦n⟧') δ) (Triangle.mk (f⟦n⟧') i' p')
      (shifted_triangle_distinguished n f i p hT) hT' (𝟙 _) (𝟙 _) (by
        change f⟦n⟧' ≫ 𝟙 _ = 𝟙 _ ≫ f⟦n⟧'
        simp only [Category.comp_id, Category.id_comp])
    dsimp only [Triangle.mk] at hi hp
    have hi' : i⟦n⟧' ≫ c = i' := by simpa only [Category.id_comp] using hi
    have hp' : δ = c ≫ p' := by
      erw [(shiftFunctor C (1 : ℤ)).map_id, Category.comp_id] at hp
      exact hp
    let gbar := (shiftFunctor C n).preimage (c ≫ gbar')
    have hgbar : gbar⟦n⟧' = c ≫ gbar' := Functor.map_preimage _ _
    refine ⟨Q, i, p, hT, gbar, ?_, ?_⟩
    · apply (shiftFunctor C n).map_injective
      rw [Functor.map_comp, hgbar, ← Category.assoc, hi', hg']
    · apply (shiftFunctor C n).map_injective
      rw [← shifted_connecting_comp n p x]
      change δ ≫ _ = _
      rw [hp', Category.assoc, hx', Functor.map_comp, hgbar, Category.assoc]
  · rintro ⟨Q, i, p, hT, gbar, hg, hx⟩
    refine ⟨Q⟦n⟧, i⟦n⟧', n.negOnePow • p⟦n⟧' ≫
      (shiftFunctorComm C (1 : ℤ) n).hom.app X,
      shifted_triangle_distinguished n f i p hT, gbar⟦n⟧', ?_, ?_⟩
    · rw [← Functor.map_comp, hg]
    · rw [shifted_connecting_comp, hx, Functor.map_comp]

variable {D : Type u'} [Category.{v'} D] [Preadditive D]
  [HasZeroObject D] [HasShift D ℤ]
  [∀ n : ℤ, Functor.Additive (shiftFunctor D n)] [Pretriangulated D]

/-- An exact functor transports Toda representatives. The shift
comparison belongs to that same functor. General exact functors only
give this containment, not equality of Toda brackets. -/
public theorem map (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated]
    {X Y Z W : C} {x : X⟦(1 : ℤ)⟧ ⟶ W}
    {f : X ⟶ Y} {g : Y ⟶ Z} {h : Z ⟶ W}
    (hx : Relation x f g h) :
    Relation ((F.commShiftIso (1 : ℤ)).inv.app X ≫ F.map x)
      (F.map f) (F.map g) (F.map h) := by
  obtain ⟨Q, i, p, hT, gbar, hg, hx⟩ := hx
  refine ⟨F.obj Q, F.map i, F.map p ≫ (F.commShiftIso (1 : ℤ)).hom.app X,
    F.map_distinguished (Triangle.mk f i p) hT, F.map gbar, ?_, ?_⟩
  · rw [← F.map_comp, hg]
  · simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
    rw [← F.map_comp, hx, F.map_comp]

variable [MonoidalCategory C]

/-- Tensoring on the right is a product containment when the actual
tensor functor, with its given shift comparison, is exact. -/
public theorem tensor_right (V : C) [(tensorRight V).CommShift ℤ]
    [(tensorRight V).IsTriangulated]
    {X Y Z W : C} {x : X⟦(1 : ℤ)⟧ ⟶ W}
    {f : X ⟶ Y} {g : Y ⟶ Z} {h : Z ⟶ W}
    (hx : Relation x f g h) :
    Relation (((tensorRight V).commShiftIso (1 : ℤ)).inv.app X ≫ (x ▷ V))
      (f ▷ V) (g ▷ V) (h ▷ V) := by
  exact map (tensorRight V) hx

/-- Tensoring on the left is the corresponding product containment
with the actual left-tensor shift comparison. -/
public theorem tensor_left (V : C) [(tensorLeft V).CommShift ℤ]
    [(tensorLeft V).IsTriangulated]
    {X Y Z W : C} {x : X⟦(1 : ℤ)⟧ ⟶ W}
    {f : X ⟶ Y} {g : Y ⟶ Z} {h : Z ⟶ W}
    (hx : Relation x f g h) :
    Relation (((tensorLeft V).commShiftIso (1 : ℤ)).inv.app X ≫ (V ◁ x))
      (V ◁ f) (V ◁ g) (V ◁ h) := by
  exact map (tensorLeft V) hx

end KIP126.StableHomotopy.Toda
