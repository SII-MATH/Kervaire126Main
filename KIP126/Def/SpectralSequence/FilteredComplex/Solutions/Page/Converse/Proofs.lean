module

public import KIP126.Def.SpectralSequence.FilteredComplex.Solutions.Page.Proofs
public import Mathlib.CategoryTheory.Preadditive.Projective.Basic

@[expose] public section

/-! A page relation can be strictified on a projective test object. The
correction is lifted from the actual boundary image and lies in the next
source filtration; no comparison map or new differential is assumed. -/

namespace KIP126.SpectralSequence.FilteredComplex.Solutions

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits

universe u v
variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Projectivity lifts an actual cycle through the image of its cycle kernel. -/
theorem exists_strict_lifts_of_cycle (FC : FilteredComplex C) (s k : ℤ) (n : ℕ)
    {T : C} [Projective T]
    (z : T ⟶ Subobject.underlying.obj (FC.cycleSubobject s k ↑n)) :
    ∃ (xl : T ⟶ Subobject.underlying.obj (FC.fil s k))
      (yl : T ⟶ Subobject.underlying.obj (FC.fil (s + ↑n) (k - 1))),
      xl ≫ FC.filToAssocGraded s k = z ≫ (FC.cycleSubobject s k ↑n).arrow ∧
      xl ≫ (FC.fil s k).arrow ≫ FC.d k =
        yl ≫ (FC.fil (s + ↑n) (k - 1)).arrow := by
  let f := (FC.fil s k).arrow ≫ FC.d k ≫
    cokernel.π (FC.fil (s + ↑n) (k - 1)).arrow
  let K := kernelSubobject f
  let p := factorThruImageSubobject (K.arrow ≫ FC.filToAssocGraded s k)
  let u := Projective.factorThru z p
  let xl := u ≫ K.arrow
  have hzero : (xl ≫ (FC.fil s k).arrow ≫ FC.d k) ≫
      cokernel.π (FC.fil (s + ↑n) (k - 1)).arrow = 0 := by
    simpa only [xl, Category.assoc, comp_zero] using
      congrArg (fun q => u ≫ q) (kernelSubobject_arrow_comp f)
  let yl := Abelian.monoLift (FC.fil (s + ↑n) (k - 1)).arrow
    (xl ≫ (FC.fil s k).arrow ≫ FC.d k) hzero
  refine ⟨xl, yl, ?_, (Abelian.monoLift_comp _ _ _).symm⟩
  calc
    xl ≫ FC.filToAssocGraded s k =
        u ≫ p ≫ (FC.cycleSubobject s k ↑n).arrow := by
          change (u ≫ K.arrow) ≫ FC.filToAssocGraded s k =
            u ≫ factorThruImageSubobject (K.arrow ≫ FC.filToAssocGraded s k) ≫
              (imageSubobject (K.arrow ≫ FC.filToAssocGraded s k)).arrow
          simp only [Category.assoc, imageSubobject_arrow_comp]
    _ = z ≫ (FC.cycleSubobject s k ↑n).arrow := by
      rw [← Category.assoc, Projective.factorThru_comp]

/-- Lift a boundary first through its intersection image, then through the
actual differential image. The two lifts obey an equality in the ambient complex. -/
theorem exists_lifts_of_boundary (FC : FilteredComplex C) (s k : ℤ) (n : ℕ)
    {T : C} [Projective T]
    (b : T ⟶ Subobject.underlying.obj (FC.boundarySubobject s k ↑n)) :
    ∃ (a : T ⟶ Subobject.underlying.obj (FC.fil (s - ↑n + 1) (k + 1)))
      (c : T ⟶ Subobject.underlying.obj (FC.fil s k)),
      a ≫ (FC.fil (s - ↑n + 1) (k + 1)).arrow ≫ FC.complex.d (k + 1) k =
        c ≫ (FC.fil s k).arrow ∧
      c ≫ FC.filToAssocGraded s k = b ≫ (FC.boundarySubobject s k ↑n).arrow := by
  let d := (FC.fil (s - ↑n + 1) (k + 1)).arrow ≫ FC.dToK k
  let I := imageSubobject d ⊓ FC.fil s k
  let oI := Subobject.ofLE I (FC.fil s k) inf_le_right
  let p := factorThruImageSubobject (oI ≫ FC.filToAssocGraded s k)
  let u := Projective.factorThru b p
  let c := u ≫ oI
  let a := Projective.factorThru
    (u ≫ Subobject.ofLE I (imageSubobject d) inf_le_left)
    (factorThruImageSubobject d)
  refine ⟨a, c, ?_, ?_⟩
  · calc
      a ≫ (FC.fil (s - ↑n + 1) (k + 1)).arrow ≫ FC.complex.d (k + 1) k = a ≫ d := rfl
      _ = (a ≫ factorThruImageSubobject d) ≫ (imageSubobject d).arrow := by
        rw [Category.assoc, imageSubobject_arrow_comp]
      _ = (u ≫ Subobject.ofLE I (imageSubobject d) inf_le_left) ≫
          (imageSubobject d).arrow := by rw [Projective.factorThru_comp]
      _ = c ≫ (FC.fil s k).arrow := by
        simp only [c, oI, Category.assoc, Subobject.ofLE_arrow]
  · calc
      c ≫ FC.filToAssocGraded s k =
          u ≫ p ≫ (FC.boundarySubobject s k ↑n).arrow := by
            change (u ≫ oI) ≫ FC.filToAssocGraded s k =
              u ≫ factorThruImageSubobject (oI ≫ FC.filToAssocGraded s k) ≫
                (imageSubobject (oI ≫ FC.filToAssocGraded s k)).arrow
            simp only [Category.assoc, imageSubobject_arrow_comp]
      _ = b ≫ (FC.boundarySubobject s k ↑n).arrow := by
        rw [← Category.assoc, Projective.factorThru_comp]

/-- Equal target page classes differ by an actual boundary on a projective
test object, so a higher-filtration source correction makes the equation strict. -/
theorem nonempty_fiber_of_differentialRelation
    (FC : FilteredComplex C) (bnd : FC.IsBounded) (n : ℕ) (s k : ℤ)
    {T : C} [Projective T]
    {x : T ⟶ FC.assocGraded s k}
    {y : T ⟶ FC.assocGraded (s + ↑n) (k - 1)}
    (h : DifferentialRelation (FC.toSpectralSequence bnd) n (s, k) x y) :
    Nonempty (Fiber FC n s k x y) := by
  obtain ⟨zx, hx, zy, hy, hd⟩ := h
  change T ⟶ Subobject.underlying.obj (FC.cycleSubobject s k ↑n) at zx
  change T ⟶ Subobject.underlying.obj (FC.cycleSubobject (s + ↑n) (k - 1) ↑n) at zy
  change zx ≫ (FC.cycleSubobject s k ↑n).arrow = x at hx
  change zy ≫ (FC.cycleSubobject (s + ↑n) (k - 1) ↑n).arrow = y at hy
  obtain ⟨xl, yl, hxl, hxy⟩ := exists_strict_lifts_of_cycle FC s k n zx
  have hstrict : xl ≫ (FC.differential_preserves s k).choose =
      yl ≫ FC.filtration.inclusion (by omega) (k - 1) := by
    apply (cancel_mono (FC.fil s (k - 1)).arrow).mp
    simpa only [Category.assoc, fil, d,
      (FC.differential_preserves s k).choose_spec,
      Algebra.Filtration.inclusion_arrow] using hxy
  obtain ⟨zx', zy', hx', hy', hd'⟩ :=
    FC.pageDifferential_of_strict_lifts s k n xl yl hstrict
  have hzx : zx' = zx := by
    apply (cancel_mono (FC.cycleSubobject s k ↑n).arrow).mp
    exact hx'.trans hxl
  subst zx'
  have heq : (zy' - zy) ≫ FC.pageπ (s + ↑n) (k - 1) ↑n = 0 := by
    rw [Preadditive.sub_comp, sub_eq_zero, ← hd']
    change zx ≫ _ ≫ (FC.toPreSS bnd).d (n : ℤ) (s, k) = _ at hd
    rw [FC.toPreSS_d_nat bnd] at hd
    exact hd
  let B := FC.boundarySubobject (s + ↑n) (k - 1) ↑n
  let Z := FC.cycleSubobject (s + ↑n) (k - 1) ↑n
  let inclusion := Subobject.ofLE B Z (FC.B_le_Z_aux (s + ↑n) (k - 1) ↑n)
  let b := Abelian.monoLift inclusion (zy' - zy) heq
  have hb : b ≫ B.arrow =
      yl ≫ FC.filToAssocGraded (s + ↑n) (k - 1) - y := by
    calc
      b ≫ B.arrow = (b ≫ inclusion) ≫ Z.arrow := by
        rw [Category.assoc, Subobject.ofLE_arrow]
      _ = (zy' - zy) ≫ Z.arrow := by rw [Abelian.monoLift_comp]
      _ = yl ≫ FC.filToAssocGraded (s + ↑n) (k - 1) - y := by
        rw [Preadditive.sub_comp, hy', hy]
  have hboundary :
      ∃ (a : T ⟶ Subobject.underlying.obj (FC.fil (s + 1) k))
        (c : T ⟶ Subobject.underlying.obj (FC.fil (s + ↑n) (k - 1))),
        a ≫ (FC.fil (s + 1) k).arrow ≫ FC.d k =
          c ≫ (FC.fil (s + ↑n) (k - 1)).arrow ∧
        c ≫ FC.filToAssocGraded (s + ↑n) (k - 1) = b ≫ B.arrow := by
    have transport : ∀ (t l : ℤ), t = s + ↑n - ↑n + 1 → l = k - 1 + 1 →
        ∃ (a : T ⟶ Subobject.underlying.obj (FC.fil t l))
          (c : T ⟶ Subobject.underlying.obj (FC.fil (s + ↑n) (k - 1))),
          a ≫ (FC.fil t l).arrow ≫ FC.complex.d l (k - 1) =
            c ≫ (FC.fil (s + ↑n) (k - 1)).arrow ∧
          c ≫ FC.filToAssocGraded (s + ↑n) (k - 1) = b ≫ B.arrow := by
      intro t l ht hl
      subst t
      subst l
      exact exists_lifts_of_boundary FC (s + ↑n) (k - 1) n b
    exact transport (s + 1) k (by omega) (by omega)
  obtain ⟨a, c, hac, hc⟩ := hboundary
  let inc := Subobject.ofLE (FC.fil (s + 1) k) (FC.fil s k) (FC.fil_anti s k)
  have hac' : (a ≫ inc) ≫ (FC.fil s k).arrow ≫ FC.d k =
      c ≫ (FC.fil (s + ↑n) (k - 1)).arrow := by
    calc
      (a ≫ inc) ≫ (FC.fil s k).arrow ≫ FC.d k =
          a ≫ (FC.fil (s + 1) k).arrow ≫ FC.d k := by
            simpa only [Category.assoc] using
              congrArg (fun q => a ≫ q ≫ FC.d k)
                (Subobject.ofLE_arrow (FC.fil_anti s k))
      _ = c ≫ (FC.fil (s + ↑n) (k - 1)).arrow := hac
  refine ⟨⟨(xl - a ≫ inc, yl - c), (mem_fiber_iff _).mpr ⟨?_, ?_, ?_⟩⟩⟩
  · change (xl - a ≫ inc) ≫ FC.filToAssocGraded s k = x
    rw [Preadditive.sub_comp, Category.assoc]
    have hinc : inc ≫ FC.filToAssocGraded s k = 0 := cokernel.condition inc
    rw [hinc, comp_zero, sub_zero, hxl]
    exact hx
  · change (yl - c) ≫ FC.filToAssocGraded (s + ↑n) (k - 1) = y
    rw [Preadditive.sub_comp, hc, hb]
    abel
  · simp only [Preadditive.sub_comp]
    rw [hxy, hac']

/-- The strict solution fiber and the canonical page relation agree for every
projective test object. In ModuleCat this includes the free rank-one ULift ℤ. -/
theorem differentialRelation_iff_nonempty_fiber
    (FC : FilteredComplex C) (bnd : FC.IsBounded) (n : ℕ) (s k : ℤ)
    {T : C} [Projective T]
    (x : T ⟶ FC.assocGraded s k)
    (y : T ⟶ FC.assocGraded (s + ↑n) (k - 1)) :
    DifferentialRelation (FC.toSpectralSequence bnd) n (s, k) x y ↔
      Nonempty (Fiber FC n s k x y) := by
  constructor
  · exact nonempty_fiber_of_differentialRelation FC bnd n s k
  · rintro ⟨a⟩
    exact differentialRelation_of_fiber FC bnd n s k a

/-- 在投射测试对象上，有限页的商页微分关系与严格过滤代表元关系等价。 -/
theorem differentialRelation_iff_representativeRelation
    (FC : FilteredComplex C) (bnd : FC.IsBounded) (n : ℕ) (s k : ℤ)
    {T : C} [Projective T]
    (x : T ⟶ FC.assocGraded s k)
    (y : T ⟶ FC.assocGraded (s + ↑n) (k - 1)) :
    DifferentialRelation (FC.toSpectralSequence bnd) n (s, k) x y ↔
      FC.RepresentativeRelation n (Int.natCast_nonneg n) s k x y := by
  rw [differentialRelation_iff_nonempty_fiber,
    nonempty_fiber_iff (Int.natCast_nonneg n)]

end KIP126.SpectralSequence.FilteredComplex.Solutions
