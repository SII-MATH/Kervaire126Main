module

public import KIP126.Main.Computation.LinCoordinates.PresentationTheorems

public import KIP126.Main.Computation.LinCoordinates.Presentation
public import KIP126.Computation.LinCoordinates.Model.Product.Data

@[expose] public section

namespace KIP126.Classical.Adams

/-- Every internal page class in range has a data-model preimage (PR #110). -/
theorem linToSphere_exists_preimage (s t : ℕ) (ht : t ≤ 261)
    (a : sphereAdamsData.Page 2 ((s : ℤ), (t : ℤ))) :
    ∃ x : KIP126.LinE2.E2At s t, linE2Presentation.comparison s t ht x = a :=
  ⟨(linE2Presentation.comparison s t ht).symm a,
    (linE2Presentation.comparison s t ht).apply_symm_apply a⟩

/-- Equality on the internal page is exactly equality in the data quotient. -/
theorem linToSphere_eq_iff (s t : ℕ) (ht : t ≤ 261)
    (x y : KIP126.LinE2.E2At s t) :
    linE2Presentation.comparison s t ht x = linE2Presentation.comparison s t ht y ↔
      x.val = y.val := by
  constructor
  · intro h
    exact congrArg Subtype.val ((linE2Presentation.comparison s t ht).injective h)
  · intro h
    exact congrArg (linE2Presentation.comparison s t ht) (Subtype.ext h)

theorem linToSphere_ne_zero_iff (s t : ℕ) (ht : t ≤ 261)
    (x : KIP126.LinE2.E2At s t) :
    linE2Presentation.comparison s t ht x ≠ 0 ↔ x.val ≠ 0 := by
  simpa only [map_zero, ZeroMemClass.coe_zero] using
    not_congr (linToSphere_eq_iff s t ht x 0)

/-- Transport a quotient-algebra product equality to the sphere E₂ page
along the comparison assumed in the computation hypotheses. -/
theorem linToSphere_mul {s t s' t' : ℕ} (h : t + t' ≤ 261)
    (x : KIP126.LinE2.E2At s t) (y : KIP126.LinE2.E2At s' t') :
    linE2Presentation.comparison (s + s') (t + t') h (KIP126.LinE2.mulAt x y) =
      linE2Presentation.product s t s' t'
        (linE2Presentation.comparison s t (by omega) x)
        (linE2Presentation.comparison s' t' (by omega) y) :=
  linE2Presentation.comparison_mul s t s' t' h x y _ rfl

theorem linToSphere_product_eq {s t s' t' : ℕ} (h : t + t' ≤ 261)
    (x : KIP126.LinE2.E2At s t) (y : KIP126.LinE2.E2At s' t')
    (z : KIP126.LinE2.E2At (s + s') (t + t')) (hz : x.val * y.val = z.val) :
    linE2Presentation.product s t s' t'
        (linE2Presentation.comparison s t (by omega) x)
        (linE2Presentation.comparison s' t' (by omega) y) =
      linE2Presentation.comparison (s + s') (t + t') h z :=
  (linE2Presentation.comparison_mul s t s' t' h x y z hz).symm

/-- Zero products transfer only when the target degree is still covered. -/
theorem linToSphere_product_eq_zero {s t s' t' : ℕ} (h : t + t' ≤ 261)
    (x : KIP126.LinE2.E2At s t) (y : KIP126.LinE2.E2At s' t')
    (hz : x.val * y.val = 0) :
    linE2Presentation.product s t s' t'
        (linE2Presentation.comparison s t (by omega) x)
        (linE2Presentation.comparison s' t' (by omega) y) = 0 := by
  simpa only [map_zero] using linToSphere_product_eq h x y 0 hz

end KIP126.Classical.Adams
