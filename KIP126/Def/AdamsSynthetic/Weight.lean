module

public import KIP126.Def.AdamsSynthetic.ExtensionLabels

@[expose] section

/-! Weight lowering at E∞ belongs to the specified ν-family. The maps,
composition and naturality are structural data; surjectivity is a separate
literature result and is not asserted here. -/
namespace KIP126.AdamsSynthetic
open CategoryTheory KIP126.StableHomotopy KIP126.Synthetic.Context
open KIP126.Synthetic.SpectralSequence KIP126.Core.SpectralSequence
open KIP126.Kervaire.Route
universe u v w
variable {C : Type u} [StableHomotopyCategory.{u,v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w,v} Syn]
  [HasFunctorialCofiber (C := Syn)]

/-- The given comparison evaluated at an actual weight. The nonnegative
λ exponent is forced by `w ≤ t`; no new choice of standard class is made. -/
public noncomputable def nuWeightLabel (D : Model C Syn) (X : ClassicalObject)
    (s t w : ℤ) (hw : w ≤ t)
    (x : (D.classical.obj (X.obj D.auxiliary)).Page 2 (s,t)) :
    (D.family.obj (D.nu.functor.obj (X.obj D.auxiliary))).E₂ (s,t,w) :=
  regradeE2 (by
    ext <;> simp [Int.toNat_of_nonneg (sub_nonneg.mpr hw)])
    (targetNuLabel D X s t (t-w).toNat x)

/-- A coherent weight map on the actual ν(X) infinity pages. Compatibility
with the specified E₂ labels identifies this map as the weight comparison,
rather than an arbitrary map between unrelated page objects. -/
public structure NuInfinityWeightMaps (D : Model C Syn) where
  map : ∀ (X : ClassicalObject) (s t w₁ w₂ : ℤ) (_hw : w₁ ≤ w₂) (_ht : w₂ ≤ t),
    ((D.family.obj (D.nu.functor.obj (X.obj D.auxiliary))).sequence.ssData (s,t,w₂)).eInfty ⟶
      ((D.family.obj (D.nu.functor.obj (X.obj D.auxiliary))).sequence.ssData (s,t,w₁)).eInfty
  map_self : ∀ (X : ClassicalObject) (s t w : ℤ) (hw : w ≤ t),
    map X s t w w le_rfl hw = 𝟙 _
  map_comp : ∀ (X : ClassicalObject) (s t w₁ w₂ w₃ : ℤ)
      (h₁₂ : w₁ ≤ w₂) (h₂₃ : w₂ ≤ w₃) (h₃ : w₃ ≤ t),
    map X s t w₂ w₃ h₂₃ h₃ ≫ map X s t w₁ w₂ h₁₂ (h₂₃.trans h₃) =
      map X s t w₁ w₃ (h₁₂.trans h₂₃) h₃
  naturality : ∀ (X Y : ClassicalObject) (f : X.obj D.auxiliary ⟶ Y.obj D.auxiliary)
      (s t w₁ w₂ : ℤ) (hw : w₁ ≤ w₂) (ht : w₂ ≤ t),
    (D.family.map (D.nu.functor.map f)).eInftyMap (s,t,w₂) ≫ map Y s t w₁ w₂ hw ht =
      map X s t w₁ w₂ hw ht ≫ (D.family.map (D.nu.functor.map f)).eInftyMap (s,t,w₁)
  representative : ∀ (X : ClassicalObject) (s t w₁ w₂ : ℤ)
      (hw : w₁ ≤ w₂) (ht : w₂ ≤ t)
      (x : (D.classical.obj (X.obj D.auxiliary)).Page 2 (s,t))
      (z : ((D.family.obj (D.nu.functor.obj (X.obj D.auxiliary))).sequence.ssData (s,t,w₂)).eInfty),
    HasInfinityRepresentative _ 2 (s,t,w₂) (nuWeightLabel D X s t w₂ ht x) z →
      HasInfinityRepresentative _ 2 (s,t,w₁) (nuWeightLabel D X s t w₁ (hw.trans ht) x)
        (map X s t w₁ w₂ hw ht z)

end KIP126.AdamsSynthetic
