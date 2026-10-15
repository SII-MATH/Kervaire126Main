module

public import KIP126.Def.Synthetic.AdamsSequence.Data
public import KIP126.Def.Synthetic.PageExtension.Lambda.Data

@[expose] public section

namespace KIP126.Synthetic.SpectralSequence

open CategoryTheory KIP126.Synthetic.Context KIP126.StableHomotopy

universe u v
noncomputable section
variable {Syn : Type u} [SyntheticCategory.{u, v} Syn]

/-- A specified weight-shift comparison on the same family's actual E∞.
Its naturality is a separate condition; no such comparison is chosen globally. -/
structure EInftyWeightShift (F : SyntheticAdamsFamily Syn) where
  iso : ∀ (A : Syn) (k : ℤ) (p : ℤ × ℤ) (w : ℤ),
    ((F.obj ((SyntheticCategory.biShift (0, k)).obj A)).sequence.ssData
      (p.1, p.2, w + k)).eInfty ≃ₗ[ℤ]
        ((F.obj A).sequence.ssData (p.1, p.2, w)).eInfty

namespace EInftyWeightShift
variable {F : SyntheticAdamsFamily Syn}

/-- The specified comparison with the subtraction spelling of the weight. -/
def lowerIso (S : EInftyWeightShift F) (A : Syn) (k : ℕ) (p : ℤ × ℤ) (w : ℤ) :
    ((F.obj ((SyntheticCategory.biShift (0, -(k : ℤ))).obj A)).sequence.ssData
      (p.1, p.2, w - k)).eInfty ≃ₗ[ℤ]
        ((F.obj A).sequence.ssData (p.1, p.2, w)).eInfty := by
  rw [sub_eq_add_neg]
  exact S.iso A (-(k : ℤ)) p w

/-- The E∞ map of the existing λ power, after the specified weight comparison. -/
def lambdaMap (S : EInftyWeightShift F) (A : Syn) (k : ℕ) (p : ℤ × ℤ) (w : ℤ) :
    ((F.obj A).sequence.ssData (p.1, p.2, w)).eInfty →ₗ[ℤ]
      ((F.obj A).sequence.ssData (p.1, p.2, w - k)).eInfty :=
  ((F.functor.map (lambdaPow k A)).eInftyMap (p.1, p.2, w - k)).hom.comp
    (S.lowerIso A k p w).symm.toLinearMap

/-- The finite λ map uses the chosen tower's actual suspended quotient map. -/
def finiteLambdaMap [HasFunctorialCofiber (C := Syn)] (S : EInftyWeightShift F)
    {A : Syn} (T : FiniteLambdaQuotientTower A) (q k : ℕ) (hkq : k < q)
    (p : ℤ × ℤ) (w : ℤ) :
    ((F.obj (XModLambdaN A (q - k))).sequence.ssData (p.1, p.2, w)).eInfty →ₗ[ℤ]
      ((F.obj (XModLambdaN A q)).sequence.ssData (p.1, p.2, w - k)).eInfty :=
  ((F.functor.map (T.lambdaInclusion k q hkq)).eInftyMap (p.1, p.2, w - k)).hom.comp
    (S.lowerIso (XModLambdaN A (q - k)) k p w).symm.toLinearMap

end EInftyWeightShift
end
end KIP126.Synthetic.SpectralSequence
