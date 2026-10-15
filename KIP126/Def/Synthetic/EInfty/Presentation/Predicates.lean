module

public import KIP126.Def.Synthetic.EInfty.Presentation.Data
public import KIP126.Def.Synthetic.EInfty.Shift.Predicates

@[expose] public section

namespace KIP126.Synthetic.SpectralSequence
open CategoryTheory KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Synthetic.Context KIP126.Classical.Adams.PageRepresentatives
universe u v w
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w, v} Syn] [HasFunctorialCofiber (C := Syn)]
  (H : Mod2EilenbergMacLane (C := C)) (N : NuFunctorData C Syn)
  (F : SyntheticAdamsFamily Syn)

/-- E∞ 比较的映射相容性，明确比较同一 F 的 λ 与 ρ 映射和保持 E₂
代表元标签的规范商映射／包含映射。这里只在相应非零窗口写公式；窗口外
的零性由全 weight presentation 本身决定，不用错误的“负 weight 全消失”。
它没有声称由任意一族线性等价就能推出这些公式。 -/
structure SyntheticEInftyMapCompatibility
    (P : SyntheticEInftyPresentation H N F) (S : EInftyWeightShift F)
    (T : ∀ X : C, FiniteLambdaQuotientTower (N.functor.obj X)) : Prop where
  shift_natural : S.Natural
  lambda_nu : ∀ (X : C) (k : ℕ) (p : ℤ × ℤ) (w : ℤ) (hw : w ≤ p.2)
    (x : ((F.nu N X).sequence.ssData (p.1, p.2, w)).eInfty),
    P.nuWindow X p (w - k) (by omega) (S.lambdaMap (N.functor.obj X) k p w x) =
      permanentQuotientMap H X (by omega) p (P.nuWindow X p w hw x)
  lambda_finite : ∀ (X : C) (q k : ℕ) (hkq : k < q) (p : ℤ × ℤ) (w : ℤ)
    (hw : 0 ≤ p.2 - w ∧ p.2 - w < (q - k : ℕ))
    (x : ((F.nuQuotient N X (q - k)).sequence.ssData (p.1, p.2, w)).eInfty),
    P.finiteWindow X q (by omega) p (w - k) (by constructor <;> omega)
        (S.finiteLambdaMap (T X) q k hkq p w x) =
      quotientMap H X (by omega) (by omega) p
        (P.finiteWindow X (q - k) (by omega) p w hw x)
  rho_finite : ∀ (X : C) (i j : ℕ) (hi : 0 < i) (hij : i ≤ j)
    (p : ℤ × ℤ) (w : ℤ) (hw : 0 ≤ p.2 - w ∧ p.2 - w < i)
    (x : ((F.nuQuotient N X j).sequence.ssData (p.1, p.2, w)).eInfty),
    P.finiteWindow X i hi p w hw
        (((F.functor.map ((T X).rho i j hij)).eInftyMap (p.1, p.2, w)).hom x) =
      quotientMap H X (by omega) (le_refl (1 + p.2 - w)) p
        (P.finiteWindow X j (by omega) p w (by constructor <;> omega) x)
  rho_nu : ∀ (X : C) (q : ℕ) (hq : 0 < q) (p : ℤ × ℤ) (w : ℤ)
    (hw : 0 ≤ p.2 - w ∧ p.2 - w < q)
    (x : ((F.nu N X).sequence.ssData (p.1, p.2, w)).eInfty),
    P.finiteWindow X q hq p w hw
        (((F.quotientProjection (N.functor.obj X) q).eInftyMap (p.1, p.2, w)).hom x) =
      permanentToFinite H X (q - p.2 + w) (1 + p.2 - w) p
        (P.nuWindow X p w (by omega) x)

end KIP126.Synthetic.SpectralSequence
