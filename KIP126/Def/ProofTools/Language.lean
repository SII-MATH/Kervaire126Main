module

public import KIP126.Def.Literature

/-! Actual page labels and crossing predicates for the paper's reusable tools.
Adapted from PageRepresentatives/Predicates and Route/Extensions at
bbac1fc05843 (MIT; see the retained source LICENSE); all operations refer to the same given model. -/

@[expose] section
namespace KIP126.ProofTools
noncomputable section
open CategoryTheory KIP126.StableHomotopy KIP126.Synthetic.Context
open KIP126.Synthetic.SpectralSequence KIP126.Classical.Adams KIP126.AdamsSynthetic
open KIP126.Core.SpectralSequence KIP126.Kervaire.Route
universe u v w
variable {C : Type u} [StableHomotopyCategory.{u,v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w,v} Syn]
  [HasFunctorialCofiber (C := Syn)] (D : Model C Syn)

public abbrev Ambient (X : ClassicalObject) (p : ℤ × ℤ) :=
  (D.classical.obj (X.obj D.auxiliary)).Page 2 p

variable (X : ClassicalObject)

/-- Membership in paper Z_c, with its valid index range explicit. -/
public def IsCycle (level : ℤ) (p : ℤ × ℤ) (x : Ambient D X p) : Prop :=
  1 ≤ level ∧ x ∈ KIP126.Literature.cycles D X level p

/-- Membership in paper B_c; this does not assert a nonzero incoming hit. -/
public def IsBoundary (level : ℤ) (p : ℤ × ℤ) (x : Ambient D X p) : Prop :=
  1 ≤ level ∧ x ∈ KIP126.Literature.boundaries D X level p

/-- A common infinite-cycle representative, allowing the zero class. -/
public def IsPermanent (p : ℤ × ℤ) (x : Ambient D X p) : Prop :=
  x ∈ KIP126.Literature.permanentCycles D X p

/-- Equality modulo the actual paper boundary submodule. -/
public def Congruent (level : ℤ) (p : ℤ × ℤ) (x y : Ambient D X p) : Prop :=
  IsBoundary D X level p (x - y)

/-- The actual Adams differential on common E₂ labels, with the degree
transport checked by `HasDifferential`. It is never a freely chosen operation. -/
public def DifferentialAt (r : ℤ) (p q : ℤ × ℤ)
    (x : Ambient D X p) (y : Ambient D X q) : Prop :=
  2 ≤ r ∧ KIP126.Core.SpectralSequence.HasDifferential
    (D.classical.obj (X.obj D.auxiliary)) r p q x y

/-- MainPaper Definition `classicalcrossdiff`: a crossing of a length-r
Adams differential beginning at p, viewed on page `page`. Its witness is an
essential differential in the actual Adams sequence, with the same stems.
This is distinct from the direction used in Moss's theorem. -/
public def HasCrossingOn (r page : ℤ) (p : ℤ × ℤ) : Prop :=
  ∃ a b : ℤ, 0 < a ∧ a ≤ page - 2 ∧ 0 ≤ b ∧ b ≤ r - page ∧
    ∃ (x : Ambient D X (p.1 + a, p.2 + a))
      (y : Ambient D X (p.1 + r - b, p.2 + r - b - 1)),
      KIP126.Core.SpectralSequence.HasNonzeroDifferential
        (D.classical.obj (X.obj D.auxiliary)) (r - a - b)
        (p.1 + a, p.2 + a) (p.1 + r - b, p.2 + r - b - 1) x y

/-- Absence of paper-direction crossings in the stated, valid page range. -/
public def NoCrossingOn (r page : ℤ) (p : ℤ × ℤ) : Prop :=
  2 ≤ page ∧ page ≤ r ∧ ¬ HasCrossingOn D X r page p


variable (X Y : ClassicalObject) (f : X.obj D.auxiliary ⟶ Y.obj D.auxiliary)

/-- A crossing in the finite page-extension position `(r,n,s,t)`.
The target degree is written as the actual shorter witness's target;
it is `(s+n-b,t+n-b)`. Its source and target cycle conditions are supplied
by that same witness, on page r-a and of length n-a-b. -/
public def FiniteHasCrossing
    (r : ℕ) (n s t : ℤ) : Prop :=
  ∃ a b : ℕ, 0 < a ∧ a ≤ r - 2 ∧
    (b : ℤ) ≤ n - a - normalizedExponent D.classicalTower f ∧
    ∃ (x' : Ambient D X (s + a, t + a))
      (y' : Ambient D Y
        (s + a + (n - a - b), t + a + (n - a - b))),
      ∃ W' : FiniteExtensionWitness D X Y f (r - a) (n - a - b) (s + a) (t + a) x' y',
        W'.Essential ∧ y' ∉ KIP126.Literature.boundaries D Y
          (1 + n - b - normalizedExponent D.classicalTower f)
          (s + a + (n - a - b), t + a + (n - a - b))

/-- Absence of crossings in this finite position. Applied to an actual
extension witness, its page and length validity are already supplied. -/
public def FiniteNoCrossing
    (r : ℕ) (n s t : ℤ) : Prop :=
  ¬ FiniteHasCrossing D X Y f r n s t

/-- The infinite clause uses the same untruncated normalized map and actual
permanent representatives. The bound a≤n-e follows from the length range,
and is recorded explicitly; there is no finite-page upper bound on a. -/
public def InfiniteHasCrossing
    (n s t : ℤ) : Prop :=
  ∃ a b : ℕ, 0 < a ∧ (a : ℤ) ≤ n - normalizedExponent D.classicalTower f ∧
    (b : ℤ) ≤ n - a - normalizedExponent D.classicalTower f ∧
    ∃ (x' : Ambient D X (s + a, t + a))
      (y' : Ambient D Y
        (s + a + (n - a - b), t + a + (n - a - b))),
      ∃ W' : InfiniteExtensionWitness D X Y f (n - a - b) (s + a) (t + a) x' y',
        W'.Essential ∧ y' ∉ KIP126.Literature.boundaries D Y
          (1 + n - b - normalizedExponent D.classicalTower f)
          (s + a + (n - a - b), t + a + (n - a - b))

public def InfiniteNoCrossing
    (n s t : ℤ) : Prop :=
  ¬ InfiniteHasCrossing D X Y f n s t


/-- 有限 stretching 的障碍候选，直接在同一个早期 λ 商的实际 ESS 中定义。
源和靶的 synthetic weight 固定为原 extension 的 `t + e(f)`，而源的
filtration 提高 `a`。源必须不在后期商到早期商的实际 `ρ` 所诱导的
`E∞` 映射像中；这与某个普通 Adams 代表元不属于后页 cycle 层不同。
允许 `b = 0` 及长度 `n - a - b = 0` 的 synthetic extension，包括
`e(f) = 1` 的情形。要求同商中实际 extension equation 的靶非零，不要求
essential 性，不换成较小 λ 商的 extension，也不额外施加普通 Adams
boundary 排除条件。排除这些候选强于仅排除 essential crossings；这是
修复后的充分条件，不声称与原普通 Adams 代表元谓词等价。 -/
public def FiniteExtensionNonliftableCrossing
    (rEarlier rLater : ℕ) (n s t : ℤ) : Prop :=
  ∃ hle : rEarlier ≤ rLater, ∃ a b : ℕ,
    0 < a ∧ a ≤ rEarlier - 2 ∧ (a : ℤ) + b ≤ n ∧
    ∃ (source : ((D.family.obj ((SyntheticObject.quotient (rEarlier - 1)
          (extensionSourceObject D X Y f)).obj D.nu D.auxiliary)).sequence.ssData
          (s + a, (t - s) + (s + a), t + normalizedExponent D.classicalTower f)).eInfty)
      (target : ((D.family.obj ((SyntheticObject.quotient (rEarlier - 1)
          (.nu Y)).obj D.nu D.auxiliary)).sequence.ssData
          (s + a + (n - a - b), (t - s) + (s + a + (n - a - b)),
            t + normalizedExponent D.classicalTower f)).eInfty),
      source ∉ Set.range (((D.family.functor.map
        ((D.quotients.tower ((extensionSourceObject D X Y f).obj D.nu D.auxiliary)).rho
          (rEarlier - 1) (rLater - 1) (Nat.sub_le_sub_right hle 1))).eInftyMap
            (s + a, (t - s) + (s + a), t + normalizedExponent D.classicalTower f)).hom) ∧
      TowerExtensionEquation (D.convergentMap
        (.quotient (rEarlier - 1) (extensionSourceObject D X Y f))
        (.quotient (rEarlier - 1) (.nu Y))
        (finiteExtensionMap D X Y f (rEarlier - 1)))
        (t - s, t + normalizedExponent D.classicalTower f) (s + a) (n - a - b) source target ∧
      target ≠ 0


end
end KIP126.ProofTools
