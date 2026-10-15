module

public import KIP126.Def.AdamsSynthetic.ExtensionLaws.GeneralizedMahowald.Predicates

@[expose] public section

/-! Representatives for the hypotheses of the generalized Mahowald rule.
Each structure records the finite extensions, desuspension, differential or
no-crossing alternatives already present in those hypotheses.
Source: the archived Main/Solution/Tools module in codex/local-backup-20261013. -/
namespace KIP126.Main.ExtensionLaws

open CategoryTheory
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Classical.Adams
open KIP126.Classical.Adams.PageRepresentatives

universe u v w
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w, v} Syn]
  [HasFunctorialCofiber (C := Syn)]
  {H : Mod2EilenbergMacLane (C := C)} {M : MilnorCooperations H}
  (D : AdamsComparison H M Syn)

/-- The hypotheses of the generalized Mahowald rule.

This is only a faithful bundling of the Blueprint hypotheses.  In particular,
it does not choose a quotient representative or a May lift. -/
structure MahowaldHypotheses (T : ClassicalCofiberTriangle D.hopfAndDetector)
    (n m l s t : ℤ) where
  exponent_sum : (normalizedExponent H T.f : ℤ) + normalizedExponent H T.g +
    normalizedExponent H T.h = 1
  triangle : NormalizedTriangleCompatible D.toAdamsComparisonData T exponent_sum
  n_positive : 1 ≤ n - normalizedExponent H T.f
  m_nonnegative : 0 ≤ m - normalizedExponent H T.g
  l_nonnegative : 0 ≤ l - normalizedExponent H T.h
  x : Ambient H (T.X.obj D.hopfAndDetector) (s + l, t + l - 1)
  y : Ambient H (T.Y.obj D.hopfAndDetector) (s + l + n, t + l - 1 + n)
  xBar : Ambient H (T.Z.obj D.hopfAndDetector) (s, t)
  yBar : Ambient H (T.Z.obj D.hopfAndDetector)
    (s + l + n + m, t + l - 1 + n + m)
  suspendedX : Ambient H ((T.X.obj D.hopfAndDetector)⟦(1 : ℤ)⟧) (s + l, t + l)
  x_cycle : IsCycle H (T.X.obj D.hopfAndDetector) (n - normalizedExponent H T.f)
    (s + l, t + l - 1) x
  y_cycle : IsCycle H (T.Y.obj D.hopfAndDetector)
    (m - normalizedExponent H T.g + 1) (s + l + n, t + l - 1 + n) y
  xBar_cycle : IsCycle H (T.Z.obj D.hopfAndDetector) (n + m + l - 1) (s, t) xBar
  yBar_permanent : IsPermanent H (T.Z.obj D.hopfAndDetector)
    (s + l + n + m, t + l - 1 + n + m) yBar
  desuspends : (D.classicalSuspension T.X).DesuspendsClass (s + l) (t + l)
    suspendedX x
  h_extension : FiniteExtension D T.Z (.shift 1 T.X) T.h
    (n + m + l - (m - normalizedExponent H T.g)).toNat l s t xBar suspendedX
  differential : DifferentialAt H (T.Z.obj D.hopfAndDetector) (n + m + l) (s, t)
    (s + l + n + m, t + l - 1 + n + m) xBar yBar
  no_crossing : FiniteExtension.NoCrossing D T.Z (.shift 1 T.X) T.h
      (n + m + l - (m - normalizedExponent H T.g)).toNat l s t ∨
    NoCrossingOn H (T.Z.obj D.hopfAndDetector) (n + m + l)
      (n + m + l - (m - normalizedExponent H T.g)) (s, t)
  g_extension : FiniteExtension D T.Y T.Z T.g
    (m - normalizedExponent H T.g + 2).toNat m (s + l + n) (t + l - 1 + n) y yBar

/-- Chosen witnesses for the two extension hypotheses.

Unlike a bare homotopy class, each field retains the actual finite quotient,
its E∞ representatives, and the `ExtensionEquation` for the normalized map.
The choices are made only from the two corresponding hypotheses in `W`. -/
structure MahowaldExtensionWitnesses (T : ClassicalCofiberTriangle D.hopfAndDetector)
    {n m l s t : ℤ} (W : MahowaldHypotheses D T n m l s t) where
  hWitness : FiniteExtensionWitness D T.Z (.shift 1 T.X) T.h
    (n + m + l - (m - normalizedExponent H T.g)).toNat l s t W.xBar W.suspendedX
  gWitness : FiniteExtensionWitness D T.Y T.Z T.g
    (m - normalizedExponent H T.g + 2).toNat m (s + l + n) (t + l - 1 + n)
    W.y W.yBar

/-- Extract the actual extension witnesses supplied existentially by the
Blueprint hypotheses. -/
noncomputable def MahowaldExtensionWitnesses.choose
    {T : ClassicalCofiberTriangle D.hopfAndDetector} {n m l s t : ℤ}
    (W : MahowaldHypotheses D T n m l s t) :
    MahowaldExtensionWitnesses D T W where
  hWitness := Classical.choice W.h_extension
  gWitness := Classical.choice W.g_extension

/-- The actual raw-cycle witness for the suspension comparison in the
Mahowald hypotheses.  This keeps the two page-two representatives and the
specified layer-level desuspension equality, rather than identifying their
E₂ labels by fiat. -/
structure MahowaldDesuspensionWitness (T : ClassicalCofiberTriangle D.hopfAndDetector)
    {n m l s t : ℤ} (W : MahowaldHypotheses D T n m l s t) where
  suspendedCycle : adamsCycles H.unit (T.X.obj D.hopfAndDetector⟦(1 : ℤ)⟧)
    2 (by decide) (s + l) (t + l)
  sourceCycle : adamsCycles H.unit (T.X.obj D.hopfAndDetector)
    2 (by decide) (s + l) (t + l - 1)
  suspendedClass : KIP126.Classical.Adams.Suspension.classOfSecondCycle H
    ((T.X.obj D.hopfAndDetector)⟦(1 : ℤ)⟧)
    (s + l) (t + l) suspendedCycle = W.suspendedX
  sourceClass : KIP126.Classical.Adams.Suspension.classOfSecondCycle H (T.X.obj D.hopfAndDetector)
    (s + l) (t + l - 1) sourceCycle = W.x
  layer_desuspends : (D.classicalSuspension T.X).desuspendFirstPage
    (s + l) (t + l) suspendedCycle.val = sourceCycle.val

/-- Choose the raw representatives whose existence is asserted by
`DesuspendsClass`. -/
noncomputable def MahowaldDesuspensionWitness.choose
    {T : ClassicalCofiberTriangle D.hopfAndDetector} {n m l s t : ℤ}
    (W : MahowaldHypotheses D T n m l s t) :
    MahowaldDesuspensionWitness D T W := by
  let a := Classical.choose W.desuspends
  let ha := Classical.choose_spec W.desuspends
  let b := Classical.choose ha
  let hb := Classical.choose_spec ha
  exact ⟨a, b, hb.1, hb.2.1, hb.2.2⟩

/-- The actual Adams differential datum used in the Mahowald diagram.
`DifferentialAt` is unpacked here only to retain its page bound and the
underlying spectral-sequence differential separately. -/
structure MahowaldDifferentialWitness (T : ClassicalCofiberTriangle D.hopfAndDetector)
    {n m l s t : ℤ} (W : MahowaldHypotheses D T n m l s t) where
  page_ge_two : 2 ≤ n + m + l
  differential : KIP126.SpectralSequence.HasDifferential
    (adamsTowerInternalSpectralSequence H.unit (T.Z.obj D.hopfAndDetector))
    (n + m + l) (s, t)
    (s + l + n + m, t + l - 1 + n + m) W.xBar W.yBar

/-- Unpack the differential hypothesis without replacing it by a chosen
operation on E₂ labels. -/
def MahowaldDifferentialWitness.ofHypotheses
    {T : ClassicalCofiberTriangle D.hopfAndDetector} {n m l s t : ℤ}
    (W : MahowaldHypotheses D T n m l s t) :
    MahowaldDifferentialWitness D T W :=
  ⟨W.differential.1, W.differential.2⟩


/-- The two distinct no-crossing alternatives allowed by the Mahowald rule.
The classical branch retains the fact that `r'` is a valid page between two
and `r`; it is not a condition on the `g`-extension. -/
inductive MahowaldNoCrossingWitness (D : AdamsComparison H M Syn) (T : ClassicalCofiberTriangle D.hopfAndDetector)
    {n m l s t : ℤ} (W : MahowaldHypotheses D T n m l s t) : Prop where
  | hExtension : FiniteExtension.NoCrossing D T.Z (.shift 1 T.X) T.h
      (n + m + l - (m - normalizedExponent H T.g)).toNat l s t →
      MahowaldNoCrossingWitness D T W
  | classicalDifferential :
      2 ≤ n + m + l - (m - normalizedExponent H T.g) →
      n + m + l - (m - normalizedExponent H T.g) ≤ n + m + l →
      ¬ PageRepresentatives.HasCrossingOn H (T.Z.obj D.hopfAndDetector)
        (n + m + l) (n + m + l - (m - normalizedExponent H T.g)) (s, t) →
      MahowaldNoCrossingWitness D T W

/-- All existing concrete evidence consumed before the synchronization step.
No field asserts the existence of a common quotient representative or of a
May pullback class; those are precisely the next two proof obligations. -/
structure MahowaldRepresentatives (T : ClassicalCofiberTriangle D.hopfAndDetector)
    {n m l s t : ℤ} (W : MahowaldHypotheses D T n m l s t) where
  extensions : MahowaldExtensionWitnesses D T W
  desuspension : MahowaldDesuspensionWitness D T W
  differential : MahowaldDifferentialWitness D T W
  noCrossing : MahowaldNoCrossingWitness D T W

/-- Produce the concrete evidence already contained in the theorem's
hypotheses. -/
noncomputable def MahowaldRepresentatives.ofHypotheses
    {T : ClassicalCofiberTriangle D.hopfAndDetector} {n m l s t : ℤ}
    (W : MahowaldHypotheses D T n m l s t) :
    MahowaldRepresentatives D T W where
  extensions := MahowaldExtensionWitnesses.choose D W
  desuspension := MahowaldDesuspensionWitness.choose D W
  differential := MahowaldDifferentialWitness.ofHypotheses D W
  noCrossing := by
    rcases W.no_crossing with h | h
    · exact .hExtension h
    · exact .classicalDifferential h.1 h.2.1 h.2.2

end KIP126.Main.ExtensionLaws
