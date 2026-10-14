module

public import KIP126.Def.AdamsSynthetic.MappingComposition
public import KIP126.Def.Literature.Toda
import all KIP126.Def.Literature.Toda

/-! The general mapping-spectrum Moss contract, with the preceding-page
defining systems used in MainPaper 2537–2545. Fixed source:
bbac1fc05843bdf2d56057e6114a38839e939378, `Def/ClassicalAdams/Moss`.
All pages, products, tower filtrations and represented stable maps below
belong to one supplied mapping system. This is an explicit theorem delivery
obligation; applicability to Moss (1970), Theorem 1.2 still requires the source
comparison. It is not inferred from arbitrary triangulated-category axioms. -/

@[expose] section
namespace KIP126.Literature.Moss
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open KIP126.StableHomotopy KIP126.AdamsSynthetic KIP126.Classical.Adams
open KIP126.Core.SpectralSequence
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {C : Type u} [StableHomotopyCategory.{u,v} C]
  [HasFunctorialCofiber (C := C)] {H : C} {unit : SphereSpectrum ⟶ H}
  {A : ClassicalAdamsFamily C} {B : ClosedSymmetricTensorTriangulated C}
  {P : ClassicalTowerPresentation unit A} {scope : C → Prop}
  (S : MappingSpectrumSystem B P scope)

public def stem (k : ℤ × ℤ) : ℤ := k.2-k.1

public abbrev sequence (X Y : MappingObject scope) := S.sequence X.val Y.val

public abbrev abutment (X Y : MappingObject scope) (n : ℤ) :=
  HomotopyGroup n (mappingSpectrum B X.val Y.val)

/-- Reindexing by equality, with no independently chosen page map. -/
public def pageCast (X Y : MappingObject scope) {r r' : ℤ} {i i' : ℤ × ℤ}
    (hr : r = r') (hi : i = i') (x : (sequence S X Y).Page r i) :
    (sequence S X Y).Page r' i' := by
  subst r'; subst i'; exact x

namespace PageMassey
public def degree (r : ℤ) (i j k : ℤ × ℤ) : ℤ × ℤ :=
  i+j+k-(r-1,r-2)

public def definingDifferential (X Y : MappingObject scope) (r : ℤ) (i j : ℤ × ℤ)
    (y : (sequence S X Y).Page r (i+j-(r,r-1))) :
    (sequence S X Y).Page r (i+j) :=
  pageCast S X Y rfl (by
    change i+j-(r,r-1)+(A.obj (mappingSpectrum B X.val Y.val)).diffDeg r = i+j
    rw [A.differentialDegree]
    abel) ((sequence S X Y).d r _ y)

public def precedingDifferential (X Y : MappingObject scope) (r : ℤ) (i j : ℤ × ℤ)
    (y : (sequence S X Y).Page (r-1) (i+j-(r-1,r-2))) :
    (sequence S X Y).Page (r-1) (i+j) :=
  definingDifferential S X Y (r-1) i j
    (pageCast S X Y rfl (by congr 2; omega) y)

/-- One common next-cycle representative, in the actual successor quotient. -/
public def Passage (X Y : MappingObject scope) (r : ℤ) (k : ℤ × ℤ)
    (a : (sequence S X Y).Page (r-1) k) (b : (sequence S X Y).Page r k) : Prop :=
  NextPageRelation (sequence S X Y) (r-1) k a
    (pageCast S X Y (by omega) rfl b)

variable (M : MappingComposition S)

/-- The signed defining value `yc - (-1)^(stem a) az` on E_(r-1). -/
public def definingValue (W X Y Z : MappingObject scope) (r : ℤ) (i j k : ℤ × ℤ)
    (a : (sequence S W X).Page (r-1) i) (c : (sequence S Y Z).Page (r-1) k)
    (y : (sequence S W Y).Page (r-1) (i+j-(r-1,r-2)))
    (z : (sequence S X Z).Page (r-1) (j+k-(r-1,r-2))) :
    (sequence S W Z).Page (r-1) (degree r i j k) :=
  let left := pageCast S W Z rfl (by unfold degree; abel)
    ((M.pairing W Y Z).ssPairing.pair (r-1) (i+j-(r-1,r-2)) k y c)
  let right := pageCast S W Z rfl (by unfold degree; abel)
    ((M.pairing W X Z).ssPairing.pair (r-1) i (j+k-(r-1,r-2)) a z)
  if Even (stem i) then left-right else left+right

/-- A complete preceding-page defining system. This does not substitute an
arbitrary ternary relation, or define the separate E₂ cobar Massey product. -/
public def Relation (r : ℤ) (_hr : 3 ≤ r) {W X Y Z : MappingObject scope}
    {i j k : ℤ × ℤ} (x : (sequence S W Z).Page r (degree r i j k))
    (a : (sequence S W X).Page r i) (b : (sequence S X Y).Page r j)
    (c : (sequence S Y Z).Page r k) : Prop :=
  ∃ (a' : (sequence S W X).Page (r-1) i)
    (b' : (sequence S X Y).Page (r-1) j) (c' : (sequence S Y Z).Page (r-1) k)
    (y : (sequence S W Y).Page (r-1) (i+j-(r-1,r-2)))
    (z : (sequence S X Z).Page (r-1) (j+k-(r-1,r-2))),
    Passage S W X r i a' a ∧ Passage S X Y r j b' b ∧ Passage S Y Z r k c' c ∧
    precedingDifferential S W Y r i j y = (M.pairing W X Y).ssPairing.pair (r-1) i j a' b' ∧
    precedingDifferential S X Z r j k z = (M.pairing X Y Z).ssPairing.pair (r-1) j k b' c' ∧
    Passage S W Z r (degree r i j k) (definingValue S M W X Y Z r i j k a' c' y z) x

/-- Full additive indeterminacy, with both free summands and their degrees. -/
public def Indeterminacy (r : ℤ) {W X Y Z : MappingObject scope} {i j k : ℤ × ℤ}
    (a : (sequence S W X).Page r i) (c : (sequence S Y Z).Page r k)
    (z : (sequence S W Z).Page r (degree r i j k)) : Prop :=
  ∃ (u : (sequence S W Y).Page r (i+j-(r-1,r-2)))
    (v : (sequence S X Z).Page r (j+k-(r-1,r-2))),
    z = pageCast S W Z rfl (by unfold degree; abel)
      ((M.pairing W Y Z).ssPairing.pair r (i+j-(r-1,r-2)) k u c) +
      pageCast S W Z rfl (by unfold degree; abel)
      ((M.pairing W X Z).ssPairing.pair r i (j+k-(r-1,r-2)) a v)
end PageMassey

/-- Residual injectivity in the actual mapping Adams tower. An associated
graded convergence isomorphism alone does not imply this condition. -/
public def WeakConvergence (X Y : MappingObject scope) : Prop :=
  let T := P.tower (mappingSpectrum B X.val Y.val)
  ∀ (s : ℕ) (n : ℤ) (f : HomotopyGroup n (T.stage (s+1))),
    (∀ (t : ℕ) (hst : s+1 ≤ t), ∃ g : HomotopyGroup n (T.stage t), g ≫ T.map hst = f) →
    f ≫ T.map (Nat.le_succ s) = 0 → f = 0

public def crossingSourceDegree (k : ℤ × ℤ) (q : ℤ) : ℤ × ℤ :=
  (q,q+stem k+1)

/-- Moss-direction crossing, distinct from extension-sequence crossings. -/
public def HasMossCrossing (X Y : MappingObject scope) (r : ℤ) (k : ℤ × ℤ) : Prop :=
  ∃ m q : ℤ, r < m ∧ 0 ≤ q ∧ q < k.1-(r-1) ∧ k.1 < q+m ∧
    (sequence S X Y).d m (crossingSourceDegree k q) ≠ 0

public def NoMossCrossingForProducts (W X Y Z : MappingObject scope)
    (r : ℤ) (i j k : ℤ × ℤ) : Prop :=
  ¬ HasMossCrossing S W Y r (i+j) ∧ ¬ HasMossCrossing S X Z r (j+k)

/-- A finite and infinite class from one actual Z∞ representative. -/
public def HasEInftyClass (X Y : MappingObject scope) (r : ℤ) (k : ℤ × ℤ)
    (x : (sequence S X Y).Page r k) (e : ((sequence S X Y).ssData k).eInfty) : Prop :=
  ∃ z : InfiniteCycles (sequence S X Y) k,
    infinityToPage (sequence S X Y) r k z = x ∧ ((sequence S X Y).ssData k).pageπ ⊤ z = e

/-- Permanence here allows zero, as in the source Moss statement. -/
public def PermanentCycle (X Y : MappingObject scope) (r : ℤ) (k : ℤ × ℤ)
    (x : (sequence S X Y).Page r k) : Prop := ∃ e, HasEInftyClass S X Y r k x e

/-- Detection through the same tower's filtration and convergence. -/
public def DetectsAbutment (X Y : MappingObject scope) (r : ℤ) (k : ℤ × ℤ)
    (x : (sequence S X Y).Page r k) (α : abutment (B := B) X Y (stem k)) : Prop :=
  ∃ e, HasEInftyClass S X Y r k x e ∧
    ∃ a : (Subobject.underlying.obj
      ((P.tower (mappingSpectrum B X.val Y.val)).filtration.F k.1 (stem k)) : ModuleCat ℤ),
      ((P.tower (mappingSpectrum B X.val Y.val)).filtration.F k.1 (stem k)).arrow a = α ∧
      ((S.convergence X.val Y.val X.property Y.property).identification k).hom e =
        (P.tower (mappingSpectrum B X.val Y.val)).filtration.toAssociatedGraded k.1 (stem k) a

public def abutmentMap (X Y : MappingObject scope) (k : ℤ × ℤ)
    (a : abutment (B := B) X Y (stem k)) : X.val⟦stem k⟧ ⟶ Y.val :=
  mappingHomotopyEquiv B (stem k) X.val Y.val a

public def shiftMap (X Y : MappingObject scope) (k : ℤ × ℤ) (n : ℤ)
    (a : abutment (B := B) X Y (stem k)) : X.val⟦stem k+n⟧ ⟶ Y.val⟦n⟧ :=
  (shiftFunctorAdd C (stem k) n).hom.app X.val ≫
    (shiftFunctor C n).map (abutmentMap X Y k a)

/-- The actual stable composite, transported through the fixed adjunction. -/
public def abutmentComposition (X Y Z : MappingObject scope) (i j : ℤ × ℤ)
    (a : abutment (B := B) X Y (stem i)) (b : abutment (B := B) Y Z (stem j)) :
    abutment (B := B) X Z (stem (i+j)) :=
  (mappingHomotopyEquiv B (stem (i+j)) X.val Z.val).symm
    (eqToHom (congrArg (fun n : ℤ => X.val⟦n⟧) (by
      dsimp [stem]; omega : stem (i+j) = stem i+stem j)) ≫
      shiftMap X Y i (stem j) a ≫ abutmentMap Y Z j b)

public def todaMap (r : ℤ) (W Z : MappingObject scope) (i j k : ℤ × ℤ)
    (a : abutment (B := B) W Z (stem (PageMassey.degree r i j k))) :
    (W.val⟦stem i+(stem j+stem k)⟧)⟦(1 : ℤ)⟧ ⟶ Z.val :=
  (shiftFunctorAdd C (stem i+(stem j+stem k)) 1).inv.app W.val ≫
    eqToHom (congrArg (fun n : ℤ => W.val⟦n⟧) (by
      dsimp [stem, PageMassey.degree]; omega : stem i+(stem j+stem k)+1 =
        stem (PageMassey.degree r i j k))) ≫
      abutmentMap W Z (PageMassey.degree r i j k) a

variable (M : MappingComposition S)

/-- The finite-page detection compatibility appearing in the original Moss
hypotheses. All products and targets are already fixed by S and M. -/
public def DetectionCompatible : Prop :=
  ∀ (X Y Z : MappingObject scope) (r : ℤ) (_hr : 2 ≤ r) (i j : ℤ × ℤ)
    (a : (sequence S X Y).Page r i) (b : (sequence S Y Z).Page r j)
    (α : abutment (B := B) X Y (stem i)) (β : abutment (B := B) Y Z (stem j)),
    DetectsAbutment S X Y r i a α → DetectsAbutment S Y Z r j b β →
    DetectsAbutment S X Z r (i+j) ((M.pairing X Y Z).ssPairing.pair r i j a b)
      (abutmentComposition X Y Z i j α β)

/-- General Moss implication. Both product-tower weak-convergence premises,
both noncrossing ranges, actual zero composites and full defining systems
are retained. Only existence of some surviving Massey member is asserted. -/
public def StatementAt (W X Y Z : MappingObject scope) : Prop :=
  ∀ (r : ℤ) (hr : 3 ≤ r) (i j k : ℤ × ℤ),
    WeakConvergence (P := P) (B := B) W Y → WeakConvergence (P := P) (B := B) X Z →
    ∀ (a : (sequence S W X).Page r i) (b : (sequence S X Y).Page r j)
      (c : (sequence S Y Z).Page r k)
      (α : abutment (B := B) W X (stem i)) (β : abutment (B := B) X Y (stem j))
      (γ : abutment (B := B) Y Z (stem k)),
    let f := shiftMap W X i (stem j+stem k) α
    let g := shiftMap X Y j (stem k) β
    let h := abutmentMap Y Z k γ
    DetectsAbutment S W X r i a α → DetectsAbutment S X Y r j b β →
    DetectsAbutment S Y Z r k c γ →
    (M.pairing W X Y).ssPairing.pair r i j a b = 0 →
    (M.pairing X Y Z).ssPairing.pair r j k b c = 0 →
    f ≫ g = 0 → g ≫ h = 0 → NoMossCrossingForProducts S W X Y Z r i j k →
    ∃ (x : (sequence S W Z).Page r (PageMassey.degree r i j k))
      (ξ : abutment (B := B) W Z (stem (PageMassey.degree r i j k))),
      PageMassey.Relation S M r hr x a b c ∧
      PermanentCycle S W Z r (PageMassey.degree r i j k) x ∧
      DetectsAbutment S W Z r (PageMassey.degree r i j k) x ξ ∧
      KIP126.StableHomotopy.Toda.Relation (todaMap r W Z i j k ξ) f g h

/-- The literature delivery contract for this object scope. Scope identity
(for example finite spectra) and comparison with the source model are producer
obligations. This definition neither supplies an inhabitant nor removes them. -/
public def Statement : Prop :=
  DetectionCompatible S M → ∀ W X Y Z, StatementAt S M W X Y Z

/-- Model-side delivery for Moss. The complete coset law is an obligation
on the defined Massey relation; it does not replace that relation with a
chosen operation or discard either indeterminacy summand. The generic
pairing already contains signed Leibniz, successor compatibility and
associativity, so no duplicate coherence structure is selected here. -/
private structure Context where
  composition : MappingComposition S
  weak_convergence : ∀ X Y : MappingObject scope, WeakConvergence (P := P) (B := B) X Y
  detection : DetectionCompatible S composition
  indeterminacy : ∀ (r : ℤ) (hr : 3 ≤ r) (W X Y Z : MappingObject scope) (i j k : ℤ × ℤ)
    (a : (sequence S W X).Page r i) (b : (sequence S X Y).Page r j)
    (c : (sequence S Y Z).Page r k)
    (x₀ x : (sequence S W Z).Page r (PageMassey.degree r i j k)),
    PageMassey.Relation S composition r hr x₀ a b c →
      (PageMassey.Relation S composition r hr x a b c ↔
        PageMassey.Indeterminacy S composition r (j := j) a c (x-x₀))

/-- The external theorem is separate from the internal mapping context.
Its source-to-model comparison is required of a producer supplying it. -/
private def SourceResults (Q : Context S) : Prop := Statement S Q.composition

/-- Consume the source theorem on exactly the context's fixed data. -/
private theorem SourceResults.at {Q : Context S} (h : SourceResults S Q)
    (W X Y Z : MappingObject scope) : StatementAt S Q.composition W X Y Z :=
  h Q.detection W X Y Z

end
end KIP126.Literature.Moss
