module

public import KIP126.AdamsSynthetic.AdamsFiltration
public import Mathlib.Algebra.Exact.Basic
public import Mathlib.Data.Finset.Prod

@[expose] section

namespace KIP126.AdamsSynthetic
open CategoryTheory CategoryTheory.Limits MonoidalCategory Pretriangulated
open KIP126.StableHomotopy
universe u v
noncomputable section
variable {C : Type u} [StableHomotopyCategory.{u,v} C]

/-- The boundary is induced by this triangle's actual connecting arrow and
this coefficient/shift comparison. It is not a freely chosen linear map. -/
public def modTwoConnecting (H : ModTwoCoefficients C)
    (shiftIso : ∀ X : C, H.object ⊗ X⟦(1 : ℤ)⟧ ≅ (H.object ⊗ X)⟦(1 : ℤ)⟧)
    (T : HoCofiberSequence (C := C)) (i : ℤ) :
    ModTwoHomology H i T.Z →+ ModTwoHomology H (i-1) T.X :=
  (AbstractAdamsTower.desuspend (H.object ⊗ T.X) i).comp
    (inducedMap (H.object ◁ T.h ≫ (shiftIso T.X).hom) i)

/-- Exactness on the same HF₂ homology and actual distinguished triangle.
The cardinality bound is proved below rather than duplicated as an input. -/
public structure ModTwoHomologyExactness (H : ModTwoCoefficients C) where
  shiftIso : ∀ X : C, H.object ⊗ X⟦(1 : ℤ)⟧ ≅ (H.object ⊗ X)⟦(1 : ℤ)⟧
  exact : ∀ (T : HoCofiberSequence (C := C)) (i : ℤ),
    Function.Exact (modTwoHomologyMap H T.g i) (modTwoConnecting H shiftIso T i)

private def exactEmbedding {A B D : Type*} [AddCommGroup A] [AddCommGroup B]
    [AddCommGroup D] (f : A →+ B) (g : B →+ D) (h : Function.Exact f g) : B ↪ A × D := by
  classical
  let sectionMap : Set.range g → B := fun y => Classical.choose y.property
  have section_eq (y : Set.range g) : g (sectionMap y) = y.val :=
    Classical.choose_spec y.property
  let rep (b : B) := sectionMap ⟨g b, b, rfl⟩
  have hrep (b : B) : g (rep b) = g b := section_eq _
  have preimage (b : B) : ∃ a : A, f a = b - rep b :=
    (h (b - rep b)).mp (by rw [map_sub, hrep, sub_self])
  let lift (b : B) := Classical.choose (preimage b)
  have hlift (b : B) : f (lift b) = b - rep b := Classical.choose_spec (preimage b)
  refine ⟨fun b => (lift b, g b), ?_⟩
  intro b b' heq
  have hl : lift b = lift b' := congrArg Prod.fst heq
  have hg : g b = g b' := congrArg Prod.snd heq
  have hr : rep b = rep b' := congrArg sectionMap (Subtype.ext hg)
  calc
    b = f (lift b) + rep b := (eq_sub_iff_add_eq.mp (hlift b)).symm
    _ = f (lift b') + rep b' := by rw [hl, hr]
    _ = b' := eq_sub_iff_add_eq.mp (hlift b')

private theorem exact_card_bound {A B D : Type*} [AddCommGroup A] [AddCommGroup B]
    [AddCommGroup D] (f : A →+ B) (g : B →+ D) (h : Function.Exact f g)
    (nA nD : ℕ) (hA : ∀ S : Finset A, S.card ≤ nA)
    (hD : ∀ S : Finset D, S.card ≤ nD) (S : Finset B) : S.card ≤ nA * nD := by
  classical
  let T := S.map (exactEmbedding f g h)
  have hsub : T ⊆ (T.image Prod.fst) ×ˢ (T.image Prod.snd) := by
    intro b hb
    exact Finset.mem_product.mpr
      ⟨Finset.mem_image.mpr ⟨b,hb,rfl⟩, Finset.mem_image.mpr ⟨b,hb,rfl⟩⟩
  calc
    S.card = T.card := (Finset.card_map _).symm
    _ ≤ ((T.image Prod.fst) ×ˢ (T.image Prod.snd)).card := Finset.card_le_card hsub
    _ = (T.image Prod.fst).card * (T.image Prod.snd).card := Finset.card_product _ _
    _ ≤ nA * nD := Nat.mul_le_mul (hA _) (hD _)

/-- Correct cardinality version of the old cofiber bound. Cardinalities
multiply; an additive bound would instead concern vector-space dimensions. -/
public theorem ModTwoHomologyExactness.cofiber_card_bound
    {H : ModTwoCoefficients C} (E : ModTwoHomologyExactness H)
    (T : HoCofiberSequence (C := C)) (i : ℤ) (nX nY : ℕ)
    (hX : ∀ S : Finset (ModTwoHomology H (i-1) T.X), S.card ≤ nX)
    (hY : ∀ S : Finset (ModTwoHomology H i T.Y), S.card ≤ nY) :
    ∀ S : Finset (ModTwoHomology H i T.Z), S.card ≤ nX * nY := by
  intro S
  simpa [Nat.mul_comm] using exact_card_bound
    (modTwoHomologyMap H T.g i) (modTwoConnecting H E.shiftIso T i)
    (E.exact T i) nY nX hY hX S

end
end KIP126.AdamsSynthetic
