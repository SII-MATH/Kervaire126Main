module

public import KIP126.Def.Synthetic.AdamsSequence.Maps.Data
public import KIP126.Def.Synthetic.AdamsFiltration.Data
public import KIP126.Def.ClassicalAdams.TowerNaturality.Page.Data
public import KIP126.Def.Comparison.ClassicalSynthetic.Data

@[expose] public section

/-! Bind a trigraded synthetic family to actual νHF₂ Adams towers.
The fixed-weight sequence has abutment π_(t-s)(Σ^(0,-w) X).
Forward/inverse maps preserve every cycle and boundary, and the differential
square is an equation for these induced page maps, not existential maps. -/
namespace KIP126.Synthetic.SpectralSequence
open CategoryTheory KIP126.StableHomotopy KIP126.Synthetic.Context
open KIP126.SpectralSequence KIP126.Classical.Adams
open KIP126.Comparison.ClassicalSynthetic
universe u v
noncomputable section
variable {Syn : Type u} [SyntheticCategory.{u, v} Syn]
  [HasFunctorialCofiber (C := Syn)] {H : Syn} (unit : S_0_0 ⟶ H)

attribute [local irreducible] adamsTowerSSData

def weightTower (X : Syn) (w : ℤ) :
    KIP126.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ) :=
  adamsTowerInternalSpectralSequence unit ((SyntheticCategory.biShift (0, -w)).obj X)

def weightTowerE2Map {X Y : Syn} (f : X ⟶ Y) (w : ℤ) (p : ℤ × ℤ) :
    ((weightTower unit X w).ssData p).page 0 ⟶ ((weightTower unit Y w).ssData p).page 0 :=
  ModuleCat.ofHom (adamsInternalE2Induced unit ((SyntheticCategory.biShift (0, -w)).map f) p)

-- These are already typed maps.  Checking the comparison fields only needs
-- their endpoints, retaining the same cokernel maps and differentials.
attribute [local irreducible] weightTowerE2Map SSData.page SSDataMorphism.pageMap classicalDifferential fixedWeightDifferential

/-- Structural realization, not BHS's comparison to the *classical* tower.
Both sides here are synthetic νHF₂-based Adams towers. -/
structure TowerPresentation (F : SyntheticAdamsFamily Syn) where
  forward : ∀ (X : Syn) (w : ℤ), SSDataMorphism (ℤ × ℤ)
    (fun p => (F.obj X).sequence.ssData (p.1, p.2, w)) (weightTower unit X w).ssData
  inverse : ∀ (X : Syn) (w : ℤ), SSDataMorphism (ℤ × ℤ) (weightTower unit X w).ssData
    (fun p => (F.obj X).sequence.ssData (p.1, p.2, w))
  left_inv : ∀ (X : Syn) (w : ℤ) (p : ℤ × ℤ),
    (forward X w).φ p ≫ (inverse X w).φ p = 𝟙 _
  right_inv : ∀ (X : Syn) (w : ℤ) (p : ℤ × ℤ),
    (inverse X w).φ p ≫ (forward X w).φ p = 𝟙 _
  comm_d : ∀ (X : Syn) (w r : ℤ) (p : ℤ × ℤ),
    (forward X w).pageMap p (↑(r - 2).toNat : WithTop ℕ) ≫
      classicalDifferential (weightTower unit X w) rfl (fun _ => rfl) r p =
    fixedWeightDifferential (F.obj X) w r p ≫
      (forward X w).pageMap (p + (r, r - 1)) (↑(r - 2).toNat : WithTop ℕ)
  /-- Naturality is anchored to the constructed tower map on E₂. Together
  with preservation of all cycles/boundaries, this pins the later page maps.
  The raw ambient remains the kernel before the initial boundary quotient. -/
  natural_e2 : ∀ {X Y : Syn} (f : X ⟶ Y) (w : ℤ) (p : ℤ × ℤ),
    (F.functor.map f).toSSDataMorphism.pageMap (p.1, p.2, w) 0 ≫ (forward Y w).pageMap p 0 =
      (forward X w).pageMap p 0 ≫ weightTowerE2Map unit f w p
end
end KIP126.Synthetic.SpectralSequence
