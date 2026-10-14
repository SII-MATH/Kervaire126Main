module

public import KIP126.Def.AdamsSynthetic

/-! Consumers accept one coherent system; none constructs a concrete model. -/
open CategoryTheory KIP126.StableHomotopy KIP126.Synthetic.Context
open KIP126.Synthetic.SpectralSequence KIP126.AdamsSynthetic
universe u v
noncomputable section
variable {Syn : Type u} [SyntheticCategory.{u,v} Syn]
  [HasFunctorialCofiber (C := Syn)] {H : Syn} {unit : S_0_0 ⟶ H}
  {F : SyntheticAdamsFamily Syn} (P : SyntheticTowerPresentation unit F)
  {X Y : Syn} (c : SyntheticTowerConvergence P X) (i : Tridegree)

example : SyntheticCanonicalIdentification P X c.identification := c.canonical

example (s m w : ℤ) (a : BiHom m w X) :
    FiltrationAtLeast P s a ↔
      ∃ b : BiHom m w ((P.tower X).stageAt s),
        b ≫ (P.tower X).projection s = a := Iff.rfl

example (f : X ⟶ Y) (p : ℤ × ℤ) (a : BiHom p.1 p.2 X) :
    syntheticHomotopyMap f p a = a ≫ f := rfl

example (x : (F.obj X).E₂ i) (a : BiHom (i.2.1-i.1) i.2.2 X)
    (h : DetectsNonzero c i x a) : Detects c i x a := h.1

example (a : BiHom (i.2.1-i.1) i.2.2 X) (h : Detects c i 0 a) :
    FiltrationAtLeast P (i.1+1) a := detects_zero_filtration c i h

example (x : (F.obj X).E₂ i) (a b : BiHom (i.2.1-i.1) i.2.2 X)
    (ha : Detects c i x a) (hb : Detects c i x b) :
    FiltrationAtLeast P (i.1+1) (a-b) := detects_sub_filtration c i ha hb

example (x : (F.obj X).E₂ i) (e e' : ((F.obj X).sequence.ssData i).eInfty)
    (h : HasInfinityRepresentative (F.obj X) 2 i x e)
    (h' : HasInfinityRepresentative (F.obj X) 2 i x e') : e=e' := h.unique h'

/-- A proof about another canonical identification cannot be substituted. -/
example (Q : SyntheticTowerPresentation unit F) (_d : SyntheticTowerConvergence Q X)
    (x : (F.obj X).E₂ i) (a : BiHom (i.2.1-i.1) i.2.2 X)
    (_h : Detects c i x a) : True := by
  fail_if_success have : Detects _d i x a := _h
  trivial

/-- Zero-leading detection carries no nonvanishing proof. -/
example (a : BiHom (i.2.1-i.1) i.2.2 X) (_h : Detects c i 0 a) : True := by
  fail_if_success have : DetectsNonzero c i 0 a := _h
  trivial

/-- Separation remains an additional mathematical obligation. -/
example : True := by
  fail_if_success exact (show HomotopySeparated P X from c)
  trivial
/-- A zero-length extension follows the actual map on the same infinity page. -/
example (d : SyntheticTowerConvergence P Y) (g : X ⟶ Y)
    (M : ConvergentMap F g c.toConvergence d.toConvergence)
    (x : ((F.obj X).sequence.ssData i).eInfty) :
    M.ExtensionEquation (i.2.1-i.1,i.2.2) i.1 0 rfl
      (by simp [SyntheticTowerConvergence.toConvergence])
      (elementMap x) (elementMap x ≫ (F.map g).eInftyMap i) :=
  M.extensionEquation_zero i (elementMap x)
end
