module

public import KIP126.Def.StableHomotopy.Spectra.Prespectrum.HomotopyGroup.Data

@[expose] public section

namespace KIP126.StableHomotopy.Spectra.Prespectrum

open Topology
open scoped Topology.Homotopy unitInterval

set_option backward.isDefEq.respectTransparency false

universe u

/-- Concatenating in an old coordinate commutes strictly with the actual bond. -/
theorem stabilizeLoop_transAt (X : Prespectrum.{u}) (n r : ℕ) (i : Fin r)
    (p q : GenLoop (Fin r) (X.level n) (X.level n).point) :
    stabilizeLoop X n r (GenLoop.transAt i p q) =
      GenLoop.transAt i.succ (stabilizeLoop X n r p) (stabilizeLoop X n r q) := by
  apply GenLoop.ext
  intro t
  have hupdate (a : I) : (fun j => (Function.update t i.succ a) j.succ) =
      Function.update (fun j => t j.succ) i a := by
    funext j
    simp [Function.update_apply]
  have hzero (a : I) : (Function.update t i.succ a) 0 = t 0 := by
    simp [(Fin.succ_ne_zero i).symm]
  change X.bond n ((GenLoop.transAt i p q) (fun j => t j.succ),t 0) = _
  simp only [GenLoop.transAt, GenLoop.coe_copy]
  split_ifs <;>
    change X.bond n (_,t 0) = X.bond n (_, (Function.update t i.succ _) 0) <;>
    simp only [hupdate, hzero]

@[simp] theorem stabilizeHomotopy_one (X : Prespectrum.{u}) (n r : ℕ)
    [NeZero r] : stabilizeHomotopy X n r 1 = 1 := by
  change (⟦stabilizeLoop X n r GenLoop.const⟧ : _root_.HomotopyGroup _ _ _) =
    ⟦GenLoop.const⟧
  rw [stabilizeLoop_const]

theorem stabilizeHomotopy_mul (X : Prespectrum.{u}) (n r : ℕ) [NeZero r]
    (p q : _root_.HomotopyGroup (Fin r) (X.level n) (X.level n).point) :
    stabilizeHomotopy X n r (p * q) =
      stabilizeHomotopy X n r p * stabilizeHomotopy X n r q := by
  induction p using Quotient.inductionOn with
  | h p =>
    induction q using Quotient.inductionOn with
    | h q =>
      calc
        _ = ⟦stabilizeLoop X n r (GenLoop.transAt 0 q p)⟧ :=
          congrArg (stabilizeHomotopy X n r)
            (_root_.HomotopyGroup.mul_spec (i := (0 : Fin r)) (p := p) (q := q))
        _ = ⟦GenLoop.transAt (0 : Fin r).succ
            (stabilizeLoop X n r q) (stabilizeLoop X n r p)⟧ :=
          congrArg Quotient.mk' (stabilizeLoop_transAt X n r 0 q p)
        _ = _ := (_root_.HomotopyGroup.mul_spec (i := (0 : Fin r).succ)).symm

end KIP126.StableHomotopy.Spectra.Prespectrum
