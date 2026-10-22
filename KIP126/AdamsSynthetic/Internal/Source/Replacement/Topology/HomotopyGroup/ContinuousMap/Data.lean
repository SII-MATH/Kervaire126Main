module

import Mathlib.Topology.Homotopy.HomotopyGroup

@[expose] section

namespace KIP126.Topology
open scoped unitInterval
universe u v w
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/-- Composition on genuine based cubical loops by a based continuous map. -/
def continuousGenLoopMap (f : C(X,Y)) (x : X) (y : Y) (h : f x = y) (n : ℕ)
    (p : GenLoop (Fin n) X x) : GenLoop (Fin n) Y y :=
  ⟨f.comp p.val, fun z hz => (congrArg f (p.property z hz)).trans h⟩

/-- The induced map on the actual based cubical homotopy quotient. -/
def continuousHomotopyMap (f : C(X,Y)) (x : X) (y : Y) (h : f x = y) (n : ℕ) :
    HomotopyGroup.Pi n X x → HomotopyGroup.Pi n Y y :=
  Quotient.map (continuousGenLoopMap f x y h n) fun _ _ h => h.comp_continuousMap f

/-- A basepoint-preserving homeomorphism induces an equivalence of actual cubical loops. -/
def homeomorphGenLoopEquiv (e : X ≃ₜ Y) (x : X) (y : Y) (h : e x = y) (n : ℕ) :
    GenLoop (Fin n) X x ≃ GenLoop (Fin n) Y y where
  toFun := continuousGenLoopMap ⟨e,e.continuous⟩ x y h n
  invFun := continuousGenLoopMap ⟨e.symm,e.symm.continuous⟩ y x (by rw [← h]; exact e.symm_apply_apply x) n
  left_inv p := by apply GenLoop.ext; intro z; exact e.symm_apply_apply (p z)
  right_inv p := by apply GenLoop.ext; intro z; exact e.apply_symm_apply (p z)

/-- The homeomorphism identifies actual relative cubical homotopies in both directions. -/
def homeomorphHomotopyEquiv (e : X ≃ₜ Y) (x : X) (y : Y) (h : e x = y) (n : ℕ) :
    HomotopyGroup.Pi n X x ≃ HomotopyGroup.Pi n Y y :=
  Quotient.congr (homeomorphGenLoopEquiv e x y h n) (fun p q => by
    constructor
    · intro h
      exact h.comp_continuousMap ⟨e,e.continuous⟩
    · intro h'
      have h'' := h'.comp_continuousMap ⟨e.symm,e.symm.continuous⟩
      change GenLoop.Homotopic
        ((homeomorphGenLoopEquiv e x y h n).symm ((homeomorphGenLoopEquiv e x y h n) p))
        ((homeomorphGenLoopEquiv e x y h n).symm ((homeomorphGenLoopEquiv e x y h n) q)) at h''
      change GenLoop.Homotopic p q
      simpa only [Equiv.symm_apply_apply] using h'')


end KIP126.Topology
