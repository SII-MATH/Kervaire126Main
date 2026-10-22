module

import Mathlib.Topology.Homotopy.Basic
import Mathlib.Topology.Category.TopCat.Basic

@[expose] section

namespace KIP126.Topology.HomotopyExtension

open CategoryTheory
open scoped unitInterval

universe u

/-- Evaluation of an actual continuous path at its initial endpoint. -/
def pathEvaluationZero (Y : TopCat.{u}) : TopCat.of C(I, Y) ⟶ Y :=
  TopCat.ofHom ⟨fun p => p 0, continuous_eval_const 0⟩

end KIP126.Topology.HomotopyExtension
