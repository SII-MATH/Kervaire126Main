module

public import KIP126.AdamsSynthetic.Standard.Background

/-! Separation of the fixed synthetic homotopy filtration on finite λ quotients.
The original unrestricted producer obligation from Kervaire126 bbac1fc05843,
Def/Kervaire/Route/Model/Coherent/Data.lean:29, was incompatible with ordinary
sphere odd torsion. The approved replacement concerns the actual λⁿ cofiber
of each selected object, with the same fixed tower and model. The canonical
associated-graded comparison alone does not establish this separation. -/

@[expose] section
namespace KIP126.AdamsSynthetic.Standard
open KIP126.Kervaire.Route

/-- An element in every nonnegative filtration level vanishes on the actual
finite λⁿ quotient of each selected object, for the same fixed synthetic tower.
This remains an unfinished foundational producer proof; it is neither a
finite filtration bound nor a proof obligation of the paper's tools. -/
public theorem synthetic_homotopy_separated (X : SyntheticObject) (n : ℕ) :
    KIP126.AdamsSynthetic.HomotopySeparated model.syntheticTower
      (KIP126.Synthetic.Context.XModLambdaN
        (X.obj model.nu model.auxiliary) n) := by
  sorry

end KIP126.AdamsSynthetic.Standard
