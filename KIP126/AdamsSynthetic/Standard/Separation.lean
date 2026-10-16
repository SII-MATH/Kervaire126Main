module

public import KIP126.AdamsSynthetic.Standard.Background

/-! Separation of the fixed synthetic homotopy filtration.
This restores the producer obligation recorded by `Model.homotopySeparated`
in Kervaire126 bbac1fc05843, Def/Kervaire/Route/Model/Coherent/Data.lean:29,
with its predicate in Model/Predicates.lean:85–87 (MIT).
The scope is exactly the selected SyntheticObject closure. The canonical
associated-graded comparison alone does not establish this separation. -/

@[expose] section
namespace KIP126.AdamsSynthetic.Standard
open KIP126.Kervaire.Route

/-- An element in every nonnegative filtration level vanishes, on each
object of the selected closure and for the same fixed synthetic tower.
This remains an unfinished foundational producer proof; it is neither a
finite filtration bound nor a proof obligation of the paper's tools. -/
public theorem synthetic_homotopy_separated (X : SyntheticObject) :
    KIP126.AdamsSynthetic.HomotopySeparated model.syntheticTower
      (X.obj model.nu model.auxiliary) := by
  sorry

end KIP126.AdamsSynthetic.Standard
