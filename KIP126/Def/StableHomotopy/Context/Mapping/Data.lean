module

public import KIP126.Def.StableHomotopy.Context.Data

@[expose] public section

namespace KIP126.StableHomotopy

open CategoryTheory

universe u v

variable {C : Type u} [StableHomotopyCategory.{u, v} C]

/-- Apply an exact, shift-compatible functor to the specified distinguished
triangle, retaining its actual connecting morphism and shift comparison. -/
def HoCofiberSequence.map (T : HoCofiberSequence (C := C)) (F : C ⥤ C)
    [F.CommShift ℤ] [F.IsTriangulated] : HoCofiberSequence (C := C) where
  X := F.obj T.X
  Y := F.obj T.Y
  Z := F.obj T.Z
  f := F.map T.f
  g := F.map T.g
  h := F.map T.h ≫ (F.commShiftIso (1 : ℤ)).hom.app T.X
  distinguished := F.map_distinguished _ T.distinguished

end KIP126.StableHomotopy
