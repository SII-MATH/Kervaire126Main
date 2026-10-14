module

public import KIP126.Def.Computation.Basis

/-! Named classes on the one actual sphere E₂. Every nonstandard atom is the
image of its archived source label under one comparison. Every composite is
formed using the actual sphere multiplication. No class carries a survival
claim merely by having a name. -/

set_option backward.isDefEq.respectTransparency false

@[expose] section
namespace KIP126.Computation
open CategoryTheory KIP126.StableHomotopy KIP126.Synthetic.Context
open KIP126.Kervaire.Route KIP126.Classical.Adams
universe u v w
variable {C : Type u} [StableHomotopyCategory.{u,v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w,v} Syn]
  [HasFunctorialCofiber (C := Syn)]

public structure Bindings (D : Model C Syn) where
  data : ProgramData.{v}
  archive : SphereArchive
  sourceBasis : SourceBasisSpecification data archive
  presentation : SpherePresentation D data

namespace Bindings
variable {D : Model C Syn} (B : Bindings D)

public noncomputable def atom (a : Atom) :
    D.classical.sphere.Page 2 (a.degree.1,a.degree.2) :=
  B.presentation.comparison a.degree.1 a.degree.2
    (by cases a <;> decide) (B.data.atom a)

public noncomputable abbrev h0 : D.classical.sphere.Page 2 (1,1) := D.standardClasses.standardHi 0
public noncomputable abbrev h1 : D.classical.sphere.Page 2 (1,2) := D.standardClasses.standardHi 1
public noncomputable abbrev h2 : D.classical.sphere.Page 2 (1,4) := D.standardClasses.standardHi 2
public noncomputable abbrev h4 : D.classical.sphere.Page 2 (1,16) := D.standardClasses.standardHi 4
public noncomputable abbrev h5 : D.classical.sphere.Page 2 (1,32) := D.standardClasses.standardHi 5
public noncomputable abbrev h6 := D.standardClasses.standardH6
public noncomputable abbrev h6Square := D.standardClasses.standardH6Square

public noncomputable def product {p q r : Bidegree}
    (x : D.classical.sphere.Page 2 p) (y : D.classical.sphere.Page 2 q)
    (h : p + q = r := by decide) : D.classical.sphere.Page 2 r :=
  (eqToHom (congrArg (D.classical.sphere.Page 2) h))
    (D.sphereAlgebra.product p q x y)

public noncomputable def h0Square : D.classical.sphere.Page 2 (2,2) :=
  product (D := D) (h0 (D := D)) (h0 (D := D))
public noncomputable def h0Six : D.classical.sphere.Page 2 (6,6) :=
  product (D := D) (product (D := D) (r := (4,4)) (h0Square (D := D)) (h0Square (D := D))) (h0Square (D := D))
public noncomputable def h5Square : D.classical.sphere.Page 2 (2,64) :=
  product (D := D) (h5 (D := D)) (h5 (D := D))
public noncomputable def W : D.classical.sphere.Page 2 (8,134) :=
  B.atom .x_126_8_4 + B.atom .x_126_8
public noncomputable def U : D.classical.sphere.Page 2 (10,134) :=
  product (D := D) (h0Square (D := D)) (B.atom .x_124_8)
public noncomputable def T : D.classical.sphere.Page 2 (14,139) :=
  product (D := D) (h1 (D := D)) (product (D := D) (r := (13,137)) (h4 (D := D)) (B.atom .x_109_12))
public noncomputable def V : D.classical.sphere.Page 2 (9,132) :=
  B.atom .x_123_9 + product (D := D) (r := (9,132)) (h0 (D := D)) (B.atom .x_123_8)
public noncomputable def Y : D.classical.sphere.Page 2 (11,136) :=
  product (D := D) (h0Square (D := D)) (B.atom .x_125_9_2)
public noncomputable def X : D.classical.sphere.Page 2 (8,130) :=
  product (D := D) (h1 (D := D)) (B.atom .x_121_7)
public noncomputable def P : D.classical.sphere.Page 2 (11,133) :=
  product (D := D) (h6 (D := D)) (B.atom .M_mul_d_0)
public noncomputable def Q : D.classical.sphere.Page 2 (12,134) :=
  product (D := D) (h5 (D := D)) (B.atom .x_91_11)
public noncomputable def correction : D.classical.sphere.Page 2 (13,137) :=
  product (D := D) (B.atom .e0) (B.atom .delta_h_6_mul_g)
public noncomputable def highClass : D.classical.sphere.Page 2 (25,150) :=
  product (D := D) (product (D := D) (r := (16,96)) (product (D := D) (r := (8,48)) (B.atom .g) (B.atom .g))
    (product (D := D) (r := (8,48)) (B.atom .g) (B.atom .g))) (B.atom .delta_h_1_mul_g)
public noncomputable def d2Target : D.classical.sphere.Page 2 (10,134) :=
  product (D := D) (r := (10,134)) (h1 (D := D)) B.V + B.U
public noncomputable def d7Source : D.classical.sphere.Page 2 (11,134) :=
  B.atom .x_123_11_2 + B.atom .x_123_11 +
    product (D := D) (r := (11,134)) (product (D := D) (r := (2,65)) (h0 (D := D)) (h6 (D := D))) (B.atom .b4)
public noncomputable def d3Candidate : D.classical.sphere.Page 2 (9,134) :=
  product (D := D) (h5 (D := D)) (B.atom .x_94_8)
public noncomputable def d3OtherCandidate : D.classical.sphere.Page 2 (9,134) :=
  B.d3Candidate + product (D := D) (r := (9,134)) (h6 (D := D)) (B.atom .b)

public theorem atom_h0 : B.atom .h0 = h0 (D := D) := B.presentation.h0
public theorem atom_h1 : B.atom .h1 = h1 (D := D) := B.presentation.h1
public theorem atom_h2 : B.atom .h2 = h2 (D := D) := B.presentation.h2
public theorem atom_h4 : B.atom .h4 = h4 (D := D) := B.presentation.h4
public theorem atom_h5 : B.atom .h5 = h5 (D := D) := B.presentation.h5
public theorem atom_h6 : B.atom .h6 = h6 (D := D) := B.presentation.h6
end Bindings
end KIP126.Computation
