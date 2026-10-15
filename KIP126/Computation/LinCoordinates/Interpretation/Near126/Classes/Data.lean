module

public import KIP126.Computation.WellFormedness.LinCoordinates.NamedClasses
public import KIP126.Computation.LinCoordinates.Model.Classes.Data
public import KIP126.Computation.LinCoordinates.Model.Product.Data

@[expose] public section

namespace KIP126.Computation.Near126
open KIP126.LinE2
noncomputable section

-- Keep degree unification from unfolding the large presentation ideal.
attribute [local irreducible] KIP126.LinE2.homogeneousPart

/-- An actual coordinate in the pinned Lin quotient, not a freely chosen class. -/
def atom (a : Atom) : E2At a.record.2.2.1 a.record.2.2.2 :=
  ⟨generator ⟨a.record.1, a.index_lt⟩, by
    simpa only [a.degree_eq] using generator_mem ⟨a.record.1, a.index_lt⟩⟩

def h0Sq : E2At 2 2 := mulAt dataH0 dataH0
def h0Six : E2At 6 6 := mulAt (mulAt h0Sq h0Sq) h0Sq
def h5Sq : E2At 2 64 := mulAt (atom .h5) (atom .h5)
/-- The CSV itself uses this composite expression as the name of generator 82. -/
def B : E2At 8 70 := atom .b
def V : E2At 9 132 := atom .x_123_9 + mulAt dataH0 (atom .x_123_8)
def U : E2At 10 134 := mulAt h0Sq (atom .x_124_8)
def T : E2At 14 139 := mulAt dataH1 (mulAt (atom .h4) (atom .x_109_12))
def W : E2At 8 134 := atom .x_126_8_4 + atom .x_126_8
def Y : E2At 11 136 := mulAt h0Sq (atom .x_125_9_2)
def X : E2At 8 130 := mulAt dataH1 (atom .x_121_7)
def P : E2At 11 133 := mulAt dataH6 (atom .M_mul_d_0)
def Q : E2At 12 134 := mulAt (atom .h5) (atom .x_91_11)
def correction : E2At 13 137 := mulAt (atom .e0) (atom .delta_h_6_mul_g)
def highClass : E2At 25 150 :=
  mulAt (mulAt (mulAt (atom .g) (atom .g)) (mulAt (atom .g) (atom .g))) (atom .delta_h_1_mul_g)
def d7Source : E2At 11 134 :=
  atom .x_123_11_2 + atom .x_123_11 + mulAt (mulAt dataH0 dataH6) (atom .b4)
def d3Candidate : E2At 9 134 := mulAt (atom .h5) (atom .x_94_8)
def d3OtherCandidate : E2At 9 134 := d3Candidate + mulAt dataH6 B

end
end KIP126.Computation.Near126
