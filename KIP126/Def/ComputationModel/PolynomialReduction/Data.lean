module

public import Std

@[expose] public section

/-! Sparse polynomials over F₂ and reduction by a supplied finite family of rules. No fixed archive is selected. -/
namespace KIP126.LinE2.Compute

abbrev Monomial := List (Nat × Nat)
abbrev PolynomialF2 := List Monomial
abbrev Calc := Except String

/-- 与原程序相同的稀疏单项式排序；排在最前面的项用于约化。 -/
def monLT : Monomial → Monomial → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | (i, a) :: xs, (j, b) :: ys =>
    if i != j then i > j else if a != b then a < b else monLT xs ys

def insertPower (i a : Nat) : Monomial → Monomial
  | [] => if a == 0 then [] else [(i, a)]
  | (j, b) :: rest =>
    if a == 0 then (j, b) :: rest
    else if i < j then (i, a) :: (j, b) :: rest
    else if i == j then (j, a + b) :: rest
    else (j, b) :: insertPower i a rest

@[no_expose]
def mulMon (a b : Monomial) : Monomial :=
  b.foldl (fun m (i, e) => insertPower i e m) a

/-- 返回 m / divisor；不能整除则返回 none。 -/
def divideMon : Monomial → Monomial → Option Monomial
  | m, [] => some m
  | [], _ :: _ => none
  | (i, a) :: ms, (j, b) :: ds =>
    if i < j then ((i, a) :: ·) <$> divideMon ms ((j, b) :: ds)
    else if i > j || a < b then none
    else do
      let rest ← divideMon ms ds
      return if a == b then rest else (i, a - b) :: rest

/-- F₂ 加法：相同单项式出现偶数次就抵消。 -/
def normalize (p : PolynomialF2) : PolynomialF2 :=
  let sorted := p.mergeSort (fun a b => !monLT b a)
  (sorted.foldl (fun acc m =>
    if acc.head? == some m then acc.tail else m :: acc) []).reverse

def add (p q : PolynomialF2) : PolynomialF2 := normalize (p ++ q)
def mul (p q : PolynomialF2) : PolynomialF2 :=
  normalize (p.flatMap fun m => q.map (mulMon m))

structure Rule where
  lead : Monomial
  tail : PolynomialF2
  deriving Repr, Inhabited

structure BasisTerm where
  s : Nat
  t : Nat
  index : Nat
  monomial : Monomial
  deriving Repr, BEq, Inhabited

/-- 按指定约化规则得到的多项式正规形及其 CSV 基坐标。
此结构记录计算值；约化正确性与基完备性的证明另行陈述。 -/
structure NormalFormCoordinates where
  normalForm : PolynomialF2
  coordinates : Array BasisTerm
  deriving Repr, BEq, Inhabited

/-- 固定 Gröbner 关系的首项约化规则，以及多项式与 CSV 基坐标的索引。 -/
structure ReductionSystem where
  rules : Array Rule
  /-- 按首项的最小、最大生成元编号索引，避免扫描数千条无关规则。 -/
  buckets : Std.HashMap (Nat × Nat) (Array Nat)
  basis : Std.HashMap Monomial BasisTerm
  byCoordinate : Std.HashMap (Nat × Nat × Nat) Monomial

def findRule (e : ReductionSystem) (m : Monomial) : Option (Nat × Monomial) := Id.run do
  for (i, _) in m do
    for (j, _) in m do
      if i ≤ j then
        for r in e.buckets[(i, j)]?.getD #[] do
          if let some q := divideMon m e.rules[r]!.lead then
            return some (r, q)
  return none

/-- 消耗一个 fuel 处理一个首项（约化或移入余式）。不会返回未完成的余式。 -/
@[no_expose]
def reduce (e : ReductionSystem) (p : PolynomialF2) (fuel : Nat := 1000000) : Calc PolynomialF2 :=
  go fuel (normalize p) []
where
  go : Nat → PolynomialF2 → PolynomialF2 → Calc PolynomialF2
    | _, [], remainder => .ok (normalize remainder)
    | 0, _ :: _, _ => .error "reduction fuel exhausted; no normal form returned"
    | n + 1, m :: rest, remainder =>
      match findRule e m with
      | none => go n rest (m :: remainder)
      | some (r, q) => go n (add rest (e.rules[r]!.tail.map (mulMon q))) remainder


end KIP126.LinE2.Compute
