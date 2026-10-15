module

public import KIP126.Def.ComputationModel.PolynomialReduction.Data
public import KIP126.Computation.LinCoordinates.Generated.E2

@[expose] public section

/-!
Ported from PR #110 commit ff39e95147712fc00cd3f700e0dd1f490d16b863,
`KIPBase/E2pageCompute.lean`; the definitions retain the same reduction algorithm.

可执行的球谱 E₂ Gröbner 约化器（v126.3.cw49，内部次数 ≤ 261）。
复现同版 source code.zip 中 alg::GE / alg2::Mon 的比较和首项约化。
使用导出的 Gröbner 规则；不重新运行 Buchberger，也不声称已证明其完备性。
本模块无 sorry、axiom、noncomputable。错误输入、超范围、燃料耗尽、
无法匹配 CSV 基的余项均显式报错。同一约化系统可用于多个乘法计算。
空单项式字符串表示 1，整个多项式字符串 "0" 表示零。
-/
namespace KIP126.LinE2.Compute

private def readNat (s : String) : Calc Nat :=
  match s.toNat? with
  | some n => .ok n
  | none => .error s!"invalid natural number: {s}"

private def parsePowers : List String → Calc Monomial
  | [] => .ok []
  | [_] => .error "monomial must contain generator/exponent pairs"
  | i :: a :: rest => do
    let i ← readNat i
    let a ← readNat a
    if i ≥ RawData.generatorCount then throw s!"unknown generator id: {i}"
    return insertPower i a (← parsePowers rest)

@[no_expose]
def parseMonomial (s : String) : Calc Monomial :=
  if s == "" then .ok [] else parsePowers (s.splitOn ",")

def parsePolynomial (s : String) : Calc PolynomialF2 := do
  if s == "0" then return []
  return normalize (← (s.splitOn ";").mapM parseMonomial)

def degree (m : Monomial) : Nat × Nat :=
  m.foldl (fun (s, t) (i, a) =>
    let row := RawData.generators[i]!
    (s + a * row.2.1, t + a * row.2.2)) (0, 0)

private def checkRange (p : PolynomialF2) : Calc Unit := do
  for m in p do
    if (degree m).2 > 261 then
      throw s!"outside data range: internal degree t = {(degree m).2} > 261"

/-- 解析、检查全部关系，建立首项整除索引及 CSV 基索引。 -/
@[no_expose]
def loadReductionSystem : Calc ReductionSystem := do
  let mut e : ReductionSystem := {
    rules := #[]
    buckets := {}
    basis := {}
    byCoordinate := {} }
  for code in RawData.relations do
    let original ← (code.splitOn ";").mapM parseMonomial
    let p := normalize original
    if p != original then throw s!"relation is not in archived canonical order: {code}"
    let lead :: tail := p | throw "zero relation in CSV"
    let (i, _) :: _ := lead | throw "unit leading term in CSV"
    let d := degree lead
    if d.2 > 261 then throw "relation exceeds degree bound"
    for m in tail do
      if degree m != d then throw "inhomogeneous CSV relation"
      if !monLT lead m then throw "relation tail does not advance the archived order"
    let r := e.rules.size
    let key := (i, lead.getLast!.1)
    let bucket := e.buckets[key]?.getD #[]
    e := { e with
      rules := e.rules.push ⟨lead, tail⟩
      buckets := e.buckets.insert key (bucket.push r) }
  if e.rules.size != RawData.relationCount then throw "relation count mismatch"
  for chunk in RawData.basisChunks do
    for line in chunk.splitOn "\n" do
      let [s, t, index, code] := line.splitOn "|" | throw "malformed basis row"
      let s ← readNat s
      let t ← readNat t
      let index ← readNat index
      let m ← parseMonomial code
      if degree m != (s, t) || t > 261 then throw "basis degree mismatch"
      if e.basis.contains m || e.byCoordinate.contains (s, t, index) then
        throw "duplicate basis monomial or coordinate"
      if (findRule e m).isSome then throw "CSV basis monomial is reducible"
      e := { e with
        basis := e.basis.insert m ⟨s, t, index, m⟩
        byCoordinate := e.byCoordinate.insert (s, t, index) m }
  if e.basis.size != RawData.basisCount then throw "basis count mismatch"
  return e

/-- 将约化余式中的各单项式对应到指定 CSV 基；缺少基项时报错。 -/
private def toNormalFormCoordinates (e : ReductionSystem) (p : PolynomialF2) : Calc NormalFormCoordinates := do
  let mut cs := #[]
  for m in p do
    let some row := e.basis[m]? | throw s!"normal monomial absent from CSV basis: {repr m}"
    cs := cs.push row
  return ⟨p, cs⟩

/-- 在 t ≤ 261 范围内计算；任意输入项或乘积项超出范围时报告错误。 -/
@[no_expose]
def ReductionSystem.multiplyStrings (e : ReductionSystem) (a b : String)
    (fuel : Nat := 1000000) : Calc NormalFormCoordinates := do
  let a ← parsePolynomial a
  let b ← parsePolynomial b
  checkRange a
  checkRange b
  let p := mul a b
  checkRange p
  toNormalFormCoordinates e (← reduce e p fuel)

/-- 明确选择截断代数语义：删除乘积中 t > 261 的项。 -/
@[no_expose]
def ReductionSystem.multiplyTruncated (e : ReductionSystem) (a b : String)
    (fuel : Nat := 1000000) : Calc NormalFormCoordinates := do
  let a ← parsePolynomial a
  let b ← parsePolynomial b
  let p := (mul a b).filter (fun m => (degree m).2 ≤ 261)
  toNormalFormCoordinates e (← reduce e p fuel)

/-- 基坐标输入；数组表示各基向量之和，重复向量相消。 -/
@[no_expose]
def ReductionSystem.multiplyBasis (e : ReductionSystem)
    (a b : Array (Nat × Nat × Nat)) (fuel : Nat := 1000000) : Calc NormalFormCoordinates := do
  let decode := fun (coords : Array (Nat × Nat × Nat)) => coords.toList.mapM fun key =>
    match e.byCoordinate[key]? with
    | some m => .ok m
    | none => .error s!"unknown basis coordinate: {repr key}"
  let p := mul (← decode a) (← decode b)
  checkRange p
  toNormalFormCoordinates e (← reduce e p fuel)

def displayMonomial (m : Monomial) : String :=
  if m.isEmpty then "1" else
    String.intercalate " * " (m.map fun (i, a) =>
      let name := (RawData.generators[i]!).1
      let name := if name == "[NULL]" || name == "" then s!"x_{i}" else name
      if a == 1 then name else s!"({name})^{a}")

/-- 显示正规形及各项的双次数、基索引。 -/
def displayNormalFormCoordinates (r : NormalFormCoordinates) : String :=
  if r.normalForm.isEmpty then "0; basis coordinates: []" else
    String.intercalate " + " (r.normalForm.map displayMonomial) ++ "\n  " ++
      String.intercalate "; " (r.coordinates.toList.map fun c =>
        s!"(s,t)=({c.s},{c.t}), basis index={c.index}")

end KIP126.LinE2.Compute
