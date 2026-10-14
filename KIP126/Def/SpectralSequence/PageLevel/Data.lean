module

public import Mathlib.Data.Int.Basic

@[expose] public section

namespace KIP126.Core.SpectralSequence

/-- Adams 谱序列的有效显示页；下界作为数据的一部分保存。 -/
structure AdamsPage where
  value : ℕ
  valid : 2 ≤ value
  deriving DecidableEq

namespace AdamsPage

/-- Adams 谱序列的第二页。 -/
def two : AdamsPage := ⟨2, le_rfl⟩

def toNat (r : AdamsPage) : ℕ := r.value

def toInt (r : AdamsPage) : ℤ := r.value

/-- 从自然数构造 Adams 页时必须显式提供有效性证明。 -/
def ofNat (r : ℕ) (hr : 2 ≤ r) : AdamsPage := ⟨r, hr⟩

/-- 整数页只在证明有效下界后才能进入 Adams 页接口。 -/
def ofInt (r : ℤ) (hr : 2 ≤ r) : AdamsPage :=
  ⟨r.toNat, by simpa using Int.toNat_le_toNat hr⟩

end AdamsPage

/-- 扩张谱序列的长度；零长度是合法的，因此不带 Adams 页下界。 -/
structure ExtensionLength where
  value : ℕ
  deriving DecidableEq

namespace ExtensionLength

def zero : ExtensionLength := ⟨0⟩

def ofNat (n : ℕ) : ExtensionLength := ⟨n⟩

def toNat (n : ExtensionLength) : ℕ := n.value

def toInt (n : ExtensionLength) : ℤ := n.value

/-- 只有长度至少为二时，才能显式把扩张长度解释为 Adams 页。 -/
def toAdamsPage (n : ExtensionLength) (hn : 2 ≤ n.value) : AdamsPage :=
  ⟨n.value, hn⟩

end ExtensionLength

namespace AdamsPage

/-- 把 Adams 页数值显式解释为扩张长度。 -/
def toExtensionLength (r : AdamsPage) : ExtensionLength := ⟨r.value⟩

end AdamsPage

structure PageLevelConvention where
  firstPage : ℕ
  admissibleFrom : ℤ
  page : ℕ → ℤ
  cycleLevel : ℕ → ℤ
  quotientExponent : ℕ → ℤ
  page_first : page firstPage = admissibleFrom
  page_succ : ∀ r, page (r + 1) = page r + 1
  cycle_succ : ∀ r, cycleLevel (r + 1) = cycleLevel r + 1
  quotient_succ : ∀ r, quotientExponent (r + 1) = quotientExponent r + 1
  cycleLevel_eq_quotientExponent : ∀ r,
    cycleLevel r = quotientExponent r

namespace PageLevelConvention

/-- 在 Adams 页类型上读取底层整数页。 -/
def pageAtAdams (P : PageLevelConvention) (r : AdamsPage) : ℤ :=
  P.page r.toNat

/-- 在扩张长度类型上读取底层整数页。 -/
def pageAtExtension (P : PageLevelConvention) (n : ExtensionLength) : ℤ :=
  P.page n.toNat

end PageLevelConvention

end KIP126.Core.SpectralSequence
