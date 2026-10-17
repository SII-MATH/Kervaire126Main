# 命题 6.20 最新二择：独立反例审查

状态：未发现满足完整前提的反例；有限计算支持，但不构成实际固定对象的证明。本文不是实现者报告，未修改生产文件、公共锁或责任清单，未运行 Lake 构建。

## 核验对象与完整目标

固定 `KIP126.AdamsSynthetic.Standard.model`，`X Y : ClassicalObject`，同一实际映射 `f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary`。记 `e = normalizedExponent model.classicalTower f`，`qE = rEarlier - 1`、`qL = rLater - 1`。量化 `rEarlier rLater : ℕ`、`n s t : ℤ` 及同一 classical E₂ 类 `x : E₂(X)^(s,t)`、`y : E₂(Y)^(s+n,t+n)`。

假设 `Wlater : FiniteExtensionWitness model X Y f rLater n s t x y`、`Wearly : FiniteExtensionWitness model X Y f rEarlier n s t x y`、`rEarlier ≤ rLater`、`Wlater.Essential`、`¬ Wearly.Essential`。Witness 的全部内含前提均保留：页码至少 2；`e ≤ n ≤ r−2+e`；源到 r 页、目标到 r−n+e 页的实际存活；实际有限商上的源/目标 E∞ 代表；同一归一化映射的实际扩张方程。

目标是 `D_y ∨ C_late`。其中 `D_y` 精确为：存在 `a : ℕ`，`0<a`、`a≤n−e`，存在同一 X 上 `(s+a,t+a)` 次 classical 原始类 `x′`，满足

* `x′ ∈ cycles model X (qE−a) (s+a,t+a)`；
* `x′ ∉ cycles model X (qL−a) (s+a,t+a)`；
* `finiteExtensionCorrectionLabel X Y f qE s t a x′` 在实际早商源 ESS 中有 E∞ 代表 `z`；
* 同一早商归一化映射在源滤过 `s+a`、长度 `n−a` 下有 `TowerExtensionEquation … z Wearly.target`，目标只作 `s+n=(s+a)+(n−a)` 的类型运输。

`C_late` 为 `¬ Paper.ExtensionNoCrossingRange Mlate (t−s,t+e) s n s`；即存在整数 `u,v`，`s<u≤v≤s+n`，同一晚商 ESS 的源/目标类 `ξ,η`，有 `TowerExtensionEquation Mlate … u (v−u) ξ η` 且 `η≠0`。允许方程自身非本质，也不额外要求 `ξ≠0`。此处没有把 C 换成定义 5.9 的 classical crossing。

读入位置：`KIP126/AdamsSynthetic/ExtensionWitnesses.lean:21`，`KIP126/ProofTools/Paper/ExtensionRepresentatives.lean:39`，`KIP126/ProofTools/Paper/ExtensionIndeterminacy.lean:191,300`。既有契约为 `metadata/proof-tools-contracts.json` 中 `paper-finite-extension-inessentiality-revised`；既有来源范围是 AimPaper `prop:dec738d3` 的人类授权修订，不能据此声称原文所有形式已证明。

读取基线 SHA-256：

* `ExtensionIndeterminacy.lean`：`1720fccd565456ad350d489a3da09eacecce316d5d9626077b71e5fdad71c34c`；
* `ExtensionRepresentatives.lean`：`b5a2b3a4d7ec4506e16d4aa444693d362c4135cf74a67f801f138e0c5f7d0a1e`；
* `ExtensionWitnesses.lean`：`2864cf03dae40fc24ad69f16026499e9b15a03b82a3ecddab0414c3b82d8a0ea`。

## 主动攻击与边界

1. **原 HZ/16 型实例不再反驳此目标。** 其晚页短箭头本身提供 C。原目标、b=0 的严格差集版本失败，只说明 C 不能任意删去。
2. **整体校正不提升不能替代首项差集。** 下文有限控制准确重现该区别；不存在误把非提升整体当 D 的空间。
3. **不能只取 a=1。** a=1 的首项可以是零或早页非本质；差集要求必须通过有界提高滤过或 essential 早页源选择保证。新版 D 不要求短方程 essential，但必须有真实早页 E∞ 代表。
4. **n=e。** 早页原目标非零时，实际 e 滤过下界已排除更高源命中该目标；早页非本质前提不成立。不能制造 `0<a≤0` 的伪反例。
5. **rEarlier=rLater。** 同标签 E∞ 代表的唯一性把两个 witness 的源目标识别；本质与非本质相冲突，不能当作边界反例。
6. **最高 a=n−e。** 此时早页源 classical 窗口仍合法：由 `n−e≤rEarlier−2=qE−1`，得 `a<qE`、`qE−a≥1`。归纳末端必须落到 `s+n−e+1`，再用 e 滤过位移推出像在 `F^(s+n+1)`。
7. **不另需无穷完备性。** 反证只使用有限滤过区间 `s+1,…,s+n−e+1`，无需断言每个非零整体有全局最大 Adams filtration。若实现用最大滤过，必须给出有限区间的确切理由。
8. **目标级 ρ 单射和源标签 ρ 自然性均实质必要。** 目标识别不可仅凭 y 同名；源 comparison 的 `Classical.choice` 所选商/shift 同构不可自动称为与 ρ 交换。当前 worker 正独立处理此处；本审查未将该相容性假设为已有证明。

## 有限计算证据

复现：在仓库根目录执行

```text
python3 metadata/interface-reviews/ProofTools/20261018-prop620-crossing-dichotomy/counterexample_search.py
```

脚本不导入项目或调用目标。全部运算是 F₂ 向量按位异或。先穷举 4096 个三层滤过交换方块：早晚源及早晚目标均 F₂³，标准基滤过为 0,1,2；目标 ρ 是恒等；早映射和源 ρ 为全部滤过保持矩阵；晚映射由交换性强制为早映射复合源 ρ。固定 s=0,n=2,e=0，qE=3,qL=4，两个原源领先项相同非零，两个实际方程都是 e₀→e₂。逐一直接检查晚 essential、早 inessential、目标级单射、source/target 滤过以及 D/C。

实际结果：22 个方块满足全部被建模的原扩张前提；18 个只有 D，4 个 D 与 C 都成立；没有 D、C 俱假的实例。

这里 D 的“classical cycle 可提升”仅建模为源 associated-graded ρ 的像，不是已构造的项目 classical Adams cycle 子对象；这点限制意味着该计算只是有限抽象压力测试，不是 actual spectrum 的证明或反例。

脚本还检查了一个需要 C 的独立控制：早源基为 `x(0),u(1),v(2)`，括号内是滤过；晚源只有 `x(0),u(1)`，ρ 是实际包含。早晚目标相同，基为 `z(2),y(3)`。定义

```text
fEarly(x)=y,  fEarly(u)=z,  fEarly(v)=z+y;
fLate(x)=y,   fLate(u)=z.
```

取 s=0,n=3,e=0，qE=4,qL=5。所有映射保持滤过，目标 ρ 恒等，方块交换，两个原方程为 x→y。晚源高滤过部分只可能像 0 或 z，所以晚原方程 essential。早页校正 `u+v` 命中 y，故早方程 inessential。其首项是可提升的 u；唯一非提升领先项是 v，而 `f(v)=z+y` 不在目标 F³，所以不存在 D。晚页 `u→z` 的源滤过 1、目标滤过 2 给 C。这是新二择成立但删除 C 后失败的完整抽象模型，不声称谱实现。

## 条件性数学核验与实现风险

在一个与目标完全相容的滤过交换方块中，若目标级 ρ 单射、源领先 classical 标签可提升当且仅当所需 E∞ 级可提升、且早映射有实际 e 滤过下界，则目标有如下独立有限反证。早页非本质给高源校正 α∈F^(s+1)，其像领先目标是原 y≠0。假设 D、C 均不存在。每一阶段的 α∈F^(s+a) 取实际领先 classical 标签；若该标签不提升，便给 D，矛盾。若可提升，取晚页同领先标签的 homotopy 代表 β。晚页无 C 强制 fLate(β) 在 F^(s+n+1)；减去 ρβ 后早页 α 的滤过提高一级，且其像仍代表原 y。重复有限次直到 α∈F^(s+n−e+1)，由 e 位移其像属于 F^(s+n+1)，与 y≠0 矛盾。

这不是本审查对实际接口的已完成 Lean 证明；它清楚指出生产候选不得省略的三个桥接：

* `Wlater.Essential` 给晚目标非零；再经实际目标比较和 ρ 在合法条带上的单射给早目标非零。
* classical cycle 的晚页存活，必须给**同一早领先标签**的晚 E∞ 提升，不能只给一个抽象同维对象或任意 representative。
* 同一实际 f 的早晚归一化商映射与 ρ 交换；不能用只满足 inclusion square 的任意 shift/cofiber 同构跳过该识别。

## 依赖审计与局限

有限脚本只使用 Python 标准库、F₂ 运算和独立枚举，没有使用候选定理、其下游推论或项目未证事实，也没有借矛盾环境导出反例。未使用外部文献作为反例证明。脚本成功不等于 Lean 编译成功或 actual fixed model 正确。

实际对象的桥接依赖既有 AdamsSynthetic standard model、quotients/coherence/convergence 与 Literature 的有限 E∞ label/window 比较、eInfinity ρ 比较等；这些含有既有登记待补责任，如 `KIP126.Literature.Standard.eInfinity_finite_labels`、`eInfinity_rho_finite`，以及 `KIP126.AdamsSynthetic.Standard.quotients`。其责任保留原上游，不能因本地二择补证而宣称全部基础构造无待补。基础经典逻辑/choice 与这些数学待补责任应分开记录。

未审计尚未产生的最终公共候选的实际传递常量依赖，未称候选已经通过 proof audit。当前没有证据要求改变已经授权的 D/C 范围；若最终实现把源差集替换成所选整体代表的非提升、把 C 改成 classical crossing，或附加未授权比较假设，则需要重新独立审查。
