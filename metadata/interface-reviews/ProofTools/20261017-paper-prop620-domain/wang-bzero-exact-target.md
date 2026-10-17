# 6.20 固定目标与提高源滤过：局部证明交付

本轮任务来自协调者转述的王老师最新意见“一般的 b，可以推 b=0”。本文件只交付服务该目标的固定目标判据；不把它登记为完整 6.20，也不声称已经完成一般 b 到 b=0 的转换。

## 范围与基线

- HEAD：`aad718722aa01dfce361f40645fc776037d1078f`。
- 只新增本报告和 `evidence/WangBzeroExactTarget.lean`；不修改生产文件、公共入口、接口锁、测试或共享待补记录。
- 参考 `evidence/IndependentChecks.lean` 中独立复核过的泛型固定目标恒等式；该来源 SHA-256 为 `bc262fbb15238fafff7e5dcc870a9a81598a1c1d336d5461f6a0c9b47e65de95`。
- 普通导入 `KIP126.ProofTools.Operations`，仅为元素级代表转换同模块 `import all KIP126.ProofTools.ConvergenceOperations`。

## 已构造的数学结论

设同一个实际 filtered map 的扩张关系已知为 `Relation f k s n x y`。利用其加法/减法性质和既有 essential 性判据，得到

```
¬ Essential f k s n x y ↔ Relation f k s n 0 y.
```

两侧保持同一个 map、分次、滤过和目标 y。这里没有任意选择的 y'。前提中原扩张方程不可删去：它提供了两个方向所需的相减构造。

再直接调用上游 `FilteredMapExtension.mem_indeterminacy_iff`，得到精确代表版本：上述条件等价于存在源在 F(s+1)、靶在 G(s+n) 的真实代表，靶代表的 associated-graded 投影恰好等于 y，并且它确实是该源代表在同一个实际 filtered map 下的像。

在 synthetic tower 上，证据文件给出对应的两条判据，最后将零源判据专门化到 `FiniteExtensionWitness D X Y f r n s t x y`：

```
¬ W.Essential ↔ TowerExtensionEquation
  (D.convergentMap <同一有限商源> <同一有限商靶> (finiteExtensionMap ...))
  (t-s,t+e(f)) s n 0 W.target.
```

该专门化直接调用 `W.equation`，没有替换原 witness 的 map、source/target convergence 或 target。

## 与论文命题 2.2 的关系及局限

论文 `prop:8154e6f1` 第 (2) 项说 inessential 的指定目标可由更高源滤过的类打到。这里证明的是其真实 filtered representative 部分，保持精确目标 y，而不是仅要求存在一个 unrelated shorter target。

尚未证明：从高源滤过代表选出具有最小精确滤过的非零 leading class、对应的 essential 短扩张、源的非提升性，以及一般 b 的数据怎样构造出 b=0 的数据。因此不能把本局部判据称为完整 6.20，也不能仅靠它推出论文中的完整 crossing 等价。

## 实际检查与依赖

验证命令：

```
lake env lean metadata/interface-reviews/ProofTools/20261017-paper-prop620-domain/evidence/WangBzeroExactTarget.lean
```

命令以 `require_escalated` 运行，沿用已有工具链，避免沙箱无法检测应用安装位置的问题。不写 `.olean` 或共享构建状态。

最终版本实际 Lean 检查退出码为 **0**。五条公开证据引理均通过 elaboration，所有 `#print axioms` 均只有 `propext`、`Classical.choice`、`Quot.sound`，没有 `sorryAx`。

初版 tower 元素代表转换在大型类型上调用宽泛 `simp` 时超时；最终改为在自由秩一模的元素 1 上求值，并用局部 `elementMap_one` 等式直接改写。上述通过结果来自最终优化后的文件；没有将失败或超时日志中的声明当作完成证明。

所有定理均参数化于实际 filtered map / convergence / model D，因此证明自身不引用项目标准模型待构造对象；没有新 axiom、sorry 或待补责任。若协调者以后专门化到 `AdamsSynthetic.Standard.model`，仍须如实保留该标准模型的既有传递待构造责任。仓库完整构建及公共接口整合由协调者统一安排。

## 后续评估：整体 homotopy 修正不能提升，不等于首项不能提升

下面给出保留指定目标 y 的真实必要性论证方案，尚未在此证据文件中实现为 Lean 定理。

固定晚页目标的实际代表 β ∈ F_late(B)^(s+n)，早页修正 δ ∈ F_early(A)^(s+1) 实现的精确目标取为 ρ_Y(β) 的 associated-graded 类。因而

```
g_early(δ) - ρ_Y(β) ∈ F_early(B)^(s+n+1).
```

若整体修正 δ 真能写成 ρ_X(α)，其中 α ∈ F_late(A)^(s+1)，利用实际方块自然性可得

```
ρ_Y(g_late(α)-β) ∈ F_early(B)^(s+n+1).
```

残差 g_late(α)-β 起初位于 F_late(B)^s。逐级应用 `finite_filtration_reflection`，可将早页的 s+n+1 滤过反射到晚页。目标端 ρ_Y 在该有限区间所需的 E∞ 单射条件来自实际有限商 strip：设固定双次数为 (m,w)=(t-s,t+e(f))，对 s≤k≤s+n 有

```
m+k-w = k-s-e(f) ≤ n-e(f) ≤ r'-2 < r'-1.
```

这正是 `rho_infty_injective` 在早商长度 r'-1 上的范围条件。因此晚页残差也位于 F_late(B)^(s+n+1)，得到由更高源滤过 α 打到同一个晚页目标 y 的修正，违背晚页扩张 essential。结论是：**实现这个精确目标的整个 δ，不属于 ρ_X(F_late(A)^(s+1))。** 这里不要求 ambient ρ_Y 单射，只需要有限区间逐级 graded 单射。

这个结论仍然不能直接推出 δ 的第一个非零 E∞ 类不在 ρ_X 的像中。首项若可以提升，只能先减去一个可提升首项的代表，把残差推高一个滤过；减去该代表还会改变其实际 g-image。若该 image 在更低目标滤过出现非零项，就必须追踪那些项与剩余修正怎样抵消。仅有“整体 δ 不可提升”，无法保证迭代后第一个不可提升首项仍单独打到指定的原目标 y。

因此要完成完整 6.20，仍需额外证明这一有限消去过程保留精确目标，或证明消去低目标项后可以构造 b=0 的短扩张。不能把整体 homotopy 不提升换写成首项 E∞ 不提升，也不能凭此替代原来的 cycle-set 差集条件。
