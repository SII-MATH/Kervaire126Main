# High125 局部修复研究交付

## 范围、基线与实际检查

任务基线 `2c70381`。协议 `/root/.agents/skills/kip-upstream-session/references/protocol.md` 与仓库 `AGENTS.md` 已读。只读生产文件；交付本报告和 `/tmp/kip-high125-local-repair.patch`。Main 唯一写入者为 `downstream_adaptation`。未运行 Lake，未写共享构建缓存，未新增 sorry、公理、责任或公共前提。

本次实际检查：源码读取及调用搜索；`git apply --check /tmp/kip-high125-local-repair.patch` 成功（退出码 0）。补丁尚未经过 Lean 编译；它只是局部去除不必要错误依赖，整个 High125 尚不能据此宣称修复。

读取时文件 SHA-256：

- `KIP126/Main/Internal/High125/Filtration.lean`: `9afc54c92e4a799086d0cd491428b65a9e6a51dabf7aaf6d69d8a6f39cbc30ba`
- `KIP126/Main/Internal/High125/Source.lean`: `8e388410bb8ab3e73c735462e4e5c60219eddd6fedf78d69e6615c697e1227ba`
- `KIP126/Main/Internal/High125/Injectivity.lean`: `32d6476fec0fc8ac68152d7f86e8a8ec3a4a5c809dd865c67aa001a9f40d36f7`
- `KIP126/Literature/Standard.lean`: `381247aaf93f80eb3d797b0b8cc96cbb8c11c849149c32303c15c716568da6a6`（共享工作区中的当前版本，已含别的 worker 的 stem62 签名修改）。

## 可以立即删除的一条多余依赖

调用搜索确认：

1. `Source.high_detected_choice_unique` 只有一个调用，即 `Source.high_detected_detector_nonzero`。
2. 后者唯一实际调用在 `Injectivity.detector_injective_filtration15` 结尾，传入的恰为 `Standard.high125`，检测证据恰为 `source_high_detected`。
3. 对这个实际常量，非零像直接由 `tmf_high125_nonzero` 经 `tmfUnit_agrees` 与 `tmfIso.hom` 的消去得到。

补丁因此删除两个任意检测辅助定理，加入默认私有的

```lean
theorem high125_detector_nonzero :
    Standard.high125 ≫ model.auxiliary.detectorUnit ≠ 0 := by
  rw [←Standard.tmfUnit_agrees,←Category.assoc]
  intro hz
  have hzero : Standard.high125 ≫ Standard.tmfUnit=0 := by
    apply (cancel_mono Standard.tmfIso.hom).mp
    simpa only [zero_comp] using hz
  exact Standard.tmf_high125_nonzero hzero
```

并把唯一消费者改为 `False.elim (high125_detector_nonzero hzero)`。公共 Main 目标不变。该支路只保留 `tmfUnit_agrees`、`tmfIso`、`tmf_high125_nonzero` 及固定对象构造的真实传递待补；不再使用经典分离性或相同检测代表唯一性。

这只移除 `classical_filtration26_zero (a-b)` 那次调用，不涉及 `high_nonzero_survival` 内的另一次调用。

## 仍然缺少的事实：high125 不是奇挠

现有尾部页计算与更正后的上游分离性，只能从 `high125 ∈ F26` 得到

```lean
KIP126.AdamsSynthetic.IsOddTorsionMap Standard.high125
```

即 `∃ n : ℕ, Odd n ∧ 0 < n ∧ n • Standard.high125 = 0`。

现有

```lean
Standard.tmf_high125_nonzero : Standard.high125 ≫ Standard.tmfUnit ≠ 0
```

只能否定 `high125 = 0`，不能否定其为非零奇挠。后复合是加法同态，所以奇挠只能推出其 tmf 像仍被同一个奇数消去；未给出该 tmf 像必须为零的理由。

源码与 API 搜索未发现以下任一可直接应用的公共事实：

- `¬ IsOddTorsionMap Standard.high125`；
- `Standard.high125` 的 2-primary 阶数见证；
- `kappaBar` 或 `wClass` 的 2-primary 阶数/乘积消去关系；
- tmf/detector 在 125 次同伦的奇挠消去或 2-local 性；
- tmf 单位映射杀掉该球谱度数的全部奇挠；
- 该具体 highClass 的全页无 incoming differential / 永久非零事实。

`tmf_finiteModTwoType` 只约束 mod-2 同调有限型，不能推出没有奇挠；`tmf_convergence` 是 E∞ 与 associated graded 的比较，也不提供滤过分离性。`HomotopyTwoLocal` 的定义虽存在，但没有对这里 tmf 或 detector 的实例定理，而且普通 integral tmf 不能凭名字当作 2-local tmf。

`Computation.Standard.high_e5` 明确只给 E5 非零及该页分量穷尽。`source_high_detected` 给永久 cycle，但不保证其 E∞ 类非零；它仍可能成为更晚 incoming differential 的边界。这两条事实合起来仍不自动给 `NonzeroSurvival`。

精确的最小元素事实为 `¬ IsOddTorsionMap Standard.high125`。例如真实证明下面较强事实即可关闭缺口：

```lean
∃ k : ℕ, (2 ^ k : ℕ) • Standard.high125 = 0
```

再结合 `tmf_high125_nonzero` 推知该元素非零，利用奇数与 2 次幂互素可排除奇挠。这里没有提供或新增该事实；它需要来源及实际证明，不能把它登记成未经批准的新责任或塞进 Main 公共前提。

## 任意检测代表的区别只落在无限滤过内

原 `high_detected_choice_unique` 的前半段是有效的：相同 E2 label 给相同 E∞ 类，故 `a-b ∈ F26`。现有尾部计算再推出所有滤过中的成员关系，因此更正后的上游仅给 `IsOddTorsionMap (a-b)`。

若想把原支路改成 detector images equality，仍至少缺少

```lean
∀ c : HomotopyGroup (C := Spectrum) 125 SphereSpectrum,
  IsOddTorsionMap c → c ≫ model.auxiliary.detectorUnit = 0
```

或仅对真实 `a-b` 的更窄结论。现有接口没有该结论。

抽象说明而非固定球谱反例：取群 `A = Z/2 ⊕ Z/3`，令 `F25=A`、所有 `Fs (s≥26)=Z/3`。`(1,0)` 与 `(1,1)` 在关联分次完全相同，但不相等。若 detector 映射取恒等，它们的 detector 像也不同。此模型只展示 associated-graded 数据的逻辑边界，不宣称完整满足项目固定谱对象或给出实际 π125 反例。

## 建议整合顺序

先由唯一 Main 写入者核对哈希并整合附带局部补丁，以移除不必要的任意代表唯一性。将 `classical_filtration26_zero` 能真实证明的内容改记为奇挠尾部，但保留 `high_nonzero_survival` 的上述阻塞；不要保留错误旧结论、增加 sorry 或以背景的其他待补导出 False。若需要继续完成 Main，协调者应安排实际 source theorem 研究或对精确缺口作独立接口审查；本交付未改变责任边界。
