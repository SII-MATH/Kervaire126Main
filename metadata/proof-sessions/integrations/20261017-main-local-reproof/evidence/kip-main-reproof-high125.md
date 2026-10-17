# Main High125：修正接口下的真实重证

## 范围与基线

独占 `KIP126/Main/Internal/High125/{Filtration,Source,Injectivity}.lean`。协议 `/root/.agents/skills/kip-upstream-session/references/protocol.md`。未新增 sorry、公理、待补责任或 Main 公共前提。构建输出只写 `/tmp`；共享 Lake 编译由 root 调度。

本轮开始的 SHA-256：Filtration `9afc54c92e4a799086d0cd491428b65a9e6a51dabf7aaf6d69d8a6f39cbc30ba`；Source `183e7a9bf4ea394a526c83986d0b0318e971737e738a872e3d4731f80b87a82a`；Injectivity `a311839e3c457b7e24160ea734a5a3f9d61d8153eb1a09363e129fd724fdbff9`。

当前冻结给 root 的生产 Filtration SHA-256 为 `a449d7e6e9141cd470b9588824cb1b6aed7de3816f0808e3d023dc040da15dd0`。

## 已完成并整合的真实证明

### 1. 高125尾部的精确结论

- `synthetic_filtration26_infinite`：实际 synthetic 球的 `(125,130)` 元素属于 F26，则属于所有非负滤过。
- `classical_filtration26_odd_torsion`：普通球的 125-stem 元素属于 F26，则是奇挠。旧的全称普通球 F26=0 不再保留。
- `synthetic_filtration26_zero (a) (haF26) (h2 : a+a=0)`：在真实阶二元素域上完整证明 F26=0。没有假定任意普通或 synthetic 元素没有奇挠。

前两条使用已有有限页计算、vanishing line 和相应 E∞ 比较；经典奇挠结论继续真实依赖上游 `finite_map_separation`。

### 2. 从无限 synthetic 滤过到 realization 奇挠

默认私有 `infinite_realization_odd` 对任意球的双次数 `(m,w)` 证明：

```lean
(a : BiHom m w S)
(ha : ∀ q : ℕ, FiltrationAtLeast model.syntheticTower q a) :
IsOddTorsionMap (Standard.realizeSphere m w a)
```

证明不增加 realization 塔比较。假设 realization 不是奇挠，用现有 `finite_filtration_of_not_odd` 得到实际 ordinary sphere 上精确滤过，再用 `nonzeroClassicalDetection_of_exact` 得到实际经典非零永久类及检测。由原 `selected_realization_prescribed_lift` 取得同一 realization 的 synthetic lift。把 a 与该 lift 都降低到共同权，差的 realization 为零，原 `selected_realization_kernel` 给某 λ 次幂相等。左端仍无限滤过；右端在任意有限权窗都有非零 E∞ 检测，与无限滤过矛盾。

其中已分别证明并验证：普通 map filtration 与实际球同伦滤过的转换；经典永久非零类在任意有限页存活；其不属于任意有限 boundary；因此其任意有限 synthetic 权窗的 E∞ 类非零。没有把普通 E∞ 与有限权窗 E∞ 混同。

### 3. 从有限 λ 商分离性消除无限滤过的 λ-torsion

与独立 worker `main_interface_report` 的实际补证串行整合。对固定 νX 的元素 a，先证明其所有有限 λ 商像为零；若 a 又被 λ 杀掉，用实际首商 connecting map 给同一个 c。所有有限商像为零，迫使这个同一个 c 在任意有限 λ 长度都可提升，因此其同一个 E2 标签到达任意有限页。直接用 `Z∞=⋂Zr`、`B0⊂Z∞` 证明该标签有共同永久 cycle，再由原 `selected_permanent_lift` 将 c 提升到未截断 νX，故 connecting map 为零。随后按 λ-torsion 指数归纳。

得到默认私有：

```lean
sphere_infinite_filtration_lambda_torsion_zero m w a ha
  (ht : ∃ k, lambdaMultiply k a=0) : a=0
```

这里使用的是有限 λ 商上的上游分离性，未恢复错误的未截断分离性。归纳所需 generic λ 组合 `HEq (λ^n(λ^k a)) (λ^(k+n) a)` 由原 biShift/λ coherence 实际证明。

### 4. 阶二无限滤过元素为零

将第2条的 realization 奇挠与 `a+a=0` 合并，由奇数与2互素得到 realization 为零。原 realization-kernel 定理给 λ-torsion，再用第3条消去 a。这个通用默认私有结果 `sphere_infinite_two_torsion_zero` 关闭第1条的实际阶二高125尾部。

### 5. 最终实际元素均为阶二，框架无需预先永久非零

生产 Injectivity 中已证明：`eta_order_two`（由原 `toda_h0_eta`、`toda_lambda_h0`、λ coherence），继而任意 η 乘积及两个 η 乘积之差均为阶二。故 DifferentialCriterion 的两个 bx η-square 消费和 ChoiceIndependence 的一个 η-error 消费都能给出真实 h2。

`high_frame` 已改从 `source_high_detected` 直接取得永久 cycle，与 E5 框架拼接。它不再依赖 `high_nonzero_survival`。

## 实际验证

以下均运行锁定工具链的 `lake env lean /tmp/...`，没有运行私有共享 Lake build：

- `/tmp/kip-high125-eta.lean`：η、η-product、η-product difference 阶二，退出0。
- `/tmp/kip-high125-frame.lean`：由 source detection 直接得到 high_frame，退出0。
- `/tmp/kip-high125-tail-true.lean`：精确 synthetic 无限滤过尾部与 classical 奇挠尾部，退出0。
- `/tmp/kip-lambda-compose.lean`：generic λ 组合，退出0。
- `/tmp/kip-high125-bridge.lean`：完整无限滤过到 realization 奇挠桥，退出0。
- `/tmp/kip-main-infinite-lambda-kernel.lean`：独立 worker 的完整有限商/永久 lift 核消去，退出0。
- `/tmp/kip-high125-filtration-integrated.lean`：完整生产 Filtration 内容，退出0，仅3条 linter 提示。
- `/tmp/kip-high125-conditional.lean`：显式 hImageNonodd 的完整 source survival 与实际阶二 detector F25/F26 两分支，退出0，仅 linter 提示。
- 生产 Filtration `git diff --check`：通过。

协调者已报告生产 target `KIP126.Main.Internal.High125.Filtration` 共享 Lake 验证通过，共2766 jobs；对应源码是上述冻结哈希 a449...。完整项目构建由 root 运行并记录到 `/tmp/kip-main-reproof-full-build.log`，当前不能宣称完整 Main 或 lake build 已通过，生产 Source/Injectivity 仍等待下述最小上游决定。

完整条件版另保存了实际命令运行日志 `/tmp/kip-high125-conditional-validation.log` 和机器记录 `/tmp/kip-high125-conditional-validation.json`：实际退出码0；条件源码 SHA-256 `c0d7176185edf348511c9c6dde00f4198aacd938e6428a9b534b25d72a8e3475`，原始日志 SHA-256 `124d6e550106a3879ac11d5d4bd30effa19a29c72af3bd7aa1aa3322521b8f3b`。该验证仅包含显式 hImageNonodd 的 standalone scratch，不表示上游已提供这一事实。

## 仍等待最小上游接口决定的 F25 分支

目前 `Source.high_nonzero_survival` 与最终 detector 注入的 F25 高类分支仍不能仅从原

```lean
high125 ≫ tmfUnit ≠ 0
```

推出。非零像可能是纯奇挠；即使经典 highClass 永久非零，也不能保证这个指定 tmf 像有非零2-primary部分。原普通球 F26=0 曾掩盖此处的奇挠差。

root 正提交的精确最小候选是加强同一源声明的结论为

```lean
¬ IsOddTorsionMap (high125 ≫ tmfUnit)
```

本 worker 未更改上游声明或接口锁。另在 `/tmp/kip-high125-conditional.lean` 用显式 `hImageNonodd` 验证完整条件版 F25 detector 论证；该参数不进入 Main 公共目标，也不登记为新责任。该完整条件版已实际 Lean 验证退出0；生产 Source/Injectivity 尚未采用未获批的加强事实。

该条件版的思路：先用经典 F26⇒奇挠，排除指定 high125 提升到更高滤过，得到其非零永久存活并使用原 prescribed lift。任意实际 a 的同 highClass 检测与该 lift 相差 F26 元素，其 realization 由第2条为奇挠；若 a 的 detector 像零，则指定 high125 的 tmf 像也是奇挠，与 hImageNonodd 矛盾。另一 F26 分支直接使用真实 h2 和已完成尾部零定理。无需声称任意检测代表唯一或指定 high125 本身已为2-primary。

## 传递依赖

仍真实使用已登记上游待补：实际 fixed model/对象构造、有限-map 分离性、有限 λ 商 synthetic 分离性、BHS `selected_finite_lift`、`selected_permanent_lift`、`selected_realization_kernel`、`selected_realization_prescribed_lift` 与实际 cofiber/首商比较及计算数据。未把这些计为本轮消除的数学责任；未新增责任或以背景不一致导出 False。

## 等待批准后可直接审阅的局部补丁

`/tmp/kip-high125-after-nonodd-approval.patch` 已通过 `git apply --check`，尚未应用。它仅在同名上游声明获准加强后，更新 Source 的 survival 推导并删除无用的任意代表非零支路；将最终私有 detector helper 精确改为 `(a)(haF15)(h2)(hz)`，用 realization 奇挠误差取代旧 high_exhaustion 的代表唯一性。该补丁不提供或新增上游事实，不得在用户决定前把它当作生产已完成结果。
