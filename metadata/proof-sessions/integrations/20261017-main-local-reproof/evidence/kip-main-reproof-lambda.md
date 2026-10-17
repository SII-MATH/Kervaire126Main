# Main 实际 λ 核重证交付

协议：`/root/.agents/skills/kip-upstream-session/references/protocol.md`。当前任务只写生产 `KIP126/Main/Internal/Choice/LambdaInjectivity.lean` 与 `KIP126/Main/Internal/Theta/RealizationKernel.lean`；没有新增公理、sorry、待补责任、公共假设或改变固定对象。未执行共享 Lake 构建。

任务开始 SHA-256：

- Choice/LambdaInjectivity：`5812a67b266ed51b9d53372cbfae03b8d32ea41f53cdda29fb49806e48aebebc`
- Theta/RealizationKernel：`509e694034b70f197c4ef2c284b35eb17afb21d2abe3d75a2784ce1b8bef3ae7`

## 已实际完成

`nu_lambda_injective_from_source` 已由实际 cofiber 长正合列重证：λ 核来自 `[S^(m+1,wt−1), CλνX]`；第一商坐标恰为 `(wt−m−2,wt−1)`。`NoOutgoingAt` 将每个该坐标 E₂ 类提升成永久 cycle，`selected_permanent_lift` 给出同一 νX 上的实际第一商 lift，因此 cofiber connecting 为零。第一商 shift0 的同构、真实 quotient maps 的复合/自然性和坐标强制转换均实际校验。没有使用任意 E∞ 注入推出未截断同伦注入。

原错误泛型 `selected_homotopyMap_injective_of_eInfty` 已删除。原 `nu_lambda_injective_from_source` 和 `nu_lambda_powers_injective_of_source_halfplane` 的消费类型保持。保留了同模块其他证明所需的 `paper_boundaries_step` 等合法辅助。

为 F9 实际核证明复建了私有：

- `lambda_shifted_finite_high_filtration_zero`：由 `essShift.filtered` 的 actual ambient/level 同构逆运输后使用公共有限商高滤过消失。
- `lambda_boundary_no_return`：源是同一 νX 的 `(1,−q)` shift，目标是实际 Cλ^qνX；源的 E∞ 低滤过窗为零，将实际 sphere 类推到目标 finite window 上方后由有限商消失判定 image 为零。
- `lambda_quotient_maps_equal_on_spheres`：同一有限商上两填充若在 incl 上一致，其差由 cofiber proj 分解；前一 no-return 给 sphere 评价相同。
- `lambda_first_quotient_delta_evaluation`：TR3 比较 actual cofiber 与 chosen finite λ–ρ–δ triangle；填充 c fixes incl，由上一引理证明 c 在 sphere maps 上等于 id，得到 actual δ evaluation。没有把不同 δ 当作定义相同。
- `lambda_zero_shift_delta_evaluation`：通过同一 shift0 iso 的实际 quotient functor、tower δ naturality、proj/incl naturality 将比较运输到 `nuZero model X`。并非更换模型或 source 对象。

这些辅助及完整实际 Choice 文件均已 `lake env lean -o /tmp/kip-main-lambda-olean/KIP126/Main/Internal/Choice/LambdaInjectivity.olean KIP126/Main/Internal/Choice/LambdaInjectivity.lean` 检查成功（exit 0，require_escalated）。该输出树专供下游独立验证，未写 `.lake/build/`。

## 已完成 F9 特例及 realization-kernel 降阶

`lambda_kernel_zero_from_filtration9` 的真实输入是同一 `a : BiHom 62 w (Σ^(0,−1)νS)`、`w≤69`、`a∈F9`、`a≫λ=0`。以下每步已拼成完整证明并实际类型检查：

1. 正合 cofiber triangle 给第一商原像 `b : BiHom 63 w CλνS`，它的 actual connecting 恰为悬移后的 a。
2. 将 a 后合成实际首商 inclusion 的 `(0,−1)` shift；真实 `model.convergentMap` 保持 F9。通过 `essShift.filtered` 的 inverse ambient/level 同构，将其送回同一 unshifted `CλνS` 的 `(62,w+1)`。由于 `1≤62+9−(w+1)`，公共有限商高滤过消失给该实际 projection 为零。
3. 通过同一 shift0 iso 及 proj/incl 自然性，把 b 的 projection 零运输到 `Cλ(nuZero sphere)`。第一商标签满射给经典 x，坐标为 `(w−63,w)`。
4. `route_actual_boundary_d2_zero` 使用 `bhs_bockstein` q=1。其存在性原像因 `rho_id` 被唯一识别为给定 b；实际 δ evaluation 由前述已经证明的 TR3/no-return 结论提供，故 Bockstein label 为零，得到同一 x 的 d₂ 为零。并未将不同 δ 当作定义同一。
5. 公共 `PageThree.reachesPage_iff_d2_eq_zero` 给 x 到达 E3；已证 `stem63_no_late_differentials` 适用于 `w−63≤6`，使所有 r≥3 outgoing 为零。公共 `isPermanentCycle_of_reachesPage` 给同一 x 的永久 cycle（允许其成为 boundary，不偷加非零）。
6. 现有 `selected_permanent_lift` 给同一 νsphere 上首商类的实际 lift，cofiber connecting 因而为零；shift0 iso 与 ordinary suspension faithful 性给原 a=0。

原泛型 `selected_homotopyMap_kernel_zero_from_f9` 及只为它服务的 `high_lambda_eMap_injective` 已删除。没有用任意 f 的 E∞ 注入假装未截断核分离。

`lambda_kills_realization_kernel_62_71` 的名称、完整类型、指定 sphere 对象与 λ 结论保持原样；原有 restriction/strong induction 降阶现在消费上面**实际** F9 λ-kernel 特例，故整条 realization-kernel 降阶已重新闭合。该引理可继续被选定 b 的阶二构造消费，证明依赖中没有 b 阶二、Toda 非空或该 realization-kernel 自身的循环。

## 传递依赖与责任边界

| 局部证明 | 消费的既有上游 |
| --- | --- |
| 第一商标签与永久 lift | 同一 `model.firstQuotient`、quotient functoriality、`selected_permanent_lift` |
| λ-kernel cofiber | 实际 `XModLambdaN.cofiberTriangle_distinguished`、triangulated coyoneda exactness、实际 shift 同构与 faithful 性 |
| shifted finite high-filtration | `essShift.filtered`、实际 convergent map、公共 `finite_high_filtration_zero`（传递依赖修正后的有限商 `synthetic_homotopy_separated`） |
| no-return / actual δ | ν E∞ window、上述 finite high-filtration、TR3 complete distinguished triangle morphism、真实 quotient tower naturality |
| F9 Bockstein / permanence | `bhs_bockstein`、`rho_id`、上面 actual δ、现有 Main stem63 计算、公共 PageThree/Permanence |
| 最终 realization-kernel | `selected_realization_kernel`、coherent λ restriction 与上面 F9 特例 |

上述 `selected_permanent_lift`、`bhs_bockstein`、`selected_realization_kernel`、底层 fixed model 结构和有限商分离性等仍含原登记的 producer 待补；这里完成的是 Main 真实消费证明，不声称这些传递上游责任已消除。没有新增生产假设/待补。

## 实际验证

- `/tmp/kip-lambda-helper.lean`、`/tmp/kip-lambda-no-return.lean`：私有实际 cofiber/firstQuotient 与 finite no-return/TR3/shift0 δ 辅助分别独立检查通过。
- Choice 完整实际源文件：`lake env lean -o /tmp/kip-main-lambda-olean/KIP126/Main/Internal/Choice/LambdaInjectivity.olean KIP126/Main/Internal/Choice/LambdaInjectivity.lean`，最终 session12222 **exit0**。
- `/tmp/kip-main-bockstein-d2-route.lean`：独立报告员构造并实际检查 Bockstein q=1/公共 PageThree 永久助手 **exit0**；已在 Main 私有范围整合，hδ 参数由前述实际 TR3 比较完全消除。
- `/tmp/kip-theta-realization-full.lean`：完整 realization-kernel 候选检查 **exit0**（session53625）。
- Theta 完整实际源文件：`lake env bash -c 'export LEAN_PATH="/tmp/kip-main-lambda-olean:$LEAN_PATH"; exec lean -o /tmp/kip-main-lambda-olean/KIP126/Main/Internal/Theta/RealizationKernel.olean KIP126/Main/Internal/Theta/RealizationKernel.lean'`，最终 session49226 **exit0**。保留一条非阻断 linter warning（`ext <;> dsimp <;> omega`）。此前尝试仅为消该 warning 而改写战术产生 snd goal，已恢复经验证原战术并重新实际编译成功；没有放宽检查。
- 所有 Lean 命令均 require_escalated 使用固定工具链，只输出 `/tmp`；overlay 中其他 KIP126 产物为只读符号链接镜像。生成两个实际目标输出前已确认它们不是指向共享缓存的符号链接。
- `git diff --check` 及 assigned files 内 `sorry|axiom|synthetic_homotopy_separated|False.elim` 搜索：通过/无命中。
- 未运行共享 `lake build`、source inventory 或公共导出锁刷新；由协调者统一执行。两个局部模块检查通过不等于整个 Main 或项目已最终通过。

## 最终源码

- `KIP126/Main/Internal/Choice/LambdaInjectivity.lean` SHA-256：`b81366348b59acc32aa35f203a231d522c13819421bcd74d59a8b7c3fd5b7813`
- `KIP126/Main/Internal/Theta/RealizationKernel.lean` SHA-256：`c1e39f6940fba0be3fc370214bdc40a6ab1b97f7deb15a9fd2429f1d5eebba17`

局部补丁：`/tmp/kip-main-reproof-lambda.patch`（只含分配的两文件）。

实际工具返回记录：`/tmp/kip-main-reproof-lambda-validation.json`（按会话实际返回抄录，未假装为共享构建日志）。
