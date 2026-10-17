# 实际 ν/球无限滤过中的 λ-torsion 消失：已检查私有补证明

构造者：`/root/main_interface_report`，2026-10-17；协调者本轮明确派发只写 `/tmp` 的证明任务。**本轮已参与候选构造，不再是该新候选的独立审查者。** 先前独立 Main 接口报告不因此改写批准状态。

## 已交付

- `/tmp/kip-main-infinite-lambda-kernel.lean`，325 行，无新增 sorry/axiom/公共接口/登记责任。
- 源文件 SHA-256：`9d749e787aac8f4df9f0a9bf1292d6899e7f6a9c2fc17b75af79a87df08dc11e`。
- `/tmp/kip-main-infinite-lambda-kernel-validation.log`：完整 bare Lean 检查 exit 0。
- `/tmp/kip-main-infinite-lambda-kernel-audit.lean` 与 `-audit.log`：同源另加六项 `#print axioms`，检查 exit 0。
- 另此前给 downstream 的 `/tmp/kip-main-bockstein-d2-route.lean` 已修正、实际 exit 0，包含 `route_actual_boundary_d2_zero` 和 `route_permanent_of_d2_and_no_late`；它们不是本新证明所需的额外假设。

精确检查命令：

```sh
/root/.elan/toolchains/leanprover--lean4---v4.32.2/bin/lake env bash -c \
  'export LEAN_PATH="/tmp/kip-main-lambda-olean:$LEAN_PATH"; exec lean /tmp/kip-main-infinite-lambda-kernel.lean'
```

以 `require_escalated` 执行，未给 `-o`，未写共享 `.lake/build`。overlay 是 downstream 的真实临时 Main Choice 编译树；普通公共依赖按固定工具链和现有缓存读取。会有无关数学的 linter 提示，不影响 exit 0。

## 最终精确声明

```lean
private theorem nu_infinite_filtration_lambda_torsion_zero
    (X : ClassicalObject) (m w : ℤ)
    (a : BiHom m w (model.nu.functor.obj (X.obj model.auxiliary)))
    (ha : ∀ s : ℕ, FiltrationAtLeast model.syntheticTower s a)
    (ht : ∃ k : ℕ, lambdaMultiply k a=0) : a=0

private theorem sphere_infinite_filtration_lambda_torsion_zero
    (m w : ℤ) (a : BiHom m w (S_0_0 : SyntheticSpectrum))
    (ha : ∀ s : ℕ, FiltrationAtLeast model.syntheticTower s a)
    (ht : ∃ k : ℕ, lambdaMultiply k a=0) : a=0
```

这不是原 unrestricted separation，不能用它消去 ordinary 奇挠。真实 λ-torsion 条件不可省略。High125 对实际阶二 η-products，先由另一个 worker 的已检查桥把其 realization 判为 odd，再用阶二排除该 odd realization，`selected_realization_kernel` 给 ht，最后本引理关 a；该桥不在此文件中。

## 证明链

1. `route_common_cycle_of_finite_cycles` 对任意实际 `SSData (ModuleCat ℤ)`：若同一个初始页类 x 在每个有限 Z_n 有代表，则有共同 Z∞代表。固定 Z_0 代表 z₀；每个 z_n 与 z₀ 的差由初始 pageπ_0 的 kernel识别落在 B_0。`B_0≤B∞≤Z∞≤Z_n`，故同一个 z₀ 的实际 ambient像在全部 Z_n 中。`Z_top_greatest`（对子模块 span）给共同 Z∞。没有误用“不同代表可以自动一致”、有限维或严格性。
2. `route_permanent_of_all_reaches` 用公共 `ProofTools.isCycle_iff_reaches` 逐页取得这些代表，并严格运输初始页 index `↑(2−r₀).toNat=0`，得到同一个 `ClassicalPermanentCycle`。
3. `route_invisible_lambda_kernel_nuzero`：a 的 actual λ map复合零，由 actual cofiber shifted coyoneda得到 c∈Cλ(nuZero X)。假设 a 在每个实际 shifted有限商投影都零。对每 n，Main Choice 已重建的 `lambda_zero_shift_delta_evaluation` 把 finite triangle T(1,n+2) 的 δ(c) 识别为 actual boundary后 finite quotient投影，故 δ(c)=0。三角正合性给同一个 c 在 Cλ^(n+2) 的 restriction lift；必须使用 `triangle_rho`，没有把 triangle.rho 当 definitionally同一个 tower.rho。
4. 公共 `bhs_finite_lift` 把这些实际 lift变为同一首商 E₂标签的全部有限页 reachability。第二步给永久类；公共 `selected_permanent_lift` 给 c 实际 lift至 nuZero X，因此 actual connecting为零，a=0。
5. `route_invisible_lambda_one_zero_nuzero` 通过 λ 自然性、实际 source shift同构与其 fully faithful 把 `lambdaMultiply 1 a=0` 化为第三步，所有有限商不可见性由 functor.map传递，无滤过提升假设。
6. 复用 high125 worker 已检查的通用 `lambda_multiply_compose`，对 λ-torsion 指数归纳；用显式分次零元 HEq运输处理 `w−k−1` 与 `w−(k+1)`。从而任何所有有限商不可见且 λ-torsion的 nuZero类为零。
7. 无限滤过的 νX类投影到每个 finite quotient后仍无限滤过，使用**已批准、已登记**的 finite-quotient separation把每个投影消去。经实际 shift0同构到 nuZero应用第六步，再经同一个 ν-unit iso得到球版本。

Prüfer可除 torsion抽象模型不满足这里的 BHS“永久标签实际 lift”承诺，因此不与本结果矛盾。这个附加真实结构是此前单纯“有限商分离+torsion”推论缺失的关键。

## 实际依赖与边界

直接调用的既有公共 producer包括：

- `Literature.Standard.bhs_finite_lift`；
- `Literature.Standard.selected_permanent_lift`；
- `AdamsSynthetic.Standard.synthetic_homotopy_separated` 的**有限商**版本；
- fixed background / first quotient / actual λ-cofiber / model.convergentMap与ESS相关结构。

同模块 Main私有操作：`Choice.nu_first_quotient_label_surjective`、`Choice.lambda_zero_shift_delta_evaluation`、`Selected.shift_assoc_inv`（通用λ组合用）。Choice δ helper通过 finite no-return已独立实现；没有消费未截断球分离或 Main最终目标。`Selected.LambdaOperations` 只导入 Main.Conditions，不循环到 High125。

`#print axioms` 实际结果：最基础 `route_common_cycle_of_finite_cycles` 仅 `[propext, Classical.choice, Quot.sound]`；模型特化及最终两个消失声明仍有 `sorryAx`，来自上述既有背景和上游 pending producers。本交付只完成 Main局部推导，不宣称填完上游全部构造。没有新增直接 sorry，没有把生产的 pending状态改为 completed，也没有靠目标本身/False.elim证明。

## 交接

已把源码、精确命令、exit0和依赖发给 `high125_local_repair`。该 worker独占 `High125/Filtration.lean`，负责生产整合。文件已经复制通用λ组合的一组 private `lambdaAt`、`lambdaAt_heq`、`multiply_heq`、`lambda_multiply_compose`；整合它与桥代码时应保留唯一版本，避免重名。测试/元数据/完整 Lake/推送与 Release缓存均由协调者安排，本构造者未执行这些动作。

无需本候选新增公共接口、人审批准或待补责任。若需要独立审查新候选，应另派未参与本构造者，不沿用本人的旧报告独立身份。
