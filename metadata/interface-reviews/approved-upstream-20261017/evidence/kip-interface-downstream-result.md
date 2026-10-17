# 下游接口适配交付

基线：`2c703812db7edb830b995c53e9fe648747a66429`。独占写入范围仅 `KIP126/ProofTools/`、`KIP126/Main/`；未修改测试、metadata、接口锁、其他模块或共享构建输出。

## 已完成的真实适配

1. ProofTools 6 个原分离性调用全部改为有限 λ 商接口。
   - `Filtration.finite_high_filtration_zero`：未取商对象 `.nu X` 加实际 q。
   - `HSource.shifted_first_detection_unique`：未取商对象 `.shift (0,e) (.nu X)` 加实际 1。
   - `MayCorrection.finite_cycle_image_correction`：未取商对象 `.shift (0,b) (.nu X)` 加实际 i。
   - 另外 3 个 shifted-finite 调用：`Filtration.shifted_finite_high_filtration_zero`、`SphereMayCorrection.shifted_nu_to_shifted_finite_no_return`、`OctahedralPullback.shifted_finite_no_return`。它们使用新增**私有** `homotopySeparated_shift` / `shifted_quotient_homotopy_separated`：通过现有 `essShift.filtered` 的实际 ambient/level 同构将无限滤过逐层逆运输到同一个未 shift 的有限商；运用新分离性后由 ambient.inv 单射回到原元素。不是只凭对象名称替换。
2. Main 的 choice-square 不变性已避免任意 θ 的阶二结论：
   - `ChoiceIndependence.lambda_eta_theta_square_independent` 的 θ' 本来就是 BX，直接使用现有 `bx_order_two`。
   - `Choice/Invariance.theta5_square_nonzero_detection_invariance_of_pages` 对 θ 与 θ' 分别同 BX 比较，借 `bx_order_two` 和原有 F6 差异得到各 square−BX² 属 F12，再用子模减法得到两平方差属于 F12。保留所有原公共声明。
3. Toda 路线的 theta 阶二改成**私有辅助**的显式真实参数，唯一实际调用 `SectionSeven/NuTarget.target_nu_divisible` 传入 `bx_order_two`。`theta5_square_nonzero_detection_choice_equivalence` 和其他公共 Main 目标未加任何假设。
4. High125 私有支路已收窄到实际对象：删除没有独立数学依据的 `high_detected_choice_unique` 和泛型 `high_detected_detector_nonzero`；新增私有 `high125_detector_nonzero`，直接用同一 `tmfUnit_agrees`、`tmfIso`、`tmf_high125_nonzero` 推出固定 high125 的 detector 非零。`Injectivity` 的唯一实际调用本来就是 high125，现在直接消费该特定结论。没有改公共接口，仍保留 `high_nonzero_survival` 对固定 high125 非奇挠的实际阻塞。
5. `Choice/OrderTwo.lean` 中不再有消费者的任意 `theta_degree_order_two` 及其专用辅助已删除，保留被其他文件使用的实际 `realization_additive`。由此去掉其错误地对任意 realization 使用无条件 `stem62_exponent_two` 的链。

## 仍然阻塞的 Main 数学事实

本补丁**不是完整可构建的最终接口迁移**。保留下列原调用点，不填新 sorry/公理、不恢复错误 universal 接口，也不把条件加到公共 Main 目标上。

- `Internal/Choice/LambdaInjectivity.lean:97`：任意 selected X/f 上 E∞ 注入推出实际 homotopy 注入。现证明把核推入每个滤过级，但新接口只控制有限商。泛型原辅助本身对普通对象过强；实际使用是 `.shift (0,-1) (.nu X)` 上 λ 的核，需真实 λ-torsion 无限滤过分离性或直接 λ-kernel 局部判定。不得把全称 false separation 改名后重用。
- `Internal/Theta/RealizationKernel.lean:124`：F9 内 λ-kernel 零，域实际为 shifted νsphere。有限商分离性尚不能从当前代码直接运输到未截断核；缺少严格滤过提升/λ-torsion 排除无限奇挠的具体比较。
- `Internal/LowEta.lean:75`：未截断 sphere 的 `(1,3)` 零结论。当前证明只知所有 E∞=0，从 associated graded 本身不能推出元素零。需要真实该度数 synthetic 计算或正确的区域分离性。
- `Internal/High125/Filtration.lean:76`：未截断 sphere 的 `(125,130)` F26 零结论，同样缺少排除无限滤过的真实局部事实。
- `Internal/High125/Filtration.lean:126`：普通 π125 的 F26 零结论，新上游只推出 `IsOddTorsionMap a`。当前消费者只剩 `High125/Source.high_nonzero_survival` 的特定 `Standard.high125`。原任意相同检测 a−b 分支已按实际消费删除。即使 tmf 像非零也不能自动排除其为奇挠；仍需 `¬ IsOddTorsionMap Standard.high125` 或真实该元素的 2-primary 消去见证，现有公共接口搜索没有找到。
- `Internal/Theta/OrderTwo.lean:59`：任意 `b : BiHom 62 70 S` 的 realization α 尚无 2-primary 证明。实际 Toda 只需为 `.b` 选择一个阶二 lift，但原 `sphere_permanent_first_quotient_lift` 只给检测，不给其积分 2-primary 性。`bx_order_two` 处理 θ 而非 b，不能代替。需实际选择阶二 b 并证明检测，或证明这个 b 的 realization 满足修正后的 `stem62_exponent_two` 前提。

这些局部事实尚无 Lean 反例，本交付不声称各具体区域目标为假。只是现有接口/源证明的逻辑断点。没有创建新未证责任或改变公共对象关联。

## 实际验证

- `/tmp/kip-shift-separation.lean`：只导入普通公共入口 `KIP126.AdamsSynthetic.ESSShift`，完全泛型的 `Model C Syn` 和显式 `SyntheticESSShiftComparison`/separation 参数；最终命令 `lake env lean /tmp/kip-shift-separation.lean`（require_escalated，未指定 -o）**exit 0**。它实际类型检查了整个 level/ambient 逆运输证明，未借固定 Standard 对象的 sorry。
- `/tmp/kip-high125-detector-probe.lean`：只导入 Mathlib 的泛型预加范畴，检查新 high125 detector 引理同样的 `tmfUnit_agrees` 重写和 `cancel_mono` 推导；`lake env lean /tmp/kip-high125-detector-probe.lean`（require_escalated、未指定 -o）**exit 0**。不以项目固定待补定理做假反证。
- 首个尝试导入 ProofTools.Laws 的临时检查因现有缺失 `Standard/ClassicalSupport.olean` 而失败，随后改为上述更小公共 import 验证，不是清缓存或放宽数学检查。
- `git diff --check -- KIP126/ProofTools KIP126/Main` **exit 0**。
- 未执行任何 `lake build`，未写 `.lake/build/`。完整实际模块编译、source inventory、公共导出/类型锁与 Trust 检查由协调者单进程执行。Main 仍保留上述失败点，不能报告全项目通过。

仍使用的传递上游待补：有限商 `synthetic_homotopy_separated`、`essShift.filtered` 等 shift/convergence 结构、原 E∞ 比较，以及 Literature 的 `bx_order_two`、BX 标定/检测、`action_filtration`。局部真实证明不等于这些待补已完成。

## 基线与交付源码哈希

| 文件 | 基线 SHA-256 | 交付 SHA-256 |
| --- | --- | --- |
| `KIP126/Main/ChoiceIndependence.lean` | `0db94baeddfa638a570f3acbc329407e17e237cfd50f13496e6b3e1872467aba` | `4094efc10e5b05faba803648e3f98a4ce8696b045f8a6fb7179e0163225820be` |
| `KIP126/Main/Internal/Choice/Invariance.lean` | `3d95910ada61d47265e5563cc15a1b214f97e8e8bbc1729631b82bede0362a01` | `92856f6d5b0ce04f4e1d3875e347d12f10d22a34a0fa5617c58b4f49873cb1cb` |
| `KIP126/Main/Internal/Choice/OrderTwo.lean` | `73f209f89ac62ebec27b2bb0443cdf8dbceb9c651ace35361cc1df980242bb7d` | `36d1dbdf573cf420c7fb78560fd7b0bc807430c8472d5ed0dc83080040ac20af` |
| `KIP126/Main/Internal/High125/Injectivity.lean` | `32d6476fec0fc8ac68152d7f86e8a8ec3a4a5c809dd865c67aa001a9f40d36f7` | `a311839e3c457b7e24160ea734a5a3f9d61d8153eb1a09363e129fd724fdbff9` |
| `KIP126/Main/Internal/High125/Source.lean` | `8e388410bb8ab3e73c735462e4e5c60219eddd6fedf78d69e6615c697e1227ba` | `183e7a9bf4ea394a526c83986d0b0318e971737e738a872e3d4731f80b87a82a` |
| `KIP126/Main/Internal/Theta/TodaExistence.lean` | `8071d5efa44940249ace4e7d52fe77f243839455a58051ec030ba4ed3183f591` | `dd8f32586841c6ca4040ce97d14d2d7d8d02664d58e94b1bab5cea032c23ef0e` |
| `KIP126/Main/SectionSeven/NuTarget.lean` | `120acb2a156b3a9196cec874bfea5a3ffe2e37edb9fa44c2c6edebcd9e05b2ad` | `c768d01ececdfb7f3f1797fd53640324f26094f8bb665270c0994b29a5d844fe` |
| `KIP126/Main/SectionSeven/ThetaToda.lean` | `7f275f7f43e967074f6ab0840bbedd309582dfe0b374056e4b15672410e331f9` | `bbc942b9141b1aa1f3bab2926da945e2f751cb55076701df50ed3ca15fac4298` |
| `KIP126/ProofTools/GeneralizedMahowald/Filtration.lean` | `b565084919c083740b423cfdd04760ff4416e5d8c62b3f6f27dd2a908c80be93` | `54f61c7307af0f7b887137c1d16faaf0c0bc73f9c84d6963fcdfde5c0d45598b` |
| `KIP126/ProofTools/GeneralizedMahowald/HSource.lean` | `1c555391e7df56302a381725dd8994ba14abb067ec60437bbb62ba46dc79c3ab` | `bc9873ea098069c368c57fbfcbee0fa3b8be1699c16b17e09af64abcc053b774` |
| `KIP126/ProofTools/GeneralizedMahowald/MayCorrection.lean` | `56733d6ae5e514a8e1684d2bc378099ff540c73486a9e67177e28a6cdcf6c3de` | `4a15a2e989e0a63af90e7e3b781dfb9e3ebd726f0b05cbde73caf3a294b384fd` |
| `KIP126/ProofTools/GeneralizedMahowald/OctahedralPullback.lean` | `8d10546c24560a30db8d648194e079e4df7789b4642a2e982311f235f313e570` | `0f28af19433fde05db82a5dd2d8f715e872dde98eb6c981c9ff947b64164a17e` |
| `KIP126/ProofTools/GeneralizedMahowald/SphereMayCorrection.lean` | `cb2eaa9aaeabafe95da880076e5f4811d3df461ab1967fdafd59d208b45716bc` | `232d78c5b0cd24d816b3e5ce2c1eb0b11c67a7c564c8bb3c2a61358f05dd5aca` |
