# 已批准上游接口调整：实现与未闭合消费者

基线提交：`2c703812db7edb830b995c53e9fe648747a66429`。本轮源码与记录尚未提交、推送。

用户在本聊天明确批准：“同意以上提案，修改原接口”；随后对协调者逐项询问明确回复：“允许新增这 1 项待补”。精确授权记录见 [approval.json](approval.json)。后者只涵盖既有 `Literature.Standard.theta5_order_two` 的同类型直接待补，不涵盖 Main 新假设或新待补。

## 已实现的接口变化

| 声明 | 当前接口/实现 | 实际验证 |
| --- | --- | --- |
| `AdamsSynthetic.Standard.synthetic_homotopy_separated` | 增加 `n : ℕ`，仅保证同一选定对象实际 `XModLambdaN (...) n` 的分离性；保留原一项基础待补。 | 固定工具链根构建与实际完整类型捕获通过。 |
| `AdamsSynthetic.Standard.classical_sphere_separated` | 结论改为 `IsOddTorsionMap a`；由已有 `finite_map_separation` 推导。 | 编译通过、无直接待补；仍依赖该上游基础定理的既有待补。 |
| `Literature.Standard.stem62_exponent_two` | 对同一普通球谱元素增加 `∃ n : ℕ, (2^n : ℕ) • a = 0` 前提。 | Literature 根构建及普通消费者完整类型锁检查通过。 |
| `AdamsSynthetic.Standard.graded_compose` | 仅该定义使用 `@[no_expose]`；真实双线性复合及齐次公式补完；原 `._proof_1` 同名、全文类型、宇宙与 kernel 指纹精确保留。 | 普通入口1825项导出精确不增不减，除两项获批分离性类型外全部原类型/宇宙不变。 |
| `Literature.Standard.tmf_convergence` | 恢复已审公开构造，精确增加 `._proof_1` 至 `._proof_19`；不包含额外 equation/congruence 导出。 | 754→773，19项全文类型/指纹/宇宙与获批提案逐项一致；除 stem62 外全部原类型不变。 |
| `Literature.Standard.theta5_order_two` | 名称、完整类型及固定 θ₅ 不变；按用户单独批准登记独立待补证明。 | 新增直接待补精确1项；没有改对象或新增 Main 前提。 |

首商相容性、Computation 可见性和权移封装的旧接口调整备选没有实施。此次仍固定普通源、同一个 ν/recovery 与标准对象，没有切换为完成球谱。

## 已完成的消费者修复

ProofTools 全部6处调用按实际有限商及 shift/滤过同构适配，整个 `KIP126.ProofTools` 根构建通过。Main 的 choice-square 比较改为各自同固定 BX 类比较；私有 Toda 的 θ 阶二条件由唯一实际 BX 调用提供；删除不再需要的任意 θ 阶二辅助和任意 high125 检测代表唯一性支路。Main/ProofTools 没有增加公共前提或直接待补。

默认构建发现仍被 `Theta.NoCrossing` 消费的经典页引理曾随旧阶二论证删除，已恢复这条合法辅助；最终增量构建实际编译 `Theta.NoCrossing` 通过。没有恢复错误的全称阶二结论。

## 待补与信任

直接待补由302降至299：消除经典奇挠推论、复合、齐次公式与tmf构造4项，单独获准增加θ₅阶二1项。当前 AdamsSynthetic 90、Literature119、Computation88、ProofTools2；Main没有直接待补。局部直接责任完成不表示传递基础责任已完成。

实际内部捕获与既有信任审计确认没有项目公理、没有 synthetic sorry。所有原接口/边界/消费/Trust 测试和检查器保留，未改工具链或依赖锁。完整捕获与编译日志见 [evidence](evidence)。

## 最终验证结果

- `python3 scripts/check-source-inventory.py`：通过，当前工作区473项目文件、28消费/审计文件。
- `git diff --check`：通过。
- AdamsSynthetic、Literature、ProofTools公共入口构建：分别通过2668、2723、2815 jobs。
- Literature现有专项测试及内部审计独立构建通过2733 jobs；最终默认构建中的 AdamsSynthetic/Literature/ProofTools 接口检查及内部审计也通过。
- 最终完整默认 `lake build`：**失败**，实际失败目标只有 `Main.Internal.Choice.LambdaInjectivity`、`Main.Internal.LowEta`、`Main.Internal.High125.Filtration`。Architecture/Integration/Main/Trust 汇总受 Main 依赖阻塞，不能声称通过。

## 仍需真实数学修复的 Main 调用

| 位置 | 缺失的实际论证 | 最终编译状态 |
| --- | --- | --- |
| `KIP126/Main/Internal/Choice/LambdaInjectivity.lean:97` | 原泛型 E∞ 注入不足以推出未截断同伦注入。实际 λ-kernel 用例需要正确局部分离性或直接 cofiber/kernel 证明。 | 实际类型检查失败。 |
| `KIP126/Main/Internal/LowEta.lean:75` | 未截断球 `(1,3)` 上的局部消失；关联分次为零不能单独推出元素为零。 | 实际类型检查失败。 |
| `KIP126/Main/Internal/High125/Filtration.lean:76` | 未截断球 `(125,130)` 的 F26 零结论需排除无限滤过核。 | 实际类型检查失败。 |
| `KIP126/Main/Internal/High125/Filtration.lean:126` | 新经典接口只给奇挠。实际剩余消费者是固定 high125；其非奇挠或真实2-primary性质尚无现成公共证明。 | 实际类型检查失败。 |
| `KIP126/Main/Internal/Theta/RealizationKernel.lean:124` | F9内实际 λ-kernel 的零结论需要严格滤过/有限商运输论证。 | 前置 Main 依赖阻塞；由源码审计定位，非已完成编译。 |
| `KIP126/Main/Internal/Theta/OrderTwo.lean:59` | 任意 b 的阶二断言不能保留；实际 Toda 需要选取并证明一个满足检测的阶二 b，或证明该所选 realization 为2-primary。 | 前置 Main 依赖阻塞；由源码审计定位，非已完成编译。 |

没有为这些缺口添加 `sorry`、新公理、Main 新假设或改锁放行。独立数学与接口审查见 [Main作用范围报告](../Main/20261017-primary-scope-after-approved-upstream/report.md)。这份报告的 θ₅单项已获准，其他额外责任/对象变更没有授权。

## 工作区与发布

本轮只归属 `source-changes.json` 列出的17个生产文件及相应 metadata。工作区同时出现另一项 Computation/SourceExpression、其测试、lakefile与对应元数据改动；它们保留原样，未归成本轮源码工作，也未回退。最初未跟踪审查资料与编译产物仍保留。崩溃转储 `core.50` 已按用户要求删除。

完整构建未通过，因此没有提交/推送本轮改动，也没有发布或标记任何 Release 构建缓存。不得把此工作区的未提交/失败构建标记成原基线提交的成功缓存。
