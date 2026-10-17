# 6.20 去掉差集条件：证明 worker 交付

状态：生产候选已通过实际 Lean 类型检查；共享入口、公共锁、消费者测试和完整构建由协调者统一整合。

## 授权与基线

本轮按协调者传达的最新人类授权：在合法早页范围内，去掉源的晚页 cycle-set 排除条件，保留固定原目标 y 和 b=0。未将旧的含差集 crossing 接口改名或修改语义。

- 基线 HEAD：`aad718722aa01dfce361f40645fc776037d1078f`，同时保留本轮之前其他 agent 已有工作树改动。
- 独占生产文件：`KIP126/ProofTools/Paper/ExtensionIndeterminacy.lean`，基线中不存在。
- 生产 SHA-256：`1720fccd565456ad350d489a3da09eacecce316d5d9626077b71e5fdad71c34c`。
- 只新增本文件和本目录 worker 证据；不改共享入口、锁、Tests、其他模块、待补清单或工具链。
- 协议：`/root/.agents/skills/kip-upstream-session/references/protocol.md`。

## 公共声明及完整语义

仅增加两个公共声明：

1. `KIP126.ProofTools.Paper.finiteExtensionCorrectionLabel`：固定未移位商中的 λ^a x′ 标签，经实际 ESS shift 比较和与 quotient inclusion 交换的 cofiber shift 同构，送入同一个 normalized finite source quotient。标为 `no_expose` 以保持结构选择同构私有；普通公共消费者仍可引用标签及后面的定理。
2. `KIP126.ProofTools.Paper.finiteExtension_inessential_iff_shorter`：给定同一 X、Y、f、n、s、t、x、y 的早晚 `FiniteExtensionWitness`，早页不晚于晚页且晚页扩张 essential，早页扩张 inessential 当且仅当存在 a>0、a≤n−e(f)、真正的 Ambient x′∈Z_(rEarly−1−a)，以及其上述 λ^a 标签的 E∞ 代表，在同一早 normalized quotient map 中支持长度 n−a 的扩张到原早页 witness 的 target。

右侧目标只有必要的 degree transport，绝不替换为任意 y′。短源坐标写成 `(s+a,(t-s)+(s+a))`，第二坐标与 `t+a` 算术相等。右侧不要求短扩张 essential，不要求 x′ 或其 E∞ 代表非零。

两个 witness 自身已有 page≥2 及 length range 字段，所以无需重复引入合法域假设。没有把 `target=ρ(target)` 或早 target≠0 加作公共前提；这些在内部由原有数据推出。

## 证明结构

1. 从真实 filtered relation 的减法性质推出，已知扩张 nonessential 等价于零源到同一目标的 homogeneous relation；再用已有 `mem_indeterminacy_iff` 转换为源在 F^(s+1) 的实际代表。
2. 由 `family_infinity_representative_map`、`finite_target_rho` 和 infinity representative 唯一性，推出原两个 witness 的 targets 的实际 ρ 绑定。
3. 晚 essential 蕴含晚 target≠0；在合法 strip 上应用已有 `rho_infty_injective` 得早 target≠0。
4. 若 n=e(f)，既有最短长度 no-crossing 判据使 essential 等价于 target≠0，所以早 nonessential 不可能。此步骤覆盖早页 E₂ / 商长度 1 边界，不增加非零或长度前提。
5. 因而早 nonessential 时 n>e(f)，可固定 a=1。取源 F^(s+1) 代表在该层的 graded 类，允许它为零。通过实际商移位同构与 `essShift.representative_iff`，将其解码为 unshifted finite quotient 的 E∞ 类；固定文献窗口给出真正的 Ambient x′∈Z_(rEarly−2)，边界分母为 B₂。运输回来得到同早商 λx′ 标签的原 E∞ 类。
6. 同一个实际代表给出长度 n−1 的短扩张到指定 target。反方向中，任意 a≥1 的短式源代表属于 F^(s+1)，直接重新构造 homogeneous indeterminacy，推出早 nonessential。

实际 target reindex 私有引理由协调者独立验证的 `TowerShortReindex.lean` 原样迁入，只有命名空间作用域调整。它只作整数等式运输，不更换对象或 map。

## 标签约束

私有 `correctionShiftIso_incl` 直接证明选定 cofiber shift 同构与实际 quotient inclusion 交换（`quotient_shift_exists.choose_spec.1`）。标签是同一 unshifted λ^a 类经 actual shift 的运输。

没有声称它与旧 `finiteNuLabel model X q e ... a` 机械 rfl 相等；现有 E₂Comparison 未给一般 shift-page compatibility，不能凭空补出这样的相等式。

## 实际验证

命令：

```
lake env lean KIP126/ProofTools/Paper/ExtensionIndeterminacy.lean
```

实际退出码 **0**；日志保存在 `worker-lean.log`，仅有第 240 行两条 tactic 风格 linter 提示。命令使用既有锁定工具链及缓存，未生成 olean 或运行共享构建。之前调试轮次的失败没有记为通过。

同源快照 `WorkerProofAudit.lean` 也通过实际 Lean 检查，退出码 **0**，原始结果保存在 `worker-audit.log` 和 `worker-dependency-audit.json`。它打印两个新公共声明的实际公理，并遍历当前可见的类型及证明体。由于该快照对部分上游使用普通 module 导入，封装隐藏的 opaque proof-body 不在其可见环境中，**602 个项目常量、28 项既有直接待构造责任仅是可见下界，不是完整传递闭包**。原始日志和 JSON 保留实际输出，不回写成其他环境的数字。

独立审计者随后在完整 CaptureTrust 式 `import all` 环境运行 ProductionAudit 并通过：主 iff 的完整项目闭包为 **822** 个常量、**38** 项既有上游直接待补；CorrectionLabel 为 **567** 个常量、**33** 项既有上游直接待补。两者均无 Main 依赖、无 ProofTools 本地直接待补、无未登记待补。完整生产审计及其证据以 [audit.md](audit.md) 为准，协调者后续的全库 CaptureTrust 再交叉核对。

两个公共声明的实际公理均为 `[propext, sorryAx, Classical.choice, Quot.sound]`；其中 sorryAx 来自既有上游责任，不能省略。本轮未把这些局部检查冒充整个仓库构建通过。

## 待补责任与交接

生产文件未使用 axiom、sorry、额外结果包或新待补前提。固定标准模型及 Literature 窗口等既有上游待构造责任仍然保留；本地完整证明不等于所有标准对象已经构造完成。worker 可见下界中的 28 项均已逐项匹配现有 `metadata/proof-obligations.json`，结果见 `worker-dependency-registry-check.json`；其中 26 项属于 AdamsSynthetic（含 Standard.shift_filtered/shift_page），2 项为 Literature.Standard.eInfinity_finite/eInfinity_nu。该 28 项不能当作全部上游责任；完整 iff 的 38 项与 Label 的 33 项由上述独立 ProductionAudit 核对，完整名单及无未登记责任的结论见 [audit.md](audit.md) 及其证据。

此 worker 没有修改旧 `FiniteExtensionNonliftableCrossing` 或 stretching 接口，也没有从本修正版宣称原 cycle-set 差集结论。协调者负责独立审查、公共入口及 interface append、普通消费测试、完整 `lake build` 和共享状态更新。
