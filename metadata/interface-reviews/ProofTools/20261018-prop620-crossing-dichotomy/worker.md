# 6.20 差集或晚页 crossing：证明 worker

状态：完整二择定理及所有辅助证明已通过最终本文件实际 Lean 检查（exit 0），生产数学源码冻结；由 root 串行正式构建、捕获及接口整合，独立 auditor 做全闭包核验。

## 任务边界与授权

本轮按 root 转述的用户授权以及王老师消息 `om_x100b620dc11210a4dd281834ddfa376`（position 1500）形式化新版。Git 基线 `aad718722aa01dfce361f40645fc776037d1078f`，工作树及旧接口基线见本目录 `baseline.json`。协议为 `/root/.agents/skills/kip-upstream-session/references/protocol.md`。

本 worker 仅写 `KIP126/ProofTools/Paper/ExtensionCrossingDichotomy.lean` 和自己的本目录记录；不修改旧数学源码、公共入口、API、Tests 或待补责任。新辅助 `ExtensionEssentialSource.lean` 由另一 worker 独占；共享构建、入口整合和锁由 root 负责。

## 公共陈述

新增 `FiniteExtensionNonliftableShortTo` 保留真正的经典 cycle-set 差集、同一早 normalized quotient map、固定原 earlyW.target（仅必要的分次运输）和 b=0 短 equation。a 的范围为 0<a≤n−e(f)，源经典坐标为 `(s+a,(t-s)+(s+a))`，循环层分别为 `rEarly−1−a` 和 `rLate−1−a`。短式不额外要求 essential 或非零。

新增 `finiteExtension_nonliftableShort_or_lateCrossing`：给定同 x/y 的早晚两个 witness、rEarly≤rLate、晚 essential、早 nonessential，推出上述差集短式，或者同晚实际 synthetic ESS 中 `¬ExtensionNoCrossingRange Mlate p s n s`。没有把后一个分支换成 Definition 5.9 的经典 `FiniteHasCrossing`。

## 完整证明路线

1. 由已有目标自然性与代表唯一性证明 early target 非零。
2. 调用同模块已证明的 `finiteExtension_essential_shorter_source` 提取早页 essential 短式到同一原目标。这里必须 essential；上一版可取 a=1 的任意短式不足以推出差集。
3. 若其经典 x′ 不是晚页对应循环，直接给出差集分支。
4. 若 x′ 是晚页循环，则构造未移位晚商的真实 E∞ 标签。未移位 quotient rho 与 finiteTargetLabel 的包含方块直接交换。
5. 既有 `quotient_shift_restriction_on_spheres` 对任意满足 inclusion 交换的 Qearly/Qlate，证明所有同次数实际 BiHom 上的 rho 方块交换。私有 `infinity_map_eq_of_homotopy_eq` 通过 associated-graded 的实际代表，将此升级为 E∞ 方块。没有假定 Classical.choose 的 Q 跨 q 严格自然。
6. root 独立重建并验证的 ESS shift E∞ 自然性仅使用公开 filtered transport、convergence 与 actual shift。结合上一步和分次运输，证明 CorrectionInfinity 在 actual source rho 下自然。
7. 将晚循环的未移位标签运输为晚 actual source E∞ 类，再利用 early CorrectionLabel 代表唯一性，证明早短源处于 actual source rho 的 E∞ 像。该结论在内部由真实对象数据证明，没有加作公共前提。
8. 若晚无 crossing，`image_correction_in_next` 使任意晚 F^(s+1) 代表的像位于晚目标 F^(s+n+1)。给定早短源的晚 leading lift，取其晚真实代表，再下降到早商，即得到同一早短源的零目标 equation，与早短式 essential 矛盾。

因此得到固定目标差集短式或同晚 ESS crossing 的二择；未使用目标自身、6.23、False 既有矛盾或新增结果包。

## 实际检查状态

最早两个核心辅助证明 `essential_short_source_not_in_range` 和 `infinity_map_eq_of_homotopy_eq` 已单独随本文件前缀通过实际 Lean（exit 0）。完整最终本文件检查命令：

```
lake env lean KIP126/ProofTools/Paper/ExtensionCrossingDichotomy.lean
```

最终 worker7 检查实际退出码 **0**，日志保存在 `worker-final-lean.log`；仅有冗余 expose、tactic 风格及 unused simp 等 linter 提示，无 error。最终生产 SHA-256 为 `aa1ae0f936ebb219b551f03731bf4001baef78dd1010029442525517afe50251`，源码共 494 行。

最后调试问题是跨 q 证明中同构逆映射的取消，以及两个只差 proof-irrelevance/定义展开的分次 cast。最终用 `Category.comp_id` 加 `rfl` 收尾，没有改数学陈述、前提或对象。此前 worker6 退出码为 1，原始失败日志保存在 `worker6-before-comp-id.log`，没有记为成功。被替代的旧进程均已结束或终止。

本 worker 没有运行 lake build 或擅自写共享 olean。root 随后已实际完成正式公共入口构建：退出码 **0**，**2823 jobs**，成功日志副本为 `worker-coordinator-public-build.log`。普通公共消费捕获、API append、完整默认 build 和全 import-all trust audit 仍由 root 统一安排；此公共入口构建通过不能代替完整默认 build。
此前 `CorrectionInfinity` 及其代表运输在嵌套期望型推断时曾超时。root 另行在 `CorrectionInfinityCheck.lean` 用显式 F/P、源元素及像元素类型、具体 eInftyMap 分次重建，并在 200000 心跳预算下实际检查通过；本文件已整体迁入这两块。没有通过增加未证责任或无限心跳隐藏缺口。

## 依赖审计边界

未新增 axiom、sorry 或待补责任。标准模型、文献 E∞ 窗口、有限商无回返与 shift 比较等原有上游责任仍须保留。最终闭包以 root 的完整 import-all CaptureTrust 和独立 ProductionAudit 为准，普通导入快照可见闭包不能冒称全部传递依赖。
