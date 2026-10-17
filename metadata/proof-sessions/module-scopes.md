# 本轮三个模块的任务范围

本文件随本轮 session prompt 发布，不安装进 skill。来源和优先级以 [本轮任务上下文](campaign-context.md) 及各模块 prompt 为准。

启动时从当前 `metadata/proof-obligations.json` 重新读取所有属于该模块的行，按 `row.module` 及登记责任映射归属；部分旧行没有 responsibility_owner，不能仅按该字段过滤。同时读本模块 `*-api.json`、`*-contracts.json`、`*-sources.json`。

三个模块均先以 a48 的实际实现建立迁移映射、优先迁入并适配到现有接口。下列主题用于组织迁移；额外的从零补证排在这一阶段之后。

以下数量只记录准备时状态：AdamsSynthetic 103、Literature 132、Computation 88。依据实际依赖前沿拆目标；不以此承诺可消除的数量。

## AdamsSynthetic

范围：底层源谱/预谱、HF₂、替换、导出 smash 与识别；实际经典 Adams 塔及完整谱页；Milnor 代数与实际 E₁/E₂ 识别；synthetic 范畴、ν、λ 反演；有限 λ 商塔与规范化；收敛、检测与滤过；乘法、映射复合、富集及权移。

- 优先按 `Standard/Background.lean`、`Source.lean`、`Operations.lean`、`Filtration.lean` 等文件与依赖分工，公共背景与内部源识别保持同一实际对象。
- 先查已有 `Internal/Source`、`Internal/Milnor`；候选源为 a484 的 `Def/Topology`、`StableHomotopy`、`ClassicalAdams/Tower*`、`Steenrod`、`Synthetic`、`Comparison`。原目录只用于定位。
- 不把整个 CompletionModel、HF2AdamsContext、synthetic 背景的公理选择当成已经完成构造。可用其中的通用证明；独立 Milnor d²=0 不可反过来借用以该复形为基础的 Adams 坐标造成循环。
- 可消费 SpectralSequence；不得接手 Literature、Computation、ProofTools、Main 的责任。
- 相关目标：`AdamsSyntheticChecks`、`ArchitectureChecks`，最终完整 `lake build`。

## Literature

范围：实现/λ反演/权移；E₂自由部分与有限λ商；E∞公式和λ/ρ相容；商代数、乘法与检测滤过；BHS lifting及比较；May/Moss/Toda与次级操作；经典η/ν/θ₅、BX、tmf等文献结论及标准类。

- 大量责任在 `Standard.lean`：按定理族并行研究，唯一文件写入者整合。`Standard/Filtration`、`QuotientAlgebra`、`Secondary` 可按文件独立派发。
- 核验原始来源是否支持当前完整量词、对象、分次、边界与适用条件；来源引用与 Lean 证明分别记录，不以“文献声称”代替证明。
- 候选源 a484 的 `Def/Comparison/ClassicalSynthetic`、`Main/Literature`、`Literature/Hypotheses` 等；其外部结果字段用于理解前提，不能把 adamsSyntheticResults 公理导入为解答。
- 上游 AdamsSynthetic/SpectralSequence 已登记接口可直接调用，不等待其他 session；用源对象到固定对象的实际比较保留同一见证。
- 相关目标：`LiteratureChecks`、`ArchitectureChecks`，最终完整 `lake build`。

## Computation

范围：生成元与基目录；Lin 源代数和完整坐标；源到实际球面 E₂ 比较及标准类标定；维数、乘积和有限关系证书；球面微分、存活、消失与 staircase；Cν 基/顶胞腔/包含连接映射；tmf 模型和指定类。

- 大量责任在 `Standard.lean`：多个 worker 交独立补丁，唯一文件写入者整合。`Table/Dimensions`、`Relations`、`ThetaRelations`、`Archive`、`Values` 等可按文件划分。
- 优先从小的有限证书与已明确来源的代数恒等式着手，再连接固定 Adams 对象。完整坐标比较必须保留对象、乘法、单位、标准 h_i/g/δ 等关联与次数上界。
- 候选源 a484 的 `Computation/LinCoordinates`、`WellFormedness`、`Tmf`、`Main/Computation`。可复用实际数据/解析/证明，不照其旧目录改本仓库归属，不引入 adamsComputations 公理。
- 严格区分有限坐标证书正确与证书计算实际 Adams 页；不能另造一个满足表的模型替代实际对象识别。反例重点为编号、端点、负次数、遗漏关系和数据/证书不一致。
- 上游 SpectralSequence/AdamsSynthetic/Literature 已登记接口可直接调用，如实记录传递依赖。
- 相关目标：`ComputationChecks`、`ArchitectureChecks`，最终完整 `lake build`。
