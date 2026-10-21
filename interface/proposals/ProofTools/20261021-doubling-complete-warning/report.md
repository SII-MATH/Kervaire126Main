---
issue_id: ProofTools-20261021-doubling-complete-warning
title: 乘二例子完整 crossing warning 的三个公开增补
summary: 方案 E 的 d0、h0d0 及完整 warning 定理已获批准、实施并通过最终核验，paper:6.8 已直接绑定。与既有13根合计16个命名根、36个真实生成项、268项导出；原216条完整记录及214项许可责任不变。
responsibility_module: ProofTools
targets:
  - KIP126.ProofTools.Standard.d0
  - KIP126.ProofTools.Standard.h0d0
  - KIP126.ProofTools.Standard.paper6_8_complete_crossing_warning
baseline_commit: f17969a0c7839f7d47d550d5e8f8a0a0aa2ffe91
reporter_agent: /root/grey_interface_report
independent_of_discoverer_and_implementer: true
evidence_level: 完整三根候选 no-o exit 0、零警告；另一独立审计对同源完整候选的 kernel 与全 proof-body 闭包核验通过，0 本地洞，82 个已登记上游位置；固定对象、实际零像和同权 crossing 对齐。
status: approved-implemented-and-validated-before-publication
human_decision: "2026-10-21，本对话用户对本报告3根及最后条目绑定的明确询问回复：‘批准这 3 项并绑定’。授权仅d0、h0d0、paper6_8_complete_crossing_warning及其必需真实生成导出、ProofTools入口／基线增量和paper:6.8直接绑定；既有13根及其他类型前提、公理、许可洞不变。"
---

# 接口审查报告

## 已批准范围与当前结果

方案 E 的范围是三个新增 public 根：`KIP126.ProofTools.Standard.d0`、`KIP126.ProofTools.Standard.h0d0`、`KIP126.ProofTools.Standard.paper6_8_complete_crossing_warning`，第三项现已直接绑定 `paper:6.8` 聚合节点，数学事实、生产接口、公共消费与最终全量构建均已核验通过。该节点含原 Example 6.8 和 Remarks 6.6、6.9–6.10。标签只有在正文定义这两个数值类的位置绑定，不作为 warning 结论的替代绑定。

不新增 public 技术谓词、Statement 包、调用方数学假设、公理或许可证明洞。不修改既有公共声明的类型、语义或对象。先前用户批准的13项保持不变；本次明确批准仅扩大到以下三根。E 的两个标签与旧报告 B 中未批准的候选同名同型，本次把它们与完整结论一并作为明确范围交审；旧 B 中单独的局部 `paper6_8_classical_d3` 不在本提案中新增，相关结论已包含在完整 warning。本方案已明确获批，协调者在旧报告作交叉记录，避免重复请求。数学补证及独立核验可以继续，生产 API、锁和新的 Blueprint 绑定已按本报告三根范围实施，最终验证全部通过。

当前完整候选位于 [public-complete-warning.lean](evidence/public-complete-warning.lean)。完整核验已经完成，结果见下文；数学核验与接口批准相互区分；本次实施所依据的人审原话记录于末尾。

## 原接口、背景与问题成因

本轮首先检查了保留冻结接口的方案。数学构造与技术辅助均保持 private；不需要改变上游、主定理或现有 13 项声明即可构造所有数值事实。审查起点的问题是：当时 ProofTools public 锁中没有上述三个 E 根，因而按仓库“Blueprint 绑定必须指向同模块 public 锁声明”的规定，当时完整 warning 不能直接绑定到这些 private 证明；获批的三个公开包装现已解决这一绑定问题。状态证据见 [增补前公开根检查](evidence/baseline-public-root-check.json)。这是新增可消费数学结论的提案，不是修改一个已知假 public 接口的修复。

已有 private `NumericalExamples.Paper6_8CrossingWarningStatement` 只有六项：指定 `d2(h4)=h0h3²`、有限页二短扩展、长扩展零目标、短 essential 扩展、长扩展 `h0d0` 目标以及错误零 `d3` 的否定。`DoublingNumericalExtensions.paper6_8_crossing_warning` 证明这六项。直接把它公开仍不够覆盖现有 Blueprint 正文：还需要实际同权 crossing、长关系 inessential、严格零像和 maximal 说明。候选不会把这个六项子结论冒充完整节点。

本报告员没有发现或实现那些私有数学构造；实际构造由 proof worker 交付。本报告独立读取原论文、Blueprint、全部相关终根类型、归一化和标签定义，并只在提案目录中写公开封装和核验证据。公开封装中的算术展开、固定第一商比较和 conjunction 组合不改变数学实现。

### 原文必须保留的事实

原文定位与逐行摘录在 [原文证据](evidence/original-source-excerpts.txt)；审阅时节点正文在 [Blueprint 目标快照](evidence/blueprint-target-at-review.txt)。

- `AimPaper/main.tex:1694–1720`，Example 6.8：`f=2`，`n=r=2,m=1,l=2,e(f)=1,s=1,t=16`；输入 `d2(h4)=h0h3²`、`d1^(f,E2)(h4)=h0h4`、`d2^(f,E∞)(h0h3²)=0`；左边、顶边两个 no-crossing 前提成立，底边有较短 essential 扩展 `d1(d0)=h0d0`；删掉底边 no-crossing 会错误地给出 `d3(h0h4)=0`。
- 原 Remark 6.9（Example 后）：同一短扩展也是长关系 `h0h3²↦h0d0` 的 crossing，使这个长关系 inessential。遗漏 crossing 控制会给出互相冲突的零／非零输出。
- 原 Remark 6.10（`rem:chuaerror`）以及 `AimPaper/main.tex:1421–1433`：实际 `a∈π(14,17)S00` 有指定第一商标签 `h0h3²`，其实际 `[h0]` 像在 `π(14,18)S00` **等于零**；另一个实际 lift 的像是带 `h0d0` 标签的非零关系。应按显式权重写成 `λβ`，其中 `β∈π(14,19)S00`，并且候选还显式证明 `λβ≠0`。零像可被任意有限次 λ 整除，因而支持原文所说的 maximal-image 选择。这里不能把零 associated grade 代替严格零像。

原文关于 Chua 一般定理的文字是来源和反例解释。本次形式化固定乘二实例的完整反例数据，不声称把整个外部 Chua 定理或任意“maximal extension”选择机制形式化。

## 真实前提与对象核对

候选固定 Standard 模型，使用其实际 classical sphere Adams 谱序列、实际 `νS0`、固定 synthetic sphere `S00`、实际 `model.nu.unitIso`、实际 normalized multiplication-by-two map、实际 `Literature.Standard.syntheticH0` 及同一 convergence/tower。没有把这些对象换成自选模型、自由映射、坐标标签或抽象 filtered group。全部根均没有数学调用方参数或自由宇宙参数；`∃ he : e=1` 是结论里证明实际乘二 exponent 为一，不是 caller 必须提供的前提。

设 `x=h0·h3²∈E2^(3,17)`，`v=h0d0∈E2^(5,19)`。候选的完整量词、类型和算术重分次均在 [精确 Lean 候选](evidence/public-complete-warning.lean)，没有使用 private 谓词出现在 public 类型中。

| 对象／结论 | 固定关联与完整保留范围 |
| --- | --- |
| `d0` | Ext archive 的 ID 8，记录名 `d_0`、次数 `(4,18)`，通过既定 source monomial 与实际 E2 comparison 进入实际球谱 E2；不是任选该次数中的一个类。 |
| `h0d0` | 现有实际 `product h0 d0`，次数 `(5,19)`；不是另选 target。 |
| `f` 与 `[h0]` | `f=2·id(S0)`，实际 exponent `e=1`；实际 normalized map 经这个等式的规范重分次，等于 `Σ(0,1)(unitIso.hom) ; syntheticH0 ; unitIso.inv`。没有以 ordinary page map 取代 positive-exponent 归一化操作。 |
| classical 与 finite 输入 | 完整指定的 `DifferentialAt 2 h4 x` 和 `FiniteExtension`，`r=2,n=1,s=1,t=16`；左 `NoCrossingOn 2 2 (1,16)` 和顶 `FiniteNoCrossing 2 1 1 16` 直接证明，未假定。 |
| 两条长关系 | `InfiniteExtension f 2 3 17 x 0` 与 `InfiniteExtension f 2 3 17 x v`；都是同一实际未截断 normalized map 的 witnesses，而不是仅到某个商的关系。 |
| 较短 essential 关系 | 存在 `InfiniteExtensionWitness f 1 4 18 d0 v` 且 `Essential`；保留长度、实际源与实际目标。 |
| paper crossing 与长关系 inessential | 完整 `InfiniteHasCrossing f 2 3 17`；并且对每一个长 `v` witness，`¬Essential` 且其指定 infinity target 非零。非零目标并不保证该关系 essential。 |
| 实际同权 crossing | 使用实际 exponent `e` 和实际 normalized map：先有 `a∈π(14,19)(Σ(0,e)νS0)` 检测 `d0`、`b=aF`；在 `p=(14,18),s=4,n=1` 给出 `TowerEssentialExtension`，target 的实际 infinity 标签是 `λh0d0`，次数 `(5,19,18)`；源 filtration representative `ar` 的实际 ambient 像等于 `λa`，且 associated grade 正好是所指定 source。所有这些 witnesses 由同一个 existential tuple 联系，不能用原 weight19 的 essentiality 静默替代 weight18 的 essentiality。 |
| 实际第二 lift | 同一实际 `S00` 上 `a∈π(14,17)`、`β∈π(14,19)`，两个指定第一商标签分别是 `x` 和 `v`，实际 `shift(a);syntheticH0=λβ` 且 `λβ≠0`；因此它与严格零像 lift 确实不同。 |
| 实际严格零/maximal lift | 同一实际 `S00` 上另一个 `a∈π(14,17)`，固定第一商标签 `x`；`shift(a);syntheticH0=0`，并且 `∀q:ℕ,∃b∈π(14,18+q),λ^q b` 等于**同一**实际像。不是只证明 `F^5/F^6` 的零类，也不把泛型 strict-zero 引理的高滤过／realization 假设转给调用方。 |
| 排除错误输出 | 精确的 `HasNonzeroDifferential d3(h0h4)=v` 以及 `¬DifferentialAt d3(h0h4)=0`，使用独立既有文献 `d3` 与 E2 唯一非零 target 标定。没有靠待检 Leibniz 结论本身反推输入。 |

三个 public 根类型都位于同一责任模块 ProofTools。候选没有新增程序结构、递归证书、程序 soundness 命题或与本任务无关的程序正确性前提。

## 独立证据与复现

固定源和工具链指纹见 [source-sha256.json](evidence/source-sha256.json)。所有复现均在固定 `lean-toolchain`、既有 `lake-manifest.json` 和已经由 root 构建的实际 `.olean` 上进行；不升级工具链、不清理或共写构建缓存。

最终命令是：

```sh
lake env lean interface/proposals/ProofTools/20261021-doubling-complete-warning/evidence/public-complete-warning.lean
```

这是无 `-o` 的单文件检查，候选只位于本提案 evidence 中，不导入生产 facade 或修改 API 锁。实际结果为 **exit 0，零警告、零错误**，日志保留在 [public-complete-warning.log](evidence/public-complete-warning.log)。候选冻结 SHA-256 为 `806244432eb5b44255324b9bd29986c360276837e914ffa6833c3d472cfeca2d`。包括第二实际像 `λβ≠0` 的 worker 私有桥原样收入 [worker-sphere-pair.lean](evidence/worker-sphere-pair.lean)，原片段 SHA-256 为 `14741ee0baecc424852e76849b4db3ad98a08611c19e824826b716fa449c7cef`；报告员独立检查其实际悬挂逆比较、unitIso 自然性和两个第一商标签。

已实际核对的数学实现分工：

- `NumericalExamples` 固定 `d0`、`h0d0` 及独立精确非零 `d3`。
- `DoublingNumericalExtensions` 构造实际 normalized map 比较、finite 输入、两种 full target 关系与 short essential extension。
- `DoublingCrossing` 证明相同 infinity source 的两个长目标带来的 inessentiality，并另行构造实际同 weight18 的 essential crossing。
- `DoublingMaximalLift` 从实际 first-quotient boundary、odd-scalar corrected d0 lift、固定低次数 Ext 与 classical separation 构造严格零像。泛型证明中的数学前提均由本地 fixed-model 计算和既有上游接口消解，最终数值根无新增假设。实际零像经 `unitIso` 传到固定 `S00`，再取零的任意 λ division 支持 maximal 说明。

三个数学文件的独立全 body 审计已经通过：六项 warning 的 73 个、actual same-weight crossing 的 71 个、严格零/maximal 终根的 82 个直接上游待补位置，分别全部已登记。报告员逐项解析对应审计日志并与当前 `proof-obligations.json` 独立比对，未登记数均为零；完整名单及复现方法见 [upstream-obligation-membership.json](evidence/upstream-obligation-membership.json)，原审计分别见 [六项 warning](evidence/doubling-final-audit.log)、[crossing](evidence/doubling-crossing-audit.log)、[严格零/maximal](evidence/doubling-maximal-closure-audit.log)。这些遍历由另一独立 proof auditor 执行，本报告员不把解析其日志称为第二次 Lean 遍历。随后独立 proof auditor 对 SHA `80624443…` 的**整个公共候选**作同源 kernel 与完整 proof-body 聚合核验，实际 exit 0、零警告／错误：`d0` 8002 个 project/boundary 依赖、31 个直接上游待补位置；`h0d0` 8019／31；完整 warning 10154／82。三根宇宙参数均为空，没有 caller 数学参数；0 本地证明洞，不使用有争议的 `finiteCrossing_iff_syntheticCrossing`。证据为 [整包审计日志](evidence/doubling-complete-warning-candidate-audit.log)、[可复现审计源码](evidence/DoublingCompleteWarningCandidateAudit.lean) 和 [82 个原登记条目](evidence/doubling-complete-warning-candidate-upstream-sites.json)。报告员又独立比对了所有 82 项的完整 baseline 条目（包括类型／证明体指纹），不只是名字；差异数为零。必须同时区分本地没有新增证明洞与整个依赖闭包没有 `sorryAx`：后者当前并不成立，Standard 模型、比较、convergence、实际文献输入等继承仓库已登记上游责任。不得把普通导入环境中可见的少量 body 数量当作完整闭包。该整包核验显式导入四个上游 InternalAudit 和所有本模块内部证明体，所列为这个完整可见闭包中的直接待补位置，不是普通 import 下的边界计数；核验不借助目标自身、Main、AdamsCalculations、算法证书或未获准的新公理补证。

## 方案及精确差异

完整原／新差异是**无同名根 → 新增以下三个根**，不删除或修改既有接口：

公开定义的精确类型和取值为：

```lean
@[no_expose] public def d0 : model.classical.sphere.Page 2 (4,18) :=
  KIP126.ProofTools.Paper.NumericalExamples.d0

public def h0d0 : model.classical.sphere.Page 2 (5,19) := product h0 d0
```

以下是第三根在 `KIP126.ProofTools.Standard` 中的**完整类型**，与已经过检的候选相同；完整 proof 和 imports 见 [候选文件](evidence/public-complete-warning.lean)。所有符号都是此前既有 public 数学语言，`d0/h0d0` 是本提案的前两个标签。

```lean
public theorem paper6_8_complete_crossing_warning :
    let f : SphereSpectrum (C := Spectrum) ⟶ SphereSpectrum := 2 • 𝟙 _
    let x : Ambient model .sphere (3,17) :=
      product h0 (model.standardClasses.standardHiSquare 3)
    let e := normalizedExponent model.classicalTower f
    ∃ he : e = 1,
    let F : (SyntheticCategory.biShift (0,1)).obj
        (model.nu.functor.obj (ClassicalObject.sphere.obj model.auxiliary)) ⟶
        model.nu.functor.obj (ClassicalObject.sphere.obj model.auxiliary) := by
      have hef : normalizedExponent model.classicalTower f = 1 := he
      simpa only [hef,Nat.cast_one] using (model.normalizedMap .sphere .sphere f).map
    F = (SyntheticCategory.biShift (0,1)).map model.nu.unitIso.hom ≫
      KIP126.Literature.Standard.syntheticH0 ≫ model.nu.unitIso.inv ∧
    DifferentialAt model .sphere 2 (1,16) (3,17) h4 x ∧
    FiniteExtension model .sphere .sphere f 2 1 1 16 h4
      (KIP126.Literature.Standard.hiProduct 0 4) ∧
    NoCrossingOn model .sphere 2 2 (1,16) ∧
    FiniteNoCrossing model .sphere .sphere f 2 1 1 16 ∧
    InfiniteExtension model .sphere .sphere f 2 3 17 x 0 ∧
    (∃ W : InfiniteExtensionWitness model .sphere .sphere f 1 4 18 d0 h0d0,
      W.Essential) ∧
    InfiniteExtension model .sphere .sphere f 2 3 17 x h0d0 ∧
    InfiniteHasCrossing model .sphere .sphere f 2 3 17 ∧
    (∀ W : InfiniteExtensionWitness model .sphere .sphere f 2 3 17 x h0d0,
      ¬ W.Essential ∧ W.target ≠ 0) ∧
    HasNonzeroDifferential model.classical.sphere 3 (2,17) (5,19)
      (KIP126.Literature.Standard.hiProduct 0 4) h0d0 ∧
    ¬ DifferentialAt model .sphere 3 (2,17) (5,19)
      (KIP126.Literature.Standard.hiProduct 0 4) 0 ∧
    -- A genuine shorter essential extension at the SAME weight 18 as
    -- the long relation, whose source represents lambda times a d0 lift.
    (∃ a : BiHom 14 19 ((SyntheticCategory.biShift (0,(e:ℤ))).obj
        (model.nu.functor.obj (ClassicalObject.sphere.obj model.auxiliary))),
      ∃ b : BiHom 14 19
        (model.nu.functor.obj (ClassicalObject.sphere.obj model.auxiliary)),
      ∃ source target,
        Detects (model.convergence (.shift (0,(e:ℤ)) (.nu .sphere))) (4,18,19)
          (regradeE2 (by rw [he]; norm_num)
            (model.comparison.nuE2 .sphere e 4 18 0 d0)) a ∧
        a ≫ (model.normalizedMap .sphere .sphere f).map = b ∧
        HasInfinityRepresentative _ 2 (5,19,18)
          (nuWeightLabel model .sphere 5 19 18 (by decide) h0d0) target ∧
        TowerEssentialExtension (F := model.family) (P := model.syntheticTower)
          (cx := model.convergence (.shift (0,(e:ℤ)) (.nu .sphere)))
          (cy := model.convergence (.nu .sphere))
          (model.convergentMap (.shift (0,(e:ℤ)) (.nu .sphere)) (.nu .sphere)
            (model.normalizedMap .sphere .sphere f).map)
          (14,18) 4 1 source target ∧
        ∃ ar : (Subobject.underlying.obj ((model.syntheticTower.filtration
          ((SyntheticCategory.biShift (0,(e:ℤ))).obj
            (model.nu.functor.obj (ClassicalObject.sphere.obj model.auxiliary)))).F
              4 (14,18)) : ModuleCat.{0} ℤ),
          ((model.syntheticTower.filtration ((SyntheticCategory.biShift (0,(e:ℤ))).obj
            (model.nu.functor.obj (ClassicalObject.sphere.obj model.auxiliary)))).F
              4 (14,18)).arrow ar = lambdaMultiply 1 a ∧
          (model.syntheticTower.filtration ((SyntheticCategory.biShift (0,(e:ℤ))).obj
            (model.nu.functor.obj (ClassicalObject.sphere.obj model.auxiliary)))).toAssociatedGraded
              4 (14,18) ar =
            (infinityGradedIso (model.convergence (.shift (0,(e:ℤ)) (.nu .sphere)))
              (14,18) 4).hom source) ∧
    -- An actual second source lift and its nonzero-label image. The
    -- factor lambda is explicit at weights 17, 18 and 19.
    (∃ a : BiHom 14 17 (S_0_0 : SyntheticSpectrum),
      ∃ β : BiHom 14 19 (S_0_0 : SyntheticSpectrum),
        a ≫ XModLambdaN.incl _ 1 =
          (KIP126.Literature.sphereFirstQuotient model 3 17).symm x ∧
        β ≫ XModLambdaN.incl _ 1 =
          (KIP126.Literature.sphereFirstQuotient model 5 19).symm h0d0 ∧
        shiftHomotopyClass (0,1) (14,17) a ≫
          KIP126.Literature.Standard.syntheticH0 = lambdaMultiply 1 β ∧
        lambdaMultiply 1 β ≠ 0) ∧
    -- A lift with strictly zero actual image, hence with every finite
    -- lambda division of that same image (the maximal-image assertion).
    (∃ a : BiHom 14 17 (S_0_0 : SyntheticSpectrum),
      a ≫ XModLambdaN.incl _ 1 =
        (KIP126.Literature.sphereFirstQuotient model 3 17).symm x ∧
      shiftHomotopyClass (0,1) (14,17) a ≫
        KIP126.Literature.Standard.syntheticH0 = 0 ∧
      ∀ q : ℕ, ∃ b : BiHom 14 (18+(q:ℤ)) (S_0_0 : SyntheticSpectrum),
        homotopyRegrade rfl (by dsimp; omega) (lambdaMultiply q b) =
          shiftHomotopyClass (0,1) (14,17) a ≫
            KIP126.Literature.Standard.syntheticH0)
```

实现使用 private 数学终根组合上述完整结论，不把 private 谓词泄露到 public 类型。`d0` 的 `@[no_expose]` 与现有已批准 `p` 标签封装方式相同；archive 索引等技术辅助不进入拟议公开面。Lean 因显式数学表达产生的算术 proof 辅助声明应由实际导出检查记录，不能另手写一个 public 技术 API。

审查时评估过保持三个根都 private、不增补 public API 的备选方案；那样虽能完成数学证明，但完整聚合节点无法直接绑定。该备选未采用：用户已批准并实施本文三个公开包装。另一种公开多个部分 theorem／technical predicate 的方案会增加公开面且容易把局部证明误读为完整 warning，也未采用。没有理由削弱节点正文、删除严格零/maximal 段落或把额外假设加到调用方来规避绑定责任。

## 下游影响

| 位置 | 已实施的最小修改及责任 | 本提案授权之外的范围 |
| --- | --- | --- |
| ProofTools public source/facade | 仅三个 E 根，沿用同模块 private 完整数学实现 | 不变更先前 13 根或其他模块 public 声明 |
| `interface/baselines/proof-tools-api.json` | 按真实三个声明、宇宙、axioms 与导出结果增补 | 不放宽类型、依赖或锁检查 |
| `paper:6.8` 聚合节点 | 完整定理绑定；按实际成果同步证明正文与状态 | 不把背景对象／private 辅助步骤绑定成结论，不形式化整个 Chua 外部定理 |
| 其他数值条目 | 仅正文确实定义 d0/h0d0 的节点可使用对应标签绑定 | 不将 E 批准扩展到别的 theorem 或算法正确性 |
| trust 与公共消费检查 | root 更新实际内部审计根；验证普通 public import 消费，运行既有 source inventory 与 `lake build` | 本报告员不改测试、baseline、生产源码或构建输出 |

不引入新的待补责任。原有上游责任继续保留；如候选的实际完整核验暴露新缺口，先修复或缩小提案事实范围，并明确说明，不通过新增许可洞使检查通过。相对 AimPaper 的修正仍由 `corrections.yaml` 和 Blueprint 唯一维护，此报告不另建修正版论文记录。

## 阻塞范围与继续项

这三个新增 public 根和完整 warning 的新绑定已获得 E 的具体批准。全部私有数学证明、完整类型封装、独立 no-o 检查、上游责任审计及生产集成最终验证均已完成。程序算法正确性不在本提案内。

已完成实际 S00 第二 full-pair 与其非零性、完整三根 no-o exit 0、整个候选同源 kernel／完整 proof-body 闭包独立审计及全部上游登记核对。没有本提案范围内尚未补齐的数学 fact；用户已明确批准，生产 API／绑定已实施；公共消费及最终全量构建已经通过。上游原有责任继续保留。

## 人类审核记录

2026-10-21，本对话用户对本方案 E 的明确询问回复：“批准这 3 项并绑定”。因此三根及 paper:6.8 直接绑定已获授权、实施并完成最终核验；其他未列公共声明仍未获批准。


### 实施记录

生产文件 `KIP126/ProofTools/DoublingWarning.lean` 的全部数学 token 与冻结候选相同，仅清理审阅注释和仪表；SHA-256 为 `aa87092d7c0d7f936b111629e97c102f1aecc3c95e797b8254af07f4406a0691`。单文件检查零警告／错误，公共入口构建通过。恰好增加三根，`paper:6.8` 只绑定完整定理，不把两个标签绑定成结论。最终接口采集与十三根组合合计新增16个命名根、36个真实编译器生成项；其中 `S_0_0.eq_1` 是在本文件展开既有球对象时生成的方程定理，不是另写的公共数学根。原216条完整记录及全部214项许可责任不变。最终全库和页面验证结果如下。

### 最终联合核验结果（十三根＋方案 E，2026-10-21）

两次授权合计 **16 个命名根＋36 个真实编译器生成项**，ProofTools 当前接口为 **137 个命名声明＋131 个生成项＝268 项导出**。原 216 条完整接口记录（类型、宇宙、公理依赖及导出关联）逐条不变，全部 214 项许可责任及其文件内容不变。`paper:6.8` 现直接绑定完整 `paper6_8_complete_crossing_warning`；相关输入、同权 crossing、长关系 inessential、第二实际非零像与实际严格零/maximal 均已完成。

协调者执行最终检查；本报告员只读核对了相应日志，不把这次文档回写称为自己重新执行构建：

- `lake build`：**成功，3618 jobs**。本地日志 `/tmp/grey-formalization-20261021/final-complete-build.log`。ProofTools audit 为 5708 declarations、1 项原有登记 pending、无 project axioms；Main audit 为 1921 declarations、0 项本地 pending。
- Source inventory：**592 project files、35 consumer/audit files**，模块依赖及 private-import 边界通过；日志 `final-inventory.log` 位于同一临时证据目录。
- Blueprint：**49 项测试通过**；原生导出 **241 个数学条目、9875 个 Lean declarations、1919 个 warnings**。日志分别为同目录 `final-all-blueprint-tests.log` 与 `final-blueprint-build.log`，warnings 按原生输出保留。
- 浏览器预览与真实卡片核验：`page_errors=[]`、`math_errors=0`；`paper:6.8` 与 `paper:6.19` 的实际卡片均为 `lean ok`，分别显示 1／2 个绑定。证据为同目录 `blueprint-final-preview.json`、`final-cards.json`；当前页面统计为 128 个 lean 条目，不沿用早期脚本抓到的旧统计。网页状态仍不替代 Lean 信任审计。
- 接口提案校验：**26 份报告通过**。没有通过改锁放宽前提、新增许可洞或修改已批准数学候选使检查通过。

以上 `/tmp` 路径为本地构建证据位置，未冒充随报告发布的附件。数学候选、独立 kernel／闭包审计与准确前提证据继续保留于两份提案各自的 `evidence/`，本次仅更新报告当前状态。

