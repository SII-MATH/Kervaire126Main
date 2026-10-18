---
title: ν 页权移的公开封装
archived_from: local-history/metadata/interface-reviews/Literature/20261017-01-weightshift-exposure/report.md
archived_sha256: f5defe567a625a08e9ea4e74d39e19908765dc6554ab1846a138261bc9f392b5
summary: "原接口内的直接构造已落实，报告标明 blocking: false；其他封装备选未获批准。"
issue_id: "20261017-01-weightshift-exposure"
responsibility_module: "Literature"
targets:
  - "KIP126.Literature.Standard.nuPage_weightShift"
baseline_commit: "bef90640c4594af4db32c86837f9d95340d1e171"
worktree: "/tmp/kip-literature-20261017-01"
candidate_source_commit: "a484b981fad612eabe2bc7a01b54e049e9a01ce4"
api_file_and_sha256: "metadata/literature-api.json: 7a986fdb9f9a9f889568182d05ad238e9a6543bbbaed3c47028aa0c0494dcc10"
source_file_and_sha256: "KIP126/Literature/Standard.lean: 357a5d3c66d720303eee69e51147d1b2457977539308b5995bad40ed71c2f680"
reporter_agent: "/root/report_stem62"
independent_of_discoverer_and_implementer: true
evidence_level: "锁定编译器源码、成功直接构造、最终754项公共捕获及普通/公开导入成功日志的独立复核；未独立执行 Lean"
status: pending-human-review
human_decision: null
blocking: false
resolution: "方案 A 原接口内直接构造已落实；B/C 未采用"
---

# 接口调整人审报告

## 最终复核结论：原接口内已解决

**方案 A 已落实，`blocking: false`。** 报告员独立读取实际直接 term 证明与日志，并复算最终公共捕获：754 个导出全名、全部 `full_type`、类型指纹和 universe 均与派发基线完全相同，目标前缀只有 `nuPage_weightShift`，没有 `_proof_*` 或 `_private_*` 新导出。原 `@[expose]` 保留；普通 `import KIP126.Literature` 与 `public import KIP126.Literature` 两种实际消费者均 exit 0，并取得不含直接/synthetic sorry 的定义体。没有使用 `no_expose`，没有批准或实施扩出口方案。

最终生产 `Standard.lean` SHA-256：`5c9e79c604b14a43e16bb24e6724f47c2202c01ce8cceab031ff43693c227c1c`。公共 capture SHA-256：`e5bbac29e480b91c51000557d128816b6b4a63e89baffe9a2b9e6f6b90fabdf7`。实际目标的完整类型和 body 与成功 `WeightShiftDirectTermProbe-1` 替换声明名后逐字一致。最终验证及源码/日志哈希保存在同目录 [final-resolution.json](final-resolution.json)。

实施者采用公开已有定理和显式 `Eq.rec`，把证明参数组织为原子项，避免编译器抽取公开辅助定理；没有绕过可见性环境或更换数学对象。这是现有授权内的正常补构造，无需人类批准。此前公开 sorry 和私有封装失败的叙述在下文保留为历史证据，不是当前目标状态。

本次只解除权移封装问题，不认证整个 session 已完成构建：协调者报告完整构建另在核查原 sorry 源位置导致的 104 项 body 指纹变化；该事项独立于本曝光/导出问题，仍由协调者审计。`nuPage_e2` 标签方程和已登记的 AdamsSynthetic 传递待补继续如实保留。

## 请求人类决定的具体问题

**当前无需人类批准接口变更**：方案 A 已在原接口内完成；以下 B/C 的具体问题仅作为历史人审备选保留，未被采用，不再阻塞本条交付。`status=pending-human-review` 与 `human_decision=null` 留作历史报告审阅，不表示 A 需要批准，也不表示任何人批准了 B/C。

本问题是**已构造的实际权移同构如何保持冻结的公开封装**，不是权移命题被证假。目标的完整数学类型有成功 probe；直接把证明放入原 exposed public def，会新增 8 个公开辅助声明。改用 `@[no_expose] public def` 可以保留同一 Lean 类型和数学值，但会撤销普通模块消费者取得该定义体的能力，不能只凭类型指纹相同当作接口未变。

优先继续现有授权内的内部实现方案：保留原 `@[expose]` 能力、原公共导出集合、全部量词和固定对象，不改锁、不新增责任；只有这些性质都实际验证，才可消除本条直接责任，无需另行请求人类批准普通补构造。

若内部方案最终无法满足冻结边界，需要人类明确决定具体哪一种变更；本报告不预先批准：

1. **方案 B**：仅允许 `KIP126.Literature.Standard.nuPage_weightShift` 从 exposed 改为 `@[no_expose]`，完整类型、数学同构、对象关联、宇宙和导出名称保持不变。接受普通 `module` 导入无法取得/展开该定义体的语义差异。
2. **方案 C**：保持 exposed，但明确允许报告列出的额外公开辅助声明。其范围须指定为直接证明产生的 8 个 `_proof_*`，或另一个经过精确捕获的候选，不能笼统批准任何未来辅助导出。
3. **继续冻结原边界**：保留公共待补定义和已证私有构造，继续其他非阻塞工作，等待原边界内封装方案。

初次报告没有证据证明 B 或 C 是唯一可行方向；随后方案 A 的直接 term 路线已解决此问题。`private_decl%` 最小探针曾保留外层 body 却增加一个公开 `_private_1`，因此没有采用。未经人类明确批准，B/C 仍不得实施；最终 A 成功不追溯构成对这些历史备选的授权。

## 原接口、背景与问题成因

基线 `KIP126/Literature/Standard.lean:22` 开始 `@[expose] section`，目标在该作用域内：

```lean
public def nuPage_weightShift :
  ∀ (X : ClassicalObject) (r s t w : ℤ),
    (model.family.nu model.nu (X.obj model.auxiliary)).Page r (s,t,w) ≅
      (model.family.obj ((SyntheticCategory.biShift (0,-1)).obj
        (model.nu.functor.obj (X.obj model.auxiliary)))).Page r (s,t,w-1) := by
  sorry
```

所有参数均已显示，没有 `2 ≤ r`、完备性或文献结果包前提。`model` 是同一 `KIP126.AdamsSynthetic.Standard.model`；`Spectrum`、`SyntheticSpectrum` 属于 `Type 1`，范畴 Hom 和谱页模块位于 universe 0。声明本身没有 universe 参数，锁中 `universes=[]`；类型指纹 `9179508221779199779`，基线待补证明体指纹 `14809824882972076594`。

完整 elaborated rendering（既有接口锁的原文；本审查未重新执行 kernel capture）：

```lean
(X : KIP126.Kervaire.Route.ClassicalObject) →
  (r s t w : ℤ) →
    CategoryTheory.Iso.{0, 1}
      (KIP126.Synthetic.SpectralSequence.SyntheticAdamsSS.Page.{0}
        (KIP126.Synthetic.SpectralSequence.SyntheticAdamsFamily.nu.{1, 0, 1}
          (KIP126.Kervaire.Route.ModelData.family.{1, 0, 1}
            (KIP126.Kervaire.Route.Model.toModelData.{1, 0, 1} KIP126.AdamsSynthetic.Standard.model))
          (KIP126.Kervaire.Route.ModelData.nu.{1, 0, 1}
            (KIP126.Kervaire.Route.Model.toModelData.{1, 0, 1} KIP126.AdamsSynthetic.Standard.model))
          (KIP126.Kervaire.Route.ClassicalObject.obj.{1, 0}
            (KIP126.Kervaire.Route.ModelData.auxiliary.{1, 0, 1}
              (KIP126.Kervaire.Route.Model.toModelData.{1, 0, 1} KIP126.AdamsSynthetic.Standard.model))
            X))
        r (Prod.mk.{0, 0} s (Prod.mk.{0, 0} t w)))
      (KIP126.Synthetic.SpectralSequence.SyntheticAdamsSS.Page.{0}
        (KIP126.Synthetic.SpectralSequence.SyntheticAdamsFamily.obj.{1, 0}
          (KIP126.Kervaire.Route.ModelData.family.{1, 0, 1}
            (KIP126.Kervaire.Route.Model.toModelData.{1, 0, 1} KIP126.AdamsSynthetic.Standard.model))
          (CategoryTheory.Functor.obj.{0, 0, 1, 1}
            (KIP126.Synthetic.Context.SyntheticCategory.biShift.{1, 0} (Prod.mk.{0, 0} 0 (-1)))
            (CategoryTheory.Functor.obj.{0, 0, 1, 1}
              (KIP126.Synthetic.Context.NuFunctorData.functor.{1, 0, 1, 0}
                (KIP126.Kervaire.Route.ModelData.nu.{1, 0, 1}
                  (KIP126.Kervaire.Route.Model.toModelData.{1, 0, 1} KIP126.AdamsSynthetic.Standard.model)))
              (KIP126.Kervaire.Route.ClassicalObject.obj.{1, 0}
                (KIP126.Kervaire.Route.ModelData.auxiliary.{1, 0, 1}
                  (KIP126.Kervaire.Route.Model.toModelData.{1, 0, 1} KIP126.AdamsSynthetic.Standard.model))
                X))))
        r (Prod.mk.{0, 0} s (Prod.mk.{0, 0} t (HSub.hSub.{0, 0, 0} w 1))))
```

目标给出同一个 ν(X) 的三分次谱页，到 `(0,-1)` biShift 后同一对象的谱页同构，页号 r 和 s、t 保持，权重 w 变为 w−1。它不是从两个抽象同维模块任意选等价。后续 `nuPage_e2` 还要求该同构在 E₂ 上与同一 `model.comparison.nuE2` 标签相符；那是独立、仍未补的责任，本权移构造成功不自动证明该标签方程。

`NuPageCoordinates` 把该同构与 E₂ 标签方程绑定；`NuPageCoordinates.lambda` 用它的 `.hom` 后接同一 synthetic λ 箭头在 family 上的 pageMap，形成 `pageLambda`。原接口是直接可调用的固定数学对象，不要求下游提供结果包。

成因是 Lean 模块公开性与辅助证明生成机制：

- 在 exposed 数据定义体中直接使用含 Prop 子证明的战术构造，会生成公开 `_proof_*`，冻结的 public export 集合不允许自动扩张。
- 简单将数据构造移到 private def，再由 exposed public def 引用该 private 数据名，触发公开语境下不可访问私有数据的检查。
- `no_expose` 允许定义体使用私有实现，但原公开定义体的可见性随之改变。

这是**实现封装不足与公开能力约定差异**。没有数学反例，也没有证据表明目标漏掉数学前提。一次包装失败不能推出原接口无法实现，更不能以改检查或改锁掩盖额外导出。

## 真实前提与对象核对

| 条件 | 独立结论 | 证据、局限和责任 |
| --- | --- | --- |
| 同一固定 ν、family、auxiliary 和 X | 满足候选构造的源码要求 | `WeightShiftProbe-3.lean:16–35` 直接使用同一 model，选择 `.nu X`，没有替代模型。上游固定对象仍待构造。 |
| r≥2 的权移坐标 | 与完整类型吻合 | `Standard.shift_page (0,-1) (.nu X) r hr (t-s,w) s`，源 `(s,(t-s)+s,w)`，靶 `(s,(t-s)+0+s,w-1)`，均用整数等式重分次到目标。 |
| 全部 r∈ℤ，包含 r<2 | 候选处理了边界 | 实际 `Page` 采用 `(r-r₀).toNat`；family.firstPage=2，r<2 时为 0，与 E₂ 同页。两端分别作 eqToIso，组合 r=2 的实际 shift_page。没有偷加 r≥2 前提。 |
| 真正的上游调用 | 已登记，可在本模块使用 | `KIP126/AdamsSynthetic/Standard/Operations.lean:273–276` 的 `shift_page` 仍为待补构造，责任属 AdamsSynthetic。使用它不是接手其责任。 |
| E₂ 标签与比较见证 | 尚未完成 | `nuPage_e2` 仍 pending，不能因数据类型通过就说这个固定同构的标签兼容已证。 |
| 暴露能力 | 基线有；no_expose 会撤销 | 锁定 Lean `MutualDef.lean`、`Environment.hasExposedBody`；普通 module import 语义，不以 import all 的访问能力替代。 |
| 公共辅助声明全部私有 | 直接候选不满足 | 保存的 public capture 含目标下 8 个新的公共 `_proof_*`。它们是证明声明，不是 8 个新增公理。 |
| a48 权移来源与当前全有限页目标相同 | 不能直接等同 | 历史 realization 权移数据和 E∞ 权移构造的对象/层次不同；当前适配借助当前已登记 finite-page shift_page。 |

## 来源范围与数学构造核验

a48 的 `Def/Comparison/ClassicalSynthetic/RealizationWeights/Data.lean:36–45` 是同一 λ 反演 realization 的 `RealizationWeightComparison` 数据，保留单位、λ 与自然性；其结构声明本身不是本全整数有限页接口的证明。a48 的 `Def/Synthetic/EInfty/Shift/Canonical/Proofs.lean:188` 的 `canonicalWeightShift_exists` 是实际 tower 的 E∞ 构造；`Literature/Standard/Sphere/EInfty.lean:14–19` 用它选出 standardEInftyWeightShift。E∞ 构造不能直接冒充每个有限页的同构，也不能忽略所用 tower 和 source comparisons。

本次候选实际适配的是当前上游 `shift_page`，它已经在冻结的 AdamsSynthetic 接口内登记。报告员独立检查了当前 `Families.lean:55–92`、`SpectralSequence/Basic/Data.lean:321–325` 和 `Standard/Operations.lean:273–276`，确认该路径保留对象、整数分次及 r<2 的项目页面约定。它不需要新引用一个外部文献公理，不从 a48 的文献结果包提取新假设，也没有从历史 E∞ 自然性公理提升出有限页结论。

本报告审查的是固定上游接口的内部组合及软件可见性，未声称重新证明 BHS 或当前 `shift_page` 的原始数学定理；这些原始来源、条件和未证责任继续由已登记上游承担。

## 独立证据与复现

### 已实际验证的记录

本报告员只做只读分析，没有执行 Lean/Lake/freeze，也没有修改源码、接口锁或检查。对协调者保存的记录进行了独立读取、哈希与依赖图复算：

- `validation/worker-comparison-WeightShiftProbe-3.json`：exit 0；对应 `.lean` SHA `39487a4a298273ecf0f8918c1bfe61c4ffe633892e08def9f1aa1bff6ccf98c3`，`.log` 为空。该 probe 的主体是完整数学目标的 `example`，不等于目标在原 exported 名称下已成功封装。
- 保存 public capture SHA `ae4e787c690c6f5555994a7510a9b1884f37333014ec7d911381d95d5c9c1d9e`；保存 trust capture SHA `4e8792ea3d739af31e73d9e488161e8f2886e231e0ca99107bd5f966978cfb1a`。其中直接公开构造目标 `direct_sorry=false`、`synthetic_sorry=false`、`is_axiom=false`，类型和宇宙匹配基线，但新增目标辅助导出如下：

```text
KIP126.Literature.Standard.nuPage_weightShift._proof_1
KIP126.Literature.Standard.nuPage_weightShift._proof_2
KIP126.Literature.Standard.nuPage_weightShift._proof_3
KIP126.Literature.Standard.nuPage_weightShift._proof_4
KIP126.Literature.Standard.nuPage_weightShift._proof_5
KIP126.Literature.Standard.nuPage_weightShift._proof_6
KIP126.Literature.Standard.nuPage_weightShift._proof_9
KIP126.Literature.Standard.nuPage_weightShift._proof_11
```

这些辅助项均不是公理，没有直接/synthetic sorry；部分传递 axioms 含已有上游的 `sorryAx`。整个首轮 capture 还有其他候选的额外生成项，不能把其全部归因于本权移定义。

- `validation/production-batch-2.log:203–205` 实际报 `Unknown identifier nuPageWeightShiftImpl`，并说明同模块有该 private declaration，但此位置需要 public。该批还有另一类型错误，因此没有把整批失败都归咎于包装。
- 原 `validation/VisibilityProbe.lean` 展示 no_expose wrapper 的最小源码；任务协调者报告其 exit 0，但本报告员没有找到其专属 `.json/.log`，所以不把该文件存在作为独立确认的执行成功。锁定编译器源码足以确认其可见性语义，尚需实际普通 import 对照来验证选择的完整包装。

### `private_decl%` 新内部路线的实际进展

已独立读取最新 `VisibilityPrivateDeclProbe-1.json/.lean/.log`：exit 0，Lean SHA `0a37e8af67bc20b3b41ce49cfe8ccaf1fa38bd66dd97c3a69dd7284e3bc93f5a`。最小源码保留 `@[expose] public def wrapper`，定义体使用 `private_decl% dataImpl n`。实际输出：

```text
hasExposedBody wrapper = true
wrapper body = fun n => VisibilityPrivateDeclProbe.wrapper._private_1 n
body dependency VisibilityPrivateDeclProbe.wrapper._private_1: exported=true, exposed=false
new exported declaration: VisibilityPrivateDeclProbe.wrapper._private_1
new exported declaration: VisibilityPrivateDeclProbe.wrapper
```

所以该原生机制确实绕开直接引用 private 数据的错误，保留外层 wrapper body，但目前最小探针多出一个公开 `_private_1`；名字里的 `_private` 字样不等于它是 Lean 的 `isPrivateName`，不能据字样过滤导出检查。

`VisibilityPrivateDeclConsumerProbe-1.json` 为 exit 0，SHA `c9c29de879582e4bacc93572ec4f6075f72d352fefaec0db1fa1e5b74ce079ad`。但源码是在同文件使用 `#with_exporting example ... := rfl`，并非另一文件普通 import。尤其 Prop 战术会按 `SyntheticMVars.lean` 临时退出 exporting scope，因此该结果不能单独证明普通外部模块可展开穿透隐藏实现。协调者仍需实际独立 consumer、完整出口捕获和真实目标封装测试。本报告没有把尚无实际日志的 WeightShiftPrivateDeclProbe 当作成功证据。

### 锁定 Lean 编译器的独立源码证据

精确工具链为 `/root/.elan/toolchains/leanprover--lean4---v4.32.2/src/lean/Lean/`，未升级：

| 文件 | SHA-256 | 独立核对位置与意义 |
| --- | --- | --- |
| `Elab/MutualDef.lean` | `8ece8e532e13d63e37f3ebebdd1e067d9c7071759eda866c735db0a90546c0de` | 20–51 定义 expose/no_expose；1342–1384 依据属性切换 exporting，no_expose 在 exposed section 内仍生效。 |
| `Environment.lean` | `100b207523d1005ae87f62f4e1693806854a35c59cd9b3210dfeeaa875d0ff98` | 844–848，`hasExposedBody` 查询公开环境中的 ConstantInfo.hasValue。 |
| `Elab/BuiltinTerm.lean` | `a4b4279878e30d55f6c3027c4985a4f078b2ef3dddeed3a4b685b1146f801b3f` | 464–485，private_decl% 在 exporting 时切到 withoutExporting，创建辅助 definition 并返回其引用，另设 inline。源码不保证没有新公开常量。 |
| `Elab/SyntheticMVars.lean` | `e33b9ec83b5ca5108b910419fda0492a36a7837cb205d7594429fb6ed9ea22fc` | 458–463 的 backward.proofsInPublic；后续 runTactic 对 Prop 子目标可能生成公开辅助定理。 |
| `Meta/AbstractNestedProofs.lean` | `0c15c160c399770e90c209bfd23944855dd888811ab7cf4aa0a3e81ec7bf92df` | 38–67 识别 trivial proof，头及全部实参原子时跳过抽取；后续抽取非平凡嵌套证明。 |

这些是当前锁定编译器的实际实现，不是未核实的当前网络建议。可见性差异在生产者和消费者均启用 `module` 的场景生效，正是本仓库正常消费方式。普通 public import 可调用同构名称，与取得该定义体是不同能力；import all 的同模块访问不能替代正常消费验证。

### 同目录复现

另保存 [ordinary-consumer-first-failure.json](ordinary-consumer-first-failure.json)：首版普通消费者实际 exit 1 的原因是探针在 `module; import KIP126.Literature` 后查询 `env.hasExposedBody`（强制进入当前消费者的公开再导出环境）。锁定编译器 `Environment.lean:2265,2289` 只将 `isExported` 的导入加入该 public map，`Elab/Import.lean:38` 把没有 `public` 的 module import 设为私有。因此这次失败本身不证明生产定义丢失曝光能力。普通消费应在当前 `env.find?` 中检查 value；检查消费者的公开再导出环境时则需 `public import`。协调者已修正探针源码，修正后的实际 exit 0 结果及 public import 对照记录见最终复核结论和 final-resolution.json。失败日志与当时源码的哈希没有绑定，本报告明确保留这一证据局限，没有把修正后的源码误配给旧失败。

[reproduce.py](reproduce.py) 固定读取 git 基线、a48、实际保存 capture 和编译器源码，输出 [evidence.json](evidence.json)，不会运行 Lean/Lake 或写源码。实际执行命令：

```sh
python3 /inspire/hdd/global_user/czxs25250150/Kervaire126Main/metadata/interface-reviews/Literature/20261017-01-weightshift-exposure/reproduce.py /tmp/kip-literature-20261017-01
```

结果 exit 0；精确识别上述 8 个新公开 helper，类型指纹不变、无目标回环、不达争议 stem62。JSON 包含原完整类型、源定位、文件哈希、全部 25 项传递待补及最小探针实际输出。它重放保存记录的只读审计，不假称重新执行编译器。

## 循环、未证及矛盾依赖审计

原始成功候选 capture 的递归依赖复算：

```text
cycle_back_to_target = false
reaches_stem62_exponent_two = false
transitive_pending_count = 25
```

25 项均在 AdamsSynthetic：24 项固定 Background 数据，加 `shift_page`。没有调用 `nuPage_e2`、本目标自身或受 stem62 争议影响的声明来完成本构造；没有通过不一致环境推出 False；没有新数学公理或额外定理前提。直接 `sorry` 的公开占位符仍存在时，其责任当然尚未消除。

源码直接构造的可用性以登记上游为条件。若最终原边界内包装通过，可记录 Literature 本地直接责任消除，并保留这些真实传递依赖；不能声称整个权移数学背景已经无未证依赖。`nuPage_e2` 的标签责任另计，不以“存在一个同型的 Iso”自动抹去其同一见证要求。

## 方案及精确差异

### 方案 A：优先保留原接口的内部方案

必须保持以下不变量：完整类型及所有 r、相同 ν/family/对象/分次；目标原公开名称；原 exposes body 能力；原导出集合；辅助声明私有；不新增公理/待补责任。以下保留初审内部路线的比较；第 1 条未采用，第 2 条随后已由实施者落实并通过最终验证，报告员没有实现生产补丁：

1. **原生 private_decl% 封装**。保持 public def 在 expose section 内，以原私有构造为数据来源，完整签名不改：

```lean
public def nuPage_weightShift :
  ∀ (X : ClassicalObject) (r s t w : ℤ),
    (model.family.nu model.nu (X.obj model.auxiliary)).Page r (s,t,w) ≅
      (model.family.obj ((SyntheticCategory.biShift (0,-1)).obj
        (model.nu.functor.obj (X.obj model.auxiliary)))).Page r (s,t,w-1) :=
  private_decl% nuPageWeightShiftImpl
```

原生最小测试表明它仍可能额外公开一个 `_private_1`；必须解决或经人审明确接受该导出，不能称已原样保持。如果实际目标生成的公开辅助集不空，则该具体方案尚未满足 A。

2. **直接 term 构造，显式全部证明参数**。在原 exposed def 内直接组合 `shift_page`、eqToIso 和整数重分次，不引用不可公开的私有数据名；用已有公共定理的原子应用代替会生成 helper 的 by 子块。`backward.proofsInPublic` 可改变 Prop 战术阶段的立即抽取，但 `PreDefinition/Basic.lean:120–127` 仍执行 `abstractNestedProofs`，所以只开启该选项不足以保证没有辅助导出。需核对所有隐式参数/证明参数，避免非平凡嵌套证明再次被抽取。初审时该路线尚未验证，不能断言不可能；随后实施者以公开原子证明实参和显式 `Eq.rec` 完成了它，实际成功与接口保持证据见本报告开头和 final-resolution.json。

A 中任何真正保留接口的实现属于已授权的正常补构造，不需人类确认；本报告的 pending 状态只保留对 B/C 等实质变更的审核，不能阻止协调者继续 A。

### 方案 B：仅撤销定义体暴露

精确差异是原 exposed section 中目标声明增加一个属性，完整类型全文保持不变：

```diff
-public def nuPage_weightShift :
+@[no_expose] public def nuPage_weightShift :
```

并以同一个 `nuPageWeightShiftImpl` 取代 sorry 作为实现。没有增加数学前提，没有改变结论、宇宙、r 范围、对象或同构身份；但普通模块中目标 ConstantInfo 将不再含可见 value，`hasExposedBody` 从 true 变 false，消费者无法按原方式取得和展开其定义体。保留 `.hom` 的使用能力不等于保留定义展开能力。

该能力目前不在本仓库类型/宇宙/名称指纹中；这说明当前检查覆盖存在局限，不意味着可以自行应用变更。本方案需要用户针对**此目标和此属性**明确授权。不能顺带把 Standard 其他定义、nuPageData 或 pageLambda 改为 no_expose。

### 方案 C：允许精确新增的辅助导出

保留原 exposed 完整数学签名和直接构造，接受上列 8 个 `_proof_*` 名称为额外导出，或接受另一经过新 capture 精确列出的辅助集，例如 private_decl% 产生的一个 `_private_1`。它们不是新增数学假设，但公开声明数与名称集合确实扩大，违反原“辅助声明私有”的冻结边界。直接证明的 8 个名称与 private_decl% 的单个名称属于不同候选，不可互相视为授权。

本方案需要人类明确选择候选及新增名称范围；更新锁时只能登记获准的精确差异。不能全局忽略 generated declarations、按 `_proof`/`_private` 字符串过滤、放宽检查或批量刷新六模块锁来接纳未审查导出。

## 下游影响

直接源码调用只有：

- `Standard.nuPage_e2`：类型含 `(nuPage_weightShift ...).hom`，同构的 E₂ 标签仍待补。
- `Standard.nuPageData`：把目标赋给 `weightShift` 字段。

其后传递到 `pageLambda`，再到 `free_lambda`/`freeData`、`inversion_lambda`/`inversionData`、`classicalLift` 及其微分/λ 兼容。保存的 Literature trust capture 的反向闭包为 11 项；该 capture 不含 Main，不能据此宣称获得全项目 kernel 依赖闭包。

对当前 `KIP126/`、`Tests/` 做源码搜索，未发现其他直接名称调用，也未发现 `unfold nuPage_weightShift`、`simp [nuPage_weightShift]` 或针对其实现的 rfl 用法。这只限定现有源码命中，不证明公开展开能力等价；外部普通消费者仍属于被冻结公共接口的范围。

责任仍归 Literature，本报告没有将其封装任务转给下游。AdamsSynthetic 的 `shift_page` 和固定 background 数据继续保持原责任，不新增上游接口；`nuPage_e2` 的标签匹配由 Literature 后续完成。

记录/验证影响：

- A 若通过，只同步真实源码、来源、私有构造复用证据、证明状态及待补责任，保持接口锁。不能把仅 private 构造已证登记成 public 责任消除。
- B 若获准，应明确记录曝光能力差异及用户真实授权，同时按最终构造的真实依赖更新 sources、obligations；不伪造类型差异。
- C 若获准，需精确更改 Literature API 的获准导出集合及对应生成声明记录，保留其真实来源和类型；不批量刷新其他模块。
- `Tests/Literature/Interface.lean` 的全类型/宇宙/导出检查应继续保留；当前不会检查 hasExposedBody，不能把它通过当作 B 保持原接口的证据。
- `Literature/InternalAudit.lean` 容许精确登记的 pending sorry，因此保留 public sorry 时 build 通过也不是目标完成。
- 最终仍由协调者串行执行真实普通 public import、exposure 对照、精准 public/trust capture、LiteratureChecks、ArchitectureChecks、Integration/Trust、source inventory 和完整 `lake build`。不要为本报告另启动会写 Lake 状态的并发进程。

## 阻塞范围与继续项

**本问题当前无阻塞目标。** 方案 A 已保留原公开类型、对象/分次、exposure 和全部导出集合；`nuPage_weightShift` 的公开直接构造已交付，不能继续按本封装问题冻结它。B/C 未采用、没有人类批准记录，也无需为合法的 A 补构造另设批准流程。

历史上暂停的是“把已证私有构造在原公开接口下交付并移除直接责任”；现在这一封装条件已满足。独立 `nuPage_e2` 标签方程和上游 `shift_page`/固定模型数据的待补责任不因此完成。完整构建中另有 body 指纹核查，不能用本报告的解除阻塞替代其验证。

其他六项独立迁移及后续真实证明可继续，保持原职责。不得扩大本报告结论为任意 `no_expose`、新增辅助导出、改检查或其他接口调整的授权。

## 已确认事实与未决部分

已确认：原始全整数目标有成功构造；同一对象、坐标与 r<2 边界匹配；早期直接 exposed 战术版本确有 8 个新增公共 helper；简单私有数据包装和 private_decl% 方案没有成为最终实现；no_expose 的能力差异真实存在但从未实施；最终直接 term 保持原 exposure，普通/公开两种消费者和精确接口检查均成功，最终754项导出名/完整类型/宇宙全部不变。

实际成功记录为 `validation/ordinary-consumer-corrected.json`、`public-consumer-final.json`、`public-capture-final.json`、`interface-final.json`（均 exit 0）。旧 `ordinary-consumer-final.json` 的 exit 1 留作首版误测历史，不能误当最终结果。报告员独立复算最终 capture、读取消费者源码与日志，没有自行运行 Lean/Lake。

未决：`nuPage_e2` 的 E₂ 标签兼容、已登记 AdamsSynthetic 传递待补，以及协调者正在处理的完整构建 body 指纹核查。本报告不把这些责任隐藏为“所有数学证明完成”，也不把它们误认作本次已解决的封装问题。

## 人类审核记录

尚无人类对本报告的 B/C 或其他具体变更作出明确决定。`human_decision: null`。agent 的判断、内部实现通过、等待或另一问题的批准均不构成本项接口变更授权。报告员未实施任何生产变更。
