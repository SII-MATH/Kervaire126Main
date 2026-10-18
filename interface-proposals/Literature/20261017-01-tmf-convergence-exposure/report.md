---
title: tmf 收敛构造的公开封装
archived_from: local-history/metadata/interface-reviews/Literature/20261017-01-tmf-convergence-exposure/report.md
archived_sha256: 7b3a18f9668900be45cf5281a0ad13bbe5ccee2ec9c5ff424046d0a087ba462c
summary: "实际收敛构造产生 19 个自动公共证明；已批准这 19 项精确导出，不涉及发现数学反例。"
issue_id: "20261017-01-tmf-convergence-exposure"
responsibility_module: "Literature"
targets:
  - "KIP126.Literature.Standard.tmf_convergence"
baseline_commit: "bef90640c4594af4db32c86837f9d95340d1e171"
worktree: "/tmp/kip-literature-20261017-01"
candidate_source_commit: "a484b981fad612eabe2bc7a01b54e049e9a01ce4"
api_file_and_sha256: "metadata/literature-api.json:66afd5aaf52646c55a40b98867689bc05279d5a4394a016857456a1420d81c19"
source_file_and_sha256: "KIP126/Literature/Standard.lean:8ba89e65cd91d11783ea3aa08fc83f5891337c1f7aaa6e8abfb39ae440072bd6"
reporter_agent: "/root/report_tmf_exposure"
independent_of_discoverer_and_implementer: true
evidence_level: "实际固定对象的条件性 Lean 构造成功；具体公开导出检查失败；编译器机制由安装版本源码独立核对"
applied_safe_fallback_source_sha256: "f73c1ad8b6fda516b8fac98758492b67e258e4692ce280b11719d6922f114377"
status: approved-interface-change
human_decision: "2026-10-17，本聊天用户：同意以上提案，修改原接口。具体范围见文末本轮批准记录。"
---

# tmf 收敛构造的公开封装人审报告

## 请求人类决定的具体问题

本报告只涉及 `tmf_convergence` 的公开封装。其固定对象上的完整实际构造已编译成功，但该具体公开 exposed 实现产生 19 个新增公开自动证明声明，与冻结的 754 个 Literature 导出冲突。这里没有发现数学反例、漏数学前提或对象关联错误，也没有证明所有保留原接口的写法均不可能。

当前合法处理是保留同一构造为私有辅助，公开目标保持原类型、原 exposed 属性和原待补责任；继续其他可完成项。该处理无需将新增导出视为已授权。本报告不请求改结论、加假设、改对象、转移责任、关闭 exposed 或削弱检查。

需人类决定的唯一可选接口变化是：是否允许本具体构造额外公开 [附件逐项列明的19个证明声明](proposed-additional-exports.md)，使 Literature 导出由754变为773，同时保留原754项的全部签名/语义/expose？精确机器清单为 [proposed-additional-exports.json](proposed-additional-exports.json)，SHA-256 `733e172b916e6e70adedb8d31e91e25d365a957b34c3b480bdbf170b329525a1`。这是本候选的精确附加范围，不声称是全局最少辅助数；不包含任何 `.eq_1`，也不授权任意未来自动 helper。若不批准，维持当前合法处理并继续研究纯现有公共常量的保留接口路线。

## 原接口、背景与问题成因

原公共源声明（无额外隐式参数、实例参数或宇宙参数）：

```lean
public def KIP126.Literature.Standard.tmf_convergence :
  KIP126.AdamsSynthetic.ClassicalTowerConvergence
    KIP126.AdamsSynthetic.Standard.model.classicalTower
    KIP126.Literature.Standard.tmf
```

冻结 elaborated 完整类型为：

```lean
KIP126.AdamsSynthetic.ClassicalTowerConvergence.{1, 0}
  (KIP126.Kervaire.Route.ModelData.classicalTower.{1, 0, 1}
    (KIP126.Kervaire.Route.Model.toModelData.{1, 0, 1}
      KIP126.AdamsSynthetic.Standard.model))
  KIP126.Literature.Standard.tmf
```

`universes=[]`，类型指纹 `4432180332182918807`。范畴实例取固定 `AdamsSynthetic.Standard.Spectrum`、其 `spectrumCategory`、`spectrumCofiber` 以及固定 model/coefficients/classical 数据；这些并非新加到声明上的可选实例。接口位于 `@[expose] section` 内，普通公共消费者应可读取该定义的 exposed body。公共辅助新增也属于导出变化，不能只看目标声明类型没变。

这里的 `ClassicalTowerConvergence` 含两项：对全部 `p : ℤ × ℤ` 的真实 `E∞ ≅ grF`，以及该同构与同一塔提升、同一无限代表和同一滤过见证相容的 `canonical` 条件。它按定义并不额外断言滤过 separated 或 complete，不能与另一文献中的强收敛术语直接互换。固定 canonical 条件如下：

```lean
∀ (p : ℤ × ℤ)
  (a : HomotopyGroup (p.2-p.1) ((P.tower X).stageAt p.1))
  (z : (Subobject.underlying.obj (((A.obj X).ssData p).Z ⊤) : ModuleCat ℤ)),
  (P.sequence X).infiniteRepresentativeE1 p z = (P.tower X).layerMap p a →
  ∀ b : (Subobject.underlying.obj
      ((P.tower X).filtration.F p.1 (p.2-p.1)) : ModuleCat ℤ),
    ((P.tower X).filtration.F p.1 (p.2-p.1)).arrow b =
      a ≫ (P.tower X).projection p.1 →
    (e p).hom (((A.obj X).ssData p).pageπ ⊤ z) =
      (P.tower X).filtration.toAssociatedGraded p.1 (p.2-p.1) b
```

候选沿固定 `tmfIso : tmf ≅ model.auxiliary.detector`，把已登记的 `model.classicalConvergence .detector` 搬回实际 tmf。它实际构造同伦群、塔滤过商和 E∞ 的同构，再验证上面全部量词的条件。这是新的当前对象适配构造，并非把旧文献结果包字段改名。

失败成因属于编译后公开封装与冻结导出边界的冲突。Lean 4.32.2 对 exposed 数据定义里的复杂 Prop 子项产生公开 `_proof_n`。batch5 的原始检查实际列出 24 个新导出：19 个目标下 `_proof_1` 至 `_proof_19`，另有 5 个由其他 unfolding/simp 触发的 `.eq_1`；后五项是独立的可修复实现细节，不应混入本项所需授权范围。

## 真实前提与对象核对

| 前提或对象条件 | 是否满足 | 证据及仍依赖的待补责任 |
| --- | --- | --- |
| X 是冻结的 `Literature.Standard.tmf` | 是 | 候选直接使用该常量；tmf 本身的构造仍是 Literature 已登记待补。 |
| 比较同构是冻结的 `tmfIso` | 是 | `let e := tmfIso`；该同构构造仍待补，未换成另选对象。 |
| 塔是固定的 `model.classicalTower` | 是 | source/target 的 tower、projection、layerMap、sequence 全来自同一个 P。P 的背景构造仍是 AdamsSynthetic 已登记待补。 |
| detector 收敛是上游登记接口 | 是 | `model.classicalConvergence .detector`，最终来自 `AdamsSynthetic.Standard.classicalConvergence` 的待补；没有在 Literature 假装补掉它。 |
| 固定滤过确为实际塔投影的 range | 是 | `tmf_filtration_map` 用同一 a 复合 `(P.map f).stage`，由 `P.map f` 的 projection 方块证明；不另选滤过。 |
| 全部分次及边界 | 是，未缩小目标范围 | p、s、m 均任意整数；负滤过通过既有 `stageAt`/`toNat` 定义处理，未新增非负/有限范围假设。 |
| E∞ 与滤过商的识别为实际比较 | 是 | E∞ map 来自 `model.classical.map e.hom`；商同构由实际 subobject/linear equivalence 和 cokernel.mapIso 构造。 |
| canonical 保持同一提升见证 | 是 | `a' := a ≫ (P.map e.hom).stage p.1.toNat`，`z'` 是同一 z 的 cycleMap，b' 满足原 b 的 arrow/q 方块，随后调用 detector 的 canonical。 |
| 不用未验证强收敛前提替代当前目标 | 是 | 本候选不使用 a48 的 nilpotent-complete/finite-kernel 泛型定理来跳过当前 canonical。 |
| 公共754导出及 exposed 原样保持 | 该具体候选未满足 | 实际 `Tests.Literature.Interface` 报新增声明；不能据 probe exit0 记直接责任已完成。 |

商同构 q 虽由带性质的存在命题取 `choose`，但非任意模型替换：其在每一真实滤过代表上的值由 arrow 方块和 cokernel π 方块指定。arrow 的 mono 性使 b' 唯一，cokernel π 的 epi 性使 q.hom 唯一。这里不把仅有 `Nonempty` 或仅有抽象同构当作 canonical 比较。

## 独立证据与复现

报告员此前未参与该候选发现或实现。本报告独立读取规则、协议、模板、完整目标、实际候选体、当前结构定义和安装版编译器源码；只写本报告独占目录及获准的工作树报告子目录，没有运行 Lean/Lake、改生产、改接口锁或审核自我实现。

证据均复制到本目录 `evidence/`，来源绝对路径及 SHA-256 见 `evidence-manifest.json`。`Standard-public-candidate.lean` 的完整文件哈希为 `8ba89e65…072bd6`。独立提取其目标 body，与协调者已通过的 `tmf-convergence-direct-probe-5.lean` 比较，二者完全相同，规范化目标 body SHA-256 为 `0e07da064ae31f2e8dce1b092130c82cc98a6dc3f6a6b18b0ba597c065a2917c`；比较结果见 `candidate-vs-passed-probe.diff`（空文件即无差异）。

协调者已实际执行并保存结果：

```sh
# 工作目录 /tmp/kip-literature-20261017-01
lake env lean metadata/proof-sessions/runs/Literature/20261017-01/absorb-21-20261017/validation/tmf-convergence-direct-probe-5.lean
# exit 0；完整候选文件 SHA a61716594c6c113a7716bcbe5f9dc9d15531c0953fbcd2e20ac8b621d0a6a0c3
lake build LiteratureChecks ArchitectureChecks
# batch5 exit 1；实际失败 Tests.Literature.Interface:13
# “Public exports changed; added: …tmf_convergence._proof_1…19…; missing: []”
```

机制最小复现为同目录 `ExposedPackagingProbe.lean`：数据类型使用 `{m : Nat // m = n}`，比较原子公共证明项、嵌套 `by`、私有定理引用和复合证明项。协调者对应记录 `exposed-packaging-probe.json` 实测 exit 0（包含预期 `#guard_msgs` 私有引用错误）；它只核验机制，不是 tmf 数学反例。该 probe 不纳入生产，也不申请其导出。

独立核对安装版 primary source 的结论（具体行号、原文和全文件 hash 见 `compiler-source-excerpts.md`）：

1. `Lean/Elab/SyntheticMVars.lean:458–526` 的 `backward.proofsInPublic` 仅控制 tactic proof 是否先离开 exporting 上下文并经 `mkAuxTheorem` 重新包装。
2. `Lean/Elab/PreDefinition/Basic.lean:120–127,183` 对数据定义仍调用 `Meta.abstractNestedProofs`。它与前一选项是两条独立阶段。
3. `Lean/Meta/AbstractNestedProofs.lean:40–66,94–117` 对非原子应用的 Prop 子项抽取辅助定理；整个值本身是 proof 时才跳过这一整步。目标是含实际同构数据的结构，不能把它改成 Prop theorem。
4. `Lean/ResolveName.lean` 和 `Lean/AddDecl.lean` 显示 private 名称不在 exporting 环境可见；`backward.privateInPublic` 会真实加入公共环境。使用该选项会违反本任务边界，不是合法的隐藏实现办法。

这些机制解释当前观察，并不构成“没有任何满足754导出的 proof term”的不可实现性证明。直接数据项用既有公共常量对原子参数的应用仍可能避开抽取；当前尚未找到完成全部 canonical 子证明的这样的写法。

### 来源和依赖审计

只读 a48 对应位置：`KIP126/Def/AdamsSynthetic/ComparisonStatements.lean:700–705` 的 `TmfDetectionData.convergence` 是结构字段；`KIP126/Literature/Source.lean:304–305` 携带源对象及比较；`KIP126/Literature/Assumptions.lean:11` 由 `adamsSyntheticResults` 外部公理提供整个包。它们本身不是当前目标的实际证明。

独立只读来源核查还确认，a48 全仓 `git grep` 对 `strong_of_acyclic_and_finite` 仅找到该定义，没有找到它产生固定 tmf 字段的调用；这只是给定提交的源码事实，不是未来不能构造的结论。

a48 同时有真实泛型证明 `KIP126/Main/AdamsSynthetic/SphereConvergence.lean:858–880`，要求 `[HasProductsOfShape ℕ C]`、`IsENilpotentComplete unit X` 和每一 n,s 的塔步诱导映射 kernel 有限。其结论是 `IsAdamsTowerStronglyConvergent unit X`；不是冻结的 `ClassicalTowerConvergence model.classicalTower tmf`。源泛型证明既未自动满足当前 tmf 的完整前提，也未自动给出同一当前 tower 的 canonical 方块。其 `associatedGraded_of_separated:639–684` 具体证明用同一 lift 生成 qj/qp 并比较 kernel，保留该具体构造再补计算式是一条可继续的内部路线；目前没有完成到当前固定 tower 的识别，不能把只读研究计作已迁入。当前候选使用已有登记 detector canonical convergence 沿固定 tmfIso 运输，不把这些源前提的尚缺实例说成已经迁入。

直接源体核对没有调用 `tmf_convergence` 自身、`tmfSourceData`、完整 Literature bindings、`stem62_exponent_two` 或 `False.elim`。构造需要真实上游 fixed-model/tower/family/cofiber 背景，且仍依赖 `tmf`、`tmfIso` 与上游 `classicalConvergence` 的待补。`Classical.choice`、`propext`、`Quot.sound` 是基础逻辑依赖；项目未证背景所带的 `sorryAx` 仍须保留。不能把“候选没有新的直接 sorry”写成“全部依赖无 sorry”。公开捕获已独立核对：`public-before-tmf-fallback-capture.json` 为774项，实际只多19个本目标证明常量和1个待内部修复的 `lambdaMultiply.eq_1`；原754项的 full_type/universes/type_fingerprint 全部未变，差异见 `independent-public-comparison.json`。完整 fresh trust capture（协调者 exit0；原始 artifact SHA-256 `712ca51ecbdd71c8a23ca18c74e92b805cebfc8e774d6cdf35e4fc17e6f5e474`）已归档 `evidence/trust-after.json`。我对实际私有构造的项目依赖闭包独立计算得到438个节点、无有向环；闭包不含公开 `tmf_convergence`、`stem62_exponent_two`，且没有项目 axiom 声明。私有主构造和19个私有自动证明均 `direct_sorry=false`、`is_axiom=false`；公开目标仍 `direct_sorry=true`。实际传递待补33项为 AdamsSynthetic31项与 Literature 的 tmf/tmfIso2项，逐名及全部可达边见 `independent-kernel-dependency-review.json`。这里包括固定 model 记录中未单独投影的其他上游字段，按实际 kernel 依赖如实保留；它们不因本项私有构造成功而被消责。private capture按其原工具设置不渲染私有 full_type，且自动编号与 public 时有重排，因此未据编号宣称19项逐字同型；public方案的精确19类型由独立公开捕获附件界定，完整数学源体一致性另有逐字符证据。

本报告附独立只读复核脚本，可在报告目录外直接复现证据检查：

```sh
python3 /inspire/hdd/global_user/czxs25250150/Kervaire126Main/metadata/interface-reviews/Literature/20261017-01-tmf-convergence-exposure/recheck-evidence.py
```

报告员实际执行该 Python 命令 exit0，输出 `PASS: 754 original public types; same complete private transport; no direct holes in private construction; no target/stem62/cycle; 33 retained pending dependencies; proposal remains unauthorized.` 它只读已保存的源快照和 kernel/public capture，不运行 Lean/Lake、不写生产文件。

## 方案及精确差异

**方案 A（当前已采用，保留接口）**：完整实际构造原封保留为

```lean
private def tmfConvergenceActualTransport :
  ClassicalTowerConvergence model.classicalTower tmf := by
  -- 同一 e、c、q、a、z、b 与全部 canonical 证明

public def tmf_convergence :
  ClassicalTowerConvergence model.classicalTower tmf := by
  sorry -- 保留本 session 之前即存在的直接责任，不新增责任
```

协调者已实际应用该保留接口方案；我独立读取新源并核实文件 SHA-256 为 `f73c1ad8b6fda516b8fac98758492b67e258e4692ce280b11719d6922f114377`，私有完整数学 body 与已通过 probe 的 public 数学 body 逐字符相等，公开目标仍为原类型加原 `sorry`。源快照和比较见 `evidence/Standard-private-fallback.lean`、`evidence/independent-fallback-source-comparison.json`；协调者随后实际 `lake build KIP126.Literature`（production-batch-6）exit0，2723 jobs；fresh public capture 恢复754项，我独立比较全部 full_type/universes/type_fingerprint 均与基线一致、无新增或缺失，见 `independent-fallback-public-comparison.json`。这些结论不代替其后的全部专项/信任检查和完整构建。对应补丁已归档 `private-transport-fallback.patch`。目标完整类型、前提、固定对象和 exposed 属性均无差异；私有辅助不得借 exporting 选项变相公开。该方案确实吸收可用的实际数学工作，但**没有消除 tmf_convergence 的直接待补**，记录必须如此。

**方案 B（仍保持754导出的继续研究）**：重写公共数据体，全部证明子项仅引用既有公共证明常量并用原子参数；实际对象、同构与 canonical 见证不能改变。未提供已通过当前完整目标的候选，因此不承诺这一路一定可行，也不应因暂未找到就冻结其他目标。辅助数据定义不能直接作为 exposed 目标的私有 shortcut。

**方案 C（须本报告的明确人类批准）**：恢复本报告留存的完整公开目标 body，并仅允许下列19个自动证明声明额外公开。原目标的签名、所有前提、固定对象、分次、canonical 见证以及原754项的签名/宇宙均无差异；变化是公共环境增加这些可引用的证明常量，因而显式打破原“所有辅助均私有”和754导出限制。它们不是新数学假设或结果包；其类型仍可能提及待补背景，相关 `sorryAx` 不能消去或隐藏。

```text
KIP126.Literature.Standard.tmf_convergence._proof_1
KIP126.Literature.Standard.tmf_convergence._proof_2
KIP126.Literature.Standard.tmf_convergence._proof_3
KIP126.Literature.Standard.tmf_convergence._proof_4
KIP126.Literature.Standard.tmf_convergence._proof_5
KIP126.Literature.Standard.tmf_convergence._proof_6
KIP126.Literature.Standard.tmf_convergence._proof_7
KIP126.Literature.Standard.tmf_convergence._proof_8
KIP126.Literature.Standard.tmf_convergence._proof_9
KIP126.Literature.Standard.tmf_convergence._proof_10
KIP126.Literature.Standard.tmf_convergence._proof_11
KIP126.Literature.Standard.tmf_convergence._proof_12
KIP126.Literature.Standard.tmf_convergence._proof_13
KIP126.Literature.Standard.tmf_convergence._proof_14
KIP126.Literature.Standard.tmf_convergence._proof_15
KIP126.Literature.Standard.tmf_convergence._proof_16
KIP126.Literature.Standard.tmf_convergence._proof_17
KIP126.Literature.Standard.tmf_convergence._proof_18
KIP126.Literature.Standard.tmf_convergence._proof_19
```

这19项的实际范围已核对：1–2为同伦群同构的两侧逆等式，3–4为 E∞ 同构逆等式，5为实际塔滤过函子性，6为同构保持滤过的 iff，7/14为环恒等的 RingHomInvPair，8/11/13为真实 cokernel 所需 HasColimit，9为带代表方块的泛型商同构存在，10/12为实际滤过单调性，15为当前 tmf/detector 的带代表商同构，16–17为经典 Adams 家族起页/微分分次约定，18为15在 p 的重索引，19为全部 canonical 条件。helper6/15/18/19类型里出现的局部前提是它们明确抽取的证明参数，由该同一完整 body 中已经构造的证明实参满足，不是给原目标新加的未证前提。

每项完整 elaborated 签名（包括全部隐式参数、类型依赖、宇宙 `[]`、分次及类型指纹）在 [附件](proposed-additional-exports.md)，机器清单 SHA 已在首节指定。长签名中展开的固定 model/typeclass 参数是实际 capture 原文，不能按简写替代以放宽授权。新增范围为原集合与这19项的并集，总数773；`lambdaMultiply.eq_1` 及 batch5 其他四项 eq_1 一律排除，必须由内部展开修复。这里没有经过验证的单个新增公开 generic-transport helper 方案，不能用未经实现的更小集合冒充现成替代。

若人类批准 C，协调者只能在批准范围内恢复本具体 public body、更新 Literature 对应导出集合/签名记录，并重新验证原754项全部不变、恰好新增上述19项、所有自动定理有实际证明且无新增直接责任、普通 exposed 消费和全部原检查通过。批准不会自动包含上游待补完成，也不允许改检查来容忍集合外声明。未经明确批准不得应用 C。

不建议关闭公开目标的 `expose`、改为 theorem/Nonempty、使用私有数据 wrapper、加结果包、新假设、`private_decl%`、改编译器、放宽检查或把本责任交给 Main/Computation；这些都不能作为本任务默认修复。

## 下游影响

- `KIP126/Literature/Standard.lean` 的私有 `tmfSourceData.convergence` 直接消费公开目标；`bindings.tmfSource` 经 `KIP126.Literature.Delivery` 将它提供给后续 Literature、ProofTools、Main 消费。这些调用无需新数学前提，但保留其传递待补。
- 方案 A/B 不改 `metadata/literature-api.json` 的754导出、完整类型、契约的对象关联、其他五模块责任或接口。`proof-obligations.json` 必须保留 tmf_convergence 直接责任。来源记录可诚实记录私有实际构造已吸收及公开封装尚缺。
- 若人类明确批准 C，仅可按附件逐项处理上述19个 Literature 新增 exports/其完整签名及对应 source/contracts/API 记录，公共集合目标为773；不得一次刷新六模块锁，不得新增数学待补，也不得删减既有检查。
- 当前保留接口版本的普通 import 消费和 public import 的 `hasExposedBody` 检查已由协调者实际运行 exit0；我已核对其代码确实检查 tmf_convergence 的 body 可见且仍保留原直接 pending，同时检查原 exposed 状态。原754全类型/宇宙/导出比对、fresh frozen-interface 检查也已通过。LiteratureChecks、ArchitectureChecks、Integration/Trust、源码清单检查及完整 lake build 由协调者在全 session 最终交付中另行覆盖；本报告不把 module build 或 batch5 失败当作全检查通过。

## 阻塞范围与继续项

只阻塞这一公开 `tmf_convergence` 构造从 pending 转为 provided 的记录，以及确实要依赖“本项直接责任已消除”的结论；不封锁现有登记接口的普通依赖消费。没有可信反例涉及本接口，所以不能把封装困难误当作禁止一切使用当前待补接口。

`tmfUnit`、`tmf_algebra_unit`、`theta5_lift`、两个 ν-cofiber 指数目标及 `weights_lambda` 等其他六项，以及 SSData/BHS/Toda 等真正可吸收私有辅助，均可继续独立整合、审计和构建。其他真实数学缺口按各自依赖闭包保留，不由此问题冻结整个 Literature。

## 人类审核记录

尚无对本报告具体方案与范围的人类决定。`status=pending-human-review`，`human_decision=null`。历史其他报告的批准、agent 建议、等待或沉默均不等于本项授权。


## 本轮批准记录（2026-10-17）

用户在本聊天阅览七份报告摘要后明确回复：

> 同意以上提案，修改原接口

本报告获准范围：

- 方案 C：恢复具体公开 tmf_convergence 构造，精确增加 _proof_1 至 _proof_19；原754项完整类型/语义保留。

该批准不是新增公理、额外待补责任、任意 Main 公共前提或未列明接口变更的授权。原文中的“尚未批准”保留为历史阶段记录；实现及实际验证另记，批准不表示证明已经完成。
