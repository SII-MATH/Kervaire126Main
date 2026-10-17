---
issue_id: "ProofTools-paper-prop620-domain-and-target"
responsibility_module: "ProofTools"
targets:
  - "AimPaper Proposition 6.20 (prop:dec738d3), first-clause domain"
  - "AimPaper Proposition 6.20, second-clause target association"
  - "KIP126.ProofTools.Paper.finiteExtension_descends (unregistered candidate)"
baseline_commit: "93fbf1215b16c9630198370c6ce3cbcff9eb4912"
worktree: "/inspire/hdd/global_user/czxs25250150/Kervaire126Main"
candidate_source_commit: "uncommitted new file, inspected at baseline HEAD"
api_file_and_sha256: "metadata/proof-tools-api.json: d4e5dbf99130724e1ec417ac1cb747b65521e5b42b3ed6c6384893e038d239ce"
source_file_and_sha256: "KIP126/ProofTools/Paper/ExtensionDescent.lean: e9094c45e638242ae998b81fb8a8d69383384db793998393b032ef2542a33a95"
reporter_agent: "/root/descent_interface_report"
independent_of_discoverer_and_implementer: true
evidence_level: "Lean-checked generic domain contradiction; independently checked exact-target identities; fixed-model candidate has existing upstream sorry dependencies; printed second-clause crossing iff remains unresolved"
status: deferred-by-user
human_decision: "2026-10-17 用户决定暂时保持不变，并将相关信息发送至飞书群 project math assistant；未批准 A 或 B。"
---

# 接口调整人审报告

## 用户决定

2026-10-17，用户明确回复：“暂时保持不变，排一个 agent 将相关信息发送到飞书群 project math assistant”。因此 A、B 均未应用；原文、现有扩张定义与公共接口保持不变。候选源码仅归档于 [UnappliedExtensionDescent.lean](evidence/UnappliedExtensionDescent.lean)，没有接入数学模块公共入口。以下保留独立审查的结论与建议，供群内讨论。

## 请求人类决定的具体问题

本报告审查本轮拟公开的论文命题 6.20。用户已授权“同时补齐这 11 条论文完整定理的证明并公开”；该授权覆盖忠实补证与公开，但没有指定如何处理源陈述的定义域冲突或补全未绑定的目标。本报告未参与问题发现或生产实现，独立读取了定义、命题全部证明、公共接口、契约、来源和实际依赖，并复跑证据。报告及证据只写入本目录。

请分别决定以下两项，不能将对一项的决定视为另一项批准：

1. **首句的合法域修正。** 是否同意公开“在 `n ≤ rEarlier - 2 + e(f)` 的早页上，同一 `f`、`x`、`y` 的 extension 沿实际商约化下降”的精确命题，登记为论文首句在定义 5.4 合法域内的自然性结果？第 5 节现有定义、所有 witness 字段和上游责任均保留。完整候选签名见下文 A；该候选还包含早晚页相同的自反情形。
2. **第二段的目标关联及交付范围。** 是否同意另行公开“早页同一目标余类包含零”的精确判据（下文 B），并明确标成可证的目标判据，继续将论文印刷的“存在某个非 liftable 较短 extension”的完整 iff 留为未决？若要求交付印刷版本的完整 iff，则须先确定 `y'` 与原目标 `y` 的关联和全部合法范围，并补出双向证明；本报告没有充分证据给出该版本的已完成修正。A 加 B **不能计为已完成论文第二段所有 crossing 内容**。

审查意见：A 有明确证明路线且候选已通过局部 Lean 检查；B 的目标绑定公式已在报告目录独立证明。优先保留现有上游定义。以上是 agent 建议；用户已决定暂不应用，完整 crossing iff 继续未决。

## 原接口、背景与问题成因

### 来源、职责和原始数学陈述

仓库 `AGENTS.md` 规定公共接口冻结；公共入口为 `KIP126.<模块>`，锁、契约及来源位于 `metadata/`。本次协议为 `/root/.agents/skills/kip-upstream-session/references/protocol.md`，采用同技能的 `assets/interface-review-template.md`。模块责任为：第 6 节公共操作定理属于 **ProofTools**；归一化映射、有限 extension witness 与 `Essential` wrapper 属于 **AdamsSynthetic**；实际 filtered map 的关系与完整目标余类属于 **SpectralSequence**。不向 Main 转移这些责任。

论文 `AimPaper/main.tex:255` 规定谱对象为 2-completed、connective、finite type，且 Adams 谱序列强收敛。命题 6.20 位于 `:1981`，标签 `prop:dec738d3`。其完整内容为：

- 给定 `d_n^(f,E_r)(x)=y`，其中 `x ∈ Z_(r-1)^(s,t)(X)`、`y ∈ Z_(r-1-n+e(f))^(s+n,t+n)(Y)`，对**所有** `2 ≤ r' < r` 断言同标签、同长度的 `d_n^(f,E_r')(x)=y`。
- 如果原 extension 本质且 `n ≤ r'-2+e(f)`，早页 extension 非本质，当且仅当存在 `0<a'≤n-e(f)`、`x' ∈ Z_(r'-1-a')^(s+a',t+a')(X) \ Z_(r-1-a')^(s+a',t+a')(X)`，满足 `d_(n-a'-b)^(fhat_(r'-1))(λ^a' x') = λ^(n-b-e(f)) y'`，其中 `b≥0`。正文没有量化或指定 `y'` 的类型、非零性、与原 `y` 的关系，也没有在该句完整写明较短式的合法性条件。

定义 5.4（`def:6c076a33`，`:1301–1317`）已经要求 `e(f) ≤ n ≤ r-2+e(f)`，并把有限页 extension 定义为同一实际归一化映射的有限 λ 商上的 synthetic extension `d_n^(fhat_(r-1))(x)=λ^(n-e(f))y`。注记 `def:fErextess`（`:1387–1388`）明确：`y` 是含经典边界和较短 ESS 像的完整余类；本质性指此**余类不含零**。

证明的首段使用实际商约化交换方块和 ESS 自然性。该步骤可以产生约化后的 synthetic equation，但将结果称为定义 5.4 的有限页 extension 时仍必须处于其合法长度域。证明的第二段先写出精确命中原目标 `λ^(n-e(f))y` 的短方程（`:2006–2013`），然后讨论源不在后期约化像中，或可 lift 的源在晚页有更短 extension 两种情形。迭代段（`:2070` 附近）最终只写存在命中某个 `y'` 的 crossing，未提供反向所需的原目标消去关系。完整原文、全部证明和紧随的推论保存在 [source-excerpts.txt](evidence/source-excerpts.txt)，可脱离聊天阅读。

当前元数据并没有一个已经锁定的完整 Prop. 6.20 公共定理。已有来源记录以 `prop:dec738d3` 标记有限 stretching 的相关工具，但其契约明确是**加强的充分条件**，不声称与印刷的完整 iff 等价。因此本问题是新公开目标的语句确定问题，不能宣称已经推翻某个现有锁定的 descent 定理。

### 现有完整 Lean 声明与对象

以下是 `KIP126/AdamsSynthetic/ExtensionWitnesses.lean` 和 `PageExtensions.lean` 的完整公共核心声明。公共宇宙和实例没有省略；`D` 是同一个给定模型，`X`、`Y` 和 `f` 均不替换。

```lean
universe u v w
variable {C : Type u} [StableHomotopyCategory.{u,v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w,v} Syn]
  [HasFunctorialCofiber (C := Syn)]
  (D : Model C Syn)
  (X Y : ClassicalObject)
  (f : X.obj D.auxiliary ⟶ Y.obj D.auxiliary)

public structure FiniteExtensionWitness (r : ℕ) (n s t : ℤ)
    (x : (D.classical.obj (X.obj D.auxiliary)).Page 2 (s,t))
    (y : (D.classical.obj (Y.obj D.auxiliary)).Page 2 (s+n,t+n)) where
  page_ge_two : 2 ≤ r
  length_lower : (normalizedExponent D.classicalTower f : ℤ) ≤ n
  length_upper : n ≤ (r : ℤ) - 2 + normalizedExponent D.classicalTower f
  source_cycle : ReachesPage (D.classical.obj (X.obj D.auxiliary)) r (s,t) x
  target_cycle : ReachesPage (D.classical.obj (Y.obj D.auxiliary))
    ((r : ℤ) - n + normalizedExponent D.classicalTower f) (s+n,t+n) y
  source : ((D.family.obj ((SyntheticObject.quotient (r-1)
    (extensionSourceObject D X Y f)).obj D.nu D.auxiliary)).sequence.ssData
      (s,(t-s)+s,t+normalizedExponent D.classicalTower f)).eInfty
  target : ((D.family.obj ((SyntheticObject.quotient (r-1) (.nu Y)).obj
    D.nu D.auxiliary)).sequence.ssData
      (s+n,(t-s)+(s+n),t+normalizedExponent D.classicalTower f)).eInfty
  source_rep : HasInfinityRepresentative _ 2 _
    (finiteSourceForExtension D X Y f (r-1) s t x) source
  target_rep : HasInfinityRepresentative _ 2 _
    (finiteTargetForExtension D X Y f (r-1) n s t length_lower y) target
  equation : TowerExtensionEquation
    (D.convergentMap (.quotient (r-1) (extensionSourceObject D X Y f))
      (.quotient (r-1) (.nu Y)) (finiteExtensionMap D X Y f (r-1)))
    (t-s,t+normalizedExponent D.classicalTower f) s n source target

public def FiniteExtension (r : ℕ) (n s t : ℤ)
    (x : (D.classical.obj (X.obj D.auxiliary)).Page 2 (s,t))
    (y : (D.classical.obj (Y.obj D.auxiliary)).Page 2 (s+n,t+n)) : Prop :=
  Nonempty (FiniteExtensionWitness D X Y f r n s t x y)

public def FiniteExtensionWitness.Essential {r : ℕ} {n s t : ℤ} {x y}
    (W : FiniteExtensionWitness D X Y f r n s t x y) : Prop :=
  TowerEssentialExtension
    (D.convergentMap (.quotient (r-1) (extensionSourceObject D X Y f))
      (.quotient (r-1) (.nu Y)) (finiteExtensionMap D X Y f (r-1)))
    (t-s,t+normalizedExponent D.classicalTower f) s n W.source W.target
```

这里未定量的 `_` 是源码中由该同一模型与分次唯一推断的参数，而非自由替换的对象。`TowerExtensionEquation` 使用相同 convergence 的 `toGraded`、`elementMap` 和实际 filtered map；它没有独立选择 ESS 或不定性。

底层完整语义（`SpectralSequence/Consumer/Extension.lean:42–69`）：

```text
Relation f k s n x y :=
  0≤n ∧ ∃ a∈F_s, b∈G_(s+n),
    [a]=x ∧ [b]=y ∧ f(a)=b
TargetIndeterminacy f k s n := { z | Relation f k s n 0 z }
TargetCoset f k s n y := { z | z-y ∈ TargetIndeterminacy f k s n }
Essential f k s n x y := Relation f k s n x y ∧ 0∉TargetCoset f k s n y
```

这是实际 maps 的陈述，完整 Lean 类型、任意测试对象 `T` 及全部隐式参数见本报告证据 `IndependentChecks.lean` 和源摘录。`ConvergentMap.targets_iff_coset`、`essential_iff_no_zero_target` 已公开证明上述对象一致性。

### 问题性质

| 问题 | 独立分类 | 不可据此声称的结论 |
| --- | --- | --- |
| 首句无条件量化所有早页 | 现有有限 extension 定义下的域不一致；若以 `FiniteExtension` 直译为总谓词，则该字面全称命题为假。缺失的是早页长度上界。 | 不能声称实际谱对象上的自然性失败，或论文拓扑结论被推翻。作者可能默许“在表达式有定义时”。 |
| 第二段的 `y'` | 来源量词/目标关联不完整，完整 iff 尚未证成；证明展示的 crossing 存在与原目标余类含零不是自动相同命题。 | 没有识别到固定谱对象的数学反例，不能标为已推翻的拓扑定理。 |
| 新候选 `finiteExtension_descends` | 合法域内的局部实现，非完整 Prop. 6.20。已通过本次复制快照核验。 | 不可把该定理的 `public` 修饰误记为已经接入根入口/接口锁，或把其局部成功记成第二段完成。 |

## 真实前提与对象核对

| 前提或对象条件 | 是否满足 | 证据及仍依赖的待补责任 |
| --- | --- | --- |
| 同一范畴、宇宙、稳定及 synthetic 实例 | 满足泛型证据的全部类型前提 | 证据显式保留 `C : Type u`、`Syn : Type w`、共同 hom 宇宙 `v` 及两个 `HasFunctorialCofiber` 实例。未另造抽象 filtered object 冒充固定对象。 |
| 同一 `D`、`X`、`Y`、实际 `f` | 满足 | 构造的是原 `FiniteExtensionWitness D X Y f`。指数始终为 `normalizedExponent D.classicalTower f`；未任意选择 `e`。 |
| 论文全局 2-completed/connective/finite type/强收敛 | 没有被反例破坏；泛型域证据也不需要放宽它们 | 零元素论证适用于满足这些条件的任何模型。报告未独立构造固定标准谱模型，固定模型存在/构造仍有项目已登记缺口。 |
| `2 ≤ r' < r` | 满足 | 反例取 `r=3`、`r'=2`。 |
| 晚页 `e≤n≤r-2+e` | 满足 | 取 `n=e+1`，上界为等号；`s,t` 任意。 |
| 原文首句未假设 source/target 非零或本质 | 满足其原有量词 | 取 `x=y=0` 合法；不将后段的 essential 前提错误套到首段。 |
| 晚页源、靶 cycle 和实际 `E∞` 代表 | 满足 | 源为零页代表；靶页为 `3-(e+1)+e=2`；有限标签保持零，代表用现有 `HasInfinityRepresentative.zero`。 |
| 同一实际归一化映射的方程 | 满足 | filtration 中源靶均零，实际方程为 `0 ≫ f = 0`，没有输入自由 extension 公理。 |
| 早页长度域 | 不满足，正是缺失条件 | 早页 witness 若存在，`length_upper` 给出 `e+1≤e`；与整数序矛盾。 |
| 第二段 `y'` 与原目标 `y` 的关联 | 未提供、未核实 | 必须检验原 `λ^(n-e)y` 属同一早页 ESS 的完整不定性；某个无关较短目标的存在不足以替代该检验。 |
| 本报告精确目标恒等式的前提 | 满足 | 明确保留已知方程 `h : Equation M p s n x y`，不从单独 `y≠0` 判断 essential。 |

## 独立证据与复现

### E1：定义域的形式化反证

发现者证据 `/tmp/aimpaper-counteraudit-20261017/DescentRangeCounterexample.lean` 已原样复制到本目录 [DescentRangeCounterexample.lean](evidence/DescentRangeCounterexample.lean)，记录来源及 SHA-256，并由本报告员复跑。完整核心结论是对**任意给定的同一合法模型** `D`、对象和映射：

```lean
FiniteExtension D X Y f 3 (normalizedExponent D.classicalTower f + 1) s t 0 0 ∧
¬ FiniteExtension D X Y f 2 (normalizedExponent D.classicalTower f + 1) s t 0 0
```

这不是从发现者日志转述而来的结论：本次实际 Lean exit code 为 **0**，只有无用 simp 参数的提示；两个 `#print axioms` 均为 `[propext, Classical.choice, Quot.sound]`，没有 `sorryAx`。新写的 [IndependentChecks.lean](evidence/IndependentChecks.lean) 还独立证明了 `earlier_domain_necessary` 和 `no_extension_outside_domain`，直接从原 witness 的字段提取所缺界，不调用发现者的定理。

证据等级：**泛型、给定模型前提下的 Lean 已核验定义域反证**。它足以排除按现有总谓词逐字实现首句；并非一个新构造的实际标准谱反例，也不反驳合法域中的拓扑自然性。若另行改定义，让域外 λ 幂零自动算平凡 extension，得到的是另一个语义；E1 不适用于该新定义，但该定义改变了当前公共契约。

### E2：同一目标的完整不定性判据

本报告员独立证明并检查了以下两条 generic 公式以及对应 tower 公式。前提是同一 filtered map 的原方程 `h : Relation f k s n x y`：

```text
¬ Essential f k s n x y ↔ 0 ∈ TargetCoset f k s n y
¬ Essential f k s n x y ↔ Relation f k s n 0 y
```

第二条不是凭“存在某个短 extension”推出来的：从同源零目标方程与原方程相减，得到零源、**原目标**的方程；反向也由同一关系相减。报告目录的 tower 版本已经证明：

```lean
(h : TowerExtensionEquation M p s n x y) :
  ¬ TowerEssentialExtension M p s n x y ↔
    TowerExtensionEquation M p s n 0 y
```

[IndependentChecks.log](evidence/IndependentChecks.log) 实际 exit code **0**；全部五条核验定理的公理只有基础三项。没有引入公理、sorry 或新的待补责任。E2 证明的是已知方程的 exact-target 恒等式，**没有证明论文非 liftable `x'` 条件的充分性、必要性或其与此公式的等价**。

### E3：当前下降候选的独立快照检查及实际依赖

候选来自 `KIP126/ProofTools/Paper/ExtensionDescent.lean`，其原文 SHA-256 见页首。该文件当时是未跟踪新文件，未被 `KIP126.ProofTools` 根入口导入，也未登记入三份 ProofTools 元数据。报告只复制到 [ReviewedExtensionDescent.lean](evidence/ReviewedExtensionDescent.lean) 核验，没有编辑生产文件。

局部检查 exit code **0**。证明先从晚页 witness 提取实际 filtration lifts，将 lifts 沿同一 `ρ_X`、`ρ_Y` 传送，用归一化映射商方块保持方程，并由 `finite_source_rho`、`finite_target_rho` 保持原 `x,y` 标签。源靶 cycle 用 `reaches_earlier` 降页。新增 `hnUpper` 恰好使构造出的早页 witness 字段有类型。

[DependencyAudit.lean](evidence/DependencyAudit.lean) 对此快照的**类型和证明体**递归遍历项目常量，并记录直接含 sorry 的依赖。实际结果见 [dependency-audit.json](evidence/dependency-audit.json)：

- 项目常量闭包为 **403** 个；Main 依赖 **0** 个。
- 不调用 `generalizedLeibniz`、`generalizedMahowald`、`finitePageExtensionStretching`，不使用待审的 Prop. 6.20 作为输入。
- 有 **24** 个既有直接待构造依赖，均属于 `AdamsSynthetic.Standard`，包括标准范畴/对象、`family`、`syntheticTower`、`quotients`、`normalizedMap`、`comparison`、`convergence` 等。完整名单逐项与当时待补清单匹配，见证据 JSON。此遍历是类型加体的保守语法闭包，会遍历 `model` 整个记录，并不表示所有字段都在核心计算中被使用。
- 实际 `#print axioms` 为 `[propext, sorryAx, Classical.choice, Quot.sound]`。候选自身和 ProofTools 局部 helper 没有新增直接证明洞，但固定模型的传递缺口没有消失。

本次没有发现通过 Main 最终结论回用本目标的循环，也没有发现以 `False.elim`、矛盾上下文或新增不一致公理证明本候选。依赖排查不证明 24 个上游待构造事实本身一致或已完成。E1/E2 的泛型证据则不需要这些具体标准构造。

### 可重复命令和实际运行环境

从报告页首仓库根目录运行（直接检查 Lean 文件，不传 `-o`）：

```sh
lake env lean metadata/interface-reviews/ProofTools/20261017-paper-prop620-domain/evidence/DescentRangeCounterexample.lean
lake env lean metadata/interface-reviews/ProofTools/20261017-paper-prop620-domain/evidence/IndependentChecks.lean
lake env lean metadata/interface-reviews/ProofTools/20261017-paper-prop620-domain/evidence/ReviewedExtensionDescent.lean
lake env lean metadata/interface-reviews/ProofTools/20261017-paper-prop620-domain/evidence/DependencyAudit.lean
```

四项最终均 **exit 0**。每项日志同目录保存。初次沙箱内两项命令仅返回 `could not detect the configuration of the Lake installation`，未执行 Lean；按协调者允许的方式提权后实际检查通过。未运行 `lake build`、未生成生产 `.olean`、未改工具链或清理缓存。工具链保持 `leanprover/lean4:v4.32.2`；构建锁与所读源码哈希见 [source-hashes.json](evidence/source-hashes.json)。本次只交报告证据，项目全面构建及公共消费检查由协调者在获准并整合生产改动后执行。

## 方案及精确差异

### 先评估保留原接口的内部方案

**所有现有上游接口可原样保留。** 合法域中的下降可以通过内部自然性证明完成，现有候选正是这种构造。精确目标余类公式也只使用既有公开定义和已证明 relation 操作。无需向 Main 添加额外假设，也无需输入“目标公式成立”来代替 ProofTools 自己的证明。

**原文字面首句不能仅靠内部补证保留。** 将原文字面目标归一化成 Lean 签名（这是拟公开目标的表示，仓库不存在此已锁定声明；使用上述完整 generic 上下文）为：

```lean
-- 原文字面目标，当前 FiniteExtension 语义下不能实现：
(X Y : ClassicalObject) (f : X.obj D.auxiliary ⟶ Y.obj D.auxiliary)
(rEarlier rLater : ℕ) (n s t : ℤ)
(x : (D.classical.obj (X.obj D.auxiliary)).Page 2 (s,t))
(y : (D.classical.obj (Y.obj D.auxiliary)).Page 2 (s+n,t+n))
(hr : 2 ≤ rEarlier) (hlt : rEarlier < rLater)
(h : FiniteExtension D X Y f rLater n s t x y) :
  FiniteExtension D X Y f rEarlier n s t x y
```

E1 对 `rLater=3`、`rEarlier=2` 给出反证。不能隐式使用未证的 fixed-model 全局矛盾来“证明”它。

**原文第二段尚无确定完整 Lean 签名。** 它没有绑定 `y'`。单独补 `∃y'` 会把判据变成“有某个较短 extension”，改变精确目标消去要求；只定义为原目标余类条件则删除了印刷式中的非 liftable 源/crossing 内容。两者不能当成同义接口替换。完整 crossing iff 仍需要独立数学证明。

### A：合法域中的下降（推荐的首句候选）

当前新文件的**精确完整签名**如下；`model` 固定指 `KIP126.AdamsSynthetic.Standard.model : Model Spectrum SyntheticSpectrum`，没有额外隐式模型参数，具体范畴及实例由该固定模型决定：

```lean
public theorem KIP126.ProofTools.Paper.finiteExtension_descends
    (X Y : ClassicalObject)
    (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (rEarlier rLater : ℕ) (n s t : ℤ)
    (x : Ambient model X (s,t))
    (y : Ambient model Y (s+n,t+n))
    (hr : 2 ≤ rEarlier) (hle : rEarlier ≤ rLater)
    (hnUpper : n ≤ (rEarlier : ℤ) - 2
      + normalizedExponent model.classicalTower f)
    (h : FiniteExtension model X Y f rLater n s t x y) :
    FiniteExtension model X Y f rEarlier n s t x y
```

语义差异：相对印刷首句，增加早页上界，使结论缩至定义本身有意义的范围；`rEarlier<rLater` 放为 `≤`，额外涵盖自反情形。`e≤n`、晚页及 cycle 前提由晚页 witness 已有字段提供，不增加无关假设。`x`、`y`、`f`、归一化指数和 λ 商塔关系不变。该结果只给出 extension 下降，不承诺 essential 性保存。

### B：同一目标余类的精确判据（替代建议，非印刷完整 iff）

可用既有公共 tower 语言表达，无需任何私有操作。完整 generic 类型已经在证据中通过：

```lean
universe u v
variable {Syn : Type u} [SyntheticCategory.{u,v} Syn]
  [HasFunctorialCofiber (C := Syn)]
  {H : Syn} {unit : S_0_0 ⟶ H} {F : SyntheticAdamsFamily Syn}
  {P : SyntheticTowerPresentation unit F} {X Y : Syn} {g : X ⟶ Y}
  {cx : SyntheticTowerConvergence P X} {cy : SyntheticTowerConvergence P Y}

-- 拟公开的语义候选；实际证明目前仅在报告证据内：
theorem tower_inessential_iff_zero_source_same_target
    (M : ConvergentMap F g cx.toConvergence cy.toConvergence)
    (p : ℤ × ℤ) (s n : ℤ)
    (x : ((F.obj X).sequence.ssData (s,p.1+s,p.2)).eInfty)
    (y : ((F.obj Y).sequence.ssData (s+n,p.1+(s+n),p.2)).eInfty)
    (h : TowerExtensionEquation M p s n x y) :
    ¬ TowerEssentialExtension M p s n x y ↔
      TowerExtensionEquation M p s n 0 y
```

应用到早页下降见证 `W'` 时，`M` 必须固定为

```lean
D.convergentMap
  (.quotient (rEarlier-1) (extensionSourceObject D X Y f))
  (.quotient (rEarlier-1) (.nu Y))
  (finiteExtensionMap D X Y f (rEarlier-1))
```

`p=(t-s,t+e(f))`、`x=W'.source`、`y=W'.target`、`h=W'.equation`。于是：

```text
¬ W'.Essential ↔ TowerExtensionEquation M p s n 0 W'.target
                ↔ 0 ∈ TargetCoset M.filteredMap p s n (toGraded(...,W'.target))
```

`W'.target` 是同一约化后的 `λ^(n-e(f))y`，由 `target_rep` 绑定，不能换成任意 `y'`。此判据甚至不需要“晚页 essential”前提，因为它是任意已知 equation 的完整目标语义；**因此它对印刷第二段的替代会丢失非 liftable crossing 的额外结构内容**。如果目标是完整命题 6.20，应把 B 当作待证明 crossing iff 的精确终点，而非把终点改名充当完整 iff 的证明。

### 其他方案及代价

| 方案 | 前提/结论变化与局限 | 评估 |
| --- | --- | --- |
| 只证明 A，完整第二段继续研究 | 保留现有定义，得到合法域自然性；用户所要完整条目尚未全部完成 | 数学上可行，状态须如实标部分完成 |
| 证明 A 加 B，明确区别于印刷 crossing iff | 提供精确目标条件，删除不了未完成的 crossing 桥接责任 | 推荐作为有边界的可审查候选；需决定本轮交付范围 |
| 坚持完整 crossing iff | 必须补全 `y'` 的合法次数/量词/原目标关联，证明非 liftable 条件的两个方向 | 仍未完成，不可自行写成已证接口 |
| 扩大 `FiniteExtensionWitness` 域以覆盖首句所有早页 | 改变 witness 的长度及 target-page 合法性、零扩张语义、标签约定及生成字段；须跨模块重审 | 没有本次必要性证据，不推荐；不是内部补证 |
| 把任意较短非零目标存在作为 inessential 定义 | 丢失原目标余类关联，改变整个 ESS 公共契约 | 不可作为默认修复 |

## 下游影响

| 声明/记录/测试 | A/B 的受控方案 | 若改上游定义域或本质性 |
| --- | --- | --- |
| 新 `ProofTools.Paper.finiteExtension_descends` 及根入口 | A 获准后，协调者整合候选并公开导入；当前无生产或测试调用方 | 改域会改变其构造需要 |
| `FiniteExtensionWitness`、`FiniteExtension`、`.Essential`、`.target_page_ge_two`、`.length_nonnegative` | 原样保留；API 与全部生成声明不变 | 改域将影响长度投影、构造器及 target-page≥2；改变 Essential 会改变 wrapper 语义 |
| `FilteredMapExtension.Relation/TargetIndeterminacy/TargetCoset/Essential`，`ConvergentMap` 两条等价及 transport | 原样消费；B 在其现有语义上补证 | 改本质性须重审 SpectralSequence 和 AdamsSynthetic，影响所有 crossing 及滤过校正工具 |
| `FiniteExtensionNonliftableCrossing`、`FinitePageExtensionStretchingLaw`、`Standard.finitePageExtensionStretching` | 不改；现有加强充分条件独立继续 | 不能借此报告声称已取得印刷完整 iff；改上游语义会影响现有证明 |
| `GeneralizedLeibniz/Filtration`、`CrossingRange`、`CrossingFinite`；`GeneralizedMahowald/ShortSource` | 没有消费新候选，不在当前阻塞闭包 | 若改 Essential/域则需逐项重审 |
| Main 的 `Internal/NuThree/{Mahowald,ActualOperations,ZeroExtensions}.lean` | 无需改动，没有消费新候选 | 改 witness 域/语义会影响其构造和 ν-extension 链 |
| `metadata/proof-tools-api.json` | 仅在获准整合后登记真实新增公共声明和生成导出，不改旧签名绕过锁 | 上游改动需对各模块单独授权并重锁 |
| `metadata/proof-tools-contracts.json`、`proof-tools-sources.json`、`aim-paper-sources.json` | 如实分别标 A 的合法域、B 的 exact-target 性质和完整 iff 未决；保存原来源 | 不得把新结果写成无差别的完整 Prop. 6.20 迁移 |
| `metadata/proof-obligations.json` | 不新增公理/待补责任；保留 24 项既有传递构造依赖及 ProofTools 两项原待补 | 原文第二段未完成不能用新假设转给 Main，也不能伪填完成 |
| `Tests/AdamsSynthetic/System.lean:48/:58`、`Structural.lean:59/:93` | 保留长度界、有限不等于无限、coset transport 和同对象方程检查 | 上游语义变化将触及这些现有边界 |
| `Tests/SpectralSequence/Consumers.lean:83/:87/:90/:121` | 保留真实 ambiguity、coset 与 essential 语义 | 改定义需重审全部对应合同 |
| `Tests/ProofTools/Consumers.lean` 及各 `Interface.lean`、`Tests.Integration`、`Tests.Trust` | 获准整合后增加普通根导入的 A/B 消费与合法域边界，保留所有旧测试 | 不允许删测试来消除域或导出失败 |

来源追踪已经核对：六模块公共源记录的固定上游为 `SII-MATH/Kervaire126` 的 `bbac1fc05843bdf2d56057e6114a38839e939378`。witness 来自 `KIP126/Def/Kervaire/Route/Extensions/Witness/Data.lean:22`，有限谓词来自 `Extensions/Predicates.lean:23`。`adams-synthetic-contracts.json` 的 `normalized-extension-language` 明确没有输入传播定理；`proof-tools-contracts.json` 的 finite stretching 限制也已保留。审查没有更改这些源路径或归属。

协调者在具体方案获准并完成生产整合后，应串行更新新增接口/来源/状态，运行普通公共消费、域边界和信任检查，再执行仓库要求的 `python3 scripts/check-source-inventory.py` 与 `lake build`。本报告未申请推送或发布，也未执行 Git pull/fetch/merge，故没有新增 Release 缓存同步动作。

## 阻塞范围与继续项

**实际阻塞：** 按现有 `FiniteExtension` 语义公开 Prop. 6.20 首句“所有早页”的字面完整签名；把第二段任意 `y'` 的存在直接登记成原 extension 的非本质 iff；在没有 crossing 双向桥接时把本条记作“论文完整定理已补证”。紧随其后的论文推论 6.23 若以本印刷 iff 为唯一证明输入，也不能据此视为已完成。

**不阻塞：** 合法域自然性及 exact-target 公式的独立研究和报告证据；已锁定 strengthened finite stretching；不调用争议语句的现有模块；本轮其他独立的论文条目。库存检查没有发现任何当前生产或测试调用新 `finiteExtension_descends`，因此本争议没有理由冻结整个 ProofTools、AdamsSynthetic、Main 或全部 11 条任务。协调者仍在安排其他独立证明。

**已确认：** 所缺上界必要；zero-label 反证在原对象/映射和全部真实前提下核验；合法域候选的局部证明通过；同目标公式具有无项目 sorry 的 generic 证明；固定模型的 24 项既有传递缺口如实保留。

**未决：** 论文是否将合法域默认为全程约定；`y'` 的精确原意；完整非 liftable crossing iff 的真实充分必要条件与双向证明；标准模型既有构造的完成。报告不把这些未决项包装为反例或批准。

## 人类审核记录

当前无针对本报告 A/B 方案的明确人类决定。`human_decision: null`。

本轮用户原话“同时补齐这 11 条论文完整定理的证明并公开”记录为任务范围背景；它不是对后来发现的域修正、目标替代或缩减完整 iff 交付范围的具体批准。协调者/worker 的建议、其他报告的决定、等待或沉默均未记作本报告批准。后续仅可由协调者按真实人类原话、出处和明确范围补记审核结果；实施另行安排。
