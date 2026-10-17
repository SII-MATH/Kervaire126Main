# 命题 6.20 差集或晚页 crossing 二分式：独立核验

基线提交：`aad718722aa01dfce361f40645fc776037d1078f`。遵守当前 `AGENTS.md` 与 `/root/.agents/skills/kip-upstream-session/references/protocol.md`。本核验者独立于主文件与 essential 源提取文件的实现者，只读其源码、接口及记录；只写本目录核验报告和自有审计 Lean 文件，不改生产、接口、Tests，不运行 lake build。

## 数学评估（初审记录，最终结论见文末）

本次授权目标是单向二分式：同一 x/y 的晚页 Wlater essential、早页 Wearly inessential，推出 `D_y ∨ C_late`。D_y 保留经典严格循环差集、`0<a≤n−e(f)`、原 y、b=0 及同一早商实际短方程；C_late 精确采用同一晚商 normalized-map ESS 的 `¬ExtensionNoCrossingRange Mlate p s n s`，p=(t−s,t+e(f))。

**C_late 不是论文 Definition 5.9 的较小经典商 crossing，也不是把它偷换成一个单纯 nonrange 源条件。** 当前公开 NoCrossingRange 量化该晚商实际 equation 的非零 E∞ 目标，允许该 equation 本身非本质；若要进一步解释为 essential crossing，须另作有限提取，不在本二分式中默认一个未证明的等同。

### 必须先选 essential 早短式

前轮“删除差集”的 iff 在正向可总取 a=1，但该首项可能为零或可提升，短方程也可能非本质。这样的见证不足以与晚页无 crossing 矛盾，不能直接恢复差集。

本轮正确做法是：在所有命中同一非零目标的高源实际代表中，取 source filtration 最大者。其范围是有限区间 `s+1…s+n`；若产生的短方程仍非本质，则零源/同目标判据提供 source filtration 再提高一层的实际代表，反驳最大性。端点 s+n 之后的像因 filtered-map 性质落入目标下一层，不能命中非零原目标。因此提取到**同一原 y 的 essential 短方程**，而非只找到某个新目标。

随后在实际归一化早商应用 `finite_crossing_target_bound`，把泛型提取给出的 `a≤n` 加强为 `a≤n−e(f)`。该范围也给出 `a≤rEarly−2`，从而经典标签所在有限 strip 合法。

已独立读取 helper `ExtensionEssentialSource.lean` 的最大过滤层证明初稿：其 `Nat.findGreatest` 谓词保留原 target br 及检测等式；非本质时直接将实际高源关系提高一层，未调用待证二分式或 nonliftability 结论。最终类型检查与完整传递依赖将在候选完成后再审。

### 无晚 crossing 确实使所有晚高源像进入目标下一层

已有 `ExtensionNoCrossingRange Mlate p s n s` 配合 `image_correction_in_next` 给出

\[
A\in F^{s+1}_{\rm late}\ \Longrightarrow\
\hat f_{\rm late}(A)\in G^{s+n+1}_{\rm late}.
\]

该引理的附加 `f(A)∈G^s` 前提由实际映射保 filtration 自动得到，`s≤s+n` 由原 witness 的 `n≥e≥0` 得到。无需添加新的 no-crossing、收敛或 compatibility 结果包作为公共前提。

### 若早 essential 短源可提升，就与其本质性矛盾

设选得的经典 x′ 还属于晚循环层。必须先构造它在**同一 normalized source 的实际 rho E∞ 映射**下的 lift；仅凭每页标签满射不能做到这一点。

一旦这个 lift 已构造，取其晚页 F^{s+a} 实际代表 A。因 a>0，无晚 crossing 使 f(A) 的 filtration ≥s+n+1；约化后仍高于原目标。它与早短方程的实际 source 代表具有同一首项，相减后源进入 F^{s+a+1}，映像仍检测同一个原目标。这使原早短方程非本质，反驳 essential 的选择。因此所取经典 x′ 不属于晚循环层，得到 D_y。

若已经有 C_late，则直接给出二分式右支。全过程没有从任意 abstract filtered square 推测实际谱实现性，也没有把 D_y 更换成 source 不在 rho 像。

## 实际 rho/shift 兼容的既有工具：范围已核实

已独立读取 `GeneralizedMahowald/QuotientShift.lean` 的 `quotient_shift_restriction_on_spheres`，及其 `NoReturn.lean` 依赖的真实证明。

完整数值前提只有 `0<i≤q`；shift δ 任意，sphere stem m、weight w 任意。对 qLate、qEarly 各自任取满足商包含方块的 quotient-shift iso，结论是所有实际 sphere 代表 c 上

\[
c\,\rho_{i,q}\,Q_i
=c\,Q_q\,\operatorname{shift}(\rho_{i,q}).
\]

这不是声称任意 cone morphism 严格相等。其证明将两种 cone 填充的差因子化到 `shift(0,−q−1)ν(ΣX)`，再使用实际 ν 的下滤过界和 i 商的有限上界；`−q−1≤−i` 由 i≤q 给出，故所有 sphere 复合为零。没有未说明的 weight 小范围。

应用 `i=rEarly−1`、`q=rLate−1` 时：i>0 由早 witness 的 rEarly≥2 得到，i≤q 由 hle 得到；因此包括 i=q 和所需 w=t+e。选择 iso 的商包含兼容性来自前轮 `correctionShiftIso_incl`，不应新增为公共前提。

最终实现仍须将该 **actual BiHom 上的自然性**，通过同一 convergence、真实 filtered shift 和 associated graded 代表，送到 `finiteExtensionCorrectionLabel` 的 E∞ 标签相容；不能用“一般 shift 的 E₂ 标签 rfl 相等”取代这一步。

## 边界和反驳检查

- **零目标/经典边界**：晚 essential 保证其实际 synthetic 目标非零；有效窗内目标 rho 单射及同 y 标签的代表唯一性再保证早目标非零。不能只用经典 y≠0。
- **n=e 与 rEarly=2**：已有最短长度 essential iff 非零目标结果排除早 inessential，故联合前提不可能。提取 essential 早短源时不得预先假定 n>0 而漏掉此分支。
- **hle 等号**：D_y 的严格经典差集为空，联合 essential/inessential 前提本身不相容；允许≤的公共签名仍可成立，且前述 sphere 自然性也覆盖 i=q。
- **边界代表**：源分母 B_{1+a} 包含于所有晚经典循环层，故同余代表不能通过加边界改变“属于晚循环层”这一性质。原经典差集必须保留在最终 D_y 类型中。
- **短源非零/essential**：这应由私有提取证明给出以支撑反证，不能加作原定理的新前提。若公共 D_y 仅要求原文的 equation，可以在结论中忘掉已构造的更强 essential 性，不改其含义。
- **晚 crossing 的对象**：必须是 Wlater 所用 rLate−1 商、同 normalized map、同 stem/weight p、同 s/n/threshold=s；不得转成早页 crossing、较小商 crossing 或无对象关联的存在式。

## 初稿交付边界

当前只给出独立数学评估和既有接口适用性结论，不提前认可尚未完成的实现。主文件 `ExtensionCrossingDichotomy.lean`、私有 helper 的完整 kernel 类型、真实证明依赖、实际编译及公共普通消费将在候选交付后核对。完整闭包应使用全数学 import-all 环境；普通公开 import 环境中可见的证明闭包只能计作下界。

## 完整候选源码复核（类型检查待协调者交付）

已逐行读取主文件当前完整证明与私有 `ExtensionEssentialSource.lean`。当前新增公共项为一个谓词 `FiniteExtensionNonliftableShortTo` 和一个定理 `finiteExtension_nonliftableShort_or_lateCrossing`；右支直接使用否定的既有 `ExtensionNoCrossingRange`，没有另设 C 谓词。完整公开签名没有新增结果包、compatibility、收敛或 short-essential 假设。`FiniteExtensionWitness` 的 `page_ge_two / length_lower / length_upper / source_cycle / target_cycle / source_rep / target_rep / equation` 字段提供原合法前提；late/early 均为同一 Standard 模型、X/Y/f/n/s/t/x/y。

私有 essential helper 两引理的真实证明已核对：泛型引理在 universe u/v 的实际 tower 上做有限最大化，actual specialization 使用既有 `finite_crossing_target_bound`，不依赖新二分式或 Main。原 target 的唯一变化是等式 `s+n=(s+a)+(n−a)` 的类型运输，未换成任意 y′。helper 已由协调者实际 build，日志 `/tmp/prop620-crossing-essential-source-build.log` 显示成功；本核验者未运行构建。

主文件的 source-lift 链条如下。`unshifted_label_infinity_exists` 在 late 商的精确 strip 中通过 `infinityFiniteWindow` 构造同一 x′ 的 E∞ 类。`correctionInfinity` 采用前轮已公开 correction label 所用的同一个 `essShift (0,e)` filtered comparison 与 `correctionShiftIso⁻¹`，仅作必要 tridegree 运输。`correctionInfinity_represents` 用该 shift 的 `representative_iff` 和真实 family-map 自然性绑定其 E₂ 标签。`correctionInfinity_rho` 先由 actual sphere 比较得到 Q/rho 的 E∞ 方块，再由 `FilteredMapTransport.transport.map_comm` 在真实 filtration level 和 associated graded 上推导 shift/rho 自然性，最后消去 Q 正反复合。由 `HasInfinityRepresentative.unique` 得到归约后等于**原来选定的早 z**。这填补了从经典 late cycle 到 normalized source rho lift 的实际对象关联，不是对任意标签任选同构。

私有 `essential_short_source_not_in_range` 取 late E∞ lift 的真实高滤过代表，应用晚页 `image_correction_in_next`，再通过 normalized-map 的实际 rho 自然方块归约。归约 source 检测同一早 z，像却在原目标下一层，因此构造同源到零的 equation，直接反驳已选早短式的 essential 性。它甚至不需要假定早晚目标之间另有人为绑定。

主定理先对晚 no-crossing 分情形。若失败，返回原晚商的右支；否则提取 essential 短式，并对同一 x′ 是否属于晚 cycles 分情形。属于则由上述两条引理矛盾；不属于则输出完整经典差集左支，并仅在结论中遗忘短式已证的 essential 性。没有通过更弱 nonrange 定义代替差集。

所有新辅助声明均 private；`@[expose]` 只令同模块 import-all 可读证明，不增加公共接口。未见新 axiom、直接 sorry、目标循环、Main 依赖或经已知矛盾构造 False 的路径；最终传递闭包仍须由完整 import-all 审计确认。

## 最终生产常量：完整 kernel / 依赖实际检查通过

实际核验对象固定为：

```text
aa1ae0f936ebb219b551f03731bf4001baef78dd1010029442525517afe50251  KIP126/ProofTools/Paper/ExtensionCrossingDichotomy.lean
b304c817a0cc1f7a958b16ae0c0e74c2e60357e2317d723b39b400c34ab36aa4  KIP126/ProofTools/Paper/ExtensionEssentialSource.lean
```

协调者正式 `lake build KIP126.ProofTools` 的成功日志 `/tmp/prop620-crossing-public-build.log` 已实际读取，显示 2823 jobs 成功。早期初稿的依赖类型展开超时、局部 quotient-shift 复合化简和最后 proof-irrelevance 的 cast 残式均不算通过；只采用最终上述 SHA 与实际编译产物。最终复核了 `correctionInfinity` 的显式类型分拆，以及 `hcancel` 中的 `Category.comp_id` 和 `rfl`，它们只消去相同索引的证明项运输，未变更公共类型或数学对象。

本核验者在已编译生产常量上独立运行：

```sh
lake env lean metadata/interface-reviews/ProofTools/20261018-prop620-crossing-dichotomy/IndependentProductionAudit.lean
```

**实际 exit code 0**。命令未带 `-o`、未运行 lake build、未写共享构建目录；仅写本核验者分配目录内日志。该审计有 477 个 imports：全部 476 个当前数学模块 `import all` 加 Lean；独立与当前 482 个 KIP126 源文件比对，唯一未导入者是六个 InternalAudit 汇总，不缺数学实现。没有以普通公开 import 中被隐藏的证明体下界冒充完整闭包。

完整 kernel 类型和原始遍历结果在 `independent-production-audit.log`；可复读 JSON 在 `independent-production-audit.json`。两条公共声明均无额外 universe 参数（固定 Standard 模型，`level_params=[]`），其完整量词、同 x/y 见证、原早目标和晚商 crossing 与授权目标一致。

| 生产公共根 | 完整项目常量闭包 | 已登记上游直接待补 | ProofTools 本地待补 | 未登记洞 | Main 依赖 | 项目公理 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| FiniteExtensionNonliftableShortTo | 601 | 33 | 0 | 0 | 0 | 0 |
| finiteExtension_nonliftableShort_or_lateCrossing | 929 | 38 | 0 | 0 | 0 | 0 |

两条根的实际 `collectAxioms` 都是 `[propext, sorryAx, Classical.choice, Quot.sound]`。**这不是无 sorry 依赖的最终上游数学实现。** 本地新增证明没有直接洞，但仍正常消费 38 条上游已登记责任。主定理 38 条为 28 条 pending-construction 与 10 条 pending-proof，分布于 AdamsSynthetic Standard 的 Background / Operations / Separation 和 Literature Standard；没有将这些来源声明当作本轮已补齐。

已逐项核对 38 个名字与责任清单相同，且其 source 文件、line 对应当前真实声明位置。完整责任条目、四个上游源 SHA、状态和清单 SHA 另存 `independent-upstream-obligations.json`。两个根的 33/38 责任**集合**与前轮 correction label / 去差集 iff 的完整审计完全相同；本轮没有引入额外上游待补、移交新责任或修改清单。

还读取了普通 `import KIP126.ProofTools` 的 `Tests/ProofTools/Consumers.lean`：新增消费直接从二分式与 `¬D_y` 推出原晚商 crossing，三个新私有 helper 名称有不可见检查；已有最短长度边界和旧接口消费保留。最终专项消费及全仓库构建由协调者调度，本核验不将 facade 构建成功冒充全仓库检查成功。

**目标级结论：通过。** 数学陈述、最终真实证明体、固定原目标、经典差集、实际 λ 商 / shift / ρ 标签关联、有限条带与边界，以及完整 kernel / 传递依赖均通过独立核验。没有新增数学阻塞；仍存在的 38 条既有上游责任保持未完成状态。旧116接口逐行保留和最终普通消费 / 全仓库检查的整合结果待协调者完成后补记。

## 普通消费与新增自动生成支持项

已独立读取 `/tmp/prop620-crossing-consumer-build.log`，普通公开消费专项构建实际成功（2825 jobs）。日志中的私有名称 Unknown identifier 对应源码 `#check_failure`，属于所需封装检查通过，不是被忽略的错误。

本轮公开 capture 实际出现六个新增可达名字，因此总导出应为 **122=87 named+35 generated**，而非只按两个数学 source commands 估计的118。四个自动支持项为：

- `FiniteExtensionNonliftableShortTo._proof_2`：`s+n=(s+a)+(n−a)` 的整数算术证明；
- `FiniteExtensionNonliftableShortTo._proof_3`：上述分次等式所诱导的 E∞ 模块类型等式；
- `KIP126.AdamsSynthetic.towerGradedIso.eq_1`：既有 towerGradedIso 定义的自动展开方程（universes v,w）；
- `KIP126.Kervaire.Route.extensionSourceObject.eq_1`：既有 normalized source 定义的自动展开方程（universes u,v,w）。

后两者 namespace 属上游，但 capture 的 kernel module 均为本次 ProofTools 主文件，未改上游定义、源码或公共 API。它们只陈述已有定义展开，不能作为新增四个数学承诺计数；也不应统称四个 cast 引理。`new-public-capture-additions.json` 保存六个实际完整 kernel 类型与 fingerprints，供最后 API 逐条比对。

四个自动支持项另经 `IndependentGeneratedAudit.lean` 在同一477-import完整环境独立运行，**实际 exit 0**；证据在 `independent-generated-audit.log/.json`。`_proof_2` 闭包2、无洞；`_proof_3` 闭包515、29项已有上游对象责任（全部已登记，是其类型所需固定模型）；两个既有定义展开方程闭包分别172/56，均无直接 sorry、只依赖基础逻辑公理。四项均无 ProofTools 洞、无未登记洞、无 Main 或项目公理。其 universe 参数也与各自展开的泛型定义一致。

## 冻结接口与全量责任交叉核对通过

协调者完成最终追加后，本核验者将当前 API 与 `/tmp/prop620-crossing-before-proof-tools-api.json` 独立逐行比较：**旧85 named +31 generated 共116条完整 JSON 行值完全相同，旧116 exports全部保留**；仅追加上述2 named+4 generated，目前共122。新增及旧行的 kernel type fingerprint、universes、axiom 集合均与当前实际 capture 相同。完整渲染类型仅允许空白换行差异；旧 `grade_difference` 的一次换行重排不构成类型改变，且其固定原始行未改。结果在 `independent-final-interface-check.json`。

相对任务 baseline 的13项 SHA，唯一变化是授权追加后的 `metadata/proof-tools-api.json`；其余五模块 API、Language/Laws、旧 ExtensionIndeterminacy、manifest/toolchain、责任清单全部字节未变。最终生产两源仍与上文冻结 SHA 相同。

又独立读取协调者实际 exit0 的全量 `.lake/trust-capture.json`（12403声明），按**真实 kernel 名称**逐条对照299登记责任的 type/body fingerprints：全部存在且完全相同，无未登记直接 sorry，无项目 axiom。五个私有上游责任保留其原私有 kernel 前缀，不按 source display name 混同。结果在 `independent-full-trust-registry-check.json`。该项是对协调者实际全量 capture 的独立数据交叉核对；前面的两次 Lean 生产/生成项核验则由本核验者独立实际运行，二者不混写。

辅助比对脚本早期曾直接比较 axioms 数组顺序、类型排版，产生无语义差异的假警报；另一次以 source display name 匹配私有登记 kernel 名，漏掉五个私有前缀。已按实际语义/精确 kernel 名修正比对方法，失败尝试 JSON 原样另存带 `raw-render-attempt` / `source-name-attempt` 文件；没有修改生产接口、检查工具、白名单或责任清单来通过。

最终独立结论维持**通过**，无数学/接口/责任阻塞。默认全仓库构建仍由协调者正在运行；本报告不以局部2823/2825成功代替该结果。

## 全仓库构建收尾

本核验者已实际读取协调者默认 `lake build` 的 `/tmp/prop620-crossing-full-build.log`，尾部为 **Build completed successfully (3090 jobs)**。日志包括 `Tests.Trust`、ProofTools / Main InternalAudit 等成功，预期私有名称的 `#check_failure` 输出仍正常。源码与责任清单最终 SHA 再次核对不变。至此本轮所需普通消费、完整依赖/责任和默认构建结果均已有实际证据，目标级独立核验完成；无待协调者处理的数学或实现阻塞。既有38上游待补不因构建成功而消失。
