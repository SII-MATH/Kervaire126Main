# 来源措辞与 hgraph 写作示例

这些是写作结构和判断示例，不是待导入条目。实际内容以所链接的项目维护源为准；不要把同标签条目再复制进 Blueprint。下文路径链接相对于本文件。

## From：数学内容保持不变

项目 [Geometry](../../../../blueprint/chapters/Geometry.tex) 的 `paper:1.1` 使用 `From`，并保留原文主标签和别名。下面是缩短后的结构示例，省略了原节点的其他来源与对应说明：

```tex
\begin{theorem}[A framed manifold of Kervaire invariant one in dimension $126$]
\label{paper:1.1}
\source{AimPaper Theorem 1.1}
From \cite{LWX126}, Theorem 1.1.\par
There exist framed manifolds of Kervaire invariant one in dimension 126.
\lean{KIP126.Geometry.kervaire_invariant_one_126}
\end{theorem}
\begin{proof}
\uses{paper:1.3,paper:1.4}
Apply Browder's criterion to the nonzero permanent square $h_6^2$.
The dimension is $2^{6+1}-2=126$.
The invariant construction and the source-to-model comparison remain
the registered upstream responsibilities of Literature.
\end{proof}
```

这里 proof 与定理相邻但不嵌套，证明调用的结果放在 proof 中。即使局部推导已完成，也保留上游几何对象及比较的待补边界。该简写不代替现有节点的完整陈述、解释或证明。

改写英文或把已定义的记号换成等价记号，不自动需要改用 `revision`。若不能确认等价，先核对来源或标明疑点，不猜一个更容易证明的解释。

## Revision：精确指出数学改动

项目 [ProofTools 原文与修正版条目](../../../../blueprint/chapters/ProofTools.tex) 有这些真实来源段落：

```tex
A finite-layer revision of \cite{LWX126}, Theorem 6.12.\par
```

```tex
A fixed-target revision of \cite{LWX126}, Proposition 6.20,
second assertion, with the late-cycle exclusion removed.\par
```

它们分别标识有限层版本，以及保留指定目标并去掉某项排除条件的版本。正文仍需给出实际模型、量词、层数/页码范围、前提与结论，不能只写一句 revision 就省略数学内容。ProofTools 的 `paper:6.20` 还明确所证版本不包含原文的一般差集等价，这是应保留的范围说明。

证明出处也要匹配实际论证；例如现有写法：

```tex
\textit{Proof of the fixed-target revision; compare
\cite{LWX126}, Proposition 6.20.}
```

它引导比较原论证，不宣称原文已经证明当前修正版。需要说明新增论证及仍继承的上游输入；修改历史与状态继续维护于 [corrections.yaml](../../../../corrections.yaml)，不在这里复制维护修正版全文。

## 项目推导：交代证明，不制造直接出处

从已有条目推出的新结论，可以在正文或 proof 中写清 `By ...` / `Combining ...` 的推导关系，并用 `\ref` 指向实际结果。若没有直接对应的文献定理，不添加虚构的 `From` 或 `revision` 段落。

若该结论只是某文献结果的特例，说明特化的参数与仍需满足的条件；如果来源本来就是 AimPaper 中该特例的陈述，可以对 AimPaper 用 `From`，并在证明中另引更一般的原始文献。不要让两个来源看起来都直接证明了尚未建立的模型对应。

## 三种连接不要混用

| 写法 | 实际用途 |
| --- | --- |
| `\cite{LWX126}` 与具体编号 | 文献归属和定位；本身不新增数学依赖或 Lean 对应 |
| `\ref{paper:1.3}` | 条目阅读导航；若是实际前提或证明依赖，再在适当位置加 `\uses` |
| `\lean{KIP126.Geometry.kervaire_invariant_one_126}` | 本条目结论到同模块实际公开声明的绑定，不是证明中用到的全部声明列表 |

跨模块结果通过其数学条目连接。一个节点可绑定多个声明，但正文必须确实分别陈述这些对象或结论；绑定一个现成谓词不能代替形式化该谓词成立的主定理。

修正文案时检查标签与别名、来源编号、BibTeX key、公式及索引、proof 关联、依赖目标和实际公开绑定。范围或对应尚不完整时，在当前节点的正文/原生说明中讲清楚，不靠增加绑定或状态标记掩盖。
