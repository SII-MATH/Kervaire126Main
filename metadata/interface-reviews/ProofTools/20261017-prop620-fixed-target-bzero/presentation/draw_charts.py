"""Classical Adams and fixed-weight ESS charts, with finite coefficient QA."""
from pathlib import Path
import json
import itertools
import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.lines import Line2D
from matplotlib.patches import FancyArrowPatch

HERE = Path(__file__).resolve().parent
plt.rcParams.update({
    "font.family": "DejaVu Sans", "font.size": 10,
    "mathtext.fontset": "stix", "pdf.fonttype": 42,
    "savefig.facecolor": "white",
})
COLORS = {0: "#c43e42", 1: "#bf791c", 2: "#16856c", 3: "#265ca6"}
MAGENTA = "#aa3b8a"


def h(a, name):
    return name if a == 0 else (r"h_0" + ("" if a == 1 else rf"^{{{a}}}") + name)


def setup(ax, xmax=2):
    ax.set_xlim(-.43, xmax + .48)
    ax.set_ylim(-.45, 7.65)
    ax.set_xticks(range(xmax + 1))
    ax.set_yticks(range(8))
    ax.grid(color="#dde2e9", linewidth=.65)
    ax.set_axisbelow(True)
    ax.set_xlabel(r"stem $t-s$")
    ax.set_ylabel(r"Adams filtration $s$")
    ax.spines[["top", "right"]].set_visible(False)


fig, axs = plt.subplots(1, 3, figsize=(12.5, 6.7))
for ax in axs:
    setup(ax)
axs[0].set_title(r"$M=H(\mathbb{Z}/16)$", pad=15)
for a in range(8):
    axs[0].plot([0], [a], "o", ms=5.5,
                mfc="white" if a >= 4 else "#17293f",
                mec=COLORS[0] if a >= 4 else "#17293f", mew=1.2)
    axs[0].text(-.07, a, "$"+h(a, "w")+"$", ha="right", va="center", fontsize=10)
for a in range(4):
    axs[0].plot(1, a, "o", mfc="white", mec=COLORS[0], ms=6, mew=1.2)
    axs[0].text(1.08, a, "$"+h(a, "v")+"$", va="center", fontsize=10)
    axs[0].add_patch(FancyArrowPatch(
        (.96, a+.06), (.035, a+3.9), arrowstyle="-|>", mutation_scale=11,
        linewidth=1.35, color=COLORS[0]))
axs[0].text(1.48, 5.8, r"$d_4(h_0^a v)$"+"\n"+r"$=h_0^{a+4}w$",
            ha="center", color=COLORS[0], fontsize=12)
axs[0].plot([1, 1], [3.3, 4.15], ":", color=COLORS[0])
axs[0].text(1.1, 4.0, "tower continues", fontsize=8, color="#6c747f")
for ax, title, names in [
    (axs[1], r"$\Sigma E_x\oplus\Sigma E_u$", ("x", "u")),
    (axs[2], r"$Y=\Sigma E_z\oplus\Sigma E_{y_0}$", ("z", "y_0")),
]:
    ax.set_title(title, pad=15)
    for a in range(8):
        ax.plot(1, a, "o", ms=11.5, mfc="#e8f0fa", mec="#265ca6")
        ax.text(1, a, "2", ha="center", va="center", fontsize=8, color="#265ca6")
        ax.text(1.13, a, "$"+h(a, names[0])+r",\,"+h(a, names[1])+"$",
                ha="left", va="center", fontsize=10)
    ax.text(.13, 6.8, "all permanent", color="#265ca6", fontsize=9)
    ax.set_xlim(-.35, 2.5)
fig.text(.5, .035, "A circle marked 2 is a two-dimensional group at the same (stem, filtration).",
         ha="center", fontsize=10)
fig.subplots_adjust(left=.055, right=.985, top=.89, bottom=.13, wspace=.38)
fig.savefig(HERE / "classical-adams.pdf", bbox_inches="tight")
fig.savefig(HERE / "classical-adams.png", dpi=180, bbox_inches="tight")
plt.close(fig)


def essential_arrows(q):
    if q == 4:
        return ([("v", a, "z", a, 0) for a in range(1, 4)]
                + [("u", a, "y", a+2, 2) for a in range(2)])
    return ([("v", a, "z", a, 0) for a in range(3, 6)]
            + [("u", a, "z", a+1, 1) for a in range(2)]
            + [("u", a, "y", a+2, 2) for a in (2, 3)]
            + [("x", 0, "y", 3, 3)])


fig, axs = plt.subplots(1, 2, figsize=(12.5, 8.0), sharey=True)
col = {"x": 0, "u": 1, "v": 2, "z": 4, "y": 5}
for ax, q in zip(axs, (4, 6)):
    ax.set_xlim(-.5, 5.65)
    ax.set_ylim(-.4, 6.25)
    ax.set_yticks(range(6))
    ax.set_xticks([0, 1, 2, 4, 5], [r"$x$", r"$u$", r"$v$", r"$z$", r"$y_0$"])
    ax.grid(axis="y", color="#dfe5ed")
    ax.set_axisbelow(True)
    ax.spines[["top", "right"]].set_visible(False)
    ax.axvspan(-.42, 2.4, color="#edf4fb", zorder=0)
    ax.axvspan(3.65, 5.5, color="#f3f5f7", zorder=0)
    ax.text(1, 5.95, "source components", ha="center", fontsize=10)
    ax.text(4.6, 5.95, "target components", ha="center", fontsize=10)
    ax.set_title(rf"$r={q+1}$, $q={q}$: "+("earlier page" if q == 4 else "later page"),
                 fontsize=14, pad=16)
    ax.set_xlabel("columns are summands, not stems", labelpad=10)
    if q == 4:
        ax.axhspan(3.5, 5.65, color="#e4e7eb", alpha=.9, zorder=1)
        ax.text(2.6, 4.8, r"outside the $q=4$ strip", ha="center", color="#727a85", fontsize=10)
        ax.axhline(3.5, color="#aab2bd", linestyle="--", linewidth=.9)
    for name in ("x", "u", "v", "z", "y"):
        start = q-3 if name == "v" else 0
        for a in range(start, q):
            ax.plot(col[name], a, "o", ms=6.7, mfc="white",
                    mec="#244563" if name in ("x", "u", "v") else "#6b7785",
                    mew=1.25, zorder=5)
            if q == 4 and name == "v" and a in (1, 2):
                ax.plot(col[name], a, "o", ms=12, mfc="none", mec=MAGENTA, mew=1.65, zorder=6)
    for src, a, dst, b, d in essential_arrows(q):
        ax.add_patch(FancyArrowPatch(
            (col[src], a), (col[dst], b), arrowstyle="-|>", mutation_scale=13,
            connectionstyle=f"arc3,rad={.035 if d == 0 else -.065}",
            shrinkA=5, shrinkB=6, color=COLORS[d], linewidth=1.65, zorder=3))
    if q == 4:
        ax.add_patch(FancyArrowPatch(
            (0, 0), (5, 3), arrowstyle="-|>", connectionstyle="arc3,rad=-0.1",
            mutation_scale=12, shrinkA=6, shrinkB=7,
            color="#8b9199", linewidth=1.5, linestyle=(0, (4, 3)), zorder=2))
        ax.text(.06, .62, r"equation only:"+"\n"+r"$d_3=0$ in ESS",
                color="#68717c", fontsize=10,
                bbox=dict(facecolor="white", edgecolor="none", alpha=.9))
    else:
        ax.text(.0, 1.3, r"$x_0\longrightarrow y_3$"+"\n"+"essential",
                color=COLORS[3], fontsize=10,
                bbox=dict(facecolor="white", edgecolor="none", alpha=.9))
axs[0].set_ylabel(r"filtration $a$ (all points have stem $1$, weight $1$)")
handles = [Line2D([0], [0], color=COLORS[d], lw=1.8, label=rf"essential $d_{d}$")
           for d in range(4)]
handles += [
    Line2D([0], [0], color="#8b9199", lw=1.5, ls="--", label="inessential equation"),
    Line2D([0], [0], marker="o", mfc="none", mec=MAGENTA, mew=1.6,
           linestyle="none", markersize=8, label=r"not liftable to $q=6$"),
]
fig.legend(handles=handles, loc="lower center", ncol=3, frameon=False, fontsize=10,
           bbox_to_anchor=(.5, .025))
fig.subplots_adjust(left=.07, right=.985, top=.9, bottom=.19, wspace=.12)
fig.savefig(HERE / "finite-ess.pdf", bbox_inches="tight")
fig.savefig(HERE / "finite-ess.png", dpi=180, bbox_inches="tight")
plt.close(fig)


# Check the displayed leading terms and essentiality in the coefficient model.
# These checks do not formalize its identification with spectra.
checks = []
for q in (4, 6):
    m = 2**q
    source = list(itertools.product(range(m), range(m), [c for c in range(m) if 8*c % m == 0]))

    def image(v):
        x, u, c = v
        return ((2*u+c) % m, (8*x+2*c) % m)

    def in_f(v, a):
        return all(c % (2**a) == 0 for c in v)

    for src, a, dst, b, d in essential_arrows(q):
        if src == "v":
            rep = (0, 0, 2**a)
        elif dst == "z":
            rep = (0, 2**a, 0)
        elif src == "u":
            rep = (0, 2**a, -(2**(a+1)) % m)
        else:
            rep = (1, 0, 0)
        target = image(rep)
        lead = tuple(c % (2**(b+1)) for c in target)
        assert 8*rep[2] % m == 0
        assert in_f(rep, a) and not in_f(rep, a+1)
        assert in_f(target, b) and not in_f(target, b+1)
        assert (lead[0] != 0) == (dst == "z")
        ambiguities = [v for v in source if in_f(v, a+1)
                       and in_f(image(v), b)
                       and tuple(c % (2**(b+1)) for c in image(v)) == lead]
        assert not ambiguities, (q, src, a, dst, b, ambiguities[:1])
        checks.append(dict(q=q, source=src, source_filtration=a, target=dst,
                           target_filtration=b, differential=d, essential=True,
                           representative=rep))
    hits = [v for v in source if in_f(v, 1) and in_f(image(v), 3)
            and tuple(c % 16 for c in image(v)) == (0, 8)]
    assert bool(hits) == (q == 4)
    checks.append(dict(q=q, original_x0_to_y3_essential=not bool(hits),
                       higher_source_witness_count=len(hits)))
(HERE / "chart-checks.json").write_text(json.dumps(checks, indent=2) + "\n")
print("Generated 2 vector charts; all displayed essential arrows and the original equation verified.")
