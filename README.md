# When does a rectangle fit into an n-dimensional box?

An explicit necessary and sufficient condition for an $A \times B$ rectangle to fit, after an
arbitrary rigid motion, into a rectangular box with edges $p_1, \dots, p_n \ge 0$, for every $n \ge 2$,
with a complete formal proof in Lean 4 / Mathlib.

*Русская версия статьи: [`paper/rectangle-in-n-box-ru.pdf`](paper/rectangle-in-n-box-ru.pdf).*

## The criterion

Carver's plane criterion: for $X \ge Y \ge 0$ (the container) and $a \ge b \ge 0$ (the rectangle),
the $a \times b$ rectangle fits into the $X \times Y$ rectangle iff $a \le X,\ b \le Y$, or

```math
a > X,\quad b \le Y,\quad \Bigl(\frac{X+Y}{a+b}\Bigr)^2+\Bigl(\frac{X-Y}{a-b}\Bigr)^2\ge 2 .
```

$\mathrm{Carver}(a,b;X,Y)$ denotes this condition after sorting both pairs. For $S \subseteq \{1,\dots,n\}$
let $\lVert p_S\rVert^2=\sum_{i\in S}p_i^2$.

**Theorem.** The $A \times B$ rectangle fits into the box $p$ if and only if for some axes $k \ne l$ and
some partition $S \sqcup T$ of the remaining axes

```math
\mathrm{Carver}\Bigl(\sqrt{A^2-\lVert p_S\rVert^2}_{+},\ \sqrt{B^2-\lVert p_T\rVert^2}_{+};\ p_k,\ p_l\Bigr).
```

These are $\tfrac12 n(n-1)2^{n-2}$ checks (1, 6, 24, 80, 240 for $n = 2, \dots, 6$). Geometrically, the side
$A$ runs along the diagonal of the coordinate subspace of the axes $S$, the side $B$ along that of $T$, and
the remainders are placed by Carver's criterion in the plane of the axes $k, l$. This is the case $k = 2$ of
the problem of Jerrard and Wetzel (*Amer. Math. Monthly* 111 (2004) 22–31) on a $k$-dimensional box in a
$d$-dimensional box; for the unit cube it reproduces their Theorem 5, and for a square it gives Nieuwland's
$3\sqrt2/4$.

## Contents

| Path | What |
|---|---|
| [`paper/rectangle-in-n-box-en.pdf`](paper/rectangle-in-n-box-en.pdf), [`paper/rectangle-in-n-box-ru.pdf`](paper/rectangle-in-n-box-ru.pdf) | The paper (English, Russian), LaTeX sources alongside |
| [`lean/`](lean/) | Lean 4 formalization; main theorem `RectInNBox.fitsN_rect_iff_explicit` in `lean/RectInNBox/RectCarver.lean` |
| [`lean/RectInNBox/Widths.lean`](lean/RectInNBox/Widths.lean) | The statement: definitions `boxN`, `pad`, `FitsN`, and the reduction to widths |
| [`tools/rect_fit.py`](tools/rect_fit.py) | Reference implementation: the criterion and an explicit position |
| [`tools/rect_benchmark.py`](tools/rect_benchmark.py) | Timing versus numerical searches over positions; results in `tools/rect_benchmark.log` |
| [`verification/`](verification/) | A self-contained prompt for independent checking that the Lean statement matches the theorem |

## Checking the formal proof

Requires [elan](https://github.com/leanprover/elan) (the Lean toolchain manager).

```sh
cd lean
lake exe cache get      # download prebuilt Mathlib (several GB)
lake build              # builds the RectInNBox library; a few minutes
lake env lean CheckAxioms.lean
```

Expected output of the last command:

```
'RectInNBox.fitsN_rect_iff_explicit' depends on axioms: [propext, Classical.choice, Quot.sound]
'RectInNBox.fitsN_rect_iff_condII' depends on axioms: [propext, Classical.choice, Quot.sound]
'RectInNBox.fits2_iff_carver' depends on axioms: [propext, Classical.choice, Quot.sound]
'RectInNBox.fitsN_rect_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'RectInNBox.fitsN_iff_widths' depends on axioms: [propext, Classical.choice, Quot.sound]
```

i.e. no `sorryAx`. The meaning of the theorem depends only on the definitions `boxN`, `pad` and `FitsN`
(`lean/RectInNBox/Widths.lean`) and on Carver's criterion `Carver` (`lean/RectInNBox/RectCarver.lean`),
which is the formula above.

| File | Content |
|---|---|
| `Reduction.lean` | A linearly mapped box inside an axis-parallel box ⇔ widths |
| `Strip.lean` | A rectangle in a strip (taken from the three-dimensional formalization) |
| `Widths.lean` | Statement; reduction to widths in `ℝⁿ`; the rectangle as orthonormal `u, v` |
| `RectSuff.lean` | Conditions (I), (II), the relaxed form, sufficiency, Lemma C |
| `RectV.lean`, `RectLemmas.lean` | Lemmas V and R |
| `RectMain.lean` | Necessity and the theorem with (II) |
| `RectCarver.lean` | Carver's plane criterion and the explicit form of the theorem |

## Using the reference implementation

```sh
python tools/rect_fit.py 1 1 1  1.06 1.06     # box p = (1, 1, 1), rectangle 1.06 × 1.06 → fits, prints u, v
python tools/rect_fit.py --selftest
python tools/rect_benchmark.py                # timing versus numerical searches (numpy, scipy)
```

In Python the criterion takes 6, 26, 80 and 194 µs per pair for $n = 3, 4, 5, 6$, the explicit position
7–42 µs. A multi-start numerical search is 330–170 000 times slower on pairs near the boundary and often
answers "does not fit" for a rectangle that fits (section "Computation" of the paper). Floating-point
comparisons are exact only in exact arithmetic; near the boundary rounding may flip the answer.

## Related

The analogous criterion for a three-dimensional box in a three-dimensional box:
[box-in-box](https://github.com/MikhailLevit1987/box-in-box),
[doi:10.5281/zenodo.22974798](https://doi.org/10.5281/zenodo.22974798).

## License

Code (`lean/`, `tools/`, `verification/`): [Apache License 2.0](LICENSE), the same as Mathlib.
Paper (`paper/`): [Creative Commons Attribution 4.0 International](paper/LICENSE).
