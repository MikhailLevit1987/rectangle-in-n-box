"""Rectangle A x B in the n-dimensional box p: the criterion (II) and an explicit placement.

Criterion (paper, Theorem 2.1; Lean: lean/RectInNBox/RectCarver.lean, fitsN_rect_iff_explicit):
the rectangle fits iff for some axes k != l and a partition S + T of the other axes
Carver(a', b'; p_k, p_l) holds, a' = sqrt(A^2 - |p_S|^2)_+, b' = sqrt(B^2 - |p_T|^2)_+.
There are n(n-1)/2 * 2^(n-2) cases (Carver is symmetric in p_k, p_l).

The placement is the construction from the proof of sufficiency (paper, Section 3):
A u = lam p_S + a' f_a, B v = mu p_T + b' f_b with f_a, f_b from Carver in the plane of the axes k, l.
Then x -> x0 + s A u + r B v, s, r in [0, 1], lies in the box for a suitable shift x0.

Usage: python rect_fit.py 1 1 1 1  1.5 0.4     (box p_1..p_n, then A B)
       python rect_fit.py --selftest
"""
import itertools
import math
import random
import sys


def carver(a, b, X, Y):
    """Carver 1957: the rectangle a x b fits into the rectangle X x Y."""
    a, b = max(a, b), min(a, b)
    X, Y = max(X, Y), min(X, Y)
    if a <= X and b <= Y:
        return True
    if b > Y:
        return False
    # here a > X >= Y >= b, so a > b
    return ((X + Y) / (a + b)) ** 2 + ((X - Y) / (a - b)) ** 2 >= 2


def carver_frame(a, b, X, Y):
    """Orthonormal f_a, f_b in the plane (X-axis, Y-axis) with a|f_a| + b|f_b| <= (X, Y), or None."""
    if not carver(a, b, X, Y):
        return None
    swap_ab, swap_xy = a < b, X < Y
    if swap_ab:
        a, b = b, a
    if swap_xy:
        X, Y = Y, X
    if a <= X and b <= Y:
        th = 0.0
    else:
        # smallest angle with a cos th + b sin th = X; Carver guarantees a sin th + b cos th <= Y there
        r = math.hypot(a, b)
        th = math.atan2(b, a) + math.acos(min(1.0, X / r))
    c, s = math.cos(th), math.sin(th)
    fa, fb = (c, s), (-s, c)
    if swap_xy:
        fa, fb = fa[::-1], fb[::-1]
    if swap_ab:
        fa, fb = fb, fa
    return fa, fb


def _cases(p, A, B):
    """All (k, l, S, T, a', b') of the criterion."""
    n = len(p)
    sq = [x * x for x in p]
    for k, l in itertools.combinations(range(n), 2):
        rest = [i for i in range(n) if i != k and i != l]
        tot = sum(sq[i] for i in rest)
        for mask in range(1 << len(rest)):
            ps2 = 0.0
            for t, i in enumerate(rest):
                if not mask >> t & 1:
                    ps2 += sq[i]
            yield k, l, rest, mask, math.sqrt(max(0.0, A * A - ps2)), math.sqrt(max(0.0, B * B - (tot - ps2)))


def fits(p, A, B):
    """The criterion: yes / no."""
    n = len(p)
    sq = [x * x for x in p]
    A2, B2 = A * A, B * B
    for k, l in itertools.combinations(range(n), 2):
        pk, pl = p[k], p[l]
        rest = [sq[i] for i in range(n) if i != k and i != l]
        tot = sum(rest)
        for mask in range(1 << len(rest)):
            ps2 = 0.0
            for t, s in enumerate(rest):
                if not mask >> t & 1:
                    ps2 += s
            a = A2 - ps2
            b = B2 - (tot - ps2)
            if carver(math.sqrt(a) if a > 0 else 0.0, math.sqrt(b) if b > 0 else 0.0, pk, pl):
                return True
    return False


def place(p, A, B):
    """Orthonormal u, v with A|u_i| + B|v_i| <= p_i (paper, Section 3), or None if the rectangle does not fit."""
    n = len(p)
    for k, l, rest, mask, a, b in _cases(p, A, B):
        fr = carver_frame(a, b, p[k], p[l])
        if fr is None:
            continue
        fa, fb = fr
        S = [i for t, i in enumerate(rest) if not mask >> t & 1]
        T = [i for t, i in enumerate(rest) if mask >> t & 1]

        def edge(L, part, rem, f):
            """L * w = lam p_part + rem f; w is a unit vector (any unit f if L = 0)."""
            w = [0.0] * n
            if L == 0:
                w[k], w[l] = f
                return w
            nrm = math.sqrt(sum(p[i] ** 2 for i in part))
            lam = min(1.0, L / nrm) if nrm > 0 else 0.0
            for i in part:
                w[i] = lam * p[i] / L
            w[k], w[l] = rem * f[0] / L, rem * f[1] / L
            return w

        return edge(A, S, a, fa), edge(B, T, b, fb)
    return None


def check(p, A, B, u, v, tol=1e-9):
    """The placement is valid: u, v orthonormal and all widths within the box."""
    dot = lambda x, y: sum(s * t for s, t in zip(x, y))
    ok_orth = abs(dot(u, u) - 1) < tol and abs(dot(v, v) - 1) < tol and abs(dot(u, v)) < tol
    ok_w = all(A * abs(ui) + B * abs(vi) <= pi * (1 + tol) + tol for ui, vi, pi in zip(u, v, p))
    return ok_orth and ok_w


def selftest(N=20000, seed=1):
    rng = random.Random(seed)
    yes = bad = 0
    for _ in range(N):
        n = rng.randint(2, 7)
        p = [rng.uniform(0.05, 1) for _ in range(n)]
        if rng.random() < 0.2:
            p[rng.randrange(n)] = 0.0
        diag = math.sqrt(sum(x * x for x in p))
        A = rng.uniform(0, 1.2) * diag
        B = rng.choice([0.0, rng.uniform(0, 1) * A, A])
        f, pl = fits(p, A, B), place(p, A, B)
        yes += f
        if f != (pl is not None) or (pl is not None and not check(p, A, B, *pl)):
            bad += 1
            print("FAIL", p, A, B, f, pl)
    print(f"selftest: {N} random cases, {yes} fit, placement verified for all of them; failures: {bad}")
    return bad == 0


def main():
    if sys.argv[1:] == ["--selftest"]:
        sys.exit(0 if selftest() else 1)
    *p, A, B = map(float, sys.argv[1:])
    pl = place(p, A, B)
    if pl is None:
        print("does not fit")
    else:
        u, v = pl
        print("fits")
        print("u =", [round(x, 12) for x in u])
        print("v =", [round(x, 12) for x in v])
        print("widths A|u_i| + B|v_i| =", [round(A * abs(a) + B * abs(b), 12) for a, b in zip(u, v)])


if __name__ == "__main__":
    main()
