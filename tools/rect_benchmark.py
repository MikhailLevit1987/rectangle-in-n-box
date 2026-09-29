"""Timing of the rectangle criterion and of the explicit placement versus a numerical search over rotations.

Same design as box-in-box/tools/benchmark.py. The numerical baseline minimises
F(u, v) = max_i (A|u_i| + B|v_i|) / p_i over orthonormal pairs (u, v) (QR of a random n x 2 matrix)
by Nelder-Mead from random starts and answers "fits" as soon as some start reaches F <= 1. Such a search
can confirm fitting, but a "does not fit" answer only means that no start succeeded.

Test pairs lie close to the boundary: (A, B) is scaled by t*(1 + e) or t*(1 - e), where t* is the largest
scale at which the rectangle fits (bisection with the criterion) and 1e-4 <= e <= 1e-2.

Requires numpy and scipy.  A second, stronger baseline: SLSQP on the smooth lifted problem (used in the project as an independent check).

Usage: python rect_benchmark.py [pairs] [dims...]   (default: 50 pairs, n = 3 4 5 6)
"""
import math
import sys
import time

import numpy as np
from scipy.optimize import minimize

import rect_fit as rf


def uv(x, n):
    q, _ = np.linalg.qr(x.reshape(n, 2))
    return q[:, 0], q[:, 1]


def F_of(p, A, B, u, v):
    return float(np.max((A * np.abs(u) + B * np.abs(v)) / p))


def numeric_place(p, A, B, starts, rng):
    """Nelder-Mead (as in box-in-box): an orthonormal pair found by the search, or None."""
    n = len(p)
    p = np.asarray(p)

    def f(x):
        u, v = uv(x, n)
        return F_of(p, A, B, u, v)
    for _ in range(starts):
        r = minimize(f, rng.normal(size=2 * n), method='Nelder-Mead',
                     options={'xatol': 1e-10, 'fatol': 1e-12, 'maxiter': 2000 * n, 'maxfev': 2000 * n})
        if r.fun <= 1:
            return uv(r.x, n)
    return None


def slsqp_place(p, A, B, starts, rng):
    """SLSQP on the smooth lifted problem: min t subject to A a_i + B b_i <= t p_i, a >= |u|, b >= |v|,
    |u| = |v| = 1, u.v = 0. A candidate is accepted only after exact re-orthonormalisation: F(u, v) <= 1."""
    n = len(p)
    p = np.asarray(p)
    I = np.eye(n)
    cons = [
        {'type': 'ineq', 'fun': lambda z: np.concatenate([z[2*n:3*n] - z[:n], z[2*n:3*n] + z[:n],
                                                          z[3*n:4*n] - z[n:2*n], z[3*n:4*n] + z[n:2*n],
                                                          z[-1] * p - A * z[2*n:3*n] - B * z[3*n:4*n]]),
         'jac': lambda z: np.block([
             [-I, 0 * I, I, 0 * I, np.zeros((n, 1))],
             [I, 0 * I, I, 0 * I, np.zeros((n, 1))],
             [0 * I, -I, 0 * I, I, np.zeros((n, 1))],
             [0 * I, I, 0 * I, I, np.zeros((n, 1))],
             [0 * I, 0 * I, -A * I, -B * I, p[:, None]]])},
        {'type': 'eq', 'fun': lambda z: np.array([z[:n] @ z[:n] - 1, z[n:2*n] @ z[n:2*n] - 1, z[:n] @ z[n:2*n]]),
         'jac': lambda z: np.vstack([np.concatenate([2 * z[:n], np.zeros(3 * n + 1)]),
                                     np.concatenate([np.zeros(n), 2 * z[n:2*n], np.zeros(2 * n + 1)]),
                                     np.concatenate([z[n:2*n], z[:n], np.zeros(2 * n + 1)])])}]
    obj = lambda z: z[-1]
    grad = lambda z: np.concatenate([np.zeros(4 * n), [1.0]])
    for _ in range(starts):
        u, v = uv(rng.normal(size=2 * n), n)
        z0 = np.concatenate([u, v, np.abs(u), np.abs(v), [F_of(p, A, B, u, v)]])
        r = minimize(obj, z0, jac=grad, constraints=cons, method='SLSQP',
                     options={'ftol': 1e-14, 'maxiter': 500})
        u, v = uv(np.column_stack([r.x[:n], r.x[n:2*n]]).ravel(), n)
        if F_of(p, A, B, u, v) <= 1:
            return u, v
    return None


def instances(N, n, rng):
    out = []
    while len(out) < N:
        p = np.sort(rng.uniform(1, 3, n))[::-1]
        A = rng.uniform(0.3, 1)
        B = A * rng.uniform(0.05, 1)
        lo, hi = 0.0, 10.0 * math.sqrt(float(np.sum(p * p))) / A
        for _ in range(60):
            mid = (lo + hi) / 2
            if rf.fits(list(p), mid * A, mid * B):
                lo = mid
            else:
                hi = mid
        s = lo * (1 + rng.choice([-1, 1]) * 10 ** rng.uniform(-4, -2))
        out.append(([float(x) for x in p], float(s * A), float(s * B)))
    return out


def per_call(fn, data, repeat=20):
    t = time.perf_counter()
    for _ in range(repeat):
        for p, A, B in data:
            fn(p, A, B)
    return (time.perf_counter() - t) / (repeat * len(data))


def run(N, n, rng):
    data = instances(N, n, rng)
    exact = [rf.fits(*d) for d in data]
    fitting = [d for d, e in zip(data, exact) if e]
    cases = n * (n - 1) // 2 * 2 ** (n - 2)
    print(f"\nn = {n}: {len(data)} pairs near the boundary, {len(fitting)} of them fit; "
          f"{cases} cases in the criterion", flush=True)
    bad = sum(not rf.check(d[0], d[1], d[2], *rf.place(*d)) for d in fitting)
    t_c = per_call(rf.fits, data)
    t_pl = per_call(rf.place, fitting)
    print(f"  criterion (yes/no):             {t_c * 1e6:9.1f} us per pair", flush=True)
    print(f"  criterion + explicit placement: {t_pl * 1e6:9.1f} us per fitting pair "
          f"(invalid placements: {bad})", flush=True)
    for name, fn, starts_list in (("Nelder-Mead", numeric_place, (5, 20)),
                                  ("SLSQP", slsqp_place, (1, 5, 20))):
        for starts in starts_list:
            t = time.perf_counter()
            num = [fn(p, A, B, starts, rng) is not None for p, A, B in data]
            t_num = (time.perf_counter() - t) / len(data)
            missed = sum(e and not m for e, m in zip(exact, num))
            extra = sum(m and not e for e, m in zip(exact, num))
            print(f"  {name:11s} {starts:2d} starts: {t_num * 1e3:9.1f} ms per pair "
                  f"(~{t_num / t_c:,.0f} times slower); wrong \"does not fit\": {missed} of {len(fitting)}, "
                  f"fit found where the criterion says no: {extra}", flush=True)


def main():
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 50
    dims = [int(x) for x in sys.argv[2:]] or [3, 4, 5, 6]
    rng = np.random.default_rng(1)
    print(f"python {sys.version.split()[0]}, numpy {np.__version__}", flush=True)
    for n in dims:
        run(N, n, rng)
    print("\nDONE", flush=True)


if __name__ == "__main__":
    main()
