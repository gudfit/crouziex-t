#!/usr/bin/env python3
"""
Numerical MO stress test on shifted/scaled Crabb matrices.

This script searches for large values of the quadratic multilinear variation
expression used in tex/c.tex (eq:multilinear-vanish style), under
  xi ⟂ span{x, A x, A* x}
and also xi ⟂ u (tangent-like unit-vector variation constraint).

Model choices:
  - A = I - alpha K_n  (shifted Crabb), alpha = 1 + sqrt(2)
  - A = K_n            (for comparison)
  - polynomial coefficients a_m = alpha^m, m = 0..n-1
    (truncated inverse / finite Neumann polynomial)
  - c_{j,k} = a_{j+k+1} when j+k+1 <= d, else 0
"""

from __future__ import annotations

import argparse
import math
from dataclasses import dataclass
from typing import List, Tuple

import numpy as np


def crabb_matrix(n: int) -> np.ndarray:
    k = np.zeros((n, n), dtype=np.complex128)
    s2 = math.sqrt(2.0)
    for i in range(n - 1):
        w = (s2 if i == 0 else 1.0) * (s2 if i == n - 2 else 1.0)
        k[i, i + 1] = w
    return k


def shifted_crabb_matrix(n: int, alpha: float) -> np.ndarray:
    return np.eye(n, dtype=np.complex128) - alpha * crabb_matrix(n)


def poly_coeff_inverse(alpha: float, n: int) -> np.ndarray:
    # p(z) = sum_{m=0}^{n-1} (alpha z)^m
    return np.array([alpha**m for m in range(n)], dtype=np.complex128)


def eval_poly_matrix(a: np.ndarray, coeff: np.ndarray) -> np.ndarray:
    n = a.shape[0]
    out = np.zeros_like(a)
    p = np.eye(n, dtype=np.complex128)
    for c in coeff:
        out += c * p
        p = p @ a
    return out


def support_vector(a: np.ndarray, theta: float) -> Tuple[np.ndarray, float]:
    h = (np.exp(-1j * theta) * a + np.exp(1j * theta) * a.conj().T) / 2.0
    vals, vecs = np.linalg.eigh(h)
    idx = int(np.argmax(vals))
    x = vecs[:, idx]
    x = x / np.linalg.norm(x)
    return x, float(vals[idx].real)


def cjk_from_coeff(coeff: np.ndarray) -> np.ndarray:
    # d = degree
    d = len(coeff) - 1
    cjk = np.zeros((d, d), dtype=np.complex128)
    for j in range(d):
        for k in range(d):
            t = j + k + 1
            if t <= d:
                cjk[j, k] = coeff[t]
    return cjk


def multilinear_variation(
    a: np.ndarray,
    x: np.ndarray,
    v: np.ndarray,
    coeff: np.ndarray,
    xi: np.ndarray,
) -> float:
    """
    Evaluates the real multilinear expression:
      Re sum_{j,k} c_jk [ (x* A^j v) <A^k x, xi>* + conj(c_jk) <(A*)^k x, xi> (v* (A*)^j x) ]
    """
    d = len(coeff) - 1
    cjk = cjk_from_coeff(coeff)

    a_pow_x = [x]
    astar_pow_x = [x]
    a_pow_v = [v]
    for _ in range(1, d):
        a_pow_x.append(a @ a_pow_x[-1])
        astar_pow_x.append(a.conj().T @ astar_pow_x[-1])
        a_pow_v.append(a @ a_pow_v[-1])

    s = 0.0 + 0.0j
    for j in range(d):
        for k in range(d):
            cij = cjk[j, k]
            if cij == 0:
                continue
            term1 = cij * np.vdot(x, a_pow_v[j]) * np.conj(np.vdot(xi, a_pow_x[k]))
            term2 = (
                np.conj(cij)
                * np.vdot(xi, astar_pow_x[k])
                * np.vdot(v, astar_pow_x[j])
            )
            s += term1 + term2
    return float(np.real(s))


def orthonormal_cols(vs: List[np.ndarray], tol: float = 1e-11) -> np.ndarray:
    b = np.stack(vs, axis=1)
    q, r = np.linalg.qr(b)
    diag = np.abs(np.diag(r))
    rank = int(np.sum(diag > tol))
    return q[:, :rank]


def orth_residual(v: np.ndarray, q: np.ndarray) -> float:
    if q.shape[1] == 0:
        return 0.0
    return float(np.linalg.norm(q.conj().T @ v))


@dataclass
class SearchHit:
    n: int
    model: str
    found_direction: bool
    abs_val: float
    val: float
    theta: float
    lambda_max: float
    orth_span_resid: float
    orth_u_resid: float
    x: np.ndarray | None
    xi: np.ndarray | None
    u: np.ndarray | None
    v: np.ndarray | None


def search_model(
    n: int,
    a: np.ndarray,
    coeff: np.ndarray,
    theta_samples: int,
    trials_per_theta: int,
    seed: int,
) -> SearchHit:
    rng = np.random.default_rng(seed)

    pa = eval_poly_matrix(a, coeff)
    u_mat, _, vh = np.linalg.svd(pa)
    v = u_mat[:, 0]
    u = np.conj(vh[0, :])
    u = u / np.linalg.norm(u)

    best_abs = -1.0
    best_val = 0.0
    best_theta = 0.0
    best_lambda = 0.0
    best_span_res = 0.0
    best_u_res = 0.0
    best_x: np.ndarray | None = None
    best_xi: np.ndarray | None = None
    found = False

    for theta in np.linspace(0.0, 2.0 * np.pi, theta_samples, endpoint=False):
        x, lam = support_vector(a, float(theta))
        span_q = orthonormal_cols([x, a @ x, a.conj().T @ x])
        if span_q.shape[1] > 0:
            u_orth = u - span_q @ (span_q.conj().T @ u)
        else:
            u_orth = u.copy()
        u_orth_norm = np.linalg.norm(u_orth)
        has_u_dir = u_orth_norm > 1e-11
        if has_u_dir:
            q_u = u_orth / u_orth_norm

        for _ in range(trials_per_theta):
            z = rng.normal(size=n) + 1j * rng.normal(size=n)
            if span_q.shape[1] > 0:
                z = z - span_q @ (span_q.conj().T @ z)
            if has_u_dir:
                z = z - q_u * np.vdot(q_u, z)
            nz = np.linalg.norm(z)
            if nz < 1e-12:
                continue
            found = True
            xi = z / nz
            val = multilinear_variation(a, x, v, coeff, xi)
            aval = abs(val)
            if aval > best_abs:
                best_abs = aval
                best_val = val
                best_theta = float(theta)
                best_lambda = lam
                best_span_res = orth_residual(xi, span_q)
                best_u_res = abs(np.vdot(xi, u))
                best_x = x.copy()
                best_xi = xi.copy()

    return SearchHit(
        n=n,
        model="",
        found_direction=found,
        abs_val=best_abs,
        val=best_val,
        theta=best_theta,
        lambda_max=best_lambda,
        orth_span_resid=best_span_res,
        orth_u_resid=best_u_res,
        x=best_x,
        xi=best_xi,
        u=u.copy(),
        v=v.copy(),
    )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--n-values", type=int, nargs="+", default=[4, 5])
    parser.add_argument("--theta-samples", type=int, default=361)
    parser.add_argument("--trials-per-theta", type=int, default=500)
    parser.add_argument("--seed", type=int, default=7)
    parser.add_argument("--dump-vectors", action="store_true")
    args = parser.parse_args()

    alpha = 1.0 + math.sqrt(2.0)
    print(f"alpha = {alpha:.15f}")
    print(
        f"theta_samples = {args.theta_samples}, trials_per_theta = {args.trials_per_theta}, seed = {args.seed}"
    )
    print("")

    for n in args.n_values:
        coeff = poly_coeff_inverse(alpha, n)
        a_shifted = shifted_crabb_matrix(n, alpha)
        a_k = crabb_matrix(n)

        hit_shifted = search_model(
            n=n,
            a=a_shifted,
            coeff=coeff,
            theta_samples=args.theta_samples,
            trials_per_theta=args.trials_per_theta,
            seed=args.seed,
        )
        hit_shifted.model = "shifted"

        hit_k = search_model(
            n=n,
            a=a_k,
            coeff=coeff,
            theta_samples=args.theta_samples,
            trials_per_theta=args.trials_per_theta,
            seed=args.seed + 1,
        )
        hit_k.model = "K"

        for hit in (hit_shifted, hit_k):
            if not hit.found_direction:
                print(
                    f"n={hit.n:2d} model={hit.model:7s} no nonzero xi remained after orthogonality constraints."
                )
                continue
            print(
                f"n={hit.n:2d} model={hit.model:7s} |variation|={hit.abs_val:.9e} "
                f"variation={hit.val:.9e} theta={hit.theta:.6f} lambda_max={hit.lambda_max:.9e}"
            )
            print(
                f"                orth_residual(span)={hit.orth_span_resid:.3e} "
                f"orth_residual(u)={hit.orth_u_resid:.3e}"
            )
            if args.dump_vectors:
                np.set_printoptions(precision=6, suppress=True)
                print(f"                x  = {hit.x}")
                print(f"                xi = {hit.xi}")
                print(f"                u  = {hit.u}")
                print(f"                v  = {hit.v}")
        print("")

    print("Interpretation:")
    print(
        "  Large nonzero values indicate a candidate MO failure for the tested coefficient ansatz."
    )
    print(
        "  This is numerical evidence only; it is not yet a formal counterexample."
    )


if __name__ == "__main__":
    main()
