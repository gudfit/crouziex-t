#!/usr/bin/env python3
"""
Near-extremal coefficient search for shifted Crabb A = I - alpha K_n,
followed by MO first-variation test on that same coefficient set.

This is quantifier-aligned numerical evidence:
  1) pick degree (n-1) polynomial coefficients by maximizing
       ||p(A)|| / max_theta |p(z_theta)|
  2) use the resulting p to define c_{jk}
  3) choose x = x_{theta*} at maximizing theta*
  4) choose (u,v) as top singular vectors of p(A)
  5) search xi with xi ⟂ span{x,Ax,A*x} and xi ⟂ u
  6) report finite-difference and multilinear-form derivative agreement
"""

from __future__ import annotations

import argparse
import math
from typing import Tuple

import numpy as np

from mo_shifted_crabb_aligned_search import (
    fd_directional_derivative,
    orth_basis,
    poly_eval_matrix,
    poly_eval_scalar,
    shifted_crabb_matrix,
    support_vec,
    variation_formula,
)


def coeff_ratio(a: np.ndarray, coeff: np.ndarray, z_samples: np.ndarray) -> Tuple[float, float, float]:
    pa = poly_eval_matrix(a, coeff)
    num = float(np.linalg.svd(pa, compute_uv=False)[0])
    den = float(max(abs(poly_eval_scalar(coeff, z)) for z in z_samples))
    if den <= 1e-14:
        return 0.0, num, den
    return num / den, num, den


def find_near_extremal_coeff(
    a: np.ndarray,
    n: int,
    z_samples: np.ndarray,
    alpha: float,
    seed: int,
    random_iters: int,
    local_iters: int,
) -> Tuple[np.ndarray, float, float, float]:
    rng = np.random.default_rng(seed)

    best_coeff = np.array([alpha**k for k in range(n)], dtype=np.complex128)
    best_ratio, best_num, best_den = coeff_ratio(a, best_coeff, z_samples)

    for _ in range(random_iters):
        c = rng.normal(size=n) + 1j * rng.normal(size=n)
        c /= max(np.max(np.abs(c)), 1e-12)
        r, num, den = coeff_ratio(a, c, z_samples)
        if r > best_ratio:
            best_ratio, best_num, best_den = r, num, den
            best_coeff = c.copy()

    step = 0.20
    for _ in range(local_iters):
        cand = best_coeff + step * (rng.normal(size=n) + 1j * rng.normal(size=n))
        r, num, den = coeff_ratio(a, cand, z_samples)
        if r > best_ratio:
            best_ratio, best_num, best_den = r, num, den
            best_coeff = cand
            step *= 1.01
        else:
            step *= 0.9995

    return best_coeff, best_ratio, best_num, best_den


def search_xi_for_coeff(
    a: np.ndarray,
    coeff: np.ndarray,
    thetas: np.ndarray,
    x_samples: list[np.ndarray],
    z_samples: np.ndarray,
    trials: int,
    seed: int,
    fd_eps: float,
):
    vals = [abs(poly_eval_scalar(coeff, z)) for z in z_samples]
    idx = int(np.argmax(vals))
    theta_star = float(thetas[idx])
    x = x_samples[idx]
    z_star = z_samples[idx]

    pa = poly_eval_matrix(a, coeff)
    U, _, Vh = np.linalg.svd(pa)
    v = U[:, 0]
    u = np.conj(Vh[0, :])
    u = u / np.linalg.norm(u)

    span_q = orth_basis([x, a @ x, a.conj().T @ x])
    u_orth = u - span_q @ (span_q.conj().T @ u) if span_q.shape[1] > 0 else u.copy()
    has_u_dir = np.linalg.norm(u_orth) > 1e-11
    if has_u_dir:
        q_u = u_orth / np.linalg.norm(u_orth)

    rng = np.random.default_rng(seed + 1000)
    best_fd = None
    best_xi = None
    for _ in range(trials):
        z = rng.normal(size=a.shape[0]) + 1j * rng.normal(size=a.shape[0])
        if span_q.shape[1] > 0:
            z = z - span_q @ (span_q.conj().T @ z)
        if has_u_dir:
            z = z - q_u * np.vdot(q_u, z)
        nz = np.linalg.norm(z)
        if nz < 1e-12:
            continue
        xi = z / nz
        fd = fd_directional_derivative(a, x, v, u, coeff, xi, fd_eps)
        if best_fd is None or abs(fd) > abs(best_fd):
            best_fd = fd
            best_xi = xi

    if best_xi is None:
        return None

    form = variation_formula(a, x, v, coeff, best_xi)
    orth_span = np.linalg.norm(span_q.conj().T @ best_xi) if span_q.shape[1] > 0 else 0.0
    orth_u = abs(np.vdot(u, best_xi))
    return {
        "theta_star": theta_star,
        "z_star": z_star,
        "x": x,
        "u": u,
        "v": v,
        "xi": best_xi,
        "fd": float(best_fd),
        "form": float(form),
        "gap": float(abs(form - best_fd)),
        "orth_span": float(orth_span),
        "orth_u": float(orth_u),
        "boundary_val": float(vals[idx]),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--n", type=int, default=4)
    parser.add_argument("--theta-samples", type=int, default=721)
    parser.add_argument("--random-iters", type=int, default=18000)
    parser.add_argument("--local-iters", type=int, default=8000)
    parser.add_argument("--xi-trials", type=int, default=10000)
    parser.add_argument("--seed", type=int, default=123)
    parser.add_argument("--fd-eps", type=float, default=1e-6)
    parser.add_argument("--dump", action="store_true")
    args = parser.parse_args()

    alpha = 1.0 + math.sqrt(2.0)
    a = shifted_crabb_matrix(args.n, alpha)

    thetas = np.linspace(0.0, 2.0 * np.pi, args.theta_samples, endpoint=False)
    x_samples = []
    z_samples = []
    for theta in thetas:
        x, _ = support_vec(a, float(theta))
        z = np.vdot(x, a @ x)
        x_samples.append(x)
        z_samples.append(z)
    z_samples = np.array(z_samples, dtype=np.complex128)

    coeff, r, num, den = find_near_extremal_coeff(
        a=a,
        n=args.n,
        z_samples=z_samples,
        alpha=alpha,
        seed=args.seed,
        random_iters=args.random_iters,
        local_iters=args.local_iters,
    )

    info = search_xi_for_coeff(
        a=a,
        coeff=coeff,
        thetas=thetas,
        x_samples=x_samples,
        z_samples=z_samples,
        trials=args.xi_trials,
        seed=args.seed,
        fd_eps=args.fd_eps,
    )

    print(f"alpha = {alpha:.15f}")
    print(f"n = {args.n}")
    print(f"theta_samples = {args.theta_samples}")
    print(f"random_iters = {args.random_iters}, local_iters = {args.local_iters}, xi_trials = {args.xi_trials}")
    print(f"seed = {args.seed}, fd_eps = {args.fd_eps}")
    print("")
    print(f"best ratio ~= {r:.9e}")
    print(f"numerator ||p(A)|| = {num:.9e}")
    print(f"denominator max|p(z_theta)| = {den:.9e}")

    if info is None:
        print("No admissible xi found after orthogonality projection.")
        return

    print(f"theta* = {info['theta_star']:.6f}")
    print(f"z(theta*) = {info['z_star']}")
    print(f"|p(z(theta*))| = {info['boundary_val']:.9e}")
    print(f"fd-derivative = {info['fd']:.9e}")
    print(f"formula-derivative = {info['form']:.9e}")
    print(f"|fd-formula| = {info['gap']:.3e}")
    print(f"orth_residual(span) = {info['orth_span']:.3e}")
    print(f"orth_residual(u) = {info['orth_u']:.3e}")

    if args.dump:
        np.set_printoptions(precision=6, suppress=True)
        print("coeff =", coeff)
        print("x =", info["x"])
        print("u =", info["u"])
        print("v =", info["v"])
        print("xi =", info["xi"])


if __name__ == "__main__":
    main()
