#!/usr/bin/env python3
"""
Aligned-angle MO stress test for shifted/scaled Crabb matrices.

This script uses the same quadratic/multilinear variation object as in tex/c.tex:
  M_u = sum_{j,k} c_{jk} A^j v u^* A^k
  S_u = (M_u + M_u^*) / 2
  F(u) = Re <x, S_u x>
and searches for xi (orthogonal to span{x,Ax,A*x} and to u) such that
  d/dt|_{0} F((u+t xi)/||u+t xi||)
is nonzero.

Support-angle selection:
  theta_* is chosen by maximizing |p(z_theta)| over sampled theta,
  with x_theta from top eigvec of H_theta and z_theta = <A x_theta, x_theta>.
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
    return np.array([alpha**m for m in range(n)], dtype=np.complex128)


def poly_eval_scalar(coeff: np.ndarray, z: complex) -> complex:
    out = 0.0 + 0.0j
    p = 1.0 + 0.0j
    for c in coeff:
        out += c * p
        p *= z
    return out


def poly_eval_matrix(a: np.ndarray, coeff: np.ndarray) -> np.ndarray:
    n = a.shape[0]
    out = np.zeros((n, n), dtype=np.complex128)
    p = np.eye(n, dtype=np.complex128)
    for c in coeff:
        out += c * p
        p = p @ a
    return out


def support_vec(a: np.ndarray, theta: float) -> Tuple[np.ndarray, float]:
    h = (np.exp(-1j * theta) * a + np.exp(1j * theta) * a.conj().T) / 2.0
    vals, vecs = np.linalg.eigh(h)
    idx = int(np.argmax(vals))
    x = vecs[:, idx]
    x = x / np.linalg.norm(x)
    return x, float(vals[idx].real)


def choose_theta_star(a: np.ndarray, coeff: np.ndarray, theta_samples: int) -> Tuple[float, np.ndarray, complex]:
    best_val = -1.0
    best_theta = 0.0
    best_x = None
    best_z = 0.0 + 0.0j
    for theta in np.linspace(0.0, 2.0 * np.pi, theta_samples, endpoint=False):
        x, _ = support_vec(a, float(theta))
        z = np.vdot(x, a @ x)
        val = abs(poly_eval_scalar(coeff, z))
        if val > best_val:
            best_val = val
            best_theta = float(theta)
            best_x = x
            best_z = z
    assert best_x is not None
    return best_theta, best_x, best_z


def cjk_from_coeff(coeff: np.ndarray) -> np.ndarray:
    d = len(coeff) - 1
    cjk = np.zeros((d, d), dtype=np.complex128)
    for j in range(d):
        for k in range(d):
            t = j + k + 1
            if t <= d:
                cjk[j, k] = coeff[t]
    return cjk


def build_M(a: np.ndarray, v: np.ndarray, u: np.ndarray, coeff: np.ndarray) -> np.ndarray:
    d = len(coeff) - 1
    cjk = cjk_from_coeff(coeff)

    a_pow_v = [v]
    a_pow_row = [u.conj().reshape(1, -1)]  # row u*
    for _ in range(1, d):
        a_pow_v.append(a @ a_pow_v[-1])
        a_pow_row.append(a_pow_row[-1] @ a)

    n = a.shape[0]
    m = np.zeros((n, n), dtype=np.complex128)
    for j in range(d):
        left = a_pow_v[j].reshape(-1, 1)
        for k in range(d):
            cij = cjk[j, k]
            if cij == 0:
                continue
            m += cij * (left @ a_pow_row[k])
    return m


def F_value(a: np.ndarray, x: np.ndarray, v: np.ndarray, u: np.ndarray, coeff: np.ndarray) -> float:
    m = build_M(a, v, u, coeff)
    s = (m + m.conj().T) / 2.0
    return float(np.real(np.vdot(x, s @ x)))


def variation_formula(a: np.ndarray, x: np.ndarray, v: np.ndarray, coeff: np.ndarray, xi: np.ndarray) -> float:
    d = len(coeff) - 1
    cjk = cjk_from_coeff(coeff)

    a_pow_x = [x]
    a_pow_v = [v]
    for _ in range(1, d):
        a_pow_x.append(a @ a_pow_x[-1])
        a_pow_v.append(a @ a_pow_v[-1])

    s = 0.0 + 0.0j
    for j in range(d):
        for k in range(d):
            cij = cjk[j, k]
            if cij == 0:
                continue
            # For xi ⟂ u and u_t = (u + t xi)/||u + t xi||:
            # d/dt Re <x, S_{u_t} x>|_{t=0} = Re d/dt <x, M_{u_t} x>|_{t=0}.
            s += cij * np.vdot(x, a_pow_v[j]) * np.vdot(xi, a_pow_x[k])
    return float(np.real(s))


def orth_basis(vs: List[np.ndarray], tol: float = 1e-11) -> np.ndarray:
    b = np.stack(vs, axis=1)
    q, r = np.linalg.qr(b)
    rank = int(np.sum(np.abs(np.diag(r)) > tol))
    return q[:, :rank]


@dataclass
class Candidate:
    n: int
    theta: float
    z_theta: complex
    fd_abs: float
    fd_derivative: float
    formula_derivative: float
    formula_fd_gap: float
    eps_sweep: List[Tuple[float, float]]
    orth_span_resid: float
    orth_u_resid: float
    x: np.ndarray
    u: np.ndarray
    v: np.ndarray
    xi: np.ndarray
    cjk: np.ndarray


def fd_directional_derivative(
    a: np.ndarray,
    x: np.ndarray,
    v: np.ndarray,
    u: np.ndarray,
    coeff: np.ndarray,
    xi: np.ndarray,
    eps: float,
) -> float:
    up = u + eps * xi
    um = u - eps * xi
    up = up / np.linalg.norm(up)
    um = um / np.linalg.norm(um)
    fdp = F_value(a, x, v, up, coeff)
    fdm = F_value(a, x, v, um, coeff)
    return float((fdp - fdm) / (2.0 * eps))


def search_candidate(
    n: int,
    theta_samples: int,
    trials: int,
    seed: int,
    fd_eps: float,
) -> Candidate | None:
    rng = np.random.default_rng(seed)
    alpha = 1.0 + math.sqrt(2.0)
    a = shifted_crabb_matrix(n, alpha)
    coeff = poly_coeff_inverse(alpha, n)

    theta_star, x, z_theta = choose_theta_star(a, coeff, theta_samples)

    pa = poly_eval_matrix(a, coeff)
    U, _, Vh = np.linalg.svd(pa)
    v = U[:, 0]
    u = np.conj(Vh[0, :])
    u = u / np.linalg.norm(u)

    span_q = orth_basis([x, a @ x, a.conj().T @ x])
    u_orth = u - span_q @ (span_q.conj().T @ u) if span_q.shape[1] > 0 else u.copy()
    nu = np.linalg.norm(u_orth)
    has_u_dir = nu > 1e-11
    if has_u_dir:
        q_u = u_orth / nu

    best = None
    for _ in range(trials):
        z = rng.normal(size=n) + 1j * rng.normal(size=n)
        if span_q.shape[1] > 0:
            z = z - span_q @ (span_q.conj().T @ z)
        if has_u_dir:
            z = z - q_u * np.vdot(q_u, z)
        nz = np.linalg.norm(z)
        if nz < 1e-12:
            continue
        xi = z / nz

        fd = fd_directional_derivative(a, x, v, u, coeff, xi, fd_eps)
        if best is None or abs(fd) > best[0]:
            best = (abs(fd), fd, xi.copy())

    if best is None:
        return None

    fdabs, fdv, xi = best
    formula_v = variation_formula(a, x, v, coeff, xi)
    formula_gap = abs(formula_v - fdv)
    eps_sweep: List[Tuple[float, float]] = []
    for eps in [1e-4, 1e-5, 1e-6, 1e-7]:
        d = fd_directional_derivative(a, x, v, u, coeff, xi, eps)
        eps_sweep.append((eps, d))
    orth_span = np.linalg.norm(span_q.conj().T @ xi) if span_q.shape[1] > 0 else 0.0
    orth_u = abs(np.vdot(u, xi))
    return Candidate(
        n=n,
        theta=theta_star,
        z_theta=z_theta,
        fd_abs=fdabs,
        fd_derivative=fdv,
        formula_derivative=formula_v,
        formula_fd_gap=formula_gap,
        eps_sweep=eps_sweep,
        orth_span_resid=float(orth_span),
        orth_u_resid=float(orth_u),
        x=x,
        u=u,
        v=v,
        xi=xi,
        cjk=cjk_from_coeff(coeff),
    )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--n-values", type=int, nargs="+", default=[4, 5])
    parser.add_argument("--theta-samples", type=int, default=721)
    parser.add_argument("--trials", type=int, default=4000)
    parser.add_argument("--seed", type=int, default=123)
    parser.add_argument("--fd-eps", type=float, default=1e-6)
    parser.add_argument("--dump", action="store_true")
    args = parser.parse_args()

    alpha = 1.0 + math.sqrt(2.0)
    print(f"alpha = {alpha:.15f}")
    print(
        f"theta_samples={args.theta_samples}, trials={args.trials}, seed={args.seed}, fd_eps={args.fd_eps}"
    )
    print("")

    for i, n in enumerate(args.n_values):
        cand = search_candidate(
            n=n,
            theta_samples=args.theta_samples,
            trials=args.trials,
            seed=args.seed + i,
            fd_eps=args.fd_eps,
        )
        if cand is None:
            print(f"n={n}: no admissible xi found")
            continue
        print(
            f"n={cand.n} theta*={cand.theta:.6f} |p(z_theta*)|={abs(poly_eval_scalar(poly_coeff_inverse(alpha, n), cand.z_theta)):.9e}"
        )
        print(
            f"    |fd-derivative|={cand.fd_abs:.9e} fd-derivative={cand.fd_derivative:.9e}"
        )
        print(
            f"    formula-derivative={cand.formula_derivative:.9e} |fd-formula|={cand.formula_fd_gap:.3e}"
        )
        print(
            f"    orth_residual(span)={cand.orth_span_resid:.3e} orth_residual(u)={cand.orth_u_resid:.3e}"
        )
        sweep_str = ", ".join([f"eps={eps:.0e}: {d:.6e}" for eps, d in cand.eps_sweep])
        print(f"    eps-sweep: {sweep_str}")
        if args.dump:
            np.set_printoptions(precision=6, suppress=True)
            print(f"    z_theta* = {cand.z_theta}")
            print(f"    x  = {cand.x}")
            print(f"    u  = {cand.u}")
            print(f"    v  = {cand.v}")
            print(f"    xi = {cand.xi}")
            print(f"    cjk =\n{cand.cjk}")
        print("")

    print("Interpretation:")
    print("  Nonzero variation + fd agreement means the multilinear derivative is numerically nonzero")
    print("  for the selected support-angle model data. This is candidate disproof evidence,")
    print("  not a formal theorem-level disproof yet.")


if __name__ == "__main__":
    main()
