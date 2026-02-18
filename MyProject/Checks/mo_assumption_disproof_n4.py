#!/usr/bin/env python3
"""
Symbolic disproof candidate for the strong pointwise MO wording ("for any unit u").

Model:
  A = I - alpha K_4, alpha = 1 + sqrt(2)
  f(z) = z^3  (degree 3 => c_{02}=c_{11}=c_{20}=1)
  x = (-1/sqrt(6), 1/sqrt(3), -1/sqrt(3), 1/sqrt(6))^T
  xi = (0, 1, 1, 0)^T
  v = x

Checks:
  1) xi ⟂ x, xi ⟂ Ax, xi ⟂ A* x
  2) First-variation term from the multilinear expansion is nonzero:
       Re sum_{j,k} c_{jk} (x^* A^j v) (xi^* A^k x)
     For f(z)=z^3 and v=x, only the k=2 channel survives under xi-orthogonality,
     giving Re(xi^* A^2 x) = 2*sqrt(6)/3 + sqrt(3) > 0.
"""

from __future__ import annotations

import sympy as sp


def main() -> None:
    sqrt2 = sp.sqrt(2)
    alpha = 1 + sqrt2

    # Shifted/scaled Crabb model in dimension 4.
    A = sp.Matrix(
        [
            [1, -alpha * sqrt2, 0, 0],
            [0, 1, -alpha, 0],
            [0, 0, 1, -alpha * sqrt2],
            [0, 0, 0, 1],
        ]
    )

    x = sp.Matrix(
        [
            -1 / sp.sqrt(6),
            1 / sp.sqrt(3),
            -1 / sp.sqrt(3),
            1 / sp.sqrt(6),
        ]
    )

    xi = sp.Matrix([0, 1, 1, 0])
    v = x

    # Orthogonality to span{x, Ax, A* x}.
    orth_x = sp.simplify((xi.T * x)[0])
    orth_Ax = sp.simplify((xi.T * (A * x))[0])
    orth_Astarx = sp.simplify((xi.T * (A.T * x))[0])

    # Degree-3 monomial: c_{02}=c_{11}=c_{20}=1 and all others zero for j,k in {0,1,2}.
    cjk = {
        (0, 2): 1,
        (1, 1): 1,
        (2, 0): 1,
    }

    a_pow_x = [x, A * x, A * A * x]
    a_pow_v = [v, A * v, A * A * v]

    deriv = 0
    for j in range(3):
        for k in range(3):
            c = cjk.get((j, k), 0)
            if c == 0:
                continue
            deriv += c * (x.T * a_pow_v[j])[0] * (xi.T * a_pow_x[k])[0]

    deriv = sp.simplify(sp.re(deriv))

    print("alpha =", alpha)
    print("orthogonality checks:")
    print("  xi^* x      =", orth_x)
    print("  xi^* A x    =", orth_Ax)
    print("  xi^* A* x   =", orth_Astarx)
    print("")
    print("multilinear derivative term:")
    print("  Re sum_{j,k} c_jk (x^* A^j v)(xi^* A^k x) =", deriv)
    print("  numeric value =", sp.N(deriv, 30))

    if orth_x == 0 and orth_Ax == 0 and orth_Astarx == 0 and sp.simplify(deriv) != 0:
        print("")
        print("Result: nonzero first variation with xi ⟂ span{x, Ax, A* x}.")
        print("This refutes the strong pointwise MO wording in this model.")
    else:
        print("")
        print("Result: conditions not met; no refutation from this data.")


if __name__ == "__main__":
    main()
