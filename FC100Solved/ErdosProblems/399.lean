/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import FormalConjectures.Util.ProblemImports

/-!
# Erdős Problem 399

Is it true that there are no solutions to $n! = x^k \pm y^k$ with $x,y,n \in \mathbb{N}$,
with $xy > 1$ and $k > 2$?

*References:*
 - [erdosproblems.com/399](https://www.erdosproblems.com/399)
- [Br32] Breusch, Robert, Zur Verallgemeinerung des Bertrandschen Postulates, da\ss zwischen $x$
  und 2 $x$ stets Primzahlen liegen. Math. Z. (1932), 505--526.
- [ErOb37] Erdős, P. and Obláth, R., \"Über diophantische Gleichungen der Form $n!=x^p+y^p$ und
  $n!\pmd m!=x^p$. Acta Litt. ac Sci. Reg. Univ. Hung. Fr.-Jos., Sect. Sci. Math. (1937), 241-255.
- [Gu04] Guy, Richard K., Unsolved problems in number theory. (2004), xviii+437.
- [PoSh73] Pollack, Richard M. and Shapiro, Harold N., The next to last case of a factorial
  diophantine equation. Comm. Pure Appl. Math. (1973), 313-325.
-/

open Nat

namespace Erdos399

/--
Is it true that there are no solutions to `n! = x^k ± y^k` with `x,y,n ∈ ℕ`, `x*y > 1`, and
`k > 2`?

The answer is no: Jonas Barfield found the counterexample `10! = 48^4 - 36^4` (equivalently,
`10! + 36^4 = 48^4`).

This is discussed in problem D2 of Guy's collection [Gu04].

This was formalized in Lean by Lu using Codex.
-/
@[category research solved, AMS 11, formal_proof using lean4 at "https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/399.lean"]
theorem erdos_399 : answer(False) ↔
    ¬ ∃ (n x y k : ℕ), 1 < x * y ∧ 2 < k ∧ (n ! = x ^ k + y ^ k ∨ n ! + y ^ k = x ^ k) := by
  simp only [false_iff, Classical.not_not]
  exact ⟨10, 48, 36, 4, by decide⟩

/-- Erdős and Obláth [ErOb37] proved this is true when $(x,y)=1$ and $k\neq 4$. -/
@[category research solved, AMS 11]
theorem erdos_399.variants.erdos_oblath {n x y k : ℕ} :
    x.Coprime y → 1 < x * y → 2 < k → k ≠ 4 →
      n ! ≠ x ^ k + y ^ k ∧ n ! + y ^ k ≠ x ^ k := by
  sorry

/-- Pollack and Shapiro [PoSh73] proved there are no solutions to $n!=x^4-1$. -/
@[category research solved, AMS 11]
theorem erdos_399.variants.pollack_shapiro (n x : ℕ) : n ! + 1 ≠ x ^ 4 := by
  sorry

/--
Cambie has also observed that considerations modulo $8$ rule out any solutions to $n!=x^4+y^4$ with
$(x,y)=1$ and $xy>1$.
-/
@[category research solved, AMS 11]
theorem erdos_399.variants.cambie {n x y : ℕ} :
    x.Coprime y → 1 < x * y → n ! ≠ x ^ 4 + y ^ 4 := by
  -- Agent proof
  intro hcop hxy hEq
  by_cases hn : 4 ≤ n
  · have hfour : 4 ! ∣ n ! := Nat.factorial_dvd_factorial hn
    have h8four : 8 ∣ 4 ! := by norm_num [Nat.factorial]
    have h8fac : 8 ∣ n ! := dvd_trans h8four hfour
    rw [hEq] at h8fac
    have hmod : (x ^ 4 + y ^ 4) % 8 = 0 := Nat.dvd_iff_mod_eq_zero.mp h8fac
    have hnot : ¬ (2 ∣ x ∧ 2 ∣ y) := by
      rintro ⟨hx, hy⟩
      have htwo : 2 ∣ Nat.gcd x y := Nat.dvd_gcd hx hy
      have hgcd : Nat.gcd x y = 1 := hcop
      rw [hgcd] at htwo
      norm_num at htwo
    have hxlt : x % 8 < 8 := Nat.mod_lt _ (by norm_num)
    have hylt : y % 8 < 8 := Nat.mod_lt _ (by norm_num)
    interval_cases hx : x % 8 <;> interval_cases hy : y % 8 <;>
      norm_num [Nat.add_mod, Nat.pow_mod, hx, hy] at hmod
    all_goals
      apply hnot
      constructor <;> rw [Nat.dvd_iff_mod_eq_zero] <;> omega
  · have hnlt : n < 4 := by omega
    have hfac : n ! ≤ 6 := by
      interval_cases n <;> norm_num [Nat.factorial]
    have hxpow : x ^ 4 ≤ 6 := by omega
    have hypow : y ^ 4 ≤ 6 := by omega
    have hsmall (z : ℕ) (hz : z ^ 4 ≤ 6) : z < 2 := by
      by_contra hzlt
      have htwo : 2 ≤ z := by omega
      have hp : 2 ^ 4 ≤ z ^ 4 := by gcongr
      norm_num at hp
      omega
    have hxlt := hsmall x hxpow
    have hylt := hsmall y hypow
    interval_cases x <;> interval_cases y <;> norm_num at hxy

/--
Erdős and Obláth observed that the Bertrand-style fact (first proved by Breusch [Br32]) that, if
$q_i$ is the sequence of primes congruent to $3\pmod{4}$ then $q_{i+1}<2q_i$ except for $q_1=3$,
together with Fermat's theorem on the sums of two squares implies that the only solution to
$n!=x^2+y^2$ is $6!=12^2+24^2$.
-/
@[category research solved, AMS 11]
theorem erdos_399.variants.sum_two_squares :
    ∀ {n x y : ℕ}, 1 < x * y → n ! = x ^ 2 + y ^ 2 →
      n = 6 ∧ (x = 12 ∧ y = 24 ∨ x = 24 ∧ y = 12) := by
  sorry

end Erdos399
