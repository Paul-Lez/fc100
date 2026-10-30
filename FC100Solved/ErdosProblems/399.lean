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
  intro hcop hxy heq
  by_cases hn : n < 4
  · have hn_le : n ≤ 3 := by omega
    have hbound : x ^ 4 + y ^ 4 ≤ 6 := by
      rw [← heq]
      interval_cases n <;> norm_num
    have hxlt : x < 2 := by
      by_contra hx
      have hx2 : 2 ≤ x := by omega
      have hxpow : 16 ≤ x ^ 4 := by
        calc
          16 = (2 : ℕ) ^ 4 := by norm_num
          _ ≤ x ^ 4 := by gcongr
      omega
    have hylt : y < 2 := by
      by_contra hy
      have hy2 : 2 ≤ y := by omega
      have hypow : 16 ≤ y ^ 4 := by
        calc
          16 = (2 : ℕ) ^ 4 := by norm_num
          _ ≤ y ^ 4 := by gcongr
      omega
    interval_cases x <;> interval_cases y <;> norm_num at hxy
  · have hn4 : 4 ≤ n := by omega
    have hdiv : 8 ∣ n ! := by
      have h4div : 8 ∣ 4 ! := by norm_num
      exact dvd_trans h4div (Nat.factorial_dvd_factorial hn4)
    have hsum_mod : (x ^ 4 + y ^ 4) % 8 = 0 := by
      rw [← heq]
      exact Nat.dvd_iff_mod_eq_zero.mp hdiv
    have hpow (a : ℕ) : a ^ 4 % 8 = if a % 2 = 0 then 0 else 1 := by
      have ha : a % 8 < 8 := Nat.mod_lt _ (by norm_num)
      interval_cases h : a % 8 <;>
        by_cases hp : a % 2 = 0 <;>
          norm_num [hp, Nat.pow_succ, Nat.mul_mod, h] <;>
          omega
    have hx_even : x % 2 = 0 := by
      by_contra hx
      by_cases hy_even : y % 2 = 0
      · have h := hsum_mod
        simp [Nat.add_mod, hpow x, hpow y, hx, hy_even] at h
      · have h := hsum_mod
        simp [Nat.add_mod, hpow x, hpow y, hx, hy_even] at h
    have hy_even : y % 2 = 0 := by
      by_contra hy
      have h := hsum_mod
      simp [Nat.add_mod, hpow x, hpow y, hx_even, hy] at h
    have hdx : 2 ∣ x := (Nat.dvd_iff_mod_eq_zero).2 hx_even
    have hdy : 2 ∣ y := (Nat.dvd_iff_mod_eq_zero).2 hy_even
    have hdg : 2 ∣ Nat.gcd x y := Nat.dvd_gcd hdx hdy
    have hgcd : Nat.gcd x y = 1 := hcop
    rw [hgcd] at hdg
    norm_num at hdg

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
