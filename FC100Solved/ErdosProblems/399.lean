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
  intro hcop hprod heq
  have hn : 4 ≤ n := by
    by_contra hn
    have hnle : n ≤ 3 := by omega
    have hsum : x ^ 4 + y ^ 4 ≤ 6 := by
      interval_cases n <;> norm_num [Nat.factorial] at heq ⊢ <;> omega
    have hxlt : x < 2 := by
      by_contra hxlt
      have hxge : 2 ≤ x := by omega
      have hxpow : 2 ^ 4 ≤ x ^ 4 := by gcongr
      norm_num at hxpow
      omega
    have hylt : y < 2 := by
      by_contra hylt
      have hyge : 2 ≤ y := by omega
      have hypow : 2 ^ 4 ≤ y ^ 4 := by gcongr
      norm_num at hypow
      omega
    interval_cases x <;> interval_cases y <;> norm_num at hprod
  have hdiv : 8 ∣ n ! :=
    dvd_trans (by norm_num [Nat.factorial] : 8 ∣ 4 !) (Nat.factorial_dvd_factorial hn)
  have hmod : (x ^ 4 + y ^ 4) % 8 = 0 := by
    rw [← heq]
    exact Nat.dvd_iff_mod_eq_zero.mp hdiv
  have hnotboth : ¬ (x % 2 = 0 ∧ y % 2 = 0) := by
    rintro ⟨hx, hy⟩
    have hdx : 2 ∣ x := Nat.dvd_iff_mod_eq_zero.mpr hx
    have hdy : 2 ∣ y := Nat.dvd_iff_mod_eq_zero.mpr hy
    have hdg : 2 ∣ Nat.gcd x y := Nat.dvd_gcd hdx hdy
    have hgcd : Nat.gcd x y = 1 := hcop
    rw [hgcd] at hdg
    norm_num at hdg
  have hfourth (z : ℕ) :
      (z % 2 = 0 ∧ z ^ 4 % 8 = 0) ∨ (z % 2 = 1 ∧ z ^ 4 % 8 = 1) := by
    have hzlt : z % 8 < 8 := Nat.mod_lt z (by norm_num)
    interval_cases hz : z % 8 <;> norm_num [Nat.pow_mod, hz] <;> omega
  rcases hfourth x with hx | hx <;> rcases hfourth y with hy | hy <;> omega

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
