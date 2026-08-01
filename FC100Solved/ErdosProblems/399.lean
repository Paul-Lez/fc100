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
  have hx0 : x ≠ 0 := by rintro rfl; omega
  have hy0 : y ≠ 0 := by rintro rfl; omega
  have hx1 : 1 ≤ x := Nat.one_le_iff_ne_zero.mpr hx0
  have hy1 : 1 ≤ y := Nat.one_le_iff_ne_zero.mpr hy0
  have hgcd : Nat.gcd x y = 1 := hcop
  have hne : ¬ (x % 2 = 0 ∧ y % 2 = 0) := by
    rintro ⟨hx2, hy2⟩
    have hdx : (2:ℕ) ∣ x := Nat.dvd_of_mod_eq_zero hx2
    have hdy : (2:ℕ) ∣ y := Nat.dvd_of_mod_eq_zero hy2
    have h2 : (2:ℕ) ∣ Nat.gcd x y := Nat.dvd_gcd hdx hdy
    rw [hgcd] at h2
    norm_num at h2
  by_cases hn : 4 ≤ n
  · have key : ∀ a : ℕ, a < 8 → a ^ 4 % 8 = a % 2 := by decide
    have hmodx : x ^ 4 % 8 = x % 2 := by
      have h8 : x ^ 4 % 8 = (x % 8) ^ 4 % 8 := by rw [Nat.pow_mod]
      have hlt : x % 8 < 8 := Nat.mod_lt x (by norm_num)
      have hk := key (x % 8) hlt
      omega
    have hmody : y ^ 4 % 8 = y % 2 := by
      have h8 : y ^ 4 % 8 = (y % 8) ^ 4 % 8 := by rw [Nat.pow_mod]
      have hlt : y % 8 < 8 := Nat.mod_lt y (by norm_num)
      have hk := key (y % 8) hlt
      omega
    have h4fac : Nat.factorial 4 ∣ n ! := Nat.factorial_dvd_factorial hn
    have h8dvd : (8:ℕ) ∣ n ! := dvd_trans (by decide : (8:ℕ) ∣ Nat.factorial 4) h4fac
    have hn8 : n ! % 8 = 0 := by
      obtain ⟨k, hk⟩ := h8dvd
      rw [hk]
      exact Nat.mul_mod_right 8 k
    rw [heq] at hn8
    have hfin : x % 2 = 0 ∧ y % 2 = 0 := by omega
    exact hne hfin
  · push_neg at hn
    have hn3 : n ≤ 3 := by omega
    have hn6 : n ! ≤ 6 := by
      calc n ! ≤ 3 ! := Nat.factorial_le hn3
      _ = 6 := by decide
    have hxb : x < 2 := by
      by_contra hcx
      push_neg at hcx
      have hx16 : (16:ℕ) ≤ x ^ 4 := by
        calc (16:ℕ) = 2 ^ 4 := by norm_num
        _ ≤ x ^ 4 := Nat.pow_le_pow_left hcx 4
      omega
    have hyb : y < 2 := by
      by_contra hcy
      push_neg at hcy
      have hy16 : (16:ℕ) ≤ y ^ 4 := by
        calc (16:ℕ) = 2 ^ 4 := by norm_num
        _ ≤ y ^ 4 := Nat.pow_le_pow_left hcy 4
      omega
    have hxeq1 : x = 1 := by omega
    have hyeq1 : y = 1 := by omega
    rw [hxeq1, hyeq1] at hxy
    omega

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
