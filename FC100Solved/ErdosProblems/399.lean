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
  have hxpos : 0 < x := by
    by_contra hx
    have hx0 : x = 0 := by omega
    simp [hx0] at hxy
  have hypos : 0 < y := by
    by_contra hy
    have hy0 : y = 0 := by omega
    simp [hy0] at hxy
  have hor : 2 ≤ x ∨ 2 ≤ y := by
    by_contra h
    push_neg at h
    have hxone : x = 1 := by omega
    have hyone : y = 1 := by omega
    norm_num [hxone, hyone] at hxy
  have hsum : 17 ≤ x ^ 4 + y ^ 4 := by
    rcases hor with hx | hy
    · have hxx : 4 ≤ x * x := Nat.mul_le_mul hx hx
      have hxxxx : 4 * 4 ≤ (x * x) * (x * x) := Nat.mul_le_mul hxx hxx
      have hxpow : 16 ≤ x ^ 4 := by
        norm_num at hxxxx
        convert hxxxx using 1 <;> ring
      have hypow : 0 < y ^ 4 := pow_pos hypos _
      omega
    · have hyy : 4 ≤ y * y := Nat.mul_le_mul hy hy
      have hyyyy : 4 * 4 ≤ (y * y) * (y * y) := Nat.mul_le_mul hyy hyy
      have hypow : 16 ≤ y ^ 4 := by
        norm_num at hyyyy
        convert hyyyy using 1 <;> ring
      have hxpow : 0 < x ^ 4 := pow_pos hxpos _
      omega
  by_cases hn : n < 4
  · interval_cases n <;> norm_num at heq <;> omega
  · have hn4 : 4 ≤ n := by omega
    have hfac : 4 ! ∣ n ! := Nat.factorial_dvd_factorial hn4
    have hdvd : 8 ∣ n ! := dvd_trans (by norm_num) hfac
    have hpow (z : ℕ) :
        (Even z ∧ ∃ q, z ^ 4 = 8 * q) ∨ (Odd z ∧ ∃ q, z ^ 4 = 8 * q + 1) := by
      rcases Nat.even_or_odd z with hz | hz
      · rcases hz with ⟨a, ha⟩
        left
        refine ⟨⟨a, ha⟩, 2 * a ^ 4, ?_⟩
        rw [ha]
        ring
      · rcases hz with ⟨a, ha⟩
        right
        refine ⟨⟨a, ha⟩, 2 * a ^ 4 + 4 * a ^ 3 + 3 * a ^ 2 + a, ?_⟩
        rw [ha]
        ring
    obtain ⟨t, ht⟩ := hdvd
    rcases hpow x with hx | hx
    · rcases hpow y with hy | hy
      · rcases hx with ⟨hx, qx, hqx⟩
        rcases hy with ⟨hy, qy, hqy⟩
        rcases hx with ⟨a, ha⟩
        rcases hy with ⟨b, hb⟩
        have hdx : 2 ∣ x := by
          refine ⟨a, ?_⟩
          omega
        have hdy : 2 ∣ y := by
          refine ⟨b, ?_⟩
          omega
        have htwo : 2 ∣ Nat.gcd x y := Nat.dvd_gcd hdx hdy
        rw [hcop] at htwo
        norm_num at htwo
      · rcases hx with ⟨_, qx, hqx⟩
        rcases hy with ⟨_, qy, hqy⟩
        omega
    · rcases hpow y with hy | hy
      · rcases hx with ⟨_, qx, hqx⟩
        rcases hy with ⟨_, qy, hqy⟩
        omega
      · rcases hx with ⟨_, qx, hqx⟩
        rcases hy with ⟨_, qy, hqy⟩
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
