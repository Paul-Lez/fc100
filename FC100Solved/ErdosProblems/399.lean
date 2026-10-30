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
  -- Coprime x y implies they are not both even
  have h_not_both_even : ¬ (2 ∣ x ∧ 2 ∣ y) := by
    intro ⟨hx2, hy2⟩
    have hgcd1 : Nat.gcd x y = 1 := Nat.Coprime.gcd_eq_one hcop
    have h2gcd : 2 ∣ Nat.gcd x y := Nat.dvd_gcd hx2 hy2
    rw [hgcd1] at h2gcd
    have : ¬ 2 ∣ (1 : ℕ) := by decide
    exact this h2gcd
  -- For n < 4, n! ≤ 6, but x^4 + y^4 > 6
  by_cases hn : n < 4
  · have h_bound : 6 < x ^ 4 + y ^ 4 := by
      have hx_pos : 0 < x := by
        by_contra! hx0
        have hx0' : x = 0 := by omega
        subst hx0'
        have : 1 < 0 := by simpa using hxy
        omega
      have hy_pos : 0 < y := by
        by_contra! hy0
        have hy0' : y = 0 := by omega
        subst hy0'
        have : 1 < 0 := by simpa using hxy
        omega
      have h_one_ge_2 : 2 ≤ x ∨ 2 ≤ y := by
        by_contra! h
        rcases h with ⟨hx2, hy2⟩
        have hx1 : x = 1 := by omega
        have hy1 : y = 1 := by omega
        subst hx1; subst hy1
        omega
      rcases h_one_ge_2 with (hx2 | hy2)
      · have hx4 : 16 ≤ x ^ 4 := by
          have : 2 ^ 4 = 16 := by norm_num
          have hx_pow : 2 ^ 4 ≤ x ^ 4 := Nat.pow_le_pow_left hx2 4
          rw [this] at hx_pow
          exact hx_pow
        have hy4 : 0 ≤ y ^ 4 := Nat.zero_le _
        omega
      · have hy4 : 16 ≤ y ^ 4 := by
          have : 2 ^ 4 = 16 := by norm_num
          have hy_pow : 2 ^ 4 ≤ y ^ 4 := Nat.pow_le_pow_left hy2 4
          rw [this] at hy_pow
          exact hy_pow
        have hx4 : 0 ≤ x ^ 4 := Nat.zero_le _
        omega
    have hn' : n ≤ 3 := by omega
    interval_cases n
    · have h0 : (0 : ℕ)! = 1 := by decide
      rw [h0] at heq; omega
    · have h1 : (1 : ℕ)! = 1 := by decide
      rw [h1] at heq; omega
    · have h2 : (2 : ℕ)! = 2 := by decide
      rw [h2] at heq; omega
    · have h3 : (3 : ℕ)! = 6 := by decide
      rw [h3] at heq; omega
  · -- n ≥ 4
    have hn4 : 4 ≤ n := by omega
    have h8fact : 8 ∣ n ! := by
      have h8_4fact : 8 ∣ (4 : ℕ)! := by decide
      have h4fact_dvd : (4 : ℕ)! ∣ n ! := Nat.factorial_dvd_factorial hn4
      exact Nat.dvd_trans h8_4fact h4fact_dvd
    have h8sum : 8 ∣ x ^ 4 + y ^ 4 := by
      rw [← heq]
      exact h8fact
    -- Now we have 8 ∣ x^4 + y^4. We'll derive a contradiction using mod 8.
    -- First, reduce x^4 and y^4 modulo 8 using the fact that a^4 ≡ (a%8)^4 [MOD 8]
    have hx_mod8 : x ^ 4 ≡ (x % 8) ^ 4 [MOD 8] := by
      have hx : x ≡ x % 8 [MOD 8] := by
        rw [Nat.ModEq, Nat.mod_mod]
      exact hx.pow 4
    have hy_mod8 : y ^ 4 ≡ (y % 8) ^ 4 [MOD 8] := by
      have hy : y ≡ y % 8 [MOD 8] := by
        rw [Nat.ModEq, Nat.mod_mod]
      exact hy.pow 4
    have hsum_mod8 : x ^ 4 + y ^ 4 ≡ (x % 8) ^ 4 + (y % 8) ^ 4 [MOD 8] :=
      hx_mod8.add hy_mod8
    have h8_dvd_sum : x ^ 4 + y ^ 4 ≡ 0 [MOD 8] := by
      rw [Nat.ModEq]
      exact Nat.mod_eq_zero_of_dvd h8sum
    -- So (x%8)^4 + (y%8)^4 ≡ 0 [MOD 8]
    have h_residue : (x % 8) ^ 4 + (y % 8) ^ 4 ≡ 0 [MOD 8] :=
      hsum_mod8.symm.trans h8_dvd_sum
    -- Brute-force check all 64 possible residues (0..7 for each)
    -- For a,b < 8, if a^4+b^4 ≡ 0 [MOD 8] then both a and b are even
    have h_cases : ∀ a ∈ Finset.range 8, ∀ b ∈ Finset.range 8,
        (a ^ 4 + b ^ 4) % 8 = 0 → (a % 2 = 0 ∧ b % 2 = 0) := by
      decide
    have hx8_mem : x % 8 ∈ Finset.range 8 := by
      apply Finset.mem_range.mpr
      exact Nat.mod_lt x (by norm_num)
    have hy8_mem : y % 8 ∈ Finset.range 8 := by
      apply Finset.mem_range.mpr
      exact Nat.mod_lt y (by norm_num)
    have h_mod8_zero : ((x % 8) ^ 4 + (y % 8) ^ 4) % 8 = 0 := by
      rw [Nat.ModEq] at h_residue
      exact h_residue
    have h_both_even_mod8 := h_cases (x % 8) hx8_mem (y % 8) hy8_mem h_mod8_zero
    rcases h_both_even_mod8 with ⟨hx_even_mod8, hy_even_mod8⟩
    -- From (x%8) % 2 = 0, deduce 2 ∣ x (since x % 2 = (x%8) % 2)
    have hx2 : 2 ∣ x := by
      have hx_mod2_eq : x % 2 = (x % 8) % 2 := by
        rw [Nat.mod_mod_of_dvd x (by norm_num : 2 ∣ 8)]
      have hx_mod2_zero : x % 2 = 0 := by
        rw [hx_mod2_eq, hx_even_mod8]
      exact Nat.dvd_of_mod_eq_zero hx_mod2_zero
    have hy2 : 2 ∣ y := by
      have hy_mod2_eq : y % 2 = (y % 8) % 2 := by
        rw [Nat.mod_mod_of_dvd y (by norm_num : 2 ∣ 8)]
      have hy_mod2_zero : y % 2 = 0 := by
        rw [hy_mod2_eq, hy_even_mod8]
      exact Nat.dvd_of_mod_eq_zero hy_mod2_zero
    exact h_not_both_even ⟨hx2, hy2⟩

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
