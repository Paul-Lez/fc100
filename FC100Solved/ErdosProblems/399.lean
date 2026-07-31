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
  intro hcop hprod h
  have hxmod : x ^ 4 % 8 = 0 ∨ x ^ 4 % 8 = 1 := by
    have hxlt : x % 8 < 8 := Nat.mod_lt _ (by norm_num)
    interval_cases hx : x % 8 <;> norm_num [Nat.pow_mod, hx]
  have hymod : y ^ 4 % 8 = 0 ∨ y ^ 4 % 8 = 1 := by
    have hylt : y % 8 < 8 := Nat.mod_lt _ (by norm_num)
    interval_cases hy : y % 8 <;> norm_num [Nat.pow_mod, hy]
  have hnot : ¬ (x ^ 4 % 8 = 0 ∧ y ^ 4 % 8 = 0) := by
    rintro ⟨hx, hy⟩
    have hx8 : 8 ∣ x ^ 4 := (Nat.dvd_iff_mod_eq_zero).2 hx
    have hy8 : 8 ∣ y ^ 4 := (Nat.dvd_iff_mod_eq_zero).2 hy
    have hx2 : 2 ∣ x ^ 4 := dvd_trans (by norm_num) hx8
    have hy2 : 2 ∣ y ^ 4 := dvd_trans (by norm_num) hy8
    have hxdvd : 2 ∣ x := (by norm_num : Nat.Prime 2).dvd_of_dvd_pow hx2
    have hydvd : 2 ∣ y := (by norm_num : Nat.Prime 2).dvd_of_dvd_pow hy2
    have htwo : 2 ∣ Nat.gcd x y := Nat.dvd_gcd hxdvd hydvd
    have hgcd : Nat.gcd x y = 1 := hcop
    norm_num [hgcd] at htwo
  have hnlt : n < 4 := by
    by_contra hnlt
    have hn4 : 4 ≤ n := by omega
    have hfac : 8 ∣ n ! := dvd_trans (by norm_num) (Nat.factorial_dvd_factorial hn4)
    have hmod : n ! % 8 = (x ^ 4 + y ^ 4) % 8 := congrArg (fun z : ℕ => z % 8) h
    have hzero : n ! % 8 = 0 := Nat.mod_eq_zero_of_dvd hfac
    rw [hzero] at hmod
    rcases hxmod with hx | hx
    · rcases hymod with hy | hy
      · exact (hnot ⟨hx, hy⟩).elim
      · norm_num [Nat.add_mod, hx, hy] at hmod
    · rcases hymod with hy | hy
      · norm_num [Nat.add_mod, hx, hy] at hmod
      · norm_num [Nat.add_mod, hx, hy] at hmod
  interval_cases n <;> norm_num at h
  all_goals
    have hxle : x ≤ 1 := by
      by_contra hxle
      have hx2 : 2 ≤ x := by omega
      have hx16 : 16 ≤ x ^ 4 := by
        calc
          16 = 2 ^ 4 := by norm_num
          _ ≤ x ^ 4 := by gcongr
      omega
    have hyle : y ≤ 1 := by
      by_contra hyle
      have hy2 : 2 ≤ y := by omega
      have hy16 : 16 ≤ y ^ 4 := by
        calc
          16 = 2 ^ 4 := by norm_num
          _ ≤ y ^ 4 := by gcongr
      omega
    interval_cases x <;> interval_cases y <;> norm_num at hprod

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
