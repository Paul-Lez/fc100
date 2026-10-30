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
  intro hcop hprod
  have hpowmod : ∀ z : ℕ, z ^ 4 % 8 = 0 ∨ z ^ 4 % 8 = 1 := by
    intro z
    have hzlt : z % 8 < 8 := Nat.mod_lt _ (by norm_num)
    interval_cases h : z % 8 <;> norm_num [Nat.pow_mod, h]
  have hzero_even : ∀ z : ℕ, z ^ 4 % 8 = 0 → z % 2 = 0 := by
    intro z hz
    have hzlt : z % 8 < 8 := Nat.mod_lt _ (by norm_num)
    interval_cases h : z % 8 <;> norm_num [Nat.pow_mod, h] at hz <;> omega
  have hsumcases : (x ^ 4 + y ^ 4) % 8 = 1 ∨ (x ^ 4 + y ^ 4) % 8 = 2 := by
    rcases hpowmod x with hx | hx <;> rcases hpowmod y with hy | hy
    · have hx2 : x % 2 = 0 := hzero_even x hx
      have hy2 : y % 2 = 0 := hzero_even y hy
      have hdx : 2 ∣ x := Nat.dvd_of_mod_eq_zero hx2
      have hdy : 2 ∣ y := Nat.dvd_of_mod_eq_zero hy2
      have hd : 2 ∣ Nat.gcd x y := Nat.dvd_gcd hdx hdy
      have hg : Nat.gcd x y = 1 := hcop
      rw [hg] at hd
      norm_num at hd
    · left
      norm_num [Nat.add_mod, hx, hy]
    · left
      norm_num [Nat.add_mod, hx, hy]
    · right
      norm_num [Nat.add_mod, hx, hy]
  have hxpos : 0 < x := by
    by_contra hx
    have hx0 : x = 0 := by omega
    subst x
    simp at hprod
  have hypos : 0 < y := by
    by_contra hy
    have hy0 : y = 0 := by omega
    subst y
    simp at hprod
  have hxpowpos : 0 < x ^ 4 := pow_pos hxpos _
  have hypowpos : 0 < y ^ 4 := pow_pos hypos _
  by_cases hn : n < 8
  · have hnle : n ≤ 7 := by omega
    interval_cases n
    · intro heq
      norm_num [Nat.factorial] at heq
      omega
    · intro heq
      norm_num [Nat.factorial] at heq
      omega
    · intro heq
      norm_num [Nat.factorial] at heq
      have hxp : x ^ 4 = 1 := by omega
      have hyp : y ^ 4 = 1 := by omega
      have hxdiv : x ∣ x ^ 4 := by
        refine ⟨x ^ 3, ?_⟩
        ring
      have hydiv : y ∣ y ^ 4 := by
        refine ⟨y ^ 3, ?_⟩
        ring
      rw [hxp] at hxdiv
      rw [hyp] at hydiv
      have hxone : x = 1 := Nat.dvd_one.mp hxdiv
      have hyone : y = 1 := Nat.dvd_one.mp hydiv
      subst x
      subst y
      norm_num at hprod
    · intro heq
      have hm := congrArg (fun z : ℕ => z % 8) heq
      norm_num [Nat.factorial] at hm
      rcases hsumcases with hs | hs <;> omega
    · intro heq
      have hm := congrArg (fun z : ℕ => z % 8) heq
      norm_num [Nat.factorial] at hm
      rcases hsumcases with hs | hs <;> omega
    · intro heq
      have hm := congrArg (fun z : ℕ => z % 8) heq
      norm_num [Nat.factorial] at hm
      rcases hsumcases with hs | hs <;> omega
    · intro heq
      have hm := congrArg (fun z : ℕ => z % 8) heq
      norm_num [Nat.factorial] at hm
      rcases hsumcases with hs | hs <;> omega
    · intro heq
      have hm := congrArg (fun z : ℕ => z % 8) heq
      norm_num [Nat.factorial] at hm
      rcases hsumcases with hs | hs <;> omega
  · have hn8 : 8 ≤ n := by omega
    have h8 : 8 ∣ n ! := by
      apply Nat.dvd_factorial <;> omega
    intro heq
    obtain ⟨k, hk⟩ := h8
    have hm := congrArg (fun z : ℕ => z % 8) heq
    rw [hk] at hm
    norm_num [Nat.mul_mod] at hm
    rcases hsumcases with hs | hs <;> omega

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
