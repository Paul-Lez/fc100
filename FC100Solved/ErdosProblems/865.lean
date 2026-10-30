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
# Erdős Problem 865

*References:*
- [erdosproblems.com/865](https://www.erdosproblems.com/865)
- [CES75] Choi, S. L. G. and Erdős, P. and Szemerédi, E., Some additive and multiplicative problems
  in number theory. Acta Arith. (1975), 37--50.
-/

open Finset Filter
open scoped Asymptotics

namespace Erdos865

/--
There exists a constant $C>0$ such that, for all large $N$, if $A\subseteq \{1,\ldots,N\}$ has
size at least $\frac{5}{8}N+C$ then there are distinct $a,b,c\in A$ such that $a+b,a+c,b+c\in A$.

A problem of Erdős and Sós (also earlier considered by Choi, Erdős, and Szemerédi [CES75], but Erdős
had forgotten this).
-/
@[category research open, AMS 5 11]
theorem erdos_865 :
    ∃ C > 0, ∀ᶠ (N : ℕ) in atTop,
      ∀ A ⊆ Icc 1 N, A.card ≥ (5 / 8 : ℝ) * N + C →
      ∃ a ∈ A, ∃ b ∈ A, ∃ c ∈ A, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      a + b ∈ A ∧ a + c ∈ A ∧ b + c ∈ A := by
  sorry

/--
It is a classical folklore fact that if $A\subseteq \{1,\ldots,2N\}$ has size $\geq N+2$ then
there are distinct $a,b\in A$ such that $a+b\in A$, which establishes the $k=2$ case.
-/
@[category research solved, AMS 5 11]
theorem erdos_865.variants.k2 (N : ℕ) :
    ∀ A ⊆ Icc 1 (2 * N), A.card ≥ N + 2 →
    ∃ a ∈ A, ∃ b ∈ A, a ≠ b ∧ a + b ∈ A := by
  -- Agent proof
  intro A hsub hcard
  have hcardpos : 0 < A.card := by omega
  have hA : A.Nonempty := Finset.card_pos.mp hcardpos
  let c := A.max' hA
  have hcA : c ∈ A := by
    simpa [c] using Finset.max'_mem A hA
  have hc_bound : c ≤ 2 * N := (Finset.mem_Icc.mp (hsub hcA)).2
  by_contra hno
  have hsum : ∀ {x y : ℕ}, x ∈ A → y ∈ A → x ≠ y → x + y ∉ A := by
    intro x y hx hy hxy hmem
    exact hno ⟨x, hx, y, hy, hxy, hmem⟩
  let f : ℕ → ℕ := fun x => if x = c then 0 else min x (c - x)
  have hf_lt : ∀ x ∈ A, f x < c / 2 + 1 := by
    intro x hx
    have hxle : x ≤ c := by
      simpa [c] using Finset.le_max' A x hx
    by_cases hxc : x = c
    · simp [f, hxc]
    · have hmin : min x (c - x) ≤ c / 2 := by
        by_cases hxhalf : x ≤ c / 2
        · exact (min_le_left x (c - x)).trans hxhalf
        · have hsubhalf : c - x ≤ c / 2 := by omega
          exact (min_le_right x (c - x)).trans hsubhalf
      simp only [f, hxc, if_false]
      omega
  have hf_inj : Set.InjOn f (↑A : Set ℕ) := by
    intro x hx y hy hxy
    have hxA : x ∈ A := by simpa using hx
    have hyA : y ∈ A := by simpa using hy
    have hxone : 1 ≤ x := (Finset.mem_Icc.mp (hsub hxA)).1
    have hyone : 1 ≤ y := (Finset.mem_Icc.mp (hsub hyA)).1
    have hxle : x ≤ c := by
      simpa [c] using Finset.le_max' A x hxA
    have hyle : y ≤ c := by
      simpa [c] using Finset.le_max' A y hyA
    by_cases hxc : x = c
    · subst x
      by_cases hyc : y = c
      · subst y
        rfl
      · have hylt : y < c := by omega
        have hz : 0 = min y (c - y) := by
          simpa [f, hyc] using hxy
        by_cases hyl : y ≤ c - y
        · rw [min_eq_left hyl] at hz
          omega
        · have hyr : c - y ≤ y := by omega
          rw [min_eq_right hyr] at hz
          omega
    · by_cases hyc : y = c
      · subst y
        have hxlt : x < c := by omega
        have hz : min x (c - x) = 0 := by
          simpa [f, hxc] using hxy
        by_cases hxl : x ≤ c - x
        · rw [min_eq_left hxl] at hz
          omega
        · have hxr : c - x ≤ x := by omega
          rw [min_eq_right hxr] at hz
          omega
      · have hmin : min x (c - x) = min y (c - y) := by
          simpa [f, hxc, hyc] using hxy
        by_cases hxl : x ≤ c - x
        · rw [min_eq_left hxl] at hmin
          by_cases hyl : y ≤ c - y
          · rw [min_eq_left hyl] at hmin
            exact hmin
          · have hyr : c - y ≤ y := by omega
            rw [min_eq_right hyr] at hmin
            by_contra hne
            apply hsum hxA hyA hne
            have hsumc : x + y = c := by omega
            simpa only [hsumc] using hcA
        · have hxr : c - x ≤ x := by omega
          rw [min_eq_right hxr] at hmin
          by_cases hyl : y ≤ c - y
          · rw [min_eq_left hyl] at hmin
            by_contra hne
            apply hsum hxA hyA hne
            have hsumc : x + y = c := by omega
            simpa only [hsumc] using hcA
          · have hyr : c - y ≤ y := by omega
            rw [min_eq_right hyr] at hmin
            omega
  have hcard_image : (A.image f).card = A.card :=
    Finset.card_image_iff.mpr hf_inj
  have himage : A.image f ⊆ range (c / 2 + 1) := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨x, hx, rfl⟩
    exact Finset.mem_range.mpr (hf_lt x hx)
  have hupper : A.card ≤ c / 2 + 1 := by
    calc
      A.card = (A.image f).card := hcard_image.symm
      _ ≤ (range (c / 2 + 1)).card := Finset.card_le_card himage
      _ = c / 2 + 1 := Finset.card_range _
  omega

noncomputable def f (N k : ℕ) : ℕ :=
  sInf {m | ∀ A ⊆ Icc 1 N, A.card ≥ m →
    ∃ S ⊆ A, S.card = k ∧ ∀ x ∈ S, ∀ y ∈ S, x ≠ y → x + y ∈ A}

/--
Erdős and Sós conjectured that
$f_k(N)\sim \frac{1}{2}\left(1+\sum_{1\leq r\leq k-2}\frac{1}{4^r}\right) N$,
where $f_k(N)$ is the minimal size of a subset of $\{1, \dots, N\}$ guaranteeing $k$ elements
have all pairwise sums in the set.
-/
@[category research open, AMS 5 11]
theorem erdos_865.variants.sos :
    ∀ᵉ (k : ℕ) (hk : 2 ≤ k),
    (fun N ↦ (f N k : ℝ)) ~[atTop] (fun N ↦ (1 / 2 : ℝ) * (1 + ∑ r ∈ Icc 1 (k - 2),
      (1 / 4 : ℝ) ^ r) * N) := by
  sorry

/--
Choi, Erdős, and Szemerédi [CES75] have proved that, for all $k\geq 3$, there exists $\epsilon_k>0$
such that (for large enough $N$) $f_k(N)\leq \left(\frac{2}{3}-\epsilon_k\right)N$.
-/
@[category research solved, AMS 5 11]
theorem erdos_865.variants.upper_bound (k : ℕ) (hk : 3 ≤ k) :
    ∃ ε > 0, ∀ᶠ N in atTop, (f N k : ℝ) ≤ (2 / 3 - ε) * N := by
  sorry

end Erdos865
