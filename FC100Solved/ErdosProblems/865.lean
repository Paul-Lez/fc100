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
  classical
  intro A hsub hcard
  have hApos : 0 < A.card := by omega
  have hAne : A.Nonempty := Finset.card_pos.mp hApos
  let c := A.max' hAne
  have hcA : c ∈ A := by
    dsimp [c]
    exact Finset.max'_mem A hAne
  have hc_le : c ≤ 2 * N := (Finset.mem_Icc.mp (hsub hcA)).2
  let B := A.erase c
  have hBcard : B.card = A.card - 1 := by
    dsimp [B]
    exact Finset.card_erase_of_mem hcA
  have hBcard_gt : N < B.card := by omega
  let f : ℕ → ℕ := fun x ↦ min x (c - x)
  have hfmem : ∀ x ∈ B, f x ∈ Icc 1 N := by
    intro x hx
    have hxB : x ∈ A.erase c := by simpa [B] using hx
    have hxne : x ≠ c := (Finset.mem_erase.mp hxB).1
    have hxA : x ∈ A := (Finset.mem_erase.mp hxB).2
    have hxlo : 1 ≤ x := (Finset.mem_Icc.mp (hsub hxA)).1
    have hxc : x ≤ c := by
      dsimp [c]
      exact Finset.le_max' A x hxA
    have hxlt : x < c := by omega
    have hxcomp : x + (c - x) = c := by omega
    dsimp [f]
    rw [Finset.mem_Icc]
    by_cases hxside : x ≤ c - x
    · rw [min_eq_left hxside]
      constructor
      · exact hxlo
      · omega
    · have hxrev : c - x ≤ x := by omega
      rw [min_eq_right hxrev]
      constructor <;> omega
  have himage : B.image f ⊆ Icc 1 N := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    exact hfmem x hx
  have hTcard : (Icc 1 N).card = N := by simp
  have hcollision : ∃ x ∈ B, ∃ y ∈ B, x ≠ y ∧ f x = f y := by
    by_contra hn
    have hfinj : Set.InjOn f (↑B : Set ℕ) := by
      intro x hx y hy hxy
      by_contra hne
      apply hn
      refine ⟨x, ?_, y, ?_, hne, hxy⟩
      · simpa using hx
      · simpa using hy
    have himagecard : (B.image f).card = B.card :=
      Finset.card_image_iff.mpr hfinj
    have hle : B.card ≤ N := by
      rw [← himagecard, ← hTcard]
      exact Finset.card_le_card himage
    omega
  obtain ⟨x, hxB, y, hyB, hxy, hfxy⟩ := hcollision
  have hxB' : x ∈ A.erase c := by simpa [B] using hxB
  have hyB' : y ∈ A.erase c := by simpa [B] using hyB
  have hxA : x ∈ A := (Finset.mem_erase.mp hxB').2
  have hyA : y ∈ A := (Finset.mem_erase.mp hyB').2
  have hxc : x ≤ c := by
    dsimp [c]
    exact Finset.le_max' A x hxA
  have hyc : y ≤ c := by
    dsimp [c]
    exact Finset.le_max' A y hyA
  have hxcomp : x + (c - x) = c := by omega
  have hycomp : y + (c - y) = c := by omega
  dsimp [f] at hfxy
  have hsum : x + y = c := by
    by_cases hxside : x ≤ c - x
    · rw [min_eq_left hxside] at hfxy
      by_cases hyside : y ≤ c - y
      · rw [min_eq_left hyside] at hfxy
        omega
      · have hyrev : c - y ≤ y := by omega
        rw [min_eq_right hyrev] at hfxy
        omega
    · have hxrev : c - x ≤ x := by omega
      rw [min_eq_right hxrev] at hfxy
      by_cases hyside : y ≤ c - y
      · rw [min_eq_left hyside] at hfxy
        omega
      · have hyrev : c - y ≤ y := by omega
        rw [min_eq_right hyrev] at hfxy
        omega
  refine ⟨x, hxA, y, hyA, hxy, ?_⟩
  rw [hsum]
  exact hcA

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
