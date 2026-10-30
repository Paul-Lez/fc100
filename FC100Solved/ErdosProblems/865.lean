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
  by_contra hex
  have hcardpos : 0 < A.card := by omega
  have hAne : A.Nonempty := Finset.card_pos.mp hcardpos
  let c := A.max' hAne
  have hcA : c ∈ A := by
    dsimp [c]
    exact Finset.max'_mem A hAne
  have hc_le : c ≤ 2 * N := (Finset.mem_Icc.mp (hsub hcA)).2
  let f : ℕ → ℕ := fun x ↦ min x (c - x)
  have hf_mem : ∀ x ∈ A.erase c, f x ∈ Icc 1 (c / 2) := by
    intro x hx
    rcases Finset.mem_erase.mp hx with ⟨hxc, hxA⟩
    have hxle : x ≤ c := by
      dsimp [c]
      exact Finset.le_max' A x hxA
    have hxlt : x < c := by omega
    have hxone : 1 ≤ x := (Finset.mem_Icc.mp (hsub hxA)).1
    have hxsubone : 1 ≤ c - x := by omega
    apply Finset.mem_Icc.mpr
    constructor
    · exact le_min hxone hxsubone
    · by_cases hxsmall : x ≤ c / 2
      · exact (min_le_left x (c - x)).trans hxsmall
      · have hsubsmall : c - x ≤ c / 2 := by omega
        exact (min_le_right x (c - x)).trans hsubsmall
  have hinj : Set.InjOn f ↑(A.erase c) := by
    intro x hx y hy hxy
    rcases Finset.mem_erase.mp hx with ⟨hxc, hxA⟩
    rcases Finset.mem_erase.mp hy with ⟨hyc, hyA⟩
    have hxle : x ≤ c := by
      dsimp [c]
      exact Finset.le_max' A x hxA
    have hyle : y ≤ c := by
      dsimp [c]
      exact Finset.le_max' A y hyA
    have hcases : x = y ∨ x + y = c := by
      dsimp [f] at hxy
      rcases le_total x (c - x) with hxsmall | hxlarge
      · rw [min_eq_left hxsmall] at hxy
        rcases le_total y (c - y) with hysmall | hylarge
        · rw [min_eq_left hysmall] at hxy
          exact Or.inl hxy
        · rw [min_eq_right hylarge] at hxy
          right
          omega
      · rw [min_eq_right hxlarge] at hxy
        rcases le_total y (c - y) with hysmall | hylarge
        · rw [min_eq_left hysmall] at hxy
          right
          omega
        · rw [min_eq_right hylarge] at hxy
          left
          omega
    rcases hcases with hxy | hsum
    · exact hxy
    · by_contra hne
      apply hex
      refine ⟨x, hxA, y, hyA, hne, ?_⟩
      rw [hsum]
      exact hcA
  have himage : (A.erase c).image f ⊆ Icc 1 (c / 2) := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨x, hx, rfl⟩
    exact hf_mem x hx
  have hcard_image : ((A.erase c).image f).card = (A.erase c).card :=
    Finset.card_image_iff.mpr hinj
  have hBupper : (A.erase c).card ≤ (Icc 1 (c / 2)).card := by
    calc
      (A.erase c).card = ((A.erase c).image f).card := hcard_image.symm
      _ ≤ (Icc 1 (c / 2)).card := Finset.card_le_card himage
  have hBupper' : (A.erase c).card ≤ c / 2 := by
    simpa [Nat.card_Icc] using hBupper
  have hcdiv : c / 2 ≤ N := by omega
  have hBlower : N + 1 ≤ (A.erase c).card := by
    rw [Finset.card_erase_of_mem hcA]
    omega
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
