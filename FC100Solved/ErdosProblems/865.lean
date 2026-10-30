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
  intro A hA hcard
  classical
  by_contra hno
  have hAne : A.Nonempty := by
    apply Finset.card_pos.mp
    omega
  let m := A.max' hAne
  have hmA : m ∈ A := Finset.max'_mem A hAne
  have hmle : m ≤ 2 * N := (Finset.mem_Icc.mp (hA hmA)).2
  let B := A.erase m
  have hBcard : N + 1 ≤ B.card := by
    have he : (A.erase m).card + 1 = A.card := Finset.card_erase_add_one hmA
    change N + 1 ≤ (A.erase m).card
    omega
  let f : ℕ → ℕ := fun x => if x ≤ m / 2 then x else m - x
  have himagesub : B.image f ⊆ Icc 1 (m / 2) := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    have hxdata : x ≠ m ∧ x ∈ A := Finset.mem_erase.mp hx
    have hxIcc := hA hxdata.2
    have hxone : 1 ≤ x := (Finset.mem_Icc.mp hxIcc).1
    have hxle : x ≤ m := Finset.le_max' A x hxdata.2
    have hxlt : x < m := by omega
    by_cases hxhalf : x ≤ m / 2
    · simp only [f, if_pos hxhalf]
      exact Finset.mem_Icc.mpr ⟨hxone, hxhalf⟩
    · simp only [f, if_neg hxhalf]
      apply Finset.mem_Icc.mpr
      constructor <;> omega
  have himagecard : (B.image f).card = B.card := by
    apply Finset.card_image_iff.mpr
    intro x hx y hy hxy
    have hxdata : x ≠ m ∧ x ∈ A := Finset.mem_erase.mp hx
    have hydata : y ≠ m ∧ y ∈ A := Finset.mem_erase.mp hy
    have hxle : x ≤ m := Finset.le_max' A x hxdata.2
    have hyle : y ≤ m := Finset.le_max' A y hydata.2
    by_cases hxhalf : x ≤ m / 2
    · by_cases hyhalf : y ≤ m / 2
      · simpa only [f, if_pos hxhalf, if_pos hyhalf] using hxy
      · have hcomp : x = m - y := by
          simpa only [f, if_pos hxhalf, if_neg hyhalf] using hxy
        by_contra hne
        have hsum : x + y = m := by omega
        exact hno ⟨x, hxdata.2, y, hydata.2, hne, by simpa only [hsum] using hmA⟩
    · by_cases hyhalf : y ≤ m / 2
      · have hcomp : m - x = y := by
          simpa only [f, if_neg hxhalf, if_pos hyhalf] using hxy
        by_contra hne
        have hsum : x + y = m := by omega
        exact hno ⟨x, hxdata.2, y, hydata.2, hne, by simpa only [hsum] using hmA⟩
      · simp only [f, if_neg hxhalf, if_neg hyhalf] at hxy
        omega
  have hc : B.card ≤ m / 2 := by
    calc
      B.card = (B.image f).card := himagecard.symm
      _ ≤ (Icc 1 (m / 2)).card := Finset.card_le_card himagesub
      _ = m / 2 := by simp
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
