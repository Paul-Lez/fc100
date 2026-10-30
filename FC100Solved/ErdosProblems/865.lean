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
  have hcard_pos : 0 < A.card := by
    have : 0 < N + 2 := by omega
    omega
  have hA_nonempty : A.Nonempty := Finset.card_pos.mp hcard_pos
  let a_max := A.max' hA_nonempty
  have ha_max_mem : a_max ∈ A := Finset.max'_mem _ hA_nonempty
  have ha_max_mem_Icc : a_max ∈ Icc 1 (2 * N) := hA ha_max_mem
  have ha_max_le : a_max ≤ 2 * N := (Finset.mem_Icc.mp ha_max_mem_Icc).right
  -- A' = A \ {a_max}
  let A' := A.erase a_max
  have hA'_card : A'.card = A.card - 1 := by
    rw [Finset.card_erase_of_mem ha_max_mem]
  have hA'_card_ge : A'.card ≥ N + 1 := by
    rw [hA'_card]
    omega
  -- The set of differences B = {a_max - x | x ∈ A'}
  let B := A'.image (λ x => a_max - x)
  -- B ⊆ Icc 1 (2*N)
  have hB_subset : B ⊆ Icc 1 (2 * N) := by
    intro d hd
    rw [Finset.mem_image] at hd
    rcases hd with ⟨x, hx, rfl⟩
    have hx_mem_A : x ∈ A := Finset.mem_of_mem_erase hx
    have hx_Icc : x ∈ Icc 1 (2 * N) := hA hx_mem_A
    have hx_pos : 1 ≤ x := (Finset.mem_Icc.mp hx_Icc).left
    have hx_le_amax : x ≤ a_max := Finset.le_max' A x hx_mem_A
    have hx_lt_amax : x < a_max := by
      by_contra! hge
      have heq : x = a_max := by omega
      exact Finset.ne_of_mem_erase hx heq
    have h_diff_pos : 1 ≤ a_max - x := by omega
    have h_diff_le : a_max - x ≤ 2 * N := by omega
    exact Finset.mem_Icc.mpr ⟨h_diff_pos, h_diff_le⟩
  -- Injectivity of x ↦ a_max - x on A'
  have h_injOn : ∀ x ∈ A', ∀ y ∈ A', a_max - x = a_max - y → x = y := by
    intro x hx y hy h_eq
    have hx_mem_A : x ∈ A := Finset.mem_of_mem_erase hx
    have hy_mem_A : y ∈ A := Finset.mem_of_mem_erase hy
    have hx_le : x ≤ a_max := Finset.le_max' A x hx_mem_A
    have hy_le : y ≤ a_max := Finset.le_max' A y hy_mem_A
    omega
  have hB_card : B.card = A'.card :=
    Finset.card_image_of_injOn h_injOn
  -- Main case analysis
  by_cases h_exists : ∃ x ∈ A', a_max - x ∈ A
  · rcases h_exists with ⟨x, hx, hx_sum_mem⟩
    have hx_mem_A : x ∈ A := Finset.mem_of_mem_erase hx
    have hx_le_max : x ≤ a_max := Finset.le_max' A x hx_mem_A
    by_cases h_eq : x = a_max - x
    · -- a_max = 2x. Need another pair from A'' = A' \ {x}
      let A'' := A'.erase x
      have hA''_card : A''.card = A'.card - 1 := by
        rw [Finset.card_erase_of_mem hx]
      -- Look at differences from A''
      by_cases h_exists2 : ∃ y ∈ A'', a_max - y ∈ A
      · rcases h_exists2 with ⟨y, hy, hy_sum_mem⟩
        have hy_mem_A' : y ∈ A' := Finset.mem_of_mem_erase hy
        have hy_mem_A : y ∈ A := Finset.mem_of_mem_erase hy_mem_A'
        have hy_ne_x : y ≠ x := Finset.ne_of_mem_erase hy
        have hy_le_max : y ≤ a_max := Finset.le_max' A y hy_mem_A
        have hy_ne_sum : y ≠ a_max - y := by
          intro heq2
          have h_amax_eq_2y : a_max = 2 * y := by
            have hsum : y + y = a_max := by
              rw [← Nat.sub_add_cancel hy_le_max, ← heq2]
            omega
          have h_amax_eq_2x : a_max = 2 * x := by
            have hsum : x + x = a_max := by
              rw [← Nat.sub_add_cancel hx_le_max, ← h_eq]
            omega
          have hxy : x = y := by omega
          exact hy_ne_x hxy.symm
        refine ⟨y, hy_mem_A, a_max - y, hy_sum_mem, hy_ne_sum, ?_⟩
        rw [add_comm, Nat.sub_add_cancel hy_le_max]
        exact ha_max_mem
      · -- No difference from A'' is in A; counting gives contradiction
        have h_all_out : ∀ y ∈ A'', a_max - y ∉ A := by
          intro y hy
          by_contra h_in
          exact h_exists2 ⟨y, hy, h_in⟩
        let B' := A''.image (λ y => a_max - y)
        have hB'_subset : B' ⊆ Icc 1 (2 * N) := by
          intro d hd
          rw [Finset.mem_image] at hd
          rcases hd with ⟨y, hy, rfl⟩
          have hy_mem_A' : y ∈ A' := Finset.mem_of_mem_erase hy
          have hy_mem_A : y ∈ A := Finset.mem_of_mem_erase hy_mem_A'
          have hy_Icc : y ∈ Icc 1 (2 * N) := hA hy_mem_A
          have hy_pos : 1 ≤ y := (Finset.mem_Icc.mp hy_Icc).left
          have hy_le_amax : y ≤ a_max := Finset.le_max' A y hy_mem_A
          have hy_lt_amax : y < a_max := by
            by_contra! hge
            have heq : y = a_max := by omega
            exact Finset.ne_of_mem_erase hy_mem_A' heq
          have h_diff_pos : 1 ≤ a_max - y := by omega
          have h_diff_le : a_max - y ≤ 2 * N := by omega
          exact Finset.mem_Icc.mpr ⟨h_diff_pos, h_diff_le⟩
        have hB'_disjoint : A ∩ B' = ∅ := by
          ext d
          constructor
          · intro hd
            rw [Finset.mem_inter] at hd
            rcases hd with ⟨hd_A, hd_B'⟩
            rw [Finset.mem_image] at hd_B'
            rcases hd_B' with ⟨y, hy, rfl⟩
            exact absurd hd_A (h_all_out y hy)
          · intro hd
            simp at hd
        have h_injOn'' : ∀ y ∈ A'', ∀ z ∈ A'', a_max - y = a_max - z → y = z := by
          intro y hy z hz h_eq2
          have hy_mem_A' : y ∈ A' := Finset.mem_of_mem_erase hy
          have hz_mem_A' : z ∈ A' := Finset.mem_of_mem_erase hz
          have hy_mem_A : y ∈ A := Finset.mem_of_mem_erase hy_mem_A'
          have hz_mem_A : z ∈ A := Finset.mem_of_mem_erase hz_mem_A'
          have hy_le : y ≤ a_max := Finset.le_max' A y hy_mem_A
          have hz_le : z ≤ a_max := Finset.le_max' A z hz_mem_A
          omega
        have hB'_card : B'.card = A''.card :=
          Finset.card_image_of_injOn h_injOn''
        -- A and B' are disjoint subsets of Icc 1 (2*N)
        -- So |A| + |B'| ≤ 2N
        have h_union_subset : A ∪ B' ⊆ Icc 1 (2 * N) := by
          intro d hd
          rw [Finset.mem_union] at hd
          rcases hd with (hd_A | hd_B')
          · exact hA hd_A
          · exact hB'_subset hd_B'
        have h_card_union : (A ∪ B').card = A.card + B'.card := by
          have h := Finset.card_union_add_card_inter A B'
          rw [hB'_disjoint, Finset.card_empty, add_zero] at h
          exact h
        have h_card_Icc : (Icc 1 (2 * N)).card = 2 * N := by
          simp
        have h_card_union_le : (A ∪ B').card ≤ (Icc 1 (2 * N)).card :=
          Finset.card_le_card h_union_subset
        rw [h_card_union, hB'_card, hA''_card, h_card_Icc] at h_card_union_le
        rw [hA'_card] at h_card_union_le
        omega
    · -- x ≠ a_max - x, done
      refine ⟨x, hx_mem_A, a_max - x, hx_sum_mem, h_eq, ?_⟩
      rw [add_comm, Nat.sub_add_cancel hx_le_max]
      exact ha_max_mem
  · -- No difference is in A
    have h_all_out : ∀ x ∈ A', a_max - x ∉ A := by
      intro x hx
      by_contra h_in
      exact h_exists ⟨x, hx, h_in⟩
    -- A and B are disjoint
    have hB_disjoint : A ∩ B = ∅ := by
      ext d
      constructor
      · intro hd
        rw [Finset.mem_inter] at hd
        rcases hd with ⟨hd_A, hd_B⟩
        rw [Finset.mem_image] at hd_B
        rcases hd_B with ⟨x, hx, rfl⟩
        exact absurd hd_A (h_all_out x hx)
      · intro hd
        simp at hd
    -- A and B are disjoint subsets of Icc 1 (2*N)
    have h_union_subset : A ∪ B ⊆ Icc 1 (2 * N) := by
      intro d hd
      rw [Finset.mem_union] at hd
      rcases hd with (hd_A | hd_B)
      · exact hA hd_A
      · exact hB_subset hd_B
    have h_card_union : (A ∪ B).card = A.card + B.card := by
      have h := Finset.card_union_add_card_inter A B
      rw [hB_disjoint, Finset.card_empty, add_zero] at h
      exact h
    have h_card_Icc : (Icc 1 (2 * N)).card = 2 * N := by
      simp
    have h_card_union_le : (A ∪ B).card ≤ (Icc 1 (2 * N)).card :=
      Finset.card_le_card h_union_subset
    rw [h_card_union, hB_card, hA'_card, h_card_Icc] at h_card_union_le
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
