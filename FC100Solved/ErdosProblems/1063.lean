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
# Erdős Problem 1063

*References:*
 * [erdosproblems.com/1063](https://www.erdosproblems.com/1063)
 * [ErSe83] Erdos, P. and Selfridge, J. L., Problem 6447. Amer. Math. Monthly (1983), 710.
 * [Gu04] Guy, Richard K., _Unsolved problems in number theory_. (2004), Problem B31.
 * [Mo85] Monier (1985). No reference found.
-/

open Filter Real
open scoped Nat Topology

namespace Erdos1063

/--
Let $n_k$ be the least $n \ge 2k$ such that all but one of the integers $n - i$ with
$0 \le i < k$ divide $\binom{n}{k}$.
-/
noncomputable def n (k : ℕ) : ℕ :=
  sInf {m | 2 * k ≤ m ∧ ∃ i0 < k, ¬ (m - i0) ∣ m.choose k ∧
    ∀ i < k, i ≠ i0 → (m - i) ∣ m.choose k}

/--
Estimate $n_k$ by finding a better upper bound.
-/
@[category research open, AMS 11]
theorem erdos_1063.better_upper :
    let upper_bound : ℕ → ℝ := answer(sorry)
    (fun k => (n k : ℝ)) =O[atTop] upper_bound ∧
    upper_bound =o[atTop] fun k =>
      (k : ℝ) * ((Finset.Icc 1 (k - 1)).lcm (fun n : ℕ => n) : ℝ) := by
  sorry

/--
Erdős and Selfridge noted that, for $n \ge 2k$ with $k \ge 2$, at least one of the numbers
$n - i$ for $0 \le i < k$ fails to divide $\binom{n}{k}$ ([ErSe83]).
-/
@[category research solved, AMS 11]
theorem erdos_1063.variants.exists_exception {n k : ℕ} (hk : 2 ≤ k) (h : 2 * k ≤ n) :
    ∃ i < k, ¬ (n - i) ∣ n.choose k := by
  sorry

/-- The initial values satisfy $n_2 = 4$, $n_3 = 6$, $n_4 = 9$, and $n_5 = 12$ ([Gu04], Problem B31). -/
@[category research solved, AMS 11]
theorem erdos_1063.variants.small_values :
    n 2 = 4 ∧ n 3 = 6 ∧ n 4 = 9 ∧ n 5 = 12 := by
  sorry

/-- Monier observed that $n_k \le k!$ for $k \ge 3$ ([Mo85]).
TODO: Find reference
-/
@[category research solved, AMS 11]
theorem erdos_1063.variants.monier_upper_bound {k : ℕ} (hk : 3 ≤ k) :
    n k ≤ k ! := by
  sorry

/-- [Cambie observed](https://www.erdosproblems.com/1063) the improved bound
$n_k \le k \cdot \operatorname{lcm}(1, \dotsc, k - 1)$. -/
@[category research solved, AMS 11]
theorem erdos_1063.variants.cambie_upper_bound {k : ℕ} (hk : 3 ≤ k) :
    n k ≤ k * (Finset.Icc 1 (k - 1)).lcm id := by
  -- Agent proof
  set L := (Finset.Icc 1 (k - 1)).lcm id with hL
  set m := k * L with hm
  have hk_pos : 0 < k := by omega
  have hkm1_mem : k - 1 ∈ Finset.Icc 1 (k - 1) :=
    Finset.mem_Icc.mpr ⟨by omega, le_refl _⟩
  have hL_dvd_km1 : (k - 1) ∣ L := Finset.dvd_lcm (f := id) hkm1_mem
  have hL_pos : 0 < L := by
    by_contra! hL0
    have hL0' : L = 0 := by omega
    rw [Finset.lcm_eq_zero_iff] at hL0'
    rcases hL0' with ⟨x, hx, hx0⟩
    have hx1 : 1 ≤ x := (Finset.mem_Icc.mp hx).left
    have hx_eq_0 : x = 0 := by simpa using hx0
    omega
  have hm_lower : 2 * k ≤ m := by
    have hL_ge_2 : 2 ≤ L := by
      have hk1_ge_2 : 2 ≤ k - 1 := by omega
      have h_le : k - 1 ≤ L := Nat.le_of_dvd hL_pos hL_dvd_km1
      omega
    nlinarith
  have hm_ge_k : k ≤ m := by
    have hL_ge_1 : 1 ≤ L := by omega
    nlinarith
  -- Key identity: m.choose k = L * (m-1).choose (k-1)
  have h_choose_eq : m.choose k = L * (m - 1).choose (k - 1) := by
    have h_mul := Nat.choose_mul (n := m) (show 1 ≤ k from by omega)
    rw [Nat.choose_one_right, Nat.choose_one_right] at h_mul
    rw [hm] at h_mul
    have h_eq : m.choose k * k = (L * (m - 1).choose (k - 1)) * k := by
      calc
        m.choose k * k = (k * L) * (m - 1).choose (k - 1) := h_mul
        _ = k * (L * (m - 1).choose (k - 1)) := by ring
        _ = (L * (m - 1).choose (k - 1)) * k := by ring
    exact Nat.eq_of_mul_eq_mul_right hk_pos h_eq
  -- For each j with 1 ≤ j ≤ k-1, j ∣ L
  have h_j_dvd_L (j : ℕ) (hj : j ∈ Finset.Icc 1 (k - 1)) : j ∣ L :=
    Finset.dvd_lcm (f := id) hj
  -- For each such j, j ∣ m - j
  have h_j_dvd_m_sub_j (j : ℕ) (hj : j ∈ Finset.Icc 1 (k - 1)) : j ∣ m - j := by
    have hj_dvd_L := h_j_dvd_L j hj
    have hj_dvd_m : j ∣ m := by
      rw [hm]
      exact hj_dvd_L.mul_left k
    have hj_dvd_j : j ∣ j := dvd_refl _
    exact Nat.dvd_sub hj_dvd_m hj_dvd_j
  -- Product formula: (m-1).choose(k-1) * (k-1)! = ∏_{j=1}^{k-1} (m-j)
  have h_prod_formula : (m - 1).choose (k - 1) * (k - 1)! = ∏ j ∈ Finset.Icc 1 (k - 1), (m - j) := by
    have h_asc := Nat.choose_eq_asc_factorial_div_factorial (m - k) (k - 1)
    have h_simp : m - k + (k - 1) = m - 1 := by omega
    rw [h_simp] at h_asc
    have h_fact_dvd : (k - 1)! ∣ (m - k + 1).ascFactorial (k - 1) :=
      Nat.factorial_dvd_ascFactorial (m - k + 1) (k - 1)
    rw [h_asc, Nat.div_mul_cancel h_fact_dvd, Nat.ascFactorial_eq_prod_range]
    -- Reindex i ↦ k-1-i which maps range(k-1) bijectively to Icc 1 (k-1)
    have h_image : Finset.image (fun i : ℕ => k - 1 - i) (Finset.range (k - 1)) = Finset.Icc 1 (k - 1) := by
      ext x
      constructor
      · intro hx
        rcases Finset.mem_image.mp hx with ⟨i, hi, rfl⟩
        have hi_lt : i < k - 1 := Finset.mem_range.mp hi
        have h_low : 1 ≤ k - 1 - i := by omega
        have h_high : k - 1 - i ≤ k - 1 := Nat.sub_le _ _
        exact Finset.mem_Icc.mpr ⟨h_low, h_high⟩
      · intro hx
        rcases Finset.mem_Icc.mp hx with ⟨hx1, hx2⟩
        set i := k - 1 - x with hi_def
        have hi_range : i ∈ Finset.range (k - 1) :=
          Finset.mem_range.mpr (by omega)
        have h_eq : k - 1 - i = x := by
          dsimp [i]
          omega
        exact Finset.mem_image.mpr ⟨i, hi_range, h_eq⟩
    calc
      ∏ i ∈ Finset.range (k - 1), (m - k + 1 + i) = ∏ i ∈ Finset.range (k - 1), (m - (k - 1 - i)) := by
        refine Finset.prod_congr rfl (fun i hi => ?_)
        have hi_lt : i < k - 1 := Finset.mem_range.mp hi
        omega
      _ = ∏ j ∈ Finset.image (fun i : ℕ => k - 1 - i) (Finset.range (k - 1)), (m - j) := by
        rw [Finset.prod_image]
        intro x hx y hy h_eq_sub
        have hx_lt : x < k - 1 := Finset.mem_range.mp hx
        have hy_lt : y < k - 1 := Finset.mem_range.mp hy
        have hx_le : x ≤ k - 1 := by omega
        have hy_le : y ≤ k - 1 := by omega
        have h_eq_sub' : k - 1 - x = k - 1 - y := h_eq_sub
        have h_eq : x = y := by
          have h1 : (k - 1 - x) + x = k - 1 := Nat.sub_add_cancel hx_le
          have h2 : (k - 1 - y) + y = k - 1 := Nat.sub_add_cancel hy_le
          rw [h_eq_sub'] at h1
          rw [← h2] at h1
          omega
        exact h_eq
      _ = ∏ j ∈ Finset.Icc 1 (k - 1), (m - j) := by rw [h_image]
  -- Factor each (m-j) = j * ((m-j)/j)
  have h_factor (j : ℕ) (hj : j ∈ Finset.Icc 1 (k - 1)) : m - j = j * ((m - j) / j) := by
    have hj_dvd := h_j_dvd_m_sub_j j hj
    simpa [mul_comm] using (Nat.div_mul_cancel hj_dvd).symm
  -- Prove ∏_{j=1}^{k-1} j = (k-1)!
  have h_prod_Icc_eq_factorial : (∏ j ∈ Finset.Icc 1 (k - 1), j) = (k - 1)! := by
    induction' k - 1 with n ih
    · simp
    · have hle : 1 ≤ n + 1 := by omega
      rw [Finset.prod_Icc_succ_top hle]
      rw [ih]
      rw [Nat.factorial_succ]
      ring
  -- Therefore (m-1).choose(k-1) * (k-1)! = (k-1)! * ∏_{j} ((m-j)/j)
  have h_prod_t : (m - 1).choose (k - 1) * (k - 1)! = (k - 1)! * ∏ j ∈ Finset.Icc 1 (k - 1), ((m - j) / j) := by
    rw [h_prod_formula]
    calc
      ∏ j ∈ Finset.Icc 1 (k - 1), (m - j) = ∏ j ∈ Finset.Icc 1 (k - 1), (j * ((m - j) / j)) := by
        refine Finset.prod_congr rfl (fun j hj => ?_)
        simpa using h_factor j hj
      _ = (∏ j ∈ Finset.Icc 1 (k - 1), j) * (∏ j ∈ Finset.Icc 1 (k - 1), ((m - j) / j)) := by
        rw [Finset.prod_mul_distrib]
      _ = (k - 1)! * (∏ j ∈ Finset.Icc 1 (k - 1), ((m - j) / j)) := by
        rw [h_prod_Icc_eq_factorial]
  have h_fact_pos : 0 < (k - 1)! := Nat.factorial_pos _
  have h_choose_prod : (m - 1).choose (k - 1) = ∏ j ∈ Finset.Icc 1 (k - 1), ((m - j) / j) := by
    have h_eq : (k - 1)! * (m - 1).choose (k - 1) = (k - 1)! * ∏ j ∈ Finset.Icc 1 (k - 1), ((m - j) / j) := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using h_prod_t
    exact Nat.eq_of_mul_eq_mul_left h_fact_pos h_eq
  -- For i ≥ 1, (m-i) = i * ((m-i)/i) and i ∣ L, so (m-i) ∣ m.choose k
  have h_div (i : ℕ) (hi : i ∈ Finset.Icc 1 (k - 1)) : (m - i) ∣ m.choose k := by
    rw [h_choose_eq, h_factor i hi]
    have hi_dvd_L := h_j_dvd_L i hi
    have hi_dvd_prod : ((m - i) / i) ∣ (m - 1).choose (k - 1) := by
      rw [h_choose_prod]
      exact Finset.dvd_prod_of_mem (fun j => (m - j) / j) hi
    exact Nat.mul_dvd_mul hi_dvd_L hi_dvd_prod
  -- Lemma: (m - j) / j = k * (L / j) - 1
  have h_div_eq (j : ℕ) (hj : j ∈ Finset.Icc 1 (k - 1)) : (m - j) / j = k * (L / j) - 1 := by
    have hj_pos : 0 < j := by
      have : 1 ≤ j := (Finset.mem_Icc.mp hj).left
      omega
    apply (Nat.eq_of_mul_eq_mul_right hj_pos)
    calc
      ((m - j) / j) * j = m - j := Nat.div_mul_cancel (h_j_dvd_m_sub_j j hj)
      _ = k * L - j := by rw [hm]
      _ = k * ((L / j) * j) - j := by rw [Nat.div_mul_cancel (h_j_dvd_L j hj)]
      _ = (k * (L / j)) * j - j := by ring
      _ = (k * (L / j)) * j - 1 * j := by simp
      _ = (k * (L / j) - 1) * j := by rw [Nat.sub_mul]
  -- Each factor (m-j)/j is coprime to k
  have h_coprime_all (j : ℕ) (hj : j ∈ Finset.Icc 1 (k - 1)) : Nat.Coprime k ((m - j) / j) := by
    rw [h_div_eq j hj]
    refine Nat.coprime_of_dvd (fun p hp h_p_dvd_k h_p_dvd_factor => ?_)
    have h_p_dvd_mul : p ∣ k * (L / j) := h_p_dvd_k.mul_right (L / j)
    have hj_pos : 0 < j := by
      have : 1 ≤ j := (Finset.mem_Icc.mp hj).left
      omega
    have h_p_dvd_one : p ∣ 1 := by
      have h_sub : p ∣ (k * (L / j)) - (k * (L / j) - 1) := Nat.dvd_sub h_p_dvd_mul h_p_dvd_factor
      have h_pos : 1 ≤ k * (L / j) := by
        have hk_ge_1 : 1 ≤ k := by omega
        have hj_le_L : j ≤ L := by
          have : j ≤ k - 1 := (Finset.mem_Icc.mp hj).right
          have hkm1_le_L : k - 1 ≤ L := Nat.le_of_dvd hL_pos hL_dvd_km1
          omega
        have hLj_ge_1 : 1 ≤ L / j := Nat.div_pos hj_le_L hj_pos
        nlinarith
      have h_sub_eq_one : (k * (L / j)) - (k * (L / j) - 1) = 1 := by omega
      rw [h_sub_eq_one] at h_sub
      exact h_sub
    have hp_ne_one : p ≠ 1 := Nat.Prime.ne_one hp
    exact hp_ne_one (Nat.eq_one_of_dvd_one h_p_dvd_one)
  -- Prove that k does not divide the product using induction on the Finset
  have h_not_dvd_prod : ¬ k ∣ ∏ j ∈ Finset.Icc 1 (k - 1), ((m - j) / j) := by
    have h_induction : ∀ (s : Finset ℕ), s ⊆ Finset.Icc 1 (k - 1) → (∀ j ∈ s, Nat.Coprime k ((m - j) / j)) → ¬ k ∣ ∏ j ∈ s, ((m - j) / j) := by
      intro s hs h_cop
      induction' s using Finset.induction_on with j s' hjs' ih
      · intro h_dvd
        have hk_gt_1 : 1 < k := by omega
        have h_prod_empty : (∏ x ∈ (∅ : Finset ℕ), ((m - x) / x)) = 1 := by simp
        rw [h_prod_empty] at h_dvd
        have := Nat.le_of_dvd (by norm_num) h_dvd
        omega
      · intro h_dvd
        have hj_mem_insert : j ∈ insert j s' := Finset.mem_insert_self j s'
        have h_cop_j : Nat.Coprime k ((m - j) / j) := h_cop j hj_mem_insert
        rw [Finset.prod_insert hjs'] at h_dvd
        rw [mul_comm] at h_dvd
        have h_dvd' : k ∣ ∏ x ∈ s', ((m - x) / x) :=
          h_cop_j.dvd_of_dvd_mul_right h_dvd
        have hs'_sub : s' ⊆ Finset.Icc 1 (k - 1) := by
          intro x hx
          apply hs
          exact Finset.mem_insert_of_mem hx
        have h_cop' : ∀ x ∈ s', Nat.Coprime k ((m - x) / x) := by
          intro x hx
          apply h_cop x
          exact Finset.mem_insert_of_mem hx
        exact ih hs'_sub h_cop' h_dvd'
    exact h_induction (Finset.Icc 1 (k - 1)) (Finset.Subset.refl _) h_coprime_all
  have h_not_div : ¬ (m - 0) ∣ m.choose k := by
    rw [h_choose_eq, Nat.sub_zero]
    intro h_dvd
    have h_dvd' : k ∣ (m - 1).choose (k - 1) := by
      have h_dvd_comm : L * k ∣ L * (m - 1).choose (k - 1) := by
        simpa [mul_comm] using h_dvd
      exact Nat.dvd_of_mul_dvd_mul_left hL_pos h_dvd_comm
    rw [h_choose_prod] at h_dvd'
    exact h_not_dvd_prod h_dvd'
  -- Assemble: m is in the set, so n k ≤ m = k*L
  have h_mem : m ∈ {m' | 2 * k ≤ m' ∧ ∃ i0 < k, ¬ (m' - i0) ∣ m'.choose k ∧
      ∀ i < k, i ≠ i0 → (m' - i) ∣ m'.choose k} := by
    refine ⟨hm_lower, 0, hk_pos, ?_, ?_⟩
    · simpa using h_not_div
    · intro i hi hi0
      have hi_mem : i ∈ Finset.Icc 1 (k - 1) := by
        refine Finset.mem_Icc.mpr ⟨by omega, ?_⟩
        omega
      exact h_div i hi_mem
  exact Nat.sInf_le h_mem

/-- The least common multiple bound implies $n_k \le \exp((1 + o(1))k)$. -/
@[category research solved, AMS 11]
theorem erdos_1063.variants.exp_upper_bound :
    ∃ f : ℕ → ℝ, Tendsto f atTop (𝓝 0) ∧
      ∀ k, (n k : ℝ) ≤ exp ((1 + f k) * k) := by
  sorry

end Erdos1063
