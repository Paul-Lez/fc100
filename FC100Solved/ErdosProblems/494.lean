/-
Copyright 2025 The Formal Conjectures Authors.

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
# Erdős Problem 494

*References:*
  - [erdosproblems.com/494](https://www.erdosproblems.com/494)
  - [SeSt58] Selfridge, J. L. and Straus, E., On the determination of numbers by their sums
      of a fixed order. Pacific Journal of Math. (1958), 847-856.
  - [Er61] Erdős, Paul, Some unsolved problems. Magyar Tud. Akad. Mat. Kutató Int. Közl. (1961),
      221-254.
  - [GFS62] Gordon, B. and Fraenkel, A. S. and Straus, E. G., On the determination of sets
      by the sets of sums of a certain order. Pacific J. Math. (1962), 187--196.
-/

open Filter

namespace Erdos494

/--
For a finite set $A \subset \mathbb{C}$ and $k \ge 1$, define $A_k$ as the multiset consisting of
all sums of $k$ distinct elements of $A$.
-/
noncomputable def sumMultiset (A : Finset ℂ) (k : ℕ) : Multiset ℂ :=
  (A.powersetCard k).val.map fun s => s.sum id

def Erdos494Unique (k : ℕ) (card : ℕ) :=
  ∀ A B : Finset ℂ, A.card = card → B.card = card → sumMultiset A k = sumMultiset B k → A = B

/--
Selfridge and Straus [SeSt58] showed that the conjecture is true when $k = 2$ and
$|A| \ne 2^l$ for $l \ge 0$.
They also gave counterexamples when $k = 2$ and $|A| = 2^l$.
-/
@[category research solved, AMS 5]
theorem erdos_494.variants.k_eq_2_card_not_pow_two :
    ∀ card : ℕ, (∀ l : ℕ, card ≠ 2 ^ l) → Erdos494Unique 2 card := by
  sorry

/--
Selfridge and Straus [SeSt58] gave counterexamples to the conjecture
when $k = 2$ and $|A| = 2^l$.
-/
@[category research solved, AMS 5]
theorem erdos_494.variants.k_eq_2_card_pow_two :
    ∀ card : ℕ, (∃ l : ℕ, card = 2 ^ l) → ¬Erdos494Unique 2 card := by
  sorry

/--
Selfridge and Straus [SeSt58] also showed that the conjecture is true when
1) $k = 3$ and $|A| > 6$ or
2) $k = 4$ and $|A| > 12$.
More generally, they proved that $A$ is determined by $A_k$ (and $|A|$) if $|A|$ is divisible by
a prime greater than $k$.
-/
@[category research solved, AMS 5]
theorem erdos_494.variants.k_eq_3_card_gt_6 :
    ∀ card > 6, Erdos494Unique 3 card := by
  sorry

/--
Selfridge and Straus [SeSt58] showed that the conjecture is true
when $k = 4$ and $|A| > 12$.
-/
@[category research solved, AMS 5]
theorem erdos_494.variants.k_eq_4_card_gt_12 :
    ∀ card > 12, Erdos494Unique 4 card := by
  sorry

/--
Selfridge and Straus [SeSt58] proved that $A$ is determined by $A_k$
if $|A|$ is divisible by a prime greater than $k$.
-/
@[category research solved, AMS 5]
theorem erdos_494.variants.card_divisible_by_prime_gt_k :
    ∀ (k card p : ℕ), p.Prime → k ∈ Set.Ioo 0 p → p ∣ card → Erdos494Unique k card := by
  sorry

/--
Kruyt noted that the conjecture fails when $|A| = k$, by rotating $A$ around an appropriate point.
-/
@[category research solved, AMS 5]
theorem erdos_494.variants.k_eq_card :
    ∀ k > 2, ¬Erdos494Unique k k := by
  sorry

/--
Similarly, Tao noted that the conjecture fails when $|A| = 2k$, by taking $A$ to be a set of
the total sum 0 and considering $-A$.
-/
@[category research solved, AMS 5]
theorem erdos_494.variants.card_eq_2k :
    ∀ k > 2, ¬Erdos494Unique k (2 * k) := by
  sorry

/--
Gordon, Fraenkel, and Straus [GRS62] proved that the claim is true for all $k > 2$ when
$|A|$ is sufficiently large.
-/
@[category research solved, AMS 5]
theorem erdos_494.variants.gordon_fraenkel_straus :
    ∀ k > 2, ∀ᶠ card in atTop, Erdos494Unique k card := by
  sorry

/--
A version in [Er61] by Erdős is product instead of sum, which is false.
Counterexample (by Steinerberger): consider $k = 3$ and let
$A = \{1, \zeta_6, \zeta_6^2, \zeta_6^4\}$ and $B = \{1, \zeta_6^2, \zeta_6^3, \zeta_6^4\}$.
-/
noncomputable def prodMultiset (A : Finset ℂ) (k : ℕ) : Multiset ℂ :=
  ((A.powersetCard k).val.map (fun s => s.prod id))

/-- A counterexample to the product version of the conjecture (by Steinerberger). -/
@[category research solved, AMS 5]
theorem erdos_494.variants.product :
    ∃ (A B : Finset ℂ), A.card = B.card ∧ prodMultiset A 3 = prodMultiset B 3 ∧
      A ≠ B := by
  -- Agent proof
  -- Primitive 6th root of unity ζ = e^(2πi/6)
  set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / 6) with hζ_def
  have hζ6 : ζ ^ 6 = 1 := by
    rw [hζ_def]
    calc
      (Complex.exp (2 * Real.pi * Complex.I / 6)) ^ 6
          = Complex.exp ((6 : ℕ) * (2 * Real.pi * Complex.I / 6)) := by
        rw [← Complex.exp_nat_mul]
      _ = Complex.exp (2 * Real.pi * Complex.I) := by ring
      _ = 1 := Complex.exp_two_pi_mul_I
  have hζ3 : ζ ^ 3 = -1 := by
    rw [hζ_def]
    calc
      (Complex.exp (2 * Real.pi * Complex.I / 6)) ^ 3
          = Complex.exp ((3 : ℕ) * (2 * Real.pi * Complex.I / 6)) := by
        rw [← Complex.exp_nat_mul]
      _ = Complex.exp (Real.pi * Complex.I) := by ring
      _ = -1 := Complex.exp_pi_mul_I
  have hζ5 : ζ ^ 5 = -(ζ ^ 2) := by
    calc
      ζ ^ 5 = ζ ^ 3 * ζ ^ 2 := by ring
      _ = (-1) * ζ ^ 2 := by rw [hζ3]
      _ = -(ζ ^ 2) := by simp
  have hζ7 : ζ ^ 7 = ζ := by
    calc
      ζ ^ 7 = ζ ^ 6 * ζ := by ring
      _ = 1 * ζ := by rw [hζ6]
      _ = ζ := by simp
  have hζ9 : ζ ^ 9 = -1 := by
    calc
      ζ ^ 9 = ζ ^ 6 * ζ ^ 3 := by ring
      _ = 1 * (-1) := by rw [hζ6, hζ3]
      _ = -1 := by simp
  -- ζ^k ≠ 1 for k = 1,2,3,4,5
  have hζ_pow_ne_one (k : ℕ) (hk : k ∈ Finset.Icc 1 5) : ζ ^ k ≠ 1 := by
    rw [hζ_def]
    intro h
    have hexp : Complex.exp ((k : ℂ) * (2 * Real.pi * Complex.I / 6)) = 1 := by
      calc
        Complex.exp ((k : ℂ) * (2 * Real.pi * Complex.I / 6))
            = (Complex.exp (2 * Real.pi * Complex.I / 6)) ^ k := by
          simpa using Complex.exp_nat_mul (2 * Real.pi * Complex.I / 6) k
        _ = 1 := h
    rcases (Complex.exp_eq_one_iff).mp hexp with ⟨n, hn⟩
    have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
    have hI : Complex.I ≠ 0 := Complex.I_ne_zero
    field_simp [hpi, hI] at hn
    have hn_int : (k : ℤ) = 6 * n := by exact_mod_cast hn
    have hk1 : (1 : ℤ) ≤ (k : ℤ) := by exact_mod_cast (Finset.mem_Icc.mp hk).1
    have hk5 : (k : ℤ) ≤ 5 := by exact_mod_cast (Finset.mem_Icc.mp hk).2
    by_cases hn_nonneg : 0 ≤ n
    · have hn_ge_one : (1 : ℤ) ≤ n := by
        by_contra hlt
        have : n = 0 := by omega
        rw [this] at hn_int
        have : (k : ℤ) = 0 := by simpa using hn_int
        omega
      have : (k : ℤ) ≥ 6 := by
        calc
          (k : ℤ) = 6 * n := hn_int
          _ ≥ 6 * 1 := by nlinarith
          _ = 6 := by norm_num
      omega
    · have hn_le_neg_one : n ≤ -1 := by omega
      have : (k : ℤ) ≤ -6 := by
        calc
          (k : ℤ) = 6 * n := hn_int
          _ ≤ 6 * (-1) := by nlinarith
          _ = -6 := by norm_num
      omega
  have hζ_ne_one : ζ ≠ 1 := by
    simpa using hζ_pow_ne_one 1 (by norm_num)
  have hζ2_ne_one : ζ ^ 2 ≠ 1 := by
    simpa using hζ_pow_ne_one 2 (by norm_num)
  have hζ4_ne_one : ζ ^ 4 ≠ 1 := by
    simpa using hζ_pow_ne_one 4 (by norm_num)
  -- Define f : Fin 6 → ℂ by f i = ζ^(i.val)
  let f : Fin 6 → ℂ := λ i => ζ ^ (i.val)
  have hf_inj : Function.Injective f := by
    intro i j h
    dsimp [f] at h
    by_contra hne
    have hne_val : i.val ≠ j.val := by
      intro heq; apply hne; exact Fin.ext heq
    by_cases hlt : i.val < j.val
    · have hsub : ζ ^ (j.val - i.val) = 1 := by
        calc
          ζ ^ (j.val - i.val) = ζ ^ j.val * (ζ ^ i.val)⁻¹ := by
            rw [pow_sub₀ ζ (Complex.exp_ne_zero _) (Nat.le_of_lt hlt)]
          _ = ζ ^ i.val * (ζ ^ i.val)⁻¹ := by rw [← h]
          _ = 1 := mul_inv_cancel₀ (pow_ne_zero _ (Complex.exp_ne_zero _))
      have hlt6 : j.val - i.val < 6 := by
        have : j.val ≤ 5 := by omega
        omega
      have h_cases : j.val - i.val = 1 ∨ j.val - i.val = 2 ∨ j.val - i.val = 3 ∨
                    j.val - i.val = 4 ∨ j.val - i.val = 5 := by omega
      rcases h_cases with (h1|h2|h3|h4|h5)
      · rw [h1] at hsub; exact hζ_pow_ne_one 1 (by norm_num) hsub
      · rw [h2] at hsub; exact hζ_pow_ne_one 2 (by norm_num) hsub
      · rw [h3] at hsub; rw [hζ3] at hsub; norm_num at hsub
      · rw [h4] at hsub; exact hζ_pow_ne_one 4 (by norm_num) hsub
      · rw [h5] at hsub; rw [hζ5] at hsub
        have hζ2_eq_neg_one : ζ ^ 2 = -1 := by
          calc
            ζ ^ 2 = -(-(ζ ^ 2)) := by ring
            _ = -(1) := by rw [hsub]
            _ = -1 := by ring
        have hζ4_eq_one : ζ ^ 4 = 1 := by
          calc
            ζ ^ 4 = (ζ ^ 2) ^ 2 := by ring
            _ = (-1) ^ 2 := by rw [hζ2_eq_neg_one]
            _ = 1 := by norm_num
        exact hζ4_ne_one hζ4_eq_one
    · have hle : j.val ≤ i.val := Nat.le_of_not_gt hlt
      by_cases heq' : j.val = i.val
      · exact hne_val heq'.symm
      · have hlt' : j.val < i.val := Nat.lt_of_le_of_ne hle heq'
        have hsub : ζ ^ (i.val - j.val) = 1 := by
          calc
            ζ ^ (i.val - j.val) = ζ ^ i.val * (ζ ^ j.val)⁻¹ := by
              rw [pow_sub₀ ζ (Complex.exp_ne_zero _) (Nat.le_of_lt hlt')]
            _ = ζ ^ j.val * (ζ ^ j.val)⁻¹ := by rw [h]
            _ = 1 := mul_inv_cancel₀ (pow_ne_zero _ (Complex.exp_ne_zero _))
        have hlt6 : i.val - j.val < 6 := by
          have : i.val ≤ 5 := by omega
          omega
        have h_cases : i.val - j.val = 1 ∨ i.val - j.val = 2 ∨ i.val - j.val = 3 ∨
                      i.val - j.val = 4 ∨ i.val - j.val = 5 := by omega
        rcases h_cases with (h1|h2|h3|h4|h5)
        · rw [h1] at hsub; exact hζ_pow_ne_one 1 (by norm_num) hsub
        · rw [h2] at hsub; exact hζ_pow_ne_one 2 (by norm_num) hsub
        · rw [h3] at hsub; rw [hζ3] at hsub; norm_num at hsub
        · rw [h4] at hsub; exact hζ_pow_ne_one 4 (by norm_num) hsub
        · rw [h5] at hsub; rw [hζ5] at hsub
          have hζ2_eq_neg_one : ζ ^ 2 = -1 := by
            calc
              ζ ^ 2 = -(-(ζ ^ 2)) := by ring
              _ = -(1) := by rw [hsub]
              _ = -1 := by ring
          have hζ4_eq_one : ζ ^ 4 = 1 := by
            calc
              ζ ^ 4 = (ζ ^ 2) ^ 2 := by ring
              _ = (-1) ^ 2 := by rw [hζ2_eq_neg_one]
              _ = 1 := by norm_num
          exact hζ4_ne_one hζ4_eq_one
  -- Embedding from Fin 6 to ℂ
  let emb : Fin 6 ↪ ℂ := ⟨f, hf_inj⟩
  -- Index sets
  let A_idx : Finset (Fin 6) := {0, 1, 2, 4}
  let B_idx : Finset (Fin 6) := {0, 2, 3, 4}
  -- The actual sets
  let A : Finset ℂ := A_idx.map emb
  let B : Finset ℂ := B_idx.map emb
  -- Key identity: product of elements in a subset = ζ^(sum of indices)
  have hprod_sum (s : Finset (Fin 6)) : (s.map emb).prod id = ζ ^ (Finset.sum s (λ i => i.val)) := by
    calc
      (s.map emb).prod id = s.prod (λ i => ζ ^ (i.val)) := by simp [emb, f]
      _ = ζ ^ (Finset.sum s (λ i => i.val)) := by rw [Finset.prod_pow_eq_pow_sum]
  -- Compute powersetCard for index sets using dec_trivial
  have hA_idx_pc_val : (A_idx.powersetCard 3).val =
      (Multiset.cons {0, 1, 2} (Multiset.cons {0, 1, 4} (Multiset.cons {0, 2, 4} (Multiset.cons {1, 2, 4} Multiset.zero)))) := by
    decide
  have hB_idx_pc_val : (B_idx.powersetCard 3).val =
      (Multiset.cons {0, 2, 3} (Multiset.cons {0, 2, 4} (Multiset.cons {0, 3, 4} (Multiset.cons {2, 3, 4} Multiset.zero)))) := by
    decide
  -- Transfer to A and B using powersetCard_map
  have hA_pc : A.powersetCard 3 = (A_idx.powersetCard 3).map (Finset.mapEmbedding emb).toEmbedding := by
    simpa [A] using Finset.powersetCard_map emb 3 A_idx
  have hB_pc : B.powersetCard 3 = (B_idx.powersetCard 3).map (Finset.mapEmbedding emb).toEmbedding := by
    simpa [B] using Finset.powersetCard_map emb 3 B_idx
  -- Compute sums of indices for each 3-element subset
  have hA_sums : (A_idx.powersetCard 3).val.map (λ s => Finset.sum s (λ i => i.val)) =
      (Multiset.cons 3 (Multiset.cons 5 (Multiset.cons 6 (Multiset.cons 7 Multiset.zero)))) := by
    decide
  have hB_sums : (B_idx.powersetCard 3).val.map (λ s => Finset.sum s (λ i => i.val)) =
      (Multiset.cons 5 (Multiset.cons 6 (Multiset.cons 7 (Multiset.cons 9 Multiset.zero)))) := by
    decide
  -- Compute prodMultiset A 3
  have hA_prod : prodMultiset A 3 = (Multiset.cons (-1) (Multiset.cons (-(ζ ^ 2)) (Multiset.cons 1 (Multiset.cons ζ Multiset.zero)))) := by
    calc
      prodMultiset A 3 = ((A.powersetCard 3).val.map (fun s => s.prod id)) := rfl
      _ = (((A_idx.powersetCard 3).map (Finset.mapEmbedding emb).toEmbedding).val.map (fun s => s.prod id)) := by rw [hA_pc]
      _ = ((A_idx.powersetCard 3).val.map ((Finset.mapEmbedding emb).toEmbedding)).map (fun s => s.prod id) := by
        simp
      _ = (A_idx.powersetCard 3).val.map ((fun s => s.prod id) ∘ ((Finset.mapEmbedding emb).toEmbedding)) := by
        rw [Multiset.map_map]
      _ = (A_idx.powersetCard 3).val.map (fun s => (((Finset.mapEmbedding emb).toEmbedding) s).prod id) := rfl
      _ = (A_idx.powersetCard 3).val.map (fun s => (s.map emb).prod id) :=
        Multiset.map_congr rfl (λ s hs => rfl)
      _ = (A_idx.powersetCard 3).val.map (fun s => ζ ^ (s.sum (λ i => i.val))) :=
        Multiset.map_congr rfl (λ s hs => by rw [hprod_sum])
      _ = ((A_idx.powersetCard 3).val.map (λ s => Finset.sum s (λ i => i.val))).map (λ n => ζ ^ n) := by
        rw [Multiset.map_map]
        rfl
      _ = (Multiset.cons 3 (Multiset.cons 5 (Multiset.cons 6 (Multiset.cons 7 Multiset.zero)))).map (λ n => ζ ^ n) := by
        rw [hA_sums]
      _ = (Multiset.cons (ζ ^ 3) (Multiset.cons (ζ ^ 5) (Multiset.cons (ζ ^ 6) (Multiset.cons (ζ ^ 7) Multiset.zero)))) := by
        rfl
      _ = (Multiset.cons (-1) (Multiset.cons (-(ζ ^ 2)) (Multiset.cons 1 (Multiset.cons ζ Multiset.zero)))) := by
        simp [hζ3, hζ5, hζ6, hζ7]
  -- Compute prodMultiset B 3
  have hB_prod : prodMultiset B 3 = (Multiset.cons (-1) (Multiset.cons (-(ζ ^ 2)) (Multiset.cons 1 (Multiset.cons ζ Multiset.zero)))) := by
    calc
      prodMultiset B 3 = ((B.powersetCard 3).val.map (fun s => s.prod id)) := rfl
      _ = (((B_idx.powersetCard 3).map (Finset.mapEmbedding emb).toEmbedding).val.map (fun s => s.prod id)) := by rw [hB_pc]
      _ = ((B_idx.powersetCard 3).val.map ((Finset.mapEmbedding emb).toEmbedding)).map (fun s => s.prod id) := by
        simp
      _ = (B_idx.powersetCard 3).val.map ((fun s => s.prod id) ∘ ((Finset.mapEmbedding emb).toEmbedding)) := by
        rw [Multiset.map_map]
      _ = (B_idx.powersetCard 3).val.map (fun s => (((Finset.mapEmbedding emb).toEmbedding) s).prod id) := rfl
      _ = (B_idx.powersetCard 3).val.map (fun s => (s.map emb).prod id) :=
        Multiset.map_congr rfl (λ s hs => rfl)
      _ = (B_idx.powersetCard 3).val.map (fun s => ζ ^ (s.sum (λ i => i.val))) :=
        Multiset.map_congr rfl (λ s hs => by rw [hprod_sum])
      _ = ((B_idx.powersetCard 3).val.map (λ s => Finset.sum s (λ i => i.val))).map (λ n => ζ ^ n) := by
        rw [Multiset.map_map]
        rfl
      _ = (Multiset.cons 5 (Multiset.cons 6 (Multiset.cons 7 (Multiset.cons 9 Multiset.zero)))).map (λ n => ζ ^ n) := by
        rw [hB_sums]
      _ = (Multiset.cons (ζ ^ 5) (Multiset.cons (ζ ^ 6) (Multiset.cons (ζ ^ 7) (Multiset.cons (ζ ^ 9) Multiset.zero)))) := by
        rfl
      _ = (Multiset.cons (-(ζ ^ 2)) (Multiset.cons 1 (Multiset.cons ζ (Multiset.cons (-1) Multiset.zero)))) := by
        rw [hζ5, hζ6, hζ7, hζ9]
      _ = (Multiset.cons (-1) (Multiset.cons (-(ζ ^ 2)) (Multiset.cons 1 (Multiset.cons ζ Multiset.zero)))) := by
        simp [Multiset.cons_swap]
  -- Cardinalities
  have hcardA : A.card = 4 := by
    dsimp [A]
    have h : (A_idx.map emb).card = A_idx.card := by
      simpa using Finset.card_image_of_injective A_idx hf_inj
    rw [h]
    decide
  have hcardB : B.card = 4 := by
    dsimp [B]
    have h : (B_idx.map emb).card = B_idx.card := by
      simpa using Finset.card_image_of_injective B_idx hf_inj
    rw [h]
    decide
  -- A ≠ B
  have hne : A ≠ B := by
    have h1 : emb (1 : Fin 6) ∈ A := by
      dsimp [A, A_idx]
      apply Finset.mem_map.mpr
      simp
    have h1not : emb (1 : Fin 6) ∉ B := by
      dsimp [B, B_idx]
      intro h
      rcases Finset.mem_map.mp h with ⟨x, hx, hxeq⟩
      have hx_eq_1 : x = 1 := hf_inj hxeq
      rw [hx_eq_1] at hx
      have h1_not_mem : (1 : Fin 6) ∉ ({0, 2, 3, 4} : Finset (Fin 6)) := by decide
      exact h1_not_mem hx
    intro h_eq
    apply h1not
    rw [← h_eq]
    exact h1
  exact ⟨A, B, by rw [hcardA, hcardB], by rw [hA_prod, hB_prod], hne⟩
  

end Erdos494
