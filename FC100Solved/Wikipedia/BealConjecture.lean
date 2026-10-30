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
# Beal conjecture

*Reference:* [Wikipedia](https://en.wikipedia.org/wiki/Beal_conjecture)
-/

namespace BealConjecture

def bealConjecture : Prop := ∀ {A B C x y z : ℕ},
    A ≠ 0 → B ≠ 0 → C ≠ 0 → 2 < x → 2 < y → 2 < z →
    A^x + B^y = C^z → 1 < Finset.gcd {A, B, C} id

/--
The **Beal Conjecture**: if we are given positive integers $A, B, C, x, y, z$ such that
$x, y, z > 2$ and $A^x + B^y = C^z$ then $A, B, C$ have a common divisor.
-/
@[category research open, AMS 11]
theorem beal_conjecture : bealConjecture := by
  sorry

/--
The Beal Conjecture implies Fermat's last theorem
-/
@[category textbook, AMS 11]
theorem flt_of_beal_conjecture (H : bealConjecture) :
    FermatLastTheorem := by
  -- Agent proof
  intro n hn
  have h2lt : 2 < n := by omega
  intro a b c ha hb hc h_eq
  have h_gcd := H ha hb hc h2lt h2lt h2lt h_eq
  set d := Finset.gcd {a, b, c} id with hd
  have hd_gt_one : 1 < d := h_gcd
  have hd_pos : 0 < d := by omega
  have hdvd_a : d ∣ a := Finset.gcd_dvd (by simp)
  have hdvd_b : d ∣ b := Finset.gcd_dvd (by simp)
  have hdvd_c : d ∣ c := Finset.gcd_dvd (by simp)
  set a' := a / d with ha'_def
  set b' := b / d with hb'_def
  set c' := c / d with hc'_def
  have ha_eq : a = d * a' := (Nat.mul_div_cancel' hdvd_a).symm
  have hb_eq : b = d * b' := (Nat.mul_div_cancel' hdvd_b).symm
  have hc_eq : c = d * c' := (Nat.mul_div_cancel' hdvd_c).symm
  have ha'_ne_zero : a' ≠ 0 := by
    intro hzero
    apply ha
    rw [ha_eq, hzero, mul_zero]
  have hb'_ne_zero : b' ≠ 0 := by
    intro hzero
    apply hb
    rw [hb_eq, hzero, mul_zero]
  have hc'_ne_zero : c' ≠ 0 := by
    intro hzero
    apply hc
    rw [hc_eq, hzero, mul_zero]
  have h_eq' : a' ^ n + b' ^ n = c' ^ n := by
    rw [ha_eq, hb_eq, hc_eq] at h_eq
    rw [mul_pow, mul_pow, mul_pow] at h_eq
    rw [← mul_add] at h_eq
    have h_d_pow_pos : 0 < d ^ n := pow_pos hd_pos n
    exact Nat.eq_of_mul_eq_mul_left h_d_pow_pos h_eq
  have h_gcd' := H ha'_ne_zero hb'_ne_zero hc'_ne_zero h2lt h2lt h2lt h_eq'
  have h_gcd_div_one : Finset.gcd {a, b, c} (fun x ↦ x / d) = 1 := by
    have ha_mem : a ∈ ({a, b, c} : Finset ℕ) := by simp
    exact Finset.gcd_div_id_eq_one ha_mem ha
  have h_image_eq : Finset.gcd ({a', b', c'} : Finset ℕ) id = Finset.gcd {a, b, c} (fun x ↦ x / d) := by
    calc
      Finset.gcd ({a', b', c'} : Finset ℕ) id = Finset.gcd ({a / d, b / d, c / d} : Finset ℕ) id := by
        simp [ha'_def, hb'_def, hc'_def]
      _ = Finset.gcd (({a, b, c} : Finset ℕ).image (fun x ↦ x / d)) id := by simp
      _ = Finset.gcd {a, b, c} (id ∘ (fun x ↦ x / d)) := by rw [Finset.gcd_image]
      _ = Finset.gcd {a, b, c} (fun x ↦ x / d) := rfl
  rw [h_image_eq, h_gcd_div_one] at h_gcd'
  omega

end BealConjecture
