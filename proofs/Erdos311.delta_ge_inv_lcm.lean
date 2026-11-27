import FormalConjectures.ErdosProblems.«311»

-- Problem: Erdős Problem 311 — delta ge inv lcm
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/311.lean (declaration Erdos311.delta_ge_inv_lcm)
-- Credit: @ashnewmanjones (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open Finset

-- L * (1 - Σ 1/n) is an integer when every n ∈ A divides L.
lemma OMA.lcm_mul_sub_sum_int (N : ℕ) (A : Finset ℕ) (hA : A ⊆ Icc 1 N) :
    ∃ k : ℤ, (((Icc 1 N).lcm id : ℕ) : ℝ) * (1 - ∑ n ∈ A, (1 : ℝ) / n) = k := by
  set L : ℕ := (Icc 1 N).lcm id with hL
  refine ⟨(L : ℤ) - ((∑ n ∈ A, L / n : ℕ) : ℤ), ?_⟩
  rw [Int.cast_sub, Int.cast_natCast, Int.cast_natCast, Nat.cast_sum, mul_sub, mul_one,
    Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun n hn => ?_
  have hnI := hA hn
  have hn0 : n ≠ 0 := Nat.ne_of_gt (Finset.mem_Icc.mp hnI).1
  have hdvd : n ∣ L := Finset.dvd_lcm (f := id) hnI
  rw [Nat.cast_div hdvd (by exact_mod_cast hn0)]
  ring

theorem OMA.solution : type_of% @Erdos311.delta_ge_inv_lcm := by
  intro N
  set L : ℕ := (Icc 1 N).lcm id with hL
  have hLpos : 0 < L := by
    rw [hL, Nat.pos_iff_ne_zero, Ne, Finset.lcm_eq_zero_iff]
    simp
  have hLR : (0 : ℝ) < L := by exact_mod_cast hLpos
  unfold Erdos311.delta
  apply le_csInf
  · exact ⟨1, one_ne_zero, ∅, Finset.empty_subset _, by simp⟩
  · rintro x ⟨hx, A, hA, rfl⟩
    obtain ⟨k, hk⟩ := OMA.lcm_mul_sub_sum_int N A hA
    rw [← hL] at hk
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact (mul_ne_zero hLR.ne' (abs_ne_zero.mp hx)) (by simpa only [Int.cast_zero] using hk)
    have hk1 : (1 : ℝ) ≤ |(k : ℝ)| := by
      rw [← Int.cast_abs]
      exact_mod_cast Int.one_le_abs hk0
    rw [div_le_iff₀ hLR]
    calc (1 : ℝ) ≤ |(k : ℝ)| := hk1
      _ = |1 - ∑ n ∈ A, (1 : ℝ) / n| * L := by
        rw [← hk, abs_mul, abs_of_pos hLR, mul_comm]
