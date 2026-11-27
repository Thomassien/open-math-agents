import FormalConjectures.ErdosProblems.«1136»

/-! Multiples of three avoid sums that are powers of two and have density one third. -/

open Filter Topology

theorem OMA.solution : type_of% @Erdos1136.erdos_1136.variants.multiples_of_three := by
  constructor
  · intro a ha b hb k hsum
    have hdiv : 3 ∣ a + b := dvd_add ha hb
    rw [hsum] at hdiv
    exact (show ¬ (3 : ℕ) ∣ 2 by decide)
      ((show Nat.Prime 3 by decide).dvd_of_dvd_pow hdiv)
  · have hcount (n : ℕ) :
        ({m : ℕ | 3 ∣ m} ∩ Set.Iio n).ncard = (n + 2) / 3 := by
      have hset :
          {m : ℕ | 3 ∣ m} ∩ Set.Iio n =
            (fun k : ℕ => 3 * k) '' Set.Iio ((n + 2) / 3) := by
        ext m
        constructor
        · rintro ⟨⟨k, rfl⟩, hk⟩
          exact ⟨k, show k < (n + 2) / 3 by
            have h : 3 * k < n := hk
            omega, rfl⟩
        · rintro ⟨k, hk, rfl⟩
          exact ⟨⟨k, rfl⟩, show 3 * k < n by
            have h : k < (n + 2) / 3 := hk
            omega⟩
      rw [hset, Set.ncard_image_of_injective _]
      · simp
      · intro a b hab
        change 3 * a = 3 * b at hab
        omega
    simp only [Set.HasDensity, Set.partialDensity, Set.inter_univ, Set.univ_inter,
      hcount, Set.ncard_Iio_nat]
    -- Apply the floor asymptotic at n + 2, then account for the shifted denominator.
    have hfloor := (tendsto_nat_floor_mul_div_atTop (R := ℝ)
        (a := 1 / 3) (by norm_num)).comp
      (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2))
    have hcorr : Tendsto (fun n : ℕ => (1 : ℝ) + 2 / n) atTop (𝓝 1) := by
      simpa [div_eq_mul_inv] using tendsto_const_nhds.add
        (tendsto_one_div_atTop_nhds_zero_nat.const_mul (2 : ℝ))
    rw [← mul_one (1 / 3 : ℝ)]
    refine (hfloor.mul hcorr).congr ?_
    intro n
    change (⌊(1 / 3 : ℝ) * ((n + 2 : ℕ) : ℝ)⌋₊ : ℝ) / ((n + 2 : ℕ) : ℝ) *
        (1 + 2 / n) = _
    rw [one_div_mul_eq_div, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num,
      Nat.floor_div_natCast, Nat.floor_natCast, Nat.cast_add]
    by_cases hn : n = 0
    · simp [hn]
    · have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
      have hn2 : (n : ℝ) + 2 ≠ 0 := by positivity
      field_simp
      <;> ring
