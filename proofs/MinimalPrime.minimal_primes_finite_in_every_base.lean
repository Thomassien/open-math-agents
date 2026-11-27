import FormalConjectures.Wikipedia.MinimalPrime

-- Credit: @harshshah1618

open MinimalPrime

theorem OMA.solution : type_of% @MinimalPrime.minimal_primes_finite_in_every_base := by
  intro b
  classical
  by_cases hb : 2 ≤ b
  · by_contra hf
    let e := (show {p : ℕ | IsMinimalPrimeInBase b p}.Infinite from hf).natEmbedding _
    have hw := Set.PartiallyWellOrderedOn.partiallyWellOrderedOn_sublistForall₂ Eq
      (Finset.range b).partiallyWellOrderedOn
    obtain ⟨m, n, hmn, hsub⟩ := hw.exists_lt (f := fun i => Nat.digits b (e i))
      (fun i d hd => Finset.mem_range.mpr (Nat.digits_lt_base (by omega) hd))
    rw [List.sublistForall₂_iff] at hsub
    obtain ⟨_, heq, hl⟩ := hsub
    rw [List.forall₂_eq_eq_eq] at heq
    exact (e n).2.2.2 ⟨e m, (e m).2.2.1,
      fun h => hmn.ne (e.injective (Subtype.ext h)), heq ▸ hl⟩
  · exact Set.finite_empty.subset (fun p hp => (hb hp.1).elim)
