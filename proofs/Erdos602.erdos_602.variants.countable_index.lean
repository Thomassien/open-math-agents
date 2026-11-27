import FormalConjectures.ErdosProblems.«602»

-- Problem: Countable index set case.
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/602.lean:156 (declaration Erdos602.erdos_602.variants.countable_index)
-- Credit: @LordMike (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

theorem OMA.solution : type_of% @Erdos602.erdos_602.variants.countable_index := by
  intro α A hA hfin _
  -- the part of `A i` outside all earlier sets is infinite
  have hinf : ∀ i, (A i \ ⋃ j ∈ Finset.range i, A j).Infinite := by
    intro i
    have overlap : (A i ∩ ⋃ j ∈ Finset.range i, A j).Finite := by
      simp only [Set.inter_iUnion]
      exact Set.Finite.biUnion (Finset.finite_toSet _) fun j hj =>
        hfin i j (Finset.mem_range.mp hj).ne'
    exact ((hA i).2.sdiff overlap).mono fun _ hx => ⟨hx.1, fun h => hx.2 ⟨hx.1, h⟩⟩
  have hpick : ∀ i, ∃ a b : α, a ∈ A i \ ⋃ j ∈ Finset.range i, A j ∧
      b ∈ A i \ ⋃ j ∈ Finset.range i, A j ∧ a ≠ b := by
    intro i
    obtain ⟨a, ha⟩ := (hinf i).nonempty
    obtain ⟨b, hb, hba⟩ := ((hinf i).sdiff (Set.finite_singleton a)).nonempty
    exact ⟨a, b, ha, hb, fun h => hba (h ▸ rfl)⟩
  choose a b ha hb hab using hpick
  have key : ∀ i j, a i ≠ b j := by
    intro i j h
    rcases lt_trichotomy i j with hij | rfl | hij
    · exact (hb j).2 (Set.mem_iUnion₂.2 ⟨i, Finset.mem_range.mpr hij, h ▸ (ha i).1⟩)
    · exact hab i h
    · exact (ha i).2 (Set.mem_iUnion₂.2 ⟨j, Finset.mem_range.mpr hij, h.symm ▸ (hb j).1⟩)
  classical
  let f : α → Fin 2 := fun n => if ∃ i, n = b i then 1 else 0
  refine ⟨f, fun i hMono => ?_⟩
  simpa [f, key, show ∃ j, b i = b j from ⟨i, rfl⟩] using
    hMono (a i) (ha i).1 (b i) (hb i).1
