import FormalConjectures.ErdosProblems.«878»

/-!
# `max f ≠ max F` at `x = 210` (Barreto)

For every `n ≤ 210` we have `f n ≤ 441` (the maximum is `f 210 = 128 + 81 + 125 + 49 = 383`); this
is a finite check done by the kernel. On the other hand `{128, 189, 125}` is a set of pairwise
coprime integers in `[2, 210]` whose prime factors all divide `210 = 2 * 3 * 5 * 7`, so
`F 210 ≥ 128 + 189 + 125 = 442`.
-/

namespace OMA.E878

open Erdos878

set_option maxRecDepth 100000 in
lemma f_le : ∀ n ∈ Finset.range 211, f n ≤ 441 := by decide +kernel

private def witness : Finset ℕ := {128, 189, 125}

lemma F_ge : 442 ≤ F 210 := by
  unfold F
  refine le_trans (by decide) (Finset.le_sup (b := witness) ?_)
  simp only [Finset.mem_filter, Finset.mem_powerset]
  refine ⟨by decide, by decide, ?_, ?_⟩
  · change ∀ a ∈ witness, ∀ b ∈ witness, a ≠ b → a.Coprime b
    decide
  · intro a ha p hp hpa
    have support : ∀ m ∈ witness, m.primeFactors ⊆ Nat.primeFactors 210 := by decide +kernel
    have ha0 : a ≠ 0 := fun e => (show 0 ∉ witness by decide) (e ▸ ha)
    exact Nat.dvd_of_mem_primeFactors (support a ha (Nat.mem_primeFactors.2 ⟨hp, hpa, ha0⟩))

end OMA.E878

theorem OMA.solution : type_of% @Erdos878.erdos_878.parts.iii_all := by
  intro h
  have h1 : Erdos878.maxUpTo Erdos878.f 210 ≤ 441 := by
    unfold Erdos878.maxUpTo
    exact Finset.sup_le OMA.E878.f_le
  have h2 : 442 ≤ Erdos878.maxUpTo Erdos878.F 210 := by
    unfold Erdos878.maxUpTo
    exact le_trans OMA.E878.F_ge
      (Finset.le_sup (f := Erdos878.F) (Finset.mem_range.2 (by norm_num)))
  have h3 := h 210
  omega
