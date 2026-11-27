import OMAStatements.S_mse_4462775

/-!
# A compact surjective linear map has finite-dimensional codomain

Credit: @lucasfreund2-cmd
Source: Mathematics Stack Exchange question 4462775.
The classical argument is also given in Ryszard Szwarc's answer of 31 May 2022.
Continuity is derived from compactness, then the open mapping theorem gives
local compactness of the codomain.
-/

open Set Filter Topology

theorem OMA.solution : type_of% @OMA.S_mse_4462775.main := by
  intro 𝕜 X Y _ _ _ _ _ _ _ T hT hcompact
  obtain ⟨D, hD, hTD⟩ := hcompact
  have hc : IsCompactOperator T :=
    (isCompactOperator_iff_image_ball_subset_compact T zero_lt_one).2 ⟨D, hD, hTD⟩
  let L : X →L[𝕜] Y := ⟨T, hc.continuous⟩
  have hopen : IsOpen (L '' Metric.ball 0 1) := L.isOpenMap hT _ Metric.isOpen_ball
  have hDnhds : D ∈ 𝓝 (0 : Y) :=
    mem_of_superset (hopen.mem_nhds ⟨0, by simp, by simp⟩) hTD
  let : LocallyCompactSpace Y := hD.locallyCompactSpace_of_mem_nhds_of_addGroup hDnhds
  exact FiniteDimensional.of_locallyCompactSpace 𝕜
