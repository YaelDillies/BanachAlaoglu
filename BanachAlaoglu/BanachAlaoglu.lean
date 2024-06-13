
import Mathlib

section Metrizability_lemma

variable (X : Type*) [TopologicalSpace X] [CompactSpace X]
--variable (g : X → ℝ) (g_cont : Continuous g)
variable (gs : ℕ → X → ℝ)
variable (gs_cont : ∀ n, Continuous (gs n))
variable (gs_sep : Set.SeparatesPoints (Set.range gs))
variable (gs_bdd : ∀ n x, |gs n x| ≤ 1)

noncomputable def ourMetric (x y : X) : ℝ :=
  ∑' n, 1/2^n * |gs n x - gs n y|

lemma outMetric_self_iff : ∀ {x y : X}, ourMetric X gs x y = 0 ↔ x = y := by
  intro x y
  constructor
  { intro sum
    rw[ourMetric] at sum
    --apply ENNReal.tsum_eq_zero.mpr n (1/2^n * |gs n x - gs n y|) at sum

    have sum_zero : ∀ n , ∑' n, 1/2^n * |gs n x - gs n y| = 0 → 1/2^n * |gs n x - gs n y| = 0 := by
      intro n sum
      --apply ENNReal.tsum_eq_zero.mp n (1/2^n * |gs n x - gs n y|)
      --rw[ENNReal.tsum_eq_zero] at sum
      sorry
    sorry
    }
  { intro x_eq_y
    rw[ourMetric, x_eq_y]
    simp
  }


lemma ourMetric_comm : ∀ x y : X, ourMetric X gs x y = ourMetric X gs y x := by
  intro x y
  rw[ourMetric, ourMetric]
  have abs_eq : ∀ n, |gs n x - gs n y| = |gs n y - gs n x| := by
    exact fun n ↦ abs_sub_comm (gs n x) (gs n y)
  rw[tsum_congr]
  intro b
  rw[abs_eq]


lemma ourMetric_triangle : ∀ x y z : X, ourMetric X gs x z ≤ ourMetric X gs x y + ourMetric X gs y z := by
  intro x y z
  rw[ourMetric, ourMetric, ourMetric]

  have plusminus_eq_zero : ∀ n, gs n y - gs n y = 0 := by
    intro n
    rw[sub_self (gs n y)]

  have plusminus_eq_self : ∀ n, |gs n x - gs n z| = |gs n x + (gs n y - gs n y) - gs n z| := by
    intro n
    specialize plusminus_eq_zero n
    rw[plusminus_eq_zero, add_zero]

  simp_rw[plusminus_eq_self]

  have tri_ineq : ∀ n, 1/2^n * |gs n x + (gs n y - gs n y) - gs n z| ≤ 1/2^n * |gs n x - gs n y| + 1/2^n * |gs n y - gs n z| := by
    intro n
    rw[← add_comm_sub, add_sub_assoc (gs n x - gs n y) (gs n y) (gs n z), ← mul_add]
    refine (mul_le_mul_left ?_).mpr ?_
    · refine one_div_pos.mpr ?refine_1.a
      refine pow_pos ?refine_1.a.H n
      linarith
    · apply abs_add (gs n x - gs n y) (gs n y - gs n z)

  have tsum_tri_ineq : ∑' (n : ℕ), 1 / 2 ^ n * |gs n x + (gs n y - gs n y) - gs n z| ≤
      ∑' (n : ℕ), (1 / 2 ^ n * |gs n x + - gs n y| + 1 / 2 ^ n * |gs n y - gs n z|) := by
    --simp_rw[tri_eq]
    apply tsum_le_tsum
    · exact tri_ineq
    · sorry
    · sorry

  have tsum_add_ineq : ∑' (n : ℕ), (1 / 2 ^ n * |gs n x + - gs n y| + 1 / 2 ^ n * |gs n y - gs n z|) =
      ∑' (n : ℕ), 1 / 2 ^ n * |gs n x - gs n y| + ∑' (n : ℕ), 1 / 2 ^ n * |gs n y - gs n z| := by
    rw[tsum_add]
    · rfl
    · sorry
    · sorry

  rw[tsum_add_ineq] at tsum_tri_ineq
  exact tsum_tri_ineq

--noncomputable instance ourMetric_space (MetricSpace X) := by

/- If X is compact, and there exists a seq of continuous real-valued functions that
separates points on X, then X is metrizable. -/
lemma X_metrizable (X 𝕜 : Type*) [NormedField 𝕜] [TopologicalSpace X] [CompactSpace X]
    (gs : ℕ → X → 𝕜) (gs_cont : ∀ n, Continuous (gs n))
    (gs_sep : Set.SeparatesPoints (Set.range gs)) :
    TopologicalSpace.MetrizableSpace X := by
  refine ⟨?_⟩
  sorry
/-
  letI : MetricSpace X := TopologicalSpace.MetrizableSpaceMetric X
  {dist := ourMetric,
  eq_of_dist_eq_zero := by ourMetric_self_iff.mp
  dist_self := by ourMetric_self_iff.mpr
  dist_comm := by ourMetric_comm
  dist_triangle := by ourMetric_triangle
  }-/





#check Set.range gs
#check Set.SeparatesPoints (Set.range gs)
#check X_metrizable
variable (x y : X)
#check @tsum ℝ _ _ ℕ (fun n ↦ 1/2^n * |gs n x - gs n y|)
#check tsum (fun n ↦ 1/2^n * |gs n x - gs n y|)
#check ENNReal.tsum_eq_zero.mpr
#check IsAbsoluteValue.abv_sub
#check TopologicalSpace.MetrizableSpace
#check TopologicalSpace.MetrizableSpace X
#check tsum_add


end Metrizability_lemma

section Seq_Banach_Alaoglu

--variable (𝕜 : Type*)
variable (V : Type*) [AddCommGroup V] [Module ℂ V] -- (V tvs)
variable [SeminormedAddCommGroup V] [NormedSpace ℂ V]
variable [TopologicalSpace.SeparableSpace V]
variable (K : Set (WeakDual ℂ V)) (K_cpt : IsCompact K)

example (ϕ : WeakDual ℂ V) (v : V) : False := by
  set a := ϕ v

  sorry
/- There exists a sequence of continuous functions that separates points on V*. -/
lemma exists_gs : ∃ (gs : ℕ → (WeakDual ℂ V) → ℂ), (∀ n, Continuous (gs n)) ∧ Set.SeparatesPoints (Set.range gs) := by

  --have exists_dense : TopologicalSpace.exists_countable_dense
  sorry

/- A compact subset of the dual V* of a separable space V is metrizable. -/
lemma subset_metrizable : TopologicalSpace.MetrizableSpace K := by
  have k_cpt' : CompactSpace K := by
    exact isCompact_iff_compactSpace.mp K_cpt
  set vs := TopologicalSpace.denseSeq V
  set gs : ℕ → K → ℂ := fun n ↦ fun ϕ ↦ (ϕ : WeakDual ℂ V) (vs n)
  apply X_metrizable K ℂ gs
  · intro n
    refine ⟨?_⟩
    intro s h
    refine IsOpen.preimage ?gs_cont.hf h
    /- from exists_gs-/
    sorry
  · rintro x y x_neq_y
    /-from exists_gs-/

    --have exists_sep : ∃ (gs : ℕ → (WeakDual ℂ V) → ℂ), Set.SeparatesPoints (Set.range gs) := by
    sorry

/- The closed unit ball is sequentially compact in V* if V is separable. -/
theorem WeakDual.isSeqCompact_closedBall (x' : NormedSpace.Dual ℂ V) (r : ℝ) :
    IsSeqCompact (WeakDual.toNormedDual ⁻¹' Metric.closedBall x' r) := by
  have b_isCompact : IsCompact (WeakDual.toNormedDual ⁻¹' Metric.closedBall x' r) := by
    apply WeakDual.isCompact_closedBall
  have b_isMetrizable : TopologicalSpace.MetrizableSpace (WeakDual.toNormedDual ⁻¹' Metric.closedBall x' r) := by
    --exact subset_metrizable V (WeakDual.toNormedDual ⁻¹' Metric.closedBall x' r)
    --exact subset_metrizable V (⇑toNormedDual ⁻¹' Metric.closedBall x' r) b_isCompact
    sorry
  /-have b_isSeqCompact : IsSeqCompact (WeakDual.toNormedDual ⁻¹' Metric.closedBall x' r) := by
    apply UniformSpace.isCompact_iff_isSeqCompact at b_isCompact
    --apply IsCompact.isSeqCompact at b_isCompact
    exact b_isCompact-/

  --apply UniformSpace.isCompact_iff_isSeqCompact at b_isCompact
  --apply IsCompact.isSeqCompact at b_isCompact
  --exact b_isSeqCompact


  sorry



#check Module.Dual
#check WeakDual ℂ V
#check Set (WeakDual ℂ V)
#check IsCompact
#check @UniformSpace.isCompact_iff_isSeqCompact
#check IsCompact.isSeqCompact
#check TopologicalSpace.exists_countable_dense
end Seq_Banach_Alaoglu
