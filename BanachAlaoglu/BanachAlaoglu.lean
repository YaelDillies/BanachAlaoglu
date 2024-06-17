
import Mathlib

section Seq_cpt_continuity

lemma IsSeqCompact.image {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y) (hf : Continuous f) {K : Set X}
    (hK : IsSeqCompact K) : IsSeqCompact (f '' K) := by
  sorry


lemma SeqCompactSpace.range {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [SeqCompactSpace X] (f : X → Y) (hf : Continuous f)
    : IsSeqCompact (Set.range f) := by
  sorry

end Seq_cpt_continuity

section Metrizability_lemma

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]
--variable (g : X → ℝ) (g_cont : Continuous g)
variable (gs : ℕ → X → ℝ)
variable (gs_cont : ∀ n, Continuous (gs n))
variable (gs_sep : Set.SeparatesPoints (Set.range gs))
variable (gs_bdd : ∀ n x, |gs n x| ≤ 1)

noncomputable def ourMetric (x y : X) : ℝ :=
  ∑' n, 1/2^n * |gs n x - gs n y|

lemma ourMetric_self_iff : ∀ {x y : X}, ourMetric gs x y = 0 ↔ x = y := by
  intro x y
  constructor
  { intro sum
    rw[ourMetric] at sum
    --apply ENNReal.tsum_eq_zero.mpr n (1/2^n * |gs n x - gs n y|) at sum
    --have foo := @ENNReal.tsum_eq_zero ℕ (fun n ↦ 1/2^n * |gs n x - gs n y|)
    have sum_zero : ∑' n, 1/2^n * |gs n x - gs n y| = 0 → ∀ n, 1/2^n * |gs n x - gs n y| = 0 := by
      intro sum


      sorry

    apply sum_zero at sum
    -- gs_sep
    have mul_const_eq_zero : ∀ (n : ℕ), 1 / 2 ^ n * |gs n x - gs n y| = 0 → |gs n x - gs n y| = 0 := by
      sorry
    --apply mul_const_eq_zero at sum
    --
    --abs_eq_zero
    sorry
    }
  { intro x_eq_y
    rw[ourMetric, x_eq_y]
    simp
  }


lemma ourMetric_comm : ∀ x y : X, ourMetric gs x y = ourMetric gs y x := by
  intro x y
  rw[ourMetric, ourMetric]
  have abs_eq : ∀ n, |gs n x - gs n y| = |gs n y - gs n x| := by
    exact fun n ↦ abs_sub_comm (gs n x) (gs n y)
  rw[tsum_congr]
  intro b
  rw[abs_eq]


lemma ourMetric_triangle : ∀ x y z : X, ourMetric gs x z ≤ ourMetric gs x y + ourMetric gs y z := by
  intro x y z
  rw[ourMetric, ourMetric, ourMetric]
/-
  have plusminus_eq_zero : ∀ n, gs n y - gs n y = 0 := by
    intro n
    rw[sub_self (gs n y)]
-/
  have plusminus_eq_self : ∀ n, |gs n x - gs n z| = |gs n x + (gs n y - gs n y) - gs n z| := by
    intro n
    simp [sub_self (gs n y)]
    --specialize plusminus_eq_zero n
    --rw[plusminus_eq_zero, add_zero]

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
    apply tsum_add
    · sorry
    · sorry


  rw[tsum_add_ineq] at tsum_tri_ineq
  exact tsum_tri_ineq
#check ourMetric
--noncomputable instance ourMetric_space (MetricSpace X) := by
noncomputable def ourMetricSpace : MetricSpace X where
  dist := ourMetric gs
  dist_self := by
    intro x
    exact (@ourMetric_self_iff X gs x x ).mpr rfl
  dist_comm := by sorry
  dist_triangle := by sorry
  edist_dist := by simp [← ENNReal.ofReal_coe_nnreal]
  eq_of_dist_eq_zero := by sorry


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
#check @ENNReal.tsum_eq_zero
#check IsAbsoluteValue.abv_sub
#check TopologicalSpace.MetrizableSpace
#check TopologicalSpace.MetrizableSpace X
#check MeasureTheory.LevyProkhorov
#check Summable


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
  set vs := TopologicalSpace.denseSeq V
  set gs : ℕ → K → ℂ := fun n ↦ fun ϕ ↦ (ϕ : WeakDual ℂ V) (vs n)

  -- TopologicalSpace.exists_countable_dense

  sorry


/- A compact subset of the dual V* of a separable space V is metrizable. -/
lemma subset_metrizable : TopologicalSpace.MetrizableSpace K := by
  have k_cpt' : CompactSpace K := by
    exact isCompact_iff_compactSpace.mp K_cpt
  set vs := TopologicalSpace.denseSeq V
  set gs : ℕ → K → ℂ := fun n ↦ fun ϕ ↦ (ϕ : WeakDual ℂ V) (vs n)
  apply X_metrizable K ℂ gs
  · intro n
    /-have phi_c : Continuous fun ϕ ↦ (ϕ : WeakDual ℂ V) (vs n) := by
      exact WeakDual.eval_continuous (vs n)-/
    /-have := @Continuous.comp K (WeakDual ℂ V) ℂ _ _ _ (fun ψ ↦ ψ) (fun ϕ ↦ (ϕ : WeakDual ℂ V) (vs n)) phi_c (by exact
      continuous_subtype_val)-/
    exact Continuous.comp (WeakDual.eval_continuous (vs n)) continuous_subtype_val
    --have gs_c : Continuous fun n ↦ fun ϕ ↦ (ϕ : WeakDual ℂ V) (vs n) := by
      --exact { isOpen_preimage := fun s a ↦ trivial }

    --exact { gs := fun n ↦ fun ϕ ↦ (ϕ : WeakDual ℂ V) (vs n) }

  · rintro x y x_neq_y


    --have exists_sep : ∃ (gs : ℕ → (WeakDual ℂ V) → ℂ), Set.SeparatesPoints (Set.range gs) := by
    sorry
#check Continuous.restrict
#check @WeakDual.toNormedDual ℂ _ V _ _
/- The closed unit ball is sequentially compact in V* if V is separable. -/
theorem WeakDual.isSeqCompact_closedBall (x' : NormedSpace.Dual ℂ V) (r : ℝ) :
    IsSeqCompact (WeakDual.toNormedDual ⁻¹' Metric.closedBall x' r) := by

  let B := (WeakDual.toNormedDual ⁻¹' Metric.closedBall x' r)


  let ι : (WeakDual.toNormedDual ⁻¹' Metric.closedBall x' r) → WeakDual ℂ V := by
    intro ϕ
    let ψ := ϕ.val
    convert ψ
    sorry

  have b_isCompact : IsCompact (WeakDual.toNormedDual ⁻¹' Metric.closedBall x' r) := by
    apply WeakDual.isCompact_closedBall
  have b_isCompact' : CompactSpace (WeakDual.toNormedDual ⁻¹' Metric.closedBall x' r) := by
    exact isCompact_iff_compactSpace.mp b_isCompact

  have b_isMetrizable : TopologicalSpace.MetrizableSpace (WeakDual.toNormedDual ⁻¹' Metric.closedBall x' r) := by
    --exact subset_metrizable V (WeakDual.toNormedDual ⁻¹' Metric.closedBall x' r)
    --exact subset_metrizable V (⇑toNormedDual ⁻¹' Metric.closedBall x' r) b_isCompact

    sorry
  --apply UniformSpace.isCompact_iff_isSeqCompact at b_isCompact
  have seq_cpt_space := @FirstCountableTopology.seq_compact_of_compact (WeakDual.toNormedDual ⁻¹' Metric.closedBall x' r)
      _ _ b_isCompact'
  have seq_cpt := (@seqCompactSpace_iff (WeakDual.toNormedDual ⁻¹' Metric.closedBall x' r) _ ).mp seq_cpt_space


  --fun ϕ ↦ ϕ


  -- have seq_incl := @SeqCompactSpace.range (WeakDual.toNormedDual ⁻¹' Metric.closedBall x' r)
     -- (WeakDual ℂ V) _ _ _ (Subtype.val ((WeakDual.toNormedDual ⁻¹' Metric.closedBall x' r) : Type _))




/-
  apply IsCompact.isSeqCompact at b_isCompact
  · exact b_isCompact
  · sorry
-/
  sorry


#check IsSeqCompact
#check Module.Dual
#check WeakDual ℂ V
#check Set (WeakDual ℂ V)
#check IsCompact
#check @UniformSpace.isCompact_iff_isSeqCompact
#check IsCompact.isSeqCompact
#check TopologicalSpace.exists_countable_dense
#check subset_metrizable

end Seq_Banach_Alaoglu
