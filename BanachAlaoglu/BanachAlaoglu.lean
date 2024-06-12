
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
    /-
    have sum_zero : ∀ n , ∑' n, 1/2^n * |gs n x - gs n y| = 0 → 1/2^n * |gs n x - gs n y| = 0 := by
      intro n
      intro sum
      exact fun n ↦ ENNReal.tsum_eq_zero.mpr n (1/2^n * |gs n x - gs n y|)
      rw[ENNReal.tsum_eq_zero] at sum
    -/

    }
  { intro x_eq_y
    rw[ourMetric, x_eq_y]
    --rw[x_eq_y]
    simp
  /-ring_nf
    rw[abs_zero]
    ring_nf
    rw[tsum_zero]-/
  }
  --apply tsum_pos ( 1/2^n * |gs n x - gs n y|)

lemma ourMetric_comm : ∀ x y : X, ourMetric X gs x y = ourMetric X gs y x := by
  intro x y
  rw[ourMetric, ourMetric]
  have abs_eq : ∀ n, |gs n x - gs n y| = |gs n y - gs n x| := by
    exact fun n ↦ abs_sub_comm (gs n x) (gs n y)
  --rw[abs_sub_comm (gs n x) (gs n y)]
  rw[tsum_congr]
  intro b
  rw[abs_eq]
  --fun b ↦ congrArg (HMul.hMul (1 / 2 ^ b)) (abs_eq b)
--(gs n x) (gs n y)

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

  have tri_eq : ∀ n, |gs n x + (gs n y - gs n y) - gs n z| ≤ (|gs n x - gs n y| + |gs n y - gs n z|) := by
    intro n
    rw[← add_comm_sub, add_sub_assoc (gs n x - gs n y) (gs n y) (gs n z)]
    apply abs_add (gs n x - gs n y) (gs n y - gs n z)

  --simp_rw[tri_eq]
  --apply fun n ↦ tri_eq
  --simp_rw[← add_assoc (gs n x) (gs n y) (- gs n y)]
    --fun n ↦ sub_self (gs n y)
  --refine Real.tsum_le_of_sum_range_le ?hf ?h
  --apply tsum_sum
  sorry


/- If X is compact, and there exists a seq of continuous real-valuen functions that
separates points on X, then X is metrizable. -/
lemma X_metrizable (X 𝕜 : Type*) [NormedField 𝕜] [TopologicalSpace X] [CompactSpace X]
    (gs : ℕ → X → 𝕜) (gs_cont : ∀ n, Continuous (gs n))
    (gs_sep : Set.SeparatesPoints (Set.range gs)) :
    TopologicalSpace.MetrizableSpace X := by
  refine ⟨?_⟩

  sorry

#check Set.range gs
#check Set.SeparatesPoints (Set.range gs)
#check X_metrizable
variable (x y : X)
#check @tsum ℝ _ _ ℕ (fun n ↦ 1/2^n * |gs n x - gs n y|)
#check tsum (fun n ↦ 1/2^n * |gs n x - gs n y|)
#check ENNReal.tsum_eq_zero.mpr
#check IsAbsoluteValue.abv_sub
#check TopologicalSpace.MetrizableSpace

end Metrizability_lemmas

section Seq_Banach_Alaoglu

--variable (𝕜 : Type*)
variable (V : Type*) [AddCommGroup V] [Module ℂ V] -- V tvs
variable [SeminormedAddCommGroup V] [NormedSpace ℂ V]
variable [TopologicalSpace.SeparableSpace V]
variable (K : Set (WeakDual ℂ V)) (K_cpt : IsCompact K)

example (ϕ : WeakDual ℂ V) (v : V) : False := by
  set a := ϕ v

  sorry
/- There exists a sequence of continuous functions that separates points on V*. -/
lemma exists_gs : ∃ (gs : ℕ → (WeakDual ℂ V) → ℂ), (∀ n, Continuous (gs n)) ∧ Set.SeparatesPoints (Set.range gs) := by

  sorry

/- A compact subset of the dual V* of a separable space V is metrizable. -/
lemma subset_metrizable : TopologicalSpace.MetrizableSpace K := by
  have k_cpt' : CompactSpace K := by
    refine ⟨?_⟩
    sorry
  set vs := TopologicalSpace.denseSeq V
  set gs : ℕ → K → ℂ := fun n ↦ fun ϕ ↦ (ϕ : WeakDual ℂ V) (vs n)
  apply X_metrizable K ℂ gs
  · intro n
    refine ⟨?_⟩
    intro s
    intro h
    --rw[gs]
    sorry
  · rintro x y x_neq_y
    --use gs n
    have exists_sep : ∃ (gs : ℕ → (WeakDual ℂ V) → ℂ), Set.SeparatesPoints (Set.range gs) := by

      sorry

    sorry

/- The closed unit ball is sequentially compact in V* if V is separable. -/
theorem WeakDual.isSeqCompact_closedBall (x' : NormedSpace.Dual ℂ V) (r : ℝ) :
    IsSeqCompact (WeakDual.toNormedDual ⁻¹' Metric.closedBall x' r) := by
  have b_isCompact : IsCompact (WeakDual.toNormedDual ⁻¹' Metric.closedBall x' r) := by
    apply WeakDual.isCompact_closedBall
  have b_isMetrizable : TopologicalSpace.MetrizableSpace (WeakDual.toNormedDual ⁻¹' Metric.closedBall x' r) := by
    --apply subset_metrizable V (WeakDual.toNormedDual ⁻¹' Metric.closedBall x' r)
    sorry
  --apply UniformSpace.isCompact_iff_isSeqCompact at b_isCompact
  apply IsCompact.isSeqCompact at b_isCompact
  exact b_isCompact

  sorry



#check Module.Dual
#check WeakDual ℂ V
#check Set (WeakDual ℂ V)
#check IsCompact
#check UniformSpace.isCompact_iff_isSeqCompact
#check IsCompact.isSeqCompact
end Seq_Banach_Alaoglu
