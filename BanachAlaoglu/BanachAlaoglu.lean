
import Mathlib
set_option maxHeartbeats 1000000
section Seq_cpt_continuity

--variable (ys : ℕ → f '' K)


lemma IsSeqCompact.image {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y)
    (hf : SeqContinuous f) {K : Set X} (hK : IsSeqCompact K) : IsSeqCompact (f '' K) := by
  rw [IsSeqCompact]
  intro ys hy

  --#check ys n
  sorry

example {X : Type*} [TopologicalSpace X] [SeqCompactSpace X] : IsSeqCompact (Set.univ : Set X) := by
  exact (seqCompactSpace_iff X).mp ‹SeqCompactSpace X›

lemma SeqCompactSpace.range {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [SeqCompactSpace X]
    (f : X → Y) (hf : SeqContinuous f) : IsSeqCompact (Set.range f) := by
  have := (@seqCompactSpace_iff X _ ).mp ‹SeqCompactSpace X›
  have foo : Set.range f = (f '' Set.univ) := by exact Eq.symm Set.image_univ
  rw[foo]
  apply IsSeqCompact.image f hf this


#check SeqCompactSpace
#check IsSeqCompact
#check @SeqCompactSpace.tendsto_subseq
--#check fun n ↦ (xs n)

end Seq_cpt_continuity



section Metrizability_lemma
--set_option diagnostics true

variable {X 𝕜 : Type*} [TopologicalSpace X] [CompactSpace X] [NormedField 𝕜]
--variable (g : X → ℝ) (g_cont : Continuous g)
variable (gs : ℕ → X → 𝕜)
variable (gs_cont : ∀ n, Continuous (gs n))
variable (gs_sep : Set.SeparatesPoints (Set.range gs))
variable (gs_bdd : ∀ n : ℕ, ∀ x : X, ‖gs n x‖  ≤ 1)

noncomputable def ourMetric (x y : X) : ℝ :=
  ∑' n, 1/2^n * ‖gs n x - gs n y‖


lemma ourMetric_self_iff : ∀ {x y : X}, ourMetric gs x y = 0 ↔ x = y := by
  intro x y
  constructor
  · intro sum
    rw [ourMetric] at sum

    have sum_zero : ∑' n, 1/2^n * ‖gs n x - gs n y‖  = 0 → ∀ n, 1/2^n * ‖gs n x - gs n y‖  = 0 := by
      intro sum
      let f := fun n ↦ 1/2^n * ‖gs n x - gs n y‖
      have summable_metric : Summable f := by
        sorry
      have terms_pos : ∀ n : ℕ, f n >= 0 := by
        have : ∀ n : ℕ, ‖gs n x - gs n y‖ >= 0 := by
          intro n
          apply norm_nonneg
        intro n
        refine mul_nonneg ?ha (this n)
        norm_num

      have tsum_zero := @tsum_pos ℕ  ℝ _ _ _ _ f summable_metric terms_pos
      contrapose! tsum_zero

      sorry
      /-have foo : (¬(∀ (i : ℕ), 0 < f i → 0 < ∑' (i : ℕ), f i)) = (∀ (i : ℕ), 0 = ∑' (i : ℕ), f i → 0 = f i) := by
        refine propext ?_
        constructor
        · intro h1
          exact fun i a ↦ False.elim (h1 tsum_zero)
        · intro h1
          intro h2
-/

/-
      have foo2 : ∀ (i : ℕ), 0 = ∑' (i : ℕ), f i → 0 = f i := by
        contrapose! tsum_zero
        rw [foo]
        exact tsum_zero
        sorry
-/

      --contrapose tsum_zero
      --rw [foo]



     -- sorry
      --contrapose tsum_zero
      --:= @tsum_eq_zero_iff ℕ ℝ _ _ _ (fun n ↦ 1/2^n * |gs n x - gs n y|) summable_metric

    apply sum_zero at sum
    -- gs_sep
    have mul_zero : ∀ a b : ℝ , a * b = 0 ↔ a = 0 ∨ b = 0 := by
      exact fun a b ↦ mul_eq_zero

    have mul_const_eq_zero : ∀ (n : ℕ), 1 / 2 ^ n * ‖gs n x - gs n y‖ = 0 → ‖gs n x - gs n y‖  = 0 := by
      intro n
      intro sum
      rw [mul_zero (1 / 2 ^ n) (‖gs n x - gs n y‖)] at sum

      have foo : ‖gs n x - gs n y‖ = 0 := by
        have foo2 : ∀ n : ℕ, 1 / 2 ^n ≥ 0 := by exact fun n ↦ Nat.zero_le (1 / 2 ^ n)
        rcases sum with h1 | h2
        ·

          sorry
        · exact h2


      sorry
      --apply mul_eq_zero at sum
    --abs_eq_zero
    --apply sum_zero at mul_const_eq_zero
    have foo : ∀ n, ‖gs n x - gs n y‖  = 0 := by
      intro n
      apply mul_const_eq_zero
      specialize sum n
      exact sum

    simp at sum
    simp_rw [sub_eq_zero] at sum
    have eq_sep : ∀ (n : ℕ), gs n x = gs n y → x = y := by sorry

    sorry

  · intro x_eq_y
    rw [ourMetric, x_eq_y]
    simp

#check tsum_eq_zero_iff
#check HasSum.summable
#check HasSum
#check mul_eq_zero

lemma ourMetric_comm : ∀ x y : X, ourMetric gs x y = ourMetric gs y x := by
  intro x y
  rw [ourMetric, ourMetric]
  have abs_eq : ∀ n, ‖gs n x - gs n y‖ = ‖gs n y - gs n x‖  := by
    intro n
    exact norm_sub_rev (gs n x) (gs n y)
    --exact fun n ↦ no_sub_comm (gs n x) (gs n y)
  rw [tsum_congr]
  intro b
  rw [abs_eq]


lemma ourMetric_triangle : ∀ x y z : X, ourMetric gs x z ≤ ourMetric gs x y + ourMetric gs y z := by
  intro x y z
  rw [ourMetric, ourMetric, ourMetric]
/-
  have plusminus_eq_zero : ∀ n, gs n y - gs n y = 0 := by
    intro n
    rw[sub_self (gs n y)]
-/
  have plusminus_eq_self : ∀ n, ‖gs n x - gs n z‖  = ‖gs n x + (gs n y - gs n y) - gs n z‖  := by
    intro n
    simp [sub_self (gs n y)]
    --specialize plusminus_eq_zero n
    --rw[plusminus_eq_zero, add_zero]

  simp_rw [plusminus_eq_self]

  have tri_ineq : ∀ n, 1/2^n * ‖gs n x + (gs n y - gs n y) - gs n z‖  ≤ 1/2^n * ‖gs n x - gs n y‖ + 1/2^n * ‖gs n y - gs n z‖  := by
    intro n
    rw [← add_comm_sub, add_sub_assoc (gs n x - gs n y) (gs n y) (gs n z) , ← mul_add]
    refine (mul_le_mul_left ?_).mpr ?_
    · refine one_div_pos.mpr ?refine_1.a
      refine pow_pos ?refine_1.a.H n
      linarith
    · exact norm_add_le (gs n x - gs n y) (gs n y - gs n z)
      --apply norm_add (gs n x - gs n y) (gs n y - gs n z)

  have tsum_tri_ineq : ∑' (n : ℕ), 1 / 2 ^ n * ‖gs n x + (gs n y - gs n y) - gs n z‖  ≤
      ∑' (n : ℕ), (1 / 2 ^ n * ‖gs n x + - gs n y‖ + 1 / 2 ^ n * ‖gs n y - gs n z‖) := by
    --simp_rw[tri_eq]
    apply tsum_le_tsum
    · simp only [← sub_eq_add_neg]
      exact tri_ineq
    · have abs_plus : ∀ n, ‖gs n x + (gs n y - gs n y) - gs n z‖  ≤ ‖gs n x‖  + ‖gs n z‖ := by
        intro n
        simp [norm_sub_le (gs n x) (gs n z)]
      --specialize gs_bdd n x

      have foo : ∀ n, ‖gs n x‖  + ‖gs n z‖  ≤ 1 + 1 := by
        intro n
        have gs_bdd' := gs_bdd
        specialize gs_bdd n x
        specialize gs_bdd' n z
        exact add_le_add gs_bdd gs_bdd'

      have foo2 : ∀ n, ‖gs n x + (gs n y - gs n y) - gs n z‖  ≤ 1 + 1 := by
        exact fun n ↦
          Preorder.le_trans ‖gs n x + (gs n y - gs n y) - gs n z‖ (‖gs n x‖ + ‖gs n z‖) (1 + 1)
            (abs_plus n) (foo n) --le_trans
      ring_nf at foo2



      set f_bound : ℕ → ℝ  := fun n ↦ (1 / 2 ^ n)
      set f_bound_mul : ℕ → ℝ := fun n ↦ 2 * (1 / 2 ^ n)

      have := (@summable_geometric_iff_norm_lt_one ℝ _ (1 / 2)).mpr
      have summable2 := summable_geometric_two
      have f_summable : Summable f_bound := by sorry

      have f_mul_summable := @Summable.const_smul ℝ ℕ ℝ _ _ _ _ _ (fun n ↦ (1 / 2 ^ n)) 2 f_summable
      --refine [smul_eq_mul ℝ 2 (fun n ↦ 1 / 2 ^ n)] at f_mul_summable
      have f_mul_summable2 : Summable (fun n ↦ 2 * (1 / 2 ^ n)) := by


        --rw [smul_eq_mul ℝ 2 (fun n ↦ 1 / 2 ^ n)] at f_mul_summable
        sorry
      have summable_if_bounded := @Summable.of_norm_bounded ℕ ℝ _ _ (fun n ↦ 1/2^n) (fun n ↦ (1 / 2 ^ n)) f_summable
      --have summable_if_bounded := @Summable.of_norm_bounded ℕ ℝ _ _ (fun n ↦ 1/2^n * ‖gs n x + (gs n y - gs n y) - gs n z‖) (fun n ↦ 2 * (1 / 2 ^ n)) f_mul_summable2

      have : ∀ (i : ℕ), ‖(fun n ↦ (1 : ℝ) / 2 ^ n) i‖ ≤ (fun n ↦ 1 / 2 ^ n) i := by
        intro i
        --apply Real.norm_of_nonneg (fun n ↦ (1 : ℝ) / 2 ^ n)
        sorry

      have : (∀ (i : ℕ), ‖(fun n ↦ 1 / 2 ^ n * ‖gs n x + (gs n y - gs n y) - gs n z‖) i‖ ≤ f_bound_mul i) := by
        intro i

        sorry
      sorry
    · sorry


      --summable_geometric_iff_norm_lt_1

  have tsum_add_ineq : ∑' (n : ℕ), (1 / 2 ^ n * ‖gs n x + - gs n y‖ + 1 / 2 ^ n * ‖gs n y - gs n z‖) =
      ∑' (n : ℕ), 1 / 2 ^ n * ‖gs n x - gs n y‖ + ∑' (n : ℕ), 1 / 2 ^ n * ‖gs n y - gs n z‖ := by

    --apply tsum_add
    · sorry



  rw [tsum_add_ineq] at tsum_tri_ineq
  exact tsum_tri_ineq

--#check le_trans
#check Summable.of_norm_bounded
#check @summable_geometric_iff_norm_lt_one
#check Summable.const_smul



noncomputable def ourMetricSpace : MetricSpace X where
  dist := ourMetric gs
  dist_self := by
    intro x
    exact (@ourMetric_self_iff X 𝕜 _ gs x x ).mpr rfl
  dist_comm := by
    intro x y
    exact (@ourMetric_comm X 𝕜 _ gs x y)
  dist_triangle := by
    intro x y z
    exact (@ourMetric_triangle X 𝕜 _ gs gs_bdd x y z)
  edist_dist := by simp [← ENNReal.ofReal_coe_nnreal]
  eq_of_dist_eq_zero := by
    intro x y
    exact (@ourMetric_self_iff X 𝕜 _ gs x y).mp

def kopio (X :Type*) (gs : ℕ → X → 𝕜) (gs_sep : Set.SeparatesPoints (Set.range gs)) (gs_bdd : ∀ n x, ‖gs n x‖ ≤ 1) := X

def kopio.mk (X :Type*) (gs : ℕ → X → 𝕜) (gs_sep : Set.SeparatesPoints (Set.range gs)) (gs_bdd : ∀ n x, ‖gs n x‖ ≤ 1) :
    X → kopio  X gs gs_sep gs_bdd := id

def kopio.toOrigin (X :Type*) (gs : ℕ → X → 𝕜) (gs_sep : Set.SeparatesPoints (Set.range gs)) (gs_bdd : ∀ n x, ‖gs n x‖ ≤ 1) :
    kopio X gs gs_sep gs_bdd → X := id

noncomputable instance : MetricSpace (kopio X gs gs_sep gs_bdd) := ourMetricSpace gs gs_bdd


lemma cont_kopio_mk (X :Type*) [TopologicalSpace X] [CompactSpace X] (gs : ℕ → X → 𝕜) (gs_sep : Set.SeparatesPoints (Set.range gs)) (gs_bdd : ∀ n x, ‖gs n x‖ ≤ 1) :
    Continuous (kopio.mk X gs gs_sep gs_bdd) := by
    rw[kopio.mk]
    refine continuous_id_of_le ?h

    sorry

lemma cont_kopio_toOrigin (X :Type*) [TopologicalSpace X] [CompactSpace X] (gs : ℕ → X → 𝕜) (gs_sep : Set.SeparatesPoints (Set.range gs)) (gs_bdd : ∀ n x, ‖gs n x‖ ≤ 1) :
    Continuous (kopio.toOrigin X gs gs_sep gs_bdd) := by
    rw [kopio.toOrigin]
    refine continuous_id_of_le ?h
    sorry

#check continuous_id

noncomputable def homeomorph_OurMetric :
  X ≃ₜ kopio X gs gs_sep gs_bdd where
    toFun := kopio.mk X gs gs_sep gs_bdd
    invFun := kopio.toOrigin X gs gs_sep gs_bdd
    left_inv := by exact congrFun rfl
    right_inv := by exact congrFun rfl
    continuous_toFun := by exact cont_kopio_mk X gs gs_sep gs_bdd
    continuous_invFun := by exact cont_kopio_toOrigin X gs gs_sep gs_bdd
/-
noncomputable def homeomorph_OurMetric :
    ProbabilityMeasure Ω ≃ₜ LevyProkhorov (ProbabilityMeasure Ω) where
  toFun := ProbabilityMeasure.toLevyProkhorov (Ω := Ω)
  invFun := LevyProkhorov.toProbabilityMeasure (Ω := Ω)
  left_inv := congrFun rfl
  right_inv := congrFun rfl
  continuous_toFun := ProbabilityMeasure.continuous_toLevyProkhorov
  continuous_invFun := LevyProkhorov.continuous_toProbabilityMeasure
-/

--#check X ≃ₜ ourMetricSpace gs
#check ourMetricSpace gs

/- If X is compact, and there exists a seq of continuous real-valued functions that
separates points on X, then X is metrizable. -/
lemma X_metrizable (X 𝕜 : Type*) [NormedField 𝕜] [TopologicalSpace X] [CompactSpace X]
    (gs : ℕ → X → 𝕜) (gs_cont : ∀ n, Continuous (gs n))
    (gs_sep : Set.SeparatesPoints (Set.range gs)) :
    TopologicalSpace.MetrizableSpace X := by
  --refine ⟨?_⟩
  have := @homeomorph_OurMetric X 𝕜 _ _ _ gs gs_sep gs_bdd


  sorry
/-
instance (X : Type*) [TopologicalSpace X] [MetrizableSpace X] [SeparableSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] :
    PseudoMetrizableSpace (ProbabilityMeasure X) :=
  letI : PseudoMetricSpace X := TopologicalSpace.pseudoMetrizableSpacePseudoMetric X
  (homeomorph_probabilityMeasure_levyProkhorov (Ω := X)).inducing.pseudoMetrizableSpace
-/


#check Set.range gs
#check Set.SeparatesPoints (Set.range gs)
#check X_metrizable
variable (x y : X)
#check @tsum ℝ _ _ ℕ (fun n ↦ 1/2^n * ‖gs n x - gs n y‖)
#check tsum (fun n ↦ 1/2^n * ‖gs n x - gs n y‖)
#check @ENNReal.tsum_eq_zero
#check IsAbsoluteValue.abv_sub
#check TopologicalSpace.MetrizableSpace
#check TopologicalSpace.MetrizableSpace X
#check MeasureTheory.LevyProkhorov
#check Summable


end Metrizability_lemma

section Seq_Banach_Alaoglu

--variable (𝕜 : Type*)
variable (V : Type*) [SeminormedAddCommGroup V] [NormedSpace ℂ V]
variable [TopologicalSpace.SeparableSpace V]
variable (K : Set (WeakDual ℂ V)) (K_cpt : IsCompact K)

example (ϕ : WeakDual ℂ V) (v : V) : False := by
  set a := ϕ v

  sorry
/- There exists a sequence of continuous functions that separates points on V*. -/
lemma exists_gs : ∃ (gs : ℕ → (WeakDual ℂ V) → ℂ), (∀ n, Continuous (gs n)) ∧ Set.SeparatesPoints (Set.range gs) := by
  set vs := TopologicalSpace.denseSeq V
  set gs : ℕ → K → ℂ := fun n ↦ fun ϕ ↦ (ϕ : WeakDual ℂ V) (vs n)
  constructor
  · sorry
  · sorry
  -- TopologicalSpace.exists_countable_dense
  --exact Continuous.comp (WeakDual.eval_continuous (vs n)) continuous_subtype_val



/- A compact subset of the dual V* of a separable space V is metrizable. -/
lemma subset_metrizable : TopologicalSpace.MetrizableSpace K := by
  have k_cpt' : CompactSpace K := by
    exact isCompact_iff_compactSpace.mp K_cpt
  set vs := TopologicalSpace.denseSeq V
  have := exists_gs V K
  obtain ⟨gs, gs_cont, gs_sep⟩ := this
  letI hs : ℕ → K → ℂ := fun n ↦ fun ϕ ↦ gs n (ϕ : WeakDual ℂ V)

  apply X_metrizable K ℂ hs
  · intro n
    exact Continuous.comp (gs_cont n) continuous_subtype_val
    /-have phi_c : Continuous fun ϕ ↦ (ϕ : WeakDual ℂ V) (vs n) := by
      exact WeakDual.eval_continuous (vs n)-/
    /-have := @Continuous.comp K (WeakDual ℂ V) ℂ _ _ _ (fun ψ ↦ ψ) (fun ϕ ↦ (ϕ : WeakDual ℂ V) (vs n)) phi_c (by exact
      continuous_subtype_val)-/
  · intro x y x_ne_y
    --refine exists_exists_eq_and.mpr ?intro.intro.gs_sep.a
    unfold_let
    have gs_sep2 : ∃n, gs n (x:↑K) ≠ gs n (y:↑K) := by

      sorry
    /-have hs_sep : (Set.range hs).SeparatesPoints := by
      unfold_let
      intro x y xny
      refine Set.exists_range_iff.mpr ?_
      sorry-/
    --dsimp
    --exact hs_sep
    sorry




    --have exists_sep : ∃ (gs : ℕ → (WeakDual ℂ V) → ℂ), Set.SeparatesPoints (Set.range gs) := by

#check Continuous.restrict
#check @WeakDual.toNormedDual ℂ _ V _ _


/- The closed unit ball is sequentially compact in V* if V is separable. -/
theorem WeakDual.isSeqCompact_closedBall (x' : NormedSpace.Dual ℂ V) (r : ℝ) :
    IsSeqCompact (WeakDual.toNormedDual ⁻¹' Metric.closedBall x' r) := by

  --let B := (WeakDual.toNormedDual ⁻¹' Metric.closedBall x' r)
  --let ι : (WeakDual.toNormedDual ⁻¹' Metric.closedBall x' r) → WeakDual ℂ V := fun ϕ ↦ ϕ

  have b_isCompact : IsCompact (WeakDual.toNormedDual ⁻¹' Metric.closedBall x' r) := by
    apply WeakDual.isCompact_closedBall
  have b_isCompact' : CompactSpace (WeakDual.toNormedDual ⁻¹' Metric.closedBall x' r) := by
    exact isCompact_iff_compactSpace.mp b_isCompact

  have b_isMetrizable : TopologicalSpace.MetrizableSpace (WeakDual.toNormedDual ⁻¹' Metric.closedBall x' r) := by
    exact subset_metrizable V (⇑toNormedDual ⁻¹' Metric.closedBall x' r) b_isCompact

  have seq_cpt_space := @FirstCountableTopology.seq_compact_of_compact (WeakDual.toNormedDual ⁻¹' Metric.closedBall x' r)
      _ _ b_isCompact'
  --have seq_cpt := (@seqCompactSpace_iff (WeakDual.toNormedDual ⁻¹' Metric.closedBall x' r) _ ).mp seq_cpt_space

  have seq_cont_phi : SeqContinuous (fun φ : (WeakDual.toNormedDual ⁻¹' Metric.closedBall x' r) ↦ (φ : WeakDual ℂ V)) := by
    refine continuous_iff_seqContinuous.mp ?_
    exact continuous_subtype_val

  have seq_incl := @SeqCompactSpace.range (WeakDual.toNormedDual ⁻¹' Metric.closedBall x' r)
                  (WeakDual ℂ V) _ _ _ (fun φ ↦ φ) seq_cont_phi
  convert seq_incl
  --constructor
  --· exact fun a ↦ seq_incl
  --· rw [seqCompactSpace_iff]



  simp only [Subtype.range_coe_subtype, Set.mem_preimage, coe_toNormedDual, Metric.mem_closedBall]
  rfl
  --sorry


#check Continuous.seqContinuous
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
