
import Mathlib
--set_option maxHeartbeats 1000000


section assumption_on_the_normed_field


open Function

section Metrizability_lemma

variable {X 𝕜 : Type*} [TopologicalSpace X] [CompactSpace X] [NormedField 𝕜]
variable (gs : ℕ → X → 𝕜)
variable (gs_cont : ∀ n, Continuous (gs n))
variable (gs_sep : Set.SeparatesPoints (Set.range gs))
--variable (gs_bdd : ∀ n : ℕ, ∀ x : X, ‖gs n x‖  ≤ 1)

noncomputable def ourMetric (x y : X) : ℝ :=
  ∑' n, (1/2)^n * (‖gs n x - gs n y‖ / (1 + ‖gs n x - gs n y‖))
variable {gs}
lemma foo {x : ℝ} (hx : 0 ≤ x) : x / (1 + x) ≤ 1 := by
  calc
    _ = ((1 + x) - 1) / (1 + x) := by ring
    _ = 1 - 1 / (1 + x) := by rw [sub_div, div_self]; positivity
    _ ≤ 1 := sub_le_self _ (by positivity)

lemma bar : (∀ (i : ℕ), ‖(fun n ↦ (1 / 2) ^ n * (‖gs n x - gs n y‖ / (1 + ‖gs n x - gs n y‖))) i‖
            ≤ (fun n ↦ (1 / 2) ^ n) i)  := by
          intro i
          simpa [add_nonneg, abs_of_nonneg] using foo (norm_nonneg _)
lemma summable_if_bounded : Summable (fun n ↦ (1 / 2) ^ n * (‖gs n x - gs n y‖ / (1 + ‖gs n x - gs n y‖))) :=
  Summable.of_norm_bounded (fun n ↦  (1 / 2) ^ n) summable_geometric_two (bar)

lemma ourMetric_self_iff : ∀ {x y : X}, ourMetric gs x y = 0 ↔ x = y := by
  intro x y
  constructor
  · intro sum
    rw [ourMetric] at sum

    have sum_zero : ∑' n, (1/2)^n * (‖gs n x - gs n y‖ / (1 + ‖gs n x - gs n y‖))  = 0 → ∀ n, (1/2)^n * (‖gs n x - gs n y‖ / (1 + ‖gs n x - gs n y‖))  = 0 := by
      have tsum_zero (g : ℕ → ℝ) (h : ∀ (i : ℕ), g i ≥ 0) (h' : Summable g) :
          ∑' (i : ℕ), g i = 0 ↔ ∀ (i : ℕ), g i = 0 := by
        calc
          _ ↔ HasSum g 0 := (Summable.hasSum_iff h').symm
          _ ↔ g = 0 := hasSum_zero_iff_of_nonneg h
          _ ↔ _ := Function.funext_iff

      intro sum
      let f := fun n ↦ (1/2)^n * (‖gs n x - gs n y‖ / (1 + ‖gs n x - gs n y‖))

      have terms_pos n : f n >= 0 := by positivity

      apply (tsum_zero (fun n ↦ (1/2)^n * (‖gs n x - gs n y‖ / (1 + ‖gs n x - gs n y‖))) terms_pos summable_if_bounded).mp
      exact sum

    apply sum_zero at sum
    simp only [one_div, inv_pow, mul_eq_zero, inv_eq_zero, pow_eq_zero_iff', OfNat.ofNat_ne_zero,
      ne_eq, false_and, norm_eq_zero, sub_eq_zero, false_or] at sum
    contrapose! sum

    have blah n : ¬1 + ‖gs n x - gs n y‖ = 0 := by positivity

    --have : ∃ a, gs a ↑x ≠ gs a ↑y := by
    simpa [Set.mem_range, ne_eq, exists_exists_eq_and, imp_self, sub_eq_zero, blah] using gs_sep sum

  · intro x_eq_y
    simp [ourMetric, one_div, inv_pow, x_eq_y, sub_self, norm_zero, mul_zero, tsum_zero]

lemma ourMetric_comm : ∀ x y : X, ourMetric gs x y = ourMetric gs y x := by
  intro x y
  unfold ourMetric
  rw [tsum_congr]
  intro b
  rw [norm_sub_rev (gs b x) (gs b y)]

lemma ourMetric_triangle : ∀ x y z : X, ourMetric gs x z ≤ ourMetric gs x y + ourMetric gs y z := by
  intro x y z
  unfold ourMetric

  have plusminus_eq_self : ∀ n, ‖gs n x - gs n z‖  = ‖gs n x + (gs n y - gs n y) - gs n z‖  := by
    intro n
    simp only [sub_self, add_zero]

  simp_rw [plusminus_eq_self]

  have tri_ineq : ∀ n, (1/2)^n * ‖gs n x + (gs n y - gs n y) - gs n z‖  ≤ (1/2)^n * (‖gs n x - gs n y‖ / (1 + ‖gs n x - gs n y‖)) + (1/2)^n * ‖gs n y - gs n z‖  := by
    intro n
    rw [← add_comm_sub, add_sub_assoc (gs n x - gs n y) (gs n y) (gs n z) , ← mul_add]
    refine (mul_le_mul_left ?_).mpr ?_
    · refine pow_pos ?refine_1.H n
      linarith
    · sorry

  sorry



noncomputable def ourMetricSpace : MetricSpace X where
  dist := ourMetric gs
  dist_self := by
    intro x
    exact (ourMetric_self_iff gs_sep ).mpr rfl
  dist_comm := ourMetric_comm
  dist_triangle := ourMetric_triangle
  edist_dist := by simp only [← ENNReal.ofReal_coe_nnreal, NNReal.coe_mk, implies_true]
  eq_of_dist_eq_zero := by
    intro x y
    exact (ourMetric_self_iff gs_sep).mp

def kopio (X :Type*) (gs : ℕ → X → 𝕜) (gs_sep : Set.SeparatesPoints (Set.range gs))
    := X

def kopio.mk (X :Type*) (gs : ℕ → X → 𝕜) (gs_sep : Set.SeparatesPoints (Set.range gs))
    :
    X → kopio X gs gs_sep := id

def kopio.toOrigin (X :Type*) (gs : ℕ → X → 𝕜) (gs_sep : Set.SeparatesPoints (Set.range gs))
    :
    kopio X gs gs_sep → X := id

noncomputable instance : MetricSpace (kopio X gs gs_sep) := ourMetricSpace gs_sep

--example (f : X → ℝ) (g : X → ℝ) (hf : Continuous f) (hg : Continuous g) : Continuous ((f + g) : X × X → ℝ ) := by sorry

lemma cont_ourMetric (gs_cont : ∀ (n : ℕ), Continuous (gs n)) : Continuous (fun (p : X × X) ↦
    ourMetric gs p.1 p.2) := by

  apply @continuous_tsum ℕ (X × X) ℝ _ _ (fun (n : ℕ) ↦ (1 / 2) ^ n) _
      (fun n ↦ fun (x, y) ↦ (1 / 2) ^ n * (‖gs n x - gs n y‖ / (1 + ‖gs n x - gs n y‖))) ?_ (summable_geometric_two) ?_
  · intro i
    simp only [one_div, inv_pow]
    have cont_xy : Continuous (fun (x,y) ↦ ‖gs i x - gs i y‖) := by
      have : Continuous (fun (x,y) ↦ gs i x - gs i y) := by
        have := Continuous.add (by exact Continuous.fst' (gs_cont i)) (Continuous.snd' (Continuous.neg (gs_cont i)))
        ring_nf at this
        exact this

      exact Continuous.norm this

    exact Continuous.mul continuous_const (by sorry)

  · simp only [inv_pow, norm_mul, norm_inv, norm_pow, RCLike.norm_ofNat, norm_norm,
    Prod.forall]
    intro n a b
    simp only [one_div, norm_inv, RCLike.norm_ofNat, inv_pow, mul_comm]
    rw [mul_le_iff_le_one_left]
    · simpa [add_nonneg, abs_of_nonneg] using foo (norm_nonneg (gs n a - gs n b))

    · simp only [inv_pos, Nat.ofNat_pos, pow_pos]

lemma cont_ourMetric' (gs_cont : ∀ (n : ℕ), Continuous (gs n)) : Continuous (fun (p : X × X) ↦
    dist (kopio.mk X gs gs_sep p.1) (kopio.mk X gs gs_sep p.2)) := by
  exact cont_ourMetric gs_cont

example (X Y Z : Type*) [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (ϕ : X × Y → Z) (x : X) (hphi : Continuous ϕ) : Continuous (fun y ↦ ϕ ⟨x, y⟩ ) := by
  exact Continuous.along_snd hphi

lemma cont_kopio_mk (X :Type*) [TopologicalSpace X] [CompactSpace X] (gs : ℕ → X → 𝕜)
    (gs_sep : Set.SeparatesPoints (Set.range gs))
    (gs_cont : ∀ n, Continuous (gs n)) :
    Continuous (kopio.mk X gs gs_sep) := by
  apply Metric.continuous_iff'.mpr
  intro x ε hε
  have cont_dist : Continuous (fun y ↦ dist (kopio.mk X gs gs_sep y)
      (kopio.mk X gs gs_sep x)) := by
    apply Continuous.along_fst (cont_ourMetric' gs_sep gs_cont)

  have interval_open : IsOpen (Set.Iio ε) := by exact isOpen_Iio
  have := @IsOpen.mem_nhds X x _ _ (cont_dist.isOpen_preimage _ interval_open) (by simpa using hε)
  filter_upwards [this] with y hy using hy


lemma cont_kopio_toOrigin (X :Type*) [TopologicalSpace X] [CompactSpace X] (gs : ℕ → X → 𝕜)
    (gs_sep : Set.SeparatesPoints (Set.range gs))
    (gs_cont : ∀ n, Continuous (gs n)):
    Continuous (kopio.toOrigin X gs gs_sep) := by
  have symm : ∀ (s : Set X), kopio.toOrigin X gs gs_sep ⁻¹' s = kopio.mk X gs gs_sep '' s := by
    exact fun s ↦ Eq.symm (Set.EqOn.image_eq_self fun ⦃x⦄ ↦ congrFun rfl)
  have : ∀ (s : Set X), IsClosed s → IsClosed (kopio.toOrigin X gs gs_sep ⁻¹' s) := by
    intro M M_closed
    have M_cpt_X := IsClosed.isCompact M_closed
    rw [isCompact_iff_finite_subcover] at M_cpt_X
    have : ∀ s : Set (kopio X gs gs_sep), IsOpen s → IsOpen (kopio.mk X gs gs_sep ⁻¹' s) := by
      intro s
      have := cont_kopio_mk X gs gs_sep gs_cont
      rw [continuous_def] at this
      specialize this s
      exact this
    have : IsClosed (kopio.toOrigin X gs gs_sep ⁻¹' M) := by
      simp only [symm M]
      have M_image_cpt : IsCompact (kopio.mk X gs gs_sep '' M) := by
        apply isCompact_of_finite_subcover
        intro _ Us Usi_open
        simp only [kopio.mk, id_eq, Set.image_id']
        exact fun a ↦ M_cpt_X Us (fun i ↦ this (Us i) (Usi_open i)) a
      exact IsCompact.isClosed M_image_cpt
    exact this
  have cont_iff_closed := @continuous_iff_isClosed (kopio X gs gs_sep) X _ _ (kopio.toOrigin X gs gs_sep)
  rw [← cont_iff_closed] at this
  exact this


noncomputable def homeomorph_OurMetric :
  X ≃ₜ kopio X gs gs_sep where
    toFun := kopio.mk X gs gs_sep
    invFun := kopio.toOrigin X gs gs_sep
    left_inv := congrFun rfl
    right_inv := congrFun rfl
    continuous_toFun := cont_kopio_mk X gs gs_sep gs_cont
    continuous_invFun := cont_kopio_toOrigin X gs gs_sep gs_cont


lemma X_metrizable' (X 𝕜 : Type*) [NormedField 𝕜][TopologicalSpace X]
    [CompactSpace X] (gs : ℕ → X → 𝕜) (gs_cont : ∀ n, Continuous (gs n))
    (gs_sep : Set.SeparatesPoints (Set.range gs)): --gs_bdd ei pitäisi tarvita
    TopologicalSpace.MetrizableSpace X := by

  exact (homeomorph_OurMetric gs_cont gs_sep).embedding.metrizableSpace


/- If X is compact, and there exists a seq of continuous real-valued functions that
separates points on X, then X is metrizable. -/
lemma X_metrizable (X 𝕜 : Type*) [NormedField 𝕜][TopologicalSpace X]
    [CompactSpace X] (gs : ℕ → X → 𝕜) (gs_cont : ∀ n, Continuous (gs n))
    (gs_sep : Set.SeparatesPoints (Set.range gs)): --(gs_bdd : ∀ n x, ‖gs n x‖ ≤ 1) : --gs_bdd ei pitäisi tarvita
    TopologicalSpace.MetrizableSpace X := by


  --exact X_metrizable' X 𝕜 hs hs_cont hs_sep hs_bdd
  exact (homeomorph_OurMetric gs_cont gs_sep).embedding.metrizableSpace

end Metrizability_lemma


section Seq_Banach_Alaoglu
variable (𝕜 : Type*) [NontriviallyNormedField 𝕜] [ProperSpace 𝕜]
variable (V : Type*) [SeminormedAddCommGroup V] [NormedSpace 𝕜 V]
variable [TopologicalSpace.SeparableSpace V]
variable (K : Set (WeakDual 𝕜 V)) (K_cpt : IsCompact K)

/- There exists a sequence of continuous functions that separates points on V*. -/
lemma exists_gs : ∃ (gs : ℕ → (WeakDual 𝕜 V) → 𝕜),
    (∀ n, Continuous (gs n)) ∧ Set.SeparatesPoints (Set.range gs) := by
  set vs := TopologicalSpace.denseSeq V
  set gs : ℕ → K → 𝕜 := fun n ↦ fun ϕ ↦ (ϕ : WeakDual 𝕜 V) (vs n)
  use (fun n ↦ fun ϕ ↦ (ϕ : WeakDual 𝕜 V) (vs n))
  --use gs2
  constructor
  · exact fun n ↦ WeakDual.eval_continuous (vs n)
  · intro w y w_ne_y
    contrapose! w_ne_y
    simp only [Set.forall_mem_range] at w_ne_y
    have : Set.EqOn (⇑w) (⇑y) (Set.range vs) := by
      simp only [Set.eqOn_range]
      exact (Set.eqOn_univ (⇑w ∘ vs) (⇑y ∘ vs)).mp fun ⦃x⦄ _ ↦ w_ne_y x
    have := Continuous.ext_on (TopologicalSpace.denseRange_denseSeq V) (map_continuous w) (map_continuous y) this
    exact DFunLike.coe_fn_eq.mp this

/- A compact subset of the dual V* of a separable space V is metrizable. -/
lemma subset_metrizable : TopologicalSpace.MetrizableSpace K := by
  have k_cpt' : CompactSpace K := by exact isCompact_iff_compactSpace.mp K_cpt
  obtain ⟨gs, gs_cont, gs_sep⟩ := exists_gs 𝕜 V K
  let hs : ℕ → K → 𝕜 := fun n ↦ fun ϕ ↦ gs n (ϕ : WeakDual 𝕜 V)
  apply X_metrizable K 𝕜 hs
  · intro n
    exact Continuous.comp (gs_cont n) continuous_subtype_val
  · intro x y x_ne_y
    refine exists_exists_eq_and.mpr ?intro.intro.gs_sep.a
    unfold_let
    have subst : ∀ a : ℕ, (fun n ϕ ↦ gs n ↑ϕ) a x ≠ (fun n ϕ ↦ gs n ↑ϕ) a y → gs a x ≠ gs a y := by
      exact fun a a ↦ a
    simp only [subst]
    have : (∃ f ∈ Set.range gs, f x ≠ f y) → ∃ a, gs a ↑x ≠ gs a ↑y := by
        simp only [Set.mem_range, ne_eq, exists_exists_eq_and, imp_self]
    apply this
    apply gs_sep
    exact Subtype.coe_ne_coe.mpr x_ne_y

/- The closed unit ball is sequentially compact in V* if V is separable. -/
theorem WeakDual.isSeqCompact_closedBall [SequentialSpace V] (x' : NormedSpace.Dual 𝕜 V) (r : ℝ) :
    IsSeqCompact (WeakDual.toNormedDual ⁻¹' Metric.closedBall x' r) := by

  have b_isCompact : IsCompact (WeakDual.toNormedDual ⁻¹' Metric.closedBall x' r) := by
    apply WeakDual.isCompact_closedBall
  have b_isCompact' : CompactSpace (WeakDual.toNormedDual ⁻¹' Metric.closedBall x' r) := by
    exact isCompact_iff_compactSpace.mp b_isCompact

  have b_isMetrizable : TopologicalSpace.MetrizableSpace (WeakDual.toNormedDual ⁻¹' Metric.closedBall x' r) := by
    exact subset_metrizable 𝕜 V (⇑toNormedDual ⁻¹' Metric.closedBall x' r) b_isCompact

  have seq_cpt_space := @FirstCountableTopology.seq_compact_of_compact (WeakDual.toNormedDual ⁻¹' Metric.closedBall x' r)
      _ _ b_isCompact'

  have seq_cont_phi : SeqContinuous (fun φ : (WeakDual.toNormedDual ⁻¹' Metric.closedBall x' r) ↦ (φ : WeakDual 𝕜 V)) := by
    refine continuous_iff_seqContinuous.mp ?_
    exact continuous_subtype_val

  have seq_incl := IsSeqCompact.range seq_cont_phi
  convert seq_incl

  simp only [Subtype.range_coe_subtype, Set.mem_preimage, coe_toNormedDual, Metric.mem_closedBall]
  rfl

end Seq_Banach_Alaoglu

section inf_dim
variable {X 𝕜: Type*} [NormedAddCommGroup X] [NormedField 𝕜] [NormedSpace 𝕜 X] [CompleteSpace X]

/- If V is an infinite-dimensional Banach Space, then the dual V* is not metrizable -/
lemma dual_not_metrizable : ¬TopologicalSpace.MetrizableSpace (WeakDual 𝕜 X) := by
  by_contra
  have dual_first_countable := @TopologicalSpace.PseudoMetrizableSpace.firstCountableTopology (WeakDual 𝕜 X) _ _
  --have : ∀ a : (WeakDual 𝕜 X), (𝓝 a).IsCountablyGenerated := by sorry
  have dual_count := dual_first_countable.nhds_generated_countable
  specialize dual_count 0
  have dual_count_iff := @Filter.isCountablyGenerated_iff_exists_antitone_basis (WeakDual 𝕜 X) (nhds 0)
  --rw [this] at dual_count
  have dual_hasAntitone := dual_count_iff.mp dual_count
  obtain ⟨nhd_basis, hasAntitone⟩ := dual_hasAntitone

  obtain ⟨basis, basis_countable⟩ := dual_count

  sorry
  --have thisbasis : ℕ → Set (WeakDual 𝕜 X) :=

  --have := @Filter.HasBasis.exists_antitone_subbasis
  --have xs : (ℕ → X)
  --have phi : (WeakDual 𝕜 X)
  --have := Filter.HasBasis.exists_antitone_subbasis (|phi (xs n)|)
  --have phi : (WeakDual 𝕜 X)

 -- have := ∀ n : ℕ, Bn = Set.iInter (phi (xs n) )
  --have : ∃ xs : (ℕ → X), ∃ ε > 0,


#check Set.iUnion
#check Set.iInter
#check Filter.HasBasis.exists_antitone_subbasis
#check Filter.isCountablyGenerated_iff_exists_antitone_basis
#check NormedSpace 𝕜
end inf_dim
