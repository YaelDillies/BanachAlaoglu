
import Mathlib

open Function

section Metrizability_lemma

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]
variable {E : ℕ → Type*} [∀ n, NormedAddCommGroup (E n)]
variable (fs : ∀ n, X → E n)
variable (fs_cont : ∀ n, Continuous (fs n))
variable (fs_sep : (∀ ⦃x y⦄, x≠y → ∃ n, fs n x ≠ fs n y))

private noncomputable def ourMetric (x y : X) : ℝ :=
  ∑' n, (1/2)^n * min (dist (fs n x) (fs n y)) 1

variable {fs}

lemma ourMetric_bdd {x y} : (∀ (i : ℕ), ‖(fun n ↦ (1 / 2) ^ n * min (dist (fs n x) (fs n y)) 1) i‖
  ≤ (fun n ↦ (1 / 2) ^ n) i) := by
  intro i
  simp only [one_div, inv_pow, Real.norm_eq_abs, abs_mul, abs_inv, abs_pow, Nat.abs_ofNat, inv_pos,
    Nat.ofNat_pos, pow_pos, mul_le_iff_le_one_right]
  rw [abs_of_nonneg (by positivity)]
  exact min_le_right (dist (fs i x) (fs i y)) 1

lemma summable_if_bounded {x y} : Summable fun n ↦ (1 / 2) ^ n * min (dist (fs n x) (fs n y)) 1 :=
  Summable.of_norm_bounded (fun n ↦ (1 / 2) ^ n) summable_geometric_two (ourMetric_bdd)

lemma ourMetric_self_iff : ∀ {x y : X}, ourMetric fs x y = 0 ↔ x = y := by
  intro x y
  constructor
  · intro sum
    rw [ourMetric] at sum
    have sum_zero : ∑' n, (1/2)^n * min (dist (fs n x) (fs n y)) 1 = 0 →
       ∀ n, (1/2)^n * min (dist (fs n x) (fs n y)) 1 = 0 := by
      have tsum_zero (g : ℕ → ℝ) (h : ∀ (i : ℕ), g i ≥ 0) (h' : Summable g) :
          ∑' (i : ℕ), g i = 0 ↔ ∀ (i : ℕ), g i = 0 := by
        calc
          _ ↔ HasSum g 0 := (Summable.hasSum_iff h').symm
          _ ↔ g = 0 := hasSum_zero_iff_of_nonneg h
          _ ↔ _ := Function.funext_iff
      intro sum
      let f := fun n ↦ (1/2)^n * min (dist (fs n x) (fs n y)) 1
      have terms_pos n : f n >= 0 := by positivity
      apply (tsum_zero (fun n ↦ (1/2)^n * min (dist (fs n x) (fs n y)) 1) (terms_pos)
          summable_if_bounded).mp
      exact sum
    apply sum_zero at sum
    simp only [one_div, inv_pow, mul_eq_zero, inv_eq_zero, pow_eq_zero_iff', OfNat.ofNat_ne_zero,
      ne_eq, false_and, norm_eq_zero, sub_eq_zero, false_or] at sum
    contrapose! sum
    specialize fs_sep sum
    obtain ⟨a, fs_neq⟩ := fs_sep
    use a
    by_contra h
    cases' le_or_lt (dist (fs a x) (fs a y)) 1 with h1 h2
    · simp only [min_eq_left_iff.mpr h1, dist_eq_zero, one_div, inv_pow, mul_eq_zero, inv_eq_zero,
        pow_eq_zero_iff', OfNat.ofNat_ne_zero, ne_eq, false_and, false_or] at *
      exact fs_neq h
    · linarith [min_eq_right_iff.mpr (LT.lt.le h2)]

  · intro x_eq_y
    simp [ourMetric, one_div, inv_pow, x_eq_y, sub_self, norm_zero, mul_zero, tsum_zero]


lemma ourMetric_comm : ∀ x y : X, ourMetric fs x y = ourMetric fs y x := by
  intro x y
  unfold ourMetric
  rw [tsum_congr]
  intro b
  rw [dist_comm]

lemma ourMetric_triangle {x y z} : ourMetric fs x z ≤ ourMetric fs x y + ourMetric fs y z := by
  unfold ourMetric
  have tri_ineq n : (1/2)^n * min (dist (fs n x) (fs n z)) 1
      ≤ (1/2)^n * min (dist (fs n x) (fs n y)) 1 + (1/2)^n * min (dist (fs n y) (fs n z)) 1 := by
    rw [← mul_add, mul_le_mul_left]
    simp only [ne_eq, min_le_iff]
    cases' (min_cases (dist (fs n x) (fs n z)) 1)
    · cases' (min_cases (dist (fs n x) (fs n y)) 1) with h1 h2
      · obtain ⟨eq_dist, _⟩ := h1
        rw [eq_dist]
        cases' (min_cases (dist (fs n y) (fs n z)) 1) with h1 h2
        · obtain ⟨eq_dist, _⟩ := h1
          rw [eq_dist]
          left
          exact dist_triangle (fs n x) (fs n y) (fs n z)
        · obtain ⟨eq_one, _⟩ := h2
          rw [eq_one]
          right
          simp [add_le_add_left]
          positivity
      · obtain ⟨eq_one, _⟩ := h2
        rw [eq_one]
        cases' (min_cases (dist (fs n y) (fs n z)) 1) with h1 h2
        · obtain ⟨eq_dist, _⟩ := h1
          rw [eq_dist]
          right
          simp [add_le_add_left]
          positivity
        · obtain ⟨eq_one, _⟩ := h2
          rw [eq_one]
          right
          simp [add_le_add_left]

    · cases' (min_cases (dist (fs n x) (fs n y)) 1) with h1 h2
      · obtain ⟨eq_dist, _⟩ := h1
        rw [eq_dist]
        cases' (min_cases (dist (fs n y) (fs n z)) 1) with h1 h2
        · obtain ⟨eq_dist, _⟩ := h1
          rw [eq_dist]
          left
          exact dist_triangle (fs n x) (fs n y) (fs n z)
        · obtain ⟨eq_one, _⟩ := h2
          rw [eq_one]
          right
          simp [add_le_add_left]
          positivity
      · obtain ⟨eq_one, _⟩ := h2
        rw [eq_one]
        cases' (min_cases (dist (fs n y) (fs n z)) 1) with h1 h2
        · obtain ⟨eq_dist, _⟩ := h1
          rw [eq_dist]
          right
          simp [add_le_add_left]
          positivity
        · obtain ⟨eq_one, _⟩ := h2
          rw [eq_one]
          right
          simp [add_le_add_left]
    · positivity
  rw [← tsum_add]
  apply tsum_le_tsum
  · exact fun i ↦ tri_ineq i
  · exact summable_if_bounded
  · simpa [mul_add] using Summable.add summable_if_bounded summable_if_bounded
  exact summable_if_bounded
  exact summable_if_bounded

noncomputable def ourMetricSpace : MetricSpace X where
  dist := ourMetric fs
  dist_self := by
    intro x
    exact (ourMetric_self_iff fs_sep ).mpr rfl
  dist_comm := ourMetric_comm
  dist_triangle x y z := ourMetric_triangle
  edist_dist := by simp only [← ENNReal.ofReal_coe_nnreal, NNReal.coe_mk, implies_true]
  eq_of_dist_eq_zero := by
    intro x y
    exact (ourMetric_self_iff fs_sep).mp

def kopio (X :Type*) (fs : ∀n, X → E n) (fs_sep : (∀ ⦃x y⦄, x≠y → ∃ n, fs n x ≠ fs n y))
    := X

def kopio.mk (X :Type*) (fs : ∀n, X → E n) (fs_sep : (∀ ⦃x y⦄, x≠y → ∃ n, fs n x ≠ fs n y)) :
    X → kopio X fs fs_sep := id

def kopio.toOrigin (X :Type*) (fs : ∀n, X → E n) (fs_sep : (∀ ⦃x y⦄, x≠y → ∃ n, fs n x ≠ fs n y)) :
    kopio X fs fs_sep → X := id

noncomputable instance : MetricSpace (kopio X fs fs_sep) := ourMetricSpace fs_sep

--example (f : X → ℝ) (g : X → ℝ) (hf : Continuous f) (hg : Continuous g) : Continuous ((f + g) : X × X → ℝ ) := by sorry
lemma continuous_ourMetric (fs_continuous : ∀ n, Continuous (fs n)) :
    Continuous (fun (p : X × X) ↦ ourMetric fs p.1 p.2) := by
  unfold ourMetric
  refine continuous_tsum (by fun_prop) summable_geometric_two ?_
  simp only [one_div, inv_pow, abs_mul, abs_inv, abs_pow, Real.norm_eq_abs, Nat.abs_ofNat,
    inv_pos, Nat.ofNat_pos, pow_pos, mul_le_iff_le_one_right, Prod.forall]
  intro n a b
  rw [abs_of_nonneg (by positivity)]
  exact min_le_right _ _

lemma continuous_ourMetric' (fs_cont : ∀ (n : ℕ), Continuous (fs n)) : Continuous (fun (p : X × X) ↦
    dist (kopio.mk X fs fs_sep p.1) (kopio.mk X fs fs_sep p.2)) := by
  exact continuous_ourMetric fs_cont

example (X Y Z : Type*) [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (ϕ : X × Y → Z) (x : X) (hphi : Continuous ϕ) : Continuous (fun y ↦ ϕ ⟨x, y⟩ ) := by
  exact Continuous.along_snd hphi

lemma cont_kopio_mk (fs_sep : (∀ ⦃x y⦄, x≠y → ∃ n, fs n x ≠ fs n y)) (fs_cont : ∀ n, Continuous (fs n)) :
    Continuous (kopio.mk X fs fs_sep) := by
  apply Metric.continuous_iff'.mpr
  intro x ε hε
  have cont_dist : Continuous (fun y ↦ dist (kopio.mk X fs fs_sep y)
      (kopio.mk X fs fs_sep x)) := by
    apply Continuous.along_fst (continuous_ourMetric' fs_sep fs_cont)

  have interval_open : IsOpen (Set.Iio ε) := by exact isOpen_Iio
  have := @IsOpen.mem_nhds X x _ _ (cont_dist.isOpen_preimage _ interval_open) (by simpa using hε)
  filter_upwards [this] with y hy using hy

lemma cont_kopio_toOrigin (fs_sep : (∀ ⦃x y⦄, x≠y → ∃ n, fs n x ≠ fs n y)) (fs_cont : ∀ n, Continuous (fs n)) :
    Continuous (kopio.toOrigin X fs fs_sep) := by
  have symm : ∀ (s : Set X), kopio.toOrigin X fs fs_sep ⁻¹' s = kopio.mk X fs fs_sep '' s := by
    exact fun s ↦ Eq.symm (Set.EqOn.image_eq_self fun ⦃x⦄ ↦ congrFun rfl)
  have : ∀ (s : Set X), IsClosed s → IsClosed (kopio.toOrigin X fs fs_sep ⁻¹' s) := by
    intro M M_closed
    have M_cpt_X := IsClosed.isCompact M_closed
    rw [isCompact_iff_finite_subcover] at M_cpt_X
    have : ∀ s : Set (kopio X fs fs_sep), IsOpen s → IsOpen (kopio.mk X fs fs_sep ⁻¹' s) := by
      intro s
      have := cont_kopio_mk fs_sep fs_cont
      rw [continuous_def] at this
      specialize this s
      exact this
    have : IsClosed (kopio.toOrigin X fs fs_sep ⁻¹' M) := by
      --simp only [symm M]
      have M_image_cpt : IsCompact (kopio.mk X fs fs_sep '' M) := by
        apply isCompact_of_finite_subcover
        intro _ Us Usi_open
        simp only [kopio.mk, id_eq, Set.image_id']
        exact fun a ↦ M_cpt_X Us (fun i ↦ this (Us i) (Usi_open i)) a
      simpa [symm M] using IsCompact.isClosed M_image_cpt
    exact this
  have cont_iff_closed := @continuous_iff_isClosed (kopio X fs fs_sep) X _ _ (kopio.toOrigin X fs fs_sep)
  rw [← cont_iff_closed] at this
  exact this


noncomputable def homeomorph_OurMetric :
  X ≃ₜ kopio X fs fs_sep where
    toFun := kopio.mk X fs fs_sep
    invFun := kopio.toOrigin X fs fs_sep
    left_inv := congrFun rfl
    right_inv := congrFun rfl
    continuous_toFun := cont_kopio_mk fs_sep fs_cont
    continuous_invFun := cont_kopio_toOrigin fs_sep fs_cont


lemma X_metrizable' (fs : ∀ n, X → E n) (fs_cont : ∀ n, Continuous (fs n))
    (fs_sep : (∀ ⦃x y⦄, x≠y → ∃ n, fs n x ≠ fs n y)): --fs_bdd ei pitäisi tarvita
    TopologicalSpace.MetrizableSpace X := by

  exact (homeomorph_OurMetric fs_cont fs_sep).embedding.metrizableSpace


/- If X is compact, and there exists a seq of continuous real-valued functions that
separates points on X, then X is metrizable. -/
lemma X_metrizable (fs : ∀ n, X → E n) (fs_cont : ∀ n, Continuous (fs n))
    (fs_sep : (∀ ⦃x y⦄, x≠y → ∃ n, fs n x ≠ fs n y)): --(fs_bdd : ∀ n x, ‖fs n x‖ ≤ 1) : --fs_bdd ei pitäisi tarvita
    TopologicalSpace.MetrizableSpace X := by


  --exact X_metrizable' X (E n) hs hs_cont hs_sep hs_bdd
  exact (homeomorph_OurMetric fs_cont fs_sep).embedding.metrizableSpace

end Metrizability_lemma


section Seq_Banach_Alaoglu
variable (𝕜 : Type*) [NontriviallyNormedField 𝕜] [ProperSpace 𝕜]
variable (V : Type*) [SeminormedAddCommGroup V] [NormedSpace 𝕜 V]
variable [TopologicalSpace.SeparableSpace V]
variable (K : Set (WeakDual 𝕜 V)) (K_cpt : IsCompact K)

--have : ∀ x y : V, x≠ y, ∃ n, fs n x ≠ fs n y

/- There exists a sequence of continuous functions that separates points on V*. -/
lemma exists_fs : ∃ (fs : ℕ → (WeakDual 𝕜 V) → 𝕜),
    (∀ n, Continuous (fs n)) ∧ (∀ ⦃x y⦄, x≠y → ∃ n, fs n x ≠ fs n y) := by
  set vs := TopologicalSpace.denseSeq V
  set fs : ℕ → K → 𝕜 := fun n ↦ fun ϕ ↦ (ϕ : WeakDual 𝕜 V) (vs n)
  use (fun n ↦ fun ϕ ↦ (ϕ : WeakDual 𝕜 V) (vs n))
  --use fs2
  constructor
  · exact fun n ↦ WeakDual.eval_continuous (vs n)
  · intro w y w_ne_y
    contrapose! w_ne_y
    --simp only [Set.forall_mem_range] at w_ne_y
    have : Set.EqOn (⇑w) (⇑y) (Set.range vs) := by
      simp only [Set.eqOn_range]
      exact (Set.eqOn_univ (⇑w ∘ vs) (⇑y ∘ vs)).mp fun ⦃x⦄ _ ↦ w_ne_y x
    have := Continuous.ext_on (TopologicalSpace.denseRange_denseSeq V) (map_continuous w) (map_continuous y) this
    exact DFunLike.coe_fn_eq.mp this

/- A compact subset of the dual V* of a separable space V is metrizable. -/
lemma subset_metrizable : TopologicalSpace.MetrizableSpace K := by
  have k_cpt' : CompactSpace K := by exact isCompact_iff_compactSpace.mp K_cpt
  obtain ⟨fs, fs_cont, fs_sep⟩ := exists_fs 𝕜 V K
  let hs : ℕ → K → 𝕜 := fun n ↦ fun ϕ ↦ fs n (ϕ : WeakDual 𝕜 V)
  apply X_metrizable (E := fun _ ↦ 𝕜) hs
  · intro n
    exact Continuous.comp (fs_cont n) continuous_subtype_val
  · intro x y x_ne_y
    apply fs_sep
    exact Subtype.coe_ne_coe.mpr x_ne_y

/- The closed unit ball is sequentially compact in V* if V is separable. -/
theorem WeakDual.isSeqCompact_closedBall [SequentialSpace V] (x' : NormedSpace.Dual 𝕜 V) (r : ℝ) :
    IsSeqCompact (WeakDual.toNormedDual ⁻¹' Metric.closedBall x' r) := by
  let b := (WeakDual.toNormedDual ⁻¹' Metric.closedBall x' r)
  have b_isCompact : IsCompact b := by
    apply WeakDual.isCompact_closedBall
  have b_isCompact' : CompactSpace b := by
    exact isCompact_iff_compactSpace.mp b_isCompact

  have b_isMetrizable : TopologicalSpace.MetrizableSpace b := by
    exact subset_metrizable 𝕜 V b b_isCompact

  have seq_cpt_space := @FirstCountableTopology.seq_compact_of_compact b
      _ _ b_isCompact'

  have seq_cont_phi : SeqContinuous (fun φ : b ↦ (φ : WeakDual 𝕜 V)) := by
    refine continuous_iff_seqContinuous.mp ?_
    exact continuous_subtype_val

  have seq_incl := IsSeqCompact.range seq_cont_phi
  convert seq_incl

  simp only [Subtype.range_coe_subtype, Set.mem_preimage, coe_toNormedDual, Metric.mem_closedBall]
  rfl

example : WeakDual 𝕜 V = (V →L[𝕜] 𝕜) := rfl

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


#help tactic
