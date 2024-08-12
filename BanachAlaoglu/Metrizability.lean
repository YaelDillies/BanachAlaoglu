import Mathlib.Topology.CompletelyRegular
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Complex.Abs
import Mathlib.Data.Real.StarOrdered
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Analysis.Normed.Order.Lattice

open Function

section Metrizability_lemma

variable {X : Type*} {E : ℕ → Type*} [TopologicalSpace X] [∀ n, PseudoMetricSpace (E n)]
variable (gs : ∀ n, X → E n)
variable (gs_cont : ∀ n, Continuous (gs n))

section pseudoMetric

private noncomputable def ourMetric (x y : X) : ℝ :=
  ∑' n, (1/2)^n * min (dist (gs n x) (gs n y)) 1

variable {gs}

lemma ourMetric_bdd {x y} : (∀ (i : ℕ), ‖(fun n ↦ (1 / 2) ^ n * min (dist (gs n x) (gs n y)) 1) i‖
  ≤ (fun n ↦ (1 / 2) ^ n) i) := by
  intro i
  simp only [one_div, inv_pow, norm_mul, norm_inv, norm_pow, RCLike.norm_ofNat, Real.norm_eq_abs,
    inv_pos, Nat.ofNat_pos, pow_pos, mul_le_iff_le_one_right]
  rw [abs_of_nonneg (by positivity)]
  exact min_le_right (dist (gs i x) (gs i y)) 1

lemma summable_if_bounded {x y} : Summable fun n ↦ (1 / 2) ^ n * min (dist (gs n x) (gs n y)) 1 :=
  Summable.of_norm_bounded (fun n ↦ (1 / 2) ^ n) summable_geometric_two (ourMetric_bdd)

lemma ourMetric_self {x y} : x = y → ourMetric gs x y = 0 := by
  intro x_eq_y
  simp [ourMetric, one_div, inv_pow, x_eq_y, sub_self, norm_zero, mul_zero, tsum_zero]

lemma ourMetric_comm {x y} : ourMetric gs x y = ourMetric gs y x := by
  unfold ourMetric
  rw [tsum_congr]
  intro b
  rw [dist_comm]

lemma ourMetric_triangle {x y z} : ourMetric gs x z ≤ ourMetric gs x y + ourMetric gs y z := by
  unfold ourMetric
  have tri_ineq n : (1/2)^n * min (dist (gs n x) (gs n z)) 1
      ≤ (1/2)^n * min (dist (gs n x) (gs n y)) 1 + (1/2)^n * min (dist (gs n y) (gs n z)) 1 := by
    rw [← mul_add, mul_le_mul_left]
    simp only [ne_eq, min_le_iff]
    cases' (min_cases (dist (gs n x) (gs n z)) 1)
    · cases' (min_cases (dist (gs n x) (gs n y)) 1) with h1 h2
      · obtain ⟨eq_dist, _⟩ := h1
        rw [eq_dist]
        cases' (min_cases (dist (gs n y) (gs n z)) 1) with h1 h2
        · obtain ⟨eq_dist, _⟩ := h1
          rw [eq_dist]
          left
          exact dist_triangle (gs n x) (gs n y) (gs n z)
        · obtain ⟨eq_one, _⟩ := h2
          rw [eq_one]
          right
          simp [add_le_add_left]
          positivity
      · obtain ⟨eq_one, _⟩ := h2
        rw [eq_one]
        cases' (min_cases (dist (gs n y) (gs n z)) 1) with h1 h2
        · obtain ⟨eq_dist, _⟩ := h1
          rw [eq_dist]
          right
          simp [add_le_add_left]
          positivity
        · obtain ⟨eq_one, _⟩ := h2
          rw [eq_one]
          right
          simp [add_le_add_left]

    · cases' (min_cases (dist (gs n x) (gs n y)) 1) with h1 h2
      · obtain ⟨eq_dist, _⟩ := h1
        rw [eq_dist]
        cases' (min_cases (dist (gs n y) (gs n z)) 1) with h1 h2
        · obtain ⟨eq_dist, _⟩ := h1
          rw [eq_dist]
          left
          exact dist_triangle (gs n x) (gs n y) (gs n z)
        · obtain ⟨eq_one, _⟩ := h2
          rw [eq_one]
          right
          simp [add_le_add_left]
          positivity
      · obtain ⟨eq_one, _⟩ := h2
        rw [eq_one]
        cases' (min_cases (dist (gs n y) (gs n z)) 1) with h1 h2
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

def pseudoMetricCopy (X : Type*) (gs : ∀n, X → E n) := X

def pseudoMetricCopy.mk (X : Type*) (gs : ∀n, X → E n) :
    X → pseudoMetricCopy X gs := id

def pseudoMetricCopy.toOrigin (X : Type*) (gs : ∀n, X → E n) :
    pseudoMetricCopy X gs → X := id

noncomputable instance ourPseudoMetricSpace : PseudoMetricSpace (pseudoMetricCopy X gs) where
  dist := ourMetric gs
  dist_self x := ourMetric_self rfl
  dist_comm x y := ourMetric_comm
  dist_triangle x y z := ourMetric_triangle
  edist_dist := by simp only [← ENNReal.ofReal_coe_nnreal, NNReal.coe_mk, implies_true]

lemma cont_ourMetric (gs_cont : ∀ (n : ℕ), Continuous (gs n)) :
    Continuous (fun (p : X × X) ↦ ourMetric gs p.1 p.2) := by
  apply @continuous_tsum ℕ (X × X) ℝ _ _ (fun (n : ℕ) ↦ (1 / 2) ^ n) _
    (fun n ↦ fun (x, y) ↦ (1 / 2) ^ n * min (dist (gs n x) (gs n y)) 1)
    ?_ (summable_geometric_two) ?_
  · intro i
    have cont_xy i := Continuous.dist (Continuous.fst' (gs_cont i)) (Continuous.snd' ((gs_cont i)))
    have continuous_min n := Continuous.min (g := (fun (_,_) ↦ 1)) (cont_xy n) (continuous_const)
    exact Continuous.mul (f := (fun _ ↦ (1 / 2) ^ i)) (continuous_const) (continuous_min i)

  · simp only [inv_pow, norm_mul, norm_inv, norm_pow, RCLike.norm_ofNat, norm_norm,
    Prod.forall]
    intro n a b
    rw [one_div, norm_inv, RCLike.norm_ofNat, inv_pow, mul_comm, mul_le_iff_le_one_left]
    · have min_pos := (le_min_iff (a := dist (gs n a) (gs n b)) (b := 1) (c := 0)).mpr
          (by refine ⟨by positivity, by positivity⟩)
      simp only [Real.norm_eq_abs, abs_of_nonneg min_pos, min_le_iff]
      right
      rfl
    · simp

lemma cont_ourMetric' (gs_cont : ∀ (n : ℕ), Continuous (gs n)) : Continuous (fun (p : X × X) ↦
    dist (pseudoMetricCopy.mk X gs p.1) (pseudoMetricCopy.mk X gs p.2)) := cont_ourMetric gs_cont

lemma cont_Copy_mk (gs_cont : ∀ n, Continuous (gs n)) :
    Continuous (pseudoMetricCopy.mk X gs) := by
  apply Metric.continuous_iff'.mpr
  intro x ε hε
  have cont_dist : Continuous (fun y ↦ dist (pseudoMetricCopy.mk X gs y)
      (pseudoMetricCopy.mk X gs x)) := Continuous.along_fst (cont_ourMetric' gs_cont)
  have := @IsOpen.mem_nhds X x _ _ (cont_dist.isOpen_preimage _ isOpen_Iio) (by simpa using hε)
  filter_upwards [this] with y hy using hy

end pseudoMetric

section Metric

variable {X : Type*} {E : ℕ → Type*} [TopologicalSpace X] [∀ n, MetricSpace (E n)]
variable {gs : ∀ n, X → E n}
variable (gs_cont : ∀ n, Continuous (gs n))
variable (gs_sep : (∀ ⦃x y⦄, x≠y → ∃ n, gs n x ≠ gs n y))

lemma ourMetric_self' {x y} : ourMetric gs x y = 0 → x = y := by
  intro sum
  rw [ourMetric] at sum
  have sum_zero : ∑' n, (1/2)^n * min (dist (gs n x) (gs n y)) 1 = 0 →
      ∀ n, (1/2)^n * min (dist (gs n x) (gs n y)) 1 = 0 := by
    have tsum_zero (g : ℕ → ℝ) (h : ∀ (i : ℕ), g i ≥ 0) (h' : Summable g) :
        ∑' (i : ℕ), g i = 0 ↔ ∀ (i : ℕ), g i = 0 := by
      calc
        _ ↔ HasSum g 0 := (Summable.hasSum_iff h').symm
        _ ↔ g = 0 := hasSum_zero_iff_of_nonneg h
        _ ↔ _ := Function.funext_iff
    intro sum
    let f := fun n ↦ (1/2)^n * min (dist (gs n x) (gs n y)) 1
    have terms_pos n : f n >= 0 := by positivity
    apply (tsum_zero (fun n ↦ (1/2)^n * min (dist (gs n x) (gs n y)) 1) (terms_pos)
        summable_if_bounded).mp
    exact sum
  apply sum_zero at sum
  simp only [one_div, inv_pow, mul_eq_zero, inv_eq_zero, pow_eq_zero_iff', OfNat.ofNat_ne_zero,
    ne_eq, false_and, norm_eq_zero, sub_eq_zero, false_or] at sum
  contrapose! sum
  specialize gs_sep sum
  obtain ⟨a, gs_neq⟩ := gs_sep
  use a
  by_contra h
  cases' le_or_lt (dist (gs a x) (gs a y)) 1 with h1 h2
  · simp only [min_eq_left_iff.mpr h1, dist_eq_zero, one_div, inv_pow, mul_eq_zero, inv_eq_zero, pow_eq_zero_iff',
      OfNat.ofNat_ne_zero, ne_eq, false_and, false_or] at *
    exact gs_neq h
  · linarith [min_eq_right_iff.mpr (LT.lt.le h2)]

def metricCopy (X : Type*) (gs : ∀n, X → E n) (_ : (∀ ⦃x y⦄, x≠y → ∃ n, gs n x ≠ gs n y)) :=
    pseudoMetricCopy X gs

noncomputable instance pseudoMetricSpace_metricCopy : PseudoMetricSpace (metricCopy X gs gs_sep) :=
    ourPseudoMetricSpace

def metricCopy.toPseudoMetricCopy : IsometryEquiv (α := metricCopy X gs gs_sep)
    (β := pseudoMetricCopy X gs) where
  toFun := id
  invFun := id
  left_inv := congrFun rfl
  right_inv := congrFun rfl
  isometry_toFun := fun _ ↦ congrFun rfl

def metricCopy.mk (X : Type*) (gs : ∀n, X → E n) (gs_sep : (∀ ⦃x y⦄, x≠y → ∃ n, gs n x ≠ gs n y)) :
    X → metricCopy X gs gs_sep := id

def metricCopy.toOrigin (X : Type*) (gs : ∀n, X → E n)
    (gs_sep : (∀ ⦃x y⦄, x≠y → ∃ n, gs n x ≠ gs n y)) :
    metricCopy X gs gs_sep → X := id

noncomputable instance metricSpace_metricCopy : MetricSpace (metricCopy X gs gs_sep) where
  eq_of_dist_eq_zero := ourMetric_self' gs_sep

lemma cont_metricCopy_mk (gs_sep : (∀ ⦃x y⦄, x≠y → ∃ n, gs n x ≠ gs n y))
    (gs_cont : ∀ n, Continuous (gs n)) :
    Continuous (metricCopy.mk X gs gs_sep) :=
  (IsometryEquiv.continuous ((metricCopy.toPseudoMetricCopy gs_sep).symm)).comp
    <| cont_Copy_mk gs_cont

end Metric

section metrizable_of_compactSpace

variable {X : Type*} {E : ℕ → Type*} [TopologicalSpace X] [∀ n, MetricSpace (E n)] [CompactSpace X]
variable {gs : ∀ n, X → E n}
variable (gs_cont : ∀ n, Continuous (gs n))
variable (gs_sep : (∀ ⦃x y⦄, x≠y → ∃ n, gs n x ≠ gs n y))

lemma cont_metricCopy_toOrigin (gs_cont : ∀ n, Continuous (gs n)) :
    Continuous (metricCopy.toOrigin X gs gs_sep) := by
  have symm (s : Set X) : metricCopy.toOrigin X gs gs_sep ⁻¹' s = metricCopy.mk X gs gs_sep '' s :=
    Eq.symm (Set.EqOn.image_eq_self fun ⦃x⦄ ↦ congrFun rfl)
  have closed_impl (s : Set X) : IsClosed s → IsClosed (metricCopy.toOrigin X gs gs_sep ⁻¹' s) := by
    intro s_closed
    have s_cpt_X := IsClosed.isCompact s_closed
    rw [isCompact_iff_finite_subcover] at s_cpt_X
    have open_preimage s : IsOpen s → IsOpen (metricCopy.mk X gs gs_sep ⁻¹' s) :=
      continuous_def.mp (cont_metricCopy_mk gs_sep gs_cont) s
    have closed_preimage_s : IsClosed (metricCopy.toOrigin X gs gs_sep ⁻¹' s) := by
      have s_image_cpt : IsCompact (metricCopy.mk X gs gs_sep '' s) := by
        apply isCompact_of_finite_subcover
        intro _ Us Usi_open
        simp only [metricCopy.mk, id_eq, Set.image_id']
        exact fun a ↦ s_cpt_X Us (fun i ↦ open_preimage (Us i) (Usi_open i)) a
      simpa [symm s] using IsCompact.isClosed s_image_cpt
    exact closed_preimage_s
  exact continuous_iff_isClosed.mpr closed_impl

noncomputable def homeomorph_OurMetric :
  X ≃ₜ metricCopy X gs gs_sep where
    toFun := metricCopy.mk X gs gs_sep
    invFun := metricCopy.toOrigin X gs gs_sep
    left_inv := congrFun rfl
    right_inv := congrFun rfl
    continuous_toFun := cont_metricCopy_mk gs_sep gs_cont
    continuous_invFun := cont_metricCopy_toOrigin gs_sep gs_cont

/- If X is compact, and there exists a seq of continuous real-valued functions that
separates points on X, then X is metrizable. -/
lemma X_metrizable (gs : ∀ n, X → E n) (gs_cont : ∀ n, Continuous (gs n))
    (gs_sep : (∀ ⦃x y⦄, x≠y → ∃ n, gs n x ≠ gs n y)) :
    TopologicalSpace.MetrizableSpace X :=
    (homeomorph_OurMetric gs_cont gs_sep).embedding.metrizableSpace

end metrizable_of_compactSpace

end Metrizability_lemma
