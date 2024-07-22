
import Mathlib
--set_option maxHeartbeats 1000000

section inducing
--variable {Y :Type*}
variable {X Y : Type*} [TopologicalSpace X][TopologicalSpace Y]
open TopologicalSpace

def Inducing.comapMetricSpace {α β} [TopologicalSpace α] [m : MetricSpace β] {f : α → β}
    (hf : Inducing f) (inj : Function.Injective f) : MetricSpace α :=
  .replaceTopology (.induced f inj m) hf.induced



theorem Inducing.metrizableSpace [MetrizableSpace Y] {f : X → Y}
    (hf : Inducing f) (inj : Function.Injective f) : MetrizableSpace X := by
  letI : MetricSpace Y := metrizableSpaceMetric Y
  --⟨⟨hf.comapMetricSpace, rfl⟩⟩
  refine ⟨@Inducing.comapMetricSpace X Y _ _ f hf inj, rfl⟩

end inducing

section assumption_on_the_normed_field
open Function
class IsSensiblyNormed (𝕜: Type*) [NormedField 𝕜] where
  squeeze' : 𝕜 → 𝕜
  cont : Continuous squeeze'
  inj : Injective squeeze'
  bdd : ∀ c : 𝕜, ‖squeeze' c‖ ≤ 1
variable (𝕜: Type*) [NormedField 𝕜] [IsSensiblyNormed 𝕜]
def squeeze (c : 𝕜) : 𝕜 :=
    ‹IsSensiblyNormed 𝕜›.squeeze' c

lemma cont_squeeze : Continuous (squeeze 𝕜) := by
  exact ‹IsSensiblyNormed 𝕜›.cont

lemma inj_squeeze : Injective (squeeze 𝕜) := by

  exact ‹IsSensiblyNormed 𝕜›.inj

lemma bdd_squeeze (c : 𝕜) : ∀ c : 𝕜, ‖squeeze 𝕜 c‖ ≤ 1 := by
  exact ‹IsSensiblyNormed 𝕜›.bdd

--example (a b : ℝ) (h1 : 0 ≤ a) (h2 : 0 ≤ b) (h3 : a ≤ b) : a / b ≤ 1 := by
  --exact div_le_one_of_le h3 h2
--example (a : ℝ) (h1 : a ≤ 1) (h2 : 0 ≤ a) : |a| ≤ 1 := by

noncomputable instance : IsSensiblyNormed ℝ where
  squeeze' : ℝ → ℝ := (fun a ↦ a / (1 + ‖a‖))
  cont := by
    have foo : Continuous (fun a : ℝ ↦ ‖a‖) := by exact continuous_norm
    have foo2 : Continuous (fun a : ℝ ↦ (1 + ‖a‖)) := by
      exact Continuous.add (by exact continuous_const) (by exact foo)
    --have : Continuous (fun a:ℝ  ↦ 1) := by exact?

    have nonzero : (∀ (x : ℝ), (fun a ↦ 1 + ‖a‖) x ≠ 0) := by
      intro x
      have lt : ∀ a : ℝ, 0 < 1 + ‖a‖ := by
        simp [add_comm, add_pos_of_nonneg_of_pos]
      have : ∀ a : ℝ, 1 + ‖a‖ ≠ 0 := by
        intro a
        specialize lt a
        have : 0 < 1 + ‖a‖ → 1 + ‖a‖ ≠ 0 := by exact fun a_1 ↦ Ne.symm (ne_of_lt lt)
        exact this lt
      apply this
    have : Continuous (fun a : ℝ ↦ a) := continuous_id
    exact Continuous.div this foo2 nonzero

  inj := by
    have foo : ∀ x y: ℝ, x/(1 + ‖x‖) = y/(1 + ‖y‖) → (x = y) := by
      intro x y
      intro h
      simp at h
      have lt : ∀ a : ℝ, 0 < 1 + ‖a‖ := by
        simp [add_comm, add_pos_of_nonneg_of_pos]
      have : ∀ a : ℝ, 1 + ‖a‖ ≠ 0 := by
        intro a
        specialize lt a
        have : 0 < 1 + ‖a‖ → 1 + ‖a‖ ≠ 0 := by exact fun a_1 ↦ Ne.symm (ne_of_lt lt)
        exact this lt
      --contrapose! h
      have xnz : (1 + |x|) ≠ 0 := by exact this x
      have ynz : (1 + |y|) ≠ 0 := by exact this y
      have := @mul_eq_mul_of_div_eq_div ℝ _ (1 + |x|) (1 + |y|) x y xnz ynz h
      --have := @div_eq_iff_eq_mul ℝ _ --x (1 + |x|) (y/(1 + |y|))
      --have := (@div_eq_div_iff_mul_eq_mul ℝ _ x (1 + |x|) y (1 + |y|))
      --contrapose! this
      ring_nf at this


      have : 0 ≤ x ∧ 0 ≤ y → (x + x * |y| = y + y * |x|) = (x + x * y = y + y * x) := by
        intro h
        rw [← abs_eq_self] at h
        rw [← abs_eq_self] at h
        simp [h]

      have : 0 ≤ x ∧ y < 0 → (x + x * |y| = y + y * |x|) = (x + x * y = - y + - y * x) := by
        intro h
        rw [← abs_eq_self] at h
        simp [h]

        sorry

      have : x < 0 ∧ y < 0 → (x + x * |y| = y + y * |x|) = (- x + - x * y = - y + - y * x) := by

        sorry

      have : x < 0 ∧ 0 ≤ y → (x + x * |y| = y + y * |x|) = (- x + - x * y = y + y * x) := by

        sorry








      sorry
    exact foo

 --#check CommGroup ℝ
  bdd := by
    have h : ∀ x : ℝ, x / (1 + ‖x‖) ≤ 1 := by
      intro x
      have : x ≤ 1 + ‖x‖ := by
        simp only [Real.norm_eq_abs]
        apply le_add_of_nonneg_of_le
        · linarith
        · exact le_abs_self x
      have : x / (1 + ‖x‖) ≤ 1 := by
        apply div_le_one_of_le
        · exact this
        · exact add_nonneg (by linarith) (by norm_num)
      exact this

    intro c
    have : ∀ x : ℝ , ‖x / (1 + ‖x‖)‖ ≤ 1 := by
      intro x
      simp only [Real.norm_eq_abs, norm_inv]
      have : ∀ a b : ℝ, 0 < b ∧ a ≤ b → a / b ≤ 1 := by
        intro a b
        intro a_le_b
        cases' a_le_b with  h1 h2

        sorry
      have : |x / (1 + |x|)| ≤ 1 := by
        have le_one : x / (1 + |x|) ≤ 1 := by exact h x
        have x_le_opa : x ≤ 1 + |x| := by
          apply le_add_of_nonneg_of_le
          · linarith
          · exact le_abs_self x
        have := @abs_le_one_iff_mul_self_le_one ℝ _ (x / (1 + |x|))
        have : (x / (1 + |x|)) * (x / (1 + |x|)) ≤ 1 ↔ x ≤ 1 + |x| := by
          constructor
          · exact fun a ↦ x_le_opa
          · have : (x / (1 + |x|)) * (x / (1 + |x|)) = (x * x) / ( 1 + 2 * |x| + x * x) := by
              ring_nf
              simp only [inv_pow, mul_eq_mul_left_iff, inv_inj, ne_eq, OfNat.ofNat_ne_zero,
                not_false_eq_true, pow_eq_zero_iff]
              left
              ring_nf
              simp only [sq_abs]
            simp [this]
            intro _
            have : x * x ≤ (1 + 2 * |x| + x * x) := by
              norm_num
              simp [add_nonneg]
            --simp only []

            simp_all [Real.norm_eq_abs, iff_true, le_add_iff_nonneg_left]

            sorry
        simp_all [Real.norm_eq_abs, iff_true]


      simp_all only [Real.norm_eq_abs]

        --simp only [abs_le]
        --exact ⟨ge_minus_one, h x⟩
      --exact this
    --exact this c
    exact this c

/- have ge_minus_one : -1 ≤ x / (1 + |x|) := by
          have : x ≤ 1 + |x| := by
            apply le_add_of_nonneg_of_le
            · linarith
            · exact le_abs_self x
          have : x ≤ 1 + |x| → |x / (1 + |x|)| ≤ 1 := by

            sorry
        -/
example (a b c : ℝ) : (a * b)/(c * b) = a / c := by

  sorry

noncomputable instance : IsSensiblyNormed ℂ where
  squeeze' : ℂ → ℂ := (fun a ↦ a / (1 + ‖a‖))
  cont := by
    have foo : Continuous (fun a : ℂ ↦ (‖a‖ : ℂ) ) := by
      norm_num
      have := Complex.continuous_abs
      have : Continuous (fun a ↦ Complex.abs a) ↔ Continuous (fun a ↦ (Complex.abs a : ℂ )) := by
        constructor
        · intro _

          sorry
        · exact fun a ↦ this



      simp_all only [iff_true]

    have foo2 : Continuous (fun a : ℂ ↦ ((1 : ℂ) + ‖a‖)) := by
      exact Continuous.add (by exact continuous_const) (by exact foo)
    --have : Continuous (fun a:ℝ  ↦ 1) := by exact?
    have nonzero : (∀ (x : ℂ), (fun (a : ℂ) ↦ ((1 : ℂ) + ‖a‖)) x ≠ 0):= by
      intro x
      simp only [Complex.norm_eq_abs]
      /-have lt : ∀ a : ℂ, 0 < ((1 : ℂ)  + ‖a‖) := by
        simp only [Complex.norm_eq_abs]
        intro a
        apply lt_add_of_lt_of_nonneg
        · linarith
        · exact AbsoluteValue.nonneg Complex.abs a
-/
      have : ∀ a : ℂ, (1 : ℂ) + ‖a‖ ≠ 0 := by
        intro a
        simp only [Complex.norm_eq_abs]
        have : 0 ≤ ↑(Complex.abs a)  := by exact AbsoluteValue.nonneg Complex.abs a
        have lt : 0 < 1 + ↑(Complex.abs a) := by
          apply add_pos_of_pos_of_nonneg
          · norm_num
          · exact this
        have : 0 < 1 + ↑(Complex.abs a) → 1 + ↑(Complex.abs a) ≠ 0 := by
          exact fun a_1 ↦ Ne.symm (ne_of_lt lt)
        have := this lt
        have : -1 ≠ (↑(Complex.abs a) : ℂ)  := by

          sorry


        have : -1 = (↑(Complex.abs a) : ℂ ) → 1 + (↑(Complex.abs a) : ℂ ) = 0 := by
          intro _

          simp_all only [Complex.norm_eq_abs, apply_nonneg, ne_eq, not_false_eq_true, imp_self, not_true_eq_false]




        --specialize lt a
        --have : 0 ≤ ((1 : ℂ) + ↑(Complex.abs (a : ℂ)))  → (1 : ℂ) + ‖a‖ ≠ 0 := by sorry--exact fun a_1 ↦ Ne.symm (ne_of_lt lt)
        --exact this lt

        sorry
      apply this
    have : Continuous (fun a : ℂ ↦ a) := continuous_id

    have := @Continuous.div ℂ ℂ _ _ _ _ (fun a ↦ a) (fun a : ℂ ↦ (1 + ‖a‖)) _ this foo2 --nonzero
    exact this nonzero



  inj := by
    intro x y x_eq_y
    norm_num at x_eq_y

    sorry
  bdd := by
    intro c
    norm_num
    have foo2 : ∀ x : ℂ, 0 ≤ Complex.abs (1 + ↑(Complex.abs x)) := by
      norm_num
    have foo4 : ∀ x : ℂ, Complex.abs x ≤ Complex.abs (1 + ↑(Complex.abs x)) := by
      intro x
      have : Complex.abs x ≤ (1 + ↑(Complex.abs x)) := by norm_num
      have : (1 + ↑(Complex.abs x)) ≤ Complex.abs ((1:ℝ ) + (↑(Complex.abs x) : ℝ)) := by
        have (a : ℝ) : a ≤ Complex.abs (a) := by
          simp only [Complex.abs_ofReal]
          exact le_abs_self a
        --exact this (1 + ↑(Complex.abs x))


        sorry
      --have : x ≤ 1 + ↑(Complex.abs x) := by sorry


      sorry
    apply div_le_one_of_le
    · exact foo4 c
    · exact foo2 c



end assumption_on_the_normed_field

section Seq_cpt_continuity

lemma IsSeqCompact.image {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y)
    (f_cont : SeqContinuous f) {K : Set X} (K_cpt : IsSeqCompact K) : IsSeqCompact (f '' K) := by
  intro ys ys_in_fK
  let xs := fun n ↦ Exists.choose (ys_in_fK n)
  obtain ⟨xs_in_K, fxs_eq_ys⟩ : (∀ n, xs n ∈ K) ∧ ∀ n, f (xs n) = ys n :=
    forall_and.mp fun n ↦ Exists.choose_spec (ys_in_fK n)
  simp only [Set.mem_image, exists_exists_and_eq_and]
  obtain ⟨a, a_in_K, phi, phi_mono, xs_phi_lim⟩ := K_cpt xs_in_K
  refine ⟨a, a_in_K, phi, phi_mono, ?_⟩
  exact Filter.Tendsto.congr (fun x ↦ fxs_eq_ys (phi x)) (f_cont xs_phi_lim)

example {X : Type*} [TopologicalSpace X] [SeqCompactSpace X] : IsSeqCompact (Set.univ : Set X) := by
  exact (seqCompactSpace_iff X).mp ‹SeqCompactSpace X›

lemma SeqCompactSpace.range {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [SeqCompactSpace X]
    (f : X → Y) (hf : SeqContinuous f) : IsSeqCompact (Set.range f) := by
  rw [← Set.image_univ]
  exact IsSeqCompact.image f hf ((seqCompactSpace_iff X).mp ‹SeqCompactSpace X›)

end Seq_cpt_continuity



section Metrizability_lemma


variable {X 𝕜 : Type*} [TopologicalSpace X] [CompactSpace X] [NormedField 𝕜]
variable (gs : ℕ → X → 𝕜)
variable (gs_cont : ∀ n, Continuous (gs n))
variable (gs_sep : Set.SeparatesPoints (Set.range gs))
variable (gs_bdd : ∀ n : ℕ, ∀ x : X, ‖gs n x‖  ≤ 1)

noncomputable def ourMetric (x y : X) : ℝ :=
  ∑' n, (1/2)^n * ‖gs n x - gs n y‖

lemma ourMetric_self_iff : ∀ {x y : X}, ourMetric gs x y = 0 ↔ x = y := by
  intro x y
  constructor
  · intro sum
    rw [ourMetric] at sum

    have sum_zero : ∑' n, (1/2)^n * ‖gs n x - gs n y‖  = 0 → ∀ n, (1/2)^n * ‖gs n x - gs n y‖  = 0 := by
      have tsum_zero (g : ℕ → ℝ) (h : ∀ (i : ℕ), g i ≥ 0) (h' : Summable g) :
          ∑' (i : ℕ), g i = 0 ↔ ∀ (i : ℕ), g i = 0 := by
        calc
          _ ↔ HasSum g 0 := (Summable.hasSum_iff h').symm
          _ ↔ g = 0 := hasSum_zero_iff_of_nonneg h
          _ ↔ _ := Function.funext_iff

      intro sum
      let f := fun n ↦ (1/2)^n * ‖gs n x - gs n y‖
      have summable_metric : Summable f := by
        have norm_bdd : ∀ n, ‖gs n x - gs n y‖  ≤ 1 + 1 := by
          exact fun n ↦ norm_sub_le_of_le (gs_bdd n x) (gs_bdd n y)
        ring_nf at norm_bdd

        have summable_if_bounded := @Summable.of_norm_bounded ℕ ℝ _ _
            (fun n ↦ (1/2)^n * ‖gs n x - gs n y‖) (fun n ↦ 2 * (1 / 2) ^ n) (Summable.mul_left 2 summable_geometric_two)

        have : (∀ (i : ℕ), ‖(fun n ↦ (1 / 2) ^ n * ‖gs n x - gs n y‖) i‖
            ≤ (fun n ↦ 2 * (1 / 2) ^ n) i)  := by
          intro i
          simp only [one_div, inv_pow, sub_self, add_zero, norm_mul, norm_inv, norm_pow,
          RCLike.norm_ofNat, norm_norm]
          rw [mul_comm]
          simp only [gt_iff_lt, inv_pos, Nat.ofNat_pos, pow_pos, mul_le_mul_right]
          exact norm_bdd i

        exact summable_if_bounded this

      have terms_pos : ∀ n : ℕ, f n >= 0 := by
        have : ∀ n : ℕ, ‖gs n x - gs n y‖ >= 0 := by
          intro n
          apply norm_nonneg
        intro n
        refine mul_nonneg ?ha (this n)
        norm_num

      apply (tsum_zero (fun n ↦ (1/2)^n * ‖gs n x - gs n y‖) terms_pos summable_metric).mp
      exact sum

    apply sum_zero at sum
    simp only [one_div, inv_pow, mul_eq_zero, inv_eq_zero, pow_eq_zero_iff', OfNat.ofNat_ne_zero,
      ne_eq, false_and, norm_eq_zero, false_or, sub_eq_zero] at sum
    contrapose! sum

    have : (∃ f ∈ Set.range gs, f x ≠ f y) → ∃ a, gs a ↑x ≠ gs a ↑y := by
      simp only [Set.mem_range, ne_eq, exists_exists_eq_and, imp_self]
    apply this
    apply gs_sep
    exact sum

  · intro x_eq_y
    rw [ourMetric, x_eq_y]
    simp

example (g : ℕ → ℝ) (h : ∀ (i : ℕ), g i ≥ 0) (h' : Summable g) :
    ∑' (i : ℕ), g i = 0 ↔ ∀ (i : ℕ), g i = 0 := by
  calc
    _ ↔ HasSum g 0 := (Summable.hasSum_iff h').symm
    _ ↔ g = 0 := hasSum_zero_iff_of_nonneg h
    _ ↔ _ := Function.funext_iff

lemma ourMetric_comm : ∀ x y : X, ourMetric gs x y = ourMetric gs y x := by
  intro x y
  rw [ourMetric, ourMetric]
  have abs_eq : ∀ n, ‖gs n x - gs n y‖ = ‖gs n y - gs n x‖  := by
    intro n
    exact norm_sub_rev (gs n x) (gs n y)
  rw [tsum_congr]
  intro b
  rw [abs_eq]

lemma ourMetric_triangle : ∀ x y z : X, ourMetric gs x z ≤ ourMetric gs x y + ourMetric gs y z := by
  intro x y z
  simp only [ourMetric]

  have plusminus_eq_self : ∀ n, ‖gs n x - gs n z‖  = ‖gs n x + (gs n y - gs n y) - gs n z‖  := by
    intro n
    simp [sub_self (gs n y)]

  simp_rw [plusminus_eq_self]

  have tri_ineq : ∀ n, (1/2)^n * ‖gs n x + (gs n y - gs n y) - gs n z‖  ≤ (1/2)^n * ‖gs n x - gs n y‖ + (1/2)^n * ‖gs n y - gs n z‖  := by
    intro n
    rw [← add_comm_sub, add_sub_assoc (gs n x - gs n y) (gs n y) (gs n z) , ← mul_add]
    refine (mul_le_mul_left ?_).mpr ?_
    · refine pow_pos ?refine_1.H n
      linarith
    · exact norm_add_le (gs n x - gs n y) (gs n y - gs n z)

  have tsum_tri_ineq : ∑' (n : ℕ), (1 / 2) ^ n * ‖gs n x + (gs n y - gs n y) - gs n z‖  ≤
      ∑' (n : ℕ), ((1 / 2) ^ n * ‖gs n x - gs n y‖ + (1 / 2) ^ n * ‖gs n y - gs n z‖) := by

    apply tsum_le_tsum
    · exact tri_ineq
    · have abs_plus : ∀ n, ‖gs n x + (gs n y - gs n y) - gs n z‖  ≤ ‖gs n x‖  + ‖gs n z‖ := by
        intro n
        simp [norm_sub_le (gs n x) (gs n z)]

      have norm_sum_bdd : ∀ n, ‖gs n x‖ + ‖gs n z‖  ≤ 1 + 1 := by
        intro n
        have gs_bdd' := gs_bdd
        specialize gs_bdd n x
        specialize gs_bdd' n z
        exact add_le_add gs_bdd gs_bdd'

      have norm_bdd : ∀ n, ‖gs n x + (gs n y - gs n y) - gs n z‖  ≤ 1 + 1 := by
        exact fun n ↦
          Preorder.le_trans ‖gs n x + (gs n y - gs n y) - gs n z‖ (‖gs n x‖ + ‖gs n z‖) (1 + 1)
            (abs_plus n) (norm_sum_bdd n)
      ring_nf at norm_bdd

      have summable_if_bounded := @Summable.of_norm_bounded ℕ ℝ _ _
          (fun n ↦ (1/2)^n * ‖gs n x + (gs n y - gs n y) - gs n z‖) (fun n ↦ 2 * (1 / 2) ^ n) (Summable.mul_left 2 summable_geometric_two)

      have : (∀ (i : ℕ), ‖(fun n ↦ (1 / 2) ^ n * ‖gs n x + (gs n y - gs n y) - gs n z‖) i‖
          ≤ (fun n ↦ 2 * (1 / 2) ^ n) i)  := by
        intro i
        simp only [one_div, inv_pow, sub_self, add_zero, norm_mul, norm_inv, norm_pow,
          RCLike.norm_ofNat, norm_norm, mul_comm, inv_pos, Nat.ofNat_pos, pow_pos, mul_le_mul_right]
        exact norm_bdd i

      exact summable_if_bounded this

    · apply Summable.add
      · have norm_bdd : ∀ n, ‖gs n x - gs n y‖  ≤ 1 + 1 := by
          exact fun n ↦ norm_sub_le_of_le (gs_bdd n x) (gs_bdd n y)
        ring_nf at norm_bdd

        have summable_if_bounded := @Summable.of_norm_bounded ℕ ℝ _ _
          (fun n ↦ (1/2)^n * ‖gs n x - gs n y‖) (fun n ↦ 2 * (1 / 2) ^ n) (Summable.mul_left 2 summable_geometric_two)

        have : (∀ (i : ℕ), ‖(fun n ↦ (1 / 2) ^ n * ‖gs n x - gs n y‖) i‖
            ≤ (fun n ↦ 2 * (1 / 2) ^ n) i)  := by
          intro i
          simp only [one_div, inv_pow, sub_self, add_zero, norm_mul, norm_inv, norm_pow,
            RCLike.norm_ofNat, norm_norm, mul_comm, inv_pos, Nat.ofNat_pos, pow_pos, mul_le_mul_right]
          exact norm_bdd i

        exact summable_if_bounded this

      · have norm_bdd : ∀ n, ‖gs n y - gs n z‖  ≤ 1 + 1 := by
          exact fun n ↦ norm_sub_le_of_le (gs_bdd n y) (gs_bdd n z)
        ring_nf at norm_bdd

        have summable_if_bounded := @Summable.of_norm_bounded ℕ ℝ _ _
            (fun n ↦ (1/2)^n * ‖gs n y - gs n z‖) (fun n ↦ 2 * (1 / 2) ^ n) (Summable.mul_left 2 summable_geometric_two)

        have : (∀ (i : ℕ), ‖(fun n ↦ (1 / 2) ^ n * ‖gs n y - gs n z‖) i‖
            ≤ (fun n ↦ 2 * (1 / 2) ^ n) i)  := by
          intro i
          simp only [one_div, inv_pow, sub_self, add_zero, norm_mul, norm_inv, norm_pow,
            RCLike.norm_ofNat, norm_norm, mul_comm, inv_pos, Nat.ofNat_pos, pow_pos, mul_le_mul_right]
          exact norm_bdd i

        exact summable_if_bounded this


  have fsummable : Summable fun n ↦ (1 / 2) ^ n * ‖gs n x - gs n y‖ := by
    have norm_bdd : ∀ n, ‖gs n x - gs n y‖  ≤ 1 + 1 := by
        exact fun n ↦ norm_sub_le_of_le (gs_bdd n x) (gs_bdd n y)
    ring_nf at norm_bdd

    have summable_if_bounded := @Summable.of_norm_bounded ℕ ℝ _ _
        (fun n ↦ (1/2)^n * ‖gs n x - gs n y‖) (fun n ↦ 2 * (1 / 2) ^ n) (Summable.mul_left 2 summable_geometric_two)

    have : (∀ (i : ℕ), ‖(fun n ↦ (1 / 2) ^ n * ‖gs n x - gs n y‖) i‖
          ≤ (fun n ↦ 2 * (1 / 2) ^ n) i)  := by
        intro i
        simp only [one_div, inv_pow, sub_self, add_zero, norm_mul, norm_inv, norm_pow,
            RCLike.norm_ofNat, norm_norm, mul_comm, inv_pos, Nat.ofNat_pos, pow_pos, mul_le_mul_right]
        exact norm_bdd i

    exact summable_if_bounded this

  have gsummable : Summable fun n ↦ (1 / 2) ^ n * ‖gs n y - gs n z‖ := by
    have norm_bdd : ∀ n, ‖gs n y - gs n z‖  ≤ 1 + 1 := by
        exact fun n ↦ norm_sub_le_of_le (gs_bdd n y) (gs_bdd n z)
    ring_nf at norm_bdd

    have summable_if_bounded := @Summable.of_norm_bounded ℕ ℝ _ _
          (fun n ↦ (1/2)^n * ‖gs n y - gs n z‖) (fun n ↦ 2 * (1 / 2) ^ n) (Summable.mul_left 2 summable_geometric_two)

    have : (∀ (i : ℕ), ‖(fun n ↦ (1 / 2) ^ n * ‖gs n y - gs n z‖) i‖
          ≤ (fun n ↦ 2 * (1 / 2) ^ n) i)  := by
        intro i
        simp only [one_div, inv_pow, sub_self, add_zero, norm_mul, norm_inv, norm_pow,
          RCLike.norm_ofNat, norm_norm, mul_comm, gt_iff_lt, inv_pos, Nat.ofNat_pos, pow_pos, mul_le_mul_right]
        exact norm_bdd i

    exact summable_if_bounded this

  have tsum_add_ineq : ∑' (n : ℕ), ((1 / 2) ^ n * ‖gs n x - gs n y‖ + (1 / 2) ^ n * ‖gs n y - gs n z‖) =
      ∑' (n : ℕ), (1 / 2) ^ n * ‖gs n x - gs n y‖ + ∑' (n : ℕ), (1 / 2)^ n * ‖gs n y - gs n z‖ := by
    rw [tsum_add fsummable gsummable]

  rw [tsum_add_ineq] at tsum_tri_ineq
  exact tsum_tri_ineq

noncomputable def ourMetricSpace : MetricSpace X where
  dist := ourMetric gs
  dist_self := by
    intro x
    exact (ourMetric_self_iff gs gs_sep gs_bdd ).mpr rfl
  dist_comm := by
    intro x y
    exact (ourMetric_comm gs x y)
  dist_triangle := by
    intro x y z
    exact (ourMetric_triangle gs gs_bdd x y z)
  edist_dist := by simp [← ENNReal.ofReal_coe_nnreal]
  eq_of_dist_eq_zero := by
    intro x y
    exact (ourMetric_self_iff gs gs_sep gs_bdd).mp

def kopio (X :Type*) (gs : ℕ → X → 𝕜) (gs_sep : Set.SeparatesPoints (Set.range gs))
    (gs_bdd : ∀ n x, ‖gs n x‖ ≤ 1) := X

def kopio.mk (X :Type*) (gs : ℕ → X → 𝕜) (gs_sep : Set.SeparatesPoints (Set.range gs))
    (gs_bdd : ∀ n x, ‖gs n x‖ ≤ 1) :
    X → kopio X gs gs_sep gs_bdd := id

def kopio.toOrigin (X :Type*) (gs : ℕ → X → 𝕜) (gs_sep : Set.SeparatesPoints (Set.range gs))
    (gs_bdd : ∀ n x, ‖gs n x‖ ≤ 1) :
    kopio X gs gs_sep gs_bdd → X := id

noncomputable instance : MetricSpace (kopio X gs gs_sep gs_bdd) := ourMetricSpace gs gs_sep gs_bdd

--example (f : X → ℝ) (g : X → ℝ) (hf : Continuous f) (hg : Continuous g) : Continuous ((f + g) : X × X → ℝ ) := by sorry

lemma cont_ourMetric (gs_cont : ∀ (n : ℕ), Continuous (gs n)) : Continuous (fun (p : X × X) ↦
    ourMetric gs p.1 p.2) := by

  apply @continuous_tsum ℕ (X × X) ℝ _ _ (fun (n : ℕ) ↦ 2 * (1 / 2) ^ n) _
      (fun n ↦ fun (x, y) ↦ (1 / 2) ^ n * ‖gs n x - gs n y‖) ?_ (Summable.mul_left _ summable_geometric_two) ?_
  · intro i
    simp only [one_div, inv_pow]
    have cont_xy : Continuous (fun (x,y) ↦ ‖gs i x - gs i y‖) := by
      have : Continuous (fun (x,y) ↦ gs i x - gs i y) := by
        have := Continuous.add (by exact Continuous.fst' (gs_cont i)) (Continuous.snd' (Continuous.neg (gs_cont i)))
        ring_nf at this
        exact this
      exact Continuous.norm this

    exact Continuous.mul continuous_const cont_xy

  · simp only [inv_pow, norm_mul, norm_inv, norm_pow, RCLike.norm_ofNat, norm_norm,
    Prod.forall]
    intro n a b
    simp only [one_div, norm_inv, RCLike.norm_ofNat, inv_pow, mul_comm]
    rw [mul_le_mul_right]
    · have := norm_sub_le_of_le (gs_bdd n a) (gs_bdd n b)
      linarith
    · simp only [inv_pos, Nat.ofNat_pos, pow_pos]

lemma cont_ourMetric' (gs_cont : ∀ (n : ℕ), Continuous (gs n)) : Continuous (fun (p : X × X) ↦
    dist (kopio.mk X gs gs_sep gs_bdd p.1) (kopio.mk X gs gs_sep gs_bdd p.2)) := by
  exact cont_ourMetric gs gs_bdd gs_cont

example (X Y Z : Type*) [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (ϕ : X × Y → Z) (x : X) (hphi : Continuous ϕ) : Continuous (fun y ↦ ϕ ⟨x, y⟩ ) := by
  exact Continuous.along_snd hphi

lemma cont_kopio_mk (X :Type*) [TopologicalSpace X] [CompactSpace X] (gs : ℕ → X → 𝕜)
    (gs_sep : Set.SeparatesPoints (Set.range gs)) (gs_bdd : ∀ n x, ‖gs n x‖ ≤ 1)
    (gs_cont : ∀ n, Continuous (gs n)) :
    Continuous (kopio.mk X gs gs_sep gs_bdd) := by
  apply Metric.continuous_iff'.mpr
  intro x ε hε
  have cont_dist : Continuous (fun y ↦ dist (kopio.mk X gs gs_sep gs_bdd y)
      (kopio.mk X gs gs_sep gs_bdd x)) := by
    apply Continuous.along_fst (cont_ourMetric' gs gs_sep gs_bdd gs_cont)

  have interval_open : IsOpen (Set.Iio ε) := by exact isOpen_Iio
  have := @IsOpen.mem_nhds X x _ _ (cont_dist.isOpen_preimage _ interval_open) (by simpa using hε)
  filter_upwards [this] with y hy using hy


lemma cont_kopio_toOrigin (X :Type*) [TopologicalSpace X] [CompactSpace X] (gs : ℕ → X → 𝕜)
    (gs_sep : Set.SeparatesPoints (Set.range gs)) (gs_bdd : ∀ n x, ‖gs n x‖ ≤ 1)
    (gs_cont : ∀ n, Continuous (gs n)):
    Continuous (kopio.toOrigin X gs gs_sep gs_bdd) := by
  have symm : ∀ (s : Set X), kopio.toOrigin X gs gs_sep gs_bdd ⁻¹' s = kopio.mk X gs gs_sep gs_bdd '' s := by
    exact fun s ↦ Eq.symm (Set.EqOn.image_eq_self fun ⦃x⦄ ↦ congrFun rfl)
  have : ∀ (s : Set X), IsClosed s → IsClosed (kopio.toOrigin X gs gs_sep gs_bdd ⁻¹' s) := by
    intro M M_closed
    have M_cpt_X := IsClosed.isCompact M_closed
    rw [@isCompact_iff_finite_subcover X _ M] at M_cpt_X
    have : ∀ s : Set (kopio X gs gs_sep gs_bdd), IsOpen s → IsOpen (kopio.mk X gs gs_sep gs_bdd ⁻¹' s) := by
      intro s
      have := @cont_kopio_mk 𝕜 _ X _ _ gs gs_sep gs_bdd gs_cont
      rw [continuous_def] at this
      specialize this s
      exact this
    have : IsClosed (kopio.toOrigin X gs gs_sep gs_bdd ⁻¹' M) := by
      simp [symm M]
      have M_image_cpt : IsCompact (kopio.mk X gs gs_sep gs_bdd '' M) := by
        apply isCompact_of_finite_subcover
        intro _ Us Usi_open
        simp [kopio.mk]
        exact fun a ↦ M_cpt_X Us (fun i ↦ this (Us i) (Usi_open i)) a
      exact IsCompact.isClosed M_image_cpt
    exact this
  have cont_iff_closed := @continuous_iff_isClosed (kopio X gs gs_sep gs_bdd) X _ _ (kopio.toOrigin X gs gs_sep gs_bdd)
  simp [← cont_iff_closed] at this
  exact this


noncomputable def homeomorph_OurMetric :
  X ≃ₜ kopio X gs gs_sep gs_bdd where
    toFun := kopio.mk X gs gs_sep gs_bdd
    invFun := kopio.toOrigin X gs gs_sep gs_bdd
    left_inv := congrFun rfl
    right_inv := congrFun rfl
    continuous_toFun := cont_kopio_mk X gs gs_sep gs_bdd gs_cont
    continuous_invFun := cont_kopio_toOrigin X gs gs_sep gs_bdd gs_cont

--#check X ≃ₜ ourMetricSpace gs
#check ourMetricSpace gs
#check BoundedContinuousFunction.mkOfCompact
#check ContinuousMap.mk
#check Continuous.comp

/- If X is compact, and there exists a seq of continuous real-valued functions that
separates points on X, then X is metrizable. -/
lemma X_metrizable (X 𝕜 : Type*) [NormedField 𝕜] [IsSensiblyNormed 𝕜] [TopologicalSpace X]
    [CompactSpace X] (gs : ℕ → X → 𝕜) (gs_cont : ∀ n, Continuous (gs n))
    (gs_sep : Set.SeparatesPoints (Set.range gs)): --(gs_bdd : ∀ n x, ‖gs n x‖ ≤ 1) : --gs_bdd ei pitäisi tarvita
    TopologicalSpace.MetrizableSpace X := by
  --refine ⟨?_⟩

  let hs := fun (n : ℕ) ↦ squeeze 𝕜 ∘ gs n
  have hs_sep : Set.SeparatesPoints (Set.range hs) := by
    intro x y x_ne_y
    unfold_let
    simp only [Set.mem_range, exists_exists_eq_and, Function.comp_apply]
    specialize gs_sep x_ne_y
    simp at gs_sep

    obtain ⟨a⟩ := gs_sep
    have : ∀ x y : 𝕜, x ≠ y → squeeze 𝕜 x ≠ squeeze 𝕜 y := by
      exact fun x y a a_1 ↦ a (inj_squeeze 𝕜 a_1)
    use a
    apply this
    assumption
  have hs_bdd : ∀ (n : ℕ) (x : X), ‖hs n x‖ ≤ 1 := by
    exact fun n x ↦ bdd_squeeze 𝕜 (gs n x) (gs n x)

  have hs_cont : ∀ n : ℕ, Continuous (hs n) := by
    exact fun n ↦ Continuous.comp (cont_squeeze 𝕜) (gs_cont n)

  have hom := homeomorph_OurMetric hs hs_cont hs_sep hs_bdd

  exact hom.inducing.metrizableSpace (f := hom) hom.injective


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
#check @Inducing.pseudoMetrizableSpace X (kopio X gs gs_sep gs_bdd) _ _ _
#check Homeomorph.inducing
#check TopologicalSpace.MetrizableSpace
#check MetricSpace.induced
#check Inducing.metrizableSpace




end Metrizability_lemma



section Seq_Banach_Alaoglu

--variable (𝕜 : Type*)
variable (V : Type*) [SeminormedAddCommGroup V] [NormedSpace ℂ V]
variable [TopologicalSpace.SeparableSpace V]
variable (K : Set (WeakDual ℂ V)) (K_cpt : IsCompact K)

/- There exists a sequence of continuous functions that separates points on V*. -/
lemma exists_gs : ∃ (gs : ℕ → (WeakDual ℂ V) → ℂ), (∀ n, Continuous (gs n)) ∧ Set.SeparatesPoints (Set.range gs) := by
  set vs := TopologicalSpace.denseSeq V
  set gs : ℕ → K → ℂ := fun n ↦ fun ϕ ↦ (ϕ : WeakDual ℂ V) (vs n)
  set gs2 : ℕ → WeakDual ℂ V → ℂ := fun n ↦ fun ϕ ↦ (ϕ : WeakDual ℂ V) (vs n)
  use gs2
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

#check @TopologicalSpace.exists_countable_dense (WeakDual ℂ V) _
#check @DenseRange.equalizer


/- A compact subset of the dual V* of a separable space V is metrizable. -/
lemma subset_metrizable : TopologicalSpace.MetrizableSpace K := by
  have k_cpt' : CompactSpace K := by exact isCompact_iff_compactSpace.mp K_cpt
  obtain ⟨gs, gs_cont, gs_sep⟩ := exists_gs V K
  let hs : ℕ → K → ℂ := fun n ↦ fun ϕ ↦ gs n (ϕ : WeakDual ℂ V)
  apply X_metrizable K ℂ hs
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
theorem WeakDual.isSeqCompact_closedBall (x' : NormedSpace.Dual ℂ V) (r : ℝ) :
    IsSeqCompact (WeakDual.toNormedDual ⁻¹' Metric.closedBall x' r) := by

  have b_isCompact : IsCompact (WeakDual.toNormedDual ⁻¹' Metric.closedBall x' r) := by
    apply WeakDual.isCompact_closedBall
  have b_isCompact' : CompactSpace (WeakDual.toNormedDual ⁻¹' Metric.closedBall x' r) := by
    exact isCompact_iff_compactSpace.mp b_isCompact

  have b_isMetrizable : TopologicalSpace.MetrizableSpace (WeakDual.toNormedDual ⁻¹' Metric.closedBall x' r) := by
    exact subset_metrizable V (⇑toNormedDual ⁻¹' Metric.closedBall x' r) b_isCompact

  have seq_cpt_space := @FirstCountableTopology.seq_compact_of_compact (WeakDual.toNormedDual ⁻¹' Metric.closedBall x' r)
      _ _ b_isCompact'

  have seq_cont_phi : SeqContinuous (fun φ : (WeakDual.toNormedDual ⁻¹' Metric.closedBall x' r) ↦ (φ : WeakDual ℂ V)) := by
    refine continuous_iff_seqContinuous.mp ?_
    exact continuous_subtype_val

  have seq_incl := @SeqCompactSpace.range (WeakDual.toNormedDual ⁻¹' Metric.closedBall x' r) (WeakDual ℂ V) _ _ _ (fun φ ↦ φ) seq_cont_phi
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

end inf_dim
