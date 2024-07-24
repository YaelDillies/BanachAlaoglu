--import Mathlib
--import Mathlib.Topology.Defs.Sequences
import Mathlib.Topology.Sequences
variable [TopologicalSpace X][TopologicalSpace Y] {f : X → Y}
open Set Filter
open scoped Topology
theorem IsSeqCompact.image (f_cont : SeqContinuous f) {K : Set X} (K_cpt : IsSeqCompact K) :
    IsSeqCompact (f '' K) := by
  intro ys ys_in_fK
  choose xs xs_in_K fxs_eq_ys using ys_in_fK
  obtain ⟨a, a_in_K, phi, phi_mono, xs_phi_lim⟩ := K_cpt xs_in_K
  refine ⟨f a, mem_image_of_mem f a_in_K, phi, phi_mono, ?_⟩
  exact (f_cont xs_phi_lim).congr fun x ↦ fxs_eq_ys (phi x)

/-- The range of sequentially continuous function on a sequentially compact space is sequentially
compact. -/
theorem IsSeqCompact.range [SeqCompactSpace X] (f_cont : SeqContinuous f) :
    IsSeqCompact (Set.range f) := by
  --rw [← Set.image_univ]
  --exact IsSeqCompact.image f_cont ((seqCompactSpace_iff X).mp ‹SeqCompactSpace X›)
  have IsSeqCompact.univ := ‹SeqCompactSpace X›.seq_compact_univ
  simpa using IsSeqCompact.univ.image f_cont
