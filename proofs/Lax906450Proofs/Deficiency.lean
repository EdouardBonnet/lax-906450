import Lax906450.Deficiency
import Mathlib.Tactic

namespace Lax906450Proofs.Deficiency

open Lax906450.Deficiency Lax906450.Partition

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
variable {A B : Finset V}

omit [Fintype V] in
private theorem least_left (h : Admissible G A B)
    (hmax : ∀ X Y, Admissible G X Y → deficiency X Y ≤ deficiency A B)
    (hmin : ∀ X Y, Admissible G X Y → deficiency X Y = deficiency A B → A.card ≤ X.card)
    {X Y : Finset V} (hXY : Admissible G X Y) (he : deficiency X Y = deficiency A B) :
    A ⊆ X := by
  have hi : Admissible G (A ∩ X) (B ∩ Y) := by
    intro u hu v huv
    exact Finset.mem_inter.mpr ⟨h u (Finset.mem_inter.mp hu).1 v huv,
      hXY u (Finset.mem_inter.mp hu).2 v huv⟩
  have hu : Admissible G (A ∪ X) (B ∪ Y) := by
    intro u hux v huv
    exact (Finset.mem_union.mp hux).elim
      (fun ha => Finset.mem_union_left _ (h u ha v huv))
      (fun hx => Finset.mem_union_right _ (hXY u hx v huv))
  have hm := hmax _ _ hu
  have hm' := hmax _ _ hi
  have ha := Finset.card_union_add_card_inter A X
  have hb := Finset.card_union_add_card_inter B Y
  have heq : deficiency (A ∩ X) (B ∩ Y) = deficiency A B := by
    unfold deficiency at *; omega
  have hsub : A ∩ X = A := Finset.eq_of_subset_of_card_le Finset.inter_subset_left
    (hmin _ _ hi heq)
  exact hsub ▸ (Finset.inter_subset_right : A ∩ X ⊆ X)

/--
---
conclusion: Lax906450.Deficiency.partition_of_maximum
---
Maximizers are closed under componentwise union and intersection. Consequently
the smallest left part is contained in every maximizing left part. Reflecting
a pair to the complements of its two parts in reverse order proves disjointness.
Exchanging the zero vertices of a minimum cover for the one vertices gives
persistency. Extending the maximizing pair by the two sides of a residual
cover gives the half-order bound.
-/
theorem partition_of_maximum (G : SimpleGraph V) (A B : Finset V)
    (h : Admissible G A B)
    (hmax : ∀ X Y, Admissible G X Y → deficiency X Y ≤ deficiency A B)
    (hmin : ∀ X Y, Admissible G X Y → deficiency X Y = deficiency A B → A.card ≤ X.card) :
    IsPartition G A B := by
  classical
  have hr : Admissible G Bᶜ Aᶜ := by
    intro u hu v huv
    exact Finset.mem_compl.mpr fun hv => Finset.mem_compl.mp hu (h v hv u huv.symm)
  have he : deficiency Bᶜ Aᶜ = deficiency A B := by
    simp only [deficiency, Finset.card_compl]
    have := Finset.card_le_univ A
    have := Finset.card_le_univ B
    omega
  have hd := least_left h hmax hmin hr he
  have hd' : Disjoint A B := Finset.disjoint_left.mpr fun _ ha => Finset.mem_compl.mp (hd ha)
  refine ⟨hd', h, ?_, ?_⟩
  · intro C hc hcov
    let H := middle A B
    have ext : Admissible G (A ∪ (H \ C)) (B ∪ C) := by
      intro u hu v huv
      rcases Finset.mem_union.mp hu with hu | hu
      · exact Finset.mem_union_left _ (h u hu v huv)
      rcases Finset.mem_sdiff.mp hu with ⟨hu, huc⟩
      by_cases hv : v ∈ B
      · exact Finset.mem_union_left _ hv
      have hvA : v ∉ A := fun ha => (Finset.mem_compl.mp hu) (Finset.mem_union_right _ (h v ha u huv.symm))
      have hvH : v ∈ H := Finset.mem_compl.mpr (by simp [hv, hvA])
      exact Finset.mem_union_right _ ((hcov u hu v hvH huv).resolve_left huc)
    have dis : Disjoint A (H \ C) := Finset.disjoint_left.mpr fun v ha hv =>
      Finset.mem_compl.mp (Finset.mem_sdiff.mp hv).1 (Finset.mem_union_left _ ha)
    have h₁ := hmax _ _ ext
    have h₂ := Finset.card_union_le B C
    have h₃ := Finset.card_sdiff_add_card_eq_card (show C ⊆ H from hc)
    simp only [deficiency, Finset.card_union_of_disjoint dis] at h₁
    change H.card ≤ 2 * C.card
    omega
  · intro S hcov hopt
    have exchange : G.IsVertexCover ((S \ A ∪ B : Finset V) : Set V) := by
      intro u v huv
      by_cases hu : u ∈ A
      · exact Or.inr (Finset.mem_union_right _ (h u hu v huv))
      by_cases hv : v ∈ A
      · exact Or.inl (Finset.mem_union_right _ (h v hv u huv.symm))
      exact (hcov huv).imp
        (fun hs => Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hs, hu⟩))
        (fun hs => Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hs, hv⟩))
    have subpair : Admissible G (A \ S) (B ∩ S) := by
      intro u hu v huv
      exact Finset.mem_inter.mpr ⟨h u (Finset.mem_sdiff.mp hu).1 v huv,
        (hcov huv).resolve_left (Finset.mem_sdiff.mp hu).2⟩
    have hx := hopt _ exchange
    have count : (S \ A ∪ B).card ≤ (S \ A).card + (B \ S).card := by
      apply le_trans (Finset.card_le_card (t := (S \ A) ∪ (B \ S)) ?_) (Finset.card_union_le _ _)
      intro v hv
      rcases Finset.mem_union.mp hv with hv | hv
      · exact Finset.mem_union_left _ hv
      by_cases hs : v ∈ S
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hs, fun ha => Finset.disjoint_left.mp hd' ha hv⟩)
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hv, hs⟩)
    have h₁ := Finset.card_sdiff_add_card_inter S A
    have h₂ := Finset.card_sdiff_add_card_inter A S
    have h₃ := Finset.card_sdiff_add_card_inter B S
    rw [Finset.inter_comm S A] at h₁
    have hm := hmax _ _ subpair
    have heq : deficiency (A \ S) (B ∩ S) = deficiency A B := by unfold deficiency at *; omega
    have h₄ := hmin _ _ subpair heq
    have h₅ : (A ∩ S).card = 0 := by omega
    have h₆ : (B \ S).card = 0 := by unfold deficiency at heq; omega
    exact ⟨Finset.sdiff_eq_empty_iff_subset.mp (Finset.card_eq_zero.mp h₆),
      Finset.disjoint_iff_inter_eq_empty.mpr (Finset.card_eq_zero.mp h₅)⟩

end Lax906450Proofs.Deficiency
