import Lax906450Proofs.ClosureLP
import Lax906450.Deficiency

namespace Lax906450Proofs.OptimalSupport

open Lax109476.LinearProgram Lax906450.Deficiency ClosureLP
open scoped Classical BigOperators

variable {n : ℕ}

noncomputable def support (f : Fin n → ℝ) : Finset (Fin n) := Finset.univ.filter (0 < f ·)

def indicator (A : Finset (Fin n)) (i : Fin n) : ℝ := if i ∈ A then 1 else 0

private theorem indicator_sum (A : Finset (Fin n)) : ∑ i, indicator A i = A.card := by
  simp [indicator]

private theorem small_step (f g : Fin n → ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ (∀ i, 0 < f i → δ ≤ f i) ∧ (∀ i, 0 < g i → δ ≤ g i) := by
  let vals := (Finset.univ.image f ∪ Finset.univ.image g).filter (0 < ·)
  let s := insert 1 vals
  have hne : s.Nonempty := ⟨1, Finset.mem_insert_self ..⟩
  refine ⟨s.min' hne, ?_, s.min'_le 1 (Finset.mem_insert_self ..), ?_, ?_⟩
  · have hm := s.min'_mem hne
    rcases Finset.mem_insert.mp hm with h | h
    · rw [h]; norm_num
    · exact (Finset.mem_filter.mp h).2
  · intro i hi
    exact s.min'_le _ (by simp [s, vals, hi])
  · intro i hi
    exact s.min'_le _ (by simp [s, vals, hi])

private noncomputable def perturb (δ : ℝ) (f : Fin n → ℝ) (A : Finset (Fin n)) (i : Fin n) :=
  max 0 (f i - δ) + δ * indicator A i

private theorem perturb_box {δ : ℝ} (hd : 0 < δ) (hd1 : δ ≤ 1) {f : Fin n → ℝ}
    (hf : ∀ i, 0 ≤ f i ∧ f i ≤ 1) (A : Finset (Fin n)) (i : Fin n) :
    0 ≤ perturb δ f A i ∧ perturb δ f A i ≤ 1 := by
  obtain ⟨h0,h1⟩ := hf i
  constructor <;> by_cases hi : i ∈ A <;> simp [perturb, indicator, hi, max_def] <;> split_ifs <;> linarith

private theorem perturb_sum {δ : ℝ} {f : Fin n → ℝ} (hf : ∀ i, 0 ≤ f i)
    (hd : 0 < δ) (hδ : ∀ i, 0 < f i → δ ≤ f i) (A : Finset (Fin n)) :
    ∑ i, perturb δ f A i = (∑ i, f i) + δ * ((A.card : ℝ) - (support f).card) := by
  have h (i : Fin n) : perturb δ f A i =
      f i - δ * indicator (support f) i + δ * indicator A i := by
    by_cases hi : 0 < f i
    · simp [perturb, indicator, support, hi, max_eq_right (sub_nonneg.mpr (hδ i hi))]
    · have he : f i = 0 := le_antisymm (le_of_not_gt hi) (hf i)
      simp [perturb, indicator, support, he, hd.le]
  simp only [h, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, indicator_sum]
  ring

/-- Integer weights encode the primary deficiency and the secondary minimum left size. -/
def score (A B : Finset (Fin n)) : ℤ := n * (A.card : ℤ) - ((n : ℤ) + 1) * B.card

theorem optimal_support (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x : Fin (columns n) → ℝ) (hx : IsPrimalOptimal (program ℝ G) x) :
    x 0 = n ∧
    Admissible G (support (x ∘ left)) (support (x ∘ right)) ∧
    ∀ A B, Admissible G A B → score A B ≤ score (support (x ∘ left)) (support (x ∘ right)) := by
  let f := x ∘ left
  let g := x ∘ right
  have hrepr : vector (x 0) f g = x := vector_eta x
  have hf := (feasible_iff G (x 0) f g).1 (hrepr.symm ▸ hx.1)
  have hcomp (t : ℝ) (a b : Fin n → ℝ) (h : Feasible G t a b) :
      t + value a b ≤ x 0 + value f g := by
    rw [← objective G, ← objective G, hrepr]
    exact hx.2 _ ((feasible_iff G ..).2 h)
  have ht := hcomp n f g {hf with marker := ⟨Nat.cast_nonneg _, le_rfl⟩}
  refine ⟨by linarith [hf.marker.2], ?_, ?_⟩
  · intro i hi j hij
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2.trans_le (hf.edges _ _ hij)⟩
  · intro A B hAB
    obtain ⟨δ, hd, hd1, hδf, hδg⟩ := small_step f g
    have hpert : Feasible G (x 0) (perturb δ f A) (perturb δ g B) := by
      refine ⟨hf.marker, perturb_box hd hd1 hf.left_box A, perturb_box hd hd1 hf.right_box B, ?_⟩
      intro i j hij
      apply add_le_add (max_le_max_left _ (sub_le_sub_right (hf.edges _ _ hij) _))
      apply mul_le_mul_of_nonneg_left _ hd.le
      by_cases hi : i ∈ A
      · simp [indicator, hi, hAB _ hi _ hij]
      · simp [indicator, hi]; split_ifs <;> norm_num
    have improvement := hcomp _ _ _ hpert
    simp only [value, perturb_sum (fun i => (hf.left_box i).1) hd hδf,
      perturb_sum (fun i => (hf.right_box i).1) hd hδg] at improvement
    have hs : (n : ℝ) * A.card - ((n : ℝ) + 1) * B.card ≤
        n * (support f).card - ((n : ℝ) + 1) * (support g).card := by
      apply le_of_mul_le_mul_left (a := δ) _ hd
      nlinarith only [improvement]
    unfold score
    exact_mod_cast hs

theorem lexicographic {A B X Y : Finset (Fin n)} (hs : score X Y ≤ score A B) :
    deficiency X Y ≤ deficiency A B ∧ (deficiency X Y = deficiency A B → A.card ≤ X.card) := by
  have formula (U W : Finset (Fin n)) :
      score U W = ((n : ℤ) + 1) * deficiency U W - U.card := by unfold score deficiency; ring
  rw [formula, formula] at hs
  have hX : X.card ≤ n := by simpa using Finset.card_le_univ X
  constructor
  · by_contra! h
    have hd : deficiency A B + 1 ≤ deficiency X Y := by omega
    have hn : 0 ≤ (n : ℤ) + 1 := by positivity
    have := mul_le_mul_of_nonneg_left hd hn
    nlinarith
  · intro he
    rw [he] at hs
    omega

end Lax906450Proofs.OptimalSupport
