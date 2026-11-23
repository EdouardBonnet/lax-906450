import Lax109476.CertifiedOptimization
import Lax906450.Partition
import Mathlib.Tactic

namespace Lax906450Proofs.ClosureLP

open Lax109476.LinearProgram Lax109476.RationalCertificates
open scoped BigOperators

variable {n : ℕ}

abbrev columns (n : ℕ) := n + n + 1
abbrev rows (n : ℕ) := columns n + n * n

/-- The first coordinate carries the order through the solver. The other
coordinates belong to the two copies of the vertex set. -/
def vector {K : Type} (t : K) (f g : Fin n → K) : Fin (columns n) → K :=
  Fin.cons t (Fin.append f g)

def left (i : Fin n) : Fin (columns n) := (Fin.castAdd n i).succ
def right (i : Fin n) : Fin (columns n) := (Fin.natAdd n i).succ

@[simp] theorem vector_zero {K : Type} (t : K) (f g : Fin n → K) : vector t f g 0 = t := rfl
@[simp] theorem vector_left {K : Type} (t : K) (f g : Fin n → K) (i : Fin n) :
    vector t f g (left i) = f i := by simp [vector, left]
@[simp] theorem vector_right {K : Type} (t : K) (f g : Fin n → K) (i : Fin n) :
    vector t f g (right i) = g i := by
  exact Fin.append_right ..

theorem vector_eta {K : Type} (v : Fin (columns n) → K) :
    vector (v 0) (fun i => v (left i)) (fun i => v (right i)) = v := by
  funext j
  refine Fin.cases ?_ (fun k => ?_) j
  · exact vector_zero ..
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) k
    · exact vector_left ..
    · exact vector_right ..

def basis {K : Type} [Zero K] [One K] (a j : Fin (columns n)) : K :=
  if j = a then 1 else 0

def program (K : Type) [Field K] (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    Program K (rows n) (columns n) where
  A := Fin.append basis fun r j =>
    let p := finProdFinEquiv.symm r
    basis (left p.1) j - basis (right p.2) j
  b := Fin.append (vector (n : K) (fun _ => 1) (fun _ => 1)) fun r =>
    let p := finProdFinEquiv.symm r
    if G.Adj p.1 p.2 then 0 else 1
  c := vector 1 (fun _ => (n : K)) (fun _ => -((n : K) + 1))

private theorem sum_basis {K : Type} [Field K] (x : Fin (columns n) → K) (a : Fin (columns n)) :
    ∑ j, basis a j * x j = x a := by classical simp [basis, ite_mul]

theorem box_row {K : Type} [Field K] (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x : Fin (columns n) → K) (i : Fin (columns n)) :
    rowValue (program K G) x (Fin.castAdd (n*n) i) = x i := by
  simp [rowValue, program, sum_basis]

theorem edge_row {K : Type} [Field K] (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x : Fin (columns n) → K) (r : Fin (n*n)) :
    rowValue (program K G) x (Fin.natAdd (columns n) r) =
      x (left (finProdFinEquiv.symm r).1) - x (right (finProdFinEquiv.symm r).2) := by
  simp [rowValue, program, sub_mul, Finset.sum_sub_distrib, sum_basis]

structure Feasible (G : SimpleGraph (Fin n)) (t : ℝ) (f g : Fin n → ℝ) : Prop where
  marker : 0 ≤ t ∧ t ≤ n
  left_box : ∀ i, 0 ≤ f i ∧ f i ≤ 1
  right_box : ∀ i, 0 ≤ g i ∧ g i ≤ 1
  edges : ∀ i j, G.Adj i j → f i ≤ g j

theorem feasible_iff (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (t : ℝ) (f g : Fin n → ℝ) :
    PrimalFeasible (program ℝ G) (vector t f g) ↔ Feasible G t f g := by
  constructor
  · rintro ⟨hpos, hrows⟩
    have box (i : Fin (columns n)) := hrows (Fin.castAdd (n*n) i)
    simp only [box_row] at box
    simp only [program, Fin.append_left] at box
    refine ⟨⟨hpos 0, box 0⟩, fun i => ?_, fun i => ?_, ?_⟩
    · simpa using And.intro (hpos (left i)) (box (left i))
    · simpa using And.intro (hpos (right i)) (box (right i))
    · intro i j hij
      have h := hrows (Fin.natAdd (columns n) (finProdFinEquiv (i,j)))
      rw [edge_row] at h
      simpa only [program, Fin.append_right, Equiv.symm_apply_apply, vector_left, vector_right, if_pos hij, sub_nonpos] using h
  · intro h
    constructor
    · intro k
      refine Fin.cases h.marker.1 (fun b => ?_) k
      exact Fin.addCases (fun i => by simpa only [vector, Fin.cons_succ, Fin.append_left, Fin.append_right] using (h.left_box i).1)
        (fun j => by simpa only [vector, Fin.cons_succ, Fin.append_left, Fin.append_right] using (h.right_box j).1) b
    · intro r
      refine Fin.addCases (fun k => ?_) (fun k => ?_) r
      · rw [box_row]
        simp only [program, Fin.append_left]
        refine Fin.cases h.marker.2 (fun b => ?_) k
        exact Fin.addCases (fun i => by simpa only [vector, Fin.cons_succ, Fin.append_left, Fin.append_right] using (h.left_box i).2)
          (fun j => by simpa only [vector, Fin.cons_succ, Fin.append_left, Fin.append_right] using (h.right_box j).2) b
      · rw [edge_row]
        simp only [vector_left, vector_right, program, Fin.append_right]
        split_ifs with hadj
        · exact sub_nonpos.mpr (h.edges _ _ hadj)
        · linarith [(h.left_box (finProdFinEquiv.symm k).1).2, (h.right_box (finProdFinEquiv.symm k).2).1]

def value (f g : Fin n → ℝ) : ℝ := n * (∑ i, f i) - ((n : ℝ) + 1) * (∑ i, g i)

theorem objective (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (t : ℝ) (f g : Fin n → ℝ) :
    primalValue (program ℝ G) (vector t f g) = t + value f g := by
  simp only [primalValue, program, vector, Fin.sum_univ_succ, Fin.sum_univ_add,
    Fin.cons_zero, Fin.cons_succ, Fin.append_left, Fin.append_right, value, one_mul,
    Finset.mul_sum, neg_mul, Finset.sum_neg_distrib, sub_eq_add_neg]

theorem cast_program (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    toReal (program ℚ G) = program ℝ G := by
  unfold toReal program
  congr 1
  · funext r j
    refine Fin.addCases (fun k => ?_) (fun k => ?_) r <;>
      simp only [Fin.append_left, Fin.append_right, basis, Rat.cast_sub, apply_ite, Rat.cast_one, Rat.cast_zero] <;> split_ifs <;> rfl
  · funext r
    refine Fin.addCases (fun k => ?_) (fun k => ?_) r
    · refine Fin.cases ?_ (fun j => ?_) k
      · simp
      · refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;> simp only [Fin.append_left, Fin.append_right, vector, Fin.cons_succ, Rat.cast_one]
    · simp [apply_ite]
  · funext j
    refine Fin.cases ?_ (fun k => ?_) j
    · simp
    · refine Fin.addCases (fun i => ?_) (fun i => ?_) k <;> simp only [Fin.append_left, Fin.append_right, vector, Fin.cons_succ, Rat.cast_one, Rat.cast_neg, Rat.cast_add, Rat.cast_natCast]

theorem feasible_bounded (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    IsFeasible (program ℝ G) ∧ IsBoundedAbove (program ℝ G) := by
  refine ⟨⟨_, (feasible_iff G 0 (fun _ => 0) (fun _ => 0)).2
    ⟨by simp, by simp, by simp, by simp⟩⟩, (n : ℝ) + n * n, ?_⟩
  intro x hx
  rw [← vector_eta x] at hx ⊢
  have h := (feasible_iff G _ _ _).1 hx
  rw [objective]
  have hf : ∑ i, x (left i) ≤ (n : ℝ) := by
    simpa using Finset.sum_le_sum (s := Finset.univ) fun i _ => (h.left_box i).2
  have hg : 0 ≤ ∑ i, x (right i) := Finset.sum_nonneg fun i _ => (h.right_box i).1
  unfold value
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
  nlinarith [mul_nonneg hn (sub_nonneg.mpr hf), mul_nonneg hn hg, h.marker.2]

end Lax906450Proofs.ClosureLP
