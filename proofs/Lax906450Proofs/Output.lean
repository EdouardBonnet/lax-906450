import Lax906450Proofs.OptimalSupport
import Lax906450Proofs.Tabulation
import Lax906450.StrongNemhauserTrotter
import Lax109476Proofs.WordDecoding

namespace Lax906450Proofs.Output

open Lax109476.RationalCertificates Lax109476.RationalEncoding Lax109476Proofs.WordDecoding
open Lax906450.StrongNemhauserTrotter WordExpressions ClosureLP OptimalSupport
open scoped Classical

/-- Read the graph order from the first primal coordinate of an optimal
certificate. Clipping bounds the output length on arbitrary word lists. -/
def count : Term := Term.minimum (.input 2) .length

def magnitude (j : Term) : Term := .input (2+3*j)

def tag : Term :=
  Term.chooseLt 0 (magnitude (1+.index)) 0
    (Term.chooseLt 0 (magnitude (1+count+.index)) 2 1)

def decode := Tabulation.output count tag

theorem polynomial : Lax759944.RamPolytime.RamPolytime decode := by
  apply Tabulation.polytime _ _ Polynomial.X
  intro xs
  simp only [count, Term.eval_minimum, Term.eval, Polynomial.eval_X]
  exact (min_le_right ..).trans (Tabulation.length_le_bits xs)

private theorem vector_magnitude {n : ℕ} (x : Fin n → ℚ) (j : Fin n) :
    (encodeVector x)[3*j.val+1]? = some (x j).num.natAbs := by
  induction n with
  | zero => exact Fin.elim0 j
  | succ n ih =>
    rw [← Fin.cons_self_tail x, encodeVector_cons]
    refine Fin.cases ?_ (fun k => ?_) j
    · simp [encodeRational]
    · simpa [encodeRational, Nat.mul_add, Nat.add_assoc] using ih (Fin.tail x) k

variable {n m : ℕ}

private theorem cert_magnitude (x : Fin (columns n) → ℚ) (y : Fin m → ℚ) (j : Fin (columns n)) :
    ((encodeCertificate (.optimal x y))[2+3*j.val]?).getD 0 = (x j).num.natAbs := by
  change (((0 :: (encodeVector x ++ encodeVector y))[2+3*j.val]?).getD 0) = _
  rw [show 2+3*j.val = (3*j.val+1)+1 by omega, List.getElem?_cons_succ,
    List.getElem?_append_left (by rw [encodeVector_length]; have := j.isLt; omega), vector_magnitude]
  rfl

private theorem positive_iff {q : ℚ} (hq : 0 ≤ q) : 0 < q.num.natAbs ↔ 0 < (q : ℝ) := by
  rw [Nat.pos_iff_ne_zero, Int.natAbs_ne_zero, Rat.num_ne_zero, Rat.cast_pos]
  exact ⟨lt_of_le_of_ne hq ∘ Ne.symm, ne_of_gt⟩

theorem decode_optimal (x : Fin (columns n) → ℚ) (y : Fin m → ℚ)
    (h0 : x 0 = n) (hpos : ∀ j, 0 ≤ x j) :
    decode (encodeCertificate (.optimal x y)) =
      labels (support (realVector x ∘ left)) (support (realVector x ∘ right)) := by
  let xs := encodeCertificate (.optimal x y)
  have hn : n ≤ xs.length := by
    simp [xs, encodeCertificate, encodeVector_length, columns]; omega
  have hcount (i : ℕ) : count.eval xs i = n := by
    have marker : (xs[2]?).getD 0 = n := by
      simpa only [xs, Fin.val_zero, Nat.mul_zero, Nat.add_zero, h0, Rat.num_natCast,
        Int.natAbs_natCast] using cert_magnitude x y 0
    simp [count, marker, Nat.min_eq_left hn]
  apply List.ext_getElem
  · simp [decode, Tabulation.output, labels, hcount, xs]
  · intro i h₁ h₂
    have hi : i < n := by simpa [labels] using h₂
    let v : Fin n := ⟨i,hi⟩
    have hl : ((xs[2+3*(1+i)]?).getD 0) = (x (left v)).num.natAbs := by
      simpa [xs, left, v, Nat.add_comm] using cert_magnitude x y (left v)
    have hr : ((xs[2+3*(1+n+i)]?).getD 0) = (x (right v)).num.natAbs := by
      simpa [xs, right, v, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using cert_magnitude x y (right v)
    change ((List.range (count.eval xs 0)).map (fun j => tag.eval xs j))[i] =
      (labels (support (realVector x ∘ left)) (support (realVector x ∘ right)))[i]
    simp [tag, magnitude, hcount, hl, hr, labels, support, realVector, positive_iff (hpos _), v]

end Lax906450Proofs.Output
