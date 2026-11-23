import Lax906450Proofs.InputBuffer
import Lax109476Proofs.RamAutomaticLayout
import Lax109476Proofs.EncodingSize

namespace Lax906450Proofs.Tabulation

open WordExpressions Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax109476Proofs Lax759944.BinaryWordEncoding Lax759944.RamPolytime Polynomial

theorem length_le_bits (xs : List ℕ) : xs.length ≤ bitSize xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih => rw [List.length_cons, Lax109476Proofs.EncodingSize.bitSize_cons]; omega

private theorem member_fits {xs : List ℕ} {a : ℕ} (ha : a ∈ xs) : a < 2^(bitSize xs) := by
  apply (Nat.lt_size_self a).trans_le
  apply Nat.pow_le_pow_right (by decide)
  induction xs with
  | nil => simp at ha
  | cons v xs ih =>
    rw [Lax109476Proofs.EncodingSize.bitSize_cons]
    rcases List.mem_cons.mp ha with rfl | h
    · omega
    · have := ih h; omega

def output (count cell : Term) (xs : List ℕ) :=
  (List.range (count.eval xs 0)).map (fun i => cell.eval xs i)

def emit (cell : Term) : Com := .seq (.write cell.compile)
  (.assign "position" (.add (.var "position") (.lit 1)))

def program (count cell : Term) : Com :=
  .seq InputBuffer.load <|
  .seq (.assign "count" count.compile) <|
  .seq (.assign "position" (.lit 0)) (.while (.lt (.var "position") (.var "count")) (emit cell))

private def Invariant (xs : List ℕ) (cell : Term) (N : ℕ) (σ : Env) : Prop :=
  Ready xs (σ.vars "position") σ ∧ σ.vars "count" = N ∧ σ.vars "position" ≤ N ∧
  σ.out = (List.range (σ.vars "position")).map (fun i => cell.eval xs i)

private theorem emit_spec {xs : List ℕ} {cell : Term} {N B b : ℕ} (hb : 0 < b)
    (hl : xs.length < 2^b) (hw : ∀ x ∈ xs, x < 2^b) (hN : N < 2^b)
    (hB : 2^(b*cell.width) ≤ B) :
    Spec B (fun σ => Invariant xs cell N σ ∧ σ.vars "position" < N)
      (emit cell) (fun σ τ => Invariant xs cell N τ ∧ τ.vars "position" = σ.vars "position"+1)
      (cell.compile.size + 5) := by
  rintro σ ⟨⟨hr,hcount,_,hout⟩, hp⟩
  have hbase : 2^b ≤ B := le_trans (Nat.pow_le_pow_right (by decide)
    (by simpa using Nat.mul_le_mul_left b cell.width_pos)) hB
  have he := (cell.compile_eval hr hb hl (hp.trans hN) hw hB).1
  let ν : Env := {σ with out := σ.out ++ [cell.eval xs (σ.vars "position")]}
  have hwrite : Run B (.write cell.compile) σ ν (1+cell.compile.size) := Run.write he
  have hinc : (Expr.add (.var "position") (.lit 1)).evalB B ν = some (σ.vars "position"+1) := by
    apply evalB_bin (evalB_var (x := "position") (hp.trans (hN.trans_le hbase)))
      (evalB_lit (lt_of_lt_of_le (Nat.one_lt_pow hb.ne' (by decide : 1 < 2)) hbase))
    exact (Nat.succ_le_of_lt hp).trans_lt (hN.trans_le hbase)
  refine ⟨_, (hwrite.seq (Run.assign hinc)).mono (by simp [Expr.size]; omega), ?_⟩
  simp [Invariant, ν, hcount, hout, List.range_succ, Nat.succ_le_of_lt hp]
  exact ⟨by simpa using hr.len, by simp, hr.data⟩

private theorem program_run (count cell : Term) (xs : List ℕ) (b B : ℕ) (hb : 0 < b)
    (hl : xs.length < 2^b) (hN : count.eval xs 0 < 2^b) (hw : ∀ x ∈ xs, x < 2^b)
    (hBc : 2^(b*count.width) ≤ B) (hBe : 2^(b*cell.width) ≤ B) :
    ∃ τ, Run B (program count cell) (initEnv (fun _ => xs.length+1) (xs.length::xs)) τ
      (12*xs.length + (cell.compile.size+9)*count.eval xs 0 + count.compile.size + 24) ∧
      τ.out = output count cell xs := by
  have hbase : 2^b ≤ B := le_trans (Nat.pow_le_pow_right (by decide)
    (by simpa using Nat.mul_le_mul_left b count.width_pos)) hBc
  obtain ⟨ν, hload, hready, hout⟩ := InputBuffer.load_run xs (hl.trans_le hbase)
    (fun x hx => (hw x hx).trans_le hbase)
  let N := count.eval xs 0
  have hcount := (count.compile_eval hready hb hl (by positivity) hw hBc).1
  have hstart : Invariant xs cell N ((ν.setVar "count" N).setVar "position" 0) := by
    simp [Invariant, hout]
    exact ⟨by simpa using hready.len, by simp, hready.data⟩
  have loop := (Spec.forRangeZero "position" "count" (Invariant xs cell N)
    N (cell.compile.size+5) (hN.trans_le hbase) (fun _ h => h.2.2.1) (fun _ h => h.2.1)
    (emit_spec hb hl hw hN hBe)).run hstart
  obtain ⟨τ,hloop,hend,hpos⟩ := loop
  refine ⟨τ, (hload.seq ((Run.assign hcount).seq hloop)).mono ?_, ?_⟩
  · dsimp only [N]
    ring_nf
    omega
  · simpa only [hpos, output, N] using hend.2.2.2

/-- A fixed tabulation with polynomially many output entries runs in polynomial
time. The bound accounts for reading arbitrary input words and every arithmetic
subexpression, including those evaluated on malformed inputs. -/
theorem polytime (count cell : Term) (P : Polynomial ℕ)
    (hP : ∀ xs, count.eval xs 0 ≤ P.eval (bitSize xs)) : RamPolytime (output count cell) := by
  let widthFactor := count.width + cell.width + 1
  let W : Polynomial ℕ := (X + P + C 3) * C widthFactor
  let T : Polynomial ℕ := C 12 * X + C (cell.compile.size+9)*P + C (count.compile.size+24)
  let b (xs : List ℕ) := bitSize xs + P.eval (bitSize xs) + 3
  have hW (xs : List ℕ) : W.eval (bitSize xs) = b xs * widthFactor := by simp [W, b]
  have hb (xs : List ℕ) : 0 < b xs := by unfold b; omega
  have hsize (xs : List ℕ) : xs.length < 2^(b xs) := by
    apply lt_of_le_of_lt _ Nat.lt_two_pow_self
    have := length_le_bits xs; unfold b; omega
  have hcnt (xs : List ℕ) : count.eval xs 0 < 2^(b xs) := by
    apply lt_of_le_of_lt _ Nat.lt_two_pow_self
    have := hP xs; unfold b; omega
  have hword (xs : List ℕ) (a : ℕ) (ha : a ∈ xs) : a < 2^(b xs) :=
    (member_fits ha).trans_le (Nat.pow_le_pow_right (by decide) (by unfold b; omega))
  have liftW (xs : List ℕ) (v : ℕ) (hv : v ≤ widthFactor) :
      2^(b xs*v) ≤ 2^(W.eval (bitSize xs)) := by
    rw [hW]; exact Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left _ hv)
  have hin (xs : List ℕ) : FitsInWords (W.eval (bitSize xs)) (xs.length :: xs) := by
    have hh := liftW xs 1 (by unfold widthFactor; omega)
    rw [Nat.mul_one] at hh
    intro a ha; rcases List.mem_cons.mp ha with rfl | ha
    · exact (hsize xs).trans_le hh
    · exact (hword xs a ha).trans_le hh
  have run (xs : List ℕ) := program_run count cell xs (b xs) _ (hb xs) (hsize xs)
    (hcnt xs) (hword xs) (liftW xs _ (by unfold widthFactor; omega))
    (liftW xs _ (by unfold widthFactor; omega))
  apply RamTransfer.ramPolytime_of_solves (RamAutomaticLayout.layout _) (program count cell) _ W T
  · intro xs; rw [hW]; exact Nat.mul_pos (hb xs) (by unfold widthFactor; omega)
  · intro xs a ha
    rcases List.mem_append.mp ha with hi | ho
    · exact hin xs a hi
    · obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ho
      have hi' := (List.mem_range.mp hi).trans (hcnt xs)
      let σ : Env := ⟨fun s => if s = "position" then i else xs.length, fun _ => xs ++ [0], [], []⟩
      have hready : Ready xs i σ := by
        refine ⟨by simp [σ], by simp [σ], ?_⟩
        intro j hj
        rcases lt_or_eq_of_le hj with hj | rfl
        · simp [σ, List.getElem?_append_left hj, List.getElem?_eq_getElem hj]
        · simp [σ]
      have h := liftW xs cell.width (by unfold widthFactor; omega)
      exact ((cell.compile_eval hready (hb xs) (hsize xs) hi' (hword xs) h).2).trans_le h
  · refine ⟨RamAutomaticLayout.layout_ok _, ?_, ?_⟩
    · rintro tape ⟨xs, rfl⟩; exact hin xs
    · rintro tape ⟨xs,rfl⟩
      obtain ⟨τ,hr,hout⟩ := run xs
      refine ⟨_,τ,hr.mono ?_,hout⟩
      simp only [List.tail_cons, T, eval_add, eval_mul, eval_C, eval_X]
      have := Nat.mul_le_mul_left 12 (length_le_bits xs)
      have := Nat.mul_le_mul_left (cell.compile.size+9) (hP xs)
      omega

end Lax906450Proofs.Tabulation
