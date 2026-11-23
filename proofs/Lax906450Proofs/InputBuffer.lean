import Lax906450Proofs.WordExpressions
import Lax808846Proofs.Lib.Fill

namespace Lax906450Proofs.InputBuffer

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning WordExpressions

private def readWord : Com :=
  .seq (.read "input.word") (Lib.Fill.put "input.data" "position" (.var "input.word"))

/-- Read the length-prefixed tape, append the zero used for out-of-bounds
lookups, and reset the position for the first output word. -/
def load : Com :=
  .seq (.read "input.length") <|
  .seq (.seq (.assign "position" (.lit 0))
    (.while (.lt (.var "position") (.var "input.length")) readWord)) <|
  .seq (.store "input.data" (.var "input.length") (.lit 0)) (.assign "position" (.lit 0))

private def Reading (xs : List ℕ) (σ : Env) : Prop :=
  σ.vars "input.length" = xs.length ∧ σ.vars "position" ≤ xs.length ∧
    σ.inp = xs.drop (σ.vars "position") ∧
    Lib.Fill.Below "input.data" "position" (xs.length + 1) (fun j => (xs[j]?).getD 0) σ

private theorem readWord_spec {B : ℕ} (xs : List ℕ) (hlen : xs.length < B)
    (hw : ∀ v ∈ xs, v < B) :
    Spec B (fun σ => Reading xs σ ∧ σ.vars "position" < xs.length) readWord
      (fun σ τ => Reading xs τ ∧ τ.vars "position" = σ.vars "position" + 1) 8 := by
  rintro σ ⟨⟨hcount, _, hinp, hfill⟩, hi⟩
  have hhead : σ.inp = xs[σ.vars "position"] :: xs.drop (σ.vars "position" + 1) :=
    hinp.trans List.cons_getElem_drop_succ.symm
  have hv : σ.inp.headD 0 = (xs[σ.vars "position"]?).getD 0 := by simp [hhead, hi]
  have hword : σ.inp.headD 0 < B := by
    rw [hhead]
    exact hw _ (List.getElem_mem hi)
  have hroom : σ.vars "position" < (σ.arrs "input.data").length := by rw [hfill.length]; omega
  unfold readWord Lib.Fill.put
  run_vcg
  · refine ⟨⟨by simp [hcount], by simpa using hi, by simp [hhead], ?_⟩, by simp⟩
    exact (hfill.step (by omega) hv).of_eq (by simp) (by simp)
  · simpa using hword

theorem load_run {B : ℕ} (xs : List ℕ) (hlen : xs.length < B) (hw : ∀ v ∈ xs, v < B) :
    ∃ τ, Run B load (initEnv (fun _ => xs.length + 1) (xs.length :: xs)) τ
        (12 * xs.length + 12) ∧ Ready xs 0 τ ∧ τ.out = [] := by
  let start := initEnv (fun _ => xs.length + 1) (xs.length :: xs)
  let afterHeader : Env := {start.setVar "input.length" xs.length with inp := xs}
  have header : Run B (.read "input.length") start afterHeader 1 := Run.read rfl
  have initial : Reading xs (afterHeader.setVar "position" 0) := by
    refine ⟨by simp [afterHeader], by simp, by simp [afterHeader], ?_⟩
    apply Lib.Fill.below_zero (g := fun _ => 0) _ (by simp)
    simp [afterHeader, start, initEnv, arrOf]
  obtain ⟨σ, loop, ⟨hcount, _, _, g, filled⟩, hpos⟩ :=
    (Spec.forRangeZero "position" "input.length" (Reading xs) xs.length 8 hlen
      (fun _ h => h.2.1) (fun _ h => h.1) (readWord_spec xs hlen hw)).run initial
  have hroom : xs.length < (σ.arrs "input.data").length := by rw [filled.length]; omega
  have store := Run.store (a := "input.data") (i := .var "input.length") (e := .lit 0)
    (evalB_var_iff.mpr ⟨hcount.symm, hcount ▸ hlen⟩) (evalB_lit (by omega : 0 < B)) hroom
  let τ := (σ.setArr "input.data" xs.length 0).setVar "position" 0
  have reset := Run.assign (x := "position")
    (evalB_lit (σ := σ.setArr "input.data" xs.length 0) (by omega : 0 < B))
  have run : Run B load start τ (12 * xs.length + 12) :=
    (header.seq (loop.seq (store.seq reset))).mono (by simp [Expr.size]; omega)
  refine ⟨τ, run, ⟨by simp [τ, hcount], by simp [τ], ?_⟩, run.out_eq (by decide)⟩
  intro j hj
  rcases lt_or_eq_of_le hj with hj | rfl
  · have hcell := filled.cell (j := j) (hpos ▸ hj)
    have hj' : j < (arrOf (xs.length + 1) g).length := by simp; omega
    simp [τ, Env.setArr, List.getElem?_set_ne (by omega : xs.length ≠ j), filled.arr,
      List.getElem?_eq_getElem hj', hcell]
  · simp [τ, Env.setArr, List.getElem?_set_self hroom]

end Lax906450Proofs.InputBuffer
