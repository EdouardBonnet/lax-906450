import Lax906450Proofs.WordExpressions
import Mathlib.Data.List.OfFn
import Mathlib.Logic.Equiv.Fin.Basic

namespace Lax906450Proofs.WordTables

open WordExpressions

set_option genSizeOfSpec false in
set_option genInjectivity false in
/-- A word list described by its length and the expression for one entry. -/
structure Table where
  length : Term
  entry : Term → Term

def single (a : Term) : Table := ⟨1, fun _ => a⟩

def append (a b : Table) : Table :=
  ⟨a.length + b.length, fun j => Term.chooseLt j a.length (a.entry j) (b.entry (j-a.length))⟩

/-- Concatenate a rectangular family of equal-length blocks in row order. -/
def blocks (rows cols : Term) (row : Term → Table) : Table :=
  ⟨rows * cols, fun j => (row (j / cols)).entry (j % cols)⟩

def triple (s a d : Term) : Table := append (single s) (append (single a) (single d))

structure Represents (xs : List ℕ) (i : ℕ) (t : Table) (w : List ℕ) : Prop where
  length : t.length.eval xs i = w.length
  entry : ∀ j : Term, ∀ h : j.eval xs i < w.length, (t.entry j).eval xs i = w[j.eval xs i]

variable {xs : List ℕ} {i : ℕ}

theorem single_spec (a : Term) : Represents xs i (single a) [a.eval xs i] := by
  refine ⟨rfl, fun j h => ?_⟩
  have he : j.eval xs i = 0 := by simpa using h
  simp [single, he]

theorem append_spec {a b : Table} {u v : List ℕ} (ha : Represents xs i a u)
    (hb : Represents xs i b v) : Represents xs i (append a b) (u++v) := by
  refine ⟨by simp [append, ha.length, hb.length], fun j hj => ?_⟩
  simp only [append, Term.eval_chooseLt, ha.length]
  by_cases h : j.eval xs i < u.length
  · rw [if_pos h, ha.entry j h, List.getElem_append_left h]
  · rw [if_neg h, List.getElem_append_right (by omega : u.length ≤ j.eval xs i)]
    have hh : (j-a.length).eval xs i < v.length := by
      simp only [Term.eval_sub, ha.length]; simp only [List.length_append] at hj; omega
    simpa [ha.length] using hb.entry (j-a.length) hh

theorem triple_spec (s a d : Term) :
    Represents xs i (triple s a d) [s.eval xs i, a.eval xs i, d.eval xs i] :=
  append_spec (single_spec _) (append_spec (single_spec _) (single_spec _))

theorem flatten_rect {α : Type*} {m k : ℕ} (f : Fin m → Fin k → α) :
    (List.ofFn fun u => List.ofFn (f u)).flatten =
      List.ofFn (fun p : Fin (m*k) => f p.divNat p.modNat) := by
  rw [List.ofFn_mul]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext u
  apply congrArg List.ofFn
  funext v
  simpa [finProdFinEquiv, Nat.mul_comm, Nat.add_comm] using
    (congrArg (fun p : Fin m × Fin k => f p.1 p.2)
      (finProdFinEquiv.symm_apply_apply (u, v))).symm

theorem blocks_spec {m k : ℕ} {m' k' : Term} {row : Term → Table} (F : Fin m → List ℕ)
    (hm : m'.eval xs i = m) (hk : k'.eval xs i = k)
    (hsize : ∀ u, (F u).length = k)
    (hrow : ∀ u : Term, ∀ hu : u.eval xs i < m, Represents xs i (row u) (F ⟨_,hu⟩)) :
    Represents xs i (blocks m' k' row) (List.ofFn F).flatten := by
  let f (u : Fin m) (v : Fin k) := (F u)[v.val]'(by rw [hsize]; exact v.isLt)
  have he (u : Fin m) : List.ofFn (f u) = F u := by
    apply List.ext_getElem <;> simp [f, hsize]
  have hrect : (List.ofFn F).flatten = List.ofFn (fun p : Fin (m*k) => f p.divNat p.modNat) := by
    rw [← flatten_rect]; simp_rw [he]
  rw [hrect]
  refine ⟨by simp [blocks, hm, hk], fun j hj => ?_⟩
  rw [List.getElem_ofFn]
  let p : Fin (m*k) := ⟨j.eval xs i, by simpa using hj⟩
  have hu : (j/k').eval xs i < m := by simpa [hk] using p.divNat.isLt
  have hv : (j%k').eval xs i < (F ⟨_,hu⟩).length := by
    rw [hsize]; simpa [hk] using p.modNat.isLt
  simpa [blocks, f, hk, Fin.divNat, Fin.modNat] using (hrow _ hu).entry _ hv

end Lax906450Proofs.WordTables
