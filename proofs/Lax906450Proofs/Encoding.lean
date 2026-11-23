import Lax906450Proofs.WordTables
import Lax906450Proofs.ClosureLP
import Lax906450.StrongNemhauserTrotter
import Lax109476Proofs.WordDecoding

namespace Lax906450Proofs.Encoding

open WordExpressions WordTables Lax906450.StrongNemhauserTrotter
open Lax109476.RationalEncoding Lax109476Proofs.WordDecoding ClosureLP

variable {n : ℕ}

def order : Term := Term.minimum (.input 0) .length
def vars (n : Term) : Term := n+n+1
def consCount (n : Term) : Term := vars n+n*n

def equal (a b : Term) : Term := 1 - Term.positive ((a-b)+(b-a))

@[simp] theorem eval_equal (xs : List ℕ) (i : ℕ) (a b : Term) :
    (equal a b).eval xs i = if a.eval xs i = b.eval xs i then 1 else 0 := by
  simp only [equal, Term.eval_sub, Term.eval_numeral, Term.eval_positive, Term.eval_add]
  by_cases h : a.eval xs i = b.eval xs i
  · simp [h]
  · have hpos : 0 < a.eval xs i - b.eval xs i + (b.eval xs i - a.eval xs i) := by omega
    simp [h, hpos]

def natural (v : Term) : Table := triple 0 v 1
def vectorWords (k : Term) (entry : Term → Table) : Table := blocks k 3 entry
def unitRow (n r : Term) : Table := vectorWords (vars n) fun j => natural (equal j r)
def edgeRow (n r : Term) : Table := vectorWords (vars n) fun j =>
  let pos := equal j (1 + r/n)
  let neg := equal j (1+n+r%n)
  triple neg (pos+neg) 1

def matrix (n : Term) : Table :=
  append (blocks (vars n) (3*vars n) (unitRow n))
    (blocks (n*n) (3*vars n) (edgeRow n))

def bounds (n : Term) : Table :=
  append (natural n) (append (vectorWords (n+n) (fun _ => natural 1))
    (vectorWords (n*n) (fun r => natural (1 - Term.input (1+r)))))

def objectiveWords (n : Term) : Table :=
  append (natural 1) (append (vectorWords n (fun _ => natural n))
    (vectorWords n (fun _ => triple 1 (n+1) 1)))

def lpTable : Table :=
  let n := order
  append (single (consCount n)) (append (single (vars n))
    (append (matrix n) (append (bounds n) (objectiveWords n))))

@[simp] theorem graph_length (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    (encodeGraph G).length = n*n+1 := by
  unfold encodeGraph
  rw [flatten_rect]
  simp

theorem graph_entry (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (r : Fin (n*n)) :
    ((encodeGraph G)[1+r.val]?).getD 0 = if G.Adj r.divNat r.modNat then 1 else 0 := by
  unfold encodeGraph
  rw [flatten_rect, Nat.one_add]
  simp [r.isLt]

@[simp] theorem graph_order (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (i : ℕ) :
    order.eval (encodeGraph G) i = n := by
  simp only [order, Term.eval_minimum, Term.eval, graph_length]
  exact Nat.min_eq_left ((Nat.le_mul_self n).trans (Nat.le_succ _))

@[simp] theorem vars_eval (a : Term) (xs : List ℕ) (i : ℕ) :
    (vars a).eval xs i = columns (a.eval xs i) := by simp [vars, columns]

@[simp] theorem cons_eval (a : Term) (xs : List ℕ) (i : ℕ) :
    (consCount a).eval xs i = rows (a.eval xs i) := by simp [consCount, rows]

variable {xs : List ℕ} {i : ℕ}

theorem natural_spec (a : Term) :
    Represents xs i (natural a) (encodeRational (a.eval xs i : ℚ)) := by
  have hnon : ¬ (a.eval xs i : ℤ) < 0 := by omega
  simpa [natural, encodeRational, hnon] using (triple_spec (xs := xs) (i := i) 0 a 1)

theorem vector_spec {k : ℕ} {k' : Term} {entry : Term → Table} {F : Fin k → ℚ}
    (hk : k'.eval xs i = k)
    (he : ∀ j : Term, ∀ h : j.eval xs i < k, Represents xs i (entry j) (encodeRational (F ⟨_,h⟩))) :
    Represents xs i (vectorWords k' entry) (encodeVector F) := by
  rw [encodeVector, List.flatMap_def, List.map_ofFn]
  exact blocks_spec _ hk rfl (by simp [encodeRational]) he

private theorem unit_spec (a r : Term) (ha : a.eval xs i = n) (hr : r.eval xs i < columns n) :
    Represents xs i (unitRow a r) (encodeVector (@basis n ℚ _ _ ⟨_,hr⟩)) := by
  apply vector_spec (by simp [ha])
  intro j hj
  have h := natural_spec (xs := xs) (i := i) (equal j r)
  by_cases he : j.eval xs i = r.eval xs i <;>
    simpa [basis, Fin.ext_iff, he] using h

private theorem edge_spec (a r : Term) (ha : a.eval xs i = n) (hr : r.eval xs i < n*n) :
    let p : Fin (n*n) := ⟨r.eval xs i,hr⟩
    Represents xs i (edgeRow a r) (encodeVector (fun j =>
      (basis (left p.divNat) j : ℚ) - basis (right p.modNat) j)) := by
  dsimp only
  apply vector_spec (by simp [ha])
  intro j hj
  let k : Fin (n*n) := ⟨r.eval xs i,hr⟩
  have hdiv : r.eval xs i / n < n := k.divNat.isLt
  have hneq : 1+r.eval xs i/n ≠ 1+n+r.eval xs i%n := by omega
  have key := triple_spec (xs := xs) (i := i) (equal j (1+a+r%a))
    (equal j (1+r/a) + equal j (1+a+r%a)) 1
  have hleft : (⟨j.eval xs i,hj⟩ = left k.divNat) ↔ j.eval xs i = 1+r.eval xs i/n := by
    simp [Fin.ext_iff, left, Fin.divNat, Nat.add_comm, k]
  have hright : (⟨j.eval xs i,hj⟩ = right k.modNat) ↔ j.eval xs i = 1+n+r.eval xs i%n := by
    simp [Fin.ext_iff, right, Fin.modNat, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, k]
  have coeff (P Q : Prop) [Decidable P] [Decidable Q] (hd : ¬ (P ∧ Q)) :
      encodeRational ((if P then 1 else 0 : ℚ) - (if Q then 1 else 0)) =
        [if Q then 1 else 0, (if P then 1 else 0)+(if Q then 1 else 0), 1] := by
    by_cases hp : P <;> by_cases hq : Q <;> simp_all [encodeRational]
  change Represents xs i _ (encodeRational ((basis (left k.divNat) ⟨_,hj⟩ : ℚ) - basis (right k.modNat) ⟨_,hj⟩))
  simp only [basis, hleft, hright, coeff _ _ (by omega : ¬ (j.eval xs i = 1+r.eval xs i/n ∧
    j.eval xs i = 1+n+r.eval xs i%n))]
  simpa only [eval_equal, Term.eval_add, Term.eval_div, Term.eval_mod, Term.eval_numeral, ha] using key

private theorem matrix_spec (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (a : Term)
    (ha : a.eval xs i = n) : Represents xs i (matrix a) (encodeRows (program ℚ G).A) := by
  unfold matrix encodeRows
  rw [show (fun r => encodeVector (((program ℚ G).A) r)) =
      Fin.append (fun r => encodeVector (basis r))
        (fun r : Fin (n*n) => encodeVector (fun j => (basis (left r.divNat) j : ℚ) - basis (right r.modNat) j)) by
        funext r; refine Fin.addCases (fun k => ?_) (fun k => ?_) r <;>
          simp only [program, Fin.append_left, Fin.append_right, finProdFinEquiv_symm_apply]]
  rw [List.ofFn_fin_append, List.flatten_append]
  apply append_spec
  · apply blocks_spec _ (by simp [ha]) (by simp [ha]) (fun _ => encodeVector_length ..)
    exact fun r hr => unit_spec a r ha hr
  · apply blocks_spec _ (by simp [ha]) (by simp [ha]) (fun _ => encodeVector_length ..)
    exact fun r hr => edge_spec a r ha hr

theorem encode_append {k l : ℕ} (f : Fin k → ℚ) (g : Fin l → ℚ) :
    encodeVector (Fin.append f g) = encodeVector f ++ encodeVector g := by
  simp [encodeVector, List.ofFn_fin_append]

private theorem bounds_spec (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (i : ℕ) :
    Represents (encodeGraph G) i (bounds order) (encodeVector (program ℚ G).b) := by
  have ones : Fin.append (fun _ : Fin n => (1 : ℚ)) (fun _ : Fin n => (1 : ℚ)) = fun _ => (1 : ℚ) := by
    funext j; exact Fin.addCases (fun i => Fin.append_left ..) (fun i => Fin.append_right ..) j
  rw [show (program ℚ G).b = Fin.append
      (Fin.cons (n : ℚ) (fun _ : Fin (n+n) => (1 : ℚ)))
      (fun r : Fin (n*n) => if G.Adj r.divNat r.modNat then 0 else 1) by
        simp only [program, vector, ones, finProdFinEquiv_symm_apply]]
  rw [encode_append, encodeVector_cons, List.append_assoc]
  unfold bounds
  apply append_spec
  · simpa using (natural_spec (xs := encodeGraph G) (i := i) order)
  · apply append_spec
    · apply vector_spec (by simp)
      intro j hj; exact natural_spec (xs := encodeGraph G) (i := i) 1
    · apply vector_spec (by simp)
      intro r hr
      let p : Fin (n*n) := ⟨_, hr⟩
      have h := natural_spec (xs := encodeGraph G) (i := i) (1-Term.input (1+r))
      have he := graph_entry G p
      change Represents _ _ _ (encodeRational (if G.Adj p.divNat p.modNat then 0 else 1))
      simp only [Term.eval_sub, Term.eval, Op.imp, Lax808846Proofs.Imp.Bop.apply] at h
      rw [he] at h
      by_cases hadj : G.Adj p.divNat p.modNat <;> simpa [hadj] using h

private theorem obj_spec (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (i : ℕ) :
    Represents (encodeGraph G) i (objectiveWords order) (encodeVector (program ℚ G).c) := by
  simp only [program, vector, encodeVector_cons, encode_append, objectiveWords]
  apply append_spec (natural_spec 1)
  apply append_spec
  · apply vector_spec (by simp)
    intro j hj; simpa using (natural_spec (xs := encodeGraph G) (i := i) order)
  · apply vector_spec (by simp)
    intro j hj
    have he : encodeRational (-((n : ℚ) + 1)) = [1, n+1, 1] := by
      rw [← Nat.cast_add_one]
      simp only [encodeRational, Rat.neg_num, Rat.num_natCast, Rat.neg_den, Rat.den_natCast,
        Int.natAbs_neg, Int.natAbs_natCast]
      congr 1
      exact if_pos (by omega)
    change Represents _ _ _ (encodeRational (-((n : ℚ)+1)))
    rw [he]
    simpa using (triple_spec (xs := encodeGraph G) (i := i) 1 (order+1) 1)

theorem instance_spec (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (i : ℕ) :
    Represents (encodeGraph G) i lpTable (encodeProgram (program ℚ G)) := by
  rw [encodeProgram_rows, List.append_assoc]
  unfold lpTable
  apply append_spec (u := [_])
  · simpa using single_spec (xs := encodeGraph G) (i := i) (consCount order)
  apply append_spec (u := [_])
  · simpa using single_spec (xs := encodeGraph G) (i := i) (vars order)
  exact append_spec (matrix_spec G order (by simp)) (append_spec (bounds_spec G i) (obj_spec G i))

end Lax906450Proofs.Encoding
