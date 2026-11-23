import Lax808846Proofs.Reasoning

namespace Lax906450Proofs.WordExpressions

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

-- These syntax types use structural recursion and the explicit width bound below.
section
set_option genSizeOfSpec false
set_option genInjectivity false

/-- The arithmetic needed to index the adjacency matrix and LP coefficients. -/
inductive Op where | add | sub | mul | div

inductive Term where
  | lit (v : ℕ)
  | length
  | index
  | input (i : Term)
  | bin (op : Op) (a b : Term)

end

@[simp] def Op.imp : Op → Bop
  | .add => .add | .sub => .sub | .mul => .mul | .div => .div

namespace Term

instance (n : ℕ) : OfNat Term n := ⟨.lit n⟩
instance : Add Term := ⟨.bin .add⟩
instance : Sub Term := ⟨.bin .sub⟩
instance : Mul Term := ⟨.bin .mul⟩
instance : Div Term := ⟨.bin .div⟩
instance : Mod Term := ⟨fun a b => a - (a / b) * b⟩

@[simp] def eval (xs : List ℕ) (i : ℕ) : Term → ℕ
  | .lit v => v
  | .length => xs.length
  | .index => i
  | .input e => (xs[eval xs i e]?).getD 0
  | .bin op a b => op.imp.apply (eval xs i a) (eval xs i b)

@[simp] theorem eval_numeral (xs : List ℕ) (i n : ℕ) :
    eval xs i (no_index (OfNat.ofNat n)) = n := rfl
@[simp] theorem eval_add (xs : List ℕ) (i : ℕ) (a b : Term) :
    eval xs i (a+b) = eval xs i a + eval xs i b := rfl
@[simp] theorem eval_sub (xs : List ℕ) (i : ℕ) (a b : Term) :
    eval xs i (a-b) = eval xs i a - eval xs i b := rfl
@[simp] theorem eval_mul (xs : List ℕ) (i : ℕ) (a b : Term) :
    eval xs i (a*b) = eval xs i a * eval xs i b := rfl
@[simp] theorem eval_div (xs : List ℕ) (i : ℕ) (a b : Term) :
    eval xs i (a/b) = eval xs i a / eval xs i b := rfl
@[simp] theorem eval_mod (xs : List ℕ) (i : ℕ) (a b : Term) :
    eval xs i (a%b) = eval xs i a % eval xs i b := by
  change _ - _ / _ * _ = _
  rw [Nat.mul_comm, ← Nat.mod_eq_sub_mul_div]

def minimum (a b : Term) := a - (a-b)
def positive (a : Term) : Term := 1 - (1-a)
def chooseLt (a b yes no : Term) : Term :=
  let flag := positive (b-a)
  flag * yes + (1-flag) * no

@[simp] theorem eval_minimum (xs : List ℕ) (i : ℕ) (a b : Term) :
    eval xs i (minimum a b) = min (eval xs i a) (eval xs i b) := by simp [minimum]; omega
@[simp] theorem eval_positive (xs : List ℕ) (i : ℕ) (a : Term) :
    eval xs i (positive a) = if 0 < eval xs i a then 1 else 0 := by
  simp only [positive, eval_sub, eval_numeral]
  split_ifs <;> omega
@[simp] theorem eval_chooseLt (xs : List ℕ) (i : ℕ) (a b yes no : Term) :
    eval xs i (chooseLt a b yes no) =
      if eval xs i a < eval xs i b then eval xs i yes else eval xs i no := by
  simp only [chooseLt, eval_add, eval_mul, eval_positive, eval_sub, eval_numeral, Nat.sub_pos_iff_lt]
  split_ifs <;> simp

def compile : Term → Expr
  | .lit n => .lit n
  | .length => .var "input.length"
  | .index => .var "position"
  | .input e =>
    let len := Expr.var "input.length"
    .get "input.data" (.sub len (.sub len (compile e)))
  | .bin op a b => .bin op.imp (compile a) (compile b)

/-- Sufficient number of bits per bit of the largest input word or loop index. -/
def width : Term → ℕ
  | .lit n => n+1
  | .length | .index => 1
  | .input a => width a + 1
  | .bin _ a b => width a + width b + 1

theorem width_pos (e : Term) : 0 < e.width := by cases e <;> simp [width]

end Term

structure Ready (xs : List ℕ) (i : ℕ) (σ : Env) : Prop where
  len : σ.vars "input.length" = xs.length
  pos : σ.vars "position" = i
  data : ∀ j ≤ xs.length, (σ.arrs "input.data")[j]? = some ((xs[j]?).getD 0)

private theorem input_bound (xs : List ℕ) (b j : ℕ) (h : ∀ x ∈ xs, x < 2^b) :
    (xs[j]?).getD 0 < 2^b := by
  by_cases hj : j < xs.length
  · simpa [List.getElem?_eq_getElem hj] using h _ (List.getElem_mem hj)
  · simp [List.getElem?_eq_none (by omega : xs.length ≤ j)]

private theorem bound_bin (op : Op) {a b u v : ℕ} (ha : a < 2^u) (hb : b < 2^v) :
    op.imp.apply a b < 2^(u+v+1) := by
  have hu := Nat.two_pow_pos u
  have hv := Nat.two_pow_pos v
  rw [pow_succ, pow_add]
  cases op with
  | add => simp [Op.imp]; nlinarith [Nat.mul_le_mul_left (2^u) hv, Nat.mul_le_mul_right (2^v) hu]
  | sub => simp [Op.imp]; have := Nat.sub_le a b; nlinarith [Nat.mul_le_mul_left (2^u) hv]
  | div => simp [Op.imp]; have := Nat.div_le_self a b; nlinarith [Nat.mul_le_mul_left (2^u) hv]
  | mul =>
    change a*b < _
    have := Nat.mul_le_mul ha.le hb.le
    nlinarith

/-- Evaluating an expression incurs its actual compiled expression cost. Each
array read clamps its address to the zero sentinel at the end of the input. -/
theorem Term.compile_eval (e : Term) {xs : List ℕ} {i b B : ℕ} {σ : Env}
    (h : Ready xs i σ) (hb : 0 < b) (hl : xs.length < 2^b) (hi : i < 2^b)
    (hw : ∀ x ∈ xs, x < 2^b) (hB : 2^(b*e.width) ≤ B) :
    e.compile.evalB B σ = some (e.eval xs i) ∧ e.eval xs i < 2^(b*e.width) := by
  have mono {j k : ℕ} (hjk : j ≤ k) : 2^(b*j) ≤ 2^(b*k) :=
    Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left _ hjk)
  have base : 2^b ≤ 2^(b*e.width) := by simpa using mono (e.width_pos)
  induction e with
  | lit v =>
    have hv : v < 2^(b*(v+1)) := (Nat.lt_two_pow_self (n := v)).trans_le
      (Nat.pow_le_pow_right (by decide) (by nlinarith))
    exact ⟨evalB_lit (hv.trans_le hB), hv⟩
  | length =>
    simp only [Term.width, mul_one] at hB ⊢
    exact ⟨by simpa [Term.compile, h.len] using
      (evalB_var (B := B) (σ := σ) (x := "input.length") (h.len ▸ hl.trans_le hB)), hl⟩
  | index =>
    simp only [Term.width, mul_one] at hB ⊢
    exact ⟨by simpa [Term.compile, h.pos] using
      (evalB_var (B := B) (σ := σ) (x := "position") (h.pos ▸ hi.trans_le hB)), hi⟩
  | input a ih =>
    have hs := mono (show a.width ≤ (Term.input a).width by simp [Term.width])
    have ⟨ha,_⟩ := ih (hs.trans hB) (by simpa using mono a.width_pos)
    let j := a.eval xs i
    have hj := input_bound xs b j hw
    have hlen : (Expr.var "input.length").evalB B σ = some xs.length :=
      evalB_var_iff.mpr ⟨h.len.symm, h.len ▸ hl.trans_le (base.trans hB)⟩
    have hsub := evalB_bin (op := .sub) hlen ha (show xs.length - j < B from
      (Nat.sub_le ..).trans_lt (hl.trans_le (base.trans hB)))
    have hidx := evalB_bin (op := .sub) hlen hsub (show xs.length - (xs.length-j) < B from
      (Nat.sub_le ..).trans_lt (hl.trans_le (base.trans hB)))
    have hdata := h.data (xs.length - (xs.length-j)) (Nat.sub_le ..)
    have heq : (xs[xs.length - (xs.length-j)]?).getD 0 = (xs[j]?).getD 0 := by
      by_cases hj' : j ≤ xs.length
      · rw [show xs.length - (xs.length-j) = j by omega]
      · simp [Nat.sub_eq_zero_of_le (by omega : xs.length ≤ j), List.getElem?_eq_none (by omega : xs.length ≤ j)]
    rw [heq] at hdata
    exact ⟨evalB_get hidx hdata (hj.trans_le (base.trans hB)), hj.trans_le base⟩
  | bin op a c iha ihc =>
    have ha := mono (show a.width ≤ (Term.bin op a c).width by simp [Term.width]; omega)
    have hc := mono (show c.width ≤ (Term.bin op a c).width by simp [Term.width]; omega)
    obtain ⟨hea,hva⟩ := iha (ha.trans hB) (by simpa using mono a.width_pos)
    obtain ⟨hec,hvc⟩ := ihc (hc.trans hB) (by simpa using mono c.width_pos)
    have hv := (bound_bin op hva hvc).trans_le (Nat.pow_le_pow_right (by decide)
      (show b*a.width + b*c.width + 1 ≤ b*(Term.bin op a c).width by
        simp only [Term.width, Nat.mul_add, Nat.mul_one]; omega))
    exact ⟨evalB_bin hea hec (hv.trans_le hB), hv⟩

end Lax906450Proofs.WordExpressions
