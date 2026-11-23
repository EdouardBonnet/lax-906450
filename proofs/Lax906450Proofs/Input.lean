import Lax906450Proofs.Encoding
import Lax906450Proofs.Tabulation

namespace Lax906450Proofs.Input

open Lax906450.StrongNemhauserTrotter Lax109476.RationalEncoding
open WordTables WordExpressions ClosureLP Encoding Polynomial

def prepare := Tabulation.output lpTable.length (lpTable.entry .index)

theorem prepare_graph {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    prepare (encodeGraph G) = encodeProgram (program ℚ G) := by
  have h := instance_spec G
  apply List.ext_getElem
  · simpa [prepare, Tabulation.output] using (h 0).length
  · intro j hl hr
    simpa only [prepare, Tabulation.output, List.getElem_map, List.getElem_range, Term.eval]
      using (h j).entry .index hr

/-- The two dimension words are followed by one rational triple per entry
of the constraint matrix, right-hand side, and objective. -/
private theorem count_formula (xs : List ℕ) :
    let n := order.eval xs 0
    lpTable.length.eval xs 0 = 2 + 3 * (rows n * columns n + rows n + columns n) := by
  simp [lpTable, consCount, matrix, bounds, objectiveWords, vectorWords, natural, triple,
    append, blocks, single, rows, columns, vars]
  ring

theorem polynomial : Lax759944.RamPolytime.RamPolytime prepare := by
  let k : Polynomial ℕ := X + X + 1
  let m := k + X * X
  apply Tabulation.polytime _ _ (2 + 3 * (m * k + m + k))
  intro xs
  have hn : order.eval xs 0 ≤ Lax759944.BinaryWordEncoding.bitSize xs := by
    simp only [order, Term.eval_minimum, Term.eval]
    exact (min_le_right ..).trans (Tabulation.length_le_bits xs)
  rw [count_formula]
  simp only [m, k, rows, columns, eval_add, eval_mul, eval_ofNat, eval_one, eval_X]
  gcongr

end Lax906450Proofs.Input
