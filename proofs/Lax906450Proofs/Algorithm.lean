import Lax906450Proofs.Input
import Lax906450Proofs.Output
import Lax218471.Combinators
import Lax759944.TuringRamPolytimeEquivalence

namespace Lax906450Proofs.Algorithm

open Lax906450 Lax906450.StrongNemhauserTrotter
open Lax109476.LinearProgram Lax109476.RationalCertificates Lax109476.RationalEncoding
open Lax759944.RamPolytime Lax759944.BinaryWordEncoding
open ClosureLP OptimalSupport

private theorem compose {f g : List ℕ → List ℕ} (hf : RamPolytime f) (hg : RamPolytime g) :
    RamPolytime (g ∘ f) := by
  let eqv := Lax759944.TuringRamPolytimeEquivalence.ramPolytime_iff_turingPolytime
  exact (eqv _).2 (Lax218471.Combinators.comp (ea := encode) (eb := encode) (ec := encode)
    ((eqv _).1 hf) ((eqv _).1 hg))

/--
---
conclusion: Lax906450.StrongNemhauserTrotter.polynomial_partition
---
The RAM builds the order constraints $0\le x_i,y_j\le1$ and $x_i\le y_j$ for
each edge $ij$. It calls the exact polynomial-time LP solver and reads the
positive coordinates of the two copies. Their supports maximize
$n|A|-(n+1)|B|$. Indeed, subtracting a common sufficiently small amount
from all positive coordinates leaves room to add that amount on any
admissible pair. An improvement of the support would improve the LP.
The integer objective maximizes deficiency and breaks ties by minimizing
the left part. The maximum-deficiency lemma gives all three conclusions.
-/
theorem polynomial_partition :
    ∃ solve : List ℕ → List ℕ, RamPolytime solve ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
        ∃ Z O : Finset (Fin n), solve (encodeGraph G) = labels Z O ∧ Partition.IsPartition G Z O := by
  obtain ⟨lp, hlp, hcert⟩ := Lax109476.CertifiedOptimization.exists_certified_polynomial_time_solver
  refine ⟨Output.decode ∘ lp ∘ Input.prepare, compose (compose Input.polynomial hlp) Output.polynomial, ?_⟩
  intro n G inst
  obtain ⟨cert, hrun, hvalid, outcome⟩ := hcert _ _ (program ℚ G)
  have hfb := feasible_bounded G
  cases cert with
  | infeasible y =>
    exact False.elim (outcome (cast_program G ▸ hfb.1))
  | unbounded x d =>
    exact False.elim (outcome.2 (cast_program G ▸ hfb.2))
  | optimal x y =>
    change IsPrimalOptimal (toReal _) (realVector x) at outcome
    rw [cast_program] at outcome
    obtain ⟨ht, hAB, hscore⟩ := optimal_support G _ outcome
    let A := support (realVector x ∘ left)
    let B := support (realVector x ∘ right)
    refine ⟨A, B, ?_, Lax906450.Deficiency.partition_of_maximum G A B hAB
      (fun X Y h => (lexicographic (hscore X Y h)).1)
      (fun X Y h => (lexicographic (hscore X Y h)).2)⟩
    simp only [Function.comp_apply, Input.prepare_graph, hrun]
    apply Output.decode_optimal _ _ _ hvalid.1.1
    change (x 0 : ℝ) = n at ht
    exact_mod_cast ht

end Lax906450Proofs.Algorithm
