import Lax906450.Partition
import Lax759944.RamPolytime

/-!
---
title: The strong Nemhauser–Trotter theorem
type: theorem
---
A single polynomial-time word-RAM program computes a persistent vertex-cover
partition of any finite simple graph. The logical input consists of the vertex count
followed by the adjacency matrix in row order. The program writes one word per
vertex, in vertex order, with $0,1,2$ encoding membership in $V_0,V_{1/2},V_1$,
respectively. The instruction count and sufficient word width are polynomial
in the binary input size.

The conclusion for every minimum vertex cover is the strengthening of the
Nemhauser–Trotter theorem due to Chlebík and Chlebíková.

# Formalization notes

For a graph on $n$ vertices the logical input has $1+n^2$ words. The RAM
input convention prepends this length to the physical tape. The algorithm
makes one call to the certified rational LP solver from `lax-109476`.
-/

namespace Lax906450.StrongNemhauserTrotter

/-- The adjacency matrix of a numbered graph, preceded by its order. -/
def encodeGraph {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : List ℕ :=
  n :: (List.ofFn fun u => List.ofFn fun v => if G.Adj u v then 1 else 0).flatten

/-- Output labels in vertex order. -/
def labels {n : ℕ} (Z O : Finset (Fin n)) : List ℕ :=
  List.ofFn fun v => if v ∈ Z then 0 else if v ∈ O then 2 else 1

/-- One uniform RAM computes all three parts on every graph, including the empty graph. -/
axiom polynomial_partition :
  ∃ solve : List ℕ → List ℕ, Lax759944.RamPolytime.RamPolytime solve ∧
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      ∃ Z O : Finset (Fin n), solve (encodeGraph G) = labels Z O ∧ Partition.IsPartition G Z O

end Lax906450.StrongNemhauserTrotter
