import Mathlib.Combinatorics.SimpleGraph.VertexCover
import Mathlib.Data.Finset.BooleanAlgebra

/-!
---
title: A persistent vertex-cover partition
type: definition
---
Write $Z=V_0$, $O=V_1$, and $H=V_{1/2}=V(G)\setminus(Z\cup O)$.
All neighbors of $Z$ belong to $O$. Every cover of $G[H]$ has size at least
$|H|/2$. Every minimum vertex cover of $G$ contains $O$ and avoids $Z$.
-/

namespace Lax906450.Partition

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The vertices left in the induced subproblem. -/
def middle (Z O : Finset V) : Finset V := (Z ∪ O)ᶜ

/-- The edges with both endpoints in the specified set are covered by C. -/
def CoversOn (G : SimpleGraph V) (H C : Finset V) : Prop :=
  ∀ u ∈ H, ∀ v ∈ H, G.Adj u v → u ∈ C ∨ v ∈ C

/-- The three conclusions of the strong Nemhauser–Trotter theorem. -/
structure IsPartition (G : SimpleGraph V) (Z O : Finset V) : Prop where
  disjoint : Disjoint Z O
  neighbors : ∀ u ∈ Z, ∀ v, G.Adj u v → v ∈ O
  half_bound : ∀ C ⊆ middle Z O, CoversOn G (middle Z O) C →
    (middle Z O).card ≤ 2 * C.card
  persistent : ∀ S : Finset V, G.IsVertexCover (S : Set V) →
    (∀ T : Finset V, G.IsVertexCover (T : Set V) → S.card ≤ T.card) →
    O ⊆ S ∧ Disjoint Z S

end Lax906450.Partition
