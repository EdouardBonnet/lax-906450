import Lax906450.Partition

/-!
---
title: Maximum deficiency and persistency
type: lemma
---
Consider pairs $(A,B)$ for which every neighbor of a vertex in $A$ belongs
to $B$. Maximize the deficiency $|A|-|B|$ and, among all maximizers, minimize
$|A|$. Any pair selected by these two rules gives the zero and one parts of a
persistent vertex-cover partition.
-/

namespace Lax906450.Deficiency

variable {V : Type*} [Fintype V] [DecidableEq V]

def Admissible (G : SimpleGraph V) (A B : Finset V) : Prop :=
  ∀ u ∈ A, ∀ v, G.Adj u v → v ∈ B

def deficiency (A B : Finset V) : ℤ := (A.card : ℤ) - B.card

axiom partition_of_maximum (G : SimpleGraph V) (A B : Finset V)
    (h : Admissible G A B)
    (hmax : ∀ X Y, Admissible G X Y → deficiency X Y ≤ deficiency A B)
    (hmin : ∀ X Y, Admissible G X Y → deficiency X Y = deficiency A B → A.card ≤ X.card) :
    Partition.IsPartition G A B

end Lax906450.Deficiency
