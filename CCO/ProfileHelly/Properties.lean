import CCO.ProfileHelly.Completion
import CCO.ProfileHelly.Forks

/-! Exact semantic conclusions for the FULL class of finite allowed table
networks. Induced factor embeddings and their exact intersection are explicit. -/
universe u v z
namespace CCO.ProfileHelly
variable {ι : Type u}

def StrongAmalgamation (T : Table.{u,v} ι) : Prop :=
  ∀ (A L R : Type z) [Finite A] [Finite L] [Finite R]
    (sortA : A → ι) (sortL : L → ι) (sortR : R → ι)
    (B : CompleteNetwork T sortA) (C : CompleteNetwork T sortL) (D : CompleteNetwork T sortR)
    (f : Network.Embedding B.toNetwork C.toNetwork)
    (g : Network.Embedding B.toNetwork D.toNetwork),
    ∃ (W : Type z) (_ : Finite W) (sortW : W → ι) (N : CompleteNetwork T sortW)
      (l : Network.Embedding C.toNetwork N.toNetwork)
      (r : Network.Embedding D.toNetwork N.toNetwork),
      (∀ a, l.point (f.point a) = r.point (g.point a)) ∧
      ∀ x y, l.point x = r.point y ↔ ∃ a, f.point a = x ∧ g.point a = y

def DistinctForks (T : Table.{u,v} ι) : Prop :=
  ∀ (i j k : ι) (a : T.Atom i j) (b : T.Atom i k),
    ∃ N : CompleteNetwork T (forkSort i j k), N.edge 0 1 = some a ∧ N.edge 0 2 = some b

theorem distinct_forks {T : Table.{u,v} ι} (laws : TableLaws T) : DistinctForks T :=
  fun _ _ _ a b => distinct_fork laws a b

/-- The source optional fork premise belongs only to the SAP clause. -/
def ProfileHellyConverse (T : Table.{u,v} ι) : Prop :=
  SemanticHomCCO.{u,v,z} T ∧ (DistinctForks T → StrongAmalgamation.{u,v,z} T)

end CCO.ProfileHelly
