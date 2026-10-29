import CCO.AclOwners.AclCore
import CCO.AclOwners.FineSpokes
import CCO.AclOwners.Rook

/-! Strong amalgamation is required only for absolutely real-acl-closed
finite induced spans. Both complete spoke tables, literal intersections
and every distinct off-base cross edge are part of the interface. -/
universe v w t
namespace CCO.AclOwners
open ParityHasse.Original RealHull.Geometry RealClosure.Bounds
open FinitePackets.Geometry FinitePackets.Normalization
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable (G : Type t) [Group G] [MulAction G M]

structure RealInducedEmbedding (A : Finset M) where
  map : M → M
  injective : Set.InjOn map (A : Set M)
  colours : ∀ x ∈ A, ∀ y ∈ A, col S (map x) (map y) = col S x y

/-- The palette applies to the NEW off-base edges of a strong amalgam;
it is not ordinary SAP over arbitrary finite nonclosed sets. -/
def StrongClosedAmalgamation (safe : Set (Atom S)) : Prop :=
  ∀ (A L R : Finset M), Closed G A → Closed G L → Closed G R → A ⊆ L → A ⊆ R →
    ∃ (f : RealInducedEmbedding S L) (g : RealInducedEmbedding S R),
      (∀ a ∈ A, f.map a = g.map a) ∧
      (∀ x ∈ L, ∀ y ∈ R, f.map x = g.map y ↔ x = y ∧ x ∈ A) ∧
      (∀ x ∈ L, x ∉ A → ∀ y ∈ R, y ∉ A →
        ∃ c ∈ safe, col S (f.map x) (g.map y) = some c)

variable {G} (H : HomogeneousSource S G)

theorem closureFinset_mono [DecidableEq M] {A B : Finset M} (h : A ⊆ B) :
    closureFinset S H A ⊆ closureFinset S H B := by
  intro x hx
  exact (mem_closureFinset S H B x).mpr
    (acl_mono h ((mem_closureFinset S H A x).mp hx))

theorem direction_point_outside_packet (D : Direction S) (x : M) :
    ∃ u : M, D.val x u ∧ ¬ finitePacket S H x u := by
  classical
  by_contra hn
  push_neg at hn
  apply D.property.1
  apply (finiteClasses_iff_at S H D.val x).mpr
  letI := finitePacket_finite S H x
  exact Finite.of_injective
    (fun y : ClassPoint S () D.val x =>
      (⟨y.val,hn y.val y.property⟩ : ClassPoint S () (finitePacket S H) x))
    (fun _ _ h => Subtype.ext (congrArg
      (fun z : ClassPoint S () (finitePacket S H) x => z.val) h))

end CCO.AclOwners
