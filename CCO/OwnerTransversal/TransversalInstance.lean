import CCO.OwnerTransversal.TransversalAge
import CCO.OwnerTransversal.TransversalModel

/-! The actual provider consumed by the global primitivity argument.
Its realization, embedding and homogeneity fields are discharged by the
internally constructed actual finite transversal age. -/

open scoped FirstOrder
open FirstOrder FirstOrder.Language

universe v w t
namespace CCO.OwnerTransversal.TransversalAge
noncomputable section
open ParityHasse.Original RealHull.Geometry RealClosure.Bounds CountableColour

variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)
variable [Countable M] [DecidableEq M] [Infinite M] (R : ResidualData S H)
variable (B : Finset (Owner S H R))

theorem colour_diag (x : U S H R B) : (limitTable S H R B).colour x x = none := by
  obtain ⟨f,_,hc,_⟩ := realize_tuple S H R B (fun _ : Fin 1 => x)
  exact (hc 0 0).symm.trans ((col_none S _ _).mpr rfl)

theorem colour_symm (x y : U S H R B) :
    (limitTable S H R B).colour x y = (limitTable S H R B).colour y x := by
  obtain ⟨f,_,hc,_⟩ := realize_tuple S H R B (![x,y])
  exact (hc 0 1).symm.trans ((col_symm S _ _).trans (hc 1 0))

theorem colour_none (x y : U S H R B) :
    (limitTable S H R B).colour x y = none ↔ x = y := by
  constructor
  · intro hc
    by_contra hne
    obtain ⟨f,_,hf,hs⟩ := realize_tuple S H R B (![x,y])
    have he : (f 0).val = (f 1).val := (col_none S _ _).mp ((hf 0 1).trans hc)
    exact hs 0 1 hne (he ▸ (finitePacket S H).val.refl (f 0).val)
  · rintro rfl
    exact colour_diag S H R B x

/-- Genuine finite-tuple homogeneity, including repeated values. -/
theorem tuple_homogeneous {I : Type*} [Finite I] (source target : I → U S H R B)
    (ho : ∀ i, (limitTable S H R B).owner (source i) = (limitTable S H R B).owner (target i))
    (hc : ∀ i j, (limitTable S H R B).colour (source i) (source j) =
      (limitTable S H R B).colour (target i) (target j)) :
    ∃ g : U S H R B ≃[Signature S H R B] U S H R B,
      ∀ i, g (source i) = target i := by
  apply (limitCoding S H R B).tuple_homogeneous (data S H R B).homogeneous source target ?_ ho hc
  intro i j
  rw [← colour_none S H R B (source i) (source j),hc i j,colour_none S H R B]

/-- The actual model interface has no unproved age or homogeneity field. -/
def model : TransversalModel S H R B (U S H R B) where
  table := limitTable S H R B
  realize_pair x y hxy := by
    obtain ⟨f,ho,hc,hs⟩ := realize_tuple S H R B (![x,y])
    exact ⟨f 0,f 1,congrArg Subtype.val (ho 0),congrArg Subtype.val (ho 1),hc 0 1,hs 0 1 hxy⟩
  embed {n} a hs := by
    let T : Table ↥B (FullColour S) (Fin n) :=
      ⟨fun i => ownerLabel S H R B (a i),fun i j => col S (a i).val (a j).val⟩
    let Q : Chart S H R B := ⟨n,T,⟨⟨a,fun _ => rfl,fun _ _ => rfl,hs⟩⟩⟩
    obtain ⟨f,ho,hc⟩ := embed_chart S H R B Q
    exact ⟨f,fun i => congrArg Subtype.val (ho i),hc⟩
  pair_homogeneous x y x' y' hx hy hc := by
    let source : Fin 2 → U S H R B := ![x,y]
    let target : Fin 2 → U S H R B := ![x',y']
    have ho : ∀ i, (limitTable S H R B).owner (source i) =
        (limitTable S H R B).owner (target i) := by
      intro i
      refine Fin.cases hx (fun j => ?_) i
      have hj : j = 0 := Subsingleton.elim _ _
      cases hj
      exact hy
    have hh : ∀ i j, (limitTable S H R B).colour (source i) (source j) =
        (limitTable S H R B).colour (target i) (target j) := by
      intro i j
      refine Fin.cases ?_ (fun k => ?_) i
      · refine Fin.cases ?_ (fun k => ?_) j
        · exact (colour_diag S H R B x).trans (colour_diag S H R B x').symm
        · have hk : k = 0 := Subsingleton.elim _ _
          cases hk
          exact hc
      · have hk : k = 0 := Subsingleton.elim _ _
        cases hk
        refine Fin.cases ?_ (fun k => ?_) j
        · exact (colour_symm S H R B y x).trans (hc.trans (colour_symm S H R B x' y'))
        · have hk : k = 0 := Subsingleton.elim _ _
          cases hk
          exact (colour_diag S H R B y).trans (colour_diag S H R B y').symm
    obtain ⟨g,hg⟩ := tuple_homogeneous S H R B source target ho hh
    have hp := (limitCoding S H R B).embedding_preserves (limitCoding S H R B) g.toEmbedding
    let a : TableAut S H R B (limitTable S H R B) := ⟨g.toEquiv,
      (fun b x => (congrArg (· = b) (hp.1 x)).to_iff),
      (fun c x y => (congrArg (· = c) (hp.2 x y)).to_iff)⟩
    exact ⟨a,hg 0,hg 1⟩

end
end CCO.OwnerTransversal.TransversalAge
