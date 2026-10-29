import CCO.OwnerTransversal.ClosedAvoidance

/-! One-point repair fixes displayed neighbours only. Protected formal
values are retained by updating just one off-anchor coordinate. -/
universe v w t z
namespace CCO.OwnerTransversal
noncomputable section
open ParityHasse.Original RealHull.Geometry RealClosure.Bounds AclOwners
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)
variable [Countable M] [DecidableEq M] (R : ResidualData S H)
variable (B : Finset (Owner S H R))

structure OriginPattern (V : Type z) where
  owner : V → Owner S H R
  edge : V → V → Option (Atom S)
  symmetric : ∀ x y, edge x y = edge y x
  diagonal : ∀ x, edge x x = none
  nonthin : ∀ x y a, edge x y = some a →
    ∀ u v : M, col S u v = some a → ¬ finitePacket S H u v

structure OriginMap {V : Type z} (P : OriginPattern S H R V) where
  point : V → NamedCarrier S H R B
  owner : ∀ x, CCO.OwnerTransversal.owner S H R (point x).val = P.owner x
  edge : ∀ x y a, P.edge x y = some a → col S (point x).val (point y).val = some a

namespace OriginMap
variable {S H R B} {V : Type z} [Fintype V] [DecidableEq V]
variable {P : OriginPattern S H R V} (f : OriginMap S H R B P)

def neighbours (x : V) : Finset (NamedCarrier S H R B) :=
  (Finset.univ.filter (fun y => P.edge x y ≠ none)).image f.point

omit [DecidableEq V] in
theorem outside_neighbour_closure (x : V) :
    f.point x ∉ namedPacketClosure S H R B (f.neighbours x) := by
  rintro ⟨a,ha,hax⟩
  obtain ⟨u,hu,hea⟩ := Finset.mem_image.mp ha
  obtain ⟨y,hy,hyu⟩ := Finset.mem_image.mp hu
  have hey : P.edge x y ≠ none := (Finset.mem_filter.mp hy).2
  cases he : P.edge x y with
  | none => exact hey he
  | some c =>
      apply P.nonthin x y c he (f.point x).val (f.point y).val (f.edge x y c he)
      have hay : (f.point y).val = a := (congrArg Subtype.val hyu).trans hea
      exact (finitePacket S H).val.symm (hay.symm ▸ hax)

variable [Infinite M]

/-- C32: new x has a fresh packet, and every other formal value is kept. -/
theorem repair (x : V) :
    ∃ f' : OriginMap S H R B P,
      (∀ y, y ≠ x → f'.point y = f.point y) ∧
      ∀ y, ¬ finitePacket S H (f'.point x).val (f.point y).val := by
  classical
  let C := f.neighbours x
  let Z := namedPacketFinset S H R B (Finset.univ.image f.point)
  let K := baseFixers S H R B C
  have horbit : (MulAction.orbit K (f.point x)).Infinite := by
    rw [fixed_orbit_eq S H R B]
    exact named_orbit_infinite S H R B C (f.point x) (f.outside_neighbour_closure x)
  obtain ⟨g,hg⟩ := finite_action_avoidance (G := K) {f.point x} Z (by
    intro y hy
    simpa only [Finset.mem_singleton.mp hy] using horbit)
  let p : V → NamedCarrier S H R B := Function.update f.point x (g.val.val (f.point x))
  have hpx : p x = g.val.val (f.point x) := Function.update_self _ _ _
  have hpy (y : V) (hy : y ≠ x) : p y = f.point y := Function.update_of_ne hy _ _
  have hfix (y : V) (hy : P.edge x y ≠ none) : g.val.val (f.point y) = f.point y :=
    g.property (f.point y) (Finset.mem_image.mpr ⟨y,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hy⟩,rfl⟩)
  have hEdge : ∀ u v a, P.edge u v = some a → col S (p u).val (p v).val = some a := by
    intro u v a huv
    have hne : u ≠ v := by
      intro he; subst v
      rw [P.diagonal] at huv
      cases huv
    by_cases hux : u = x
    · subst u
      rw [hpx,hpy v (Ne.symm hne)]
      rw [← hfix v (by rw [huv]; exact Option.some_ne_none _)]
      exact (NamedAut.colour_fixed g.val (f.point x) (f.point v)).trans (f.edge x v a huv)
    · by_cases hvx : v = x
      · subst v
        rw [hpy u hux,hpx]
        have hxu : P.edge x u = some a := (P.symmetric x u).trans huv
        rw [← hfix u (by rw [hxu]; exact Option.some_ne_none _)]
        exact (NamedAut.colour_fixed g.val (f.point u) (f.point x)).trans (f.edge u x a huv)
      · rw [hpy u hux,hpy v hvx]
        exact f.edge u v a huv
  let f' : OriginMap S H R B P := {
    point := p
    owner := by
      intro y
      by_cases hy : y = x
      · subst y
        rw [hpx,NamedAut.owner_fixed]
        exact f.owner x
      · rw [hpy y hy]
        exact f.owner y
    edge := hEdge }
  refine ⟨f',hpy,?_⟩
  intro y hxy
  have hmem : g.val.val (f.point x) ∈ Z := by
    apply (mem_namedPacketFinset S H R B _ _).mpr
    refine ⟨(f.point y).val,?_,?_⟩
    · exact Finset.mem_image.mpr ⟨f.point y,
        Finset.mem_image.mpr ⟨y,Finset.mem_univ _,rfl⟩,rfl⟩
    · exact (finitePacket S H).val.symm (by simpa only [f',hpx] using hxy)
  exact hg (f.point x) (Finset.mem_singleton_self _) _ hmem rfl

def collisionPairs : Finset (V × V) := by
  classical
  exact Finset.univ.filter (fun p => p.1 ≠ p.2 ∧
    finitePacket S H (f.point p.1).val (f.point p.2).val)

def PacketSeparated : Prop :=
  ∀ x y, x ≠ y → ¬ finitePacket S H (f.point x).val (f.point y).val

omit [Infinite M] in
/-- Ordered colliding formal packet pairs strictly decrease after one
off-anchor repair.  Recorded absence imposes no extra condition. -/
theorem repair_decreases (x z : V) (hxz : x ≠ z)
    (hcol : finitePacket S H (f.point x).val (f.point z).val)
    (f' : OriginMap S H R B P)
    (hkeep : ∀ y, y ≠ x → f'.point y = f.point y)
    (hfresh : ∀ y, ¬ finitePacket S H (f'.point x).val (f.point y).val) :
    f'.collisionPairs.card < f.collisionPairs.card := by
  classical
  have hsub : f'.collisionPairs ⊆ f.collisionPairs := by
    intro p hp
    obtain ⟨hne,hpF⟩ := (Finset.mem_filter.mp hp).2
    have hp₁ : p.1 ≠ x := by
      intro he
      rw [he,hkeep p.2 (by simpa only [he] using Ne.symm hne)] at hpF
      exact hfresh p.2 hpF
    have hp₂ : p.2 ≠ x := by
      intro he
      rw [he,hkeep p.1 hp₁] at hpF
      exact hfresh p.1 ((finitePacket S H).val.symm hpF)
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _,hne,by simpa only [hkeep _ hp₁,hkeep _ hp₂] using hpF⟩
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨hsub,?_⟩
  intro he
  have hm : (x,z) ∈ f'.collisionPairs := he ▸
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hxz,hcol⟩)
  have hF := (Finset.mem_filter.mp hm).2.2
  rw [hkeep z (Ne.symm hxz)] at hF
  exact hfresh z hF

/-- C33: finite collision descent produces a globally packet-separated
completion and retains every protected formal value. -/
theorem separate (f : OriginMap S H R B P) (A : Finset V)
    (hA : ∀ x ∈ A, ∀ y ∈ A, x ≠ y →
      ¬ finitePacket S H (f.point x).val (f.point y).val) :
    ∃ g : OriginMap S H R B P,
      (∀ a ∈ A, g.point a = f.point a) ∧ g.PacketSeparated := by
  classical
  by_cases hgood : f.PacketSeparated
  · exact ⟨f,fun _ _ => rfl,hgood⟩
  · have hbad : ∃ x y, x ≠ y ∧ finitePacket S H (f.point x).val (f.point y).val := by
      simp only [PacketSeparated,not_forall,not_not] at hgood
      obtain ⟨x,y,hne,hF⟩ := hgood
      exact ⟨x,y,hne,hF⟩
    obtain ⟨x,z,hxA,hxz,hF⟩ : ∃ x z, x ∉ A ∧ x ≠ z ∧
        finitePacket S H (f.point x).val (f.point z).val := by
      obtain ⟨x,z,hxz,hF⟩ := hbad
      by_cases hxA : x ∈ A
      · have hzA : z ∉ A := fun hz => hA x hxA z hz hxz hF
        exact ⟨z,x,hzA,Ne.symm hxz,(finitePacket S H).val.symm hF⟩
      · exact ⟨x,z,hxA,hxz,hF⟩
    obtain ⟨f',hkeep,hfresh⟩ := f.repair x
    have hA' : ∀ u ∈ A, ∀ v ∈ A, u ≠ v →
        ¬ finitePacket S H (f'.point u).val (f'.point v).val := by
      intro u hu v hv hne
      rw [hkeep u (by intro he; exact hxA (he ▸ hu)),
        hkeep v (by intro he; exact hxA (he ▸ hv))]
      exact hA u hu v hv hne
    have hlt := f.repair_decreases x z hxz hF f' hkeep hfresh
    obtain ⟨g,hg,hsep⟩ := separate f' A hA'
    refine ⟨g,?_,hsep⟩
    intro a ha
    exact (hg a ha).trans (hkeep a (by intro he; exact hxA (he ▸ ha)))
termination_by f.collisionPairs.card
decreasing_by exact hlt

end OriginMap
end
end CCO.OwnerTransversal
