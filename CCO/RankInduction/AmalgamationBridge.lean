import CCO.RankInduction.Basis

/-! The global predicate quantifies over arbitrary closed base maps.
Its literal-inclusion specialization supplies exactly the closed-span
interface of the normalized relative MI constructor. -/

universe v w t
namespace CCO.RankInduction
open RawExact Owners.Product Owners.Provider
open ParityHasse.Original RealHull.Geometry RealClosure.Bounds AclOwners

variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)

noncomputable def embeddingOnFinset (L : Finset M) (W : Set M)
    (f : FiniteLift.OrbitalEmbedding G (↑L : Set M) W) : RealInducedEmbedding S L := by
  classical
  exact {
  map x := if h : x ∈ L then (f.toEmbedding ⟨x,h⟩).val else x
  injective := by
    intro x hx y hy he
    change (if h : x ∈ L then (f.toEmbedding ⟨x,h⟩).val else x) = (if h : y ∈ L then (f.toEmbedding ⟨y,h⟩).val else y) at he
    rw [dite_eq_left (show x ∈ L from hx),dite_eq_left (show y ∈ L from hy)] at he
    exact congrArg Subtype.val (f.toEmbedding.injective (Subtype.ext he))
  colours := by
    intro x hx y hy
    simp only [dite_eq_left hx,dite_eq_left hy]
    obtain ⟨g,hgx,hgy⟩ := f.pair ⟨x,hx⟩ ⟨y,hy⟩
    exact (congrArg₂ (col S) hgx.symm hgy.symm).trans (col_invariant S H g x y) }

include H

theorem finset_strong_closed (safe : Set (S.Atom () ()))
    (hs : FiniteLift.StrongClosedAmalgamation G (FiniteLift.aclSet G) (S.menuRel safe)) :
    AclOwners.StrongClosedAmalgamation S G safe := by
  classical
  intro A L R hA hL hR hAL hAR
  let f : FiniteLift.OrbitalEmbedding G (↑A : Set M) (↑L : Set M) := {
    toEmbedding := { toFun a := ⟨a.val,hAL a.property⟩
                     inj' := by intro a b hab; exact Subtype.ext (congrArg (fun z : (↑L : Set M) => z.val) hab) }
    pair := by
      intro a b
      refine ⟨1,?_,?_⟩
      · change (1 : G) • a.val = a.val
        exact one_smul G a.val
      · change (1 : G) • b.val = b.val
        exact one_smul G b.val }
  let g : FiniteLift.OrbitalEmbedding G (↑A : Set M) (↑R : Set M) := {
    toEmbedding := { toFun a := ⟨a.val,hAR a.property⟩
                     inj' := by intro a b hab; exact Subtype.ext (congrArg (fun z : (↑R : Set M) => z.val) hab) }
    pair := by
      intro a b
      refine ⟨1,?_,?_⟩
      · change (1 : G) • a.val = a.val
        exact one_smul G a.val
      · change (1 : G) • b.val = b.val
        exact one_smul G b.val }
  obtain ⟨W,-,l,r,commute,strong,cross⟩ := hs (↑A) (↑L) (↑R)
    A.finite_toSet L.finite_toSet R.finite_toSet hA hL hR f g
  refine ⟨embeddingOnFinset S H L W l,embeddingOnFinset S H R W r,?_,?_,?_⟩
  · intro a ha
    have hp := congrArg Subtype.val (commute ⟨a,ha⟩)
    change (l.toEmbedding ⟨a,hAL ha⟩).val = (r.toEmbedding ⟨a,hAR ha⟩).val at hp
    simpa only [embeddingOnFinset,dite_eq_left (hAL ha),dite_eq_left (hAR ha)] using hp
  · intro x hx y hy
    simp only [embeddingOnFinset,dite_eq_left hx,dite_eq_left hy]
    rw [← Subtype.ext_iff]
    constructor
    · intro he
      obtain ⟨a,hax,hay⟩ := (strong ⟨x,hx⟩ ⟨y,hy⟩).mp he
      exact ⟨(congrArg Subtype.val hax).symm.trans (congrArg Subtype.val hay),
        (show a.val = x from congrArg Subtype.val hax) ▸ a.property⟩
    · rintro ⟨hxy,ha⟩
      apply (strong ⟨x,hx⟩ ⟨y,hy⟩).mpr
      exact ⟨⟨x,ha⟩,rfl,Subtype.ext hxy⟩
  · intro x hx hxA y hy hyA
    have hx' : (⟨x,hx⟩ : (↑L : Set M)) ∉ Set.range f.toEmbedding := by
      rintro ⟨a,ha⟩
      exact hxA ((show a.val = x from congrArg Subtype.val ha) ▸ a.property)
    have hy' : (⟨y,hy⟩ : (↑R : Set M)) ∉ Set.range g.toEmbedding := by
      rintro ⟨a,ha⟩
      exact hyA ((show a.val = y from congrArg Subtype.val ha) ▸ a.property)
    obtain ⟨c,hc,hcol⟩ := cross ⟨x,hx⟩ ⟨y,hy⟩ hx' hy'
    exact ⟨c,hc,by simpa only [embeddingOnFinset,dite_eq_left hx,dite_eq_left hy, col] using hcol⟩

end CCO.RankInduction
