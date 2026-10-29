import CCO.ProfileHelly.Network
import CCO.ProfileHelly.CyclicAlgebra

/-! Actual finite allowed networks and guarded colliding word walks.
No SAP, profile Helly or completion theorem enters this semantic branch. -/
universe u v z
namespace CCO.ProfileHelly
variable {ι : Type u} {T : Table.{u,v} ι} {V : Type z} {sort : V → ι}

namespace Network
variable (D : Network T sort)
abbrev Point (_D : Network T sort) (i : ι) := {x : V // sort x = i}

def colour {i j : ι} (x : D.Point i) (y : D.Point j) : Option (T.Atom i j) := by
  rcases x with ⟨x,rfl⟩
  rcases y with ⟨y,rfl⟩
  exact D.edge x y

@[simp] theorem colour_mk (x y : V) :
    D.colour ⟨x,rfl⟩ ⟨y,rfl⟩ = D.edge x y := rfl

theorem colour_ne {i j} {x : D.Point i} {y : D.Point j} {a : T.Atom i j}
    (h : D.colour x y = some a) : x.val ≠ y.val := by
  rcases x with ⟨x,rfl⟩
  rcases y with ⟨y,rfl⟩
  intro he
  change x = y at he
  subst y
  change D.edge x x = some a at h
  rw [D.diagonal] at h
  cases h

theorem colour_swap {i j} {x : D.Point i} {y : D.Point j} {a : T.Atom i j}
    (h : D.colour x y = some a) : D.colour y x = some (T.conv a) := by
  rcases x with ⟨x,rfl⟩
  rcases y with ⟨y,rfl⟩
  change D.edge x y = some a at h
  change D.edge y x = some (T.conv a)
  rw [← D.edge_reverse y x,h]
  rfl
end Network

namespace CompleteNetwork
variable (D : CompleteNetwork T sort)

theorem colour_exists {i j} (x : D.toNetwork.Point i) (y : D.toNetwork.Point j)
    (hne : x.val ≠ y.val) : ∃ a, D.toNetwork.colour x y = some a := by
  rcases x with ⟨x,rfl⟩
  rcases y with ⟨y,rfl⟩
  exact D.complete x y hne

theorem colour_triangle {i j k} (x : D.toNetwork.Point i)
    (y : D.toNetwork.Point j) (z : D.toNetwork.Point k)
    (a : T.Atom i j) (b : T.Atom j k) (c : T.Atom i k)
    (ha : D.toNetwork.colour x y = some a) (hb : D.toNetwork.colour y z = some b)
    (hc : D.toNetwork.colour x z = some c) : T.triangle a b c := by
  rcases x with ⟨x,rfl⟩
  rcases y with ⟨y,rfl⟩
  rcases z with ⟨z,rfl⟩
  exact D.legal x y z (D.toNetwork.colour_ne ha) (D.toNetwork.colour_ne hb)
    (D.toNetwork.colour_ne hc) a b c ha hb hc
end CompleteNetwork

namespace Word
variable (D : Network T sort)

/-- Positive walks may collide at nonadjacent occurrences. -/
def Realizes : {i j : ι} → Word T i j → D.Point i → D.Point j → Prop
  | _,_,single a,x,y => D.colour x y = some a
  | _,_,cons a w,x,y => ∃ q : D.Point _, D.colour x q = some a ∧ Realizes w q y

/-- C04/C05: only the ACTUAL distinct endpoint guard is needed.
The closed-tail case is repaired by return-square absorption. -/
theorem guarded_readout (laws : TableLaws T) (N : CompleteNetwork T sort)
    {i j} (w : Word T i j) (x : N.toNetwork.Point i) (y : N.toNetwork.Point j)
    (hw : Realizes N.toNetwork w x y) (hne : x.val ≠ y.val)
    (c : T.Atom i j) (hc : N.toNetwork.colour x y = some c) : c ∈ w.profile := by
  have main : ∀ n, ∀ {i j} (w : Word T i j), w.length = n →
      ∀ (x : N.toNetwork.Point i) (y : N.toNetwork.Point j),
      Realizes N.toNetwork w x y → x.val ≠ y.val →
      ∀ c, N.toNetwork.colour x y = some c → c ∈ w.profile := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro i j w hn x y hw hne c hc
      cases w with
      | single a => exact Option.some.inj (hc.symm.trans hw)
      | @cons i k j a tail =>
        obtain ⟨q,hxq,hqy⟩ := hw
        by_cases hqy_ne : q.val ≠ y.val
        · obtain ⟨b,hb⟩ := N.colour_exists q y hqy_ne
          have hlen : tail.length < n := by simp only [length] at hn; omega
          have hbp := ih tail.length hlen tail rfl q y hqy hqy_ne b hb
          exact ⟨a,rfl,b,hbp,N.colour_triangle x q y a b c hxq hb hc⟩
        · have he : q.val = y.val := not_not.mp hqy_ne
          have hs : k = j := q.property.symm.trans ((congrArg sort he).trans y.property)
          subst j
          have hq : q = y := Subtype.ext he
          subst q
          have hac : a = c := Option.some.inj (hxq.symm.trans hc)
          subst c
          cases tail with
          | single b => exact False.elim (N.toNetwork.colour_ne hqy rfl)
          | @cons k l k b rest =>
            obtain ⟨z,hyz,hzy⟩ := hqy
            have hlen : rest.length < n := by simp only [length] at hn; omega
            have hb := ih rest.length hlen rest rfl z y hzy
              (Ne.symm (N.toNetwork.colour_ne hyz)) (T.conv b) (N.toNetwork.colour_swap hyz)
            exact T.product_mono (Set.Subset.refl _) (T.product_mono (Set.Subset.refl _)
              (Set.singleton_subset_iff.mpr hb)) (laws.return_square_right a b)
  exact main w.length w rfl x y hw hne c hc

theorem realizes_append {i j k} (p : Word T i j) (q : Word T j k)
    (x : D.Point i) (y : D.Point k) :
    Realizes D (p.append q) x y ↔
      ∃ z : D.Point j, Realizes D p x z ∧ Realizes D q z y := by
  induction p with
  | single a => rfl
  | cons a p ih =>
    constructor
    · rintro ⟨z,hxz,hzy⟩
      obtain ⟨r,hzr,hry⟩ := (ih q z).mp hzy
      exact ⟨r,⟨z,hxz,hzr⟩,hry⟩
    · rintro ⟨r,⟨z,hxz,hzr⟩,hry⟩
      exact ⟨z,hxz,(ih q z).mpr ⟨r,hzr,hry⟩⟩

/-- C04: a positive closed hom-walk contains a genuine return square.
The open tail readout uses the already proved strong length induction. -/
theorem closed_return_square (laws : TableLaws T) (N : CompleteNetwork T sort)
    {i} (w : Word T i i) (x : N.toNetwork.Point i)
    (hw : Realizes N.toNetwork w x x) :
    ∃ j, ∃ a : T.Atom i j, T.product {a} {T.conv a} ⊆ w.profile := by
  cases w with
  | single a => exact False.elim (N.toNetwork.colour_ne hw rfl)
  | cons a tail =>
    obtain ⟨y,hxy,hyx⟩ := hw
    have ha := guarded_readout laws N tail y x hyx
      (Ne.symm (N.toNetwork.colour_ne hxy)) (T.conv a) (N.toNetwork.colour_swap hxy)
    exact ⟨_,a,T.product_mono (Set.Subset.refl _) (Set.singleton_subset_iff.mpr ha)⟩

/-- A semantic cycle may collapse the two chosen arc terminals. The first
EDGE still has distinct images; guarded readout there plus pure Peirce
recovers the algebraic arc intersection without any injectivization. -/
theorem two_arc_readout (laws : TableLaws T) (N : CompleteNetwork T sort)
    {i j} (p q : Word T i j) (x : N.toNetwork.Point i)
    (hw : Realizes N.toNetwork (p.append q.reverse) x x) :
    (p.profile ∩ q.profile).Nonempty := by
  cases p with
  | single a =>
    obtain ⟨y,hxy,hyx⟩ := hw
    have ha := guarded_readout laws N q.reverse y x hyx
      (Ne.symm (N.toNetwork.colour_ne hxy)) (T.conv a) (N.toNetwork.colour_swap hxy)
    rw [profile_reverse laws] at ha
    change T.conv (T.conv a) ∈ q.profile at ha
    rw [T.conv_invol] at ha
    exact ⟨a,rfl,ha⟩
  | cons a tail =>
    obtain ⟨y,hxy,hyx⟩ := hw
    have ha := guarded_readout laws N (tail.append q.reverse) y x hyx
      (Ne.symm (N.toNetwork.colour_ne hxy)) (T.conv a) (N.toNetwork.colour_swap hxy)
    rw [profile_append laws,profile_reverse laws] at ha
    exact (arc_cut a tail q).mpr ha

end Word
end CCO.ProfileHelly
