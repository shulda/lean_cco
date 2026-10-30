import CCO.FullPhaseLift.Boundary.FreeUnion
import CCO.CloneSAP.FiniteUnion

/-! A concrete strong free amalgam of full ternary structures. This
establishes the amalgamation property of the K₄³-free hypergraph class
independently of the support-normal interface which the class refutes. -/

universe u
namespace CCO.FullPhaseLift.Boundary.FreeAmalgam
open CloneSAP.FiniteUnion
variable {A B C : Type u} (RA : TripleRelation A) (RB : TripleRelation B)
  (RC : TripleRelation C) (s : A ↪ B) (t : A ↪ C)

abbrev Vertex (_s : A ↪ B) (t : A ↪ C) := Union (A := B) t
abbrev leftMap (s : A ↪ B) (t : A ↪ C) : B ↪ Vertex s t := left t
noncomputable abbrev rightMap (s : A ↪ B) (t : A ↪ C) : C ↪ Vertex s t := right s t

noncomputable def relation : TripleRelation (Vertex s t) := fun x y z =>
  (∃ a b c, leftMap s t a = x ∧ leftMap s t b = y ∧ leftMap s t c = z ∧ RB a b c) ∨
  (∃ a b c, rightMap s t a = x ∧ rightMap s t b = y ∧ rightMap s t c = z ∧ RC a b c)

variable (hs : ∀ x y z, RB (s x) (s y) (s z) ↔ RA x y z)
variable (ht : ∀ x y z, RC (t x) (t y) (t z) ↔ RA x y z)

include hs ht in
theorem left_induced (x y z : B) :
    relation RB RC s t (leftMap s t x) (leftMap s t y) (leftMap s t z) ↔ RB x y z := by
  constructor
  · rintro (⟨a,b,c,ha,hb,hc,hR⟩ | ⟨a,b,c,ha,hb,hc,hR⟩)
    · have ha' := (leftMap s t).injective ha
      have hb' := (leftMap s t).injective hb
      have hc' := (leftMap s t).injective hc
      simpa only [ha',hb',hc'] using hR
    · obtain ⟨a₀,hsa,hta⟩ := intersection s t x a ha.symm
      obtain ⟨b₀,hsb,htb⟩ := intersection s t y b hb.symm
      obtain ⟨c₀,hsc,htc⟩ := intersection s t z c hc.symm
      have hA : RA a₀ b₀ c₀ := (ht _ _ _).mp (by simpa only [hta,htb,htc] using hR)
      simpa only [hsa,hsb,hsc] using (hs _ _ _).mpr hA
  · intro hR
    exact Or.inl ⟨x,y,z,rfl,rfl,rfl,hR⟩

include hs ht in
theorem right_induced (x y z : C) :
    relation RB RC s t (rightMap s t x) (rightMap s t y) (rightMap s t z) ↔ RC x y z := by
  constructor
  · rintro (⟨a,b,c,ha,hb,hc,hR⟩ | ⟨a,b,c,ha,hb,hc,hR⟩)
    · obtain ⟨a₀,hsa,hta⟩ := intersection s t a x ha
      obtain ⟨b₀,hsb,htb⟩ := intersection s t b y hb
      obtain ⟨c₀,hsc,htc⟩ := intersection s t c z hc
      have hA : RA a₀ b₀ c₀ := (hs _ _ _).mp (by simpa only [hsa,hsb,hsc] using hR)
      simpa only [hta,htb,htc] using (ht _ _ _).mpr hA
    · have ha' := (rightMap s t).injective ha
      have hb' := (rightMap s t).injective hb
      have hc' := (rightMap s t).injective hc
      simpa only [ha',hb',hc'] using hR
  · intro hR
    exact Or.inr ⟨x,y,z,rfl,rfl,rfl,hR⟩

theorem cover (x : Vertex s t) :
    (∃ a, leftMap s t a = x) ∨ (∃ b, rightMap s t b = x) := by
  rcases x with a | ⟨b,hb⟩
  · exact Or.inl ⟨a,rfl⟩
  · exact Or.inr ⟨b,right_off s t b hb⟩

include hs ht in
theorem k4Free (hB : K4Free RB) (hC : K4Free RC) :
    K4Free (relation RB RC s t) := by
  apply k4Free_of_two_factors (relation RB RC s t) RB RC
    (leftMap s t) (rightMap s t) hB hC
    (left_induced RA RB RC s t hs ht) (right_induced RA RB RC s t hs ht)
    (cover s t)
  intro x y z h
  rcases h with ⟨a,b,c,ha,hb,hc,_⟩ | ⟨a,b,c,ha,hb,hc,_⟩
  · exact Or.inl ⟨⟨a,ha⟩,⟨b,hb⟩,⟨c,hc⟩⟩
  · exact Or.inr ⟨⟨a,ha⟩,⟨b,hb⟩,⟨c,hc⟩⟩

def NoRepeats {V : Type u} (R : TripleRelation V) : Prop :=
  ∀ x y z, R x y z → x ≠ y ∧ x ≠ z ∧ y ≠ z

def Symmetric {V : Type u} (R : TripleRelation V) : Prop :=
  (∀ x y z, R x y z ↔ R y x z) ∧ (∀ x y z, R x y z ↔ R x z y)

theorem noRepeats (hB : NoRepeats RB) (hC : NoRepeats RC) :
    NoRepeats (relation RB RC s t) := by
  intro x y z h
  rcases h with ⟨a,b,c,ha,hb,hc,hR⟩ | ⟨a,b,c,ha,hb,hc,hR⟩
  · obtain ⟨hab,hac,hbc⟩ := hB a b c hR
    subst x; subst y; subst z
    exact ⟨fun h => hab ((leftMap s t).injective h),
      fun h => hac ((leftMap s t).injective h),fun h => hbc ((leftMap s t).injective h)⟩
  · obtain ⟨hab,hac,hbc⟩ := hC a b c hR
    subst x; subst y; subst z
    exact ⟨fun h => hab ((rightMap s t).injective h),
      fun h => hac ((rightMap s t).injective h),fun h => hbc ((rightMap s t).injective h)⟩

theorem symmetric (hB : Symmetric RB) (hC : Symmetric RC) :
    Symmetric (relation RB RC s t) := by
  constructor
  · intro x y z
    constructor
    · rintro (⟨a,b,c,ha,hb,hc,hR⟩ | ⟨a,b,c,ha,hb,hc,hR⟩)
      · exact Or.inl ⟨b,a,c,hb,ha,hc,(hB.1 _ _ _).mp hR⟩
      · exact Or.inr ⟨b,a,c,hb,ha,hc,(hC.1 _ _ _).mp hR⟩
    · rintro (⟨a,b,c,ha,hb,hc,hR⟩ | ⟨a,b,c,ha,hb,hc,hR⟩)
      · exact Or.inl ⟨b,a,c,hb,ha,hc,(hB.1 _ _ _).mp hR⟩
      · exact Or.inr ⟨b,a,c,hb,ha,hc,(hC.1 _ _ _).mp hR⟩
  · intro x y z
    constructor
    · rintro (⟨a,b,c,ha,hb,hc,hR⟩ | ⟨a,b,c,ha,hb,hc,hR⟩)
      · exact Or.inl ⟨a,c,b,ha,hc,hb,(hB.2 _ _ _).mp hR⟩
      · exact Or.inr ⟨a,c,b,ha,hc,hb,(hC.2 _ _ _).mp hR⟩
    · rintro (⟨a,b,c,ha,hb,hc,hR⟩ | ⟨a,b,c,ha,hb,hc,hR⟩)
      · exact Or.inl ⟨a,c,b,ha,hc,hb,(hB.2 _ _ _).mp hR⟩
      · exact Or.inr ⟨a,c,b,ha,hc,hb,(hC.2 _ _ _).mp hR⟩

/-- The SAME maps commute on the base and identify no extra vertices. -/
theorem commute (a : A) : leftMap s t (s a) = rightMap s t (t a) :=
  CloneSAP.FiniteUnion.commute s t a

theorem strong_intersection (b : B) (c : C)
    (h : leftMap s t b = rightMap s t c) : ∃ a, s a = b ∧ t a = c :=
  intersection s t b c h

end CCO.FullPhaseLift.Boundary.FreeAmalgam
