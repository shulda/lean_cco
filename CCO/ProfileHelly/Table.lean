import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Set.Lattice.Bounded
import Mathlib.Tactic.Ext

/-! Standalone finite typed diversity tables. Triangles are INPUT data, not
realized triangles of an assumed homogeneous source. Logical equality is
never one of the atomic names. -/
universe u v
namespace CCO.ProfileHelly

structure Table (ι : Type u) where
  Atom : ι → ι → Type v
  finiteSort : Fintype ι
  finiteAtom : ∀ i j, Fintype (Atom i j)
  nonemptyAtom : ∀ i j, Nonempty (Atom i j)
  conv : ∀ {i j}, Atom i j → Atom j i
  conv_invol : ∀ {i j} (a : Atom i j), conv (conv a) = a
  symmetricLoop : ∀ {i} (a : Atom i i), conv a = a
  triangle : ∀ {i j k}, Atom i j → Atom j k → Atom i k → Prop
  peirce_left : ∀ {i j k} (a : Atom i j) (b : Atom j k) (c : Atom i k),
    triangle a b c ↔ triangle c (conv b) a
  peirce_right : ∀ {i j k} (a : Atom i j) (b : Atom j k) (c : Atom i k),
    triangle a b c ↔ triangle (conv a) c b
  reverse : ∀ {i j k} (a : Atom i j) (b : Atom j k) (c : Atom i k),
    triangle a b c ↔ triangle (conv b) (conv a) (conv c)

namespace Table
variable {ι : Type u} (T : Table.{u,v} ι)
abbrev Menu (i j : ι) := Set (T.Atom i j)

def product {i j k : ι} (A : T.Menu i j) (B : T.Menu j k) : T.Menu i k :=
  {c | ∃ a ∈ A, ∃ b ∈ B, T.triangle a b c}

def opposite {i j : ι} (A : T.Menu i j) : T.Menu j i := {a | T.conv a ∈ A}

theorem opposite_opposite {i j} (A : T.Menu i j) : T.opposite (T.opposite A) = A := by
  ext a
  simp only [opposite,Set.mem_ofPred_eq,T.conv_invol]

theorem opposite_singleton {i j} (a : T.Atom i j) :
    T.opposite {a} = {T.conv a} := by
  ext b
  constructor
  · intro h
    exact (T.conv_invol b).symm.trans (congrArg T.conv h)
  · rintro rfl
    exact T.conv_invol a

theorem product_mono {i j k} {A A' : T.Menu i j} {B B' : T.Menu j k}
    (hA : A ⊆ A') (hB : B ⊆ B') : T.product A B ⊆ T.product A' B' := by
  rintro c ⟨a,ha,b,hb,htri⟩
  exact ⟨a,hA ha,b,hB hb,htri⟩

theorem product_singleton {i j k} (a : T.Atom i j) (b : T.Atom j k) (c : T.Atom i k) :
    c ∈ T.product {a} {b} ↔ T.triangle a b c := by
  simp only [product,Set.mem_ofPred_eq,Set.mem_singleton_iff,exists_eq_left]

theorem opposite_product {i j k} (A : T.Menu i j) (B : T.Menu j k) :
    T.opposite (T.product A B) = T.product (T.opposite B) (T.opposite A) := by
  ext c
  constructor
  · rintro ⟨a,ha,b,hb,htri⟩
    refine ⟨T.conv b,?_,T.conv a,?_,?_⟩
    · simpa only [opposite,Set.mem_ofPred_eq,T.conv_invol] using hb
    · simpa only [opposite,Set.mem_ofPred_eq,T.conv_invol] using ha
    · simpa only [T.conv_invol] using (T.reverse a b (T.conv c)).mp htri
  · rintro ⟨b,hb,a,ha,htri⟩
    exact ⟨T.conv a,ha,T.conv b,hb,(T.reverse b a c).mp htri⟩

theorem set_peirce_left {i j k} (A : T.Menu i j) (B : T.Menu j k) (C : T.Menu i k) :
    (T.product A B ∩ C).Nonempty ↔ (A ∩ T.product C (T.opposite B)).Nonempty := by
  constructor
  · rintro ⟨c,⟨a,ha,b,hb,htri⟩,hc⟩
    refine ⟨a,ha,c,hc,T.conv b,?_,(T.peirce_left a b c).mp htri⟩
    simpa only [opposite,Set.mem_ofPred_eq,T.conv_invol] using hb
  · rintro ⟨a,ha,c,hc,b,hb,htri⟩
    exact ⟨c,⟨a,ha,T.conv b,hb,by
      simpa only [T.conv_invol] using (T.peirce_left c b a).mp htri⟩,hc⟩

theorem set_peirce_right {i j k} (A : T.Menu i j) (B : T.Menu j k) (C : T.Menu i k) :
    (T.product A B ∩ C).Nonempty ↔ (B ∩ T.product (T.opposite A) C).Nonempty := by
  constructor
  · rintro ⟨c,⟨a,ha,b,hb,htri⟩,hc⟩
    refine ⟨b,hb,T.conv a,?_,c,hc,(T.peirce_right a b c).mp htri⟩
    simpa only [opposite,Set.mem_ofPred_eq,T.conv_invol] using ha
  · rintro ⟨b,hb,a,ha,c,hc,htri⟩
    exact ⟨c,⟨T.conv a,ha,b,hb,by
      simpa only [T.conv_invol] using (T.peirce_right a c b).mp htri⟩,hc⟩
end Table

structure TableLaws {ι : Type u} (T : Table.{u,v} ι) : Prop where
  total : ∀ {i j k} (a : T.Atom i j) (b : T.Atom j k), (T.product {a} {b}).Nonempty
  associative : ∀ {i j k l} (A : T.Menu i j) (B : T.Menu j k) (C : T.Menu k l),
    T.product (T.product A B) C = T.product A (T.product B C)

namespace TableLaws
variable {ι : Type u} {T : Table.{u,v} ι} (h : TableLaws T)
include h

theorem product_nonempty {i j k} {A : T.Menu i j} {B : T.Menu j k}
    (ha : A.Nonempty) (hb : B.Nonempty) : (T.product A B).Nonempty := by
  obtain ⟨a,ha⟩ := ha
  obtain ⟨b,hb⟩ := hb
  obtain ⟨c,hc⟩ := h.total a b
  exact ⟨c,T.product_mono (Set.singleton_subset_iff.mpr ha) (Set.singleton_subset_iff.mpr hb) hc⟩

/-- C03: every output atom survives an actual return-square prefix,
without an identity atom or a zero-length STRONG profile. -/
theorem return_square {i j k} (a : T.Atom i j) (c : T.Atom i k) :
    c ∈ T.product (T.product {a} {T.conv a}) {c} := by
  obtain ⟨b,hb⟩ := h.total (T.conv a) c
  have hc : T.triangle a b c := by
    have hh := (T.product_singleton _ _ _).mp hb
    simpa only [T.conv_invol] using (T.peirce_right (T.conv a) c b).mp hh
  rw [h.associative]
  exact ⟨a,rfl,b,hb,hc⟩

theorem return_square_right {i j k} (a : T.Atom i j) (b : T.Atom j k) :
    a ∈ T.product {a} (T.product {b} {T.conv b}) := by
  obtain ⟨c,hc⟩ := h.total a b
  rw [← h.associative]
  exact ⟨c,hc,T.conv b,rfl,(T.peirce_left a b c).mp ((T.product_singleton _ _ _).mp hc)⟩
end TableLaws
end CCO.ProfileHelly
