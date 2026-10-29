import CCO.ProfileHelly.Fill

/-! The finite completion measure counts UNORDERED distinct pairs.
A fill deletes exactly its one pair, retaining every other missing pair. -/
universe u v z
namespace CCO.ProfileHelly.Network
variable {ι : Type u} {T : Table.{u,v} ι} {V : Type z} {sort : V → ι}
variable (D : Network T sort)

def Missing : Sym2 V → Prop := Sym2.lift ⟨fun x y => x ≠ y ∧ D.edge x y = none,by
  intro x y
  apply propext
  constructor <;> rintro ⟨hne,hm⟩
  · exact ⟨hne.symm,D.reverse_missing x y hm⟩
  · exact ⟨hne.symm,D.reverse_missing y x hm⟩⟩

@[simp] theorem missing_mk (x y : V) : D.Missing s(x,y) ↔ x ≠ y ∧ D.edge x y = none := Iff.rfl

noncomputable def missingPairs [Finite V] : Finset (Sym2 V) := by
  classical
  let : Fintype V := Fintype.ofFinite V
  exact Finset.univ.filter D.Missing

@[simp] theorem mem_missingPairs [Finite V] (p : Sym2 V) : p ∈ D.missingPairs ↔ D.Missing p := by
  classical
  simp [missingPairs]

theorem missing_fill (x y : V) (hne : x ≠ y) (a : T.Atom (sort x) (sort y))
    (p : Sym2 V) : (D.fill x y hne a).Missing p ↔ D.Missing p ∧ p ≠ s(x,y) := by
  classical
  induction p using Sym2.inductionOn with
  | hf p q =>
    by_cases h : p = x ∧ q = y
    · rcases h with ⟨hp,hq⟩
      subst p
      subst q
      simp [missing_mk]
    · by_cases h' : p = y ∧ q = x
      · rcases h' with ⟨hp,hq⟩
        subst p
        subst q
        simp [missing_mk,Sym2.eq_swap]
      · have hs : s(p,q) ≠ s(x,y) := by
          intro he
          exact (Sym2.eq_iff.mp he).elim h h'
        simp only [missing_mk,D.fill_other x y hne a p q h h',hs,ne_eq,not_false_eq_true,and_true]

theorem missingPairs_fill [Finite V] [DecidableEq V] (x y : V) (hne : x ≠ y) (a : T.Atom (sort x) (sort y)) :
    (D.fill x y hne a).missingPairs = D.missingPairs.erase s(x,y) := by
  classical
  ext p
  simp only [mem_missingPairs,missing_fill,Finset.mem_erase]
  exact and_comm

theorem missingPairs_fill_card [Finite V] (x y : V) (hne : x ≠ y)
    (a : T.Atom (sort x) (sort y)) (hm : D.edge x y = none) :
    (D.fill x y hne a).missingPairs.card + 1 = D.missingPairs.card := by
  classical
  rw [D.missingPairs_fill]
  exact Finset.card_erase_add_one ((D.mem_missingPairs s(x,y)).mpr ((D.missing_mk x y).mpr ⟨hne,hm⟩))

theorem missingPairs_fill_lt [Finite V] (x y : V) (hne : x ≠ y)
    (a : T.Atom (sort x) (sort y)) (hm : D.edge x y = none) :
    (D.fill x y hne a).missingPairs.card < D.missingPairs.card := by
  have h := D.missingPairs_fill_card x y hne a hm
  omega

theorem missingPairs_empty_iff [Finite V] : D.missingPairs = ∅ ↔
    ∀ x y, x ≠ y → ∃ a, D.edge x y = some a := by
  constructor
  · intro hempty x y hxy
    cases he : D.edge x y with
    | none =>
      have hh := (D.mem_missingPairs s(x,y)).mpr ⟨hxy,he⟩
      rw [hempty] at hh
      exact False.elim (Finset.notMem_empty _ hh)
    | some a => exact ⟨a,rfl⟩
  · intro hc
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro p hp
    have hm := (D.mem_missingPairs p).mp hp
    induction p using Sym2.inductionOn with
    | hf x y =>
      obtain ⟨hne,he⟩ := hm
      obtain ⟨a,ha⟩ := hc x y hne
      rw [he] at ha
      cases ha

end CCO.ProfileHelly.Network
