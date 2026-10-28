import CCO.RealClosure.Bounds.TerminalParity
import CCO.RawExact.Presentations

/-! B011 C27: ONE equality-inclusive original RAW word for every FULL
original invariant equivalence. The proof is before and independent of
CCO/exact-ball Helly and full-lattice distributivity. -/
universe u v w t
namespace CCO.RealClosure.Bounds
open CCO.ParityHasse.Original
variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X) {i : ι}
variable {G : Type t} [Group G] [∀ j, MulAction G (X j)]
variable (H : HomogeneousSource S G)

/-- Finite join in the FULL lattice, with actual equality as empty join. -/
def terminalListJoin : List (ColourEq S i) → ColourEq S i
  | [] => ⊥
  | E :: L => ColourEq.join S H E (terminalListJoin L)

theorem terminalListJoin_le (L : List (ColourEq S i)) (E : ColourEq S i)
    (h : ∀ F ∈ L, F ≤ E) : terminalListJoin S H L ≤ E := by
  induction L with
  | nil => exact bot_le
  | cons F L ih =>
    change F.val ⊔ (terminalListJoin S H L).val ≤ E.val
    exact sup_le (h F (List.mem_cons_self)) (ih (fun Q hQ => h Q (List.mem_cons_of_mem F hQ)))

theorem le_terminalListJoin {L : List (ColourEq S i)} {E : ColourEq S i}
    (h : E ∈ L) : E ≤ terminalListJoin S H L := by
  induction L with
  | nil => cases h
  | cons F L ih =>
    rcases List.mem_cons.mp h with he | he
    · subst E
      change F.val ≤ F.val ⊔ (terminalListJoin S H L).val
      exact le_sup_left
    · change E.val ≤ F.val ⊔ (terminalListJoin S H L).val
      exact le_trans (ih he) (show (terminalListJoin S H L).val ≤
        F.val ⊔ (terminalListJoin S H L).val from le_sup_right)

/-- Concatenate actual words, using represented composition=join of the
commuting original equivalences; no general union-of-exacts claim is made. -/
theorem terminalListJoin_one_word (L : List (ColourEq S i))
    (hw : ∀ E ∈ L, ∃ word : RawWord S i i, RawWord.relation S word = E.val.r) :
    ∃ word : RawWord S i i, RawWord.relation S word = (terminalListJoin S H L).val.r := by
  induction L with
  | nil => exact ⟨.nil i,rfl⟩
  | cons E L ih =>
    obtain ⟨e,he⟩ := hw E (List.mem_cons_self)
    obtain ⟨tail,ht⟩ := ih (fun F hF => hw F (List.mem_cons_of_mem E hF))
    refine ⟨RawWord.append S e tail,?_⟩
    rw [RawWord.relation_append S,he,ht]
    funext x y
    exact propext (sup_relation_iff S H E (terminalListJoin S H L) x y).symm

/-- Whether a literal old diversity atom belongs to an original E. -/
def TerminalAtomBelow (E : ColourEq S i) (c : S.Atom i i) : Prop :=
  ∀ x y, S.atomRel c x y → E x y

noncomputable def terminalAtoms (E : ColourEq S i) : List (S.Atom i i) := by
  classical
  letI := S.finiteAtom i i
  exact (Finset.univ.filter (TerminalAtomBelow S E)).toList

@[simp] theorem mem_terminalAtoms (E : ColourEq S i) (c : S.Atom i i) :
    c ∈ terminalAtoms S E ↔ TerminalAtomBelow S E c := by
  classical
  simp [terminalAtoms]

/-- The list contains every genuine old E-atom, and its generated components
join to E, including the true diagonal and the empty diversity palette. -/
theorem terminal_components_join (E : ColourEq S i) :
    terminalListJoin S H ((terminalAtoms S E).map (connectivityColourEq S H)) = E := by
  apply le_antisymm
  · apply terminalListJoin_le
    intro F hF
    obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hF
    exact connectivity_le_of_atom_le S H c E ((mem_terminalAtoms S E c).mp hc)
  · intro x y hxy
    cases hc : S.colour x y with
    | none =>
      have he : x = y := by
        have htag := (S.colour_none_iff x y).mp hc
        simpa only [Sigma.mk.injEq,heq_eq_eq,true_and] using htag
      subst y
      exact (terminalListJoin S H _).val.refl x
    | some c =>
      have hbelow : TerminalAtomBelow S E c := by
        intro a b hab
        exact (E.property x y a b (hc.trans hab.symm)).mp hxy
      have hmem : connectivityColourEq S H c ∈
          (terminalAtoms S E).map (connectivityColourEq S H) :=
        List.mem_map.mpr ⟨c,(mem_terminalAtoms S E c).mpr hbelow,rfl⟩
      apply le_terminalListJoin S H hmem
      exact ⟨1,(relPow_one _ x y).mpr hc⟩

include H

/-- Headline CCO-free result under FULL ORIGINAL sortwise NR2.
The one word is on the actual original sort, using ambient G pair orbitals. -/
theorem terminal_one_raw_word (nr2 : SortNR2 S i) (E : ColourEq S i) :
    ∃ word : RawWord S i i, RawWord.relation S word = E.val.r := by
  obtain ⟨word,hw⟩ := terminalListJoin_one_word S H
    ((terminalAtoms S E).map (connectivityColourEq S H)) (by
      intro F hF
      obtain ⟨c,_,rfl⟩ := List.mem_map.mp hF
      exact terminal_connectivity_one_word S H nr2 c)
  exact ⟨word,(terminal_components_join S H E) ▸ hw⟩

omit H in
/-- Identity uses the genuine zero-letter RAW word, not a diversity atom. -/
theorem terminal_identity_empty_word :
    RawWord.relation S (.nil i) = (⊥ : Setoid (X i)).r := rfl

omit H in
/-- On a singleton original sort every equivalence is represented by the
actual empty word, without NR2, SAP or CCO. -/
theorem terminal_singleton_empty_word [Subsingleton (X i)] (E : ColourEq S i) :
    RawWord.relation S (.nil i) = E.val.r := by
  funext x y
  apply propext
  constructor
  · intro h
    subst y
    exact E.val.refl x
  · intro _
    exact Subsingleton.elim x y

/-- A ONE-word presentation, including an original real witness pair. -/
theorem terminal_single_word_exact (nr2 : SortNR2 S i) (E : ColourEq S i) :
    ∃ D : RawExact.NonemptyExact S i i,
      D.words.length = 1 ∧ RawExact.evaluate S D.words = E.val.r := by
  obtain ⟨word,hw⟩ := terminal_one_raw_word S H nr2 E
  have hev : RawExact.evaluate S [word] = E.val.r := by
    funext x y
    simpa only [RawExact.evaluate,List.mem_singleton,forall_eq] using congrFun (congrFun hw x) y
  obtain ⟨x⟩ := S.nonemptySort i
  exact ⟨⟨[word],x,x,by simpa only [hev] using E.val.refl x⟩,rfl,hev⟩

end CCO.RealClosure.Bounds
