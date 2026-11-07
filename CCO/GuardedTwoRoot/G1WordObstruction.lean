import CCO.GuardedTwoRoot.G1OldSAP
import CCO.PositiveWords
import CCO.RawExact.Convolution

/-! Source14 FG1: the ACTUAL p/q/r source has no positive word with
endpoint menu {p,q}. More strongly, every equality-inclusive RAW exact
presentation containing both p and q also contains r. True equality
letters and diagonal outputs are retained throughout. -/

namespace CCO.GuardedTwoRoot.G1
noncomputable section

/-- Closure property distinguishing the coarse block diagonal from
every actual positive or RAW-exact word menu. -/
def PQClosed (A : Set Atom) : Prop := p ∈ A → q ∈ A → r ∈ A

/-- FG1 itself: equality of the actual coarse block coordinates has
exact old DISTINCT-real-pair diversity slice {p,q}. Equality of the
old real points remains a separate logical diagonal. -/
theorem coarse_diagonal_diversity_guard :
    source.diversityGuard (i := ()) (j := ())
      (fun x y : Real => block x = block y) = ({p,q} : Set Atom) := by
  change ({a : Atom | ∃ x y : Real, block x = block y ∧ colour x y = some a}) =
    ({p,q} : Set Atom)
  ext a
  constructor
  · rintro ⟨x,y,hblock,hcolour⟩
    fin_cases a
    · simp
    · simp
    · exact False.elim (((colour_r x y).mp hcolour) hblock)
  · intro ha
    rcases Set.mem_insert_iff.mp ha with ha | ha
    · subst a
      exact ⟨((0,false),0),((0,false),1),rfl,by decide⟩
    · have haq : a = q := Set.mem_singleton_iff.mp ha
      subst a
      exact ⟨((0,false),0),((0,true),0),rfl,by decide⟩

private theorem triangle_p_left {i j k : Unit} {b c : Atom}
    (h : source.Triangle (i := i) (j := j) (k := k) p b c) : b = c := by
  obtain ⟨x,y,z,hxy,hyz,hxz⟩ := h
  obtain ⟨_,hb,hd⟩ := (colour_p x y).mp hxy
  have hxne : x ≠ z := by
    intro he
    subst z
    simp [source,AtomicSource.atomRel,colour] at hxz
  have hyne : y ≠ z := by
    intro he
    subst z
    simp [source,AtomicSource.atomRel,colour] at hyz
  have he : colour x z = colour y z := by
    simp only [colour,if_neg hxne,if_neg hyne,hb,hd]
  exact Option.some.inj (hyz.symm.trans (he.symm.trans hxz))

private theorem triangle_q_q {i j k : Unit} {b : Atom}
    (h : source.Triangle (i := i) (j := j) (k := k) q b q) : b = p := by
  obtain ⟨x,y,z,hxy,hyz,hxz⟩ := h
  obtain ⟨hby,hdy⟩ := (colour_q x y).mp hxy
  obtain ⟨hbz,hdz⟩ := (colour_q x z).mp hxz
  have hyne : y ≠ z := by
    intro he
    subst z
    simp [source,AtomicSource.atomRel,colour] at hyz
  have hd : bit y = bit z := by
    cases hx : bit x <;> cases hy : bit y <;> cases hz : bit z <;>
      simp_all
  have hp : colour y z = some p :=
    (colour_p y z).mpr ⟨hyne,hby.symm.trans hbz,hd⟩
  exact Option.some.inj (hyz.symm.trans hp)

private theorem triangle_any_r_r {i j k : Unit} (a : Atom) :
    source.Triangle (i := i) (j := j) (k := k) a r r := by
  cases i
  cases j
  cases k
  fin_cases a
  · exact ⟨((0,false),0),((0,false),1),((1,false),0),
      by dsimp only [AtomicSource.atomRel,source]; decide,
      by dsimp only [AtomicSource.atomRel,source]; decide,
      by dsimp only [AtomicSource.atomRel,source]; decide⟩
  · exact ⟨((0,false),0),((0,true),0),((1,false),0),
      by dsimp only [AtomicSource.atomRel,source]; decide,
      by dsimp only [AtomicSource.atomRel,source]; decide,
      by dsimp only [AtomicSource.atomRel,source]; decide⟩
  · exact ⟨((0,false),0),((1,false),0),((2,false),0),
      by dsimp only [AtomicSource.atomRel,source]; decide,
      by dsimp only [AtomicSource.atomRel,source]; decide,
      by dsimp only [AtomicSource.atomRel,source]; decide⟩

/-- The closure property is preserved by the literal STRONG triangle
product. Its witnesses are old real triples, not an abstract table. -/
theorem pqClosed_atomic_product {i j k : Unit} (a : Atom)
    (A : source.Menu j k) (hA : PQClosed A) :
    PQClosed (source.product ({a} : source.Menu i j) A) := by
  rintro ⟨a',ha',b,hb,htriP⟩ ⟨a'',ha'',c,hc,htriQ⟩
  have ha'Eq : a' = a := Set.mem_singleton_iff.mp ha'
  have ha''Eq : a'' = a := Set.mem_singleton_iff.mp ha''
  subst a'
  subst a''
  have hrA : r ∈ A := by
    fin_cases a
    · have hbp : b = p := triangle_p_left htriP
      have hcq : c = q := triangle_p_left htriQ
      exact hA (hbp ▸ hb) (hcq ▸ hc)
    · have hbq : b = q := triangle_p_left (source.triangle_rotate htriP)
      have hcp : c = p := triangle_q_q htriQ
      exact hA (hcp ▸ hc) (hbq ▸ hb)
    · have hbr : b = r := triangle_p_left (source.triangle_rotate htriP)
      exact hbr ▸ hb
  exact ⟨a,rfl,r,hrA,triangle_any_r_r a⟩

/-- Every genuine positive word obeys the p/q⇒r obstruction. -/
theorem positive_profile_pqClosed {i j : Unit} (word : PositiveWord source i j) :
    PQClosed (PositiveWord.profile source word) := by
  induction word with
  | single a =>
      intro hp hq
      have hpa : p = a := Set.mem_singleton_iff.mp hp
      have hqa : q = a := Set.mem_singleton_iff.mp hq
      exact False.elim (by have := hpa.trans hqa.symm; exact (by decide : p ≠ q) this)
  | cons a rest ih => exact pqClosed_atomic_product a _ ih

/-- FG1 positive obstruction, with all old word lengths quantified. -/
theorem no_positive_coarse_diagonal {i j : Unit} (word : PositiveWord source i j) :
    PositiveWord.profile source word ≠ ({p,q} : Set Atom) := by
  intro he
  have h := positive_profile_pqClosed word
  rw [he] at h
  have hr := h (by simp) (by simp)
  simpa [p,q,r] using hr

/-- Identity-inclusive normalization does not bypass the obstruction:
an all-equality RAW word has empty diversity guard. -/
theorem raw_word_guard_pqClosed {i j : Unit} (word : RawWord source i j) :
    PQClosed (source.diversityGuard (RawWord.relation source word)) := by
  rcases PositiveWord.raw_guard_empty_or_positive_profile_of_SAP
    source homogeneous old_ageSAP word with h | ⟨positive,h⟩
  · rw [h]
    intro hp
    exact False.elim hp
  · rw [h]
    exact positive_profile_pqClosed positive

/-- The same fine atom at ANY actual pair satisfies the same RAW word;
this is the original group's actual pair homogeneity. -/
private theorem raw_word_of_guard {i j : Unit} (word : RawWord source i j)
    {a : Atom} (ha : a ∈ source.diversityGuard (RawWord.relation source word))
    {x y : Real} (hxy : colour x y = some a) : RawWord.relation source word x y := by
  obtain ⟨x',y',hword,hcolour⟩ := ha
  obtain ⟨g,hgx,hgy⟩ := source.pair_homogeneous_of_homogeneous homogeneous
    x' x y' y (hcolour.trans hxy.symm)
  have h := RawExact.word_invariant_of_homogeneous source homogeneous word g x' y' hword
  rwa [hgx,hgy] at h

/-- All words of ONE exact presentation are read on the SAME actual
r-pair. This also covers the empty presentation (the universal relation). -/
theorem raw_exact_guard_pqClosed (P : RawExact.Presentation source () ()) :
    PQClosed (source.diversityGuard (RawExact.evaluate source P)) := by
  rintro ⟨xp,yp,hp,hcp⟩ ⟨xq,yq,hq,hcq⟩
  let xr : Real := ((0,false),0)
  let yr : Real := ((1,false),0)
  refine ⟨xr,yr,?_,by dsimp only [AtomicSource.atomRel,source]; decide⟩
  intro word hw
  have hpw : p ∈ source.diversityGuard (RawWord.relation source word) :=
    ⟨xp,yp,hp word hw,hcp⟩
  have hqw : q ∈ source.diversityGuard (RawWord.relation source word) :=
    ⟨xq,yq,hq word hw,hcq⟩
  exact raw_word_of_guard word ((raw_word_guard_pqClosed word) hpw hqw) (by decide)

/-- The actual coarse equivalence J (including logical equality) is
not FULL RAW exact: no finite word-intersection presents same-block. -/
theorem coarse_block_not_raw_exact (P : RawExact.Presentation source () ()) :
    RawExact.evaluate source P ≠ (fun x y : Real => block x = block y) := by
  intro he
  have hp : p ∈ source.diversityGuard (RawExact.evaluate source P) := by
    refine ⟨((0,false),0),((0,false),1),?_,by dsimp only [AtomicSource.atomRel,source]; decide⟩
    rw [he]
    rfl
  have hq : q ∈ source.diversityGuard (RawExact.evaluate source P) := by
    refine ⟨((0,false),0),((0,true),0),?_,by dsimp only [AtomicSource.atomRel,source]; decide⟩
    rw [he]
    rfl
  obtain ⟨x,y,hrel,hcol⟩ := raw_exact_guard_pqClosed P hp hq
  rw [he] at hrel
  exact ((colour_r x y).mp hcol) hrel

end
end CCO.GuardedTwoRoot.G1
