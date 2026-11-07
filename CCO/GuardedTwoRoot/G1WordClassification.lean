import CCO.GuardedTwoRoot.G1WordObstruction

/-! Literal source14 word classification in the actual infinite
block/bit/clone source. R-free positive words have EXACT singleton p/q
profile according to the parity of their q-letter count. Every word
containing r has r in its actual STRONG profile. Multiplication facts
come from actual old triangles and the already proved original SAP,
not from a supplied finite multiplication table. -/

namespace CCO.GuardedTwoRoot.G1
noncomputable section

local instance (i j : Unit) : DecidableEq (source.Atom i j) := by
  change DecidableEq Atom
  infer_instance
local instance (i j : Unit) : Fintype (source.Atom i j) := source.finiteAtom i j

private theorem p_triangle_forces {i j k : Unit} {a b : Atom}
    (h : source.Triangle (i := i) (j := j) (k := k) p a b) : a = b := by
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
    simp only [colour,ite_eq_right hxne,ite_eq_right hyne,hb,hd]
  exact Option.some.inj (hyz.symm.trans (he.symm.trans hxz))

private theorem qq_triangle_forces {i j k : Unit} {a : Atom}
    (h : source.Triangle (i := i) (j := j) (k := k) q q a) : a = p := by
  obtain ⟨x,y,z,hxy,hyz,hxz⟩ := h
  obtain ⟨hxyB,hxyBit⟩ := (colour_q x y).mp hxy
  obtain ⟨hyzB,hyzBit⟩ := (colour_q y z).mp hyz
  have hxne : x ≠ z := by
    intro he
    subst z
    simp [source,AtomicSource.atomRel,colour] at hxz
  have hBit : bit x = bit z := by
    cases hx : bit x <;> cases hy : bit y <;> cases hz : bit z <;> simp_all
  have hp : colour x z = some p :=
    (colour_p x z).mpr ⟨hxne,hxyB.trans hyzB,hBit⟩
  exact Option.some.inj (hxz.symm.trans hp)

private theorem singleton_product_of_forced_triangle {i j k : Unit}
    (a b c : Atom)
    (hForced : ∀ d, source.Triangle (i := i) (j := j) (k := k) a b d → d = c) :
    source.product ({a} : source.Menu i j) ({b} : source.Menu j k) = ({c} : Set Atom) := by
  have hNonempty : (source.product ({a} : source.Menu i j) ({b} : source.Menu j k)).Nonempty :=
    PositiveWord.profile_nonempty_of_SAP source homogeneous old_ageSAP (.cons (i := i) (j := j) (k := k) a (.single b))
  have hSubset : source.product ({a} : source.Menu i j) ({b} : source.Menu j k) ⊆ {c} := by
    rintro d ⟨a',ha,b',hb,h⟩
    have ha' : a' = a := ha
    have hb' : b' = b := hb
    subst a'
    subst b'
    exact hForced d h
  obtain ⟨d,hd⟩ := hNonempty
  have hdc : d = c := hSubset hd
  apply Set.Subset.antisymm hSubset
  rintro e he
  have hec : e = c := he
  exact hec.symm ▸ hdc ▸ hd

/-- Actual infinite clones and old SAP supply every singleton endpoint. -/
theorem p_product_singleton {i j k : Unit} (a : Atom) :
    source.product ({p} : source.Menu i j) ({a} : source.Menu j k) = ({a} : Set Atom) :=
  singleton_product_of_forced_triangle p a a (fun _ h => (p_triangle_forces h).symm)

theorem q_product_p {i j k : Unit} :
    source.product ({q} : source.Menu i j) ({p} : source.Menu j k) = ({q} : Set Atom) := by
  apply singleton_product_of_forced_triangle
  intro a h
  exact (p_triangle_forces (source.triangle_reverse h)).symm

theorem q_product_q {i j k : Unit} :
    source.product ({q} : source.Menu i j) ({q} : source.Menu j k) = ({p} : Set Atom) :=
  singleton_product_of_forced_triangle q q p (fun _ h => qq_triangle_forces h)

/-- The count refers to actual old q letters; r does not toggle it. -/
def qLetterCount (a : Atom) : ℕ := if a = q then 1 else 0

def qCount {i j : Unit} : PositiveWord source i j → ℕ
  | .single a => qLetterCount a
  | .cons a rest => qLetterCount a + qCount rest

def RFree {i j : Unit} : PositiveWord source i j → Prop
  | .single a => a ≠ r
  | .cons a rest => a ≠ r ∧ RFree rest

def ContainsR {i j : Unit} : PositiveWord source i j → Prop
  | .single a => a = r
  | .cons a rest => a = r ∨ ContainsR rest

/-- Source14 C44: exact singleton profile, not merely an upper bound
or failure of the two-element coarse menu. All positive lengths occur. -/
theorem rfree_profile_exact {i j : Unit} (word : PositiveWord source i j)
    (hFree : RFree word) :
    PositiveWord.profile source word = ({if qCount word % 2 = 0 then p else q} : Set Atom) := by
  induction word with
  | @single i j a =>
      cases i
      cases j
      change Atom at a
      fin_cases a
      · simp [PositiveWord.profile,qCount,qLetterCount,p,q]
        rfl
      · simp [PositiveWord.profile,qCount,qLetterCount,q]
        rfl
      · exact False.elim (hFree rfl)
  | @cons i j k a rest ih =>
      cases i
      cases j
      cases k
      obtain ⟨ha,hRest⟩ := hFree
      rw [PositiveWord.profile,ih hRest]
      change Atom at a
      fin_cases a
      · have hCount : qCount (.cons (i := ()) (j := ()) (k := ()) p rest) = qCount rest := by
          simp [qCount,qLetterCount,p,q]
        change (source.product ({p} : source.Menu () ())
          ({if qCount rest % 2 = 0 then p else q} : source.Menu () ()) : Set Atom) =
          ({if qCount (.cons (i := ()) (j := ()) (k := ()) p rest) % 2 = 0 then p else q} : Set Atom)
        rw [hCount]
        exact p_product_singleton (i := ()) (j := ()) (k := ()) _
      · have hCount : qCount (.cons (i := ()) (j := ()) (k := ()) q rest) = 1 + qCount rest := by
          simp [qCount,qLetterCount]
        change (source.product ({q} : source.Menu () ())
          ({if qCount rest % 2 = 0 then p else q} : source.Menu () ()) : Set Atom) =
          ({if qCount (.cons (i := ()) (j := ()) (k := ()) q rest) % 2 = 0 then p else q} : Set Atom)
        rw [hCount]
        have hMod : qCount rest % 2 < 2 := Nat.mod_lt _ (by decide)
        by_cases hEven : qCount rest % 2 = 0
        · have hNext : (1 + qCount rest) % 2 ≠ 0 := by omega
          rw [ite_eq_left hEven,ite_eq_right hNext]
          exact q_product_p (i := ()) (j := ()) (k := ())
        · have hNext : (1 + qCount rest) % 2 = 0 := by omega
          rw [ite_eq_right hEven,ite_eq_left hNext]
          exact q_product_q (i := ()) (j := ()) (k := ())
      · exact False.elim (ha rfl)

private theorem triangle_any_r_r_actual {i j k : Unit} (a : Atom) :
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

/-- Source14 C45: a word with an actual r letter always has an r
endpoint in its STRONG profile. The endpoints therefore leave J. -/
theorem r_mem_profile_of_containsR {i j : Unit} (word : PositiveWord source i j)
    (hR : ContainsR word) : r ∈ PositiveWord.profile source word := by
  induction word with
  | single a => exact hR.symm
  | cons a rest ih =>
      rcases hR with ha | hRest
      · subst a
        obtain ⟨b,hb⟩ := PositiveWord.profile_nonempty_of_SAP source homogeneous old_ageSAP rest
        exact ⟨r,rfl,b,hb,source.triangle_reverse (triangle_any_r_r_actual b)⟩
      · exact ⟨a,rfl,r,ih hRest,triangle_any_r_r_actual a⟩

end
end CCO.GuardedTwoRoot.G1
