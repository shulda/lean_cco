import CCO.UnaryTermsReturn.CommonBlockEmbeddingBlocks
import CCO.UnaryTermsReturn.CommonBlockFreshness
import Lean.Elab.Tactic.Omega

/-!
# B052 C16: compatible block labels for an ORIGINAL strong age amalgam

The two-original-sort common-block source has genuine full atomic
binary colours recording equality of block labels and *separate*
literal equality of real points. A pair of finite induced
embeddings C→A and C→B therefore determines a partial
bijection of the blocks meeting the common base.

We construct the block assignment for the B-side inside the
actual old source: every B block meeting the common base is
sent to the corresponding A base block, while all other B
blocks are shifted beyond the maximum block of the finite A
side. This is an ACTUAL natural block assignment, not a
hidden quotient chart or an assumed SAP instance.

Proved below: precise compatibility at every base block, and
preservation/reflection of block equality on the whole B
side, including the cross-sort case. Distinct real clone
codes and the final finite induced pushout remain separate
C16 obligations.
-/

namespace CCO.UnaryTermsReturn

open CCO

/-- The highest occupied original block label in a finite induced
A diagram, using the ACTUAL old carrier points. -/
noncomputable def commonBlockFiniteMax
    (A : FiniteInduced (X := CommonBlockReal)) : ℕ :=
  A.finite_vertices.toFinset.sup
    (fun p : Sigma CommonBlockReal => p.2.1)

/-- Every actual A vertex lies in a block at most the
finite maximum, including all named real sorts. -/
theorem commonBlockFiniteBlock_le_max
    (A : FiniteInduced (X := CommonBlockReal))
    (a : ↥A.vertices) :
    a.val.2.1 ≤ commonBlockFiniteMax A := by
  classical
  have hm : a.val ∈ A.finite_vertices.toFinset := by
    simpa using a.property
  exact Finset.le_sup (s := A.finite_vertices.toFinset)
    (f := fun p : Sigma CommonBlockReal => p.2.1) hm

/-- Colour-preserving complete old induced embeddings encode the
SAME equality of base block labels, on both sides. -/
theorem commonBlockBaseEmbeddingBlocks_iff
    (C A B : FiniteInduced (X := CommonBlockReal))
    (s : InducedEmbedding commonBlockOriginalAtomicSource C A)
    (t : InducedEmbedding commonBlockOriginalAtomicSource C B)
    (c d : ↥C.vertices) :
    (s.toEmbedding c).val.2.1 =
      (s.toEmbedding d).val.2.1 ↔
    (t.toEmbedding c).val.2.1 =
      (t.toEmbedding d).val.2.1 :=
  (commonBlockInducedEmbedding_preserves_block C A s c d).symm.trans
    (commonBlockInducedEmbedding_preserves_block C B t c d)

/-- Every B old block is either anchored to C and sent to its
corresponding ACTUAL A base block, or shifted above ALL A
block labels. The choice of a base representative does not
alter the resulting numeric label, proved separately.
The whole B carrier is finite, but no countability assumption
on hidden quotients is used. -/
noncomputable def commonBlockAmalgamLabel
    (C A B : FiniteInduced (X := CommonBlockReal))
    (s : InducedEmbedding commonBlockOriginalAtomicSource C A)
    (t : InducedEmbedding commonBlockOriginalAtomicSource C B)
    (b : ↥B.vertices) : ℕ := by
  classical
  exact if h : ∃ c : ↥C.vertices,
      (t.toEmbedding c).val.2.1 = b.val.2.1 then
    (s.toEmbedding (Classical.choose h)).val.2.1
  else
    commonBlockFiniteMax A + 1 + b.val.2.1

/-- The block label assigned to a B vertex with a base
anchor c is EXACTLY the old A block of s(c), independent
of any choice of a different representative of that block. -/
theorem commonBlockAmalgamLabel_base
    (C A B : FiniteInduced (X := CommonBlockReal))
    (s : InducedEmbedding commonBlockOriginalAtomicSource C A)
    (t : InducedEmbedding commonBlockOriginalAtomicSource C B)
    (b : ↥B.vertices) (c : ↥C.vertices)
    (hbc : (t.toEmbedding c).val.2.1 = b.val.2.1) :
    commonBlockAmalgamLabel C A B s t b =
      (s.toEmbedding c).val.2.1 := by
  classical
  unfold commonBlockAmalgamLabel
  split_ifs with h
  · have hd := Classical.choose_spec h
    exact (commonBlockBaseEmbeddingBlocks_iff C A B s t
      (Classical.choose h) c).mpr (hd.trans hbc.symm)
  · exact False.elim (h ⟨c,hbc⟩)

/-- Every unanchored B block receives a fresh numerical block
label strictly ABOVE the maximum occupied A block. This
constructs new ACTUAL original blocks, not just fresh clones
within an old block. -/
theorem commonBlockAmalgamLabel_fresh
    (C A B : FiniteInduced (X := CommonBlockReal))
    (s : InducedEmbedding commonBlockOriginalAtomicSource C A)
    (t : InducedEmbedding commonBlockOriginalAtomicSource C B)
    (b : ↥B.vertices)
    (hUnanchored : ¬ ∃ c : ↥C.vertices,
      (t.toEmbedding c).val.2.1 = b.val.2.1) :
    commonBlockAmalgamLabel C A B s t b =
      commonBlockFiniteMax A + 1 + b.val.2.1 := by
  classical
  simp only [commonBlockAmalgamLabel,dif_neg hUnanchored]

/-- The actual block assignment PRESERVES and REFLECTS
same-block equality within ALL of B, not merely on C.
It is the key finite-colour amalgamation witness. -/
theorem commonBlockAmalgamLabel_eq_iff
    (C A B : FiniteInduced (X := CommonBlockReal))
    (s : InducedEmbedding commonBlockOriginalAtomicSource C A)
    (t : InducedEmbedding commonBlockOriginalAtomicSource C B)
    (b b' : ↥B.vertices) :
    commonBlockAmalgamLabel C A B s t b =
        commonBlockAmalgamLabel C A B s t b' ↔
      b.val.2.1 = b'.val.2.1 := by
  classical
  let anchored (b : ↥B.vertices) : Prop :=
    ∃ c : ↥C.vertices,
      (t.toEmbedding c).val.2.1 = b.val.2.1
  constructor
  · intro hm
    by_cases hb : anchored b
    · obtain ⟨c,hc⟩ := hb
      by_cases hb' : anchored b'
      · obtain ⟨d,hd⟩ := hb'
        have hA : (s.toEmbedding c).val.2.1 =
            (s.toEmbedding d).val.2.1 := by
          calc
            _ = commonBlockAmalgamLabel C A B s t b :=
              (commonBlockAmalgamLabel_base C A B s t b c hc).symm
            _ = commonBlockAmalgamLabel C A B s t b' := hm
            _ = (s.toEmbedding d).val.2.1 :=
              commonBlockAmalgamLabel_base C A B s t b' d hd
        exact hc.symm.trans
          ((commonBlockBaseEmbeddingBlocks_iff C A B s t c d).mp hA |>.trans hd)
      · have hB := commonBlockAmalgamLabel_fresh C A B s t b' hb'
        have hA := commonBlockAmalgamLabel_base C A B s t b c hc
        have hBound := commonBlockFiniteBlock_le_max A
          (s.toEmbedding c)
        omega
    · by_cases hb' : anchored b'
      · obtain ⟨d,hd⟩ := hb'
        have hB := commonBlockAmalgamLabel_fresh C A B s t b hb
        have hA := commonBlockAmalgamLabel_base C A B s t b' d hd
        have hBound := commonBlockFiniteBlock_le_max A
          (s.toEmbedding d)
        omega
      · have hB := commonBlockAmalgamLabel_fresh C A B s t b hb
        have hB' := commonBlockAmalgamLabel_fresh C A B s t b' hb'
        omega
  · intro hbb'
    by_cases hb : anchored b
    · obtain ⟨c,hc⟩ := hb
      have hc' : (t.toEmbedding c).val.2.1 = b'.val.2.1 :=
        hc.trans hbb'
      rw [commonBlockAmalgamLabel_base C A B s t b c hc,
        commonBlockAmalgamLabel_base C A B s t b' c hc']
    · have hb' : ¬ anchored b' := by
        intro hh
        obtain ⟨c,hc⟩ := hh
        exact hb ⟨c,hc.trans hbb'.symm⟩
      rw [commonBlockAmalgamLabel_fresh C A B s t b hb,
        commonBlockAmalgamLabel_fresh C A B s t b' hb',
        hbb']

end CCO.UnaryTermsReturn
