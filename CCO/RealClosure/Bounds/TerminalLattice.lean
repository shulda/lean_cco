import CCO.RealClosure.Bounds.TerminalWords
import CCO.ExactCRT.SourceLattice

/-! B011 C28: only AFTER the CCO-free one-word theorem, original semantic
CCO supplies exact-ball Helly and upgrades the actual exact distributive
sublattice to the FULL original invariant lattice. -/
universe u v w t
namespace CCO.RealClosure.Bounds
open CCO.ParityHasse.Original CCO.ExactCRT
variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X) {i : ι}
variable {G : Type t} [Group G] [∀ j, MulAction G (X j)]
variable (H : HomogeneousSource S G)
include H

/-- Exactness follows from one word, independently of CCO or SAP. -/
theorem terminal_all_exact (nr2 : SortNR2 S i) (E : ColourEq S i) :
    IsExactEq S E.val := by
  obtain ⟨D,_,hD⟩ := terminal_single_word_exact S H nr2 E
  exact ⟨D,hD⟩

/-- Exact and full equivalences coincide only after terminal word discharge.
The CCO argument is used for the sublattice structure, not word existence. -/
noncomputable def terminalExactOrderIso (cco : SemanticCCO.{u,v,max u v,w} S)
    (nr2 : SortNR2 S i) : ColourEq S i ≃o ExactEq S H cco i where
  toFun E := ⟨E.val,terminal_all_exact S H nr2 E⟩
  invFun E := ⟨E.val,isExactEq_colourInvariant S H E.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

/-- Full-lattice distributivity uses original semantic CCO and the actual
B008 exact lattice theorem. No distributivity enters the word proof. -/
@[instance_reducible] def terminalDistribLattice
    (cco : SemanticCCO.{u,v,max u v,w} S) (nr2 : SortNR2 S i) :
    letI := ColourEq.lattice S H (i := i)
    DistribLattice (ColourEq S i) := by
  letI := ColourEq.lattice S H (i := i)
  letI := exactDistribLattice S H cco i
  apply DistribLattice.ofInfSupLe
  intro E F K
  let e : ExactEq S H cco i := terminalExactOrderIso S H cco nr2 E
  let f : ExactEq S H cco i := terminalExactOrderIso S H cco nr2 F
  let k : ExactEq S H cco i := terminalExactOrderIso S H cco nr2 K
  have hd : e ⊓ (f ⊔ k) ≤ (e ⊓ f) ⊔ (e ⊓ k) := le_of_eq (inf_sup_left e f k)
  exact hd

/-- Source-facing export retaining the source SAP premise while separating
its logical role from the weaker CCO-free word theorem above. -/
theorem terminal_source_words_and_distributivity (_sap : AgeSAP S)
    (cco : SemanticCCO.{u,v,max u v,w} S) (nr2 : SortNR2 S i) :
    (∀ E : ColourEq S i, ∃ word : RawWord S i i, RawWord.relation S word = E.val.r) ∧
    (letI := ColourEq.lattice S H (i := i); Nonempty (DistribLattice (ColourEq S i))) :=
  ⟨terminal_one_raw_word S H nr2,⟨terminalDistribLattice S H cco nr2⟩⟩

end CCO.RealClosure.Bounds
