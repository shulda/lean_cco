import CCO.TerminalHiddenHN.ReadoutRamsey
import CCO.TerminalHiddenHN.RealExpansion

/-! The finite comparison language is a concrete relational expansion of
the ORIGINAL real age. Its admissible predicate assignments are exactly
the orders on the actual generated hidden support. Restriction and all
embedding maps retain the same original vertices, including diagonal
comparison tuples. No SAP, cover or CCO gate enters this construction. -/

universe u v w r l k
namespace CCO.TerminalHiddenHN.RealInterpretation
open CCO.UnaryFreshFrames
noncomputable section
variable {ι : Type u} {X : ι → Type v} {S : CCO.AtomicSource.{u,v,w} ι X}
variable {G : Type r} [Group G] [∀ i, MulAction G (X i)]
variable {U : Language.{max u l}} {V : Type k} {P : Structure U V}
variable (D : RealInterpretation (G := G) S U P) (H : CCO.HomogeneousSource S G)

/-- One new binary name for each ordered pair of real-source normal
forms. Unary names are empty; all old predicates remain in the old age. -/
def readoutExpansion : CCO.TerminalHiddenHN.RealExpansionData S where
  Unary := PEmpty.{max u l + 1}
  Binary := D.ComparisonName H
  finiteUnary := inferInstance
  finiteBinary := D.ComparisonName_finite H
  unarySort := PEmpty.elim
  leftSort q := q.1
  rightSort q := q.2.1
  Expansion := D.ReadoutOn
  nonempty := D.readout_nonempty H
  unary a q := PEmpty.elim q
  binary a q x y := D.comparison H a q x y
  unary_sorted a q := PEmpty.elim q
  binary_sorted a q x y h := D.comparison_sorted H a q x y h
  faithful a b hu hb := D.readout_faithful H a b hb
  restrict e b := D.restrictReadout H e b
  restrict_unary e b q := PEmpty.elim q
  restrict_binary e b q x y := D.comparison_restrict H e b q x y

/-- This is literal precompactness on a fixed old carrier, with no
replacement of that carrier by an isomorphism class. -/
theorem readoutExpansion_precompact (A : CCO.FiniteInduced (X := X)) :
    Finite ((D.readoutExpansion H).Expansion A) :=
  (D.readoutExpansion H).finite_expansions A

theorem readoutExpansion_reasonable : (D.readoutExpansion H).Reasonable := by
  intro A B e a
  exact D.readout_reasonable H e a

/-- Forgetting the redundant non-order codes changes no embedding set:
the finite comparison predicates recover the entire hidden order. -/
def relationalToReadout {A B : CCO.FiniteInduced (X := X)}
    {a : D.ReadoutOn A} {b : D.ReadoutOn B}
    (e : (D.readoutExpansion H).Embedding a b) : D.ReadoutEmbedding H a b :=
  D.readoutEmbedding_of_comparisons H e.old (fun q x y => (e.binary_iff q x y).symm)

def readoutToRelational {A B : CCO.FiniteInduced (X := X)}
    {a : D.ReadoutOn A} {b : D.ReadoutOn B}
    (e : D.ReadoutEmbedding H a b) : (D.readoutExpansion H).Embedding a b where
  old := e.old
  unary_iff q := PEmpty.elim q
  binary_iff q x y := (D.comparison_readoutEmbedding H e q x y).symm

def relationalReadoutEquiv {A B : CCO.FiniteInduced (X := X)}
    (a : D.ReadoutOn A) (b : D.ReadoutOn B) :
    (D.readoutExpansion H).Embedding a b ≃ D.ReadoutEmbedding H a b where
  toFun := D.relationalToReadout H
  invFun := D.readoutToRelational H
  left_inv e := by ext x; rfl
  right_inv e := by apply ReadoutEmbedding.ext H; rfl

theorem readoutToRelational_comp {A B C : CCO.FiniteInduced (X := X)}
    {a : D.ReadoutOn A} {b : D.ReadoutOn B} {c : D.ReadoutOn C}
    (g : D.ReadoutEmbedding H b c) (f : D.ReadoutEmbedding H a b) :
    D.readoutToRelational H (g.comp H f) =
      (D.readoutToRelational H g).comp (D.readoutToRelational H f) := by
  ext x
  rfl

/-- The actual hidden Ramsey input is discharged separately by the
terminal HN theorem. The readout transfer itself assumes only that input
on the SAME whole age, including arbitrary orphan-bearing hosts. -/
theorem readoutExpansion_ramsey
    (ramsey : CCO.FullCode.HasHiddenRamsey D.orderedAge) :
    (D.readoutExpansion H).Ramsey := by
  intro A B a b n hn
  obtain ⟨C,c,hC⟩ := D.readout_ramsey H ramsey A B a b n hn
  refine ⟨C,c,?_⟩
  intro colour
  obtain ⟨g,shade,hg⟩ := hC (fun f => colour (D.readoutToRelational H f))
  refine ⟨D.readoutToRelational H g,?_⟩
  intro f₁ f₂
  have h₁ := hg (D.relationalToReadout H f₁)
  have h₂ := hg (D.relationalToReadout H f₂)
  have eq₁ : D.readoutToRelational H (g.comp H (D.relationalToReadout H f₁)) =
      (D.readoutToRelational H g).comp f₁ := by
    ext x
    rfl
  have eq₂ : D.readoutToRelational H (g.comp H (D.relationalToReadout H f₂)) =
      (D.readoutToRelational H g).comp f₂ := by
    ext x
    rfl
  exact (congrArg colour eq₁).symm.trans (h₁.trans (h₂.symm.trans (congrArg colour eq₂)))

/-- Standalone source readout theorem: finite relationality and literal
precompact reasonableness use only A01/A02; Ramsey uses exactly A05. -/
theorem hasFiniteRelationalRamseyExpansion_of_hiddenRamsey
    (ramsey : CCO.FullCode.HasHiddenRamsey D.orderedAge) :
    CCO.TerminalHiddenHN.HasFiniteRelationalRamseyExpansion S :=
  ⟨D.readoutExpansion H,D.readoutExpansion_reasonable H,D.readoutExpansion_ramsey H ramsey⟩

end
end CCO.TerminalHiddenHN.RealInterpretation
