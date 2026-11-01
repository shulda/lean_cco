import CCO.TerminalLattice.OriginalThetaPresentations
import CCO.TerminalLattice.SparseWordMarkedEdges
import CCO.TerminalLattice.CentreAbsorption

/-!
# B050 source08 C26–C30: ONE real sparse graph of PRIVATE MULTI-BRANCH theta gadgets

The standalone original typed theta-cycle lemma is stronger than the
single-word private network used for source C40. Here each actual
unoriented W graph edge of label j carries an arbitrary FINITE NONEMPTY
list of distinct private positive OLD typed word branches whose
individual STRONG endpoint profiles all CONTAIN the prescribed menu T_j.
Every centre spoke may carry an arbitrary finite list of branches
containing K-diversity; the list may be EMPTY, representing a BARE
unconstrained Top spoke which specifies literally NO old atomic edge.
Every missing W graph edge also has an empty private presentation.

This constructs ONE honest finite typed original source partial diagram
via accepted B002 with all original intermediate named sorts. There
is no original CCO invocation, quotient action, hidden one-word
assumption, or added old identity edge at this stage.
-/

universe u v w t

namespace CCO.TerminalLattice

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ j : ι, MulAction G (X j)]

/-- Assign the ACTUAL private list to each canonical original
marked pair: centre last has optional spoke theta branches, genuine
W edges have their label-specific theta branches, and all absent
graph edges have no old specified edge or word occurrence. -/
noncomputable def originalSparseThetaSelection
    {i : ι} {q r g : Nat}
    (W : CCO.ParityHasse.Sparse.SparseLabelledGraph q r g)
    (spokes : List (PositiveWord S i i))
    (families : Fin r → List (PositiveWord S i i)) :
    CCO.RawExact.QuotientExpansion.Edge (W.size+1) →
      List (PositiveWord S i i) := by
  classical
  intro e
  if hCentre : e.val.2.val = W.size then
    exact spokes
  else
    let x : Fin W.size :=
      ⟨e.val.1.val, by
        have hl := e.property
        have hr := e.val.2.isLt
        omega⟩
    let y : Fin W.size :=
      ⟨e.val.2.val, by
        have hr := e.val.2.isLt
        omega⟩
    exact if W.graph.Adj x y then
      families (W.label s(x,y))
    else []

/-- The ACTUAL assigned fine STRONG menu of the same genuine
canonical marked pair. A bare or missing edge can use an arbitrary
empty guard; its REAL presentation is empty and contributes no
positive occurrence. -/
noncomputable def originalSparseThetaGuard
    {i : ι} {q r g : Nat}
    (W : CCO.ParityHasse.Sparse.SparseLabelledGraph q r g)
    (K : ParityHasse.Original.ColourEq S i)
    (menus : Fin r → S.Menu i i) :
    CCO.RawExact.QuotientExpansion.Edge (W.size+1) → S.Menu i i := by
  classical
  intro e
  if hCentre : e.val.2.val = W.size then
    exact originalEquivDiversityPalette S K
  else
    let x : Fin W.size :=
      ⟨e.val.1.val, by
        have hl := e.property
        have hr := e.val.2.isLt
        omega⟩
    let y : Fin W.size :=
      ⟨e.val.2.val, by
        have hr := e.val.2.isLt
        omega⟩
    exact if W.graph.Adj x y then
      menus (W.label s(x,y))
    else ∅

/-- This is a true SOURCE theta path requirement, not an assumption
that any branch word has EXACT spectrum T_j: each graph label has
a NONEMPTY finite list of positive words, and each word's profile
merely contains its nonempty assigned STRONG menu. -/
def OriginalSparseThetaBranchSpec
    {i : ι} {r : Nat}
    (K : ParityHasse.Original.ColourEq S i)
    (spokes : List (PositiveWord S i i))
    (menus : Fin r → S.Menu i i)
    (families : Fin r → List (PositiveWord S i i)) : Prop :=
  (∀ p ∈ spokes,
    originalEquivDiversityPalette S K ⊆ PositiveWord.profile S p) ∧
  (∀ j : Fin r,
    families j ≠ [] ∧
    (menus j).Nonempty ∧
    ∀ p ∈ families j, menus j ⊆ PositiveWord.profile S p)

/-- EVERY genuine marked pair with at least one specified positive
private word has one nonempty OLD fine menu common to ALL its
branches. If the pair is a bare spoke or absent graph edge,
the premise is FALSE, so no invented source realization occurs. -/
theorem originalSparseTheta_guards_valid
    {i : ι} {q r g : Nat}
    (W : CCO.ParityHasse.Sparse.SparseLabelledGraph q r g)
    (K : ParityHasse.Original.ColourEq S i)
    (hK : (⊥ : ParityHasse.Original.ColourEq S i) < K)
    (spokes : List (PositiveWord S i i))
    (menus : Fin r → S.Menu i i)
    (families : Fin r → List (PositiveWord S i i))
    (hSpec : OriginalSparseThetaBranchSpec S K spokes menus families) :
    ∀ e, originalSparseThetaSelection S W spokes families e ≠ [] →
      (originalSparseThetaGuard S W K menus e).Nonempty ∧
      ∀ p ∈ originalSparseThetaSelection S W spokes families e,
        originalSparseThetaGuard S W K menus e ⊆
          PositiveWord.profile S p := by
  classical
  intro e hPresent
  by_cases hCentre : e.val.2.val = W.size
  · have hSpoke : originalSparseThetaSelection S W spokes families e =
        spokes := by
      simp [originalSparseThetaSelection,hCentre]
    have hGuard : originalSparseThetaGuard S W K menus e =
        originalEquivDiversityPalette S K := by
      simp [originalSparseThetaGuard,hCentre]
    rw [hSpoke] at hPresent ⊢
    rw [hGuard]
    refine ⟨original_nonzero_Kdiv_nonempty S K hK,?_⟩
    exact hSpec.1
  · let x : Fin W.size :=
      ⟨e.val.1.val, by
        have hl := e.property
        have hr := e.val.2.isLt
        omega⟩
    let y : Fin W.size :=
      ⟨e.val.2.val, by
        have hr := e.val.2.isLt
        omega⟩
    by_cases hAdj : W.graph.Adj x y
    · have hSel : originalSparseThetaSelection S W spokes families e =
          families (W.label s(x,y)) := by
        simp [originalSparseThetaSelection,hCentre,x,y,hAdj]
      have hMenu : originalSparseThetaGuard S W K menus e =
          menus (W.label s(x,y)) := by
        simp [originalSparseThetaGuard,hCentre,x,y,hAdj]
      rw [hSel,hMenu]
      obtain ⟨_,hne,hContained⟩ := hSpec.2 (W.label s(x,y))
      exact ⟨hne,hContained⟩
    · have hSel : originalSparseThetaSelection S W spokes families e =
          [] := by
        simp [originalSparseThetaSelection,hCentre,x,y,hAdj]
      exact False.elim (hPresent hSel)

/-- The actual finite typed OLD theta network with EVERY given
private branch of EVERY present sparse graph edge/spoke. Original
B002 supplies honest private interiors, deterministic specified
atomic colours, and finite formal vertices. All presentations
have a genuine reference pair thanks to the proved common fine
menu, even for multiple distinct branches on the same marked pair.

Only ORIGINAL source H and SAP are used to construct reference walks.
Original CCO is not invoked and no global root homomorphism is assumed.
-/
noncomputable def originalSparseThetaDiagram
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i : ι} {q r g : Nat}
    (W : CCO.ParityHasse.Sparse.SparseLabelledGraph q r g)
    (K : ParityHasse.Original.ColourEq S i)
    (hK : (⊥ : ParityHasse.Original.ColourEq S i) < K)
    (spokes : List (PositiveWord S i i))
    (menus : Fin r → S.Menu i i)
    (families : Fin r → List (PositiveWord S i i))
    (hSpec : OriginalSparseThetaBranchSpec S K spokes menus families) :
    PartialDiagram S
      (CCO.RawExact.QuotientExpansion.Vertex S
        (fun _ : Fin (W.size+1) => i)
        (originalThetaPresentations S
          (originalSparseThetaSelection S W spokes families))) :=
  originalThetaDiagram S H sap
    (originalSparseThetaSelection S W spokes families)
    (originalSparseThetaGuard S W K menus)
    (originalSparseTheta_guards_valid
      S W K hK spokes menus families hSpec)

end CCO.TerminalLattice
