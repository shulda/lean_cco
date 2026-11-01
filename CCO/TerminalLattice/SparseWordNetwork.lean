import CCO.TerminalLattice.OptionalPositiveNetwork
import CCO.TerminalLattice.ExternalUniformPowers
import CCO.ParityHasse.Sparse.Labelled

/-!
# B050 C27: ONE concrete finite OLD private word network

We reuse the ACCEPTED B002 generic finite private-word expansion
with all old original named sorts.  Its marked roots consist of
the real sparse-graph vertices (indices 0,...,W.size-1), plus one
LAST centre (index W.size). Each centre-to-root pair carries ONE
genuine OLD positive word spelling K-diversity; each actual sparse
graph edge carries ONE actual label-specific OLD positive word.
Every absent graph edge has NO original specified edge (empty typed
presentation, interpreted as old Top only for reference endpoints).

A single finite PartialDiagram is constructed. The difficult C27
proof that ALL its cycles contract to the two proved C30 word forms
remains open; no CCO is used in constructing this syntax.
-/

universe u v w t

namespace CCO.TerminalLattice

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]

/-- Genuine original centre index, disjoint from every graph-root
index and LAST in the canonical ordered marked vertex set. -/
def oldSparseCentre {q r g : Nat}
    (W : CCO.ParityHasse.Sparse.SparseLabelledGraph q r g) :
    Fin (W.size + 1) := Fin.last W.size

/-- Genuine graph-root indices, different from the LAST centre. -/
def oldSparseRoot {q r g : Nat}
    (W : CCO.ParityHasse.Sparse.SparseLabelledGraph q r g)
    (v : Fin W.size) : Fin (W.size + 1) :=
  Fin.castSucc v

/-- The actual ONE-word-or-NO-word selection on canonical marked
unordered pairs. The LAST centre is excluded from graph-edge tests.
All chosen words are source POSITIVE and same-sort at their endpoints,
even if their original typed private interiors visit other sorts. -/
noncomputable def oldSparseWordSelection {i : ι} {q r g : Nat}
    (W : CCO.ParityHasse.Sparse.SparseLabelledGraph q r g)
    (spoke : PositiveWord S i i)
    (words : Fin r → PositiveWord S i i) :
    CCO.RawExact.QuotientExpansion.Edge (W.size + 1) →
      Option (PositiveWord S i i) := by
  classical
  intro e
  if hCentre : e.val.2.val = W.size then
    exact some spoke
  else
    let x : Fin W.size :=
      ⟨e.val.1.val, by have hl := e.property; have hr := e.val.2.isLt; omega⟩
    let y : Fin W.size :=
      ⟨e.val.2.val, by have hr := e.val.2.isLt; omega⟩
    exact if W.graph.Adj x y then
      some (words (W.label s(x,y)))
    else none

/-- The one actual finite typed OLD source diagram for C31–C35.
The B002 private path construction supplies genuine finite vertices
and deterministic, converse-correct OLD atomic edge labels. -/
noncomputable def oldSparseWordDiagram
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i : ι} {q r g : Nat}
    (W : CCO.ParityHasse.Sparse.SparseLabelledGraph q r g)
    (spoke : PositiveWord S i i)
    (words : Fin r → PositiveWord S i i) :
    PartialDiagram S
      (CCO.RawExact.QuotientExpansion.Vertex S
        (fun _ : Fin (W.size+1) => i)
        (oldOptionalPositivePresentations S
          (oldSparseWordSelection S W spoke words))) :=
  oldOptionalPositiveDiagram S H sap
    (oldSparseWordSelection S W spoke words)

/-- The first `W.size` marked vertices are precisely graph roots,
and the last is a distinct centre, in one common ORIGINAL named
source sort. This is literal syntax, before any CCO homomorphism. -/
theorem oldSparseRoot_ne_centre {q r g : Nat}
    (W : CCO.ParityHasse.Sparse.SparseLabelledGraph q r g)
    (v : Fin W.size) :
    oldSparseRoot W v ≠ oldSparseCentre W := by
  intro h
  have hv : (oldSparseRoot W v).val = (oldSparseCentre W).val :=
    congrArg Fin.val h
  dsimp [oldSparseRoot, oldSparseCentre] at hv
  omega

end CCO.TerminalLattice
