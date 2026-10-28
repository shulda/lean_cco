import CCO.RawExact.CertifiedWalkChain

/-!
# B002 C12/C18: RAW walk colours do not depend on chosen real witnesses

Two actual WordPath realizations of the SAME typed RAW word can have
different real vertices and even different output pairs. However each
genuine diversity edge has exactly the word's recorded original atom.
The full consecutive old tagged pair-colour sequences therefore agree.

This is the key soundness statement allowing one arbitrary reference
walk to assign edge labels in the private fan, while using a DIFFERENT
pairwise-common-root witness to realize a simple cycle. No source
CCO, SAP, tuple lifting or quotient section is assumed.
-/

universe u v w

namespace CCO.RawExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)

/-- Corresponding edges in the two actual tagged real-point traces
have identical full original typed pair colours. The traces need
not have identical points. -/
def SameEdgeColours : List (Sigma X) → List (Sigma X) → Prop
  | [], [] => True
  | [_], [_] => True
  | p :: q :: tail, p' :: q' :: tail' =>
      taggedColour S p q = taggedColour S p' q' ∧
      SameEdgeColours (q :: tail) (q' :: tail')
  | _, _ => False

/-- Two genuine certificates with the SAME typed atomic word letters
have exactly matching full old edge colours, even if their real
endpoints or intermediate vertices differ. -/
theorem sameEdgeColours_of_certificates
    {points points' : List (Sigma X)}
    {steps : List (TypedAtomicStep S)}
    (h : TypedWalkCertificate S points steps)
    (h' : TypedWalkCertificate S points' steps) :
    SameEdgeColours S points points' := by
  induction h generalizing points' with
  | singleton p =>
      cases h' with
      | singleton q => trivial
  | step x y a edge rest ih =>
      cases h' with
      | step x' y' a' edge' rest' =>
          constructor
          · change S.colour x y = S.colour x' y'
            change S.colour x y = some a at edge
            change S.colour x' y' = some a at edge'
            exact edge.trans edge'.symm
          · exact ih rest'

/-- Direct consumer for two independent actual OLD realizations
of the SAME RAW word; no common root was presupposed. -/
theorem sameEdgeColours_of_wordPaths
    {i j : ι} (word : RawWord S i j)
    {x x' : X i} {y y' : X j}
    (h : WordPath S word x y)
    (h' : WordPath S word x' y') :
    SameEdgeColours S (realWalkTrace S h) (realWalkTrace S h') :=
  sameEdgeColours_of_certificates S
    (realWalkTrace_certified S h)
    (realWalkTrace_certified S h')

end CCO.RawExact
