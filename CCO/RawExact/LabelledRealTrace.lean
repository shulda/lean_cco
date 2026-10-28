import CCO.RawExact.RealTrace
import CCO.RawExact.AtomicStepTrace

/-!
# B002 C12/C18: genuine colour-certified RAW walk traces

A represented RAW WordPath records real intermediate vertices for
each typed diversity letter. We now obtain a finite consecutive
point list with exactly the literal old atomic edge colours, with
genuine identity letters erased. Walks need not be injective.
-/

universe u v w

namespace CCO.RawExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)

/-- Finite colour-certified walks on actual ORIGINAL tagged points.
A step must carry the real colour recorded in the source's dependent
atomic palette. Only diversity atoms are allowed as edges. -/
inductive TypedWalkCertificate :
    List (Sigma X) → List (TypedAtomicStep S) → Prop where
  | singleton (p : Sigma X) : TypedWalkCertificate [p] []
  | step {i j : ι} (x : X i) (y : X j)
      (a : S.Atom i j)
      {remaining : List (Sigma X)}
      {more : List (TypedAtomicStep S)}
      (edge : S.atomRel a x y)
      (rest : TypedWalkCertificate
        ((⟨j, y⟩ : Sigma X) :: remaining) more) :
      TypedWalkCertificate
        ((⟨i, x⟩ : Sigma X) :: (⟨j, y⟩ : Sigma X) :: remaining)
        ((⟨i, j, a⟩ : TypedAtomicStep S) :: more)

/-- Every original walk trace is nonempty, and starts at its
genuine original source vertex, with its exact sort tag. -/
theorem realWalkTrace_cons {i j : ι}
    {word : RawWord S i j} {x : X i} {z : X j}
    (h : WordPath S word x z) :
    ∃ tail : List (Sigma X),
      realWalkTrace S h = (⟨i, x⟩ : Sigma X) :: tail := by
  induction h with
  | nil x => exact ⟨[], rfl⟩
  | identity tail ih =>
      simpa only [realWalkTrace] using ih
  | atom a edge rest ih =>
      exact ⟨realWalkTrace S rest, rfl⟩

/-- Each letter of a real RAW word has the prescribed atomic colour
on adjacent points of its realized trace. This proves that word
witnesses can be attached as *actual* finite graph paths without
any source-level injectivity or hypothetical quotient section. -/
theorem realWalkTrace_certified {i j : ι}
    {word : RawWord S i j} {x : X i} {z : X j}
    (h : WordPath S word x z) :
    TypedWalkCertificate S
      (realWalkTrace S h) (rawAtomicSteps S word) := by
  induction h with
  | nil x =>
      exact TypedWalkCertificate.singleton (⟨_, x⟩ : Sigma X)
  | identity tail ih =>
      simpa only [realWalkTrace, rawAtomicSteps] using ih
  | atom a edge rest ih =>
      obtain ⟨pts, hpts⟩ := realWalkTrace_cons S rest
      rw [hpts] at ih
      simpa only [realWalkTrace, rawAtomicSteps, hpts] using
        (TypedWalkCertificate.step x _ a edge ih)

end CCO.RawExact
