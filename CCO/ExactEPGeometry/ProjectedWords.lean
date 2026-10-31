import CCO.APCharacter.Towers.UnaryReduct
import CCO.RawExact.Presentations

/-!
# B062 C23–C27: literal RAW-word forgetfulness for actual unary reducts

An actual unary refinement retains the very same original binary atom
names (injectively) and a bijection of the whole real point carriers.
Forgetting a current RAW word therefore constructs one precisely typed
ORIGINAL RAW word. Every genuine current witness maps to a genuine old
witness, including the real diagonal and repeated intermediate vertices.

The reverse containment is NOT claimed: a middle old vertex need not
belong to the prescribed intermediate child sort. That step requires
the genuine AP-only nonempty trace-product theorem and is separately
recorded in the source C23–C28 contract. No SAP or quotient section.
-/

universe u v w

namespace CCO.ExactEPGeometry.ProjectedWords

variable {ι κ : Type u} {X : ι → Type v} {Y : κ → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable (T : AtomicSource.{u,v,w} κ Y)
variable (P : APCharacter.Towers.UnaryReduct S T)

/-- Current atomic edges are EXACTLY old named atomic edges between the
projected endpoints, provided the current atom name is fixed. The
converse uses injectivity of the genuine binary name map, not SAP. -/
theorem atom_iff {i j : κ} (a : T.Atom i j) (x : Y i) (y : Y j) :
    T.atomRel a x y ↔
      S.atomRel (P.atom i j a) (P.point i x) (P.point j y) := by
  change T.colour x y = some a ↔
    S.colour (P.point i x) (P.point j y) = some (P.atom i j a)
  rw [P.colour i j x y]
  constructor
  · intro h
    rw [h]
    rfl
  · intro h
    cases hc : T.colour x y with
    | none =>
        rw [hc] at h
        cases h
    | some b =>
        rw [hc] at h
        have hb : P.atom i j b = P.atom i j a := Option.some.inj h
        exact hc.trans (congrArg some ((P.atom_injective i j) hb))

/-- The projected diagonal is still the TRUE diagonal: the whole-carrier
bijection excludes collisions of two distinct child points. -/
theorem point_eq_iff {i : κ} (x y : Y i) :
    P.point i x = P.point i y ↔ x = y := by
  constructor
  · intro h
    have he : (⟨P.parent i, P.point i x⟩ : Sigma X) =
        ⟨P.parent i, P.point i y⟩ :=
      congrArg (fun z : X (P.parent i) => (⟨P.parent i,z⟩ : Sigma X)) h
    have htag : (⟨i,x⟩ : Sigma Y) = ⟨i,y⟩ := P.bijective.1 he
    simpa only [Sigma.mk.injEq, heq_eq_eq, true_and] using htag
  · exact congrArg (P.point i)

/-- Properly sort-indexed erasure of a complete CURRENT RAW word to a
complete ORIGINAL RAW word, retaining every identity letter and every
actually named diversity atom. -/
def forgetWord {i j : κ} : RawWord T i j →
    RawWord S (P.parent i) (P.parent j)
  | .nil i => .nil (P.parent i)
  | .identity tail => .identity (forgetWord tail)
  | .atom a tail => .atom (P.atom _ _ a) (forgetWord tail)

/-- The forward word trace proof constructs every original intermediate
vertex by projecting the SAME real current intermediate witness. Hence
the marked route cannot acquire a fake original diagonal or skip an edge. -/
theorem forgetWord_forward {i j : κ} (W : RawWord T i j) :
    ∀ x : Y i, ∀ y : Y j,
      RawWord.relation T W x y →
        RawWord.relation S (forgetWord S T P W)
          (P.point i x) (P.point j y) := by
  induction W with
  | nil i =>
      intro x y h
      change P.point i x = P.point i y
      exact congrArg (P.point i) h
  | identity tail ih =>
      exact ih
  | atom a tail ih =>
      intro x z h
      obtain ⟨y,hxy,hyz⟩ := h
      refine ⟨P.point _ y, ?_, ih y z hyz⟩
      exact (atom_iff S T P a x y).mp hxy

/-- Old RAW word presentations obtained by forgetting every current
restriction. Empty presentation remains old Top, not Id or an empty
diversity palette. -/
def forgetProfile {i j : κ} (L : RawExact.Presentation T i j) :
    RawExact.Presentation S (P.parent i) (P.parent j) :=
  L.map (forgetWord S T P)

/-- Every real current word-profile witness satisfies ALL original
forgotten restrictions, not merely the union of their palette supports. -/
theorem forgetProfile_forward {i j : κ} (L : RawExact.Presentation T i j)
    (x : Y i) (y : Y j)
    (h : RawExact.evaluate T L x y) :
    RawExact.evaluate S (forgetProfile S T P L)
      (P.point i x) (P.point j y) := by
  intro W hW
  obtain ⟨U,hU,rfl⟩ := List.mem_map.mp hW
  exact forgetWord_forward S T P U x y (h U hU)

/-- A GENUINELY nonempty current RAW exact domain yields a GENUINELY
nonempty original RAW exact profile, with an actual projected pair. This
is the forward original lift construction used in C26/C27; converse
equality of the current trace is still an open source obligation. -/
def forgetExact {i j : κ} (D : RawExact.NonemptyExact T i j) :
    RawExact.NonemptyExact S (P.parent i) (P.parent j) := by
  refine ⟨forgetProfile S T P D.words, ?_⟩
  obtain ⟨x,y,hxy⟩ := D.nonempty
  exact ⟨P.point i x, P.point j y,
    forgetProfile_forward S T P D.words x y hxy⟩

/-- Forward source-to-original lift relation: the output is an actual
old word-profile pair on the original sort, not a quotient-domain point. -/
theorem forgetExact_forward {i j : κ}
    (D : RawExact.NonemptyExact T i j) (x : Y i) (y : Y j)
    (h : RawExact.evaluate T D.words x y) :
    RawExact.evaluate S (forgetExact S T P D).words
      (P.point i x) (P.point j y) :=
  forgetProfile_forward S T P D.words x y h

end CCO.ExactEPGeometry.ProjectedWords
