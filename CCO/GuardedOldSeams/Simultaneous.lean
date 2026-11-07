import CCO.GuardedOldSeams.WordInsertion

/-!
# Simultaneous exact original-word insertion

Each request stores its literal positive word and actual fine endpoint
atom.  A finite induction grows one complete induced old base; the next
word avoids that entire current base.  Endpoint pairs may overlap.
-/

universe u v a t

namespace CCO.GuardedOldSeams

open StrongExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,a} ι X)

/-- An obligation for this particular old positive word and these actual
distinct endpoints; no coarser semigroup element replaces the word. -/
structure WordRequest where
  sourceSort : ι
  targetSort : ι
  word : PositiveWord S sourceSort targetSort
  source : X sourceSort
  target : X targetSort
  atom : S.Atom sourceSort targetSort
  profile : atom ∈ PositiveWord.profile S word
  colour : S.colour source target = some atom

def WordRequest.InBase (r : WordRequest S) (A : FiniteInduced (X := X)) : Prop :=
  (⟨r.sourceSort, r.source⟩ : Sigma X) ∈ A.vertices ∧
  (⟨r.targetSort, r.target⟩ : Sigma X) ∈ A.vertices

theorem WordRequest.endpoints_distinct (r : WordRequest S) :
    (⟨r.sourceSort, r.source⟩ : Sigma X) ≠ ⟨r.targetSort, r.target⟩ :=
  S.atomRel_ne r.colour

def lineRange {i j : ι} {w : PositiveWord S i j} {x : X i} {y : X j}
    (line : LiteralLine S w x y) : Set (Sigma X) := Set.range (lineImage S line)

def lineInterior {i j : ι} {w : PositiveWord S i j} {x : X i} {y : X j}
    (line : LiteralLine S w x y) : Set (Sigma X) :=
  {z | ∃ p : wordPositions S w,
    p ≠ wordSource S w ∧ p ≠ wordTarget S w ∧ lineImage S line p = z}

theorem finite_lineRange {i j : ι} {w : PositiveWord S i j} {x : X i} {y : X j}
    (line : LiteralLine S w x y) : (lineRange S line).Finite := by
  let : Finite (wordPositions S w) := finite_wordPositions S w
  exact Set.finite_range _

theorem lineInterior_subset_range {i j : ι} {w : PositiveWord S i j}
    {x : X i} {y : X j} (line : LiteralLine S w x y) :
    lineInterior S line ⊆ lineRange S line := by
  rintro z ⟨p, _, _, hp⟩
  exact ⟨p, hp⟩

/-- A literal complete old extension: all pair colours are inherited from
the same original source and the old points themselves are retained. -/
def extendBase (A : FiniteInduced (X := X)) {i j : ι} {w : PositiveWord S i j}
    {x : X i} {y : X j} (line : LiteralLine S w x y) : FiniteInduced (X := X) where
  vertices := A.vertices ∪ lineRange S line
  finite_vertices := A.finite_vertices.union (finite_lineRange S line)

theorem old_subset_extendBase (A : FiniteInduced (X := X)) {i j : ι}
    {w : PositiveWord S i j} {x : X i} {y : X j} (line : LiteralLine S w x y) :
    A.vertices ⊆ (extendBase S A line).vertices := fun _ h => Or.inl h

def FreshWordLine.weaken {i j : ι} {w : PositiveWord S i j} {x : X i} {y : X j}
    {Z Z' : Set (Sigma X)} (line : FreshWordLine S w x y Z') (h : Z ⊆ Z') :
    FreshWordLine S w x y Z where
  toLiteralLine := line.toLiteralLine
  injective := line.injective
  fresh p hs ht hp := line.fresh p hs ht (h hp)

theorem FreshWordLine.interior_disjoint {i j : ι} {w : PositiveWord S i j}
    {x : X i} {y : X j} {Z : Set (Sigma X)} (line : FreshWordLine S w x y Z) :
    Disjoint (lineInterior S line.toLiteralLine) Z := by
  rw [Set.disjoint_left]
  rintro z ⟨p, hs, ht, rfl⟩ hz
  exact line.fresh p hs ht hz

/-- All requested words occur in a single finite complete induced member.
Each is simple, every interior avoids the original old base, and interiors
of distinct obligations are disjoint. -/
structure SimultaneousWords (A : FiniteInduced (X := X)) {n : Nat}
    (requests : Fin n → WordRequest S) where
  base : FiniteInduced (X := X)
  old_subset : A.vertices ⊆ base.vertices
  endpoints_old : ∀ k, (requests k).InBase S A
  line : ∀ k, FreshWordLine S (requests k).word
    (requests k).source (requests k).target A.vertices
  line_subset : ∀ k, lineRange S (line k).toLiteralLine ⊆ base.vertices
  private_interiors : ∀ k l, k ≠ l →
    Disjoint (lineInterior S (line k).toLiteralLine)
      (lineInterior S (line l).toLiteralLine)

/-- C59--C63: actual finite simultaneous insertion, using only the original
homogeneity and visible SAP.  The recursive forbidden set contains every
earlier word as well as all of the complete old base. -/
theorem simultaneous_word_insertion
    {G : Type t} [Group G] [∀ q : ι, MulAction G (X q)]
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (A : FiniteInduced (X := X)) {n : Nat} (requests : Fin n → WordRequest S)
    (endpoints : ∀ k, (requests k).InBase S A) :
    Nonempty (SimultaneousWords S A requests) := by
  classical
  induction n with
  | zero =>
      exact ⟨{
        base := A
        old_subset := fun _ h => h
        endpoints_old := endpoints
        line := fun k => Fin.elim0 k
        line_subset := fun k => Fin.elim0 k
        private_interiors := fun k => Fin.elim0 k }⟩
  | succ n ih =>
      let tail : Fin n → WordRequest S := fun k => requests k.succ
      obtain ⟨old⟩ := ih tail (fun k => endpoints k.succ)
      let r := requests 0
      obtain ⟨new⟩ := fresh_word_line_of_profile S H sap r.word r.atom r.profile
        r.source r.target r.colour old.base.vertices old.base.finite_vertices
      let B := extendBase S old.base new.toLiteralLine
      let lines : ∀ k, FreshWordLine S (requests k).word
          (requests k).source (requests k).target A.vertices :=
        Fin.cases (new.weaken S old.old_subset) old.line
      refine ⟨{
        base := B
        old_subset := old.old_subset.trans (old_subset_extendBase S old.base new.toLiteralLine)
        endpoints_old := endpoints
        line := lines
        line_subset := ?_
        private_interiors := ?_ }⟩
      · intro k
        refine Fin.cases ?_ (fun k => ?_) k
        · exact fun _ h => Or.inr h
        · exact (old.line_subset k).trans
            (old_subset_extendBase S old.base new.toLiteralLine)
      · intro k l
        refine Fin.cases ?_ (fun k => ?_) k
        · refine Fin.cases ?_ (fun l => ?_) l
          · intro h
            exact False.elim (h rfl)
          · intro _
            exact (new.interior_disjoint S).mono_right
              ((lineInterior_subset_range S (old.line l).toLiteralLine).trans
                (old.line_subset l))
        · refine Fin.cases ?_ (fun l => ?_) l
          · intro _
            exact ((new.interior_disjoint S).mono_right
              ((lineInterior_subset_range S (old.line k).toLiteralLine).trans
                (old.line_subset k))).symm
          · intro h
            exact old.private_interiors k l (fun heq => h (congrArg Fin.succ heq))

/-- With no obligations the literal old complete base already suffices. -/
theorem simultaneous_empty (A : FiniteInduced (X := X)) :
    ∃ out : SimultaneousWords S A (Fin.elim0 : Fin 0 → WordRequest S), out.base = A := by
  exact ⟨{
    base := A
    old_subset := fun _ h => h
    endpoints_old := fun k => Fin.elim0 k
    line := fun k => Fin.elim0 k
    line_subset := fun k => Fin.elim0 k
    private_interiors := fun k => Fin.elim0 k }, rfl⟩

/-- The retained old vertices form an induced embedding, hence preserve
every complete old colour, including the real diagonal. -/
def SimultaneousWords.old_embedding (A : FiniteInduced (X := X)) {n : Nat}
    {requests : Fin n → WordRequest S} (out : SimultaneousWords S A requests) :
    InducedEmbedding S A out.base where
  toEmbedding := {
    toFun := fun p => ⟨p.val, out.old_subset p.property⟩
    inj' := fun _ _ h => Subtype.ext
      (congrArg (fun p : ↥out.base.vertices => p.val) h) }
  preserves_sort _ := rfl
  preserves_colours _ _ := rfl

end CCO.GuardedOldSeams
