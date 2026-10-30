import CCO.APCharacter.Completion.Walks
import CCO.APCharacter.Paths

/-! The finite family of ALL simple endpoint paths has a common old output;
phase primality chooses an allowed output from exactly that same family. -/
universe u v w z t
namespace CCO.APCharacter.Completion
variable {ι : Type u} {X : ι → Type v} {S : AtomicSource.{u,v,w} ι X}
variable {V : Type z} (D : PartialDiagram S V) (M : MaskData S)
variable (bits : V → Bit) (legal : M.LocalLegal D bits)

noncomputable def markedWalk {x y : V} (p : (graph D).Walk x y) :
    M.MarkedWord (i := D.vertexSort x) (j := D.vertexSort y) (bits x) (bits y) :=
  match p with
  | .nil => .nil _ _ (legal.1 _)
  | .cons h p => .atom (edgeAtom D h) (legal.1 _)
      (legal.2 _ _ h.choose (edgeAtom D h) (edgeAtom_spec D h)) (markedWalk p)

theorem markedWalk_word {x y : V} (p : (graph D).Walk x y) :
    (markedWalk D M bits legal p).word = walkWord D p := by
  induction p with
  | nil => rfl
  | cons h p ih =>
    change RawWord.atom _ (markedWalk D M bits legal p).word = RawWord.atom _ (walkWord D p)
    rw [ih]

noncomputable def pathExact (f : DiagramHom D) {x y : V}
    (p : (graph D).Path x y) : RawExact.NonemptyExact S (D.vertexSort x) (D.vertexSort y) where
  words := [walkWord D p.val]
  nonempty := ⟨f.point x,f.point y,by
    intro word hw
    have he : word = walkWord D p.val := List.mem_singleton.mp hw
    subst word
    exact hom_realizes_walk D f p.val⟩

@[simp] theorem pathExact_relation (f : DiagramHom D) {x y : V}
    (p : (graph D).Path x y) (a : X (D.vertexSort x)) (b : X (D.vertexSort y)) :
    RawExact.evaluate S (pathExact D f p).words a b ↔
      RawWord.relation S (walkWord D p.val) a b := by
  simp [pathExact,RawExact.evaluate]

noncomputable def pathConstraints (f : DiagramHom D) (x y : V) :
    List (RawExact.NonemptyExact S (D.vertexSort x) (D.vertexSort y)) := by
  letI := pathFintype D x y
  exact Finset.univ.toList.map (pathExact D f)

include legal in
/-- C28-C29, with the disconnected (empty path family) case included by the
empty-family source primality law. No marked realization is assumed. -/
theorem choose_allowed_endpoint {G : Type t} [Group G] [∀ i, MulAction G (X i)]
    (H : HomogeneousSource S G) (laws : M.Calculus) (f : DiagramHom D) (x y : V) :
    ∃ (a : X (D.vertexSort x)) (b : X (D.vertexSort y)),
      (∀ p : (graph D).Path x y, RawWord.relation S (walkWord D p.val) a b) ∧
      M.allowed (S.colour a b) (bits x) (bits y) := by
  classical
  letI := pathFintype D x y
  let ds := pathConstraints D f x y
  have hNonempty : TRel.Nonempty (fun a b => ∀ d ∈ ds, RawExact.evaluate S d.words a b) := by
    refine ⟨f.point x,f.point y,?_⟩
    intro d hd
    obtain ⟨p,_,rfl⟩ := List.mem_map.mp hd
    exact (pathExact_relation D f p _ _).mpr (hom_realizes_walk D f p.val)
  have individual : ∀ d ∈ ds, ∃ a b, RawExact.evaluate S d.words a b ∧
      M.allowed (S.colour a b) (bits x) (bits y) := by
    intro d hd
    obtain ⟨p,_,rfl⟩ := List.mem_map.mp hd
    obtain ⟨a,b,hab,hm⟩ := (markedWalk D M bits legal p.val).allowed_output H laws
    rw [markedWalk_word] at hab
    exact ⟨a,b,(pathExact_relation D f p a b).mpr hab,hm⟩
  obtain ⟨a,b,hab,hm⟩ := laws.primality ds (bits x) (bits y)
    (legal.1 x) (legal.1 y) hNonempty individual
  refine ⟨a,b,?_,hm⟩
  intro p
  apply (pathExact_relation D f p a b).mp
  exact hab _ (List.mem_map.mpr ⟨p,by simp,rfl⟩)

end CCO.APCharacter.Completion
