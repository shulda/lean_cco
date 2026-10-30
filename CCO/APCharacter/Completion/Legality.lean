import CCO.APCharacter.Completion.FoldCoherence
import CCO.APCharacter.Masks
import CCO.StrongExact.PairEdgeExtension

/-! Local phase legality survives the two genuine completion operations,
and a terminal complete old diagram admits ONE global seed marking. -/
universe u v w z
namespace CCO.APCharacter.Completion
variable {ι : Type u} {X : ι → Type v} {S : AtomicSource.{u,v,w} ι X}
variable (M : MaskData S)

theorem real_none_same_bits {i j : ι} (a : X i) (b : X j) (ε η : Bit)
    (hn : S.colour a b = none) (ha : M.allowed (S.colour a b) ε η) : ε = η := by
  have hi : i = j := congrArg Sigma.fst ((S.colour_none_iff a b).mp hn)
  subst j
  rw [hn] at ha
  exact ((M.identity i ε η).mp ha).1

variable {V : Type z} (D : PartialDiagram S V) (bits : V → Bit)

theorem insertion_legal (legal : M.LocalLegal D bits)
    (x y : V) (hxy : x ≠ y) (a : S.Atom (D.vertexSort x) (D.vertexSort y))
    (allowed : M.allowed (some a) (bits x) (bits y)) :
    M.LocalLegal (D.withPair x y hxy a) bits := by
  classical
  refine ⟨legal.1,?_⟩
  intro p q hpq b hb
  by_cases hf : p = x ∧ q = y
  · rcases hf with ⟨rfl,rfl⟩
    have he : a = b := Option.some.inj ((D.withPair_specified p q hxy a).symm.trans hb)
    rwa [← he]
  · by_cases hr : p = y ∧ q = x
    · rcases hr with ⟨rfl,rfl⟩
      have hc := ((D.withPair q p hxy a).edge_reverse q p hxy a).mp
        (D.withPair_specified q p hxy a)
      have he : S.conv a = b := Option.some.inj (hc.symm.trans hb)
      rw [← he]
      exact (M.reverse a (bits q) (bits p)).mp allowed
    · rw [D.withPair_edge_of_other x y hxy a p q hpq hf hr] at hb
      exact legal.2 p q hpq b hb

/-- C34-C35: on the complete terminal old diagram EVERY original pair is
locally legal, including actual equality, so the accepted finite seed theorem
applies once to the whole finite point family. -/
theorem terminal_marking {V : Type (max u v)} (D : PartialDiagram S V)
    (bits : V → Bit) (legal : M.LocalLegal D bits)
    (complete : D.IsComplete) (seeds : M.FiniteSeedExtension) (f : DiagramHom D) :
    ∃ mark, M.GlobalMarking mark ∧ ∀ x, mark (f.image x) = bits x := by
  letI : Finite V := D.finite_type
  apply seeds D.vertexSort f.point bits legal.1
  intro x y
  by_cases hxy : x = y
  · subst y
    have hc : S.colour (f.point x) (f.point x) = none := (S.colour_none_iff _ _).mpr rfl
    rw [hc]
    exact (M.identity _ _ _).mpr ⟨rfl,legal.1 x⟩
  · obtain ⟨a,ha⟩ := complete x y hxy
    rw [f.preserves_edge x y hxy a ha]
    exact legal.2 x y hxy a ha

/-- C24/C31: bits on the literal representative carrier remain locally
legal, since every quotient edge has a coherent original-edge lift. -/
theorem fold_legal (f : DiagramHom D) (legal : M.LocalLegal D bits)
    (x y : V) (hxy : x ≠ y) (sameSort : D.vertexSort x = D.vertexSort y)
    (sameBits : bits x = bits y) (missing : D.edge x y hxy = none)
    (bound : IdentityBound D x y) :
    M.LocalLegal (foldDiagram D f x y hxy sameSort missing bound) (fun a => bits a.val) := by
  letI : Finite V := D.finite_type
  refine ⟨fun a => legal.1 a.val,?_⟩
  intro u v huv c hc
  let q := identify x y hxy
  let sort := fun a : Identified y => D.vertexSort a.val
  let typed := fun a => (identify_sorts x y hxy D sameSort a).symm
  let compatible := pushCompatible_of_edgeCoherent D f q sort typed
    (identify_edge_coherent D f x y hxy missing bound)
  obtain ⟨a,b,ha,hb,hab,hc'⟩ := pushDiagram_lift D f q sort typed compatible u v huv c hc
  obtain ⟨hne,d,hd⟩ := hab
  have hAllow : M.allowed (S.colour (f.point a) (f.point b)) (bits a) (bits b) := by
    rw [f.preserves_edge a b hne d hd]
    exact legal.2 a b hne d hd
  let AllowedPair := fun (p q : Sigma X) => M.allowed (S.colour p.2 q.2) (bits a) (bits b)
  have hAllow' : AllowedPair (f.image a) (f.image b) := hAllow
  rw [← pushedPoint_sigma D f q sort typed a u ha,
      ← pushedPoint_sigma D f q sort typed b v hb] at hAllow'
  change M.allowed (S.colour (pushedPoint D f q sort typed a u ha)
      (pushedPoint D f q sort typed b v hb)) (bits a) (bits b) at hAllow'
  rw [hc'] at hAllow'
  have haBits : bits a = bits u.val := by
    have h := identify_bits x y hxy bits sameBits a
    change bits (q a).val = bits a at h
    rw [ha] at h
    exact h.symm
  have hbBits : bits b = bits v.val := by
    have h := identify_bits x y hxy bits sameBits b
    change bits (q b).val = bits b at h
    rw [hb] at h
    exact h.symm
  rwa [haBits,hbBits] at hAllow'

end CCO.APCharacter.Completion
