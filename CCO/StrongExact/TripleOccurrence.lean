import CCO.StrongExact.TripleHom

/-!
# C09: three original exact menus occur iff all three PC supports hold

Every coordinate atom is realized in an injective completion of the SAME
finite private-word diagram. A supported old-colour triangle supplies
common roots for the three side families. SAP separates collisions while
retaining the chosen coordinate's diversity atom. The three formal roots
remain distinct for arbitrary repeated named sorts.
-/

universe u v w
namespace CCO.StrongExact
variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {i j k : ι}

/-- PC gives complete endpoint-survivor equality on every side of ONE
fixed seed diagram, using each of the three support inclusions. -/
theorem triple_survivor_eq_present_of_PC
    {G : Type*} [Group G] [∀ t : ι, MulAction G (X t)]
    (H : HomogeneousSource S G) (sap : AgeSAP S) (W : TripleWords S i j k)
    (x : X i) (y : X j) (z : X k) (seed : TripleLiteralLines S W x y z)
    (hPC : S.PC (present S W.left) (present S W.right) (present S W.across))
    (s : TripleSide) :
    (tripleDiagram S W x y z seed).survivor
      (.inl (tripleSideSource s)) (.inl (tripleSideTarget s))
      (tripleSideRoots_ne S W s) = present S (TripleWords.side S W s) := by
  apply Set.Subset.antisymm (triple_survivor_subset_present S H sap W x y z seed s)
  intro a ha
  cases s with
  | left =>
      obtain ⟨c,hc,d,hd,hTri⟩ := hPC.2.1 ha
      obtain ⟨x',z',y',hxz,hzy,hxy⟩ := hTri
      have hb : S.conv d ∈ present S W.right := hd
      have hyz := (S.colour_swap z' y' d).mp hzy
      let lines := TripleLiteralLines.of_membership S H sap W a (S.conv d) c
        ha hb hc x' y' z' hxy hyz hxz
      exact triple_lines_give_survivor S H sap W x y z seed
        x' y' z' lines .left a hxy
  | right =>
      obtain ⟨d,hd,c,hc,hTri⟩ := hPC.2.2 ha
      obtain ⟨y',x',z',hyx,hxz,hyz⟩ := hTri
      have hb : S.conv d ∈ present S W.left := hd
      have hxy := (S.colour_swap y' x' d).mp hyx
      let lines := TripleLiteralLines.of_membership S H sap W (S.conv d) a c
        hb ha hc x' y' z' hxy hyz hxz
      exact triple_lines_give_survivor S H sap W x y z seed
        x' y' z' lines .right a hyz
  | across =>
      obtain ⟨b,hb,c,hc,hTri⟩ := hPC.1 ha
      obtain ⟨x',y',z',hxy,hyz,hxz⟩ := hTri
      let lines := TripleLiteralLines.of_membership S H sap W b c a
        hb hc ha x' y' z' hxy hyz hxz
      exact triple_lines_give_survivor S H sap W x y z seed
        x' y' z' lines .across a hxz

/-- Occurrence as the full three endpoint-survivor menus of an actual
finite strongly completable private-word diagram. The three roots have
literal original sorts `(i,j,k)` and are distinct formal constructors. -/
def ThreeRootWordOccurrence (A : S.Menu i j) (B : S.Menu j k) (C : S.Menu i k) : Prop :=
  ∃ (W : TripleWords S i j k) (x : X i) (y : X j) (z : X k)
    (seed : TripleLiteralLines S W x y z),
    (tripleDiagram S W x y z seed).HasStrongCompletion ∧
    (tripleDiagram S W x y z seed).survivor
      (.inl .left) (.inl .middle) (tripleSideRoots_ne S W .left) = A ∧
    (tripleDiagram S W x y z seed).survivor
      (.inl .middle) (.inl .right) (tripleSideRoots_ne S W .right) = B ∧
    (tripleDiagram S W x y z seed).survivor
      (.inl .left) (.inl .right) (tripleSideRoots_ne S W .across) = C

/-- Necessity uses actual whole-diagram survivors, hence ALL three
PC coordinates, without SAP, CCO or exactness assumptions. -/
theorem threeRootWordOccurrence_PC
    {A : S.Menu i j} {B : S.Menu j k} {C : S.Menu i k}
    (h : ThreeRootWordOccurrence S A B C) : S.PC A B C := by
  obtain ⟨W,x,y,z,seed,_hCompletion,hA,hB,hC⟩ := h
  have hPC := (tripleDiagram S W x y z seed).survivor_PC
    (.inl .left) (.inl .middle) (.inl .right)
    (tripleSideRoots_ne S W .left) (tripleSideRoots_ne S W .right)
    (tripleSideRoots_ne S W .across)
  rw [hA,hB,hC] at hPC
  exact hPC

/-- Sufficiency constructs one actual original-colour diagram and
realizes every coordinate atom in its own injective completion. No
conditional theta, PC-completion or triangle-fullness provider is used. -/
theorem threeRootWordOccurrence_of_PC_of_SAP
    {G : Type*} [Group G] [∀ t : ι, MulAction G (X t)]
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {A : S.Menu i j} {B : S.Menu j k} {C : S.Menu i k}
    (hA : Exact S A) (hB : Exact S B) (hC : Exact S C)
    (hPC : S.PC A B C) : ThreeRootWordOccurrence S A B C := by
  classical
  obtain ⟨_hAn,as,hAs⟩ := hA
  obtain ⟨_hBn,bs,hBs⟩ := hB
  obtain ⟨hCn,cs,hCs⟩ := hC
  let W : TripleWords S i j k := ⟨as,bs,cs⟩
  have hLeft : present S W.left = A := hAs.symm
  have hRight : present S W.right = B := hBs.symm
  have hAcross : present S W.across = C := hCs.symm
  have hPC' : S.PC (present S W.left) (present S W.right) (present S W.across) := by
    rw [hLeft,hRight,hAcross]
    exact hPC
  have hNonempty : (present S W.across).Nonempty := by
    rw [hAcross]
    exact hCn
  obtain ⟨c,hc⟩ := hNonempty
  obtain ⟨a,ha,b,hb,hTri⟩ := hPC'.1 hc
  obtain ⟨x,y,z,hxy,hyz,hxz⟩ := hTri
  let seed := TripleLiteralLines.of_membership S H sap W a b c ha hb hc
    x y z hxy hyz hxz
  have hSurvivors := triple_survivor_eq_present_of_PC S H sap W x y z seed hPC'
  have hOccurs := triple_lines_give_survivor S H sap W x y z seed
    x y z seed .across c hxz
  obtain ⟨f,hf,_hColour⟩ := hOccurs
  exact ⟨W,x,y,z,seed,⟨f,hf⟩,
    (hSurvivors .left).trans hLeft,
    (hSurvivors .right).trans hRight,
    (hSurvivors .across).trans hAcross⟩

/-- The full C09 original exact-menu occurrence criterion, with
all three PC inclusions and full whole-diagram survivor domains. -/
theorem threeRootWordOccurrence_iff_PC_of_SAP
    {G : Type*} [Group G] [∀ t : ι, MulAction G (X t)]
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {A : S.Menu i j} {B : S.Menu j k} {C : S.Menu i k}
    (hA : Exact S A) (hB : Exact S B) (hC : Exact S C) :
    ThreeRootWordOccurrence S A B C ↔ S.PC A B C :=
  ⟨threeRootWordOccurrence_PC S,
    threeRootWordOccurrence_of_PC_of_SAP S H sap hA hB hC⟩

end CCO.StrongExact
