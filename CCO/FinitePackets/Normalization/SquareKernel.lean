import CCO.FinitePackets.Normalization.ThinBasic
import CCO.FinitePackets.Geometry.CoreWords
import CCO.FinitePackets.Geometry.Sigma

/-! C19/C22: the actual least equivalence containing the finite-packet
atom squares. Finite joins are represented products; each square closure
has an actual stabilized positive even word. Thus their product is one
RAW word, with the empty diversity list giving the literal empty word.
No CCO, SAP, exact-product theorem, or quotient source is used. -/
universe v w t
namespace CCO.FinitePackets.Normalization
open CCO.RealHull.Geometry CCO.RealHull.Canonical CCO.ParityHasse.Original
open CCO.FinitePackets.Geometry
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))

noncomputable def packetAtoms (F : ColourEq S ()) : Finset (Atom S) := by
  classical
  letI := S.finiteAtom () ()
  exact Finset.univ.filter (AtomBelow S F)

@[simp] theorem mem_packetAtoms (F : ColourEq S ()) (a : Atom S) :
    a ∈ packetAtoms S F ↔ AtomBelow S F a := by
  classical
  simp only [packetAtoms,Finset.mem_filter,Finset.mem_univ,true_and]

def squareClosure (a : Atom S) : ColourEq S () := supportEquiv S (evenSupport S a)

theorem atom_square_le_closure (a : Atom S) (x z : M)
    (h : RawSymmetric.compose (S.atomRel a) (S.atomRel a) x z) :
    squareClosure S a x z := by
  obtain ⟨y,hxy,hyz⟩ := h
  change col S x z ∈ plus S (evenSupport S a).val
  cases hc : col S x z with
  | none => exact none_mem_plus S _
  | some b =>
    exact (some_mem_plus S _ b).mpr
      (subset_generated S (square S a) ⟨x,y,z,hxy,hyz,hc⟩)

theorem squareClosure_le {a : Atom S} {F : ColourEq S ()} (ha : AtomBelow S F a) :
    squareClosure S a ≤ F := by
  apply (supportEquiv_le_iff S (evenSupport S a) F).mpr
  apply generated_le S (square S a) (equivalenceSupport S F)
  rintro b ⟨x,y,z,hxy,hyz,hxz⟩
  exact ⟨x,z,F.val.trans (ha x y hxy) (ha y z hyz),hxz⟩

theorem squareClosure_eq_bot_of_thin {a : Atom S} (ha : ThinColour S (some a)) :
    squareClosure S a = ⊥ := by
  apply le_antisymm
  · apply (supportEquiv_le_iff S (evenSupport S a) ⊥).mpr
    apply generated_le S (square S a) (equivalenceSupport S ⊥)
    rintro b ⟨x,y,z,hxy,hyz,hxz⟩
    have he : x = z := (ha y).unique ((col_symm S y x).trans hxy) hyz
    exact ⟨x,z,he,hxz⟩
  · exact bot_le

variable {G : Type t} [Group G] [MulAction G M]
variable (H : HomogeneousSource S G)

noncomputable def squareJoin (s : Finset (Atom S)) : ColourEq S () :=
  letI := ColourEq.lattice S H (i := ())
  s.sup (squareClosure S)

noncomputable def squareKernel (F : ColourEq S ()) : ColourEq S () :=
  squareJoin S H (packetAtoms S F)

theorem squareJoin_word (s : Finset (Atom S)) :
    ∃ word : RawWord S () (), RawWord.relation S word = (squareJoin S H s).val.r := by
  classical
  letI := ColourEq.lattice S H (i := ())
  induction s using Finset.induction_on with
  | empty => exact ⟨.nil (),rfl⟩
  | @insert a s has ih =>
    obtain ⟨n,hn⟩ := exists_positive_even_word S H a
    obtain ⟨word,hw⟩ := ih
    refine ⟨RawWord.append S (positiveEvenWord S a n) word,?_⟩
    rw [RawWord.relation_append,hn,hw]
    have hj : squareJoin S H (insert a s) = squareClosure S a ⊔ squareJoin S H s :=
      Finset.sup_insert
    rw [hj]
    funext x y
    exact propext (sup_relation_iff S H (squareClosure S a) (squareJoin S H s) x y).symm

theorem squareKernel_le (F : ColourEq S ()) : squareKernel S H F ≤ F := by
  classical
  letI := ColourEq.lattice S H (i := ())
  apply Finset.sup_le
  intro a ha
  exact squareClosure_le S ((mem_packetAtoms S F a).mp ha)

theorem atom_square_le_kernel {F : ColourEq S ()} {a : Atom S} (ha : AtomBelow S F a)
    (x z : M) (h : RawSymmetric.compose (S.atomRel a) (S.atomRel a) x z) :
    squareKernel S H F x z := by
  classical
  letI := ColourEq.lattice S H (i := ())
  have he : squareClosure S a ≤ squareKernel S H F :=
    Finset.le_sup (f := squareClosure S) ((mem_packetAtoms S F a).mpr ha)
  exact he (atom_square_le_closure S a x z h)

theorem fullColour_square_le_kernel {F : ColourEq S ()} {c : FullColour S}
    (hc : FullColourBelow S F c) (x z : M)
    (h : ∃ y, col S x y = c ∧ col S y z = c) : squareKernel S H F x z := by
  cases c with
  | none =>
    obtain ⟨y,hxy,hyz⟩ := h
    exact ((col_none S x y).mp hxy |>.trans ((col_none S y z).mp hyz)) ▸
      (squareKernel S H F).val.refl x
  | some a => exact atom_square_le_kernel S H hc x z h

theorem squareKernel_finite (F : ColourEq S ()) (hF : FiniteIndex S ⊥ F) :
    FiniteIndex S ⊥ (squareKernel S H F) :=
  finiteIndex_lower S (squareKernel_le S H F) hF

noncomputable def squareKernelWord (F : ColourEq S ()) : RawWord S () () :=
  Classical.choose (squareJoin_word S H (packetAtoms S F))

theorem squareKernelWord_relation (F : ColourEq S ()) :
    RawWord.relation S (squareKernelWord S H F) = (squareKernel S H F).val.r :=
  Classical.choose_spec (squareJoin_word S H (packetAtoms S F))

noncomputable def squareKernelExact (F : ColourEq S ()) : RawExact.NonemptyExact S () () := by
  refine ⟨[squareKernelWord S H F],?_⟩
  obtain ⟨x⟩ := S.nonemptySort ()
  refine ⟨x,x,?_⟩
  intro word hw
  have he : word = squareKernelWord S H F := List.mem_singleton.mp hw
  subst word
  exact (squareKernelWord_relation S H F).symm ▸ (squareKernel S H F).val.refl x

theorem squareKernelExact_represents (F : ColourEq S ()) :
    RawExact.evaluate S (squareKernelExact S H F).words = (squareKernel S H F).val.r := by
  funext x y
  apply propext
  change (∀ word ∈ [squareKernelWord S H F], RawWord.relation S word x y) ↔ _
  simp only [List.mem_singleton,forall_eq,squareKernelWord_relation S H F]

theorem squareKernel_eq_bot_of_thin (F : ColourEq S ()) (hthin : ThinBottom S F) :
    squareKernel S H F = ⊥ := by
  classical
  letI := ColourEq.lattice S H (i := ())
  apply le_antisymm
  · apply Finset.sup_le
    intro a ha
    exact le_of_eq (squareClosure_eq_bot_of_thin S
      (hthin (some a) ((mem_packetAtoms S F a).mp ha)))
  · exact bot_le

theorem empty_diversity_kernel (F : ColourEq S ()) (he : packetAtoms S F = ∅) :
    squareKernel S H F = ⊥ ∧
    RawWord.relation S (.nil ()) = (squareKernel S H F).val.r := by
  have hk : squareKernel S H F = ⊥ := by
    unfold squareKernel
    rw [he]
    rfl
  exact ⟨hk,by rw [hk]; rfl⟩

theorem squareKernel_nonidentity_of_nonthin (F : ColourEq S ())
    {a : Atom S} (ha : AtomBelow S F a) (hnt : ¬ ThinColour S (some a)) :
    ⊥ < squareKernel S H F := by
  have hn : squareKernel S H F ≠ ⊥ := by
    intro he
    apply hnt
    intro x
    obtain ⟨y,hy⟩ := colour_serial S H (some a) x
    refine ⟨y,hy,?_⟩
    intro z hz
    have hzy := atom_square_le_kernel S H ha z y
      ⟨x,(col_symm S z x).trans hz,hy⟩
    rw [he] at hzy
    exact hzy
  exact lt_of_le_of_ne bot_le (Ne.symm hn)

end CCO.FinitePackets.Normalization
