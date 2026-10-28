import CCO.RealClosure.Bounds.Examples.PhasePackets
import CCO.ExactCRT.ExactLattice

/-! Every actual RAW word has one endpoint phase difference. A proper
relation containing equality AND the thin flip cannot be full RAW exact;
the empty restriction family is handled separately as actual Top. -/
namespace CCO.RealClosure.Bounds.Examples.Phase
open ParityHasse.Original RawExact

def wordPhase {i j : Unit} : RawWord source i j → Bool
  | .nil _ => false
  | .identity tail => wordPhase tail
  | .atom a tail => a.val.2.2 ^^ wordPhase tail

theorem word_relation_phase {i j : Unit} (w : RawWord source i j) (x y : Point)
    (h : RawWord.relation source w x y) : (phase x ^^ phase y) = wordPhase w := by
  induction w generalizing x with
  | nil i =>
    change x = y at h
    subst y
    exact Bool.xor_self _
  | identity tail ih => exact ih x h
  | @atom i j k a tail ih =>
    obtain ⟨z,hxz,hzy⟩ := h
    have ha : (phase x ^^ phase z) = a.val.2.2 :=
      congrArg (fun p : Pattern => p.2.2) ((colour_some x z a).mp hxz)
    change (phase x ^^ phase y) = (a.val.2.2 ^^ wordPhase tail)
    calc
      _ = ((phase x ^^ phase z) ^^ (phase z ^^ phase y)) := by
        cases phase x <;> cases phase z <;> cases phase y <;> rfl
      _ = _ := by rw [ha,ih z hzy]

def origin : Point := (0,0,false)
def flipOrigin : Point := (0,0,true)

theorem proper_flip_not_exact (E : ColourEq source ())
    (hproper : ∃ x y : Point, ¬ E x y) (hflip : E origin flipOrigin) :
    ¬ ExactCRT.IsExactEq source (i := ()) E.val := by
  rintro ⟨D,hD⟩
  cases hp : D.words with
  | nil =>
    obtain ⟨x,y,hxy⟩ := hproper
    apply hxy
    rw [← hD,hp,evaluate_nil]
    trivial
  | cons word rest =>
    have he0 : evaluate source D.words origin origin := by rw [hD]
    have he1 : evaluate source D.words origin flipOrigin := by rw [hD]; exact hflip
    have hm : word ∈ D.words := by rw [hp]; exact List.mem_cons_self
    have h0 := word_relation_phase word origin origin (he0 word hm)
    have h1 := word_relation_phase word origin flipOrigin (he1 word hm)
    change false = wordPhase word at h0
    change true = wordPhase word at h1
    exact Bool.false_ne_true (h0.trans h1.symm)

def rowEq : ColourEq source () :=
  ⟨⟨fun x y => row x = row y,⟨fun _ => rfl,Eq.symm,Eq.trans⟩⟩,
    fun _ _ _ _ hc => (coordinates_of_colour_eq hc).1⟩
def columnEq : ColourEq source () :=
  ⟨⟨fun x y => column x = column y,⟨fun _ => rfl,Eq.symm,Eq.trans⟩⟩,
    fun _ _ _ _ hc => (coordinates_of_colour_eq hc).2.1⟩

theorem packet_not_exact : ¬ ExactCRT.IsExactEq source (i := ()) packetEq.val :=
  proper_flip_not_exact packetEq ⟨origin,(1,0,false),by change ¬ ((0:ℕ)=1 ∧ (0:ℕ)=0); decide⟩ ⟨rfl,rfl⟩

theorem finitePacket_not_exact :
    ¬ ExactCRT.IsExactEq source (i := ()) (finitePacket source homogeneous).val := by
  rw [finitePacket_eq]
  exact packet_not_exact

theorem row_not_exact : ¬ ExactCRT.IsExactEq source (i := ()) rowEq.val :=
  proper_flip_not_exact rowEq ⟨origin,(1,0,false),by change ¬ ((0:ℕ)=1); decide⟩ rfl

theorem column_not_exact : ¬ ExactCRT.IsExactEq source (i := ()) columnEq.val :=
  proper_flip_not_exact columnEq ⟨origin,(0,1,false),by change ¬ ((0:ℕ)=1); decide⟩ rfl
end CCO.RealClosure.Bounds.Examples.Phase
