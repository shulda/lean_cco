# Finite owner providers and full fibre-product actions — proof notes

Source `490c3f36d85db5a0b3ced0598e6c431825254ec5`. These are mathematical
proof expansions for OTHER receiving Lean projects. No Lean declarations
or human TeX were changed. The complete local contracts, DAG, source hashes
and export map are in `module.json`; that graph validates bookkeeping,
not mathematical truth.

## N00: Scope, quantified inputs and action criterion

This module covers exactly six numbered source results: the generic
finite-base lemma and its exact corollary, the standalone prescribed-owner
point lemma, and owner_master/01–03. The simultaneous master in 04 and
rooted ACF/rank induction are consumers, not exports of this module.
The actual source need not have SAP or NR2. No arbitrary owner-naming
homogeneity or finite-kernel width-two premise is used.

The contracts are branch-specific quantified theorems, not a conjunction
of all A-nodes. The generic finite-base theorem takes ambient lifts as an
argument; the exact-source instance DISCHARGES that argument using joint
lifting. Likewise the abstract product theorem takes the full group
identity as an argument, and the actual fine-coloured theorem proves
one valid instance of that argument. Applying a generic theorem does not
leave its now-constructed argument as an extra unproved source premise.

The largest finite-packet construction is REUSED from finite_packets C03
(I05); it is not a second foundational export. Actual nested mixed,
countable joint lifting and exact fine-colour meet are I01–I03 from RAW.
Ordinary EPPA of the current source is a conditional input A02. If Q was
itself obtained by an exact quotient, first supply the prepared full
exact-quotient source inheritance theorem; do not silently treat arbitrary
quotients as new standing sources.

For the group branch, I04 is the already assigned shared B001 export,
not a duplicate export. If pi:Y->B is onto, Y nonempty, equivariant for
rho:K->Gamma, then onto rho plus fibre-transitive kernel is equivalent to
all prescribed point lifts. In one direction lift gamma to k0 and correct
k0*x to y by an element of ker(rho). Conversely choose x, choose y above
gamma*pi(x), and apply point lifting to prove onto; use gamma=1 for the
kernel. No faithfulness, finiteness or section is required. All empty
actual systems are handled directly in N11.

Node firewalls separate generic finite-base, finite packets, abstract
point transfer, actual fine products and abstract product consumers.
Only the exact ambient-lift instance retains countability. The nested
product target does not need C's prescribed-point property; the EPPA
consumer needs neither D's T-fibre property nor C's point property,
because it has its separate stronger-on-input partial-map extension rule.

## N01: Recognizable quotients and generic finite-base restriction

D01–D04 and C01–C03 use an actual quotient whose kernel equality and
quotient pair colours are recognizable in finite induced old structures.
For an induced automorphism beta of C, define its quotient value using a
representative. Kernel preservation makes this independent; beta inverse
makes the quotient map bijective. For any quotient pair choose two
representatives: the pullback colour is an old-colour union, preserved
by beta in both directions. Thus the descended map is an induced
quotient automorphism. It is uniquely determined when C maps onto the
quotient image, and composition descends to composition. The same
argument for a partial induced map gives a partial quotient isomorphism
on the actual projected domain, with injectivity from kernel reflection.
Mere ambient invariance without finite colour recognition is insufficient.

If finite induced T subset X and Age(X) has ordinary EPPA, choose an
abstract finite EPPA extension C* in Age(X), including an embedding of T.
Choose any embedding e:C*->X. On e(T), the inverse of the restriction
e|T, followed by the given inclusion T->X, is a finite induced partial
isomorphism of X. Homogeneity extends it to h in Aut(X). Then h(e(C*))
is an ambient finite induced EPPA witness containing the originally given
T pointwise. Transport all extension automorphisms by this isomorphism.

This establishes the line “realised over A* by homogeneity” without an
amalgamation or free realization assumption. It also shows that one
ordinary EPPA witness simultaneously accommodates all partial
automorphisms of T; only finitely many chosen ones are subsequently used.

This is the expansion of `lem:finite-base`. Let X be homogeneous, with
the stated finite fine relational structure. Let pi:X->T be an actual
invariant quotient whose equality and pair colours are determined by
the fine pair colours, so every automorphism of any finite induced
substructure preserves the restricted owner-equivalence relation. Assume
ordinary EPPA for Age(X). Let B finite, A finite over B, and let R be
any finite list or set of requests (p_r,gamma_r) on A. Assume for each r
an actual ambient g_r in Aut(X) extending p_r and inducing gamma_r on
every owner in B. This is an explicit premise in this general lemma.

1. Choose one s_b in pi^{-1}(b) for every b in B, and put
   S=A union {s_b:b in B}. Thus S is finite, lies over B and meets
   every owner. If B=empty, then A=S=empty and one can return W=empty
   immediately; all requests are the empty map with the unique empty
   owner permutation. No EPPA call is needed in that case.
2. Form A*=S union union_r g_r(S). It is finite and lies over B because
   g_r induces gamma_r on B. For every r, u_r=g_r|S has its entire
   domain and range in A*, so it is a partial automorphism of A*.
   In particular it contains every prescribed point of dom(p_r).
3. Use N01 and ordinary EPPA to get finite induced C subset X containing
   A*, and beta_r in Aut(C) extending u_r for all r. No coherence or
   relations between the different beta_r are imposed.
4. Put W=C intersect pi^{-1}(B). It contains S and hence A and one
   representative of each owner. Thus pi(W)=B, independently of the
   requests and even if the request family is empty.
5. Fix r, x in W and b=pi(x). Both x and s_b lie in C and are in the
   same owner class. Since beta_r preserves the restricted owner
   equivalence, beta_r(x) and beta_r(s_b) have the same owner. But
   beta_r(s_b)=g_r(s_b), whose owner is gamma_r(b). Thus
   pi(beta_r(x))=gamma_r(pi(x)) belongs to B. Hence beta_r(W) subset W.
6. Restrict beta_r to W. This restriction is injective on finite W,
   hence bijective onto W, and is an induced automorphism. It extends
   p_r and has the prescribed owner action on all B. Its inverse need
   not have been independently selected.

All steps also work for an empty request family. Empty-domain requests
with arbitrary gamma_r are substantive when B is nonempty: the values
on the chosen representatives s_b encode the whole owner action. Merely
extending p_r by EPPA, without adjoining g_r(S), would not do this.

## N02: Genuine joint maps discharge the ambient-lift premise

This is the nontrivial discharge of the previous ambient-lift premise.
Take any finite induced T subset pi^{-1}(B), any partial automorphism
p of T, and any gamma in Aut(B) satisfying compatibility. Display all
points of dom(p) in the real sort and EVERY owner of B in the actual
E-quotient sort. Define f to be p on real points and gamma on B.

For E!=Id these are distinct tagged sorts, so injectivity within each
sort suffices. If E=Id and the quotient sort is identified with Q as in
the imported theorem, all real points lie in B and compatibility says
p(x)=gamma(x) on dom(p). Thus the union is well defined and is just the
finite map gamma on B. This identity-quotient edge case needs no duplicate
Id sort or extra lift assumption.

For general E check all pair types:

* Real-real pair orbitals are fine atomic colours and are preserved by p.
* Owner-owner pair orbitals are precisely the named actual colours in B
  and are preserved by gamma, including owner equality.
* For real x in dom(p) and owner c in B, the mixed orbital is determined
  by the owner-owner orbital of (pi(x),c). Indeed its pullback for an old
  atom a is Id;a;E=a;E=E;a;E, using `lem:nested-mixed`. Since pi(x)
  and c BOTH lie in the domain B of gamma, compatibility and gamma's
  pair-colour preservation give preservation of this mixed orbital.
  Reverse ordered pairs are covered by converses. Logical equality and
  membership (x belongs to c) are included, not suppressed.

The map f is therefore a genuine partial isomorphism of the COMPLETE
joint real/exact-owner orbital structure. `thm:typed-joint-exact-lifting`
or its one-sort specialization supplies one original g in Aut(Q) that
extends p and induces exactly gamma on every displayed owner of B.
The same proof covers p=empty, in which case there are no mixed pairs.

This application uses countability from the current joint-lifting
provider. It does not infer that gamma already belongs to an ambient
image, or select lifts coherently. Compatibility only on a smaller
overlap would be insufficient: coverage of every pi(x) by gamma is
essential and holds because gamma has domain all B.

Imported human-expanded providers are `raw_exact` C17 (nested mixed)
and C21/C23 (joint lifting). Their prepared proof route is exact balls
and countable back-and-forth with persistent quotient anchors; neither
ordinary EPPA nor rooted ACF is an input to that route.

Apply N01 to the finitely many lifts just constructed. This proves cor:fixed-base (C05) for ANY finite induced B, including empty B and B not closed under F_O. The packet-closed/nonempty A07 premise belongs only to the later owner provider. In particular every empty-real request may still prescribe an arbitrary automorphism on the ENTIRE B.

## N03: Greatest finite packets and their actual owner images

C06 instantiates finite_packets C03 (I05) at Q and its canonical owner source. The latter is transitive under the induced original action; all its named actual pair orbitals are symmetric. Every full Aut(O)-invariant relation is also invariant under that transitive induced action and therefore is a union of the finitely many named pair orbitals. This supplies exactly the elementary finite symmetric relation framework of the imported packet construction; no homogeneity, CCO or countability argument is needed for this isolated step. F_Q and F_O are not assumed exact.

Let F=F_Q. In the original symmetric represented algebra all invariant
relations commute, so F join E=F;E=E;F. The quotient relation
R=(F join E)/E is well defined on O. For any fixed x in Q, the entire
R-class of pi(x) is exactly pi(F[x]):

* If z in F[x], then pi(z) R pi(x).
* If pi(y) R pi(x), use F;E to find z with x F z E y. Thus
  pi(y)=pi(z), with z in F[x].

Consequently every R-class is finite. Its invariance under the full
structural Aut(O), rather than merely the induced Aut(Q)-action, deserves
explicit justification: its pullback is an E-saturated union of original
pair orbitals. It therefore descends to a union of the named actual owner
pair colours. Every structural automorphism of O preserves that union.
Thus R is an invariant finite-class owner equivalence, whence R<=F_O.
This argument does not require a global lift of an owner automorphism.

For every t with pi(t) in B and every z F_Q t, one gets
pi(z) F_O pi(t), hence pi(z) in B by B-closedness. Therefore
F_Q[T] subset pi^{-1}(B) for every T subset pi^{-1}(B).
If T is finite, its full closure is finite. If pi(T)=B, the full closure
still has image exactly B, since it contains T. In particular the two
closure operations used later do not accidentally add new owners.

Inputs: symmetric commutation (`raw_exact` C04), actual orbital descent
(`raw_exact` C14, or its elementary group-action part), and greatest
finite-class equivalences (`finite_packets` C03). No exactness of F is
used. Exactness of E is not needed for this isolated calculation once the
actual owner orbital language and F_O are available.

## N04: All finite requests, packet closure and generated orbit trimming

1. Pick representatives S={s_b:b in B} and let
   A+=F_Q[A union S]. By N03 this is finite, lies over B, is fully
   F_Q-closed, contains A and meets every owner. B!=empty makes A+
   nonempty even when A=empty.
2. Let R be ALL compatible pairs (p,gamma), with p an arbitrary partial
   automorphism of A+ and gamma in Aut(B). This is finite because the
   set of partial injective self-maps of a finite set is finite and
   Aut(B) is finite. Explicitly it includes every empty-domain request
   (empty,gamma) and every singleton a->a' with
   gamma(pi(a))=pi(a'). All these singleton maps are fine partial
   automorphisms because the one-sort source is transitive. A typed or
   unary-enriched variant would have to retain the corresponding
   singleton partial-isomorphism hypothesis; transitivity is used here.
3. N02 gives an ambient lift for each member of this finite family.
   Apply N01 with input A+ to obtain a common finite D0 over B extending
   every request. D0 contains A+ and has pi(D0)=B. For each r choose
   one beta_r in Aut(D0) with its prescribed action.
4. Put D1=F_Q[D0]. It is finite, fully packet-closed and has image B
   by N03. Extend each beta_r, which is a partial automorphism of the
   current source Q on its complete finite domain D0, to h_r in
   Aut(Q) by homogeneity. Because h_r(D0)=D0 and F_Q is invariant,
   h_r(D1)=D1. Since D0 meets every owner, h_r still induces exactly
   gamma_r on all B, not only on the original request's real domain.
5. Let alpha_r=h_r|D1 and G0=<alpha_r:r in R> inside Aut(D1).
   This group is finite since D1 is finite. Do not claim the group
   generated by the ambient h_r is finite. Every G0 element respects
   the owner action on B and sends complete ambient F_Q-classes in D1
   to complete ambient F_Q-classes. The latter assertion follows either
   by composing the h_r lifts, or from the fact each generator and its
   inverse is the restriction of such a lift.
6. Set D=union_{g in G0} g(A+). This is finite, contains A+, is induced,
   and is G0-invariant since left multiplication permutes G0. Each
   g(A+) is a union of complete ambient F_Q-classes by step 5. Thus D
   is FULL-F_Q-closed, not merely a union of restricted classes.
   It lies over B, and its image equals B because A+ already meets
   every owner.
7. Every alpha_r restricts to an automorphism of D extending the same
   p_r and retaining its full gamma_r component. Thus the resulting D
   extends every request on A+, and a fortiori every request on A:
   any partial automorphism of A is a partial automorphism of A+
   with the identical domain, range and values. No extension to an
   automorphism of A+ is asserted or needed.

The full D1 alone need not have the orbit-reaching-A+ property needed in
the next step. Trimming to G0 A+ gives it explicitly while preserving
every selected extension and full-packet closedness. For each x in D,
write x=g(a), a in A+, g in G0. Then g^{-1}|D sends x into A+.

## N05: Pure point conjugation and finite owner-provider assembly

Use the following elementary lemma independently of any ACF notion.
Let rho:Aut(D)->Aut(B) be the induced homomorphism. Suppose nonempty
A0 subset D meets every Aut(D)-orbit in D. Suppose for any a,a' in A0
and delta in Aut(B) with delta(pi(a))=pi(a'), there is k in Aut(D)
with k(a)=a' and rho(k)=delta. Then for all x,y in D and gamma in
Aut(B) with gamma(pi(x))=pi(y), a beta with beta(x)=y and
rho(beta)=gamma exists.

Choose g,h in Aut(D) with a=g(x) in A0 and a'=h(y) in A0.
With composition acting rightmost first, set

    delta = rho(h) * gamma * rho(g)^{-1}.

Then delta(pi(a))=rho(h)(gamma(pi(x)))=pi(h(y))=pi(a').
Select k for this singleton request and set beta=h^{-1}*k*g.
Its point value is beta(x)=y and its owner component is

    rho(beta)=rho(h)^{-1} * delta * rho(g)=gamma.

For the provider take A0=A+, use the orbit argument at the end of N04,
and the singleton requests retained from N04. The induced quotient-action construction of N01 supplies rho. This
proves conclusion (2) for every point introduced by the EPPA construction
and orbit closure, with exactly the requested owner action.

The pure conjugation proof above is C12 and uses no source premises. Its separate actual-source packet consumer is C30: an automorphism beta of finite induced D extends ambiently by homogeneity;
therefore it preserves the restricted invariant relation F_Q. When D is
fully F_Q-closed, this gives beta(F_Q[x])=F_Q[beta(x)] as complete ambient
packets contained in D. Hence beta sends every subset of F_Q[x] into
F_Q[y] when beta(x)=y. For the standalone point lemma without full packet
closedness the meaningful version is a subset of F_Q[x] intersect D;
beta is only defined on D. This is a minor domain clarification for the
last sentence of `lem:acf-point-homogeneity`, not a provider gap.

Surjectivity rho_D follows already from the retained empty-real request
(empty,gamma) for each gamma in Aut(B). It also follows from point
homogeneity and pi(D)=B, but the empty-real request route is direct.
For x,y in one fibre use gamma=identity in N05; the resulting beta
belongs to ker(rho_D). Thus the kernel is transitive on every fibre.
No faithfulness, free fibre action, product decomposition, independent
packet permutations or semidirect-product splitting follows.

A=empty is explicitly allowed: representatives of nonempty B make A+
nonempty, and all later arguments apply. Empty dom(p) is always allowed,
including owner motions with no real constraint. E=Id is handled in N02;
E=Top has a single owner and reduces the owner component to the trivial
group. F_Q=Id makes full-packet closure do nothing. Finite Q causes no
problem; F_Q=Top then forces A+=Q once A+ is nonempty, and the closure
steps remain finite. A one-element B is permitted. If one wanted to
remove nonemptiness of B from the provider statement, B=empty forces
A=empty and D=empty is the direct boundary case; the nonempty point
lemma must simply be skipped. No theorem strengthening is required for
the stated source result.

## N06: Set realization and the forward quotient action

Every invariant binary relation is a union of symmetric original orbitals. Products of invariant relations are invariant and hence symmetric. Therefore (R;S)^op=S;R=R;S for all invariant R,S. In particular E;J=J;E. The product E;J is an equivalence containing E and J and contained in any equivalence containing them; consequently E;J=E∨J=H.

Define q([x]_K)=([x]_E,[x]_J). It is well-defined and injective because equality of both coordinates is precisely E∩J-equivalence. Its image lies in the fibre product. If an E-class e and a J-class j have the same H-image, choose representatives u∈e,v∈j. Then uHv means u(E;J)v, so there is z with uEzJv. Thus z∈e∩j and q([z]_K)=(e,j). This is surjectivity. No fine-colour assertion has yet been made.

For a finite induced D⊆X/E and C⊆X/J with common image B⊆X/H, both onto B, the inverse image W=q^(-1)(D×_B C) is a finite induced structure. Every d∈D has an owner b and some c∈C over b; hence W→D is onto, and symmetrically W→C is onto.

#### 3.2 Actual orbit blocks, not arbitrary quotient colour declarations

Let G=Aut(X). For any equivariant quotient maps α:X→X/E and β:X→X/J and any actual G-orbital Θ represented by (α(u),β(v)), the inverse image of Θ equals E;a;J, where a=G·(u,v).

Indeed, if (α(x),β(y)) is in that orbital, take g∈G with gα(u)=α(x) and gβ(v)=β(y). Then xEgu, (gu,gv)∈a, and gvJy, so (x,y)∈E;a;J. Conversely changing representatives within E,J does not change the output pair, and every a-pair projects to Θ. For a same quotient this gives E;a;E. Different old a can give the same block; the distinct blocks, rather than arbitrarily selected representatives, are exactly the actual quotient orbitals and partition X².

On X/K, the E-coordinate kernel is equality of E-images. It is induced by the invariant equivalence E/K. Every actual G-orbital of X/K either lies wholly inside this equivalence or is disjoint from it; hence the kernel is a union of named fine colours. Every E-quotient pair orbital similarly pulls back to a union of fine K-orbitals. These assertions restrict to any finite induced W and its coordinate image D; no finite homogeneity theorem is required.

For f∈Aut(W), define g_D(d)=p_D(f(w)) using any w with p_D(w)=d. If w,w′ project to the same d, their pair belongs to the named kernel union; f preserves that union, so the definition is independent of w. Apply the same argument to f^(-1) to obtain bijectivity. For d,d′ choose arbitrary lifts w,w′. If the D-pair has a given quotient colour, its pullback is a union of W-fine colours. The pair (w,w′) belongs to that union; f preserves it; hence (g_Dd,g_Dd′) has the same D-colour. Thus g_D∈Aut(D). The identical proof gives g_C∈Aut(C).

Their induced B-maps agree: for every w, r_Dg_Dp_D(w)=r_Cg_Cp_C(w), because f(w) lies in W. Since W→B is onto, they agree on all B. This also explicitly proves that the action homomorphisms Aut(D)→Aut(B) and Aut(C)→Aut(B) exist: apply the same named-kernel and named-colour argument to r_D,r_C. These homomorphisms need not be onto.

Coordinate restriction is a group homomorphism. It is injective because a point of W is uniquely determined by its D and C coordinates.

## N07: Equality-inclusive fine-colour recovery and the natural group isomorphism

K is a nonempty full exact relation because E∩J contains equality. The old atom a is a nonempty one-letter exact word (including a=Id). Commutation and equivalence idempotence give

E;a;E=E;a, J;a;J=J;a, K;a;K=K;a.

The imported **nonempty** exact meet-product law applies to E∩J and a, giving

(E∩J);a=(E;a)∩(J;a).

Thus the exact fine-colour identity holds. Each saturation contains a, so the intersections appearing here are nonempty; no invalid distribution over an empty represented intersection is used.

Take two pairs of K-classes with equal E-projected and J-projected pair colours. Choose an old atom a representing the first fine K-pair. Representatives of the second pair lie in E;a;E and J;a;J, hence in K;a;K, and therefore have the same fine K-pair orbital. This works when either coarse pair is equal and when the fine pair is equal. Quotient equality is a genuine colour whose pullback is the kernel equivalence, and must not be deleted as “diversity”.

Let (g,h)∈Aut(D)×Aut(C) have the same induced B-action δ. The coordinate map F(d,c)=(gd,hc) sends W into itself because r_D(gd)=δ(r_Dd)=δ(r_Cc)=r_C(hc). Its inverse uses (g^(-1),h^(-1)); **fullness** of W ensures that every resulting compatible pair is present.

For any w,w′∈W choose an old atom a representing their fine K-colour. The E-coordinate pair has pullback block E;a;E and the J-coordinate pair has block J;a;J. Since g,h preserve those coordinate colours, representatives of Fw,Fw′ belong to their intersection, equal to K;a;K by the exact readout in N07. Thus F preserves the original fine colour. The same applies to equality; no independent recolouring is performed. Hence F∈Aut(W).

The two constructions are inverse and canonical, yielding

Aut(W) ≅ Aut(D) ×_(Aut(B)) Aut(C).

The equality notation used later is an identification through this canonical action, not an assertion that all quotient automorphism groups are ambient group quotients with chosen global lifts.

## N08: Abstract nonnested target action

Let K act on nonempty Y, Γ act on B, π:Y→B be onto and equivariant for an explicit homomorphism ρ:K→Γ. The following are equivalent:

1. ρ is onto and kerρ acts transitively on each π-fibre.
2. Given x,y∈Y and γ∈Γ with γπ(x)=π(y), some k∈K satisfies ρ(k)=γ and kx=y.

Proof 1⇒2: choose k₀ lifting γ. Then k₀x and y have the same π-image, so choose h∈kerρ taking k₀x to y and take hk₀. Proof 2⇒1: given γ choose any x and any y over γπ(x); condition 2 lifts γ. Setting γ=1 gives fibre transitivity. Faithfulness, finiteness, exactness and splitting are unnecessary. Nonemptiness is used only in the choice of x; empty actual finite quotient systems are handled separately.

A useful equivalent stabilizer form of 2 is: each γ mapping π(x) to π(y) has a lift in the transporter K_(x→y). In particular K_x→Γ_(πx) is onto. This last stabilizer assertion does **not** follow merely from transitivity of K on all Y plus onto ρ.

## 6. Arbitrary target T, with no nesting between T and O

Retain actual maps r_D:D→O,r_C:C→O and W=D×_O C, all onto, and the actual group identity FK. Let t:D→T be an onto actual quotient with an induced homomorphism τ:Aut(D)→Aut(T). The crucial hypotheses are:

* τ is onto and kerτ is transitive on every t-fibre;
* C has prescribed-owner point lifting over O (condition 2 of the action criterion in N00).

There is **no** assumption that t determines r_D, or conversely. FK ensures every W-automorphism has a D-component, so W→D→T carries a well-defined induced group action.

Assume nonempty. Given w=(d,x),w′=(d′,y), and η∈Aut(T) with ηt(d)=t(d′), the action criterion in N00 gives g∈Aut(D) inducing η and satisfying gd=d′. Let δ be this particular g's O-action. Compatibility of the two points implies

δr_C(x)=δr_D(d)=r_D(gd)=r_D(d′)=r_C(y).

The C hypothesis supplies h inducing **exactly this δ**, with hx=y. Then (g,h)∈Aut(W), has T-action η, and sends w to w′. Thus W→T has prescribed-action point lifting. By the action criterion in N00 its group action is onto and its kernel is transitive on every fibre.

The order of choices matters conceptually: choose g meeting the T prescription, *then accept its O-action*, and ask C to match it. No homomorphism Aut(T)→Aut(O), no map T→O, and no simultaneous independent choice of T- and O-actions is needed.

An explicit positive nonnested sanity check: take D=A×B in coordinate-equality language, T=A, O=B, C=B×Z, all factors nonempty pure sets, and W=A×B×Z. The kernel over T acts transitively on each {a}×B×Z. Neither of T,O maps naturally to the other. The general proof is not restricted to this Cartesian example.

## N09: Nested target product and its actual kernel

Add a map s:T→O with r_D=s∘t. Let W_T=T×_O C be the full actual induced product, and assume its corresponding group identity. The map q:W→W_T, q(d,x)=(t(d),x), is onto: given (u,x), choose d with t(d)=u; the factorization implies r_Dd=s(u)=r_Cx.

Given w=(d,x),w′=(d′,y) and α∈Aut(W_T) taking q(w) to q(w′), write α=(η,h) using the assumed W_T group identity. Thus ηt(d)=t(d′), hx=y, and η,h have the same O-action. By prescribed-action point lifting of D→T choose g∈Aut(D) inducing η and sending d to d′. Since r_D=s∘t and t is onto, the induced O-action of g is precisely that of η. It matches h, so (g,h)∈Aut(W) lifts α and sends w to w′. Apply the action criterion in N00 to conclude onto action and fibre-transitive kernel.

Two useful sharpenings follow from the proof but are not asserted as source amendments: (b) does not itself use C's point-homogeneity hypothesis; it only uses the two product identities and the D→T property. Also ker(Aut(W)→Aut(W_T)) identifies exactly with {(g,1_C):g∈kerτ}; factorization ensures every such g has trivial O-action. Its transitivity can therefore be seen directly on {(d,x):t(d)=u} for fixed (u,x).

## N10: Sparse partial-map descent and exact-owner EPPA matching

Let A_W⊆W be any finite induced substructure, not necessarily a full product. Let A_D=p_D(A_W), A_C=p_C(A_W). Suppose D extends every partial automorphism of A_D. Suppose C extends each pair (p,δ) where p is a partial automorphism of A_C, δ∈Aut(O), and r_Cp=δr_C on dom p. Both extensions must be automorphisms of their entire finite witnesses; C's extension must induce δ on **all of O**.

Necessary descent contract: on A_W, equality of D-coordinates and equality of C-coordinates are unions of old fine colours; also the pullback of each *actual* D- or C-pair colour is an old fine-colour union. In the standing setting these facts were proved in N06. Mere abstract quotient sets or coordinate kernels alone do not suffice to certify quotient-colour preservation.

Take a partial automorphism f:S→S′ of A_W. Define S_D=p_D(S), S′_D=p_D(S′), and f_D(p_Dw)=p_Df(w). Kernel preservation makes it well-defined. Kernel reflection, obtained from preservation under f^(-1), makes it injective. Its range is exactly S′_D. Given any d,d′∈S_D choose lifts w,w′∈S; the pullback colour-union condition and fine-colour preservation by f show that (f_Dd,f_Dd′) has exactly the same actual D-colour as (d,d′). Hence f_D is a genuine partial automorphism of A_D. Do the same for f_C:S_C→S′_C.

Choose g∈Aut(D) extending f_D, using ordinary EPPA. Let δ be g's exact induced action on O. For each x∈S_C choose w=(d,x)∈S. Then

r_Cf_C(x)=r_Df_D(d)=r_Dg(d)=δr_D(d)=δr_C(x).

Thus (f_C,δ) is a compatible request. Choose h∈Aut(C) extending f_C and inducing δ on all O. FK gives (g,h)∈Aut(W). For every (d,x)∈S its image is (f_Dd,f_Cx)=f(d,x), proving ordinary EPPA for the original A_W.

There is no requirement that f was induced by a partial automorphism of some earlier real A. This matters at the master theorem caller: A_V can have partial automorphisms that are not projected from any partial automorphism of A. The descent proof starts afresh from each partial automorphism of A_V.

If f has empty domain, the empty compatible request is covered (or the identity of W extends it directly). If W=∅ then A_W=∅ and EPPA is trivial. The EPPA paragraph logically needs FK and its extension hypotheses; it does not use the auxiliary quotient T or D's point-homogeneity condition. Thus 04's choice T=D merely makes the superfluous condition (i) tautological; it causes no gap.

## N11: Empty systems, assembled export and checked master callers

If B=∅ and D→B,C→B are functions, D=C=∅ and W=∅. All groups are trivial. If B≠∅, surjectivity forces D,C,W nonempty. No mixed case is possible under the stated surjectivity assumptions.

For the general kernel lemma, if C is empty its surjective owner image O
is empty; the map D->O forces D empty, and surjectivity D->T forces
T empty. W and optional W_T are empty. All actual automorphism groups
are the unique trivial groups, so onto and fibre assertions follow
directly. The empty partial map extends by the empty permutation. This
is separate from the nonempty action criterion, whose reverse direction
cannot infer surjectivity from vacuous point requests.

C26 simply assembles N08, optional N09, N10 and these boundary cases into
the existing source lemma. The independent EPPA clause uses its group
identity and A11, not the point-kernel subclaims. The following is a
checked interface to 04, not an expansion/export of that master theorem.

At a step adding p, the ambient identities are actual exact products X_V=X_(V−)×_(X_O)X_(U_p); the new finite witness is the **full** induced B_V=B_(V−)×_(B_O)D_p. Old quotient maps are onto because the old witnesses are a compatible quotient system, and D_p projects onto precisely B_O. Thus 02 applies to every new B_V, retaining all original fine colours.

For M3 use L=B_U×_(B_O)D_p, D=B_U, C=D_p. For an old target B_V, V need not contain O. Old M3 supplies onto action and transitive kernels for B_U→B_V, and the provider supplies the prescribed-owner C property. N08 applies without an illicit map B_V→B_O.

For a new target B_V, V contains U_p, hence V− contains O. The old map B_U→B_O factors through B_(V−). The target B_V is its full product with D_p and has its own 02 identity. N09 applies.

The reduction from maps out of L to every nested B_V→B_(V′) is elementary but should mention that every Aut(L) descends to every actual quotient B_V, because quotient kernels/colour blocks are named fine-colour unions. Onto: lift α∈Aut(B_(V′)) to L, then descend to B_V. For transitivity, given b,b′∈B_V with common B_(V′)-image, choose any lifts l,l′∈L. Their B_(V′)-images agree by commutativity. Move l to l′ by ker(Aut(L)→Aut(B_(V′))); descend the result to B_V. It fixes B_(V′) pointwise and maps b to b′.

For M1 use D=B_(V−), C=D_p, O=B_O, A_W=A_V. The projected original inputs are exactly A_(V−), A_(U_p). Old M1 supplies D's EPPA, and provider clause (1) supplies every compatible C request with an arbitrary prescribed automorphism of B_O. The actual coordinate quotients give the descent contract of N10. No extra owner section, induced-source assumption, or all-quotient automorphism lifting theorem is needed at this consumer.

The caller remains conditional on the owner provider and on ordinary EPPA for all exact quotients, including the identity source; this local audit supplies no independent unconditional EPPA theorem.

## N12: Genuine finite controls and premise boundaries

These are explicit boundary tests for the abstract interfaces. Unless said otherwise they are **not claimed** to satisfy all standing homogeneous CCO/full-exact source assumptions.

### N1: Sparse product, despite both projections onto

Let O be a singleton, D=C={0,1} as pure sets, with coordinate equality colours on D×C. Let W={(0,0),(0,1),(1,0)}, retaining both named coordinate kernels. Both projections are onto. In W the D-fibres have sizes 2 and 1 and the C-fibres have sizes 2 and 1, so every W-automorphism fixes each fibre and each point. Aut(W)=1, whereas Aut(D)×Aut(C)=S₂×S₂. The compatible coordinate swap (0↔1, identity) does not preserve W. Thus fullness is essential even when kernels remain named and coordinate colours recover the fine colours.

### N2: Full set product with extra fine colours

Let X=F₃² and name the full binary orbital language of G={ (i,j)↦(εi+a,εj+b):a,b∈F₃, ε∈{±1} }. Each orbital is symmetric: differences are identified with their common negative. Let E be equality of first coordinates and J equality of second coordinates. They commute, K=Id, H=Top, so the carrier is the full 3×3 product. The actual quotient languages on either factor have just equality and diversity, so each factor has automorphism group S₃. The named fine colour “difference (1,1) or (−1,−1)” is changed to “difference (1,−1) or (−1,1)” by (i,j)↦(−i,j). Therefore a legitimate pair in S₃×S₃ fails to preserve fine colours. In fact the fine group is exactly G: any automorphism preserving E,J has coordinate permutations; every F₃ permutation has form x↦εx+a, and preservation of the two diagonal-slope colours forces the two signs equal.

Thus Aut(X) has order 18 rather than 36, although the set product is full and the coordinate kernels are named. The missing hypothesis is precisely fine-colour recovery: for a diagonal-slope atom a, (E;a;E)∩(J;a;J) includes both diagonal slopes, strictly more than a. This example does not refute 02: it is not asserted that both E,J are full RAW exact in a valid standing CCO source.

### N3: Whole-C transitivity plus onto owner action is too weak

Take O={1,2,3}, C={(i,j):i≠j}, and let K=S₃ act on C by simultaneous permutation, with π(i,j)=i and ρ:K→S₃ the identity. The action on C is transitive and ρ is onto, but kerρ=1 and each owner fibre has two points. For x=(1,2),y=(1,3), the prescription δ=id_O cannot be realized by an element taking x to y.

Set D=T=O with t=id, and use abstract full pullback action W=D×_O C≅C. D→T has the required property. If one replaced C's prescribed-owner point property by the weaker transitivity-plus-onto condition, conclusion (a) would fail: W→T has trivial kernel on two-point fibres. This is an abstract group-action control; it is not a claim about the symmetry of a finite CCO orbital language.

### N4: Merely naming the projection kernels does not suffice for EPPA descent

Let W be a set with a named equivalence whose quotient D is additionally assigned a relation not pulled back to a named fine-colour union on W. A partial automorphism of W can preserve that equivalence but change the extra D relation, so its quotient map need not be a partial automorphism of D. The sharp required contract is both named kernels **and named quotient-colour pullbacks**, as stated in 03. A concrete binary instance: W={0,1,2}, only equality named, kernel identity, and D=W additionally carries graph path 0–1–2. The singleton map 0↦1 is a W-partial automorphism but its two-point extension {0,2}→{0,1} is also a pure-set partial automorphism and changes a D-nonedge to a D-edge. This quotient structure is deliberately not an actual quotient orbital language of W. The actual-colour hypothesis rules it out.

### N5: Matching only the prescribed owners on a partial domain is too weak

For FK, the induced coordinate actions must agree on the **entire** finite owner set O. Agreeing only on old source owners cannot ensure that their coordinatewise action preserves all of W. For O={0,1,2}, D=C=O and W its diagonal, let g=id and h=(1 2). They agree on old owner 0, yet (1,1) maps to (1,2)∉W. Hence C's extension must have exactly δ on all O, as required by 03 and supplied by provider (1).

### P1: No split section is needed, and may not exist

Let C=Z/4 act on itself by translations and O=Z/2, with π reduction mod 2 and ρ the same reduction. The kernel {0,2} is transitive on each π-fibre, so all point prescriptions are realizable. But ρ has no homomorphic section: an order-two preimage of the nonzero element of Z/2 would be needed, and the only nonzero order-two element 2 maps to zero. These actions can be realized as automorphism actions of the named difference orbital structures, though that particular Z/4 language is directed and is used only to illustrate the purely group-theoretic section boundary.

For D=C=Z/4 over O, the compatible-pair group is {(a,b):a≡b mod2}; it acts coordinatewise on the full pullback. All lifting proofs above work by selecting the required element for each request and do not turn those choices into a homomorphism. A “choose one canonical lift for every owner permutation” proof that then multiplies those lifts would therefore introduce an unjustified splitting assumption.

The executable script uses the following slightly different small models
for the first three controls; both the written examples above and these
variants isolate the same stated premises.

* Positive model: X=F2^3 with points (o,d,c), naming EVERY vector
  difference as its ordered-pair colour. Exhaustive colour-preserving
  permutation backtracking yields actual groups of orders 8/4/4/2 on
  W,D=(o,d),C=(o,c),O=o. It does not assume translation groups during
  enumeration. Coordinate differences are exact literal readouts,
  including zero (the diagonal).
* Nonfull control C27: {d=c} has four points and projects onto D and C,
  but the compatible pair flipping only d leaves that subset. This is
  intentionally outside the FULL-product premise.
* Extra-colour control C28: on the full eight-point set, refine the
  difference colour by R(x,y) iff x_d=y_c and x_c=y_d. The same d-only
  flip preserves both coordinate difference colours and violates R,
  for example on x=(0,0,0),y=(1,0,0). Actual refined automorphism group
  has order four. This deliberately lacks exact fine-colour recovery;
  it is not a standing-source CCO counterexample.
* Missing-C control C29: take D=F2^2 with its full translation action,
  O the first bit, T the second. On C=F2^2 retain only the subgroup
  translating the first bit and fixing the second. That group maps
  onto the full O group, but cannot change the second C bit within
  an O-fibre. The matching-pair group on W has order four, maps onto
  T and has a two-element kernel. That kernel cannot send
  (0,0,0) to (0,0,1). This is an explicit ACTION model showing why
  C's prescribed-point premise is needed; the restricted C action
  is not passed off as the full automorphism group of its difference
  structure. A relational realization could name the second bit.
* The C4->C2 example checks all sixteen compatible point prescriptions
  and rejects both candidate identity-preserving sections. This
  directed group-action example does not assert symmetric CCO.

The positive script checks all partial isometries on five selected sparse
original sources, starting from their actual domain/range projections.
For EVERY first-factor extension it verifies compatibility of its exact
owner component and finds all matching second-factor extensions. It
also checks trivial empty quotient systems, the generic finite-base
restriction inside a six-point pure-equivalence source with 48 actual
automorphisms, all 512 four-point seed-conjugation choices, and cyclic
full-packet orbit trimming with an incomplete-packet countercontrol.
Finite checks certify only
these finite examples, not ordinary EPPA of a new age, infinite joint
lifting, actual exactness of arbitrary added colours or the master.

## N13: Receiving projects and return to the human article

B018 is a substantial provider package C01–C13 and C30, reusing B002's actual
exact lifting and the elementary greatest-packet interface from B013.
B019 is a substantial product/action package C14–C29, using accepted
B001 elementary quotient/actions and B002 fine-colour meet. Once these
interfaces are accepted, the two packages can be implemented independently;
B019 takes prescribed factor properties as quantified input instead of
waiting for B018 to prove a particular instance. The five T-tasks are
internal proof milestones, not individual project assignments.

Preserve actual quotient maps, complete pair-colour pullbacks and full
finite owner actions in the public API. Reuse the shared prescribed-action
criterion. No section object or arbitrary family of fine-colour fibre
permutations belongs in these statements. The source provider is conditional
on ordinary EPPA of the CURRENT source; an optional proof of its external
EPPA provider is a separate assignment. The later rank induction must not
feed the same-rank rooted conclusion back into that premise.

The article-feedback ledger records finite-domain wording in the standalone
point lemma, full-owner packet invariance, both kernel and colour descent,
all empty/singleton requests and the independent EPPA consumer. No
numbered conclusion or human TeX was changed in this preparation pass.
The checked master callers are not a proof of its full simultaneous
induction, packet closure and all-family CRT clause. Those are the next
bounded preparation target, followed by joint-owner/rooted consumers.
