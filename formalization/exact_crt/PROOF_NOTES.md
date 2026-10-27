# Exact CRT, quotient readout and guarded descent

Mathematical preparation for other Lean projects; no Lean representation or
provider import here has compiled. The module covers the five numbered
results in `exact_lattice_crt.tex` and `exact_gluing_geometry.tex`, and the
two unnumbered fibre-product/colour equations. Source hashes and the claim
DAG are in `module.json`. Human TeX is unchanged.

## N01: Permuting equivalences and their classes

Let X be inhabited and Ecal a sublattice of actual equivalence relations
on X, closed under ambient binary meet/join. Its members pairwise permute
under represented relational composition. X and Ecal need not be finite.
The sublattice need not contain ambient equality or the universal relation.

For commuting E,F, EF is an equivalence containing both E and F. Any
equivalence containing them contains EF, hence EF=E join F. Consequently
E[x] meets F[y] iff x(E join F)y: witnesses of the class intersection give
the two-step walk, and a product witness gives a common representative.
This is also equality of the two quotient-class images in X/(E join F).
No class representative is required to be chosen coherently over all tuples.

## N02: Class Helly and distributivity

Assume finite class Helly. If xEy and x(F join G)y, write xFzGy.
The three classes E[x], F[x], G[y] meet pairwise, with witnesses x,y,z.
A common w gives x(E meet F)w(E meet G)y. Thus
E meet (F join G) <= (E meet F) join (E meet G). The opposite inclusion
is order-theoretic. This distributive law implies the dual distributive law.

Conversely suppose Ecal is distributive. Induct on a finite list of
pairwise-intersecting classes. For an empty list use X inhabited, and for
one class use its centre. For n>=2 let z meet the first n-1 classes.
Each intersects E_n[x_n], so z(E_i join E_n)x_n for every i<n. The
nonempty meet H=meet_(i<n) E_i belongs to Ecal, and finite distributivity
gives meet_(i<n)(E_i join E_n)=H join E_n. Since H commutes with E_n,
choose zHwE_n x_n. This w lies in every original class.

Repeated relations/centres cause no issue. Do not form an empty meet
inside an arbitrary sublattice to handle the induction's zero case.

## N03: The finite compatible-tuple map

For a finite **nonempty** list E_i, set K=meet E_i. Define
[x]_K -> ([x]_(E_i))_i. It is well-defined; equality of images is exactly
K-equivalence, hence injective. Each image tuple is compatible in every
X/(E_i join E_j). These facts need no distributivity.

N01 identifies compatibility with pairwise intersection of the chosen
classes. Class Helly gives one real representative of every compatible
tuple; conversely CRT surjectivity gives class Helly for nonempty families.
The empty class family is handled independently by X inhabited.

For an optional empty CRT family, the ambient intersection is Top_X and
X/Top_X and the empty product are singletons. An arbitrary sublattice's
greatest element cannot replace Top_X. In the actual exact lattice Top is
present, so that extension is internal there. All CRT assertions here are
finite. On Nat the nested equivalences with singleton classes below n and
one tail class [n,infinity) form a commuting distributive chain; the tail
classes have every finite intersection nonempty but no total intersection.
Thus no infinite-family CRT follows from these hypotheses.

## N04: Internal finite Birkhoff proof

For a finite inhabited distributive lattice Lambda, let P be its nonzero
join-irreducibles, ordered by inherited <=. Exclude bottom. These elements
need not be atoms, and are not the meet-irreducibles used for coordinates.

Every a is the finite join of the join-irreducibles below it: induct on
the strict lower set of a. Bottom is the empty join. A nonbottom a is
either itself irreducible or decomposes as b join c with b,c<a, where
induction applies. Distributivity makes every p in P join-prime: if
p<=a join b, then p=(p meet a) join (p meet b), so p<=a or p<=b.
Finite induction gives the analogous nonempty finite-join property;
the empty join cannot dominate p because p is nonzero.

Define Phi(a)={p in P:p<=a} and Psi(D)=join D for a downset D of P.
Decomposition proves Psi(Phi(a))=a. For p<=join D, finite join-primality
finds d in D with p<=d; downward closure puts p in D. This proves
Phi(Psi(D))=D, including D empty. Both maps are monotone, hence give the
order/lattice isomorphism Lambda ~= Down(P). For a one-element lattice,
P is empty and Down(P) is a singleton. A receiving project may reuse a
matching library theorem instead; no exact Lean name is prescribed here.

## N05: Actual exact-lattice instantiation

In the actual original one-sort symmetric homogeneous CCO source, finitely
many orbitals give finitely many invariant relations. Exact equivalences
include Id and Top. Their meets contain Id, so exact-meet nonemptiness is
automatic; RAW exact convolution makes their represented products exact.
All invariant relations commute because all original pair orbitals are
symmetric, so products are ambient joins. Thus exact equivalences form a
finite bounded sublattice of the full invariant lattice.

Use the **different-centre exact-ball Helly** provider for the classes
E_i[x_i], not merely Helly of binary supports. Apply N02/N03, then N04.
This proves distributivity, finite set-level CRT and Birkhoff representation
for the exact sublattice. No SAP, Hasse/parity, finite-index assumption or
distributivity of the full invariant lattice is used.

## N06: Selected meet-irreducible coordinates

In a distributive lattice, if L is binary meet-irreducible and x meet y<=L,
then L=(x join L) meet (y join L). Irreducibility gives x<=L or y<=L.
Induct over a finite **nonempty** list J_1,...,J_r to obtain
meet_i J_i<=L => some J_i<=L. Lattice finiteness is not needed for this
algebraic argument, though the source works in a finite lattice.

The J_i need not be distinct or themselves meet-irreducible. Use the proper
meet-irreducible convention for actual quotient coordinates. Even if a
binary definition permits top, the source's r>=1 keeps its conclusion true;
with r=0 and L=top it would be false. For represented equivalences,
J_i<=L induces the well-defined surjection [x]_(J_i) -> [x]_L. This is an
upward quotient image, not an ambient-automorphism lifting theorem.

## N07: Two-factor sets and fine colours

For any two permuting equivalences E,J, K=E meet J, Q=E join J, the
canonical map X/K -> (X/E) times_(X/Q) (X/J) is injective and onto.
Compatibility says that the two classes lie in one Q-class; Q=EJ gives
their common representative. No Helly or distributivity is needed for
this **two-factor set bijection**.

In the actual exact source, colour readout is a separate provider:
for every original atom a, including Id,
K;a=(E;a) meet (J;a). Original commutation/idempotence identify these
with K;a;K, E;a;E and J;a;J. The actual quotient pair orbitals are exactly
these saturated blocks, so the two coarse colours recover the fine K
colour. The abstract set CRT does not establish this formula. Neither
formula by itself supplies joint extension of finite maps or a group section.

## N08: Actual typed orbital blocks and inverse images

Now use named individually transitive original sorts and exact kernels E_s
on every sort visited by a word. Name all actual pair orbitals of the
original action on the quotients. The pullback of an output orbital with
an old representative atom a:u->v is E_u;a;E_v. To prove this, move one
output pair to the other by an original automorphism and change endpoints
within their kernel classes. No quotient homogeneity or lifting section
is assumed. These blocks are exact by typed RAW convolution.

Quotient equality pulls back to E_s, not Id_s. Quotient Top pulls back to
typed Top. Pullback commutes with composition: a quotient intermediate
class has real representatives; their possible discrepancy is removed by
endpoint saturation. Thus for a word a_1;...;a_k the actual pullback is
E_s0;a_1;E_s1;a_2;...;a_k;E_sk. Keep these intermediate kernels.
Induction on words and ordinary inverse-image intersections gives full
exactness of pullbacks of nonempty exact quotient relations. No intertwining
is needed in this direction. Empty words pull back to E_s, and empty
restriction lists to Top.

## N09: Same-sort exact descent

Retain the source statement: invariant exact J, exact nonempty Q>=J and
explicit J;Q;J=Q. Containment alone does not replace saturation for an
arbitrary relation. For Q an equivalence containing J, saturation follows.
The proof actually works for any nonempty exact saturated Q, but the source
export keeps its stated hypotheses; no stronger source theorem is claimed.

For a presentation Q=meet P_i, RAW convolution over the nonempty result
gives Q=meet (J;P_i;J). In the one-sort symmetric setting every original
invariant relation commutes with J, so for a positive word P_i=a_1...a_k,
J;P_i;J=(J;a_1;J)...(J;a_k;J). This is the pullback of its factorwise
quotient word. For an empty word both saturation and quotient equality
pullback give J. For an empty restriction list use Top. The quotient image
is therefore a meet of quotient word profiles, hence exact. The converse
is N08 and does not require descent as a provider.

## N10: Typed descent with presentation-local intertwining

Let nonempty exact D:s->t satisfy E_s;D;E_t=D, with a fixed finite word
presentation. Only atoms a:u->v occurring in that presentation must obey
E_u;a=a;E_v. Kernels are supplied for every visited intermediate sort,
not just s,t. The condition is about this presentation, not every atom in
the entire language. It is a sufficient criterion, not a characterization.

In the N08 word pullback move each E_si through its adjacent letter using
intertwining and collapse idempotent kernels. This gives E_s;P_w;E_t.
Identity factors automatically intertwine, and a zero-length word is a
loop word. Typed nonempty-result exact convolution then gives
D=meet_w (E_s;P_w;E_t), each factor being one quotient-word pullback.
The quotient relation is exact. The empty presentation is typed Top.
Converse exact pullback is N08 and imports no intertwining premise.

A diagnostic actual finite source has three named sorts A,B,C, each F2,
with all typed pair colours given by bit difference. Partial isomorphisms
extend by a common bit translation, and semantic CCO is XOR cycle
consistency, so this is homogeneous CCO without SAP. Take E_A=E_C=Id,
E_B=Top and the bit-zero atoms a:A->B,b:B->C. Their old word ab is already
endpoint-saturated, with two pairs. Its factorwise quotient-word pullback
(E_A;a;E_B)(E_B;b;E_C) has four pairs, and intertwining fails.
This refutes that factorwise identity without intertwining. It does NOT
refute unrestricted exact descent: the old A->C relation still descends
as a named quotient atom. Do not promote this control into a stronger
negative theorem.
