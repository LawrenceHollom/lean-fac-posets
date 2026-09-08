# Sequential consolidation limits by principal cuts

This gives a mathematical replacement for the sequential upper-bound argument
in `lem:consolidation-stabilises` (S3.J.5--J.12). It uses the preceding atomic
existence, alternating-class hull, and atomic stabilization results, explicitly
listed below. It does not claim that those prerequisites, this construction, or
the later arbitrary-chain argument have already been formalized in Lean.

The principal interpolation, nonempty trace, maximal trace extension, local
profile calculus, increasing cut realization and its strict order preservation,
strict-separation safeguard, and generic continuity toolkit
are implemented in `Completion/{PrincipalInterpolation,BoundaryProfiles,
CutRealization,Continuity}.lean`. The complete sequential theorem remains a
later Lean obligation, dependent on the inputs in Section 2.

The existing completion `H(P)` and its germ equivalence are unchanged. Stable
germs are used as ordered constraints. They are not required to occur unchanged
in the final chain.

## 1. The necessary witness convention

For an increasing genuine germ `X`, put

    D(X) = {p in P : p < x for some x in a representative of X}.

For a decreasing genuine germ use the dual set

    U(X) = {p in P : x < p for some x in a representative of X}.

These sets are representative independent. For increasing germs, `D(Y) <= D(X)`
is exactly the atomic base formula "every representative point of Y is below
some representative point of X", without imposing atomicity on either argument.
The corresponding decreasing formula is `U(Y) <= U(X)`.

A **whole-chain witness** from `C` to `D` is an order embedding of their entire
nonprincipal orders, including the formal endpoints, that:

* fixes the formal bottom and top;
* takes genuine points to genuine points and preserves their direction;
* preserves existing nonempty suprema and infima;
* satisfies `D(f(X)) <= D(X)` for increasing genuine `X`, and
  `U(f(X)) <= U(X)` for decreasing genuine `X`.

The last condition may equivalently be required only at atomic points, under
the scattered/vacillating hypotheses used here: a non-atomic increasing point
is a supremum of increasing atomic points below it. Continuity and the union
formula for its lower cut give the condition at that point. Use the dual
argument for decreasing points. Keeping the condition at all genuine points
in the interface makes composition immediate and avoids a recursive definition.

There is **no requirement that the genuine image be cofinal in the whole target
chain's nonprincipal order**. The formal-endpoint cofinality clause can be
retained, but it follows from fixing the formal endpoints. The useful
cofinality assertions are the local assertions at individual genuine image
points. Section 8 proves the stronger end preservation actually needed for
illfounded gluing.

### Why genuine cofinality at every outer end is impossible

The following example rules out a sequential upper-bound theorem with that
additional requirement; this is not merely a limitation of the construction.

Let `B = W_0 + W_1 + ...`, with each `W_i` of type `omega`, let `R` have type
`omega`, and let `G = {g_0 < g_1 < ...}`. The poset is the union of the two chains
`B + R` and `G`. Its only cross-chain comparisons are

    w < g_j  iff  w belongs to W_i with i < j.

In particular no point of `G` is below any point of `B + R`, and all of `R` is
incomparable with `G`. This poset is countable, wellfounded, scattered,
quasifounded, vacillating, out-wellfounded, and of width two.

Its maximal chains are exactly

    C_n = W_0 + ... + W_(n-1) + {g_n < g_(n+1) < ...},
    C_infinity = B + R.

The genuine nonprincipal order of `C_n` is
`w_0 < ... < w_(n-1) < u`, where `u` is the common atomic upper germ of the
`G`-tails. Inclusions fixing all these points witness `C_n -> C_(n+1)`, even
with genuine cofinality and genuine-endpoint preservation. These chains are
alternating maximal, so they are candidates starting from `C_0`.

No finite-stage `C_m` can bound all of them, by the sizes of their nonprincipal
orders. The only remaining maximal chain is `C_infinity`, whose genuine order
is `w_0 < w_1 < ... < v < r`, where `v` is the upper germ of `B` and `r` that
of `R`. Genuine cofinality would force the image of `u` to be `r`. Its atomic
clause is false, since `G` and `R` are incomparable. Thus there is no upper
bound with genuine cofinality imposed globally.

With the whole-chain convention above, there is an upper-bound witness fixing
the `w_i` and mapping `u` to `v`. This is the behavior the general construction
must permit.

## 2. Inputs from the preceding machinery

Let `C_0 -> C_1 -> ...` be maximal candidate chains, with chosen whole-chain
witnesses `f_n`. Write `f_s,t` for their finite composites, and `X_t = f_s,t(X)`.
We use the following previously scheduled mathematical inputs.

1. Increasing atomic germs have an omega final segment, and decreasing atomic
   germs have an omega-star initial segment. Atomicity is germ invariant.
   Non-atomic increasing points are approximated from below by increasing
   atomic points; decreasing points have the dual approximation.
2. An infinite alternation class `I` has boundary markers `L_I` and `R_I` in the
   nonprincipal order: `L_I` is decreasing or the formal bottom, and `R_I` is
   increasing or the formal top. For different ordered classes `I < J`,
   `R_I < L_J`. At an outer boundary a formal marker is permitted; it is not
   asserted to be a represented germ.
3. The ambient external hull `Q_I` of a class in an alternating-maximal chain
   is out-wellfounded. Genuine germs between the transported boundary markers
   have representatives in this hull. Indeed, the local `D`/`U` inclusions
   retain all external principal lower and upper bounds of `I`.
4. In a fixed such hull, every sequence of increasing atomic germs with
   successive atomic consolidations is eventually constant; dually below.
   This follows from atomic antisymmetry, the domination antichain lemma, FAC,
   and wellfoundedness of `N+` in an out-wellfounded hull. An infinite sequence
   of distinct atomic consolidations has, by infinite Ramsey, either a
   domination antichain or a descending domination subsequence. The former
   contradicts FAC by the domination lemma, and the latter contradicts that
   wellfoundedness.

   If proving wellfoundedness of `N+` requires realizing an ordered family of
   ambient germs in one chain, use the principal-cut construction of Section 4.
   That construction uses only scatteredness and so is available before atomic
   stabilization; it does not create a circular dependency.

These are local atomic statements; none asserts antisymmetry of consolidation
on general germs. Boundary markers must be interpreted in the original
chain's completion, not as the images of both formal endpoints of every
subchain completion.

## 3. Protected atomic descendants

Fix an increasing atomic `A` at stage `s`, in class `I`. At stage `t >= s`, allow
increasing atomic states `Y` satisfying

    f_s,t(L_I) < Y <= f_s,t(A).

There is an edge to a next-stage state `Z` if `Z <= f_t(Y)` and `Z` remains
above `f_s,t+1(L_I)`. An outgoing edge always exists, by atomic approximation
below the genuine increasing point `f_t(Y)` and above the lower marker.

The protected lower marker is essential. It keeps every state in the fixed
out-wellfounded hull `Q_I`; a graph allowing arbitrary jumps to earlier
alternation classes would not have this justification.

Every infinite path eventually becomes constant by input 4. Let `S_s(A)` be
the set of germs reached by a finite protected path which then remain constant
along a protected path forever. Thus `S_s(A)` is nonempty. The decreasing
construction reverses the inequalities and uses the transported upper marker
`R_I` as protection.

A constant path at `Y` actually has `f_t(Y) = Y` at all sufficiently late stages.
For example, in the increasing case the edge gives `Y <= f_t(Y)`, while both
points are in `N(C_t+1)` and the local lower-set inclusion gives the reverse
inequality. This observation is only about germs, not persistence of their
representing points.

Let `S` be the union of all these stabilization sets, for all starting stages
and atomic sources of both signs. **`S` is a chain in `H(P)`:** any two of its
points occur together in every sufficiently late `N(C_t)`. We do not assert
that one chain in `P` realizes these germs unchanged.

We will also need a uniform estimate. If `X` is an increasing point of `C_s`,
`A <= X` is increasing atomic, and `Z in S_s(A)`, then

    D(Z) <= D(X_t)    for every t >= s.                 (3.1)

If `Z` stabilizes after stage `t`, this follows from the local lower-set
inclusions along the composed path back to stage `t`. If it stabilizes before
stage `t`, its constant continuation is below `f_s,t(A) <= X_t`. The dual
estimate is `U(Z) <= U(X_t)` for decreasing atomic `A >= X`.

## 4. Realizing ordered constraints by principal cuts

Extend `S` to a maximal chain `K` of `H(P)`. Let

    E = {p in P : the principal point p belongs to K}.

Assume `P` is nonempty; if `P` is empty, all stage chains are empty and the
endpoint-only identity witnesses give the upper bound immediately. Under this
assumption `E` is a nonempty chain. It is not required to be maximal or saturated.

### Principal interpolation in K

If `g` is a genuine increasing point of `K`, then

    for every a in K with a < g, some e in E satisfies a < e < g.       (4.1)

The dual assertion holds above a genuine decreasing point.

Here is a proof using scatteredness. In a principal-free convex interval of
`K`, a cover can only have an increasing lower endpoint and a decreasing upper
endpoint. Every other pair of signs admits a principal point strictly between
it in `H(P)`; for a cover this point is comparable with all of `K` and must be
in `K`, a contradiction. Thus two cover edges cannot share an endpoint.

Here is a direct way to conclude that the interval has at most two points,
without a further quotient. In any scattered linear order with no consecutive
covers, the set of lower endpoints of covers is densely ordered: between
`x < y` in that set, the successor `x'` of `x` is strictly below `y`, and the
scattered cover lemma applied in `[x',y]` supplies another lower endpoint
strictly between `x` and `y`. Three points in the original order supply two
distinct lower endpoints by applying the cover lemma in its two adjacent
intervals. That gives a nontrivial dense order and hence a rational copy,
contradicting scatteredness. This argument is checked in
`Preliminaries/ScatteredCovers.lean`.

If (4.1) failed, the nonempty interval `(a,g]` in `K` would consist of at most
two genuine points, giving a cover immediately below the increasing point `g`.
That cover also admits a principal interpolant, a contradiction. This proves
(4.1) and its dual. Nonemptiness of `E` follows similarly; if `K` contains no
genuine point, maximality permits insertion of a principal point directly.

Now extend `E` to a maximal chain `C` in `P`. For a genuine increasing `g in K`
define the following initial segment of `C`:

    I_g = {c in C : c <= e for some e in E with e < g}.

It is nonempty and has no greatest point by (4.1). Let `rho(g)` be its increasing
germ in `H(C)`. For decreasing `g`, use the final segment

    J_g = {c in C : e <= c for some e in E with g < e}

and its decreasing germ. Send principal points of `K` to the same principal
points of `C`, and send formal endpoints to formal endpoints.

This map is strictly order preserving and preserves direction. For equal
signs, and for a decreasing point below an increasing point, use a principal
interpolant in `K`. For an increasing point below a decreasing point, every
point of the initial segment defining the first image is below every point
of the final segment defining the second. Their different directions give
distinct completion points even when there is no principal point between them.

We also have the local estimates

    D(rho(g)) <= D(g)   for increasing g,
    U(rho(g)) <= U(g)   for decreasing g.               (4.2)

For example, `c <= e < g` implies `c in D(g)`.

### The strict-separation safeguard

If `p` is any principal point of `P` with `p < g in K` increasing, then

    some e in E has e < g and NOT e <= p.               (4.3)

Otherwise (4.1) shows that every member of `K` below `g` is below `p`. Every
member at or above `g` is above `p`, so maximality puts `p` in `K`. Applying
(4.1) above this `p` contradicts the assumed upper bound.

It follows that if an initial segment `T` of `C` is bounded above by such a
`p`, its increasing germ is strictly below `rho(g)`: choose `e` from (4.3).
Because `C` is a chain and `e` is not below `p`, every point of `T` is below
`e`, and `e < rho(g)`. This safeguard replaces the invalid claim that a stable
atomic germ remains atomic, or even remains present, in the final chain.

## 5. The upper-bound maps

For an increasing atomic point `A` of `C_s`, set

    F_s(A) = sup_{H(C)} {rho(Z) : Z in S_s(A)}.

For a decreasing atomic point take the corresponding infimum. For a
non-atomic increasing point `X`, set

    F_s(X) = sup {F_s(A) : A increasing atomic in C_s, A < X},

and use the dual infimum for non-atomic decreasing points. Formal endpoints
map to formal endpoints.

All these images are genuine and have the required sign. More explicitly, an
increasing image is the germ of the union of the nonempty initial segments
`I_Z` appearing in its formula. That union has no greatest point. This also
handles an attained supremum of stabilization images. Use unions of final
segments for decreasing images.

Equations (3.1) and (4.2), together with this union description, give

    D(F_s(X)) <= D(X_t)    for every t >= s, increasing X,
    U(F_s(X)) <= U(X_t)    for every t >= s, decreasing X.              (5.1)

In particular the required local cofinality conditions hold at `t = s` for
every genuine source point, not merely the atomic ones.

## 6. Strict order preservation

Suppose first that `X < Y` are increasing points of `C_s`. Choose an increasing
atomic `A` with `X < A <= Y`, taking `A = Y` when `Y` is atomic. In the protected
graph for `A`, further require the state at stage `t` to lie above `X_t`.
This is possible at every step: use the larger of the original lower marker
and `X_t`, and atomic approximation below the next image. The refined path
still lies in `Q_I`, so it stabilizes at some `Z in S_s(A)` with `X_t < Z` for
all sufficiently large `t`.

Fix such a stage `t` and take a principal separator `p` with `X_t < p < Z`.
By (5.1), the initial segment representing `F_s(X)` is bounded above by `p`.
The safeguard (4.3) therefore gives

    F_s(X) < rho(Z) <= F_s(Y).

This proves strictness for all increasing pairs, including a non-atomic point
immediately below an atomic one. The decreasing proof is its order dual.

If `X` is increasing and `Y` decreasing with `X < Y`, every positive stabilized
descendant used for `X` is below every negative stabilized descendant used for
`Y`: at a sufficiently late common stage the former is at most `X_t`, while
the latter is at least `Y_t`. Consequently `F_s(X) <= F_s(Y)`. Their different
directions make the inequality strict.

For an atomic decreasing `A` below an atomic increasing `B`, consider their
source alternation classes. If they are the same, all their stabilized
descendants lie in one out-wellfounded hull. A positive descendant cannot lie
below a negative one, and they are comparable in a late `C_t`, so every
negative descendant is below every positive descendant. If the classes
`I < J` differ, protection gives, at any sufficiently late common stage,

    negative descendant < f_s,t(R_I) < f_s,t(L_J) < positive descendant.

In either case, choose one descendant of each sign. Their `rho` images give

    F_s(A) <= rho(negative descendant)
           < rho(positive descendant) <= F_s(B).

For arbitrary decreasing `X < Y` increasing, choose atomic decreasing
`X <= A < Y` and atomic increasing `A < B <= Y`, using equality when the
respective endpoint is atomic. The defining infimum/supremum formulas give
`F_s(X) <= F_s(A) < F_s(B) <= F_s(Y)`.

Formal endpoints cause no difficulty since all other images are genuine.
This proves strict order preservation and injectivity.

## 7. Continuity and the sequential upper bound

A non-attained supremum in `N(C_s)` is a genuine non-atomic increasing point.
The direction follows from the completion's cut description. Atomic increasing
points cannot be such suprema: the start of an omega final segment gives a
principal bound strictly below the point for all smaller nonprincipal points.
The formal top cannot be a non-attained supremum either: take the supremum in
`H(C_s)` of the proposed nonempty set. The completion's non-attained-bound
theorem makes it a genuine increasing point, so it already belongs to `N(C_s)`
and is strictly below the formal top.
The dual assertions hold for infima.

Suppose `X = sup T` is not attained. Increasing atomic points below `X` are
cofinal there. For every such atomic `A`, some `t in T` satisfies `A < t`.
The definition of `F_s(X)` and monotonicity therefore imply

    F_s(X) = sup {F_s(A) : A atomic increasing, A < X}
           = sup F_s[T].

Attained suprema are preserved by monotonicity. Infima follow by duality;
empty-set bounds follow from the formal endpoints. Thus `F_s` is a whole-chain
witness from `C_s` to the same maximal chain `C`, for every `s`.

In particular `F_0` makes `C` a candidate. The earlier closure theorem then
retains alternating maximality. No equality of the finite-stage carriers'
liminf with `C`, no persistence of stable representatives, and no unchanged
image of a stable germ are used.

## 8. Compatibility with the later application

The local cofinality condition is precisely what the atomic domination and
comparison arguments use. It composes. The candidate relation remains on
whole chains; a partial order can be taken on its mutual-reachability quotient.
General germ-local consolidation is not asserted to be antisymmetric.

Illfounded boundary preservation also remains available. Let an illfounded
increasing source point `X` have cofinal alternating atomic points

    A_0(+) < B_0(-) < A_1(+) < B_1(-) < ... < X.

Their images are strictly ordered with the same signs, and continuity makes
their supremum `F_s(X)`. They therefore witness an illfounded image point.
The positive local condition gives `D(F_s(X)) <= D(X)`. For the reverse
inclusion, take a principal point below `X`, choose a later decreasing `B_i`,
and use its negative local condition. A representative point above the given
principal point can then be chosen below `F_s(X)`. Hence the source and image
are bicomparable, as required for gluing.

In a quasifounded ambient poset this illfounded image cannot have a principal
point of `C` above it: together with a principal point below it, that would
place an illfounded limit inside a principal-bounded interval. Therefore an
illfounded upper endpoint maps to the genuine upper endpoint of `C`; the dual
holds below. The actual end cofinality needed for illfounded gluing is thus a
consequence, even though imposing it at ordinary ends would destroy upper
bounds as in Section 1.

The final finite-trace replacement still has whole-chain witnesses: existing
points outside the replaced interval are retained, and an atomic replaced
interval maps to its new boundary using the atomic base condition. A finite
interval can introduce new genuine points. The witness convention imposes no
new global-end obstruction on these replacements. Their nontriviality is
checked using the fixed-domain self-embedding/atomic antisymmetry argument,
not the false partial order on general germs.

The arbitrary-chain reduction (S3.J.13) remains a separate proof obligation;
the sequential theorem alone is not a justification for applying Zorn.
