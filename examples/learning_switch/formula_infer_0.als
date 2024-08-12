//0
open util/boolean
open util/ordering[Idx] as IdxOrder
open util/ordering[ParamIdx] as ParamIdxOrder

abstract sig Var {}

abstract sig Atom {}

abstract sig Sort {
	atoms : some Atom
}

abstract sig ParamIdx {}

// base name for an action
abstract sig BaseName {
	paramIdxs : set ParamIdx,
	paramTypes : set(ParamIdx->Sort)
}

// concrete action
abstract sig Act {
	baseName : BaseName,
	params : ParamIdx->Atom
}


/* Formula signatures (represented by a DAG) */
abstract sig Formula {
	children : set Formula
}

sig TT, FF extends Formula {} {
	no children
}


sig Implies extends Formula {
	left : Formula,
	right : Formula
} {
	children = left + right
}

sig FlSymAction {
    baseName : BaseName,

    // actToFlParamsMap maps action-params to fluent-params
    // in other words, actToFlParamsMap decides which of the action-params will be
    // used for setting a boolean value of the state variable (representing the
    // fluent) in the _hist TLA+ code.
    actToFlParamsMap : set(ParamIdx->ParamIdx)
} {
    // actToFlParamsMap is an injective function
    all x1,x2,y1,y2 : ParamIdx |
        (x1->y1 in actToFlParamsMap and x2->y2 in actToFlParamsMap) implies (x1->y1 = x2->y2 or (not x1=x2 and not y1=y2))

    // domain(actToFlParamsMap) \subseteq paramIdxs(baseName)
    actToFlParamsMap.ParamIdx in baseName.paramIdxs
}

sig Fluent extends Formula {
    initially : Bool,
    initFl : set FlSymAction,
    termFl : set FlSymAction,

    // vars represents the parameters (including the ordering) to the fluent itself
	vars : set(ParamIdx->Var)
} {
    no children
    no initFl.baseName & termFl.baseName // strong condition for ensuring initFl and termFl are mutex
    some initFl + termFl
    some vars

    // vars is a function
    all p : ParamIdx, v1,v2 : Var | (p->v1 in vars and p->v2 in vars) implies (v1 = v2)


    // each fluent must accept all the fluent params in vars
    all s : (initFl + termFl) | ParamIdx.(s.actToFlParamsMap) = vars.Var

    // each action must input the same param-types to the fluent
    let flParamTypes = vars.envVarTypes |
        all a : (initFl+termFl) |
            // for each param in the action, its type must match the fluent
            all actIdx : a.actToFlParamsMap.ParamIdx |
                let flIdx = actIdx.(a.actToFlParamsMap) |
                    flIdx.flParamTypes = actIdx.(a.baseName.paramTypes)
}

sig Forall extends Formula {
	var : Var,
	sort : Sort,
	matrix : Formula
} {
	children = matrix
}

sig Exists extends Formula {
	var : Var,
	sort : Sort,
	matrix : Formula
} {
	children = matrix
}

one sig Root extends Formula {} {
	one children
}

fact {
	all f : Formula | f in Root.*children // all formulas must be a sub-formula of the root
	no Root.^children & Root // root appears once
	all f : Formula | f not in f.^children // eliminates cycles in formula nodes

	ParamIdx.(Fluent.vars) in (Forall.var + Exists.var) // approximately: no free variables=

	// do not quantify over a variable that's already in scope
	all f1, f2 : Forall | (f2 in f1.^children) implies not (f1.var = f2.var)
	all f1, f2 : Exists | (f2 in f1.^children) implies not (f1.var = f2.var)
	all f1 : Forall, f2 : Exists | (f2 in f1.^children) implies not (f1.var = f2.var)
	all f1 : Exists, f2 : Forall | (f2 in f1.^children) implies not (f1.var = f2.var)
}


abstract sig Env {
	maps : set(Var -> Atom)
}
one sig EmptyEnv extends Env {} {
	no maps
}

abstract sig Idx {}

abstract sig Trace {
	path : Idx -> Act, // the path for the trace
	lastIdx : Idx, // the last index in the path for the trace
	satisfies : Env -> Idx -> Formula // formulas that satisfy this trace
} {
	// trace semantics, i.e. e |- t,i |= f, where e is an environment, t is a trace, i is an index, and f is a formula
	all e : Env, i : Idx, f : TT | e->i->f in satisfies
	all e : Env, i : Idx, f : FF | e->i->f not in satisfies
	all e : Env, i : Idx, f : Implies | e->i->f in satisfies iff (e->i->f.left in satisfies implies e->i->f.right in satisfies)

    // e |- t,i |= f (where f is a fluent) iff any (the disjunction) of the following three hold:
    // 1. i = 0 and f.initally = True and t[i] \notin f.termFl
    // 2. t[i] \in f.initFl
    // 3. t[i] \notin f.termFl and (e |- t,i-1 |= f)
	all e : Env, i : Idx, f : Fluent | e->i->f in satisfies iff
        // a is the action at the current index i in the trace
        let a = i.path |
            ((i = IdxOrder/first and f.initially = True and not isTermAct[a,e,f]) or
             (isInitAct[a,e,f]) or
             (not isTermAct[a,e,f] and some i' : Idx | i'->i in IdxOrder/next and e->i'->f in satisfies))

	all e : Env, i : Idx, f : Forall | e->i->f in satisfies iff
		(all x : f.sort.atoms | some e' : Env | pushEnv[e',e,f.var,x] and e'->i->f.matrix in satisfies)
	all e : Env, i : Idx, f : Exists | e->i->f in satisfies iff
		(some x : f.sort.atoms | some e' : Env | pushEnv[e',e,f.var,x] and e'->i->f.matrix in satisfies)
	all e : Env, i : Idx, f : Root | e->i->f in satisfies iff e->i->f.children in satisfies
}

// does this action initiate the fluent?
pred isInitAct[a : Act, e : Env, f : Fluent] {
    some s : f.initFl |
        a.baseName = s.baseName and (~(f.vars)).(~(s.actToFlParamsMap)).(a.params) in e.maps
}

// does this action terminate the fluent?
pred isTermAct[a : Act, e : Env, f : Fluent] {
    some s : f.termFl |
        a.baseName = s.baseName and (~(f.vars)).(~(s.actToFlParamsMap)).(a.params) in e.maps
}

pred pushEnv[env', env : Env, v : Var, x : Atom] {
	env'.maps = env.maps + (v->x)
}

fun indices[t : Trace] : set Idx {
	t.lastIdx.*(~IdxOrder/next)
}

fun rangeParamIdx[p : ParamIdx] : set ParamIdx {
	p.*(~ParamIdxOrder/next)
}

abstract sig PosTrace extends Trace {} {}
abstract sig NegTrace extends Trace {} {}
one sig EmptyTrace extends Trace {} {
	 no path
}


/* main */
run {
	// find a formula that separates "good" traces from "bad" ones
	all pt : PosTrace | EmptyEnv->indices[pt]->Root in pt.satisfies
	all nt : NegTrace | no (EmptyEnv->nt.lastIdx->Root & nt.satisfies)
	EmptyEnv->T0->Root in EmptyTrace.satisfies // the formula must satisfy the empty trace
	minsome children // smallest formula possible
}
for 8 Formula, 5 FlSymAction

one sig P0, P1, P2, P3, P4 extends ParamIdx {}

fact {
	ParamIdxOrder/first = P0
	ParamIdxOrder/next = P0->P1 + P1->P2 + P2->P3 + P3->P4
	all f : Fluent | (f.vars.Var = P0) or (f.vars.Var = P0+P1) or (f.vars.Var = P0+P1+P2) or (f.vars.Var = P0+P1+P2+P3) or (f.vars.Var = P0+P1+P2+P3+P4)
}



one sig n1, n2, n3 extends Atom {}

one sig Node extends Sort {} {
	atoms = n1 + n2 + n3
}

one sig Forward extends BaseName {} {
	paramIdxs = P0 + P1 + P2 + P3 + P4
	paramTypes = P0->Node + P1->Node + P2->Node + P3->Node + P4->Node
}
one sig Forwardn2n1n3n2n3 extends Act {} {
	params = (P0->n2 + P1->n1 + P2->n3 + P3->n2 + P4->n3)
}
one sig Forwardn2n1n3n2n2 extends Act {} {
	params = (P0->n2 + P1->n1 + P2->n3 + P3->n2 + P4->n2)
}
one sig Forwardn2n1n3n2n1 extends Act {} {
	params = (P0->n2 + P1->n1 + P2->n3 + P3->n2 + P4->n1)
}
one sig Forwardn3n2n3n3n1 extends Act {} {
	params = (P0->n3 + P1->n2 + P2->n3 + P3->n3 + P4->n1)
}
one sig Forwardn3n1n1n2n1 extends Act {} {
	params = (P0->n3 + P1->n1 + P2->n1 + P3->n2 + P4->n1)
}
one sig Forwardn3n2n2n1n2 extends Act {} {
	params = (P0->n3 + P1->n2 + P2->n2 + P3->n1 + P4->n2)
}
one sig Forwardn3n2n3n3n3 extends Act {} {
	params = (P0->n3 + P1->n2 + P2->n3 + P3->n3 + P4->n3)
}
one sig Forwardn3n1n1n2n3 extends Act {} {
	params = (P0->n3 + P1->n1 + P2->n1 + P3->n2 + P4->n3)
}
one sig Forwardn3n2n2n1n1 extends Act {} {
	params = (P0->n3 + P1->n2 + P2->n2 + P3->n1 + P4->n1)
}
one sig Forwardn3n2n3n3n2 extends Act {} {
	params = (P0->n3 + P1->n2 + P2->n3 + P3->n3 + P4->n2)
}
one sig Forwardn3n1n1n2n2 extends Act {} {
	params = (P0->n3 + P1->n1 + P2->n1 + P3->n2 + P4->n2)
}
one sig Forwardn1n3n1n3n3 extends Act {} {
	params = (P0->n1 + P1->n3 + P2->n1 + P3->n3 + P4->n3)
}
one sig Forwardn3n2n2n1n3 extends Act {} {
	params = (P0->n3 + P1->n2 + P2->n2 + P3->n1 + P4->n3)
}
one sig Forwardn2n1n3n3n1 extends Act {} {
	params = (P0->n2 + P1->n1 + P2->n3 + P3->n3 + P4->n1)
}
one sig Forwardn2n1n2n1n3 extends Act {} {
	params = (P0->n2 + P1->n1 + P2->n2 + P3->n1 + P4->n3)
}
one sig Forwardn2n1n3n3n3 extends Act {} {
	params = (P0->n2 + P1->n1 + P2->n3 + P3->n3 + P4->n3)
}
one sig Forwardn2n1n2n1n2 extends Act {} {
	params = (P0->n2 + P1->n1 + P2->n2 + P3->n1 + P4->n2)
}
one sig Forwardn2n1n3n3n2 extends Act {} {
	params = (P0->n2 + P1->n1 + P2->n3 + P3->n3 + P4->n2)
}
one sig Forwardn2n1n2n1n1 extends Act {} {
	params = (P0->n2 + P1->n1 + P2->n2 + P3->n1 + P4->n1)
}
one sig Forwardn1n3n1n3n1 extends Act {} {
	params = (P0->n1 + P1->n3 + P2->n1 + P3->n3 + P4->n1)
}
one sig Forwardn1n3n1n3n2 extends Act {} {
	params = (P0->n1 + P1->n3 + P2->n1 + P3->n3 + P4->n2)
}
one sig Forwardn3n2n2n2n1 extends Act {} {
	params = (P0->n3 + P1->n2 + P2->n2 + P3->n2 + P4->n1)
}
one sig Forwardn3n1n1n3n2 extends Act {} {
	params = (P0->n3 + P1->n1 + P2->n1 + P3->n3 + P4->n2)
}
one sig Forwardn3n1n1n3n1 extends Act {} {
	params = (P0->n3 + P1->n1 + P2->n1 + P3->n3 + P4->n1)
}
one sig Forwardn3n2n2n2n3 extends Act {} {
	params = (P0->n3 + P1->n2 + P2->n2 + P3->n2 + P4->n3)
}
one sig Forwardn3n3n3n1n3 extends Act {} {
	params = (P0->n3 + P1->n3 + P2->n3 + P3->n1 + P4->n3)
}
one sig Forwardn3n2n2n2n2 extends Act {} {
	params = (P0->n3 + P1->n2 + P2->n2 + P3->n2 + P4->n2)
}
one sig Forwardn3n1n1n3n3 extends Act {} {
	params = (P0->n3 + P1->n1 + P2->n1 + P3->n3 + P4->n3)
}
one sig Forwardn1n3n1n2n2 extends Act {} {
	params = (P0->n1 + P1->n3 + P2->n1 + P3->n2 + P4->n2)
}
one sig Forwardn3n3n3n1n1 extends Act {} {
	params = (P0->n3 + P1->n3 + P2->n3 + P3->n1 + P4->n1)
}
one sig Forwardn1n3n1n2n3 extends Act {} {
	params = (P0->n1 + P1->n3 + P2->n1 + P3->n2 + P4->n3)
}
one sig Forwardn3n3n3n1n2 extends Act {} {
	params = (P0->n3 + P1->n3 + P2->n3 + P3->n1 + P4->n2)
}
one sig Forwardn2n1n2n2n1 extends Act {} {
	params = (P0->n2 + P1->n1 + P2->n2 + P3->n2 + P4->n1)
}
one sig Forwardn2n2n3n1n3 extends Act {} {
	params = (P0->n2 + P1->n2 + P2->n3 + P3->n1 + P4->n3)
}
one sig Forwardn2n1n2n2n3 extends Act {} {
	params = (P0->n2 + P1->n1 + P2->n2 + P3->n2 + P4->n3)
}
one sig Forwardn2n2n3n1n2 extends Act {} {
	params = (P0->n2 + P1->n2 + P2->n3 + P3->n1 + P4->n2)
}
one sig Forwardn2n1n2n2n2 extends Act {} {
	params = (P0->n2 + P1->n1 + P2->n2 + P3->n2 + P4->n2)
}
one sig Forwardn2n2n3n1n1 extends Act {} {
	params = (P0->n2 + P1->n2 + P2->n3 + P3->n1 + P4->n1)
}
one sig Forwardn1n3n1n2n1 extends Act {} {
	params = (P0->n1 + P1->n3 + P2->n1 + P3->n2 + P4->n1)
}
one sig Forwardn3n3n3n2n1 extends Act {} {
	params = (P0->n3 + P1->n3 + P2->n3 + P3->n2 + P4->n1)
}
one sig Forwardn3n2n2n3n2 extends Act {} {
	params = (P0->n3 + P1->n2 + P2->n2 + P3->n3 + P4->n2)
}
one sig Forwardn3n2n1n1n1 extends Act {} {
	params = (P0->n3 + P1->n2 + P2->n1 + P3->n1 + P4->n1)
}
one sig Forwardn3n2n2n3n1 extends Act {} {
	params = (P0->n3 + P1->n2 + P2->n2 + P3->n3 + P4->n1)
}
one sig Forwardn1n3n1n1n3 extends Act {} {
	params = (P0->n1 + P1->n3 + P2->n1 + P3->n1 + P4->n3)
}
one sig Forwardn3n2n1n1n3 extends Act {} {
	params = (P0->n3 + P1->n2 + P2->n1 + P3->n1 + P4->n3)
}
one sig Forwardn3n2n2n3n3 extends Act {} {
	params = (P0->n3 + P1->n2 + P2->n2 + P3->n3 + P4->n3)
}
one sig Forwardn3n2n1n1n2 extends Act {} {
	params = (P0->n3 + P1->n2 + P2->n1 + P3->n1 + P4->n2)
}
one sig Forwardn1n3n2n3n2 extends Act {} {
	params = (P0->n1 + P1->n3 + P2->n2 + P3->n3 + P4->n2)
}
one sig Forwardn1n3n1n1n1 extends Act {} {
	params = (P0->n1 + P1->n3 + P2->n1 + P3->n1 + P4->n1)
}
one sig Forwardn3n3n3n2n2 extends Act {} {
	params = (P0->n3 + P1->n3 + P2->n3 + P3->n2 + P4->n2)
}
one sig Forwardn1n3n2n3n3 extends Act {} {
	params = (P0->n1 + P1->n3 + P2->n2 + P3->n3 + P4->n3)
}
one sig Forwardn1n3n1n1n2 extends Act {} {
	params = (P0->n1 + P1->n3 + P2->n1 + P3->n1 + P4->n2)
}
one sig Forwardn3n3n3n2n3 extends Act {} {
	params = (P0->n3 + P1->n3 + P2->n3 + P3->n2 + P4->n3)
}
one sig Forwardn2n1n2n3n2 extends Act {} {
	params = (P0->n2 + P1->n1 + P2->n2 + P3->n3 + P4->n2)
}
one sig Forwardn2n2n3n2n1 extends Act {} {
	params = (P0->n2 + P1->n2 + P2->n3 + P3->n2 + P4->n1)
}
one sig Forwardn2n1n1n1n1 extends Act {} {
	params = (P0->n2 + P1->n1 + P2->n1 + P3->n1 + P4->n1)
}
one sig Forwardn2n1n2n3n1 extends Act {} {
	params = (P0->n2 + P1->n1 + P2->n2 + P3->n3 + P4->n1)
}
one sig Forwardn2n2n3n2n3 extends Act {} {
	params = (P0->n2 + P1->n2 + P2->n3 + P3->n2 + P4->n3)
}
one sig Forwardn2n1n1n1n3 extends Act {} {
	params = (P0->n2 + P1->n1 + P2->n1 + P3->n1 + P4->n3)
}
one sig Forwardn2n1n2n3n3 extends Act {} {
	params = (P0->n2 + P1->n1 + P2->n2 + P3->n3 + P4->n3)
}
one sig Forwardn2n2n3n2n2 extends Act {} {
	params = (P0->n2 + P1->n2 + P2->n3 + P3->n2 + P4->n2)
}
one sig Forwardn2n1n1n1n2 extends Act {} {
	params = (P0->n2 + P1->n1 + P2->n1 + P3->n1 + P4->n2)
}
one sig Forwardn1n3n2n3n1 extends Act {} {
	params = (P0->n1 + P1->n3 + P2->n2 + P3->n3 + P4->n1)
}
one sig Forwardn3n3n3n3n1 extends Act {} {
	params = (P0->n3 + P1->n3 + P2->n3 + P3->n3 + P4->n1)
}
one sig Forwardn3n3n3n3n2 extends Act {} {
	params = (P0->n3 + P1->n3 + P2->n3 + P3->n3 + P4->n2)
}
one sig Forwardn3n3n2n1n1 extends Act {} {
	params = (P0->n3 + P1->n3 + P2->n2 + P3->n1 + P4->n1)
}
one sig Forwardn3n2n1n2n2 extends Act {} {
	params = (P0->n3 + P1->n2 + P2->n1 + P3->n2 + P4->n2)
}
one sig Forwardn3n2n1n2n1 extends Act {} {
	params = (P0->n3 + P1->n2 + P2->n1 + P3->n2 + P4->n1)
}
one sig Forwardn1n3n2n2n3 extends Act {} {
	params = (P0->n1 + P1->n3 + P2->n2 + P3->n2 + P4->n3)
}
one sig Forwardn1n2n1n3n3 extends Act {} {
	params = (P0->n1 + P1->n2 + P2->n1 + P3->n3 + P4->n3)
}
one sig Forwardn3n2n1n2n3 extends Act {} {
	params = (P0->n3 + P1->n2 + P2->n1 + P3->n2 + P4->n3)
}
one sig Forwardn1n2n1n3n2 extends Act {} {
	params = (P0->n1 + P1->n2 + P2->n1 + P3->n3 + P4->n2)
}
one sig Forwardn1n3n2n2n1 extends Act {} {
	params = (P0->n1 + P1->n3 + P2->n2 + P3->n2 + P4->n1)
}
one sig Forwardn3n3n3n3n3 extends Act {} {
	params = (P0->n3 + P1->n3 + P2->n3 + P3->n3 + P4->n3)
}
one sig Forwardn3n3n2n1n2 extends Act {} {
	params = (P0->n3 + P1->n3 + P2->n2 + P3->n1 + P4->n2)
}
one sig Forwardn1n3n2n2n2 extends Act {} {
	params = (P0->n1 + P1->n3 + P2->n2 + P3->n2 + P4->n2)
}
one sig Forwardn3n3n2n1n3 extends Act {} {
	params = (P0->n3 + P1->n3 + P2->n2 + P3->n1 + P4->n3)
}
one sig Forwardn1n1n3n1n2 extends Act {} {
	params = (P0->n1 + P1->n1 + P2->n3 + P3->n1 + P4->n2)
}
one sig Forwardn1n1n3n1n1 extends Act {} {
	params = (P0->n1 + P1->n1 + P2->n3 + P3->n1 + P4->n1)
}
one sig Forwardn1n1n3n1n3 extends Act {} {
	params = (P0->n1 + P1->n1 + P2->n3 + P3->n1 + P4->n3)
}
one sig Forwardn3n1n3n2n1 extends Act {} {
	params = (P0->n3 + P1->n1 + P2->n3 + P3->n2 + P4->n1)
}
one sig Forwardn3n1n3n2n3 extends Act {} {
	params = (P0->n3 + P1->n1 + P2->n3 + P3->n2 + P4->n3)
}
one sig Forwardn3n1n3n2n2 extends Act {} {
	params = (P0->n3 + P1->n1 + P2->n3 + P3->n2 + P4->n2)
}
one sig Forwardn3n1n3n3n2 extends Act {} {
	params = (P0->n3 + P1->n1 + P2->n3 + P3->n3 + P4->n2)
}
one sig Forwardn3n1n2n1n1 extends Act {} {
	params = (P0->n3 + P1->n1 + P2->n2 + P3->n1 + P4->n1)
}
one sig Forwardn3n1n3n3n1 extends Act {} {
	params = (P0->n3 + P1->n1 + P2->n3 + P3->n3 + P4->n1)
}
one sig Forwardn3n1n2n1n3 extends Act {} {
	params = (P0->n3 + P1->n1 + P2->n2 + P3->n1 + P4->n3)
}
one sig Forwardn3n1n3n3n3 extends Act {} {
	params = (P0->n3 + P1->n1 + P2->n3 + P3->n3 + P4->n3)
}
one sig Forwardn3n1n2n1n2 extends Act {} {
	params = (P0->n3 + P1->n1 + P2->n2 + P3->n1 + P4->n2)
}
one sig Forwardn3n2n3n1n1 extends Act {} {
	params = (P0->n3 + P1->n2 + P2->n3 + P3->n1 + P4->n1)
}
one sig Forwardn3n1n2n2n2 extends Act {} {
	params = (P0->n3 + P1->n1 + P2->n2 + P3->n2 + P4->n2)
}
one sig Forwardn3n1n2n2n1 extends Act {} {
	params = (P0->n3 + P1->n1 + P2->n2 + P3->n2 + P4->n1)
}
one sig Forwardn3n2n3n1n3 extends Act {} {
	params = (P0->n3 + P1->n2 + P2->n3 + P3->n1 + P4->n3)
}
one sig Forwardn3n2n3n1n2 extends Act {} {
	params = (P0->n3 + P1->n2 + P2->n3 + P3->n1 + P4->n2)
}
one sig Forwardn3n1n2n2n3 extends Act {} {
	params = (P0->n3 + P1->n1 + P2->n2 + P3->n2 + P4->n3)
}
one sig Forwardn2n1n3n1n3 extends Act {} {
	params = (P0->n2 + P1->n1 + P2->n3 + P3->n1 + P4->n3)
}
one sig Forwardn2n1n3n1n2 extends Act {} {
	params = (P0->n2 + P1->n1 + P2->n3 + P3->n1 + P4->n2)
}
one sig Forwardn2n1n3n1n1 extends Act {} {
	params = (P0->n2 + P1->n1 + P2->n3 + P3->n1 + P4->n1)
}
one sig Forwardn3n1n2n3n1 extends Act {} {
	params = (P0->n3 + P1->n1 + P2->n2 + P3->n3 + P4->n1)
}
one sig Forwardn3n2n3n2n2 extends Act {} {
	params = (P0->n3 + P1->n2 + P2->n3 + P3->n2 + P4->n2)
}
one sig Forwardn3n1n1n1n2 extends Act {} {
	params = (P0->n3 + P1->n1 + P2->n1 + P3->n1 + P4->n2)
}
one sig Forwardn3n1n2n3n3 extends Act {} {
	params = (P0->n3 + P1->n1 + P2->n2 + P3->n3 + P4->n3)
}
one sig Forwardn3n2n3n2n1 extends Act {} {
	params = (P0->n3 + P1->n2 + P2->n3 + P3->n2 + P4->n1)
}
one sig Forwardn3n1n1n1n1 extends Act {} {
	params = (P0->n3 + P1->n1 + P2->n1 + P3->n1 + P4->n1)
}
one sig Forwardn3n1n2n3n2 extends Act {} {
	params = (P0->n3 + P1->n1 + P2->n2 + P3->n3 + P4->n2)
}
one sig Forwardn3n2n3n2n3 extends Act {} {
	params = (P0->n3 + P1->n2 + P2->n3 + P3->n2 + P4->n3)
}
one sig Forwardn3n1n1n1n3 extends Act {} {
	params = (P0->n3 + P1->n1 + P2->n1 + P3->n1 + P4->n3)
}
one sig Forwardn2n2n1n3n3 extends Act {} {
	params = (P0->n2 + P1->n2 + P2->n1 + P3->n3 + P4->n3)
}
one sig Forwardn2n2n1n3n2 extends Act {} {
	params = (P0->n2 + P1->n2 + P2->n1 + P3->n3 + P4->n2)
}
one sig Forwardn2n2n1n3n1 extends Act {} {
	params = (P0->n2 + P1->n2 + P2->n1 + P3->n3 + P4->n1)
}
one sig Forwardn2n3n2n2n1 extends Act {} {
	params = (P0->n2 + P1->n3 + P2->n2 + P3->n2 + P4->n1)
}
one sig Forwardn2n3n2n2n2 extends Act {} {
	params = (P0->n2 + P1->n3 + P2->n2 + P3->n2 + P4->n2)
}
one sig Forwardn2n3n2n2n3 extends Act {} {
	params = (P0->n2 + P1->n3 + P2->n2 + P3->n2 + P4->n3)
}
one sig Forwardn1n2n3n2n3 extends Act {} {
	params = (P0->n1 + P1->n2 + P2->n3 + P3->n2 + P4->n3)
}
one sig Forwardn1n1n1n1n3 extends Act {} {
	params = (P0->n1 + P1->n1 + P2->n1 + P3->n1 + P4->n3)
}
one sig Forwardn1n1n2n3n1 extends Act {} {
	params = (P0->n1 + P1->n1 + P2->n2 + P3->n3 + P4->n1)
}
one sig Forwardn1n1n2n3n3 extends Act {} {
	params = (P0->n1 + P1->n1 + P2->n2 + P3->n3 + P4->n3)
}
one sig Forwardn1n2n3n2n2 extends Act {} {
	params = (P0->n1 + P1->n2 + P2->n3 + P3->n2 + P4->n2)
}
one sig Forwardn1n1n1n1n2 extends Act {} {
	params = (P0->n1 + P1->n1 + P2->n1 + P3->n1 + P4->n2)
}
one sig Forwardn1n1n2n3n2 extends Act {} {
	params = (P0->n1 + P1->n1 + P2->n2 + P3->n3 + P4->n2)
}
one sig Forwardn1n2n3n2n1 extends Act {} {
	params = (P0->n1 + P1->n2 + P2->n3 + P3->n2 + P4->n1)
}
one sig Forwardn1n1n1n1n1 extends Act {} {
	params = (P0->n1 + P1->n1 + P2->n1 + P3->n1 + P4->n1)
}
one sig Forwardn2n3n2n3n1 extends Act {} {
	params = (P0->n2 + P1->n3 + P2->n2 + P3->n3 + P4->n1)
}
one sig Forwardn2n3n2n3n2 extends Act {} {
	params = (P0->n2 + P1->n3 + P2->n2 + P3->n3 + P4->n2)
}
one sig Forwardn2n3n1n1n1 extends Act {} {
	params = (P0->n2 + P1->n3 + P2->n1 + P3->n1 + P4->n1)
}
one sig Forwardn2n3n2n3n3 extends Act {} {
	params = (P0->n2 + P1->n3 + P2->n2 + P3->n3 + P4->n3)
}
one sig Forwardn2n3n1n1n2 extends Act {} {
	params = (P0->n2 + P1->n3 + P2->n1 + P3->n1 + P4->n2)
}
one sig Forwardn2n3n1n1n3 extends Act {} {
	params = (P0->n2 + P1->n3 + P2->n1 + P3->n1 + P4->n3)
}
one sig Forwardn1n2n3n1n3 extends Act {} {
	params = (P0->n1 + P1->n2 + P2->n3 + P3->n1 + P4->n3)
}
one sig Forwardn1n1n2n2n3 extends Act {} {
	params = (P0->n1 + P1->n1 + P2->n2 + P3->n2 + P4->n3)
}
one sig Forwardn1n2n3n1n2 extends Act {} {
	params = (P0->n1 + P1->n2 + P2->n3 + P3->n1 + P4->n2)
}
one sig Forwardn1n1n2n2n2 extends Act {} {
	params = (P0->n1 + P1->n1 + P2->n2 + P3->n2 + P4->n2)
}
one sig Forwardn1n2n3n1n1 extends Act {} {
	params = (P0->n1 + P1->n2 + P2->n3 + P3->n1 + P4->n1)
}
one sig Forwardn1n1n2n2n1 extends Act {} {
	params = (P0->n1 + P1->n1 + P2->n2 + P3->n2 + P4->n1)
}
one sig Forwardn2n3n1n2n1 extends Act {} {
	params = (P0->n2 + P1->n3 + P2->n1 + P3->n2 + P4->n1)
}
one sig Forwardn2n3n1n2n2 extends Act {} {
	params = (P0->n2 + P1->n3 + P2->n1 + P3->n2 + P4->n2)
}
one sig Forwardn2n3n1n2n3 extends Act {} {
	params = (P0->n2 + P1->n3 + P2->n1 + P3->n2 + P4->n3)
}
one sig Forwardn1n1n2n1n3 extends Act {} {
	params = (P0->n1 + P1->n1 + P2->n2 + P3->n1 + P4->n3)
}
one sig Forwardn1n1n2n1n2 extends Act {} {
	params = (P0->n1 + P1->n1 + P2->n2 + P3->n1 + P4->n2)
}
one sig Forwardn1n1n3n3n3 extends Act {} {
	params = (P0->n1 + P1->n1 + P2->n3 + P3->n3 + P4->n3)
}
one sig Forwardn1n1n2n1n1 extends Act {} {
	params = (P0->n1 + P1->n1 + P2->n2 + P3->n1 + P4->n1)
}
one sig Forwardn1n1n3n3n2 extends Act {} {
	params = (P0->n1 + P1->n1 + P2->n3 + P3->n3 + P4->n2)
}
one sig Forwardn1n1n3n3n1 extends Act {} {
	params = (P0->n1 + P1->n1 + P2->n3 + P3->n3 + P4->n1)
}
one sig Forwardn2n3n1n3n1 extends Act {} {
	params = (P0->n2 + P1->n3 + P2->n1 + P3->n3 + P4->n1)
}
one sig Forwardn2n3n1n3n2 extends Act {} {
	params = (P0->n2 + P1->n3 + P2->n1 + P3->n3 + P4->n2)
}
one sig Forwardn2n3n1n3n3 extends Act {} {
	params = (P0->n2 + P1->n3 + P2->n1 + P3->n3 + P4->n3)
}
one sig Forwardn1n1n3n2n3 extends Act {} {
	params = (P0->n1 + P1->n1 + P2->n3 + P3->n2 + P4->n3)
}
one sig Forwardn1n1n3n2n2 extends Act {} {
	params = (P0->n1 + P1->n1 + P2->n3 + P3->n2 + P4->n2)
}
one sig Forwardn3n1n3n1n2 extends Act {} {
	params = (P0->n3 + P1->n1 + P2->n3 + P3->n1 + P4->n2)
}
one sig Forwardn1n1n3n2n1 extends Act {} {
	params = (P0->n1 + P1->n1 + P2->n3 + P3->n2 + P4->n1)
}
one sig Forwardn3n1n3n1n1 extends Act {} {
	params = (P0->n3 + P1->n1 + P2->n3 + P3->n1 + P4->n1)
}
one sig Forwardn3n1n3n1n3 extends Act {} {
	params = (P0->n3 + P1->n1 + P2->n3 + P3->n1 + P4->n3)
}
one sig Forwardn2n2n3n3n2 extends Act {} {
	params = (P0->n2 + P1->n2 + P2->n3 + P3->n3 + P4->n2)
}
one sig Forwardn2n1n1n2n2 extends Act {} {
	params = (P0->n2 + P1->n1 + P2->n1 + P3->n2 + P4->n2)
}
one sig Forwardn2n2n2n1n1 extends Act {} {
	params = (P0->n2 + P1->n2 + P2->n2 + P3->n1 + P4->n1)
}
one sig Forwardn2n2n3n3n1 extends Act {} {
	params = (P0->n2 + P1->n2 + P2->n3 + P3->n3 + P4->n1)
}
one sig Forwardn2n1n1n2n1 extends Act {} {
	params = (P0->n2 + P1->n1 + P2->n1 + P3->n2 + P4->n1)
}
one sig Forwardn2n2n2n1n3 extends Act {} {
	params = (P0->n2 + P1->n2 + P2->n2 + P3->n1 + P4->n3)
}
one sig Forwardn2n2n3n3n3 extends Act {} {
	params = (P0->n2 + P1->n2 + P2->n3 + P3->n3 + P4->n3)
}
one sig Forwardn2n1n1n2n3 extends Act {} {
	params = (P0->n2 + P1->n1 + P2->n1 + P3->n2 + P4->n3)
}
one sig Forwardn2n2n2n1n2 extends Act {} {
	params = (P0->n2 + P1->n2 + P2->n2 + P3->n1 + P4->n2)
}
one sig Forwardn1n2n1n3n1 extends Act {} {
	params = (P0->n1 + P1->n2 + P2->n1 + P3->n3 + P4->n1)
}
one sig Forwardn3n2n1n3n1 extends Act {} {
	params = (P0->n3 + P1->n2 + P2->n1 + P3->n3 + P4->n1)
}
one sig Forwardn3n3n2n2n1 extends Act {} {
	params = (P0->n3 + P1->n3 + P2->n2 + P3->n2 + P4->n1)
}
one sig Forwardn3n3n2n2n2 extends Act {} {
	params = (P0->n3 + P1->n3 + P2->n2 + P3->n2 + P4->n2)
}
one sig Forwardn3n2n1n3n3 extends Act {} {
	params = (P0->n3 + P1->n2 + P2->n1 + P3->n3 + P4->n3)
}
one sig Forwardn3n2n1n3n2 extends Act {} {
	params = (P0->n3 + P1->n2 + P2->n1 + P3->n3 + P4->n2)
}
one sig Forwardn1n3n2n1n2 extends Act {} {
	params = (P0->n1 + P1->n3 + P2->n2 + P3->n1 + P4->n2)
}
one sig Forwardn1n2n1n2n2 extends Act {} {
	params = (P0->n1 + P1->n2 + P2->n1 + P3->n2 + P4->n2)
}
one sig Forwardn1n3n3n3n3 extends Act {} {
	params = (P0->n1 + P1->n3 + P2->n3 + P3->n3 + P4->n3)
}
one sig Forwardn1n3n2n1n3 extends Act {} {
	params = (P0->n1 + P1->n3 + P2->n2 + P3->n1 + P4->n3)
}
one sig Forwardn1n2n1n2n1 extends Act {} {
	params = (P0->n1 + P1->n2 + P2->n1 + P3->n2 + P4->n1)
}
one sig Forwardn3n3n2n2n3 extends Act {} {
	params = (P0->n3 + P1->n3 + P2->n2 + P3->n2 + P4->n3)
}
one sig Forwardn1n3n3n3n1 extends Act {} {
	params = (P0->n1 + P1->n3 + P2->n3 + P3->n3 + P4->n1)
}
one sig Forwardn1n3n2n1n1 extends Act {} {
	params = (P0->n1 + P1->n3 + P2->n2 + P3->n1 + P4->n1)
}
one sig Forwardn1n2n1n2n3 extends Act {} {
	params = (P0->n1 + P1->n2 + P2->n1 + P3->n2 + P4->n3)
}
one sig Forwardn1n3n3n3n2 extends Act {} {
	params = (P0->n1 + P1->n3 + P2->n3 + P3->n3 + P4->n2)
}
one sig Forwardn2n3n3n1n2 extends Act {} {
	params = (P0->n2 + P1->n3 + P2->n3 + P3->n1 + P4->n2)
}
one sig Forwardn2n1n1n3n3 extends Act {} {
	params = (P0->n2 + P1->n1 + P2->n1 + P3->n3 + P4->n3)
}
one sig Forwardn2n2n2n2n2 extends Act {} {
	params = (P0->n2 + P1->n2 + P2->n2 + P3->n2 + P4->n2)
}
one sig Forwardn2n3n3n1n3 extends Act {} {
	params = (P0->n2 + P1->n3 + P2->n3 + P3->n1 + P4->n3)
}
one sig Forwardn2n1n1n3n2 extends Act {} {
	params = (P0->n2 + P1->n1 + P2->n1 + P3->n3 + P4->n2)
}
one sig Forwardn2n2n2n2n1 extends Act {} {
	params = (P0->n2 + P1->n2 + P2->n2 + P3->n2 + P4->n1)
}
one sig Forwardn2n1n1n3n1 extends Act {} {
	params = (P0->n2 + P1->n1 + P2->n1 + P3->n3 + P4->n1)
}
one sig Forwardn2n3n3n1n1 extends Act {} {
	params = (P0->n2 + P1->n3 + P2->n3 + P3->n1 + P4->n1)
}
one sig Forwardn2n2n2n2n3 extends Act {} {
	params = (P0->n2 + P1->n2 + P2->n2 + P3->n2 + P4->n3)
}
one sig Forwardn3n3n2n3n2 extends Act {} {
	params = (P0->n3 + P1->n3 + P2->n2 + P3->n3 + P4->n2)
}
one sig Forwardn3n3n1n1n1 extends Act {} {
	params = (P0->n3 + P1->n3 + P2->n1 + P3->n1 + P4->n1)
}
one sig Forwardn3n3n2n3n3 extends Act {} {
	params = (P0->n3 + P1->n3 + P2->n2 + P3->n3 + P4->n3)
}
one sig Forwardn3n3n1n1n2 extends Act {} {
	params = (P0->n3 + P1->n3 + P2->n1 + P3->n1 + P4->n2)
}
one sig Forwardn3n3n2n3n1 extends Act {} {
	params = (P0->n3 + P1->n3 + P2->n2 + P3->n3 + P4->n1)
}
one sig Forwardn1n2n2n3n2 extends Act {} {
	params = (P0->n1 + P1->n2 + P2->n2 + P3->n3 + P4->n2)
}
one sig Forwardn1n2n1n1n1 extends Act {} {
	params = (P0->n1 + P1->n2 + P2->n1 + P3->n1 + P4->n1)
}
one sig Forwardn1n3n3n2n2 extends Act {} {
	params = (P0->n1 + P1->n3 + P2->n3 + P3->n2 + P4->n2)
}
one sig Forwardn1n2n2n3n1 extends Act {} {
	params = (P0->n1 + P1->n2 + P2->n2 + P3->n3 + P4->n1)
}
one sig Forwardn1n3n3n2n3 extends Act {} {
	params = (P0->n1 + P1->n3 + P2->n3 + P3->n2 + P4->n3)
}
one sig Forwardn1n2n1n1n3 extends Act {} {
	params = (P0->n1 + P1->n2 + P2->n1 + P3->n1 + P4->n3)
}
one sig Forwardn3n3n1n1n3 extends Act {} {
	params = (P0->n3 + P1->n3 + P2->n1 + P3->n1 + P4->n3)
}
one sig Forwardn1n2n2n3n3 extends Act {} {
	params = (P0->n1 + P1->n2 + P2->n2 + P3->n3 + P4->n3)
}
one sig Forwardn1n2n1n1n2 extends Act {} {
	params = (P0->n1 + P1->n2 + P2->n1 + P3->n1 + P4->n2)
}
one sig Forwardn1n3n3n2n1 extends Act {} {
	params = (P0->n1 + P1->n3 + P2->n3 + P3->n2 + P4->n1)
}
one sig Forwardn2n2n1n1n2 extends Act {} {
	params = (P0->n2 + P1->n2 + P2->n1 + P3->n1 + P4->n2)
}
one sig Forwardn2n3n3n2n3 extends Act {} {
	params = (P0->n2 + P1->n3 + P2->n3 + P3->n2 + P4->n3)
}
one sig Forwardn2n2n2n3n3 extends Act {} {
	params = (P0->n2 + P1->n2 + P2->n2 + P3->n3 + P4->n3)
}
one sig Forwardn2n2n1n1n1 extends Act {} {
	params = (P0->n2 + P1->n2 + P2->n1 + P3->n1 + P4->n1)
}
one sig Forwardn2n2n2n3n2 extends Act {} {
	params = (P0->n2 + P1->n2 + P2->n2 + P3->n3 + P4->n2)
}
one sig Forwardn2n2n2n3n1 extends Act {} {
	params = (P0->n2 + P1->n2 + P2->n2 + P3->n3 + P4->n1)
}
one sig Forwardn2n3n3n2n1 extends Act {} {
	params = (P0->n2 + P1->n3 + P2->n3 + P3->n2 + P4->n1)
}
one sig Forwardn2n2n1n1n3 extends Act {} {
	params = (P0->n2 + P1->n2 + P2->n1 + P3->n1 + P4->n3)
}
one sig Forwardn2n3n3n2n2 extends Act {} {
	params = (P0->n2 + P1->n3 + P2->n3 + P3->n2 + P4->n2)
}
one sig Forwardn3n3n1n2n2 extends Act {} {
	params = (P0->n3 + P1->n3 + P2->n1 + P3->n2 + P4->n2)
}
one sig Forwardn3n3n1n2n3 extends Act {} {
	params = (P0->n3 + P1->n3 + P2->n1 + P3->n2 + P4->n3)
}
one sig Forwardn1n3n3n1n3 extends Act {} {
	params = (P0->n1 + P1->n3 + P2->n3 + P3->n1 + P4->n3)
}
one sig Forwardn3n3n1n2n1 extends Act {} {
	params = (P0->n3 + P1->n3 + P2->n1 + P3->n2 + P4->n1)
}
one sig Forwardn1n1n1n3n2 extends Act {} {
	params = (P0->n1 + P1->n1 + P2->n1 + P3->n3 + P4->n2)
}
one sig Forwardn1n2n2n2n1 extends Act {} {
	params = (P0->n1 + P1->n2 + P2->n2 + P3->n2 + P4->n1)
}
one sig Forwardn1n3n3n1n1 extends Act {} {
	params = (P0->n1 + P1->n3 + P2->n3 + P3->n1 + P4->n1)
}
one sig Forwardn1n1n1n3n1 extends Act {} {
	params = (P0->n1 + P1->n1 + P2->n1 + P3->n3 + P4->n1)
}
one sig Forwardn1n3n3n1n2 extends Act {} {
	params = (P0->n1 + P1->n3 + P2->n3 + P3->n1 + P4->n2)
}
one sig Forwardn1n2n2n2n3 extends Act {} {
	params = (P0->n1 + P1->n2 + P2->n2 + P3->n2 + P4->n3)
}
one sig Forwardn1n1n1n3n3 extends Act {} {
	params = (P0->n1 + P1->n1 + P2->n1 + P3->n3 + P4->n3)
}
one sig Forwardn1n2n2n2n2 extends Act {} {
	params = (P0->n1 + P1->n2 + P2->n2 + P3->n2 + P4->n2)
}
one sig Forwardn2n2n1n2n3 extends Act {} {
	params = (P0->n2 + P1->n2 + P2->n1 + P3->n2 + P4->n3)
}
one sig Forwardn2n3n2n1n3 extends Act {} {
	params = (P0->n2 + P1->n3 + P2->n2 + P3->n1 + P4->n3)
}
one sig Forwardn2n2n1n2n2 extends Act {} {
	params = (P0->n2 + P1->n2 + P2->n1 + P3->n2 + P4->n2)
}
one sig Forwardn2n2n1n2n1 extends Act {} {
	params = (P0->n2 + P1->n2 + P2->n1 + P3->n2 + P4->n1)
}
one sig Forwardn2n3n3n3n1 extends Act {} {
	params = (P0->n2 + P1->n3 + P2->n3 + P3->n3 + P4->n1)
}
one sig Forwardn2n3n3n3n2 extends Act {} {
	params = (P0->n2 + P1->n3 + P2->n3 + P3->n3 + P4->n2)
}
one sig Forwardn2n3n2n1n1 extends Act {} {
	params = (P0->n2 + P1->n3 + P2->n2 + P3->n1 + P4->n1)
}
one sig Forwardn2n3n3n3n3 extends Act {} {
	params = (P0->n2 + P1->n3 + P2->n3 + P3->n3 + P4->n3)
}
one sig Forwardn2n3n2n1n2 extends Act {} {
	params = (P0->n2 + P1->n3 + P2->n2 + P3->n1 + P4->n2)
}
one sig Forwardn3n3n1n3n3 extends Act {} {
	params = (P0->n3 + P1->n3 + P2->n1 + P3->n3 + P4->n3)
}
one sig Forwardn1n2n2n1n3 extends Act {} {
	params = (P0->n1 + P1->n2 + P2->n2 + P3->n1 + P4->n3)
}
one sig Forwardn3n3n1n3n1 extends Act {} {
	params = (P0->n3 + P1->n3 + P2->n1 + P3->n3 + P4->n1)
}
one sig Forwardn3n3n1n3n2 extends Act {} {
	params = (P0->n3 + P1->n3 + P2->n1 + P3->n3 + P4->n2)
}
one sig Forwardn1n2n3n3n1 extends Act {} {
	params = (P0->n1 + P1->n2 + P2->n3 + P3->n3 + P4->n1)
}
one sig Forwardn1n1n1n2n1 extends Act {} {
	params = (P0->n1 + P1->n1 + P2->n1 + P3->n2 + P4->n1)
}
one sig Forwardn1n2n3n3n3 extends Act {} {
	params = (P0->n1 + P1->n2 + P2->n3 + P3->n3 + P4->n3)
}
one sig Forwardn1n1n1n2n3 extends Act {} {
	params = (P0->n1 + P1->n1 + P2->n1 + P3->n2 + P4->n3)
}
one sig Forwardn1n2n2n1n2 extends Act {} {
	params = (P0->n1 + P1->n2 + P2->n2 + P3->n1 + P4->n2)
}
one sig Forwardn1n2n3n3n2 extends Act {} {
	params = (P0->n1 + P1->n2 + P2->n3 + P3->n3 + P4->n2)
}
one sig Forwardn1n1n1n2n2 extends Act {} {
	params = (P0->n1 + P1->n1 + P2->n1 + P3->n2 + P4->n2)
}
one sig Forwardn1n2n2n1n1 extends Act {} {
	params = (P0->n1 + P1->n2 + P2->n2 + P3->n1 + P4->n1)
}


one sig T0, T1, T2 extends Idx {}

fact {
	IdxOrder/first = T0
	IdxOrder/next = T0->T1 + T1->T2

}


fun envVarTypes : set(Var->Sort) {
	var1->Node + var0->Node
}


one sig var1, var0 extends Var {} {}


one sig var0ton3var1ton1 extends Env {} {}
one sig var0ton2var1ton2 extends Env {} {}
one sig var1ton3var0ton1 extends Env {} {}
one sig var0ton3 extends Env {} {}
one sig var0ton3var1ton2 extends Env {} {}
one sig var1ton3var0ton2 extends Env {} {}
one sig var0ton1var1ton1 extends Env {} {}
one sig var0ton2 extends Env {} {}
one sig var0ton1 extends Env {} {}
one sig var0ton3var1ton3 extends Env {} {}
one sig var0ton2var1ton1 extends Env {} {}
one sig var1ton2var0ton1 extends Env {} {}


fact PartialInstance {
	lastIdx = (EmptyTrace->T0) + (PT1->T2) + (NT->T1)

	path = (PT1 -> (T0->Forwardn1n2n1n1n3 + T1->Forwardn1n2n1n2n1 + T2->Forwardn1n2n1n1n3)) +
		(NT -> (T0->Forwardn3n2n2n1n3 + T1->Forwardn3n1n1n2n1))

	maps = var0ton3var1ton1->(var0->n3 + var1->n1) +
		var0ton2var1ton2->(var0->n2 + var1->n2) +
		var1ton3var0ton1->(var1->n3 + var0->n1) +
		var0ton3->(var0->n3) +
		var0ton3var1ton2->(var0->n3 + var1->n2) +
		var1ton3var0ton2->(var1->n3 + var0->n2) +
		var0ton1var1ton1->(var0->n1 + var1->n1) +
		var0ton2->(var0->n2) +
		var0ton1->(var0->n1) +
		var0ton3var1ton3->(var0->n3 + var1->n3) +
		var0ton2var1ton1->(var0->n2 + var1->n1) +
		var1ton2var0ton1->(var1->n2 + var0->n1)

	baseName = Forwardn1n3n1n3n1->Forward +
		Forwardn1n3n1n3n2->Forward +
		Forwardn1n3n1n3n3->Forward +
		Forwardn2n1n2n1n3->Forward +
		Forwardn2n1n1n3n1->Forward +
		Forwardn2n1n2n1n1->Forward +
		Forwardn2n1n1n3n2->Forward +
		Forwardn2n1n2n1n2->Forward +
		Forwardn2n1n1n3n3->Forward +
		Forwardn3n2n3n3n3->Forward +
		Forwardn3n2n3n3n2->Forward +
		Forwardn3n2n3n3n1->Forward +
		Forwardn2n2n2n2n1->Forward +
		Forwardn2n2n2n2n2->Forward +
		Forwardn2n2n2n2n3->Forward +
		Forwardn2n3n3n1n1->Forward +
		Forwardn2n3n3n1n2->Forward +
		Forwardn2n3n3n1n3->Forward +
		Forwardn1n2n1n1n1->Forward +
		Forwardn1n2n1n1n3->Forward +
		Forwardn1n2n1n1n2->Forward +
		Forwardn3n1n3n1n1->Forward +
		Forwardn3n1n3n1n2->Forward +
		Forwardn3n1n3n1n3->Forward +
		Forwardn2n3n2n3n1->Forward +
		Forwardn2n3n2n3n2->Forward +
		Forwardn2n3n2n3n3->Forward +
		Forwardn3n1n2n3n2->Forward +
		Forwardn3n1n2n3n3->Forward +
		Forwardn3n1n2n3n1->Forward +
		Forwardn1n1n3n3n3->Forward +
		Forwardn1n1n3n3n2->Forward +
		Forwardn1n1n3n3n1->Forward +
		Forwardn2n1n2n2n2->Forward +
		Forwardn2n1n2n2n3->Forward +
		Forwardn2n2n3n1n3->Forward +
		Forwardn2n1n2n2n1->Forward +
		Forwardn2n2n3n1n1->Forward +
		Forwardn2n2n3n1n2->Forward +
		Forwardn3n2n3n2n3->Forward +
		Forwardn3n2n3n2n2->Forward +
		Forwardn3n2n3n2n1->Forward +
		Forwardn2n2n2n3n1->Forward +
		Forwardn2n2n2n3n2->Forward +
		Forwardn2n2n2n3n3->Forward +
		Forwardn3n3n3n3n2->Forward +
		Forwardn3n3n3n3n1->Forward +
		Forwardn2n3n3n2n1->Forward +
		Forwardn3n3n3n3n3->Forward +
		Forwardn2n3n3n2n2->Forward +
		Forwardn2n3n3n2n3->Forward +
		Forwardn3n1n3n2n1->Forward +
		Forwardn3n1n3n2n2->Forward +
		Forwardn3n1n3n2n3->Forward +
		Forwardn1n3n1n1n3->Forward +
		Forwardn2n1n2n3n3->Forward +
		Forwardn2n1n2n3n1->Forward +
		Forwardn2n1n2n3n2->Forward +
		Forwardn2n2n3n2n2->Forward +
		Forwardn2n2n3n2n3->Forward +
		Forwardn2n2n3n2n1->Forward +
		Forwardn3n2n3n1n2->Forward +
		Forwardn3n2n3n1n3->Forward +
		Forwardn1n3n1n1n1->Forward +
		Forwardn1n3n1n1n2->Forward +
		Forwardn3n2n3n1n1->Forward +
		Forwardn3n2n2n3n1->Forward +
		Forwardn3n2n2n3n2->Forward +
		Forwardn3n2n2n3n3->Forward +
		Forwardn1n2n2n1n1->Forward +
		Forwardn1n2n2n1n2->Forward +
		Forwardn1n2n2n1n3->Forward +
		Forwardn1n1n1n2n3->Forward +
		Forwardn1n1n1n2n2->Forward +
		Forwardn1n1n1n2n1->Forward +
		Forwardn3n3n3n2n3->Forward +
		Forwardn3n3n3n2n2->Forward +
		Forwardn2n3n3n3n1->Forward +
		Forwardn2n3n3n3n2->Forward +
		Forwardn2n3n3n3n3->Forward +
		Forwardn3n3n3n2n1->Forward +
		Forwardn1n2n1n3n1->Forward +
		Forwardn1n2n1n3n3->Forward +
		Forwardn1n2n1n3n2->Forward +
		Forwardn3n1n2n1n1->Forward +
		Forwardn3n1n2n1n2->Forward +
		Forwardn3n1n2n1n3->Forward +
		Forwardn1n3n2n2n3->Forward +
		Forwardn1n3n2n2n1->Forward +
		Forwardn1n3n2n2n2->Forward +
		Forwardn1n3n1n2n2->Forward +
		Forwardn1n3n1n2n3->Forward +
		Forwardn2n2n3n3n1->Forward +
		Forwardn2n2n3n3n2->Forward +
		Forwardn3n1n1n3n1->Forward +
		Forwardn3n1n1n3n2->Forward +
		Forwardn3n1n1n3n3->Forward +
		Forwardn2n2n3n3n3->Forward +
		Forwardn1n3n1n2n1->Forward +
		Forwardn3n2n2n2n1->Forward +
		Forwardn3n2n2n2n2->Forward +
		Forwardn3n2n2n2n3->Forward +
		Forwardn1n1n1n1n3->Forward +
		Forwardn1n1n1n1n2->Forward +
		Forwardn1n1n1n1n1->Forward +
		Forwardn3n3n3n1n3->Forward +
		Forwardn3n3n3n1n2->Forward +
		Forwardn1n2n1n2n2->Forward +
		Forwardn3n3n3n1n1->Forward +
		Forwardn1n2n1n2n1->Forward +
		Forwardn1n2n1n2n3->Forward +
		Forwardn1n3n2n1n1->Forward +
		Forwardn3n3n2n3n3->Forward +
		Forwardn3n3n2n3n2->Forward +
		Forwardn3n3n2n3n1->Forward +
		Forwardn2n1n3n3n1->Forward +
		Forwardn2n1n3n3n2->Forward +
		Forwardn2n1n3n3n3->Forward +
		Forwardn3n1n2n2n3->Forward +
		Forwardn3n1n2n2n1->Forward +
		Forwardn3n1n2n2n2->Forward +
		Forwardn1n3n2n1n2->Forward +
		Forwardn1n3n2n1n3->Forward +
		Forwardn1n1n2n2n3->Forward +
		Forwardn3n1n1n2n1->Forward +
		Forwardn2n3n1n2n1->Forward +
		Forwardn2n3n1n2n2->Forward +
		Forwardn2n3n1n2n3->Forward +
		Forwardn3n1n1n2n2->Forward +
		Forwardn3n1n1n2n3->Forward +
		Forwardn1n1n2n2n2->Forward +
		Forwardn1n1n2n2n1->Forward +
		Forwardn3n2n2n1n1->Forward +
		Forwardn3n2n2n1n2->Forward +
		Forwardn3n2n2n1n3->Forward +
		Forwardn1n2n3n1n2->Forward +
		Forwardn1n2n3n1n3->Forward +
		Forwardn1n2n2n3n1->Forward +
		Forwardn1n2n3n1n1->Forward +
		Forwardn1n2n2n3n2->Forward +
		Forwardn1n2n2n3n3->Forward +
		Forwardn3n2n1n3n2->Forward +
		Forwardn3n2n1n3n3->Forward +
		Forwardn3n2n1n3n1->Forward +
		Forwardn1n3n3n2n1->Forward +
		Forwardn1n3n3n2n2->Forward +
		Forwardn1n3n3n2n3->Forward +
		Forwardn3n3n2n2n3->Forward +
		Forwardn2n1n3n2n1->Forward +
		Forwardn3n3n2n2n2->Forward +
		Forwardn2n1n3n2n2->Forward +
		Forwardn3n3n2n2n1->Forward +
		Forwardn2n1n3n2n3->Forward +
		Forwardn3n1n1n1n1->Forward +
		Forwardn3n1n1n1n2->Forward +
		Forwardn2n3n1n1n2->Forward +
		Forwardn2n3n1n1n3->Forward +
		Forwardn2n3n1n1n1->Forward +
		Forwardn3n1n1n1n3->Forward +
		Forwardn1n1n2n1n1->Forward +
		Forwardn1n1n2n1n3->Forward +
		Forwardn1n1n2n1n2->Forward +
		Forwardn1n1n1n3n3->Forward +
		Forwardn1n2n2n2n1->Forward +
		Forwardn1n2n2n2n2->Forward +
		Forwardn1n2n2n2n3->Forward +
		Forwardn1n1n1n3n2->Forward +
		Forwardn1n1n1n3n1->Forward +
		Forwardn3n2n1n2n3->Forward +
		Forwardn2n2n1n1n1->Forward +
		Forwardn2n2n1n1n2->Forward +
		Forwardn3n2n1n2n1->Forward +
		Forwardn3n2n1n2n2->Forward +
		Forwardn1n3n3n1n1->Forward +
		Forwardn1n3n3n1n2->Forward +
		Forwardn2n2n1n1n3->Forward +
		Forwardn1n3n3n1n3->Forward +
		Forwardn3n3n2n1n3->Forward +
		Forwardn2n1n3n1n2->Forward +
		Forwardn3n3n2n1n2->Forward +
		Forwardn2n1n3n1n3->Forward +
		Forwardn3n3n2n1n1->Forward +
		Forwardn3n3n1n3n2->Forward +
		Forwardn2n1n3n1n1->Forward +
		Forwardn3n3n1n3n1->Forward +
		Forwardn1n3n2n3n2->Forward +
		Forwardn1n3n2n3n3->Forward +
		Forwardn3n3n1n3n3->Forward +
		Forwardn1n3n2n3n1->Forward +
		Forwardn2n1n1n1n1->Forward +
		Forwardn2n1n1n1n2->Forward +
		Forwardn2n1n1n1n3->Forward +
		Forwardn1n2n3n3n2->Forward +
		Forwardn1n2n3n3n3->Forward +
		Forwardn1n2n3n3n1->Forward +
		Forwardn2n2n1n2n1->Forward +
		Forwardn3n2n1n1n2->Forward +
		Forwardn3n2n1n1n3->Forward +
		Forwardn3n1n3n3n1->Forward +
		Forwardn3n1n3n3n2->Forward +
		Forwardn3n1n3n3n3->Forward +
		Forwardn3n2n1n1n1->Forward +
		Forwardn2n2n1n2n2->Forward +
		Forwardn2n2n1n2n3->Forward +
		Forwardn1n1n3n1n2->Forward +
		Forwardn2n3n2n1n3->Forward +
		Forwardn1n1n3n1n1->Forward +
		Forwardn2n3n2n1n1->Forward +
		Forwardn2n3n2n1n2->Forward +
		Forwardn3n3n1n2n1->Forward +
		Forwardn3n3n1n2n3->Forward +
		Forwardn3n3n1n2n2->Forward +
		Forwardn1n1n3n1n3->Forward +
		Forwardn1n1n2n3n3->Forward +
		Forwardn1n1n2n3n2->Forward +
		Forwardn2n3n1n3n1->Forward +
		Forwardn2n3n1n3n2->Forward +
		Forwardn2n1n1n2n1->Forward +
		Forwardn2n3n1n3n3->Forward +
		Forwardn2n1n1n2n2->Forward +
		Forwardn2n1n1n2n3->Forward +
		Forwardn1n1n2n3n1->Forward +
		Forwardn2n2n2n1n1->Forward +
		Forwardn1n2n3n2n3->Forward +
		Forwardn1n2n3n2n1->Forward +
		Forwardn1n2n3n2n2->Forward +
		Forwardn2n2n2n1n2->Forward +
		Forwardn2n2n2n1n3->Forward +
		Forwardn1n3n3n3n3->Forward +
		Forwardn2n2n1n3n3->Forward +
		Forwardn2n2n1n3n1->Forward +
		Forwardn1n3n3n3n1->Forward +
		Forwardn2n2n1n3n2->Forward +
		Forwardn1n3n3n3n2->Forward +
		Forwardn2n3n2n2n2->Forward +
		Forwardn1n1n3n2n1->Forward +
		Forwardn2n3n2n2n3->Forward +
		Forwardn2n3n2n2n1->Forward +
		Forwardn3n3n1n1n2->Forward +
		Forwardn3n3n1n1n1->Forward +
		Forwardn3n3n1n1n3->Forward +
		Forwardn1n1n3n2n3->Forward +
		Forwardn1n1n3n2n2->Forward
}


one sig NT extends NegTrace {} {}

one sig PT1 extends PosTrace {} {}
