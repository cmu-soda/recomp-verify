//4
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

one sig P0 extends ParamIdx {}

fact {
	ParamIdxOrder/first = P0
	ParamIdxOrder/next = none->none
	all f : Fluent | (f.vars.Var = P0)
}



one sig rm2, rm1 extends Atom {}

one sig RMs extends Sort {} {
	atoms = rm2 + rm1
}

one sig SndPrepare extends BaseName {} {
	paramIdxs = P0
	paramTypes = P0->RMs
}
one sig SndPreparerm1 extends Act {} {
	params = (P0->rm1)
}
one sig SndPreparerm2 extends Act {} {
	params = (P0->rm2)
}

one sig SilentAbort extends BaseName {} {
	paramIdxs = P0
	paramTypes = P0->RMs
}
one sig SilentAbortrm1 extends Act {} {
	params = (P0->rm1)
}
one sig SilentAbortrm2 extends Act {} {
	params = (P0->rm2)
}

one sig RcvAbort extends BaseName {} {
	paramIdxs = P0
	paramTypes = P0->RMs
}
one sig RcvAbortrm1 extends Act {} {
	params = (P0->rm1)
}
one sig RcvAbortrm2 extends Act {} {
	params = (P0->rm2)
}

one sig RcvCommit extends BaseName {} {
	paramIdxs = P0
	paramTypes = P0->RMs
}
one sig RcvCommitrm1 extends Act {} {
	params = (P0->rm1)
}
one sig RcvCommitrm2 extends Act {} {
	params = (P0->rm2)
}


one sig T0, T1, T2, T3 extends Idx {}

fact {
	IdxOrder/first = T0
	IdxOrder/next = T0->T1 + T1->T2 + T2->T3
	no (Fluent.initFl + Fluent.termFl).baseName & SilentAbort
}


fun envVarTypes : set(Var->Sort) {
	var1->RMs + var0->RMs
}


one sig var1, var0 extends Var {} {}


one sig var1torm2var0torm1 extends Env {} {}
one sig var1torm1var0torm2 extends Env {} {}
one sig var0torm2 extends Env {} {}
one sig var1torm1var0torm1 extends Env {} {}
one sig var0torm1 extends Env {} {}
one sig var1torm2var0torm2 extends Env {} {}


fact PartialInstance {
	lastIdx = (EmptyTrace->T0) + (PT1->T1) + (PT4->T1) + (PT8->T2) + (PT7->T1) + (PT5->T1) + (PT3->T3) + (PT2->T2) + (NT->T3) + (PT6->T2)

	path = (PT1 -> (T0->RcvAbortrm1 + T1->SilentAbortrm2)) +
		(PT4 -> (T0->SndPreparerm1 + T1->RcvAbortrm1)) +
		(PT8 -> (T0->SndPreparerm1 + T1->RcvAbortrm1 + T2->RcvAbortrm2)) +
		(PT7 -> (T0->RcvAbortrm1 + T1->RcvAbortrm2)) +
		(PT5 -> (T0->SndPreparerm1 + T1->RcvAbortrm2)) +
		(PT3 -> (T0->SndPreparerm1 + T1->SndPreparerm2 + T2->RcvCommitrm1 + T3->RcvCommitrm2)) +
		(PT2 -> (T0->SndPreparerm1 + T1->SndPreparerm2 + T2->RcvCommitrm2)) +
		(NT -> (T0->SndPreparerm1 + T1->SndPreparerm2 + T2->RcvAbortrm1 + T3->RcvCommitrm2)) +
		(PT6 -> (T0->SndPreparerm1 + T1->RcvAbortrm1 + T2->SndPreparerm2))

	maps = var1torm2var0torm1->(var1->rm2 + var0->rm1) +
		var1torm1var0torm2->(var1->rm1 + var0->rm2) +
		var0torm2->(var0->rm2) +
		var1torm1var0torm1->(var1->rm1 + var0->rm1) +
		var0torm1->(var0->rm1) +
		var1torm2var0torm2->(var1->rm2 + var0->rm2)

	baseName = SilentAbortrm1->SilentAbort +
		RcvAbortrm1->RcvAbort +
		SilentAbortrm2->SilentAbort +
		RcvAbortrm2->RcvAbort +
		SndPreparerm2->SndPrepare +
		SndPreparerm1->SndPrepare +
		RcvCommitrm2->RcvCommit +
		RcvCommitrm1->RcvCommit
}


one sig NT extends NegTrace {} {}

one sig PT1 extends PosTrace {} {}
one sig PT2 extends PosTrace {} {}
one sig PT3 extends PosTrace {} {}
one sig PT4 extends PosTrace {} {}
one sig PT5 extends PosTrace {} {}
one sig PT6 extends PosTrace {} {}
one sig PT7 extends PosTrace {} {}
one sig PT8 extends PosTrace {} {}
