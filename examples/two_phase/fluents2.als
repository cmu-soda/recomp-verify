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
	paramIdxs : set ParamIdx
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

sig Not extends Formula {
	child : Formula
} {
	children = child
}

sig Implies extends Formula {
	left : Formula,
	right : Formula
} {
	children = left + right
}

sig Fluent extends Formula {
    initially : Bool,
    initFl : set BaseName,
    termFl : set BaseName,
	vars : ParamIdx->Var
} {
    no children
    no initFl & termFl
    some initFl + termFl
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

	ParamIdx.(Fluent.vars) in (Forall.var + Exists.var) // approximately: no free variables
	all f : Fluent | (f.vars).Var = (f.initFl.paramIdxs + f.termFl.paramIdxs) // the number of params in each action-var must match the action
	all v1, v2 : Var, p : ParamIdx, f : Fluent | (p->v1 in f.vars and p->v2 in f.vars) implies v1 = v2

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
	all e : Env, i : Idx, f : Not | e->i->f in satisfies iff (e->i->f.child not in satisfies)
	all e : Env, i : Idx, f : Implies | e->i->f in satisfies iff (e->i->f.left in satisfies implies e->i->f.right in satisfies)
	//all e : Env, i : Idx, f : And | e->i->f in satisfies iff (e->i->f.left in satisfies and e->i->f.right in satisfies)
	//all e : Env, i : Idx, f : Or | e->i->f in satisfies iff (e->i->f.left in satisfies or e->i->f.right in satisfies)

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
	a.baseName in f.initFl and (~(f.vars)).(a.params) = e.maps
}

// does this action terminate the fluent?
pred isTermAct[a : Act, e : Env, f : Fluent] {
	a.baseName in f.termFl and (~(f.vars)).(a.params) = e.maps
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
for 7 Formula

one sig P0 extends ParamIdx {}

fact {
	ParamIdxOrder/first = P0
	ParamIdxOrder/next = none->none
}



one sig rm2, rm1 extends Atom {}

one sig RMs extends Sort {} {
	atoms = rm2 + rm1
}

one sig SndAbort extends BaseName {} {
    paramIdxs = P0
}
one sig SndAbortrm1 extends Act {} {
	params = (P0->rm1)
}
one sig SndAbortrm2 extends Act {} {
	params = (P0->rm2)
}

one sig RcvPrepare extends BaseName {} {
    paramIdxs = P0
}
one sig RcvPreparerm1 extends Act {} {
	params = (P0->rm1)
}
one sig RcvPreparerm2 extends Act {} {
	params = (P0->rm2)
}

one sig SndCommit extends BaseName {} {
    paramIdxs = P0
}
one sig SndCommitrm1 extends Act {} {
	params = (P0->rm1)
}
one sig SndCommitrm2 extends Act {} {
	params = (P0->rm2)
}

one sig SndPrepare extends BaseName {} {
    paramIdxs = P0
}
one sig SndPreparerm1 extends Act {} {
	params = (P0->rm1)
}
one sig SndPreparerm2 extends Act {} {
	params = (P0->rm2)
}

one sig RcvAbort extends BaseName {} {
    paramIdxs = P0
}
one sig RcvAbortrm1 extends Act {} {
	params = (P0->rm1)
}
one sig RcvAbortrm2 extends Act {} {
	params = (P0->rm2)
}

one sig RcvCommit extends BaseName {} {
    paramIdxs = P0
}
one sig RcvCommitrm1 extends Act {} {
	params = (P0->rm1)
}
one sig RcvCommitrm2 extends Act {} {
	params = (P0->rm2)
}


one sig T0, T1, T2, T3, T4, T5, T6, T7 extends Idx {}

fact {
	IdxOrder/first = T0
	IdxOrder/next = T0->T1 + T1->T2 + T2->T3 + T3->T4 + T4->T5 + T5->T6 + T6->T7
	no (Fluent.initFl + Fluent.termFl) & (SndPrepare + RcvAbort + RcvCommit)
}


one sig var1, var0 extends Var {} {}


one sig var1torm2var0torm1 extends Env {} {}
one sig var1torm1var0torm2 extends Env {} {}
one sig var0torm2 extends Env {} {}
one sig var1torm1var0torm1 extends Env {} {}
one sig var0torm1 extends Env {} {}
one sig var1torm2var0torm2 extends Env {} {}


fact PartialInstance {
	lastIdx = (EmptyTrace->T0) + (PT2->T4) + (PT4->T4) + (NT->T7) + (PT1->T2) + (PT3->T2)

	path = (PT2 -> (T0->SndPreparerm1 + T1->SndPreparerm2 + T2->RcvPreparerm1 + T3->RcvPreparerm2 + T4->SndCommitrm1)) +
		(PT4 -> (T0->SndPreparerm1 + T1->SndPreparerm2 + T2->RcvPreparerm1 + T3->RcvPreparerm2 + T4->SndAbortrm2)) +
		(NT -> (T0->SndPreparerm1 + T1->SndPreparerm2 + T2->RcvPreparerm1 + T3->SndAbortrm1 + T4->RcvAbortrm1 + T5->RcvPreparerm2 + T6->SndCommitrm2 + T7->RcvCommitrm2)) +
		(PT1 -> (T0->SndAbortrm2 + T1->RcvAbortrm1 + T2->SndAbortrm2)) +
		(PT3 -> (T0->SndPreparerm1 + T1->RcvPreparerm1 + T2->SndAbortrm1))

	maps = var1torm2var0torm1->(var1->rm2 + var0->rm1) +
		var1torm1var0torm2->(var1->rm1 + var0->rm2) +
		var0torm2->(var0->rm2) +
		var1torm1var0torm1->(var1->rm1 + var0->rm1) +
		var0torm1->(var0->rm1) +
		var1torm2var0torm2->(var1->rm2 + var0->rm2)

	baseName = RcvAbortrm1->RcvAbort +
		SndAbortrm2->SndAbort +
		RcvAbortrm2->RcvAbort +
		SndPreparerm2->SndPrepare +
		SndPreparerm1->SndPrepare +
		SndCommitrm1->SndCommit +
		RcvCommitrm2->RcvCommit +
		SndCommitrm2->SndCommit +
		RcvCommitrm1->RcvCommit +
		SndAbortrm1->SndAbort +
		RcvPreparerm2->RcvPrepare +
		RcvPreparerm1->RcvPrepare
}


one sig NT extends NegTrace {} {}

one sig PT1 extends PosTrace {} {}
one sig PT2 extends PosTrace {} {}
one sig PT3 extends PosTrace {} {}
one sig PT4 extends PosTrace {} {}
