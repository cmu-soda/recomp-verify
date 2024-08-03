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
    // 3. t[i] \notin f.termFl and (e |-> t,i-1 |= f)
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

pred isInitAct[a : Act, e : Env, f : Fluent] {
	a.baseName in f.initFl and (~(f.vars)).(a.params) = e.maps
}

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

one sig P0, P1, P2 extends ParamIdx {}

fact {
	ParamIdxOrder/first = P0
	ParamIdxOrder/next = P0->P1 + P1->P2
}



one sig req2, n1, resp2, n2, req1, id2, resp1, id1 extends Atom {}

one sig Response extends Sort {} {
	atoms = resp2 + resp1
}
one sig Node extends Sort {} {
	atoms = n1 + n2
}
one sig DbRequestId extends Sort {} {
	atoms = id2 + id1
}
one sig Request extends Sort {} {
	atoms = req2 + req1
}

one sig ReceiveResponse extends BaseName {} {
	paramIdxs = P0 + P1
}
one sig ReceiveResponsen1resp2 extends Act {} {
	params = (P0->n1 + P1->resp2)
}
one sig ReceiveResponsen1resp1 extends Act {} {
	params = (P0->n1 + P1->resp1)
}
one sig ReceiveResponsen2resp2 extends Act {} {
	params = (P0->n2 + P1->resp2)
}
one sig ReceiveResponsen2resp1 extends Act {} {
	params = (P0->n2 + P1->resp1)
}

one sig ServerProcessRequest extends BaseName {} {
	paramIdxs = P0 + P1 + P2
}
one sig ServerProcessRequestn1req1id2 extends Act {} {
	params = (P0->n1 + P1->req1 + P2->id2)
}
one sig ServerProcessRequestn2req2id2 extends Act {} {
	params = (P0->n2 + P1->req2 + P2->id2)
}
one sig ServerProcessRequestn2req1id1 extends Act {} {
	params = (P0->n2 + P1->req1 + P2->id1)
}
one sig ServerProcessRequestn2req1id2 extends Act {} {
	params = (P0->n2 + P1->req1 + P2->id2)
}
one sig ServerProcessRequestn1req2id1 extends Act {} {
	params = (P0->n1 + P1->req2 + P2->id1)
}
one sig ServerProcessRequestn1req2id2 extends Act {} {
	params = (P0->n1 + P1->req2 + P2->id2)
}
one sig ServerProcessRequestn1req1id1 extends Act {} {
	params = (P0->n1 + P1->req1 + P2->id1)
}
one sig ServerProcessRequestn2req2id1 extends Act {} {
	params = (P0->n2 + P1->req2 + P2->id1)
}

one sig NewRequest extends BaseName {} {
	paramIdxs = P0 + P1
}
one sig NewRequestn1req2 extends Act {} {
	params = (P0->n1 + P1->req2)
}
one sig NewRequestn1req1 extends Act {} {
	params = (P0->n1 + P1->req1)
}
one sig NewRequestn2req2 extends Act {} {
	params = (P0->n2 + P1->req2)
}
one sig NewRequestn2req1 extends Act {} {
	params = (P0->n2 + P1->req1)
}

one sig DbProcessRequest extends BaseName {} {
	paramIdxs = P0 + P1 + P2
}
one sig DbProcessRequestid1req2resp1 extends Act {} {
	params = (P0->id1 + P1->req2 + P2->resp1)
}
one sig DbProcessRequestid1req1resp1 extends Act {} {
	params = (P0->id1 + P1->req1 + P2->resp1)
}
one sig DbProcessRequestid2req2resp1 extends Act {} {
	params = (P0->id2 + P1->req2 + P2->resp1)
}
one sig DbProcessRequestid1req2resp2 extends Act {} {
	params = (P0->id1 + P1->req2 + P2->resp2)
}
one sig DbProcessRequestid1req1resp2 extends Act {} {
	params = (P0->id1 + P1->req1 + P2->resp2)
}
one sig DbProcessRequestid2req2resp2 extends Act {} {
	params = (P0->id2 + P1->req2 + P2->resp2)
}
one sig DbProcessRequestid2req1resp1 extends Act {} {
	params = (P0->id2 + P1->req1 + P2->resp1)
}
one sig DbProcessRequestid2req1resp2 extends Act {} {
	params = (P0->id2 + P1->req1 + P2->resp2)
}


one sig T0, T1, T2, T3 extends Idx {}

fact {
	IdxOrder/first = T0
	IdxOrder/next = T0->T1 + T1->T2 + T2->T3
	no Fluent.initFl & NewRequest
	no Fluent.termFl & NewRequest
}


one sig var2, var1, var0 extends Var {} {}


one sig var1toresp1var0toresp1var2ton1 extends Env {} {}
one sig var0toresp1 extends Env {} {}
one sig var0toresp1var1toresp2var2ton1 extends Env {} {}
one sig var1toresp1var0toresp2var2ton1 extends Env {} {}
one sig var1toresp1var0toresp1var2ton2 extends Env {} {}
one sig var1toresp1var0toresp1 extends Env {} {}
one sig var0toresp1var1toresp2 extends Env {} {}
one sig var1toresp1var0toresp2 extends Env {} {}
one sig var0toresp2var2ton2var1toresp2 extends Env {} {}
one sig var0toresp2var1toresp2 extends Env {} {}
one sig var0toresp2var1toresp2var2ton1 extends Env {} {}
one sig var0toresp1var2ton2var1toresp2 extends Env {} {}
one sig var1toresp1var0toresp2var2ton2 extends Env {} {}
one sig var0toresp2 extends Env {} {}


fact PartialInstance {
	lastIdx = (EmptyTrace->T0) + (PT1->T3) + (NT->T0)

	path = (PT1 -> (T0->NewRequestn1req1 + T1->ServerProcessRequestn1req1id1 + T2->ServerProcessRequestn1req1id2 + T3->DbProcessRequestid2req1resp2)) +
		(NT -> (T0->ReceiveResponsen1resp1))

	maps = var1toresp1var0toresp1var2ton1->(var1->resp1 + var0->resp1 + var2->n1) +
		var0toresp1->(var0->resp1) +
		var0toresp1var1toresp2var2ton1->(var0->resp1 + var1->resp2 + var2->n1) +
		var1toresp1var0toresp2var2ton1->(var1->resp1 + var0->resp2 + var2->n1) +
		var1toresp1var0toresp1var2ton2->(var1->resp1 + var0->resp1 + var2->n2) +
		var1toresp1var0toresp1->(var1->resp1 + var0->resp1) +
		var0toresp1var1toresp2->(var0->resp1 + var1->resp2) +
		var1toresp1var0toresp2->(var1->resp1 + var0->resp2) +
		var0toresp2var2ton2var1toresp2->(var0->resp2 + var2->n2 + var1->resp2) +
		var0toresp2var1toresp2->(var0->resp2 + var1->resp2) +
		var0toresp2var1toresp2var2ton1->(var0->resp2 + var1->resp2 + var2->n1) +
		var0toresp1var2ton2var1toresp2->(var0->resp1 + var2->n2 + var1->resp2) +
		var1toresp1var0toresp2var2ton2->(var1->resp1 + var0->resp2 + var2->n2) +
		var0toresp2->(var0->resp2)

	baseName = DbProcessRequestid1req2resp1->DbProcessRequest +
		DbProcessRequestid1req2resp2->DbProcessRequest +
		NewRequestn1req2->NewRequest +
		NewRequestn1req1->NewRequest +
		DbProcessRequestid1req1resp2->DbProcessRequest +
		DbProcessRequestid2req2resp2->DbProcessRequest +
		DbProcessRequestid1req1resp1->DbProcessRequest +
		DbProcessRequestid2req2resp1->DbProcessRequest +
		ReceiveResponsen1resp1->ReceiveResponse +
		ReceiveResponsen1resp2->ReceiveResponse +
		ReceiveResponsen2resp2->ReceiveResponse +
		ReceiveResponsen2resp1->ReceiveResponse +
		ServerProcessRequestn2req2id1->ServerProcessRequest +
		ServerProcessRequestn2req2id2->ServerProcessRequest +
		ServerProcessRequestn2req1id1->ServerProcessRequest +
		NewRequestn2req1->NewRequest +
		ServerProcessRequestn2req1id2->ServerProcessRequest +
		NewRequestn2req2->NewRequest +
		ServerProcessRequestn1req1id2->ServerProcessRequest +
		ServerProcessRequestn1req2id2->ServerProcessRequest +
		ServerProcessRequestn1req1id1->ServerProcessRequest +
		ServerProcessRequestn1req2id1->ServerProcessRequest +
		DbProcessRequestid2req1resp1->DbProcessRequest +
		DbProcessRequestid2req1resp2->DbProcessRequest
}


one sig NT extends NegTrace {} {}

one sig PT1 extends PosTrace {} {}
