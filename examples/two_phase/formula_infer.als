open util/ordering[Idx]

abstract sig Var {}

abstract sig Atom {}

abstract sig Sort {
	atoms : some Atom
}

// base name for an action
abstract sig BaseName {
	numParams : Int
}

// concrete action
abstract sig Act {
	baseName : one BaseName,
	params : seq Atom
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

sig OnceVar extends Formula {
	baseName : BaseName,
	vars : seq Var
} {
	no children
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
	OnceVar.vars.elems in (Forall.var + Exists.var) // approximately: no free variables
	all f : OnceVar | #(f.vars) = f.baseName.numParams // the number of params in each action must match the action

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
	all e : Env, i : Idx, f : OnceVar | e->i->f in satisfies iff
		((some a : Act | concreteAct[a,e,f] and i->a in path) or (some i' : Idx | i'->i in next and e->i'->f in satisfies))
	all e : Env, i : Idx, f : Forall | e->i->f in satisfies iff
		(all x : f.sort.atoms | some e' : Env | pushEnv[e',e,f.var,x] and e'->i->f.matrix in satisfies)
	all e : Env, i : Idx, f : Exists | e->i->f in satisfies iff
		(some x : f.sort.atoms | some e' : Env | pushEnv[e',e,f.var,x] and e'->i->f.matrix in satisfies)
	all e : Env, i : Idx, f : Root | e->i->f in satisfies iff e->i->f.children in satisfies

	// rule: only one action can happen at a given index
	all a1, a2 : Act, i : Idx | (i->a1 in path and i->a2 in path) implies a1 = a2

	// rule: maps (in each environment) is a function
	all e : Env, v : Var, s,t : Atom | (v->s in e.maps and v->t in e.maps) implies s = t
}

pred concreteAct[a : Act, e : Env, f : OnceVar] {
	f.baseName = a.baseName and
	all j : (f.vars.inds + a.params.inds) |
		let m = f.vars[j]->a.params[j] | some m and m in e.maps
}

pred pushEnv[env', env : Env, v : Var, x : Atom] {
	env'.maps = env.maps + (v->x)
}

fun indices[t : Trace] : set Idx {
	{ i : Idx | t.lastIdx in i.*next }
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
	all nt : NegTrace | EmptyEnv->nt.lastIdx->Root not in nt.satisfies
	EmptyEnv->T0->Root in EmptyTrace.satisfies
	minsome children // smallest formula possible
} for 7 Formula,
1 seq

one sig rm2, rm1 extends Atom {}

one sig RMs extends Sort {} {
	atoms = rm2 + rm1
}

one sig SndAbort extends BaseName {} {
	numParams = 1
}
one sig SndAbortrm1 extends Act {} {
	baseName = SndAbort
	params[0] = rm1
	#params = 1
}
one sig SndAbortrm2 extends Act {} {
	baseName = SndAbort
	params[0] = rm2
	#params = 1
}

one sig RcvPrepare extends BaseName {} {
	numParams = 1
}
one sig RcvPreparerm1 extends Act {} {
	baseName = RcvPrepare
	params[0] = rm1
	#params = 1
}
one sig RcvPreparerm2 extends Act {} {
	baseName = RcvPrepare
	params[0] = rm2
	#params = 1
}

one sig SndCommit extends BaseName {} {
	numParams = 1
}
one sig SndCommitrm1 extends Act {} {
	baseName = SndCommit
	params[0] = rm1
	#params = 1
}
one sig SndCommitrm2 extends Act {} {
	baseName = SndCommit
	params[0] = rm2
	#params = 1
}

one sig SndPrepare extends BaseName {} {
	numParams = 1
}
one sig SndPreparerm1 extends Act {} {
	baseName = SndPrepare
	params[0] = rm1
	#params = 1
}
one sig SndPreparerm2 extends Act {} {
	baseName = SndPrepare
	params[0] = rm2
	#params = 1
}

one sig RcvAbort extends BaseName {} {
	numParams = 1
}
one sig RcvAbortrm1 extends Act {} {
	baseName = RcvAbort
	params[0] = rm1
	#params = 1
}
one sig RcvAbortrm2 extends Act {} {
	baseName = RcvAbort
	params[0] = rm2
	#params = 1
}

one sig RcvCommit extends BaseName {} {
	numParams = 1
}
one sig RcvCommitrm1 extends Act {} {
	baseName = RcvCommit
	params[0] = rm1
	#params = 1
}
one sig RcvCommitrm2 extends Act {} {
	baseName = RcvCommit
	params[0] = rm2
	#params = 1
}


one sig T0, T1, T2, T3, T4, T5, T6, T7 extends Idx {}

fact {
	first = T0
	next = T0->T1 + T1->T2 + T2->T3 + T3->T4 + T4->T5 + T5->T6 + T6->T7
	no OnceVar.baseName & SndPrepare
	no OnceVar.baseName & RcvAbort
	no OnceVar.baseName & RcvCommit
}


one sig var1, var0 extends Var {} {}


one sig var1torm2var0torm1 extends Env {} {
	maps = var1->rm2 + var0->rm1
}
one sig var1torm1 extends Env {} {
	maps = var1->rm1
}
one sig var1torm1var0torm2 extends Env {} {
	maps = var1->rm1 + var0->rm2
}
one sig var1torm2 extends Env {} {
	maps = var1->rm2
}
one sig var0torm2 extends Env {} {
	maps = var0->rm2
}
one sig var1torm1var0torm1 extends Env {} {
	maps = var1->rm1 + var0->rm1
}
one sig var0torm1 extends Env {} {
	maps = var0->rm1
}
one sig var1torm2var0torm2 extends Env {} {
	maps = var1->rm2 + var0->rm2
}


one sig NT extends NegTrace {} {
  lastIdx = T7
  (T0->SndPreparerm1 + T1->SndPreparerm2 + T2->RcvPreparerm1 + T3->SndAbortrm1 + T4->RcvAbortrm1 + T5->RcvPreparerm2 + T6->SndCommitrm2 + T7->RcvCommitrm2) in path
}

one sig PT1 extends PosTrace {} {
  lastIdx = T7
  (T0->SndPreparerm1 + T1->SndPreparerm2 + T2->RcvPreparerm1 + T3->RcvPreparerm2 + T4->SndAbortrm2 + T5->RcvAbortrm1 + T6->RcvAbortrm2 + T7->SndAbortrm2) in path
}
one sig PT2 extends PosTrace {} {
  lastIdx = T4
  (T0->SndPreparerm1 + T1->SndPreparerm2 + T2->RcvPreparerm1 + T3->RcvPreparerm2 + T4->SndCommitrm1) in path
}
