open util/boolean

/* LTS signatures */
abstract sig Act {}

abstract sig State {
	init : Bool,
	error : Bool
}

abstract sig Transition {
	src : State,
	act : Act,
	dst : State
}

// returns all "predecessor" transitions
fun predTransitions[t : Transition] : set Transition {
	{ p : Transition | p.dst = t.src }
}


/* Formula signatures (represented by a DAG) */
abstract sig Formula {
	children : set Formula
}
fact {
	// eliminates cycles in formula nodes
	all f : Formula | f not in f.^children
}

one sig Root extends Formula {} {
	one children
}
fact {
	// all formulas must be a sub-formula of the root
	all f : Formula | f in Root.*children
}

sig Not extends Formula {
	child : Formula
} {
	children = child
}

sig And, Implies, Or extends Formula {
	left : Formula,
	right : Formula
} {
	children = left + right
}

sig OnceAct extends Formula {
	act : Act
} {
	no children
}

sig TT, FF extends Formula {} {
	no children
}


/* formula semantics, i.e. when t |= f, where t is a transition and f is a formula */
one sig Semantics {
	satisfies : set (Transition -> Formula)
} {
	all t : Transition, f : Root | t->f in satisfies iff t->f.children in satisfies
	all t : Transition, f : TT | t->f in satisfies
	all t : Transition, f : FF | t->f not in satisfies
	all t : Transition, f : Not | t->f in satisfies iff (t->f.child not in satisfies)
	all t : Transition, f : And | t->f in satisfies iff (t->f.left in satisfies and t->f.right in satisfies)
	all t : Transition, f : Implies | t->f in satisfies iff (t->f.left in satisfies implies t->f.right in satisfies)
	all t : Transition, f : Or | t->f in satisfies iff (t->f.left in satisfies or t->f.right in satisfies)
	all t : Transition, f : OnceAct | t->f in satisfies iff
		((f.act = t.act) or (some predTransitions[t] and predTransitions[t]->f in satisfies))
}


/* main */
run {
	// find a formula that separates "good" transitions from "bad" ones. we assume that the PI state is a sink,
	// i.e. the PI state has no outgoing transitions.
	all t : Transition | (t.dst.error = False) iff (t->Root in Semantics.satisfies)
	minsome children
} for 10 Formula

one sig SndPrepareXrm1 extends Act {} {}
one sig RcvCommitXrm2 extends Act {} {}
one sig RcvCommitXrm1 extends Act {} {}
one sig SndPrepareXrm2 extends Act {} {}
one sig RcvAbortXrm1 extends Act {} {}
one sig RcvAbortXrm2 extends Act {} {}

one sig PI extends State {} {
	init = False
	error = True
}
one sig S1 extends State {} {
	init = False
	error = False
}
one sig S2 extends State {} {
	init = False
	error = False
}
one sig S3 extends State {} {
	init = False
	error = False
}
one sig S4 extends State {} {
	init = False
	error = False
}
one sig S5 extends State {} {
	init = False
	error = False
}
one sig S6 extends State {} {
	init = False
	error = False
}
one sig S7 extends State {} {
	init = False
	error = False
}
one sig S8 extends State {} {
	init = False
	error = False
}
one sig S9 extends State {} {
	init = True
	error = False
}
one sig S10 extends State {} {
	init = False
	error = False
}
one sig S11 extends State {} {
	init = False
	error = False
}
one sig S12 extends State {} {
	init = False
	error = False
}
one sig S13 extends State {} {
	init = False
	error = False
}
one sig S14 extends State {} {
	init = False
	error = False
}
one sig S15 extends State {} {
	init = False
	error = False
}
one sig S16 extends State {} {
	init = False
	error = False
}

one sig T1 extends Transition {} {
	src = S1
	act = RcvCommitXrm2
	dst = S12
}
one sig T2 extends Transition {} {
	src = S1
	act = RcvCommitXrm1
	dst = PI
}
one sig T3 extends Transition {} {
	src = S1
	act = RcvAbortXrm1
	dst = S4
}
one sig T4 extends Transition {} {
	src = S1
	act = RcvAbortXrm2
	dst = PI
}
one sig T5 extends Transition {} {
	src = S2
	act = RcvCommitXrm2
	dst = S12
}
one sig T6 extends Transition {} {
	src = S2
	act = RcvCommitXrm1
	dst = S2
}
one sig T7 extends Transition {} {
	src = S2
	act = SndPrepareXrm2
	dst = S13
}
one sig T8 extends Transition {} {
	src = S2
	act = RcvAbortXrm1
	dst = S3
}
one sig T9 extends Transition {} {
	src = S2
	act = RcvAbortXrm2
	dst = PI
}
one sig T10 extends Transition {} {
	src = S3
	act = RcvCommitXrm2
	dst = PI
}
one sig T11 extends Transition {} {
	src = S3
	act = RcvCommitXrm1
	dst = S2
}
one sig T12 extends Transition {} {
	src = S3
	act = SndPrepareXrm2
	dst = S5
}
one sig T13 extends Transition {} {
	src = S3
	act = RcvAbortXrm1
	dst = S3
}
one sig T14 extends Transition {} {
	src = S3
	act = RcvAbortXrm2
	dst = S4
}
one sig T15 extends Transition {} {
	src = S4
	act = RcvCommitXrm2
	dst = PI
}
one sig T16 extends Transition {} {
	src = S4
	act = RcvCommitXrm1
	dst = PI
}
one sig T17 extends Transition {} {
	src = S4
	act = RcvAbortXrm1
	dst = S4
}
one sig T18 extends Transition {} {
	src = S4
	act = RcvAbortXrm2
	dst = S4
}
one sig T19 extends Transition {} {
	src = S5
	act = RcvCommitXrm2
	dst = PI
}
one sig T20 extends Transition {} {
	src = S5
	act = RcvCommitXrm1
	dst = S13
}
one sig T21 extends Transition {} {
	src = S5
	act = RcvAbortXrm1
	dst = S5
}
one sig T22 extends Transition {} {
	src = S5
	act = RcvAbortXrm2
	dst = S4
}
one sig T23 extends Transition {} {
	src = S6
	act = RcvCommitXrm2
	dst = S11
}
one sig T24 extends Transition {} {
	src = S6
	act = RcvCommitXrm1
	dst = S2
}
one sig T25 extends Transition {} {
	src = S6
	act = SndPrepareXrm2
	dst = S14
}
one sig T26 extends Transition {} {
	src = S6
	act = RcvAbortXrm1
	dst = S3
}
one sig T27 extends Transition {} {
	src = S6
	act = RcvAbortXrm2
	dst = S10
}
one sig T28 extends Transition {} {
	src = S7
	act = SndPrepareXrm1
	dst = S11
}
one sig T29 extends Transition {} {
	src = S7
	act = RcvCommitXrm2
	dst = S7
}
one sig T30 extends Transition {} {
	src = S7
	act = RcvCommitXrm1
	dst = S12
}
one sig T31 extends Transition {} {
	src = S7
	act = RcvAbortXrm1
	dst = PI
}
one sig T32 extends Transition {} {
	src = S7
	act = RcvAbortXrm2
	dst = S8
}
one sig T33 extends Transition {} {
	src = S8
	act = SndPrepareXrm1
	dst = S10
}
one sig T34 extends Transition {} {
	src = S8
	act = RcvCommitXrm2
	dst = S7
}
one sig T35 extends Transition {} {
	src = S8
	act = RcvCommitXrm1
	dst = PI
}
one sig T36 extends Transition {} {
	src = S8
	act = RcvAbortXrm1
	dst = S4
}
one sig T37 extends Transition {} {
	src = S8
	act = RcvAbortXrm2
	dst = S8
}
one sig T38 extends Transition {} {
	src = S9
	act = SndPrepareXrm1
	dst = S6
}
one sig T39 extends Transition {} {
	src = S9
	act = RcvCommitXrm2
	dst = S7
}
one sig T40 extends Transition {} {
	src = S9
	act = RcvCommitXrm1
	dst = S2
}
one sig T41 extends Transition {} {
	src = S9
	act = SndPrepareXrm2
	dst = S16
}
one sig T42 extends Transition {} {
	src = S9
	act = RcvAbortXrm1
	dst = S3
}
one sig T43 extends Transition {} {
	src = S9
	act = RcvAbortXrm2
	dst = S8
}
one sig T44 extends Transition {} {
	src = S10
	act = RcvCommitXrm2
	dst = S11
}
one sig T45 extends Transition {} {
	src = S10
	act = RcvCommitXrm1
	dst = PI
}
one sig T46 extends Transition {} {
	src = S10
	act = RcvAbortXrm1
	dst = S4
}
one sig T47 extends Transition {} {
	src = S10
	act = RcvAbortXrm2
	dst = S10
}
one sig T48 extends Transition {} {
	src = S11
	act = RcvCommitXrm2
	dst = S11
}
one sig T49 extends Transition {} {
	src = S11
	act = RcvCommitXrm1
	dst = S12
}
one sig T50 extends Transition {} {
	src = S11
	act = RcvAbortXrm1
	dst = PI
}
one sig T51 extends Transition {} {
	src = S11
	act = RcvAbortXrm2
	dst = S10
}
one sig T52 extends Transition {} {
	src = S12
	act = RcvCommitXrm2
	dst = S12
}
one sig T53 extends Transition {} {
	src = S12
	act = RcvCommitXrm1
	dst = S12
}
one sig T54 extends Transition {} {
	src = S12
	act = RcvAbortXrm1
	dst = PI
}
one sig T55 extends Transition {} {
	src = S12
	act = RcvAbortXrm2
	dst = PI
}
one sig T56 extends Transition {} {
	src = S13
	act = RcvCommitXrm2
	dst = S12
}
one sig T57 extends Transition {} {
	src = S13
	act = RcvCommitXrm1
	dst = S13
}
one sig T58 extends Transition {} {
	src = S13
	act = RcvAbortXrm1
	dst = S5
}
one sig T59 extends Transition {} {
	src = S13
	act = RcvAbortXrm2
	dst = PI
}
one sig T60 extends Transition {} {
	src = S14
	act = RcvCommitXrm2
	dst = S11
}
one sig T61 extends Transition {} {
	src = S14
	act = RcvCommitXrm1
	dst = S13
}
one sig T62 extends Transition {} {
	src = S14
	act = RcvAbortXrm1
	dst = S5
}
one sig T63 extends Transition {} {
	src = S14
	act = RcvAbortXrm2
	dst = S10
}
one sig T64 extends Transition {} {
	src = S15
	act = RcvCommitXrm2
	dst = PI
}
one sig T65 extends Transition {} {
	src = S15
	act = RcvCommitXrm1
	dst = S12
}
one sig T66 extends Transition {} {
	src = S15
	act = RcvAbortXrm1
	dst = PI
}
one sig T67 extends Transition {} {
	src = S15
	act = RcvAbortXrm2
	dst = S4
}
one sig T68 extends Transition {} {
	src = S16
	act = SndPrepareXrm1
	dst = S14
}
one sig T69 extends Transition {} {
	src = S16
	act = RcvCommitXrm2
	dst = S7
}
one sig T70 extends Transition {} {
	src = S16
	act = RcvCommitXrm1
	dst = S13
}
one sig T71 extends Transition {} {
	src = S16
	act = RcvAbortXrm1
	dst = S5
}
one sig T72 extends Transition {} {
	src = S16
	act = RcvAbortXrm2
	dst = S8
}

