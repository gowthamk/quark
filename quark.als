open util/ordering[Time] as TO

sig Time {}

sig Commit {}

//one sig InitCommit extends Commit {}

sig Value {
    merge_fn: Value -> Value/*LCA*/ -> Value
}

fact MergeIsTotal {
    all v1,v2,l: Value | one l.(v2.(v1.merge_fn))
}

abstract sig Action {}
one sig NewCommit, Fork, FastFwd, Merge extends Action {}

sig Version {
    createdAt: Time,
    commits: set Commit,
    value: Value, 
    branch: Branch
}
/*one sig Root extends Version {}{
    createdAt = first
    commits = InitCommit
    branch = Master
}*/

sig Branch {
    createdAt: Time,
    mem: Version -> Time,
    head: Version -> Time,
    lca: Branch -> Version -> Time
} {
    all t: prevs[createdAt] | no mem.t
    all t: Time | head.t in mem.t 
    all t: Time | all v: mem.t | v.branch = this 
    all t: (Time - prevs[createdAt])| one head.t 
    all t: prevs[createdAt] | no lca.t
    all t: Time | this.lca.t = head.t
}

fact LCACommutative {
    all b1,b2: Branch | all t: Time | 
        b2.(b1.lca).t = b1.(b2.lca).t
}

one sig Master extends Branch {}

fact MasterIsFirst {
    all b: (Branch - Master) | 
        not b.createdAt = first
}

one sig System {
    vertices: Version -> Time,
    edges: Version -> Version -> Action -> Time,
    branches: Branch -> Time,
} {
    all t: Time | branches.t.mem.t = vertices.t
    all t: Time | all a: Action | edges.t.a in (vertices.t -> vertices.t)
}

pred init [t: Time] {
    no System.edges.t
    System.branches.t = Master
    Master.createdAt = t
    some v:Version {
        v.createdAt = t
        one v.commits
        v.branch = Master
        System.vertices.t = v
        Master.mem.t = v
        Master.head.t = v
    }
}

pred skip[t,t': Time, b: Branch] {
    b.mem.t' = b.mem.t
    b.head.t' = b.head.t
}

pred update_lca[t,t': Time, new_tups: Branch -> Branch -> Version] {
    let symm_tups = {b2, b1: Branch, v: Version | 
    b1 -> b2 -> v in new_tups and not b1 = b2} |
    let new_tups' = new_tups + symm_tups|
    let b1b2s = new_tups'.Version |
    let old_tups = lca.t - (b1b2s -> Version) |
    lca.t' = old_tups + new_tups'
    //lca.t' = lca.t + new_tups'
}

pred commit[t,t': Time] {
    let vrsns = System.vertices.t |
    let cmts = vrsns.commits |
        some c: (Commit - cmts) | some v: (Version - vrsns) |
        some val: Value | some b: System.branches.t {
            let hd = b.head.t {
                v.createdAt = t'
                v.commits = hd.commits + c
                v.value = val
                v.branch = b
                b.mem.t' = b.mem.t + v                
                b.head.t' = v
                /* LCA needs to be updated with the refl tuple */
                update_lca[t,t', b -> b -> v]
                System.vertices.t' = System.vertices.t + v
                System.edges.t' = System.edges.t + hd->v->NewCommit
                System.branches.t' = System.branches.t
                all b': (Branch - b) | skip[t,t',b']
            }
        }
}


pred fork[t,t': Time] {
    let vrsns = System.vertices.t |
    some v: (Version - vrsns) |
    some b: System.branches.t |
    some b': (Branch - System.branches.t) |
    let hd = b.head.t |
    let tups1 = (b -> b' -> hd) + (b' -> b' -> v) |
    let tups2 = {new_b:b', b'':(System.branches.t - b), v':vrsns 
    | v' = b''.(b.lca).t} |
    let new_tups = tups1 + tups2 {
        v.createdAt = t'
        v.commits = hd.commits
        v.value = hd.value
        v.branch = b'
        b'.createdAt = t'
        b'.mem.t' = v
        b'.head.t' = v
        update_lca[t,t',new_tups]
        /*b.(b'.lca).t' = hd
        all b'':(System.branches.t - b) | b'.(b''.lca).t' = b.(b''.lca).t
        all b:(System.branches.t - b') | fork_skip[t,t',b,b']*/
        all b:(System.branches.t - b') | skip[t,t',b]
        System.vertices.t' = System.vertices.t + v
        System.edges.t' = System.edges.t + hd->v->Fork
        System.branches.t' = System.branches.t + b'
    }
}

/*
 * v1 ->* v2
 */
pred ancestor_of[v1,v2: Version, t:Time] {
    let edges = System.edges.t.Action |
    v2 in v1.*edges
}
/*
 * v1 ->* v2 or v2 ->* v1
 */
pred ancestrally_related[v1,v2: Version, t: Time] {
    ancestor_of[v1,v2,t] or ancestor_of[v2,v1,t]
}

pred fastfwd[t,t' : Time] {
    let vrsns = System.vertices.t |
    some v: (Version - vrsns) |
    /*
     * FastFwd'ing b1 by merging b2
     */
    some b1: System.branches.t |
    some b2: (System.branches.t - b1) |
    let hd1 = b1.head.t |
    let hd2 = b2.head.t |
    let lb1b2 = b2.(b1.lca).t |
    let new_tups = (b1 -> b2 -> hd2) + (b1 -> b1 -> v) +
    {b1:b1, b:(System.branches.t - (b1 + b2)), v':b.(b2.lca).t | 
    ancestor_of[b.(b1.lca).t, b.(b2.lca.t), t]} {
        /* hd1 must be same or a fork of L(b1,b2). */
        hd1.commits = lb1b2.commits
        /* hd2 must be ahead of L(b1,b2) */
        some (hd2.commits - lb1b2.commits)
        all b: (System.branches.t - (b1 + b2)) | 
            ancestrally_related[b.(b1.lca).t, b.(b2.lca).t, t]
        v.createdAt = t'
        v.commits = hd2.commits
        v.value = hd2.value
        v.branch = b1
        b1.mem.t' = b1.mem.t + v
        b1.head.t' = v
        some new_tups
        update_lca[t,t',new_tups]
        all b:(System.branches.t - b1) | skip[t,t',b]
        System.vertices.t' = System.vertices.t + v
        System.edges.t' = System.edges.t + hd1->v->FastFwd + hd2->v->FastFwd
        System.branches.t' = System.branches.t
    }
}

pred merge[t,t' : Time] {
    let vrsns = System.vertices.t |
    some v: (Version - vrsns) |
    /*
     * Merging b2 into b1
     */
    some b1: System.branches.t |
    some b2: (System.branches.t - b1) |
    let hd1 = b1.head.t |
    let hd2 = b2.head.t |
    let lb1b2 = b2.(b1.lca).t |
    let val1 = hd1.value |
    let val2 = hd2.value |
    let lca_val = lb1b2.value |
    let new_tups = (b1 -> b2 -> hd2) + (b1 -> b1 -> v) +
    {b1:b1, b:(System.branches.t - (b1 + b2)), v':b.(b2.lca).t | 
    ancestor_of[b.(b1.lca).t, b.(b2.lca.t), t]} {
        /* hd1 and hd2 must be ahead of L(b1,b2) */
        some (hd1.commits - lb1b2.commits)
        some (hd2.commits - lb1b2.commits)
        all b: (System.branches.t - (b1 + b2)) | 
            ancestrally_related[b.(b1.lca).t, b.(b2.lca).t, t]
        v.createdAt = t'
        v.commits = hd1.commits + hd2.commits
        v.value = lca_val.(val2.(val1.merge_fn))
        v.branch = b1
        b1.mem.t' = b1.mem.t + v
        b1.head.t' = v
        some new_tups
        update_lca[t,t',new_tups]
        all b:(System.branches.t - b1) | skip[t,t',b]
        System.vertices.t' = System.vertices.t + v
        System.edges.t' = System.edges.t + hd1->v->Merge + hd2->v->Merge
        System.branches.t' = System.branches.t
    }
}

fact traces {
    init [first]
    all t: Time - last |
        let t' = t.next |
            commit[t,t'] or fork[t,t'] or fastfwd[t,t'] or merge[t,t']
}

/*
 * Checking convergence
 */ 
assert convergence {
    all t: Time | all v1,v2: System.vertices.t | 
        v1.commits = v2.commits => v1.value = v2.value
}

/* No violation */
check convergence for 7 but 4 Branch

/*
 * Checking progress
 */
pred quiescent_state[t: Time] {
    all b1,b2: System.branches.t | b1.head.t.commits = b2.head.t.commits
}

pred exists_mergeable[t: Time] {
    some b1: System.branches.t |
    some b2: (System.branches.t - b1) |
    let hd1 = b1.head.t |
    let hd2 = b2.head.t |
    let lb1b2 = b2.(b1.lca).t {
        /* Either hd1 is L(b1,b2) or hd1 and hd2 are ahead of L(b1,b2) */
        hd1.commits = lb1b2.commits or some (hd1.commits - lb1b2.commits)
        some (hd2.commits - lb1b2.commits)
        all b: (System.branches.t - (b1 + b2)) | 
            ancestrally_related[b.(b1.lca).t, b.(b2.lca).t, t]
    }
}

assert progress {
    all t: Time | quiescent_state[t] or exists_mergeable[t]
}

check progress for 7 but 4 Branch

/*
 * Sample executions
 */
pred example {
    some v1,v2:Version | v1 -> v2 -> Merge in System.edges.last 
}


pred convergent_example {
    all b1,b2: System.branches.last | b1.head.last.commits = b2.head.last.commits
    some disj b1,b2,b3,b4: System.branches.last | 
        some disj v1,v2,v4,v5,v7,v8,v10,v11: Version |
            v1.branch = b1 && v2.branch = b1 && //v3.branch = b1 &&
            v4.branch = b2 && v5.branch = b2 && //v6.branch = b2 &&
            v7.branch = b3 && v8.branch = b3 && //v9.branch = b3 &&
            v10.branch = b4 && v11.branch = b4 //&& v12.branch = b4
}

run convergent_example for 8 but exactly 4 Branch, 4 Commit

pred convergent_example2 {
    all b1,b2: System.branches.last | b1.head.last.commits = b2.head.last.commits
    some disj b1,b2,b3: System.branches.last | 
        some disj v1,v2,v4,v5,v7,v8: Version |
            v1.branch = b1 && v2.branch = b1 && //v3.branch = b1 &&
            v4.branch = b2 && v5.branch = b2 && //v6.branch = b2 &&
            v7.branch = b3 && v8.branch = b3 //&& //v9.branch = b3 &&
            //v10.branch = b4 && v11.branch = b4 //&& v12.branch = b4
    all v1,v2:Version | all a: Action | 
        v1 -> v2 -> a in System.edges.last => a != FastFwd
}

run convergent_example2 for 7 but exactly 3 Branch, exactly 3 Commit

