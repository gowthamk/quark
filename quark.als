module quark

open util/ordering[Time] as TO

sig Time {}

sig Commit {}

one sig InitCommit extends Commit {}

sig Value {}

abstract sig Action {}
one sig NewCommit, Fork, FastFwd, Merge extends Action {}

sig Version {
    createdAt: Time,
    commits: set Commit,
    value: Value, 
    branch: Branch
}
one sig Root extends Version {}{
    createdAt = first
    commits = InitCommit
    branch = Master
}

sig Branch {
    createdAt: Time,
    mem: Version -> Time,
    head: Version lone -> Time,
    lca: Branch -> lone Version -> Time
} {
    all t: prevs[createdAt] | no mem.t
    all t: Time | head.t in mem.t 
    all t: Time | all v: mem.t | v.branch = this 
    all t: (Time - prevs[createdAt])| one head.t 
    all t: prevs[createdAt] | no lca.t
}

fact lcaCommutative {
    all b1,b2: Branch | all t: Time | 
        b2.(b1.lca).t = b1.(b2.lca).t
}

one sig Master extends Branch {} {
    createdAt = first
    mem.first = Root
    head.first = Root
}

one sig System {
    vertices: Version -> Time,
    edges: Version -> Version -> Action -> Time,
    branches: Branch -> Time,
}

pred init [t: Time] {
    System.vertices.t = Root
    no System.edges.t
    System.branches.t = Master
}

pred skip[t,t': Time, b: Branch] {
    b.mem.t' = b.mem.t
    b.head.t' = b.head.t
    b.lca.t' = b.lca.t
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
                b.lca.t' = b.lca.t
                System.vertices.t' = System.vertices.t + v
                System.edges.t' = System.edges.t + hd->v->NewCommit
                System.branches.t' = System.branches.t
                all b': (Branch - b) | skip[t,t',b']
            }
        }
}

fact traces {
    init [first]
    all t: Time - last |
        let t' = t.next |
            commit[t,t']
}

pred example {

}

run example for 3
