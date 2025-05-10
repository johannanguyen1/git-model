#lang forge/temporal

open "operations.frg"
open "sigs.frg"

option max_tracelength 6
option min_tracelength 6

test suite for Init {
    assert {InitSAT and Init} is sat for exactly 1 Repo, exactly 4 CommitNode, exactly 1 Root, exactly 3 Int
    assert {InitUNSAT and Init} is unsat for exactly 1 Repo, exactly 4 CommitNode, exactly 1 Root, exactly 3 Int
}

// SAT: one firstRoot, others unused
pred InitSAT {
    always WellformedRepo

    some r: Repo, fr: CommitNode | {
        r.totalCommits = fr
        r.firstRoot = fr

        fr.next = none
        fr.outgoingBranches = none
        fr.prevBranchNode = none

        all c: CommitNode - fr | c in Unused.unusedCommits
    }
}

// UNSAT: one firstRoot, others are used in next fields of firstRoot but shouldn't be 
pred InitUNSAT {
    always WellformedRepo

    some r: Repo, fr: CommitNode, c: CommitNode | {
        r.totalCommits = fr
        r.firstRoot = fr

        fr.next = none
        fr.outgoingBranches = none
        fr.prevBranchNode = none

        c != fr
        c not in Unused.unusedCommits
    }
}

test suite for AddOneCommitNode {
    assert {AddOneCommitNodeSAT and AddOneCommitNode} is sat for exactly 1 Repo, exactly 3 CommitNode, exactly 1 Root, exactly 3 Int
    assert {AddOneCommitNodeUNSAT and AddOneCommitNode} is unsat for exactly 1 Repo, exactly 3 CommitNode, exactly 1 Root, exactly 3 Int
}

// SAT: adding a commitNode into Repo reduces the number of unusedCommits by 1
pred AddOneCommitNodeSAT {
    Init
    always WellformedRepo

    one c: Unused.unusedCommits | {
        Unused.unusedCommits' = Unused.unusedCommits - c
        Repo.totalCommits' = Repo.totalCommits + c
    }
}

// UNSAT: can’t move anything from unused to repo because none are unused
pred AddOneCommitNodeUNSAT {
    Init
    always WellformedRepo

    Unused.unusedCommits = none
    some Repo.totalCommits
    Unused.unusedCommits' = Unused.unusedCommits
}

test suite for Commit {
    assert {CommitSAT} is sat for exactly 1 Repo, exactly 4 CommitNode, exactly 1 Root, exactly 3 Int
    assert {CommitSAT2} is sat for exactly 1 Repo, exactly 2 CommitNode, exactly 1 Root, exactly 3 Int

    assert {CommitUNSAT} is unsat for exactly 1 Repo, exactly 4 CommitNode, exactly 1 Root, exactly 3 Int
    assert {CommitUNSAT2} is unsat for exactly 1 Repo, exactly 4 CommitNode, exactly 1 Root, exactly 3 Int

}

// SAT: can commit from inital state
pred CommitSAT {
    Init
    always WellformedRepo

    some r: Root | Commit[r]
}

// SAT: fields hold after a commit 
pred CommitSAT2 {
    Init
    always WellformedRepo
    eventually {
        some r: Root, c: CommitNode | {
            Commit[r]
            c in Repo.totalCommits
            // commit creates a new commit node correctly
            r.next' = Unused.unusedCommits - Unused.unusedCommits'
            c not in Unused.unusedCommits // commit should not be unused
            c.prevBranchNode' = c.prevBranchNode  // previous branch node should stay the same
            c.fileState != none  // new commit should have a valid file state
            no c.next // no next commit after this one
        }
    }
}

// UNSAT: no unused commits to add
pred CommitUNSAT {
    Init
    always WellformedRepo
    Unused.unusedCommits = none
    eventually {
        some r: Root | Commit[r]
    }
}

// UNSAT: root should have a next commit and commit is in incorrect order
pred CommitUNSAT2 {
    Init
    always WellformedRepo
    eventually {
        some r: Root, c: CommitNode | {
            r in Repo.totalCommits
            Commit[r]
            c not in Unused.unusedCommits // commit should not be unused
            c.prevBranchNode' = c.prevBranchNode  // previous branch node should stay the same
            c.fileState != none  // new commit should have a valid file state
            // why it should fail: 
            c.next' != r // commit is in incorrect order
            r.next' = none  // root should have a next commit, commit failed 
        }
    }
}


test suite for Branching {
    assert {BranchingSAT} is sat for exactly 1 Repo, exactly 4 CommitNode, exactly 2 Root, exactly 3 Int
    assert {BranchingSAT2} is sat for exactly 1 Repo, exactly 4 CommitNode, exactly 2 Root, exactly 3 Int
    assert {BranchingSAT3} is sat for exactly 1 Repo, exactly 4 CommitNode, exactly 2 Root, exactly 3 Int
    assert {BranchOffNonMainSAT4} is sat for exactly 1 Repo, exactly 4 CommitNode, exactly 4 Root, exactly 5 Int

    assert {BranchingUNSAT} is unsat for exactly 1 Repo, exactly 2 CommitNode, exactly 2 Root, exactly 3 Int
}

// SAT: sanity, branching can occur off initial state
pred BranchingSAT {
    Init
    always WellformedRepo

    some r: Root | Branching[r]
}

// SAT: sanity #2, branching can occur off commit node
pred BranchingSAT2 {
    Init
    always WellformedRepo

    eventually {
        some r: Root, c: CommitNode | {
            r in Repo.totalCommits
            c in Repo.totalCommits
            c.next = none // commit node has no further commits yet
            c not in Unused.unusedCommits // commit node is not unused
            Branching[r]
        }
    }
}

// SAT: branching should change fields as commented below
pred BranchingSAT3 {
    Init
    always WellformedRepo

    eventually {
        some r: Root | {
            Branching[r]
            // new root commit is created correctly
            some newRoot: Root | {
                newRoot in Repo.totalCommits'
                newRoot in Unused.unusedCommits // came from unused commits
                newRoot.next = none // no next commit exists for the new root
                newRoot.outgoingBranches = none // new root has no outgoing branches initially
                newRoot.fileState' != none // new root should have a valid fileState
                newRoot.prevBranchNode' != none // new root should point to its parent commit as prevBranchNode
            }
        }
    }
}

// SAT: branching off a non-main branch
pred BranchOffNonMainSAT4 {
    Init
    always WellformedRepo

    // first, branch off the main root
    Branching[Repo.firstRoot]
    // then, branch off of that new branch
    next_state {
        some r: Root | r != Repo.firstRoot and Branching[r]
    }
}

// UNSAT: cannot branch with no unusedCommits 
pred BranchingUNSAT {
    Init
    always WellformedRepo

    Unused.unusedCommits = none
    some r: Root | Branching[r]
}

test suite for Merge {
    assert {MergeSAT1} is sat for exactly 1 Repo, exactly 4 CommitNode, exactly 2 Root, exactly 3 Int
    assert {MergeSAT2} is sat for exactly 1 Repo, exactly 4 CommitNode, exactly 2 Root, exactly 3 Int
    assert {MergeSAT3} is sat for exactly 1 Repo, exactly 4 CommitNode, exactly 2 Root, exactly 3 Int
    assert {MergeSAT4} is sat for exactly 1 Repo, exactly 4 CommitNode, exactly 2 Root, exactly 3 Int
    assert {MergeUNSAT} is unsat for exactly 1 Repo, exactly 4 CommitNode, exactly 2 Root, exactly 3 Int
    assert {MergeUNSAT2} is unsat for exactly 1 Repo, exactly 4 CommitNode, exactly 2 Root, exactly 3 Int
}

// SAT: after branching and committing, can merge
pred MergeSAT1 {
    Init
    always WellformedRepo

    // Step 1: Branch off the firstRoot
    eventually {
        Branching[Repo.firstRoot]
    }

    // Step 2: Commit on the new branch
    eventually {
        some r: Root | r != Repo.firstRoot and Commit[r]
    }

    // Step 3: Merge the branches
    eventually {
        some rootToMerge: Root | {
            Merge[Repo.firstRoot, rootToMerge]
        }
    }
}

// SAT: after committing, branching and committing, can merge
pred MergeSAT2 {
    Init
    always WellformedRepo

    // Step 3: Commit on the root branch
    eventually {
        some r: Root | r != Repo.firstRoot and Commit[r]
    }

    // Step 2: Branch off the firstRoot
    eventually {
        Branching[Repo.firstRoot]
    }

    // Step 3: Commit on the new branch
    eventually {
        some r: Root | r != Repo.firstRoot and Commit[r]
    }

    // Step 4: Merge the branches
    eventually {
        some rootToMerge: Root | {
            Merge[Repo.firstRoot, rootToMerge]
        }
    }
}

// SAT: after merging, can commit
pred MergeSAT3 {
    Init
    always WellformedRepo

    // Step 3: Commit on the root branch
    eventually {
        some r: Root | r != Repo.firstRoot and Commit[r]
    }

    // Step 2: Branch off the firstRoot
    eventually {
        Branching[Repo.firstRoot]
    }

    // Step 3: Commit on the new branch
    eventually {
        some r: Root | r != Repo.firstRoot and Commit[r]
    }

    // Step 4: Merge the branches
    eventually {
        some rootToMerge: Root | {
            Merge[Repo.firstRoot, rootToMerge]

            some c1, c2: CommitNode | {
                c1 in Repo.firstRoot.*next
                c2 in rootToMerge.*next
            }
        }
    }

    // Step 5: Commit on the merged branch
    eventually {
        some r: Root | r != Repo.firstRoot and Commit[r]
    }
}


// SAT: after merging, can commit then merge again
pred MergeSAT4 {
    Init
    always WellformedRepo

    // Step 3: Commit on the root branch
    eventually {
        some r: Root | r != Repo.firstRoot and Commit[r]
    }

    // Step 2: Branch off the firstRoot
    eventually {
        Branching[Repo.firstRoot]
    }

    // Step 3: Commit on the new branch
    eventually {
        some r: Root | r != Repo.firstRoot and Commit[r]
    }

    // Step 4: Merge the branches
    eventually {
        some rootToMerge: Root | {
            Merge[Repo.firstRoot, rootToMerge]
        }
    }

    // Step 5: Commit on the merged branch
    eventually {
        some r: Root | r != Repo.firstRoot and Commit[r]
    }

    // Step 6: Merge the branches
    eventually {
        some rootToMerge: Root | {
            Merge[Repo.firstRoot, rootToMerge]
        }
    }
}

// UNSAT: cannot merge with no unused commits available
pred MergeUNSAT {
    Init
    always WellformedRepo

    Unused.unusedCommits = none
    some rootToMerge: Root | Merge[Repo.firstRoot, rootToMerge]
}

// UNSAT: cannot merge with yourself
pred MergeUNSAT2 {
    Init
    always WellformedRepo

    eventually {
        Merge[Repo.firstRoot, Repo.firstRoot]
    }
}


test suite for Revert {
    assert {RevertSAT} is sat for exactly 1 Repo, exactly 4 CommitNode, exactly 2 Root, exactly 3 Int
    assert {RevertUNSAT} is unsat for exactly 1 Repo, exactly 4 CommitNode, exactly 2 Root, exactly 3 Int
}

// SAT: properties of a reverted commit is maintained
pred RevertSAT {
    always WellformedRepo

    Init => {
        eventually {
            some c: CommitNode | {
                Revert[c]
                some parent: CommitNode | {
                parent in c.*next and parent.next = Unused.unusedCommits - Unused.unusedCommits'
                parent.next.next = none
                parent.next.outgoingBranches = none
                parent.next.fileState = c.fileState
                }
            }
        }
    }
}


// UNSAT parent.next future timesteps do not match what's expected... EXPLAIN 
pred RevertUNSAT {
    Init
    always WellformedRepo

    AddOneCommitNode
    some c: CommitNode | {
        Revert[c]
        one parent: Repo.totalCommits | {
            (parent in c.*next and parent.next = none)
            parent.next' = (Unused.unusedCommits - Unused.unusedCommits')
            parent.outgoingBranches' = parent.outgoingBranches
            parent.fileState' = parent.fileState
            
            parent.next'.next' != none
            parent.next'.outgoingBranches' != none
            parent.next'.fileState' != c.fileState // new commit should have the same fileState as revertingTo/c, testing when it doesn't
        }
    }
}



