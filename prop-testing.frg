#lang forge/temporal

open "sigs.frg"
open "operations.frg"

option max_tracelength 5
option min_tracelength 2

// PROPERTY TESTING:

test suite for Init {
    assert { Init } is sat for exactly 1 Repo, exactly 1 Root, exactly 1 Unused, exactly 1 CommitNode, exactly 1 Int
}

test suite for Invariants {
    // TESTS OF INCLUSION
    assert { UniqueCommits } is necessary for Invariants
    assert { Acyclic } is necessary for Invariants
    assert { Reachable } is necessary for Invariants
    assert { RootNoParents } is necessary for Invariants

    assert { UniqueCommits } is sat for exactly 1 Repo, 1 Root, 2 CommitNode
    assert { Acyclic } is sat for exactly 1 Repo, 1 Root, 2 CommitNode
    assert { Reachable } is sat for exactly 1 Repo, 1 Root, 2 CommitNode
    assert { RootWithParents } is sat for exactly 1 Repo, 1 Root, 2 CommitNode

    // TESTS OF EXLCUSION
    assert { Invariants and Cyclic } is unsat for exactly 1 Repo, 1 Root, 2 CommitNode
    assert { Invariants and NotReachable } is unsat for exactly 1 Repo, 1 Root, 2 CommitNode
    assert { Invariants and RootWithParents } is unsat for exactly 1 Repo, 1 Root, 2 CommitNode
    assert { Invariants and NonUniqueCommits } is unsat for exactly 1 Repo, 1 Root, 2 CommitNode
}

// after any two arbitrary operations, properties must be preserved

pred threeStepTrace {
    Init
    WellformedRepo
    some r1, r2: Root | Branching[r1] or Commit[r2]

    some r3, r4: Root | Branching[r3] or Commit[r4]

    some c3, c4: CommitNode, r5: Root | Merge[c3, r5] or Revert[c4]
}

test suite for PostOperationInvariants {
    assert { threeStepTrace } is sufficient for PostOperationInvariants

    assert { threeStepTrace and CommitDeletionAllowed } is unsat for exactly 1 Repo, 1 Root, 2 CommitNode
    assert { threeStepTrace and MutableHistory } is unsat for exactly 1 Repo, 1 Root, 2 CommitNode
}

pred BranchCommitMergeTrace {
    Init
    WellformedRepo
    some r: Root | Branching[r]
    some r2: Root | Commit[r2]
    some c: CommitNode, r3: Root | Merge[c, r3]
}

test suite for BranchCommitMergeTraceInvariants {
    assert { BranchCommitMergeTrace } is sufficient for PostOperationInvariants
    assert { BranchCommitMergeTrace and CommitDeletionAllowed } is unsat for exactly 1 Repo, 1 Root, 2 CommitNode
    assert { BranchCommitMergeTrace and MutableHistory } is unsat for exactly 1 Repo, 1 Root, 2 CommitNode
}

pred CommitBranchRevertTrace {
    Init
    WellformedRepo
    some r: Root | Commit[r]
    some r2: Root | Branching[r2]
    some c: CommitNode | Revert[c]
}

test suite for CommitBranchRevertTraceInvariants {
    assert { CommitBranchRevertTrace } is sufficient for PostOperationInvariants
    assert { CommitBranchRevertTrace and CommitDeletionAllowed } is unsat for exactly 1 Repo, 1 Root, 2 CommitNode
    assert { CommitBranchRevertTrace and MutableHistory } is unsat for exactly 1 Repo, 1 Root, 2 CommitNode
}

pred CommitCommitRevertTrace {
    Init
    WellformedRepo
    some r: Root | Commit[r]
    some r2: Root | Commit[r2]
    some c: CommitNode | Revert[c]
}

test suite for CommitBranchRevertTraceInvariants {
    assert { CommitCommitRevertTrace } is sufficient for PostOperationInvariants
    assert { CommitCommitRevertTrace and CommitDeletionAllowed } is unsat for exactly 1 Repo, 1 Root, 2 CommitNode
    assert { CommitCommitRevertTrace and MutableHistory } is unsat for exactly 1 Repo, 1 Root, 2 CommitNode
}

