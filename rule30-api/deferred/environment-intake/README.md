# Deferred concrete-path example

The adjacent file preserves the exact authored declaration of
`Rule30Api.EnvironmentMemoryTraces.matchingCompletionUsesExistingAtomicWriter`.
It is **unproved and excluded from this release's formal coverage**. The file
is a declaration fragment from `EnvironmentMemoryTraces`, outside both configured
source roots (`src` and `stdlib`); it is not a registered proof module.

It asserts that this one pinned fixture, at `/private`, requests the expected
pending-file write with matching serialized contents. It does not prove rename,
validated readback, crash recovery, or power-loss durability. Native evidence
is not a substitute kernel theorem.

The release retains every main obligation, all new pin/schema/content/refusal/
replay obligations, `mismatchedCompletionExitsBeforeWrite`, and the checked
singleton serialization equality. Runtime checks, atomic replacement and exact
validated readback requirements are unchanged.

The checked parser/serialization source review is preserved as Library artifact
`intake-proof-repair-review.tar.gz` (SHA-256
`7b35573eac83743ca35cf38bdd5ecb3dd292052e400eb37b2012d221564ecc58`).
The unsuccessful core transfer and its receipts are preserved separately as
`intake-corepath-transfer-result.tar.gz` (SHA-256
`2e847a001fd3a167734e20e51cbb11b5825a934b3d59188decbe3730dc4eff5d`).
The latter stopped at `intakeAcquiredBridge`; it did not test the transferred
UTF-8 proof in this consumer. No claim or runtime policy was weakened to close it.
