import Snaky.E1Data

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem pairs00_matching : ((pairs00.flatMap fun p => [p.1, p.2]).Nodup) ∧
    (∀ p ∈ pairs00, p.1 < 100 ∧ p.2 < 100 ∧ p.1 ≠ p.2) := by decide +kernel

theorem pairs01_matching : ((pairs01.flatMap fun p => [p.1, p.2]).Nodup) ∧
    (∀ p ∈ pairs01, p.1 < 100 ∧ p.2 < 100 ∧ p.1 ≠ p.2) := by decide +kernel

theorem pairs02_matching : ((pairs02.flatMap fun p => [p.1, p.2]).Nodup) ∧
    (∀ p ∈ pairs02, p.1 < 100 ∧ p.2 < 100 ∧ p.1 ≠ p.2) := by decide +kernel

theorem pairs10_matching : ((pairs10.flatMap fun p => [p.1, p.2]).Nodup) ∧
    (∀ p ∈ pairs10, p.1 < 100 ∧ p.2 < 100 ∧ p.1 ≠ p.2) := by decide +kernel

theorem pairs11_matching : ((pairs11.flatMap fun p => [p.1, p.2]).Nodup) ∧
    (∀ p ∈ pairs11, p.1 < 100 ∧ p.2 < 100 ∧ p.1 ≠ p.2) := by decide +kernel

theorem pairs12_matching : ((pairs12.flatMap fun p => [p.1, p.2]).Nodup) ∧
    (∀ p ∈ pairs12, p.1 < 100 ∧ p.2 < 100 ∧ p.1 ≠ p.2) := by decide +kernel

end Snaky.E1
