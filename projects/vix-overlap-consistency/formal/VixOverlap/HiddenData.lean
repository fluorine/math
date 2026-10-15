import VixOverlap.ScheduleData
import Mathlib.Data.Fin.VecNotation

/-! Exact positive latent states for the hidden-schedule construction. -/

namespace VixOverlap.Hidden

open ScheduleCertificate

abbrev Atom := Fin 39

-- Literal data from certificates/hidden-witness.json, in its support order.
def scheduleIndex : Atom → ℕ :=
  ![0, 1, 2, 4, 4, 5, 5, 8, 13, 15, 15, 16, 20, 21, 25, 25, 28, 28, 28,
    31, 32, 33, 33, 34, 37, 39, 41, 47, 48, 49, 50, 54, 56, 56, 58, 58, 60, 62, 63]

def signalCode : Atom → ℕ :=
  ![41, 1, 5, 21, 41, 41, 42, 41, 41, 43, 47, 37, 41, 37, 37, 41, 37, 41, 57,
    43, 21, 1, 21, 5, 21, 23, 25, 27, 21, 37, 21, 21, 37, 40, 25, 41, 37, 37, 43]

def numerator : Atom → ℕ :=
  ![16, 16, 32, 9, 23, 16, 16, 3, 3, 90, 32, 7, 16, 7, 16, 49, 7, 25, 64,
    65, 6, 16, 32, 128, 6, 38, 15, 15, 16, 64, 32, 16, 16, 16, 7, 25, 32, 16, 16]

theorem scheduleIndex_lt : ∀ a : Atom, scheduleIndex a < 64 := by decide

def schedule (a : Atom) : Schedule := ⟨scheduleIndex a, scheduleIndex_lt a⟩

/-- Signals are read from left to right in their base-four code. -/
def signal (a : Atom) (w : Fin 3) : ℕ :=
  signalCode a / 4 ^ (2 - w.val) % 4

theorem signal_lt_four (a : Atom) (w : Fin 3) : signal a w < 4 :=
  Nat.mod_lt _ (by decide)

theorem signal_le_three (a : Atom) (w : Fin 3) : signal a w ≤ 3 := by
  have := signal_lt_four a w
  omega

noncomputable def weight (a : Atom) : ℝ := numerator a / 1024

/-- At event `j`, completed activities and signals already fixed are known.
The activity of cell `i+1` is first known at its end, event `i+2`. -/
def History (j : ℕ) (a b : Atom) : Prop :=
  (∀ i : Fin 6, i.val + 1 < j → bit (schedule a) i = bit (schedule b) i) ∧
    (∀ w : Fin 3, w.val + 2 ≤ j → signal a w = signal b w)

instance (j : ℕ) (a b : Atom) : Decidable (History j a b) := by
  unfold History
  infer_instance

theorem history_refl (j : ℕ) (a : Atom) : History j a a :=
  ⟨fun _ _ => rfl, fun _ _ => rfl⟩

theorem history_symm {j : ℕ} {a b : Atom} (h : History j a b) : History j b a :=
  ⟨fun i hi => (h.1 i hi).symm, fun w hw => (h.2 w hw).symm⟩

theorem history_trans {j : ℕ} {a b d : Atom}
    (hab : History j a b) (hbd : History j b d) : History j a d :=
  ⟨fun i hi => (hab.1 i hi).trans (hbd.1 i hi),
    fun w hw => (hab.2 w hw).trans (hbd.2 w hw)⟩

def latentHistory (j : ℕ) : Setoid Atom where
  r := History j
  iseqv := ⟨history_refl j, fun h => history_symm h, fun h k => history_trans h k⟩

theorem history_refines {j k : ℕ} (hjk : j ≤ k) {a b : Atom}
    (h : History k a b) : History j a b :=
  ⟨fun i hi => h.1 i (by omega), fun w hw => h.2 w (by omega)⟩

theorem history_root (a b : Atom) : History 0 a b := by
  constructor <;> intro i hi <;> omega

theorem history_one (a b : Atom) : History 1 a b := by
  constructor <;> intro i hi <;> omega

theorem history_bit {j : ℕ} {a b : Atom} (h : History j a b)
    (i : Fin 6) (hi : i.val + 1 < j) : bit (schedule a) i = bit (schedule b) i :=
  h.1 i hi

theorem history_signal {j : ℕ} {a b : Atom} (h : History j a b)
    (w : Fin 3) (hw : w.val + 2 ≤ j) : signal a w = signal b w :=
  h.2 w hw

end VixOverlap.Hidden
