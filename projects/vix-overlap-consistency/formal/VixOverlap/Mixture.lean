import VixOverlap.BroadContract
import Mathlib.Data.Fintype.Sum

/-! Mixtures of complete filtered models with a common root budget field.

The branch is hidden at event zero and revealed at event one. Every conditional
equation is proved in unnormalized form; neither mixture weight is divided out.
The construction therefore includes both endpoint mixtures and null histories.
-/

noncomputable section
open scoped BigOperators

namespace VixOverlap.Mixture

variable {Ω₀ Ω₁ : Type} [Fintype Ω₀] [Fintype Ω₁]

def separated (H₀ : Setoid Ω₀) (H₁ : Setoid Ω₁) : Setoid (Ω₀ ⊕ Ω₁) where
  r := Sum.LiftRel H₀.r H₁.r
  iseqv := {
    refl := by
      intro x
      cases x with
      | inl x => exact Sum.LiftRel.inl (H₀.refl x)
      | inr x => exact Sum.LiftRel.inr (H₁.refl x)
    symm := by
      intro x y h
      cases h with
      | inl h => exact Sum.LiftRel.inl (H₀.symm h)
      | inr h => exact Sum.LiftRel.inr (H₁.symm h)
    trans := by
      intro x y z hxy hyz
      cases hxy with
      | inl hxy =>
        cases hyz with
        | inl hyz => exact Sum.LiftRel.inl (H₀.trans hxy hyz)
      | inr hxy =>
        cases hyz with
        | inr hyz => exact Sum.LiftRel.inr (H₁.trans hxy hyz)
  }

def partition (F₀ : HistoryFiltration 7 Ω₀) (F₁ : HistoryFiltration 7 Ω₁)
    (j : Fin 8) : Setoid (Ω₀ ⊕ Ω₁) :=
  if j = 0 then ⊤ else separated (F₀.partition j) (F₁.partition j)

def filtration (F₀ : HistoryFiltration 7 Ω₀) (F₁ : HistoryFiltration 7 Ω₁) :
    HistoryFiltration 7 (Ω₀ ⊕ Ω₁) where
  partition := partition F₀ F₁
  refines := by
    intro j k hjk x y h
    change (if k = 0 then ⊤ else separated (F₀.partition k) (F₁.partition k)).r x y at h
    change (if j = 0 then ⊤ else separated (F₀.partition j) (F₁.partition j)).r x y
    by_cases hj : j = 0
    · rw [if_pos hj]
      trivial
    · have hk : k ≠ 0 := by
        intro hk
        subst k
        exact hj (le_antisymm hjk (Fin.zero_le j))
      rw [if_neg hj]
      rw [if_neg hk] at h
      cases h with
      | inl h => exact Sum.LiftRel.inl (F₀.refines j k hjk _ _ h)
      | inr h => exact Sum.LiftRel.inr (F₁.refines j k hjk _ _ h)
  root := by intro x y; change True; trivial

theorem filtration_root_rel (F₀ : HistoryFiltration 7 Ω₀) (F₁ : HistoryFiltration 7 Ω₁)
    (x y : Ω₀ ⊕ Ω₁) : ((filtration F₀ F₁).partition 0).r x y := by
  change True
  trivial

theorem filtration_inl_inl (F₀ : HistoryFiltration 7 Ω₀) (F₁ : HistoryFiltration 7 Ω₁)
    (j : Fin 8) (hj : j ≠ 0) (x y : Ω₀) :
    ((filtration F₀ F₁).partition j).r (Sum.inl x) (Sum.inl y) ↔ (F₀.partition j).r x y := by
  change (if j = 0 then ⊤ else separated (F₀.partition j) (F₁.partition j)).r _ _ ↔ _
  rw [if_neg hj]
  exact Sum.liftRel_inl_inl

theorem filtration_inr_inr (F₀ : HistoryFiltration 7 Ω₀) (F₁ : HistoryFiltration 7 Ω₁)
    (j : Fin 8) (hj : j ≠ 0) (x y : Ω₁) :
    ((filtration F₀ F₁).partition j).r (Sum.inr x) (Sum.inr y) ↔ (F₁.partition j).r x y := by
  change (if j = 0 then ⊤ else separated (F₀.partition j) (F₁.partition j)).r _ _ ↔ _
  rw [if_neg hj]
  exact Sum.liftRel_inr_inr

theorem filtration_inl_inr (F₀ : HistoryFiltration 7 Ω₀) (F₁ : HistoryFiltration 7 Ω₁)
    (j : Fin 8) (hj : j ≠ 0) (x : Ω₀) (y : Ω₁) :
    ¬ ((filtration F₀ F₁).partition j).r (Sum.inl x) (Sum.inr y) := by
  change ¬ (if j = 0 then ⊤ else separated (F₀.partition j) (F₁.partition j)).r _ _
  rw [if_neg hj]
  exact Sum.not_liftRel_inl_inr

theorem filtration_inr_inl (F₀ : HistoryFiltration 7 Ω₀) (F₁ : HistoryFiltration 7 Ω₁)
    (j : Fin 8) (hj : j ≠ 0) (x : Ω₁) (y : Ω₀) :
    ¬ ((filtration F₀ F₁).partition j).r (Sum.inr x) (Sum.inl y) := by
  change ¬ (if j = 0 then ⊤ else separated (F₀.partition j) (F₁.partition j)).r _ _
  rw [if_neg hj]
  exact Sum.not_liftRel_inr_inl

def weight (ε : ℝ) (p₀ : Ω₀ → ℝ) (p₁ : Ω₁ → ℝ) : Ω₀ ⊕ Ω₁ → ℝ :=
  Sum.elim (fun x => (1 - ε) * p₀ x) (fun x => ε * p₁ x)

def law (p₀ : FiniteLaw Ω₀) (p₁ : FiniteLaw Ω₁) (ε : ℝ)
    (h0 : 0 ≤ ε) (h1 : ε ≤ 1) : FiniteLaw (Ω₀ ⊕ Ω₁) where
  weight := weight ε p₀.weight p₁.weight
  nonneg := by
    intro x
    cases x with
    | inl x => exact mul_nonneg (sub_nonneg.mpr h1) (p₀.nonneg x)
    | inr x => exact mul_nonneg h0 (p₁.nonneg x)
  total := by
    simp only [weight, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
      ← Finset.mul_sum, p₀.total, p₁.total, mul_one]
    ring

theorem law_nonempty {Ω : Type} [Fintype Ω] (p : FiniteLaw Ω) : Nonempty Ω := by
  by_contra h
  haveI : IsEmpty Ω := not_nonempty_iff.mp h
  have := p.total
  simpa using this

variable {grid : EventGrid 7}

theorem root_historySum {Ω : Type} [Fintype Ω] (M : FiniteModel grid Ω)
    (x : Ω) (f : Ω → ℝ) :
    historySum M.law.weight (M.filtration.partition 0) x f = M.expectation f := by
  simp [historySum, FiniteModel.expectation, M.filtration.root]

theorem root_historyMass {Ω : Type} [Fintype Ω] (M : FiniteModel grid Ω) (x : Ω) :
    historyMass M.law.weight (M.filtration.partition 0) x = 1 := by
  simp [historyMass, root_historySum, FiniteModel.expectation, M.law.total]

theorem root_stock_expectation {Ω : Type} [Fintype Ω] (M : FiniteModel grid Ω)
    (k : Fin 8) : M.expectation (M.stock k) = 1 := by
  let x : Ω := Classical.choice (law_nonempty M.law)
  have h := M.martingale 0 k (Fin.zero_le k) x
  simpa [root_historySum, root_historyMass, M.stock_initial] using h

theorem root_budget_expectation {Ω : Type} [Fintype Ω] (M : FiniteModel grid Ω)
    (b : Fin 7 → ℝ) (hb : ∀ h x, M.budget 0 h x = b h)
    (k : Fin 8) (h : Fin 7) (hkh : k.val ≤ h.val) :
    M.expectation (M.budget k h) = b h := by
  let x : Ω := Classical.choice (law_nonempty M.law)
  have ht := M.tower 0 k h (Fin.zero_le k) hkh x
  simpa [root_historySum, root_historyMass, hb] using ht

theorem root_diagonal_expectation {Ω : Type} [Fintype Ω] (M : FiniteModel grid Ω)
    (b : Fin 7 → ℝ) (hb : ∀ h x, M.budget 0 h x = b h) :
    M.expectation (fun x => -2 * Real.log (M.stock 1 x / M.stock 0 x)) = b 0 := by
  let x : Ω := Classical.choice (law_nonempty M.law)
  have hd := M.diagonal 0 x
  simpa [root_historySum, root_historyMass, hb] using hd

theorem historySum_zero (F₀ : HistoryFiltration 7 Ω₀) (F₁ : HistoryFiltration 7 Ω₁)
    (p₀ : Ω₀ → ℝ) (p₁ : Ω₁ → ℝ) (ε : ℝ) (x : Ω₀ ⊕ Ω₁)
    (f : Ω₀ ⊕ Ω₁ → ℝ) :
    historySum (weight ε p₀ p₁) ((filtration F₀ F₁).partition 0) x f =
      (1-ε) * (∑ y, p₀ y * f (Sum.inl y)) + ε * (∑ y, p₁ y * f (Sum.inr y)) := by
  simp [historySum, filtration_root_rel, weight, Fintype.sum_sum_type, mul_assoc,
    Finset.mul_sum]

theorem historySum_inl (F₀ : HistoryFiltration 7 Ω₀) (F₁ : HistoryFiltration 7 Ω₁)
    (p₀ : Ω₀ → ℝ) (p₁ : Ω₁ → ℝ) (ε : ℝ) (j : Fin 8) (hj : j ≠ 0)
    (x : Ω₀) (f : Ω₀ ⊕ Ω₁ → ℝ) :
    historySum (weight ε p₀ p₁) ((filtration F₀ F₁).partition j) (Sum.inl x) f =
      (1-ε) * historySum p₀ (F₀.partition j) x (fun y => f (Sum.inl y)) := by
  simp only [historySum, Fintype.sum_sum_type,
    filtration_inl_inl F₀ F₁ j hj, filtration_inl_inr F₀ F₁ j hj, if_false, weight,
    Sum.elim_inl, Sum.elim_inr, Finset.sum_const_zero, add_zero, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  split_ifs
  · ring
  · rename_i hmix hbase
    exact (hbase ((filtration_inl_inl F₀ F₁ j hj x y).mp hmix)).elim
  · rename_i hmix hbase
    exact (hmix ((filtration_inl_inl F₀ F₁ j hj x y).mpr hbase)).elim
  · ring

theorem historySum_inr (F₀ : HistoryFiltration 7 Ω₀) (F₁ : HistoryFiltration 7 Ω₁)
    (p₀ : Ω₀ → ℝ) (p₁ : Ω₁ → ℝ) (ε : ℝ) (j : Fin 8) (hj : j ≠ 0)
    (x : Ω₁) (f : Ω₀ ⊕ Ω₁ → ℝ) :
    historySum (weight ε p₀ p₁) ((filtration F₀ F₁).partition j) (Sum.inr x) f =
      ε * historySum p₁ (F₁.partition j) x (fun y => f (Sum.inr y)) := by
  simp only [historySum, Fintype.sum_sum_type,
    filtration_inr_inr F₀ F₁ j hj, filtration_inr_inl F₀ F₁ j hj, if_false, weight,
    Sum.elim_inl, Sum.elim_inr, Finset.sum_const_zero, zero_add, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  split_ifs
  · ring
  · rename_i hmix hbase
    exact (hbase ((filtration_inr_inr F₀ F₁ j hj x y).mp hmix)).elim
  · rename_i hmix hbase
    exact (hmix ((filtration_inr_inr F₀ F₁ j hj x y).mpr hbase)).elim
  · ring

theorem historyMass_zero (F₀ : HistoryFiltration 7 Ω₀) (F₁ : HistoryFiltration 7 Ω₁)
    (p₀ : FiniteLaw Ω₀) (p₁ : FiniteLaw Ω₁) (ε : ℝ) (x : Ω₀ ⊕ Ω₁) :
    historyMass (weight ε p₀.weight p₁.weight)
      ((filtration F₀ F₁).partition 0) x = 1 := by
  rw [historyMass, historySum_zero]
  simp only [mul_one, p₀.total, p₁.total]
  ring

theorem historyMass_inl (F₀ : HistoryFiltration 7 Ω₀) (F₁ : HistoryFiltration 7 Ω₁)
    (p₀ : Ω₀ → ℝ) (p₁ : Ω₁ → ℝ) (ε : ℝ) (j : Fin 8) (hj : j ≠ 0) (x : Ω₀) :
    historyMass (weight ε p₀ p₁) ((filtration F₀ F₁).partition j) (Sum.inl x) =
      (1-ε) * historyMass p₀ (F₀.partition j) x := by
  exact historySum_inl F₀ F₁ p₀ p₁ ε j hj x (fun _ => 1)

theorem historyMass_inr (F₀ : HistoryFiltration 7 Ω₀) (F₁ : HistoryFiltration 7 Ω₁)
    (p₀ : Ω₀ → ℝ) (p₁ : Ω₁ → ℝ) (ε : ℝ) (j : Fin 8) (hj : j ≠ 0) (x : Ω₁) :
    historyMass (weight ε p₀ p₁) ((filtration F₀ F₁).partition j) (Sum.inr x) =
      ε * historyMass p₁ (F₁.partition j) x := by
  exact historySum_inr F₀ F₁ p₀ p₁ ε j hj x (fun _ => 1)

def stock (M₀ : FiniteModel grid Ω₀) (M₁ : FiniteModel grid Ω₁)
    (j : Fin 8) : Ω₀ ⊕ Ω₁ → ℝ := Sum.elim (M₀.stock j) (M₁.stock j)

def budget (M₀ : FiniteModel grid Ω₀) (M₁ : FiniteModel grid Ω₁)
    (j : Fin 8) (h : Fin 7) : Ω₀ ⊕ Ω₁ → ℝ := Sum.elim (M₀.budget j h) (M₁.budget j h)

variable (M₀ : FiniteModel grid Ω₀) (M₁ : FiniteModel grid Ω₁)
variable (ε : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1)
variable (b : Fin 7 → ℝ)
variable (hb₀ : ∀ h x, M₀.budget 0 h x = b h)
variable (hb₁ : ∀ h x, M₁.budget 0 h x = b h)

/-- Mixture of full finite models with an initially hidden branch. -/
def model : FiniteModel grid (Ω₀ ⊕ Ω₁) where
  law := law M₀.law M₁.law ε h0 h1
  filtration := filtration M₀.filtration M₁.filtration
  stock := stock M₀ M₁
  budget := budget M₀ M₁
  stock_pos := by
    intro j x
    cases x with
    | inl x => exact M₀.stock_pos j x
    | inr x => exact M₁.stock_pos j x
  stock_initial := by
    intro x
    cases x with
    | inl x => exact M₀.stock_initial x
    | inr x => exact M₁.stock_initial x
  stock_adapted := by
    intro j x y h
    by_cases hj : j = 0
    · subst j
      cases x <;> cases y <;> simp [stock, M₀.stock_initial, M₁.stock_initial]
    · change (if j = 0 then ⊤ else separated (M₀.filtration.partition j)
        (M₁.filtration.partition j)).r x y at h
      rw [if_neg hj] at h
      cases h with
      | inl h => exact M₀.stock_adapted j _ _ h
      | inr h => exact M₁.stock_adapted j _ _ h
  budget_nonneg := by
    intro j h x hjh
    cases x with
    | inl x => exact M₀.budget_nonneg j h x hjh
    | inr x => exact M₁.budget_nonneg j h x hjh
  budget_adapted := by
    intro j h x y hjh hxy
    by_cases hj : j = 0
    · subst j
      cases x <;> cases y <;> simp [budget, hb₀, hb₁]
    · change (if j = 0 then ⊤ else separated (M₀.filtration.partition j)
        (M₁.filtration.partition j)).r x y at hxy
      rw [if_neg hj] at hxy
      cases hxy with
      | inl hxy => exact M₀.budget_adapted j h _ _ hjh hxy
      | inr hxy => exact M₁.budget_adapted j h _ _ hjh hxy
  martingale := by
    intro j k hjk x
    change historySum (weight ε M₀.law.weight M₁.law.weight)
      ((filtration M₀.filtration M₁.filtration).partition j) x (stock M₀ M₁ k) =
      stock M₀ M₁ j x * historyMass (weight ε M₀.law.weight M₁.law.weight)
        ((filtration M₀.filtration M₁.filtration).partition j) x
    by_cases hj : j = 0
    · subst j
      rw [historySum_zero, historyMass_zero]
      change (1-ε) * M₀.expectation (M₀.stock k) +
        ε * M₁.expectation (M₁.stock k) = stock M₀ M₁ 0 x * 1
      rw [root_stock_expectation, root_stock_expectation]
      cases x <;> simp [stock, M₀.stock_initial, M₁.stock_initial]
    · cases x with
      | inl x =>
        rw [historySum_inl _ _ _ _ _ _ hj, historyMass_inl _ _ _ _ _ _ hj]
        change (1-ε) * historySum M₀.law.weight (M₀.filtration.partition j) x
          (M₀.stock k) = M₀.stock j x * ((1-ε) * _)
        rw [M₀.martingale j k hjk x]
        ring
      | inr x =>
        rw [historySum_inr _ _ _ _ _ _ hj, historyMass_inr _ _ _ _ _ _ hj]
        change ε * historySum M₁.law.weight (M₁.filtration.partition j) x
          (M₁.stock k) = M₁.stock j x * (ε * _)
        rw [M₁.martingale j k hjk x]
        ring
  diagonal := by
    intro h x
    change historySum (weight ε M₀.law.weight M₁.law.weight)
      ((filtration M₀.filtration M₁.filtration).partition h.castSucc) x
      (fun y => -2 * Real.log (stock M₀ M₁ h.succ y / stock M₀ M₁ h.castSucc y)) =
      budget M₀ M₁ h.castSucc h x * historyMass (weight ε M₀.law.weight M₁.law.weight)
        ((filtration M₀.filtration M₁.filtration).partition h.castSucc) x
    by_cases hh : h = 0
    · subst h
      rw [show (0 : Fin 7).castSucc = (0 : Fin 8) from rfl,
        historySum_zero, historyMass_zero]
      change (1-ε) * M₀.expectation (fun y => -2 * Real.log (M₀.stock 1 y / M₀.stock 0 y)) +
        ε * M₁.expectation (fun y => -2 * Real.log (M₁.stock 1 y / M₁.stock 0 y)) =
        budget M₀ M₁ 0 0 x * 1
      rw [root_diagonal_expectation M₀ b hb₀, root_diagonal_expectation M₁ b hb₁]
      cases x <;> simp only [budget, Sum.elim_inl, Sum.elim_inr, hb₀, hb₁, mul_one] <;> ring
    · have hj : h.castSucc ≠ 0 := by
        intro he
        apply hh
        apply Fin.ext
        simpa only [Fin.val_castSucc, Fin.val_zero] using
          congrArg (fun z : Fin 8 => z.val) he
      cases x with
      | inl x =>
        rw [historySum_inl _ _ _ _ _ _ hj, historyMass_inl _ _ _ _ _ _ hj]
        change (1-ε) * historySum M₀.law.weight (M₀.filtration.partition h.castSucc) x
          (fun y => -2 * Real.log (M₀.stock h.succ y / M₀.stock h.castSucc y)) =
          M₀.budget h.castSucc h x * ((1-ε) * _)
        rw [M₀.diagonal h x]
        ring
      | inr x =>
        rw [historySum_inr _ _ _ _ _ _ hj, historyMass_inr _ _ _ _ _ _ hj]
        change ε * historySum M₁.law.weight (M₁.filtration.partition h.castSucc) x
          (fun y => -2 * Real.log (M₁.stock h.succ y / M₁.stock h.castSucc y)) =
          M₁.budget h.castSucc h x * (ε * _)
        rw [M₁.diagonal h x]
        ring
  tower := by
    intro j k h hjk hkh x
    change historySum (weight ε M₀.law.weight M₁.law.weight)
      ((filtration M₀.filtration M₁.filtration).partition j) x (budget M₀ M₁ k h) =
      budget M₀ M₁ j h x * historyMass (weight ε M₀.law.weight M₁.law.weight)
        ((filtration M₀.filtration M₁.filtration).partition j) x
    by_cases hj : j = 0
    · subst j
      rw [historySum_zero, historyMass_zero]
      change (1-ε) * M₀.expectation (M₀.budget k h) + ε * M₁.expectation (M₁.budget k h) =
        budget M₀ M₁ 0 h x * 1
      rw [root_budget_expectation M₀ b hb₀ k h hkh,
        root_budget_expectation M₁ b hb₁ k h hkh]
      cases x <;> simp only [budget, Sum.elim_inl, Sum.elim_inr, hb₀, hb₁, mul_one] <;> ring
    · cases x with
      | inl x =>
        rw [historySum_inl _ _ _ _ _ _ hj, historyMass_inl _ _ _ _ _ _ hj]
        change (1-ε) * historySum M₀.law.weight (M₀.filtration.partition j) x
          (M₀.budget k h) = M₀.budget j h x * ((1-ε) * _)
        rw [M₀.tower j k h hjk hkh x]
        ring
      | inr x =>
        rw [historySum_inr _ _ _ _ _ _ hj, historyMass_inr _ _ _ _ _ _ hj]
        change ε * historySum M₁.law.weight (M₁.filtration.partition j) x
          (M₁.budget k h) = M₁.budget j h x * (ε * _)
        rw [M₁.tower j k h hjk hkh x]
        ring

local notation "M" => model M₀ M₁ ε h0 h1 b hb₀ hb₁

theorem expectation_mix (f : Ω₀ ⊕ Ω₁ → ℝ) :
    (M).expectation f = (1-ε) * M₀.expectation (fun x => f (Sum.inl x)) +
      ε * M₁.expectation (fun x => f (Sum.inr x)) := by
  simp [FiniteModel.expectation, model, law, weight, Fintype.sum_sum_type,
    Finset.mul_sum, mul_assoc]

@[simp] theorem vix_inl (w : Window 7) (x : Ω₀) :
    (M).vix w (Sum.inl x) = M₀.vix w x := by
  rfl

@[simp] theorem vix_inr (w : Window 7) (x : Ω₁) :
    (M).vix w (Sum.inr x) = M₁.vix w x := by
  rfl

theorem stock_call_mix (j : Fin 8) (K : ℝ) :
    stockCallPrice M j K = (1-ε) * stockCallPrice M₀ j K + ε * stockCallPrice M₁ j K := by
  exact expectation_mix M₀ M₁ ε h0 h1 b hb₀ hb₁
    (fun x => callPayoff K ((M).stock j x))

theorem vix_call_mix (w : Window 7) (K : ℝ) :
    vixCallPrice M w K = (1-ε) * vixCallPrice M₀ w K + ε * vixCallPrice M₁ w K := by
  exact expectation_mix M₀ M₁ ε h0 h1 b hb₀ hb₁
    (fun x => callPayoff K ((M).vix w x))

theorem window_log_identity (w : Window 7) (hw : w.start ≠ 0)
    (hW₀ : ∀ x, historySum M₀.law.weight (M₀.filtration.partition w.start) x
      (fun y => -2 * Real.log (M₀.stock w.finish y / M₀.stock w.start y)) =
      M₀.windowBudget w x * historyMass M₀.law.weight (M₀.filtration.partition w.start) x)
    (hW₁ : ∀ x, historySum M₁.law.weight (M₁.filtration.partition w.start) x
      (fun y => -2 * Real.log (M₁.stock w.finish y / M₁.stock w.start y)) =
      M₁.windowBudget w x * historyMass M₁.law.weight (M₁.filtration.partition w.start) x)
    (x : Ω₀ ⊕ Ω₁) :
    historySum (M).law.weight ((M).filtration.partition w.start) x
      (fun y => -2 * Real.log ((M).stock w.finish y / (M).stock w.start y)) =
      (M).windowBudget w x * historyMass (M).law.weight ((M).filtration.partition w.start) x := by
  change historySum (weight ε M₀.law.weight M₁.law.weight)
    ((filtration M₀.filtration M₁.filtration).partition w.start) x
    (fun y => -2 * Real.log (stock M₀ M₁ w.finish y / stock M₀ M₁ w.start y)) =
    (M).windowBudget w x * historyMass (weight ε M₀.law.weight M₁.law.weight)
      ((filtration M₀.filtration M₁.filtration).partition w.start) x
  cases x with
  | inl x =>
    rw [historySum_inl _ _ _ _ _ _ hw, historyMass_inl _ _ _ _ _ _ hw]
    change (1-ε) * historySum M₀.law.weight (M₀.filtration.partition w.start) x
      (fun y => -2 * Real.log (M₀.stock w.finish y / M₀.stock w.start y)) =
      M₀.windowBudget w x * ((1-ε) * _)
    rw [hW₀ x]
    ring
  | inr x =>
    rw [historySum_inr _ _ _ _ _ _ hw, historyMass_inr _ _ _ _ _ _ hw]
    change ε * historySum M₁.law.weight (M₁.filtration.partition w.start) x
      (fun y => -2 * Real.log (M₁.stock w.finish y / M₁.stock w.start y)) =
      M₁.windowBudget w x * (ε * _)
    rw [hW₁ x]
    ring

end VixOverlap.Mixture

namespace VixOverlap.Broad

open ScheduleCertificate ScheduleModel

variable {Ω₀ Ω₁ : Type} [Fintype Ω₀] [Fintype Ω₁]

theorem uniform_admissible : Admissible (model uniformScheduleLaw) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x
    exact stockValue_one x.1 x.2
  · intro x
    exact budgetValue_cell_zero uniformScheduleLaw 0 x
  · exact model_root_budget uniformScheduleLaw ScheduleModel.uniform_bit_mean
  · exact uniform_moment_bound uniformScheduleLaw

theorem uniform_fitsPanel (J : Finset (Fin 3)) :
    FitsPanel (model uniformScheduleLaw) 1 J := by
  constructor
  · intro j K hK
    rfl
  · intro w hw K hK
    rw [actual_vix_call]
    apply QuoteContract.windowCall_from_marginal
    change WindowMarginal uniformWeight w 1
    intro k
    simpa [mixedTarget] using uniform_window w k

def commonRootBudget (h : Fin 7) : ℝ := if h = 0 then 0 else c/2

theorem admissible_root_budget {Ω : Type} [Fintype Ω] (M : FiniteModel grid Ω)
    (hA : Admissible M) (h : Fin 7) (x : Ω) : M.budget 0 h x = commonRootBudget h := by
  refine Fin.cases ?_ (fun i => ?_) h
  · simpa [commonRootBudget] using hA.2.1 x
  · simpa [commonRootBudget] using hA.2.2.1 i x

/-- Convex mixture within the broader class, with branch revelation at event one. -/
def mix (M₀ : FiniteModel grid Ω₀) (M₁ : FiniteModel grid Ω₁)
    (ε : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (hA₀ : Admissible M₀) (hA₁ : Admissible M₁) :
    FiniteModel grid (Ω₀ ⊕ Ω₁) :=
  Mixture.model M₀ M₁ ε h0 h1 commonRootBudget
    (admissible_root_budget M₀ hA₀) (admissible_root_budget M₁ hA₁)

theorem mix_admissible (M₀ : FiniteModel grid Ω₀) (M₁ : FiniteModel grid Ω₁)
    (ε : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (hA₀ : Admissible M₀) (hA₁ : Admissible M₁) :
    Admissible (mix M₀ M₁ ε h0 h1 hA₀ hA₁) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x
    cases x with
    | inl x => exact hA₀.1 x
    | inr x => exact hA₁.1 x
  · intro x
    cases x with
    | inl x => exact hA₀.2.1 x
    | inr x => exact hA₁.2.1 x
  · intro i x
    cases x with
    | inl x => exact hA₀.2.2.1 i x
    | inr x => exact hA₁.2.2.1 i x
  · intro x
    cases x with
    | inl x => exact hA₀.2.2.2 x
    | inr x => exact hA₁.2.2.2 x

theorem targetCall_mix (ε : ℝ) (w : Fin 3) (K : ℝ) :
    QuoteContract.targetCall c ε w K =
      (1-ε) * QuoteContract.targetCall c 0 w K + ε * QuoteContract.targetCall c 1 w K := by
  unfold QuoteContract.targetCall mixedTarget
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _
  ring

/-- Ordinary calls interpolate linearly after the mixture branch is revealed. -/
theorem mix_fitsPanel (M₀ : FiniteModel grid Ω₀) (M₁ : FiniteModel grid Ω₁)
    (ε : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (hA₀ : Admissible M₀) (hA₁ : Admissible M₁)
    (J : Finset (Fin 3)) (hF₀ : FitsPanel M₀ 0 J) (hF₁ : FitsPanel M₁ 1 J) :
    FitsPanel (mix M₀ M₁ ε h0 h1 hA₀ hA₁) ε J := by
  constructor
  · intro j K hK
    rw [mix, Mixture.stock_call_mix, hF₀.1 j K hK, hF₁.1 j K hK]
    ring
  · intro w hw K hK
    rw [mix, Mixture.vix_call_mix, hF₀.2 w hw K hK, hF₁.2 w hw K hK]
    exact (targetCall_mix ε w K).symm

theorem mix_window_log_identity
    (M₀ : FiniteModel grid Ω₀) (M₁ : FiniteModel grid Ω₁)
    (ε : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (hA₀ : Admissible M₀) (hA₁ : Admissible M₁)
    (hW₀ : ∀ w x, historySum M₀.law.weight (M₀.filtration.partition (window w).start) x
      (fun y => -2 * Real.log (M₀.stock (window w).finish y / M₀.stock (window w).start y)) =
      M₀.windowBudget (window w) x *
        historyMass M₀.law.weight (M₀.filtration.partition (window w).start) x)
    (hW₁ : ∀ w x, historySum M₁.law.weight (M₁.filtration.partition (window w).start) x
      (fun y => -2 * Real.log (M₁.stock (window w).finish y / M₁.stock (window w).start y)) =
      M₁.windowBudget (window w) x *
        historyMass M₁.law.weight (M₁.filtration.partition (window w).start) x)
    (w : Fin 3) (x : Ω₀ ⊕ Ω₁) :
    let M := mix M₀ M₁ ε h0 h1 hA₀ hA₁
    historySum M.law.weight (M.filtration.partition (window w).start) x
      (fun y => -2 * Real.log (M.stock (window w).finish y / M.stock (window w).start y)) =
      M.windowBudget (window w) x *
        historyMass M.law.weight (M.filtration.partition (window w).start) x := by
  have hw : (window w).start ≠ 0 := by
    intro h
    have hv := congrArg (fun j : Fin 8 => j.val) h
    change w.val + 2 = 0 at hv
    omega
  exact Mixture.window_log_identity M₀ M₁ ε h0 h1 commonRootBudget
    (admissible_root_budget M₀ hA₀) (admissible_root_budget M₁ hA₁)
    (window w) hw (hW₀ w) (hW₁ w) x

/-- A compatible zero-parameter endpoint extends to the entire quoted convex
family, with the same structural initial conditions and moment bound. -/
theorem compatible_family {Ω : Type} [Fintype Ω] (M₀ : FiniteModel grid Ω)
    (hA₀ : Admissible M₀) (hF₀ : FitsPanel M₀ 0 Finset.univ)
    (ε : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1) : HasCompatibleLaw ε := by
  let M := mix M₀ (model uniformScheduleLaw) ε h0 h1 hA₀ uniform_admissible
  refine ⟨Ω ⊕ State, inferInstance, M, ?_, ?_⟩
  · exact mix_admissible M₀ (model uniformScheduleLaw) ε h0 h1 hA₀ uniform_admissible
  · exact mix_fitsPanel M₀ (model uniformScheduleLaw) ε h0 h1 hA₀ uniform_admissible
      Finset.univ hF₀ (uniform_fitsPanel Finset.univ)

end VixOverlap.Broad
