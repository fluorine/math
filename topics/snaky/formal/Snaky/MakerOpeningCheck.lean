import Snaky.CardsSound

/-! Proof factoring for the unchanged ordinary-card checker. Each transformed
support inclusion is established once; a reply adds its one excluded cell. -/
namespace Snaky.MakerOpeningCheck

theorem all_of_parts {α : Type} (f : α → Bool) {xs ys : List α}
    (heq : xs = ys) (h : ys.all f = true) : xs.all f = true := heq ▸ h

theorem self_cover (xs : List Pt) : xs.all (fun x => xs.contains x) = true := by
  rw [List.all_eq_true]
  intro x hx
  exact List.contains_iff_mem.mpr hx

theorem hint_of_parts {get : Nat → Option Card} {c d : Card} {hn : Hint}
    (hg : get hn.1 = some d) (hh : decide (d.h < c.h) = true)
    (ho : hn.2.isOrient = true)
    (ha : d.A.all (fun a => (c.p :: c.A).contains (hn.2.app a)) = true)
    (hs : d.S.all (fun s => c.S.contains (hn.2.app s)) = true) :
    hintOK get c.h (c.p :: c.A) (fun s => c.S.contains s) hn = true := by
  simp only [hintOK, hg, hh, ho, ha, hs, Bool.and_self]

theorem hint_avoid {get : Nat → Option Card} {c d : Card} {hn : Hint} {w : Pt}
    (hg : get hn.1 = some d)
    (h : hintOK get c.h (c.p :: c.A) (fun s => c.S.contains s) hn = true)
    (ha : d.S.all (fun s => hn.2.app s != w) = true) :
    hintOK get c.h (c.p :: c.A) (fun s => c.S.contains s && s != w) hn = true := by
  simp only [hintOK, hg, Bool.and_eq_true] at h ⊢
  refine ⟨h.1, ?_⟩
  rw [List.all_eq_true] at ha ⊢
  have hs := List.all_eq_true.mp h.2
  intro s hsD
  rw [Bool.and_eq_true]
  exact ⟨hs s hsD, ha s hsD⟩

theorem reply_of_hint {get : Nat → Option Card} {c d : Card} {hn : Hint} {w : Pt}
    (hl : c.replies.lookup w = some hn) (hg : get hn.1 = some d)
    (h : hintOK get c.h (c.p :: c.A) (fun s => c.S.contains s) hn = true)
    (ha : d.S.all (fun s => hn.2.app s != w) = true) : replyOK get c w = true := by
  unfold replyOK
  rw [hl]
  rw [Bool.or_eq_true]
  exact Or.inr (hint_avoid hg h ha)

end Snaky.MakerOpeningCheck
