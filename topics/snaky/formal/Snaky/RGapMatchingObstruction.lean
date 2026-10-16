import Init.Data.List.Lemmas

/-!
# Five selected guards have no static matching cover

Labels `0,1,...,8` denote the distinct cells `a,b,...,i`. The mate function
is defined on every natural number. Its endpoints may lie outside these nine
cells; no odd-domain perfect-matching assumption is made.

The five requirements are `bf`, `abc`, `bcde`, `dfgh`, and `cdgi`.
Their protection forces `bf`, then `ac`, then `de`, then `gh`, leaving no
pair in `cdgi`. This is a static matching obstruction, not a Maker strategy.
There is no dependency on the game development or any external certificate.
-/

namespace Snaky.RGapMatchingObstruction

/-- A guard contains both endpoints of at least one mate pair. -/
def Protects (mate : Nat → Nat) (guard : List Nat) : Prop :=
  ∃ x, x ∈ guard ∧ mate x ∈ guard

private theorem two_forces {mate : Nat → Nat} {a b : Nat}
    (inv : ∀ x, mate (mate x) = x) (noFixed : ∀ x, mate x ≠ x)
    (h : Protects mate [a, b]) : mate a = b := by
  obtain ⟨x, hx, hy⟩ := h
  have hx' : x = a ∨ x = b := by simpa using hx
  have hy' : mate x = a ∨ mate x = b := by simpa using hy
  rcases hx' with hxa | hxb
  · subst x
    rcases hy' with h | h
    · exact False.elim (noFixed a h)
    · exact h
  · subst x
    rcases hy' with h | h
    · have hi := inv b
      rw [h] at hi
      exact hi
    · exact False.elim (noFixed b h)

/-- If the mate of a guard vertex is outside, neither endpoint of the
guard's protecting pair can be that vertex. This uses global involutivity. -/
private theorem remove_unavailable {mate : Nat → Nat} {guard : List Nat} {z : Nat}
    (inv : ∀ x, mate (mate x) = x) (outside : mate z ∉ guard)
    (h : Protects mate guard) :
    Protects mate (guard.filter fun x => decide (x ≠ z)) := by
  obtain ⟨x, hx, hy⟩ := h
  have hxz : x ≠ z := by
    intro he
    apply outside
    simpa only [he] using hy
  have hyz : mate x ≠ z := by
    intro he
    have hi := inv x
    rw [he] at hi
    apply outside
    simpa only [hi] using hx
  refine ⟨x, List.mem_filter.mpr ⟨hx, ?_⟩, List.mem_filter.mpr ⟨hy, ?_⟩⟩
  · simpa using hxz
  · simpa using hyz

/-- No globally fixed-point-free involution can protect all five guards.
In particular, allowing arbitrary partners outside labels `0..8` does not
evade the obstruction. The conclusion says nothing about adaptive play. -/
theorem no_static_matching
    (mate : Nat → Nat)
    (inv : ∀ x, mate (mate x) = x)
    (noFixed : ∀ x, mate x ≠ x) :
    ¬ (Protects mate [1, 5] ∧ Protects mate [0, 1, 2] ∧
       Protects mate [1, 2, 3, 4] ∧ Protects mate [3, 5, 6, 7] ∧
       Protects mate [2, 3, 6, 8]) := by
  rintro ⟨hbf, habc, hbcde, hdfgh, hcdgi⟩
  have h_bf : mate 1 = 5 := two_forces inv noFixed hbf
  have hac : Protects mate [0, 2] :=
    remove_unavailable (z := 1) inv (by simp [h_bf]) habc
  have h_ac : mate 0 = 2 := two_forces inv noFixed hac
  have h_ca : mate 2 = 0 := by
    have hi := inv 0
    rw [h_ac] at hi
    exact hi
  have hcde : Protects mate [2, 3, 4] :=
    remove_unavailable (z := 1) inv (by simp [h_bf]) hbcde
  have hde : Protects mate [3, 4] :=
    remove_unavailable (z := 2) inv (by simp [h_ca]) hcde
  have h_de : mate 3 = 4 := two_forces inv noFixed hde
  have h_fb : mate 5 = 1 := by
    have hi := inv 1
    rw [h_bf] at hi
    exact hi
  have hfgh : Protects mate [5, 6, 7] :=
    remove_unavailable (z := 3) inv (by simp [h_de]) hdfgh
  have hgh : Protects mate [6, 7] :=
    remove_unavailable (z := 5) inv (by simp [h_fb]) hfgh
  have h_gh : mate 6 = 7 := two_forces inv noFixed hgh
  have hdgi : Protects mate [3, 6, 8] :=
    remove_unavailable (z := 2) inv (by simp [h_ca]) hcdgi
  have hgi : Protects mate [6, 8] :=
    remove_unavailable (z := 3) inv (by simp [h_de]) hdgi
  have hi : Protects mate [8] :=
    remove_unavailable (z := 6) inv (by simp [h_gh]) hgi
  obtain ⟨x, hx, hy⟩ := hi
  have hx' : x = 8 := by simpa using hx
  subst x
  exact noFixed 8 (by simpa using hy)

end Snaky.RGapMatchingObstruction

#print axioms Snaky.RGapMatchingObstruction.no_static_matching
