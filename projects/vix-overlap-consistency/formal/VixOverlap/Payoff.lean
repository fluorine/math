import Mathlib.Basic.Real.Basic

namespace VixOverlap

/-- Ordinary European call payoff, in discounted units. -/
def callPayoff (strike underlying : ℝ) : ℝ := max (underlying - strike) 0

end VixOverlap
