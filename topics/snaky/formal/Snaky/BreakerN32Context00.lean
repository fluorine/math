import Snaky.BreakerN32RootRow26
import Snaky.BreakerN32RootRow27
import Snaky.BreakerN32RootRow40
import Snaky.BreakerN32RootRow41
import Snaky.BreakerN32RootRow52
import Snaky.BreakerN32RootRow53
import Snaky.BreakerN32RootRow54
import Snaky.BreakerN32RootRow55
import Snaky.BreakerN32RootRow67
import Snaky.BreakerN32RootRow68
import Snaky.BreakerN32RootRow69
import Snaky.BreakerN32RootRow81
import Snaky.BreakerN32RootRow83
import Snaky.BreakerN32RootRow95
import Snaky.BreakerN32RootRow96
import Snaky.BreakerN32RootRow97
import Snaky.BreakerN32RootRow108
import Snaky.BreakerN32RootRow109
import Snaky.BreakerN32RootRow110
import Snaky.BreakerN32RootRow111
import Snaky.BreakerN32RootRow123
import Snaky.BreakerN32RootRow124
import Snaky.BreakerN32RootRow125
import Snaky.BreakerN32RootRow139

namespace Snaky.BreakerN32.C00
open Snaky.Breaker

theorem defense : ¬ BlackWins guards 196 [] (outside 196 domain) := by
  apply local_round_not_blackWins shape
  intro u hu
  have cases : u = 26 ∨ u = 27 ∨ u = 40 ∨ u = 41 ∨ u = 52 ∨ u = 53 ∨ u = 54 ∨ u = 55 ∨ u = 67 ∨ u = 68 ∨ u = 69 ∨ u = 81 ∨ u = 83 ∨ u = 95 ∨ u = 96 ∨ u = 97 ∨ u = 108 ∨ u = 109 ∨ u = 110 ∨ u = 111 ∨ u = 123 ∨ u = 124 ∨ u = 125 ∨ u = 139 := by
    simpa only [domain, List.mem_cons, List.not_mem_nil, or_false] using hu
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨68, row26Fresh, row26Defense⟩
  · exact ⟨68, row27Fresh, row27Defense⟩
  · exact ⟨68, row40Fresh, row40Defense⟩
  · exact ⟨68, row41Fresh, row41Defense⟩
  · exact ⟨53, row52Fresh, row52Defense⟩
  · exact ⟨52, row53Fresh, row53Defense⟩
  · exact ⟨68, row54Fresh, row54Defense⟩
  · exact ⟨68, row55Fresh, row55Defense⟩
  · exact ⟨53, row67Fresh, row67Defense⟩
  · exact ⟨96, row68Fresh, row68Defense⟩
  · exact ⟨53, row69Fresh, row69Defense⟩
  · exact ⟨67, row81Fresh, row81Defense⟩
  · exact ⟨69, row83Fresh, row83Defense⟩
  · exact ⟨68, row95Fresh, row95Defense⟩
  · exact ⟨68, row96Fresh, row96Defense⟩
  · exact ⟨68, row97Fresh, row97Defense⟩
  · exact ⟨68, row108Fresh, row108Defense⟩
  · exact ⟨68, row109Fresh, row109Defense⟩
  · exact ⟨68, row110Fresh, row110Defense⟩
  · exact ⟨68, row111Fresh, row111Defense⟩
  · exact ⟨68, row123Fresh, row123Defense⟩
  · exact ⟨68, row124Fresh, row124Defense⟩
  · exact ⟨68, row125Fresh, row125Defense⟩
  · exact ⟨68, row139Fresh, row139Defense⟩

end Snaky.BreakerN32.C00
