import Snaky.E1Uncovered00Part00
import Snaky.E1Uncovered00Part01
import Snaky.E1Uncovered00Part02
import Snaky.E1Uncovered00Part03
import Snaky.E1Uncovered00Part04
import Snaky.E1Uncovered00Part05
import Snaky.E1Uncovered00Part06
import Snaky.E1Uncovered00Part07
import Snaky.E1Uncovered00Part08
import Snaky.E1Uncovered00Part09
import Snaky.E1Uncovered01Part00
import Snaky.E1Uncovered01Part01
import Snaky.E1Uncovered01Part02
import Snaky.E1Uncovered01Part03
import Snaky.E1Uncovered01Part04
import Snaky.E1Uncovered01Part05
import Snaky.E1Uncovered01Part06
import Snaky.E1Uncovered01Part07
import Snaky.E1Uncovered01Part08
import Snaky.E1Uncovered01Part09
import Snaky.E1Uncovered02Part00
import Snaky.E1Uncovered02Part01
import Snaky.E1Uncovered02Part02
import Snaky.E1Uncovered02Part03
import Snaky.E1Uncovered02Part04
import Snaky.E1Uncovered02Part05
import Snaky.E1Uncovered02Part06
import Snaky.E1Uncovered02Part07
import Snaky.E1Uncovered02Part08
import Snaky.E1Uncovered02Part09
import Snaky.E1Uncovered10Part00
import Snaky.E1Uncovered10Part01
import Snaky.E1Uncovered10Part02
import Snaky.E1Uncovered10Part03
import Snaky.E1Uncovered10Part04
import Snaky.E1Uncovered10Part05
import Snaky.E1Uncovered10Part06
import Snaky.E1Uncovered10Part07
import Snaky.E1Uncovered10Part08
import Snaky.E1Uncovered10Part09
import Snaky.E1Uncovered11Part00
import Snaky.E1Uncovered11Part01
import Snaky.E1Uncovered11Part02
import Snaky.E1Uncovered11Part03
import Snaky.E1Uncovered11Part04
import Snaky.E1Uncovered11Part05
import Snaky.E1Uncovered11Part06
import Snaky.E1Uncovered11Part07
import Snaky.E1Uncovered11Part08
import Snaky.E1Uncovered11Part09
import Snaky.E1Uncovered12Part00
import Snaky.E1Uncovered12Part01
import Snaky.E1Uncovered12Part02
import Snaky.E1Uncovered12Part03
import Snaky.E1Uncovered12Part04
import Snaky.E1Uncovered12Part05
import Snaky.E1Uncovered12Part06
import Snaky.E1Uncovered12Part07
import Snaky.E1Uncovered12Part08
import Snaky.E1Uncovered12Part09

namespace Snaky.E1

theorem uncovered00_exact : sources.filter (fun t => !covered pairs00 t) = uncovered00 := by
  simp only [sources, List.filter_append, uncovered00_part00, uncovered00_part01, uncovered00_part02, uncovered00_part03, uncovered00_part04, uncovered00_part05, uncovered00_part06, uncovered00_part07, uncovered00_part08, uncovered00_part09]
  rfl

theorem uncovered01_exact : sources.filter (fun t => !covered pairs01 t) = uncovered01 := by
  simp only [sources, List.filter_append, uncovered01_part00, uncovered01_part01, uncovered01_part02, uncovered01_part03, uncovered01_part04, uncovered01_part05, uncovered01_part06, uncovered01_part07, uncovered01_part08, uncovered01_part09]
  rfl

theorem uncovered02_exact : sources.filter (fun t => !covered pairs02 t) = uncovered02 := by
  simp only [sources, List.filter_append, uncovered02_part00, uncovered02_part01, uncovered02_part02, uncovered02_part03, uncovered02_part04, uncovered02_part05, uncovered02_part06, uncovered02_part07, uncovered02_part08, uncovered02_part09]
  rfl

theorem uncovered10_exact : sources.filter (fun t => !covered pairs10 t) = uncovered10 := by
  simp only [sources, List.filter_append, uncovered10_part00, uncovered10_part01, uncovered10_part02, uncovered10_part03, uncovered10_part04, uncovered10_part05, uncovered10_part06, uncovered10_part07, uncovered10_part08, uncovered10_part09]
  rfl

theorem uncovered11_exact : sources.filter (fun t => !covered pairs11 t) = uncovered11 := by
  simp only [sources, List.filter_append, uncovered11_part00, uncovered11_part01, uncovered11_part02, uncovered11_part03, uncovered11_part04, uncovered11_part05, uncovered11_part06, uncovered11_part07, uncovered11_part08, uncovered11_part09]
  rfl

theorem uncovered12_exact : sources.filter (fun t => !covered pairs12 t) = uncovered12 := by
  simp only [sources, List.filter_append, uncovered12_part00, uncovered12_part01, uncovered12_part02, uncovered12_part03, uncovered12_part04, uncovered12_part05, uncovered12_part06, uncovered12_part07, uncovered12_part08, uncovered12_part09]
  rfl

end Snaky.E1
