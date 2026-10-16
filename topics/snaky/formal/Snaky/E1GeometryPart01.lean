import Snaky.E1GeometryDefs

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem geometry01_checked : (Geometry10.part01.filter eligible).all (fun F => sources.contains (traceOf F)) = true := by decide +kernel
theorem geometry01_count : (Geometry10.part01.filter eligible).length = 6 := by decide +kernel
end Snaky.E1
