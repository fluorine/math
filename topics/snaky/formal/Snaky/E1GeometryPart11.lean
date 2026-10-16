import Snaky.E1GeometryDefs

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem geometry11_checked : (Geometry10.part11.filter eligible).all (fun F => sources.contains (traceOf F)) = true := by decide +kernel
theorem geometry11_count : (Geometry10.part11.filter eligible).length = 5 := by decide +kernel
end Snaky.E1
