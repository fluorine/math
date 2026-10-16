import Snaky.E1GeometryDefs

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem geometry39_checked : (Geometry10.part39.filter eligible).all (fun F => sources.contains (traceOf F)) = true := by decide +kernel
theorem geometry39_count : (Geometry10.part39.filter eligible).length = 0 := by decide +kernel
end Snaky.E1
