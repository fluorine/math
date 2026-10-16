import Snaky.E1GeometryDefs

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem geometry38_checked : (Geometry10.part38.filter eligible).all (fun F => sources.contains (traceOf F)) = true := by decide +kernel
theorem geometry38_count : (Geometry10.part38.filter eligible).length = 0 := by decide +kernel
end Snaky.E1
