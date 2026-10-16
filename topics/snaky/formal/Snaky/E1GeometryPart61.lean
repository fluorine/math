import Snaky.E1GeometryDefs

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem geometry61_checked : (Geometry10.part61.filter eligible).all (fun F => sources.contains (traceOf F)) = true := by decide +kernel
theorem geometry61_count : (Geometry10.part61.filter eligible).length = 6 := by decide +kernel
end Snaky.E1
