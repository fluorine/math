import Snaky.E1GeometryDefs

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem geometry48_checked : (Geometry10.part48.filter eligible).all (fun F => sources.contains (traceOf F)) = true := by decide +kernel
theorem geometry48_count : (Geometry10.part48.filter eligible).length = 0 := by decide +kernel
end Snaky.E1
