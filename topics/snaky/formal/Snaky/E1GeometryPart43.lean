import Snaky.E1GeometryDefs

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem geometry43_checked : (Geometry10.part43.filter eligible).all (fun F => sources.contains (traceOf F)) = true := by decide +kernel
theorem geometry43_count : (Geometry10.part43.filter eligible).length = 6 := by decide +kernel
end Snaky.E1
