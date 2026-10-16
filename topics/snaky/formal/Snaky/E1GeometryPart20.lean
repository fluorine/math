import Snaky.E1GeometryDefs

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem geometry20_checked : (Geometry10.part20.filter eligible).all (fun F => sources.contains (traceOf F)) = true := by decide +kernel
theorem geometry20_count : (Geometry10.part20.filter eligible).length = 7 := by decide +kernel
end Snaky.E1
