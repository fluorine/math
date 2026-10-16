import Snaky.E1Conditions
import Snaky.E1MaskInventoryData

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem maskInventory13 : inputMasks13.filter validRow = outputMasks13 := by decide +kernel
end Snaky.E1
