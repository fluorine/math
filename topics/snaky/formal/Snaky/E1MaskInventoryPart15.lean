import Snaky.E1Conditions
import Snaky.E1MaskInventoryData

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem maskInventory15 : inputMasks15.filter validRow = outputMasks15 := by decide +kernel
end Snaky.E1
