import Snaky.E1Conditions
import Snaky.E1MaskInventoryData

namespace Snaky.E1
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem maskInventory07 : inputMasks07.filter validRow = outputMasks07 := by decide +kernel
end Snaky.E1
