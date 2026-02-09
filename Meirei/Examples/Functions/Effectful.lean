import PredictableVerification.IR.Meirei.Elaborator.Index

namespace Effectful

abbrev EffectM := Id

/-- Assert that property holds for the result of an effectful computation. -/
def satisfies (m : EffectM α) (P : α → Prop) : Prop := P m

/-- Infix notation: `m ⊧ P` means the effectful computation `m` satisfies predicate `P`. -/
notation:50 m " ⊧ " P => satisfies m P

-- Effect: getY returns an Int
axiom getY : Unit → EffectM Int

noncomputable def prodOfTwoWithEffect (x : Int) : EffectM Int := do
  let y ← getY ()
  return x * y

-- ============================================================================
-- Meirei version using the elaborator
-- ============================================================================

noncomputable def prodOfTwoWithEffect' := [Meirei|
  def prodOfTwoWithEffect(x: int) : int {
    y <- getY();
    return x * y;
  }
]

-- Check that the elaborated version has the expected type
#check (prodOfTwoWithEffect' : Int → EffectM Int)

-- ============================================================================
-- More Complex Example: Order Processing with Effectful Operations
-- ============================================================================

-- Effects for order processing
axiom getDiscountThreshold : Unit → EffectM Int  -- Fetch discount threshold from config/DB
axiom getDiscountMultiplier : Unit → EffectM Int -- Fetch current discount multiplier
axiom recordSale : Int → EffectM Unit            -- Log a sale amount to audit system

/--
  Process a list of order amounts:
  1. Fetch the current discount threshold from configuration
  2. For each order:
     - If above threshold: apply discount multiplier and record the discounted sale
     - If below threshold: record the original sale amount
  3. Return total revenue
-/
noncomputable def processOrders := [Meirei|
  def processOrders(orderAmounts: [int]) : int {
    discountThreshold <- getDiscountThreshold();
    var totalRevenue : int = 0;
    for amount in orderAmounts {
      if (amount > discountThreshold) {
        multiplier <- getDiscountMultiplier();
        recordSale(amount * multiplier);
        totalRevenue = totalRevenue + amount * multiplier;
      } else {
        recordSale(amount);
        totalRevenue = totalRevenue + amount;
      }
    }
    return totalRevenue;
  }
]

#print processOrders
#check (processOrders : List Int → EffectM Int)

end Effectful
