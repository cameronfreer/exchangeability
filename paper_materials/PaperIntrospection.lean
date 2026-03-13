/-
Introspection file for paper materials.

This file collects #check, #print, and #print axioms commands for
key theorems and definitions in the de Finetti formalization.

Run with: lake env lean paper_materials/PaperIntrospection.lean
-/
import Exchangeability.DeFinetti.Theorem
import Exchangeability.DeFinetti.TheoremViaL2
import Exchangeability.DeFinetti.TheoremViaKoopman

open Exchangeability
open Exchangeability.DeFinetti

-- ============================================================================
-- MAIN THEOREMS
-- ============================================================================

section MainTheorems

#check @Exchangeability.DeFinetti.deFinetti
#check @Exchangeability.DeFinetti.deFinetti_equivalence
#check @Exchangeability.DeFinetti.deFinetti_RyllNardzewski_equivalence
#check @Exchangeability.DeFinetti.conditionallyIID_of_contractable

-- Alternative proofs
#check @Exchangeability.DeFinetti.conditionallyIID_of_contractable_viaL2
#check @Exchangeability.DeFinetti.conditionallyIID_of_contractable_viaKoopman

end MainTheorems

-- ============================================================================
-- CORE DEFINITIONS
-- ============================================================================

section CoreDefinitions

#print Exchangeability.Exchangeable
#print Exchangeability.FullyExchangeable
#print Exchangeability.Contractable
#print ConditionallyIID

end CoreDefinitions

-- ============================================================================
-- KEY LEMMAS
-- ============================================================================

section KeyLemmas

-- Exchangeable → Contractable
#check @Exchangeability.contractable_of_exchangeable

-- ConditionallyIID → Exchangeable
#check @exchangeable_of_conditionallyIID

-- Permutation extension (combinatorial heart)
#check @Exchangeability.exists_perm_extending_strictMono

end KeyLemmas

-- ============================================================================
-- AXIOM CHECKS
-- ============================================================================

section AxiomChecks

#print axioms Exchangeability.DeFinetti.deFinetti
#print axioms Exchangeability.DeFinetti.deFinetti_RyllNardzewski_equivalence
#print axioms Exchangeability.DeFinetti.conditionallyIID_of_contractable_viaL2
#print axioms Exchangeability.DeFinetti.conditionallyIID_of_contractable_viaKoopman

end AxiomChecks
