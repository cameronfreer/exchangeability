-- Main entry point for the exchangeability project.
import Std
import Exchangeability

def main : IO Unit := do
  IO.println "========================================="
  IO.println "  Welcome to exchangeability"
  IO.println "  Towards a formal de Finetti theorem"
  IO.println "========================================="
  IO.println ""
  IO.println "This project focuses on developing the infrastructure needed"
  IO.println "for a Lean 4 proof of de Finetti's theorem."
  IO.println ""
  IO.println "Key files:"
  IO.println "• `Exchangeability/Probability/DeFinetti.lean`"
  IO.println "• `blueprint/deFinetti.md`"
  IO.println ""
  IO.println "Run 'lake build' to build the project."
