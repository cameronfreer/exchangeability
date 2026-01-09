-- Main entry point for the exchangeability project.
import Std
import Exchangeability

def main : IO Unit := do
  IO.println "========================================="
  IO.println "  Welcome to exchangeability"
  IO.println "  A formalization of de Finetti's theorem"
  IO.println "========================================="
  IO.println ""
  IO.println "This project provides a complete Lean 4 formalization"
  IO.println "of de Finetti's theorem with three independent proofs."
  IO.println ""
  IO.println "Key files:"
  IO.println "• `Exchangeability/DeFinetti.lean`"
  IO.println "• `blueprint/deFinetti.md`"
  IO.println ""
  IO.println "Run 'lake build' to build the project."
