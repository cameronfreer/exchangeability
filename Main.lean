-- Main entry point for leantest-afp basic Lean 4 example
import IO
import LeantestAfp

def main : IO Unit := do
  IO.println "========================================="
  IO.println "  Welcome to leantest-afp!"
  IO.println "  Basic Lean 4 Example Project"
  IO.println "========================================="
  IO.println ""
  IO.println "This project demonstrates:"
  IO.println "• Basic function definitions"
  IO.println "• Simple theorems and proofs"
  IO.println "• Type definitions (structures)"
  IO.println "• List operations"
  IO.println "• Mathematical computations"
  IO.println ""
  IO.println "Check out the source files in LeantestAfp/ to see examples!"
  IO.println ""
  IO.println "Run 'lake build' to build the project"
  IO.println "Run 'lean --run LeantestAfp/Basic.lean' to see the #eval outputs"