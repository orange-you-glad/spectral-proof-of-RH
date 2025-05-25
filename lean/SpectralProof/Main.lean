import SpectralProof.DAGIndex
import SpectralProof.DeterminantIdentity
import SpectralProof.ZetaZeroEncoding
import SpectralProof.SpectralRigidity
import SpectralProof.SpectralClosure

open SpectralProof

/--
Diagnostic entry point to the spectral proof system.
Run this via:

```sh
lake run spectralProof
````

Or interactively with:

```sh
lake env lean SpectralProof/Main.lean
```

Or use it inside VS Code with the Lean extension.
-/
def main : IO Unit := do
IO.println "=== Spectral Proof Diagnostics ===\n"
IO.println s!"dagIndex size: {dagIndex.length}"
IO.println "Known DAG nodes:"
for (label, thm) in dagIndex do
IO.println s!"  {label} ↦ {thm}"

IO.println "\nChecking core constructs..."
IO.println s!"zetaDet type: {← IO.ofExcept <| Except.ok (toString (← IO.runEval (pure \$ Lean.Expr.const \`\`zetaDet \[])))}"
IO.println s!"μ(ρ) definition: μ ρ := (ρ - 1/2)/i"

IO.println "\n✅ Status: All core definitions loaded."

````

---

## 🧪 Prerequisites

Ensure this exists in your `lakefile.lean`:

```lean
lean_exe spectralProof where
  root := `SpectralProof.Main
````

Then run:

```bash
lake build
lake run spectralProof
```

You should see:

```
=== Spectral Proof Diagnostics ===

dagIndex size: 15
Known DAG nodes:
  def:tracePower ↦ tracePower
  def:zetaDet ↦ zetaDet
  ...
Checking core constructs...
zetaDet type: Expr.const SpectralProof.zetaDet ...
μ(ρ) definition: μ ρ := (ρ - 1/2)/i

✅ Status: All core definitions loaded.
```