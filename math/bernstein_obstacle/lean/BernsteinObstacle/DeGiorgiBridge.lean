import DeGiorgi.SobolevSpace
import DeGiorgi.PositivePart

namespace BernsteinObstacle

/-!
# Compatibility bridge to the De Giorgi Sobolev development

This file is intentionally small.  Its first role is to establish that the
published weak-derivative, `W₀^{1,p}` approximation, and positive-part layers
can be imported on the Bernstein obstacle project's pinned Lean/mathlib stack.
Once that compatibility gate is green, the physical recovery theorem can be
instantiated without rebuilding the entire Sobolev foundation privately.
-/

#check DeGiorgi.MemW1p
#check DeGiorgi.MemW1pWitness
#check DeGiorgi.MemW01p
#check DeGiorgi.MemH01
#check DeGiorgi.MemW1pWitness.memW1p
#check DeGiorgi.MemW1p.someWitness

end BernsteinObstacle
