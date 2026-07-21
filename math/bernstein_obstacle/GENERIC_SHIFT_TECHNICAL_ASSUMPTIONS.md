# Technical assumptions for the generic-shift packing theorem

The retained-element count in `GENERIC_SHIFT_THEOREM.md` is intended for a compact
embedded regular arc with a uniform tubular neighborhood.  Concretely, assume the arc
`Gamma` has positive reach `rho_Gamma>0`: every point at distance less than
`rho_Gamma` from `Gamma` has a unique nearest point on `Gamma`.

This assumption has two roles.

1. **Local arclength versus Euclidean distance.** For sufficiently short subarcs,
   arclength and chord length are uniformly comparable.  Thus points separated by
   `D h` in arclength are separated by a fixed multiple of `h` in Euclidean distance,
   once `h` is below a threshold depending on the curvature bound.
2. **No distant return into one element.** Two portions of the arc that are far apart
   in arclength cannot enter the same `O(h)` triangle when `h << rho_Gamma`.

Consequently a maximal `D h`-separated good set can be associated with distinct
triangles after choosing `D` larger than the reference-mesh diameter and local
bi-Lipschitz constants.  If one works instead with a simple graph patch over one fixed
tangent direction, positive reach follows automatically after shrinking the patch.

The per-level Fubini identity and the measure lower bound for good translations need
only rectifiability.  Positive reach is needed for the clean conversion from good arc
length to a uniform lower count of distinct retained elements and for the tubular
prism construction.