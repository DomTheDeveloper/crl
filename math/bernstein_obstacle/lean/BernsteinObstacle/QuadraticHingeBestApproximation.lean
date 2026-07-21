import BernsteinObstacle.QuadraticHingeProjection

namespace BernsteinObstacle

/-!
# Exact best quadratic approximation of the hinge profile

The pointwise lower-bound theorem is upgraded to a greatest-lower-bound
statement over the entire two-parameter space of affine derivatives.  The
explicit optimal slope and intercept attain the bound, so this is an exact
best-approximation theorem rather than only a saturation inequality.
-/

/-- Set of all normalized squared derivative errors produced by quadratic
approximants. -/
def quadraticHingeAffineDerivativeErrorRange (theta : ℝ) : Set ℝ :=
  Set.range fun p : ℝ × ℝ =>
    quadraticHingeAffineDerivativeErrorSq theta p.1 p.2

/-- The sharp normalized constant is the greatest lower bound of the squared
`H¹`-seminorm errors over the full quadratic polynomial space. -/
theorem quadraticHingeAffineDerivativeErrorSq_isGLB
    (theta : ℝ) :
    IsGLB (quadraticHingeAffineDerivativeErrorRange theta)
      (((4 : ℝ) / 3) * theta ^ 3 * (1 - theta) ^ 3) := by
  constructor
  · intro value hvalue
    rcases hvalue with ⟨p, rfl⟩
    exact quadraticHingeAffineDerivativeErrorSq_lowerBound
      theta p.1 p.2
  · intro lower hlower
    have hoptimal := hlower <|
      Set.mem_range_self
        (quadraticHingeOptimalSlope theta,
          quadraticHingeOptimalIntercept theta)
    simpa [quadraticHingeAffineDerivativeErrorRange,
      quadraticHingeAffineDerivativeErrorSq_at_optimal] using hoptimal

/-- Set of all scaled squared derivative errors produced by quadratic
approximants on `[0,h]`. -/
def scaledQuadraticHingeAffineDerivativeErrorRange
    (amplitude h theta : ℝ) : Set ℝ :=
  Set.range fun p : ℝ × ℝ =>
    scaledQuadraticHingeAffineDerivativeErrorSq
      amplitude h theta p.1 p.2

/-- For nonnegative interval length, the scaled sharp constant is the greatest
lower bound of all squared derivative errors over the full quadratic space. -/
theorem scaledQuadraticHingeAffineDerivativeErrorSq_isGLB
    (amplitude h theta : ℝ) (hh : 0 ≤ h) :
    IsGLB
      (scaledQuadraticHingeAffineDerivativeErrorRange amplitude h theta)
      (((4 : ℝ) / 3) * amplitude ^ 2 * theta ^ 3 *
        (1 - theta) ^ 3 * h ^ 3) := by
  constructor
  · intro value hvalue
    rcases hvalue with ⟨p, rfl⟩
    exact scaledQuadraticHingeAffineDerivativeErrorSq_lowerBound
      amplitude h theta p.1 p.2 hh
  · intro lower hlower
    have hoptimal := hlower <|
      Set.mem_range_self
        (scaledQuadraticHingeOptimalSlope amplitude theta,
          scaledQuadraticHingeOptimalIntercept amplitude h theta)
    simpa [scaledQuadraticHingeAffineDerivativeErrorRange,
      scaledQuadraticHingeAffineDerivativeErrorSq_at_optimal] using hoptimal

end BernsteinObstacle
