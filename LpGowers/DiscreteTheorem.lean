module

public import LpGowers.BinaryTheorem
public import LpGowers.DiscreteLargeSide
public import LpGowers.DiscreteEntropyUpper

/-! # The three parts of Theorem 1.5 of Kovač–Rogers -/

@[expose] public section
namespace LpGowers.Discrete

/-- The full binary critical exponents, both fixed-degree logarithmic bounds,
and the fixed-side additive binomial entropy asymptotic. -/
theorem discreteClaim : DiscreteClaim := ⟨binaryClaim, largeSideClaim, largeDegreeClaim⟩

end LpGowers.Discrete
