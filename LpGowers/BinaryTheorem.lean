module

public import LpGowers.DiscreteBinaryInterval
public import LpGowers.DiscreteTensorization

/-! # Sharp exponents on all binary boxes, Theorem 1.5(a) -/
@[expose] public section
namespace LpGowers.Discrete

/-- The signed one-dimensional counts and the two-point scalar inequality
determine both critical exponents simultaneously in every ambient dimension. -/
theorem binaryClaim : BinaryClaim :=
  binaryClaim_of_one_dimensional_extension (fun d k _ => functionExponent_of_one_dimensional d k 2)

end LpGowers.Discrete
