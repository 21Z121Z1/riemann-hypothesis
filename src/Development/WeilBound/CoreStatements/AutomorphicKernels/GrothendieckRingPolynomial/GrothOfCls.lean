import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.GrothendieckRingPolynomial.ClassGlEqClass
import Development.WeilBound.CoreStatements.AutomorphicKernels.GrothendieckRingPolynomial.ClassProductIrreducibleLeft
import Development.WeilBound.CoreStatements.AutomorphicKernels.GrothendieckRingPolynomial.MulClassBasisRight
import Development.WeilBound.CoreStatements.AutomorphicKernels.GrothendieckRingPolynomial.ClassProductIrreducibleFold
import Development.WeilBound.CoreStatements.AutomorphicKernels.GrothendieckRingPolynomial.ClassProductIrreducibleCast
import Development.WeilBound.CoreStatements.AutomorphicKernels.GrothendieckRingPolynomial.Bundle0003
import Development.WeilBound.CoreStatements.AutomorphicKernels.GrothendieckRingPolynomial.Bundle0002
import Development.WeilBound.CoreStatements.AutomorphicKernels.GrothendieckRingPolynomial.Bundle0001

namespace PositivityTheory.Groth

theorem groth_of_cls (H : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], Cls k) :
    GlobalTheory.Published.GrothendieckRingPolynomial := by
  refine groth_of_steps (fun k _ _ _ _ => ?_) triAut uniTri
  have hc := H k
  have hm := mulCls k
  have ha := assoc k hm
  have hco := comm k
  have ho := one k
  have hp := prodList k hm
  exact ⟨hc, hm, ha, hco, ho, hp, tri k hc, multOne k hc hm ha hco ho hp, jCls k, jSeg k, altSum k⟩

end PositivityTheory.Groth
