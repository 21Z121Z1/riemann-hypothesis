import Formalism.SharpRestriction.AdmissibleParameterJoins.Bundle0009
import Formalism.SharpRestriction.SmoothDesignExistence.SumOverPrimesHypotheses
import Formalism.SharpRestriction.AdmissibleParameterJoins.Bundle0010
import Formalism.SharpRestriction.Divisibility.ChainOperators.Bundle0002
import Formalism.LocalToGlobal.Bundle0002

-- bundled from Formalism.LocalToGlobal.GroupLattices.AdmissibleOfInclusion
section
noncomputable section

namespace Formalism.L2.G.Adm2In

open Formalism.BasicNotions Formalism.MainNotions

structure Adm2In (𝒞 : FamClass) : Prop where

  pt0 : Closed 𝒞 fun Fm _ => ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (_ : Fm.x1 < x) (i : Fm.Ix x), ∀ u, Formalism.MainNotions.product_first_zeroth_parts.Conclusion6 (Fm.D x i) u
  ptTw : Closed 𝒞 fun Fm _ => ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (hx : Fm.x1 < x) (i : Fm.Ix x),
    Formalism.MainNotions.WeightDegreeSizes.TwistedChainIntegral (Fm.D x i) (Fm.ex x hx i).tw
  per0 : Closed 𝒞 fun Fm _ => ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (_ : Fm.x1 < x) (i : Fm.Ix x), Formalism.MainNotions.WeightDegreeSizes.PeriodClassSumWeyl (Fm.D x i)
  perTw : Closed 𝒞 fun Fm _ => ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (hx : Fm.x1 < x) (i : Fm.Ix x),
    Formalism.MainNotions.WeightDegreeSizes.TwistedPeriodIntegral (Fm.D x i) (Fm.X x i) (Fm.ex x hx i).tw

  serv : Closed 𝒞 fun Fm _ => WeilJacquetShalikaLaw.ServF Fm

  p10 : Closed 𝒞 fun Fm _ => ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (hx : Fm.x1 < x) (i : Fm.Ix x),
    ∀ u, Formalism.MainNotions.product_first_zeroth_parts.Conclusion5Sharp (Fm.D x i) u ∧ Formalism.MainNotions.product_first_zeroth_parts.TupleChainSharpColumnValuation (Fm.X x i) (Fm.ex x hx i).tw u

  dgt : Closed 𝒞 fun Fm _ => ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (_ : Fm.x1 < x) (i : Fm.Ix x), Formalism.MainNotions.WeightDegreeSizes.LevelPrimeCoprimeStabiliser (Fm.D x i)

  atG : Closed 𝒞 fun Fm _ => ∃ C1 C2 : ℝ, Formalism.MainNotions.WeightDegreeSizes.FamilyPeriodFormCond Fm C1 C2 ∧ Formalism.MainNotions.WeightDegreeSizes.familySizeBoundAtTypePrime Fm C1

end Formalism.L2.G.Adm2In

end
end

-- bundled from Formalism.LocalToGlobal.GroupLattices.ServiceOfTiedSelection
section
noncomputable section

namespace Formalism.L2.G.ServT

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Pk Formalism.L2

structure ServT (𝒞 : FamClass) (sel : TSel 𝒞) : Prop where

  twU : Closed 𝒞 fun Fm _ => ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (hx : Fm.x1 < x) (i : Fm.Ix x),
    ∃ LC, WeilJacquetShalikaLaw.CmpV (Fm.ex x hx i).cmp (Fm.X x i) (Fm.ex x hx i).tw (reW (Fm.Gy x i) LC) ∧ SysTw (Fm.D x i) (Fm.L x i)
      (Fm.Gx x i) Fm.GK (Fm.X x i) (reW (Fm.Gy x i) LC) (Fm.ex x hx i).lev (Fm.ex x hx i).errX Fm.cX.err 1

  pdv : Closed 𝒞 fun Fm _ => ∀ (hc : 𝒞 Fm) (x : ℝ) (hx : Fm.x1 < x) (h0 : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
    ((((sel Fm hc).2 x hx h0 i).T.ker.ent.UnUnit ∧ OrbitPlaces.KmapRat ((sel Fm hc).2 x hx h0 i).T.ker.ent ∧
        OrbitPlaces.KFi (Fm.D x i) (Fm.ex x hx i).tw ∧ OrbitPlaces.Stab0 (Fm.D x i)) ∧
      ∃ (ep : _) (be : _) (sg : _),
        OrbitPlaces.EvenConditionsInert (OrbitPlaces.ofKer (nuRowOK (Fm.D x i)) ((sel Fm hc).2 x hx h0 i).T.ker.ent ep be sg) (Fm.X x i) ∧
        OrbitPlaces.EvenConditionsAtC (OrbitPlaces.ofKer (nuRowOK (Fm.D x i)) ((sel Fm hc).2 x hx h0 i).T.ker.ent ep be sg) (Fm.X x i) ∧
        OrbitPlaces.OrbitBoundWithoutOperator (OrbitPlaces.ofKer (nuRowOK (Fm.D x i)) ((sel Fm hc).2 x hx h0 i).T.ker.ent ep be sg) (Fm.Gx x i) Fm.GK ∧
        OrbitPlaces.JetIntegralityBis (OrbitPlaces.ofKer (nuRowOK (Fm.D x i)) ((sel Fm hc).2 x hx h0 i).T.ker.ent ep be sg) (Fm.X x i) ∧
        OrbitPlaces.ThetaKernelShapeAtD (OrbitPlaces.ofKer (nuRowOK (Fm.D x i)) ((sel Fm hc).2 x hx h0 i).T.ker.ent ep be sg) (Fm.X x i) ∧
        OrbitPlaces.Shape (Fm.D x i) (Fm.L x i) (Fm.Gx x i)
          (OrbitPlaces.ofKer (nuRowOK (Fm.D x i)) ((sel Fm hc).2 x hx h0 i).T.ker.ent ep be sg))

theorem closed_imp_class {𝒞 : FamClass} {P Q : ∀ {eps : ℝ}, FamP eps → ℝ → Prop} (hP : Closed 𝒞 P)
    (h : ∀ {eps : ℝ} (Fm : FamP eps) (CH : ℝ), 𝒞 Fm → P Fm CH → Q Fm CH) : Closed 𝒞 Q := by
  unfold Closed at hP ⊢
  obtain ⟨ε1, hε1, hP⟩ := hP
  refine ⟨ε1, hε1, fun eps he he1 => ?_⟩
  obtain ⟨K, hK⟩ := hP eps he he1
  exact ⟨K, fun Fm CH hc hL => h Fm CH hc (hK Fm CH hc hL)⟩

theorem service_of_tied_selection {𝒞 : FamClass} (sel : TSel 𝒞) (h : ServT 𝒞 sel) : SumOverPrimesHypotheses 𝒞 where
  twU := h.twU
  pdv := closed_imp_class h.pdv fun Fm _ hc hp => ⟨(sel Fm hc).1, fun x hx0 hx i => ⟨_, hp hc x hx hx0 i⟩⟩

theorem servF_of_servT {𝒞 : FamClass} (sel : TSel 𝒞) (hD : Closed 𝒞 fun Fm _ => DGamSize Fm) (h : ServT 𝒞 sel) :
    Closed 𝒞 fun Fm _ => WeilJacquetShalikaLaw.ServF Fm :=
  sum_over_primes_service 𝒞 hD (service_of_tied_selection sel h)

end Formalism.L2.G.ServT

end
end

