import Formalism.SharpRestriction.AdmissibleParameterJoins.Bundle0007
import Formalism.SharpRestriction.AdmissibleParameterJoins.Bundle0005
import Formalism.SharpRestriction.Divisibility.WeightDegreeSizes
import Formalism.SharpRestriction.AdmissibleParameterJoins.Bundle0006

-- bundled from Formalism.SharpRestriction.AdmissibleParameterJoins.DIVfromGLl
section
noncomputable section

namespace Formalism.MainNotions.J

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions.WeilJacquetShalikaLaw Formalism.MainNotions.WeightDegreeSizes

variable {D : D7} {L : SizeData₂ D}

theorem chain_norm_of_sixth (h6 : ∀ u, Formalism.MainNotions.product_first_zeroth_parts.Conclusion6 D u) : MemberChainIntegral D := h6

theorem pairing_integrality_both_sides (Dx : DivX D) (T : TwForms D) : PairingFromIntegrality D Dx T := fun h6 h6T hp hpT =>
  ⟨fun hD => ⟨fun u w _ => pairing_lift_valuation_bound hD h6 hp u w, fun u μ _ hμ w _ hQ => pairTw_of hD h6T hpT u μ hμ w hQ⟩,
   fun hD => ⟨fun u w _ => pairing_lift_valuation_bound hD h6 hp u w, fun u μ hμ w _ hQ => pairTw_of hD h6T hpT u μ hμ w hQ⟩⟩

theorem levelColumn_of_sharpBound {Dx : DivX D} {T : TwForms D} (h5 : ∀ u, Formalism.MainNotions.product_first_zeroth_parts.Conclusion5Sharp D u) (hTw : LevelPrimeColumnOtherTuples D Dx T) :
    ValuationAtLevelPrime D Dx T := fun u w hw μ hQ x hx =>
  ⟨fun _ => ColGe0_atT D u (h5 u) w hw x hx, fun hμ => hTw u w hw μ hμ hQ x hx⟩

theorem periodBound_at_level_of_twisted {Dx : DivX D} {T : TwForms D} (hD : DGamDef D) (hE : ∀ u, Formalism.MainNotions.product_first_zeroth_parts.ETDef D u L)
    (hN : NuAtTDef D L) (hG : LevelPrimeCoprimeStabiliser D) (hp : PeriodClassSumWeyl D) (h6T : TwistedChainIntegral D T) (hpT : TwistedPeriodIntegral D Dx T)
    (hTw : LevelPrimeColumnOtherTuples D Dx T) (h5 : ∀ u, Formalism.MainNotions.product_first_zeroth_parts.Conclusion5Sharp D u) (h6 : ∀ u, Formalism.MainNotions.product_first_zeroth_parts.Conclusion6 D u) : PeriodBoundAtLevelPrime D L :=
  period_integral_at_levelPrime (pairing_integrality_both_sides Dx T h6 h6T hp hpT).2 hD hE hN hG (levelColumn_of_sharpBound h5 hTw)

theorem sizeData_at_level_primes_of_defs {X : ErrX D} {K : Formalism.MainNotions.G.Consts} {c : ErrC} (P : ParameterChoice' D L) (hF : L.FDef) (hE : L.EDef X K c)
    (hTg : LevelPrimeNotTypePrime D) : LevelPrimeSizes D L := ETDef_of P hF hE hTg

theorem gains_losses_eq_defined (Gi : Formalism.MainNotions.G.Inst D L) (K : Formalism.MainNotions.G.Consts) (X : ErrX D) (c : ErrC)
    (hF : ∀ w, Formalism.MainNotions.G.ParametersFill Gi K w) (hE : L.EDef X K c) : Formalism.MainNotions.LocalQuadraticParts.ZeroGainAbove L := stmtZ Gi K X c hF hE

end Formalism.MainNotions.J

end
end

-- bundled from Formalism.SharpRestriction.AdmissibleParameterJoins.GandSy
section
noncomputable section

namespace Formalism.MainNotions.J

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions.G Formalism.MainNotions.WeilJacquetShalikaLaw

variable {D : D7} {L : SizeData₂ D}

theorem period_conditions_of_pairing {X : Inst D L} {Y : LatInst D} {K : Consts} {c : LatCmp D} {Dx : DivX D} {T : TwForms D}
    {lev : LevelData D} {Xe : ErrX D} {ce : ErrC}
    (hP : Formalism.MainNotions.WeightDegreeSizes.PairingAtEveryPlace D Dx T) (hE : ErrDefs D L Xe lev K ce) (hET : Formalism.MainNotions.WeightDegreeSizes.LevelPrimeSizes D L)
    (ht : Ties9 D L X Y c) (hS : c.NuServedDef X Y K) (hNT : NuAtTDef D L) (hN : Formalism.MainNotions.WeightDegreeSizes.NuInM D L)
    (hGI : Formalism.MainNotions.WeightDegreeSizes.ServedHasModel X K) (hF : ∀ w, ParametersFill X K w)
    (hcs : ∀ p : ℕ, p.Prime → IsCs D p → p ∈ L.drop) (hG : Formalism.MainNotions.WeightDegreeSizes.LevelPrimeCoprimeStabiliser D)
    (h1 : Formalism.MainNotions.WeilJacquetShalikaLaw.Conclusion1 D L X Y K c Dx T lev Xe ce 1) (h5 : Formalism.MainNotions.WeightDegreeSizes.ValuationAtLevelPrime D Dx T) {C1 C2 : ℝ}
    (hCL : Formalism.MainNotions.LiftErrorLocal.PropositionCLatticeBound D L Xe C1 C2) (hSg : Formalism.MainNotions.WeightDegreeSizes.SgAtG D L Xe C1) (hlin : Formalism.MainNotions.WeightDegreeSizes.PerColSmul D) :
    Formalism.MainNotions.LocalQuadraticParts.adm2 D L :=
  Formalism.MainNotions.WeightDegreeSizes.l2_bound_of_inputs hP hE hET ht hS hNT hN hGI (Formalism.MainNotions.WeightDegreeSizes.gainLe_of_fills hF hcs) hG h1 h5 hCL hSg hlin

theorem no_gain_condition_of_pairing_sign {K : Consts} {Dx : DivX D} {T : TwForms D} {lev : LevelData D} {Xe : ErrX D} {ce : ErrC}
    (hP : Formalism.MainNotions.WeightDegreeSizes.PairingAtEveryPlace D Dx T) (hE : ErrDefs D L Xe lev K ce) (hF : L.FDef)
    (h : Formalism.MainNotions.WeilJacquetShalikaLaw.ColumnValuationAwayFromTypePrimes D L K Dx T lev Xe ce 1) {C1 C2 : ℝ} (hCL : Formalism.MainNotions.LiftErrorLocal.PropositionCLatticeBound D L Xe C1 C2)
    (hSg : Formalism.MainNotions.WeightDegreeSizes.SgAtG D L Xe C1) : Formalism.MainNotions.LocalQuadraticParts.adm12 D L :=
  Formalism.MainNotions.WeightDegreeSizes.fourth_complement_of_pairing hP hE hF h hCL hSg

theorem servedModel_of_params (P : ParameterChoice' D L) (X : Inst D L) (K : Consts) (h3 : 3 ≤ L.sc.x ^ (L.sc.ez / 5)) :
    Formalism.MainNotions.WeightDegreeSizes.ServedHasModel X K := by
  unfold Formalism.MainNotions.WeightDegreeSizes.ServedHasModel
  intro u w hw hV
  refine Formalism.BasicNotions.gIdx_of_cand P K h3 u _ ?_ hw
  unfold VV at hV
  by_contra hc
  exact hV (if_neg (fun h => hc h.1))

end Formalism.MainNotions.J
end
end

