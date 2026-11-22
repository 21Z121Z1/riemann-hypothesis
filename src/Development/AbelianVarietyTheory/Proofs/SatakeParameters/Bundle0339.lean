import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0006
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TendstoOneOfSummable
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0208
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0338
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0313
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0310
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0312
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0019
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
import Formalism.LocalToGlobal.GroupLattices.AdmissibleAtGeneratorPlaces
import Formalism.SharpRestriction.AdmissibleParameterJoins.Bundle0010
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0246

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaEigenCompatibilityFifth
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem GlobalTheory.EigStrSplit.str_split : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep), Formalism.MainNotions.SumRepresentations.Conclusion41 D → Formalism.MainNotions.SumRepresentations.adm7 D → Formalism.MainNotions.SumRepresentations.tieLab D → ∀ (i : D.nd.Loc) (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i), ∀ x ∈ ZgoodN D.nd D.naut i, ∀ f : D.what₂.Mt (D.nd.mu i) (j.1 + 1), (hj ▸ f : D.what₂.Mt (D.nd.mu i) (D.nd.j i)) ∈ eigC D.nd D.naut i x → ∀ y, X.R.extV j (X.tupT (D.nd.mu i)) y = X.fn hμ j f → y ≠ 0 → ∀ h, GlobalTheory.Hk3.IsOpsV X.R j (X.tupT (D.nd.mu i)) h → ∀ (s : GlobalTheory.DownLift.Sys D) (B : GlobalTheory.LFun.Fam D.host.E), GlobalTheory.DownLift.IsEigV X.R j (X.tupT (D.nd.mu i)) h s y → GlobalTheory.LFun.IsSysParamD D (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl X.R (X.tupT (D.nd.mu i))) (Formalism.IndefR.Links.Vc D j).rank s B → ∀ w : HeightOneSpectrum (𝓞 D.host.E), GlobalTheory.Hk3.Good X.R (X.tupT (D.nd.mu i)) w → Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) (w.under (𝓞 D.host.F)) → ∃ B' : Multiset ℂ, (B w).map (fun a : ℂˣ => (a : ℂ)) = B' + GlobalTheory.DownLift.str (Ideal.absNorm w.asIdeal) (GlobalTheory.DownLift.valV X.R j (X.tupT (D.nd.mu i)) w : ℂ) D.R.t ∧ ∀ a ∈ B', ‖a‖ ≤ (Ideal.absNorm w.asIdeal : ℝ) ^ (((D.R.r : ℝ) - 1) / 2) := by
  intro hAF hL D P X hA h41 h7 htl i hμ j hj x hx f hf y hy hy0 hh hops s B hs hB w hw hsp
  obtain ⟨Q, hQx, hu, hBQ⟩ := GlobalTheory.T.theta_eigen_compatibility_eighth hAF hL D P X hA h41 h7 htl i hμ j hj x hx f hf y hy hy0 hh hops s B hs hB w hw hsp
  obtain ⟨-, Sig, ⟨P0, hP0, hbc⟩, hgood⟩ := hx
  have hcusp := GlobalTheory.T.goodLabels_rank_part_parameter_cuspidal D htl i x Sig ⟨P0, hP0, hbc⟩ hgood
  obtain ⟨hS, hQ⟩ := GlobalTheory.T.good_place_outside_bad_sets hL D P X hA h41 htl i w hw
  have hz := GlobalTheory.T.frobEig_tw_eq_inv_valV_of_isSplit hAF hL D P X hA htl i hμ j hj w hw hsp
  obtain ⟨B', e, hB'⟩ := GlobalTheory.T.base_change_twisted_cusp_parts hAF hL D P h41 h7 htl i x Q P0 Sig hQx hP0 hcusp hbc w hsp hS hQ hu _ hz
  exact ⟨B', hBQ.trans e, hB'⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TypePrimePeriodRowOfConstructedPointChains
section
noncomputable section

namespace GlobalTheory.AtG

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.Fc GlobalTheory.Mem.Top GlobalTheory.AtG

theorem row_atG_of_jetSplitAmb : JetSplitAmb → ∀ {Bd : BdT} (Q : V4.Slot) (Lk : LkT Bd),
    RowE Q Lk (fun _ D O _ _ => ∀ μ, (μ = D.what₂.mu0 ∨ ∃ w, μ = D.what₂.muAt w) → TiesAt D O.ex.errX O.X μ) →
    Row Q Lk fun 𝒜 _ => Closed (W3 𝒜) fun Fm _ => ∃ C1, (∃ x0, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i,
      Formalism.L2.G.Adm2InU.UsedTuplesBoundByConstant (Fm.D x i) (Fm.L x i) (Fm.ex x hx i).errX C1) ∧ WeightDegreeSizes.familySizeBoundAtTypePrime Fm C1 := by
  intro hJ Bd Q Lk hE
  refine ⟨_, hE, fun 𝒜 σ s => ?_⟩
  refine ⟨1 / 100, by norm_num, fun eps he hle => ?_⟩
  obtain ⟨xs, hxs⟩ := GlobalTheory.T.kernelDegrees_small_against_typePrimes eps he (by linarith)
  refine ⟨⟨0, fun _ => 0, fun _ => 2, fun _ => 0⟩, fun Fm CH hc hL => ?_⟩
  have hg : (2 : ℝ) ≤ Fm.cX.err.g := hL.2.2.1 Fm.cX.err.g (by simp [FamP.cMid])
  obtain ⟨κ, -, -, t⟩ := s Fm (w3_a hc)
  refine ⟨1, ⟨xs, fun x hx hx0 i => ?_⟩, Formalism.MainNotions.J.family_type_prime_loss Fm zero_le_one (by linarith)⟩
  refine GlobalTheory.T.propositionCOneUsedTuples_one_of_tiesAt_sizeAt hJ (Fm.D x i) (Fm.L x i) (Fm.ex x hx i).errX (Fm.X x i) (t x hx i).2 ?_
  exact hxs (Fm.D x i) (Fm.L x i) (Fm.params x hx i) (Fm.sizes x hx i) (Fm.L_eps x i) (by rw [Fm.L_x x i hx]; exact hx0)

end GlobalTheory.AtG

end
end

