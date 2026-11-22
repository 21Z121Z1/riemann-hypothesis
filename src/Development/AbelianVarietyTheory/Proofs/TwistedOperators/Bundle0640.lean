import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0502
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0316
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0006
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0012
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0629
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0261
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0451
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1947
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1876
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1759
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0577
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0205
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0634
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CompletedTensorLatticeStrongApproxOpenCompact
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0232
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0320
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0533
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0227
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0237
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsMixedLagrangianChartIntegralRowChange
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0524
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0565
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0570
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0609
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0584
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0586
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0515
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0633
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0232
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0630

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFiniteSupportMulLatticeStabilizer
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.TruncAway

open GlobalTheory.AdelicU

theorem exists_trunc_mul_inK : ∀ {D : D7} (V : HSp D) (L : GlobalTheory.FinPl.Lat V), L.FG → Submodule.span D.host.E (L : Set (Fin V.rank → D.host.E)) = ⊤ →
  ∀ (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) (b : GA D V), ∃ (b' : GA D V) (P : Finset (HeightOneSpectrum (𝓞 D.host.F))),
    (∀ v ∉ P, GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v b' = 1) ∧ GlobalTheory.FinPl.InK V L (fun v => v ∉ S) (b'⁻¹ * b) := by
  intro D V L hfg hspan S b
  haveI : Submodule.IsLattice D.host.E L := ⟨hfg, hspan⟩
  have hfin := Filter.eventually_cofinite.1 (eventually_proj_mem_stabLoc D.sp.cm.sig V.gram L b)
  classical
  let P : Finset (HeightOneSpectrum (𝓞 D.host.F)) := S ∪ hfin.toFinset
  let b' : GA D V := ofInf D.sp.cm.sig V.gram (projInf D.sp.cm.sig V.gram b) *
    embAt D.sp.cm.sig V.gram P (projAt D.sp.cm.sig V.gram P b)
  have hat := mem_atPts.1 (embAt_mem D.sp.cm.sig V.gram P (projAt D.sp.cm.sig V.gram P b))
  have hout : ∀ v ∉ P, proj D.sp.cm.sig V.gram v b' = 1 := fun v hv => by
    simp only [b', map_mul, proj_ofInf, one_mul]
    exact hat.2 v hv
  have hin : ∀ v ∈ P, proj D.sp.cm.sig V.gram v b' = proj D.sp.cm.sig V.gram v b := fun v hv => by
    simp only [b', map_mul, proj_ofInf, one_mul]
    exact proj_embAt D.sp.cm.sig V.gram P _ ⟨v, hv⟩
  have hinf : projInf D.sp.cm.sig V.gram b' = projInf D.sp.cm.sig V.gram b := by
    simp only [b', map_mul, projInf_ofInf, mem_finPts.1 hat.1, mul_one]
  refine ⟨b', P, hout, ?_, ?_⟩
  · rw [GlobalTheory.FinPl.KOpen.mem_grpAt_iff]
    refine ⟨mem_finPts.2 ?_, fun v hv => ?_⟩
    · rw [map_mul, map_inv, hinf, inv_mul_cancel]
    · have hvP : v ∈ P := Finset.mem_union_left _ (not_not.1 hv)
      rw [map_mul, map_inv, hin v hvP, inv_mul_cancel]
  · refine GlobalTheory.FinPl.KOpen.moves_of_levelOpen V L hfg _ (mem_levelOpen.2 fun v => ?_)
    by_cases hv : v ∈ P
    · rw [map_mul, map_inv, hin v hv, inv_mul_cancel]; exact one_mem _
    · rw [map_mul, map_inv, hout v hv, inv_one, one_mul]
      by_contra h
      exact hv (Finset.mem_union_right _ (hfin.mem_toFinset.2 h))

end GlobalTheory.TruncAway

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsHeisenbergDerivativeArchimedeanDirectionStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_heisenberg_derivative_archimedean_direction : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Wd)
    (ψ : AddChar (AF F) ℂ), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ →
    ∀ (g : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)) (u : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E)),
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) u →
      ∃ g₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d),
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (M.heisLine ψ u) g g₁ := by
  first | exact @GlobalTheory.HeisLineDeriv.exists_actsD | exact GlobalTheory.HeisLineDeriv.exists_actsD | (intros; apply GlobalTheory.HeisLineDeriv.exists_actsD <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIdeleGeneratesPolarisationIdealConjPlaces
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LiftLevel

set_option maxHeartbeats 4000000 in

theorem exists_isGen : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (hn : T.rank ≤ S.rank) (ΛT : Lt D.host.E T.rank), IsSelfDualC T ΛT → IsAA C.X.Λ ΛT → ∀ (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)), Formalism.L2.DIV.IsFrame βS (stdL D.host.E S.rank) → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ), Pg.Nonempty → (∀ PP, PP ∈ Pg ∨ PP ∈ Q → (2 : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ e : AE D, IsIdemSum e (Pg ∪ Q) → ∃ a : AE D, (∃ b : AE D, a * b = e) ∧ GlobalTheory.LiftLevel.IsGen C βS βT Pg Q e a := by
  intro D S T C hn ΛT hsd hAA βS βT hβS hβT Pg Q ξ hPg h2 e he
  have hS : S.gram = 1 := C.m.gS
  obtain ⟨γ, hγ, s, hs, h1, h2'⟩ := GlobalTheory.T.exists_global_scalar_prime_to_conj_polarisationLattice' D T.rank C.X.Λ ΛT hAA (Pg ∪ Q)
  obtain ⟨t, ht, hte⟩ := GlobalTheory.T.exists_integral_inverse_on_conjugate_half D (Pg ∪ Q) e he s hs
  have hee : e * e = e := GlobalTheory.PlaceVec.idemSum_mul_self he
  have hecinf : infPart D (cA D e) = 0 := GlobalTheory.PlaceVec.infPart_cA (GlobalTheory.PlaceVec.idemSum_infPart he)
  have hinf : ∀ x : WO S T, IsHalf (cA D e) x → IsFinPt x := by
    intro x hx
    ext i j
    simp only [Matrix.map_apply, Matrix.zero_apply]
    rw [← hx i j, map_mul, hecinf, zero_mul]
  have hmulA : ∀ (L1 L2 : Lt D.host.E T.rank) (c : D.host.E), (∀ v ∈ L1, ((s : D.host.E) * c) • v ∈ L2) →
      ∀ x : WO S T, IsHalf (cA D e) x → x ∈ hatA S T (tens (stdL D.host.E S.rank) L1) →
        incA D c • x ∈ hatA S T (tens (stdL D.host.E S.rank) L2) := by
    intro L1 L2 c hc x hx hxm
    have h3 := GlobalTheory.T.incA_smul_mem_adelicCompletionMatrixGroup D S T _ L1 L2 _ hc x hxm
    have h4 := smul_mem_hatA_of_int (fun o y hy => HatLat.smul_mem_tens _ _ o hy) ht h3
    convert h4 using 1
    ext i j
    simp only [Matrix.smul_apply, smul_eq_mul, map_mul]
    have hxij := hx i j
    calc incA D c * x i j = incA D c * (cA D e * x i j) := by rw [hxij]
      _ = (t * incA D (s : D.host.E) * cA D e) * (incA D c * x i j) := by rw [hte]; ring
      _ = t * (incA D (s : D.host.E) * incA D c * (cA D e * x i j)) := by ring
      _ = t * (incA D (s : D.host.E) * incA D c * x i j) := by rw [hxij]
  have hsc : ∀ (I : Ideal (𝓞 D.host.E)) (L1 L2 : Lt D.host.E T.rank) (c : D.host.E), (∀ v ∈ L1, c • v ∈ L2) →
      ∀ v ∈ I • L1, c • v ∈ I • L2 := by
    intro I L1 L2 c hc v hv
    refine Submodule.smul_induction_on hv (fun i hi w hw => ?_) (fun a b ha hb => ?_)
    · rw [smul_comm]
      exact Submodule.smul_mem_smul hi (hc w hw)
    · rw [smul_add]; exact add_mem ha hb
  refine ⟨e * incA D (star γ⁻¹), ⟨e * incA D (star γ), ?_⟩, ?_⟩
  · have hu : incA D (star γ⁻¹) * incA D (star γ) = 1 := by
      rw [← map_mul, star_inv₀, inv_mul_cancel₀ (star_ne_zero.mpr hγ), map_one]
    calc e * incA D (star γ⁻¹) * (e * incA D (star γ)) = (e * e) * (incA D (star γ⁻¹) * incA D (star γ)) :=
          mul_mul_mul_comm _ _ _ _
      _ = e := by rw [hu, mul_one, hee]
  intro x hx
  have hadj : adjA S T βS βT (e * incA D (star γ⁻¹)) x = adjA S T βS βT 1 (incA D γ⁻¹ • x) :=
    GlobalTheory.T.ideleFrameAdjointMatrix_half_idempotent_smul D S T βS βT e γ⁻¹ x hx
  have hy : IsHalf (cA D e) (incA D γ⁻¹ • x) := by
    intro i j
    simp only [Matrix.smul_apply, smul_eq_mul]
    rw [mul_left_comm, hx i j]
  have hyf := hinf _ hy
  have hback : incA D γ • (incA D γ⁻¹ • x) = x := by
    rw [smul_smul, ← map_mul, mul_inv_cancel₀ hγ, map_one, one_smul]
  rw [hadj]
  obtain ⟨hsq, hle, hconj⟩ := GlobalTheory.T.prod_primes_squarefree_conjugateIdeal_prod D (Pg ∪ Q)
  have hmem : ∀ (I : Ideal (𝓞 D.host.E)),
      (incA D γ⁻¹ • x ∈ hatA S T (tens (stdL D.host.E S.rank) (I • ΛT)) ↔
        x ∈ hatA S T (tens (stdL D.host.E S.rank) (I • C.X.Λ))) := by
    intro I
    constructor
    · intro hm
      have := hmulA (I • ΛT) (I • C.X.Λ) γ (hsc I ΛT C.X.Λ _ h2') _ hy hm
      rwa [hback] at this
    · intro hm
      exact hmulA (I • C.X.Λ) (I • ΛT) γ⁻¹ (hsc I C.X.Λ ΛT _ h1) x hx hm
  have hctop : conjI (⊤ : Ideal (𝓞 D.host.E)) = ⊤ := by
    rw [Ideal.eq_top_iff_one]
    unfold conjI
    exact Ideal.subset_span ⟨1, Submodule.mem_top, by simp⟩
  constructor
  · have hB := GlobalTheory.T.ideleFrameAdjoint_integral_iff_dualLattice D S T hS ΛT hsd βS βT hβT ⊤ (by rw [← Ideal.one_eq_top]; exact squarefree_one) _ hyf
    rw [hctop, Submodule.top_smul] at hB
    have h5 := hmem ⊤
    rw [Submodule.top_smul, Submodule.top_smul] at h5
    rw [← h5, ← hB]
    constructor
    · intro h; exact ⟨h, fun PP hPP => absurd (top_le_iff.mp hPP) PP.isPrime.ne_top⟩
    · intro h; exact h.1
  · have hB := GlobalTheory.T.ideleFrameAdjoint_integral_iff_dualLattice D S T hS ΛT hsd βS βT hβT _ hsq _ hyf
    rw [hconj] at hB
    have hB' : (IsIntM (adjA S T βS βT 1 (incA D γ⁻¹ • x)) ∧ ∀ PP : Formalism.L2.DIV.Pl D.host.E,
        (∏ PP ∈ Pg ∪ Q, PP.asIdeal) ≤ PP.asIdeal → redM PP (adjA S T βS βT 1 (incA D γ⁻¹ • x)) = 0) ↔
        incA D γ⁻¹ • x ∈ hatA S T (tens (stdL D.host.E S.rank) (liftI Pg Q • ΛT)) := hB
    have h5 := hmem (liftI Pg Q)
    rw [← h5, ← hB']
    simp only [hle]

end GlobalTheory.LiftLevel

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsMixedLagrangianChartIntegralRowChangeStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At piW psiLoc chrW)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlipMatch

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_mixedLagrangian_chart_integral_rowChange : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil) (B : Frames G) (t : T) (i j : Fin D.R.m) (M : Vol G) (e : Num G i j) (Bs : Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (X : Chars D.host.F D.host.E)
    (om : Rep D.sp.cm.sig Γ.V Γ.W) (om' : Rep D.sp.cm.sig Γ.V' Γ.W) (h : IsTripleOf W M t i j e Bs Γ X), IsTriple Bs Γ X om om' → IsTied t i j e Bs Γ X →
    ∀ (v : Bs.P) (w : Pl D.host.E), splitPrime (Bs.τ v) = w → ∀ jj : Fv D.host.F v ≃+* Kw w, IsPlaceIso (Bs.τ v) w jj → IsLocIso jj →
    ∀ cc : GL (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (Kw w), (Γ.W.bas v).val.map jj * cc.val = basCols B e w →
    ∃ g ∈ KO (Kw w) (Fin (spW G i j).rank),
      IsMixChart v.1 (mixHalf e (atPl w 1)) (mixHalf e (cA D (atPl w 1))) (mixCo B t e w)
        (fun u => chart jj (finCongr (rankW G t i j w)) (colsEq t e w) g (invT cc) (coX (Bs.τ v) (Γ.V.bas v) (Γ.W.bas v) u))
        (fun u => (xiAt w)⁻¹ • chart jj (finCongr (rankW G t i j w)) (colsEq t e w) (invT g) cc
          (coY D.sp.cm.sig Γ.V Γ.W (Bs.τ v) (Γ.V.bas v) (Γ.W.bas v) u))
        (Assignment.one.block _ _)ᶜ := by
  first | exact @GlobalTheory.FlipMatch.RowChart.exists_mixChart | exact GlobalTheory.FlipMatch.RowChart.exists_mixChart | (intros; apply GlobalTheory.FlipMatch.RowChart.exists_mixChart <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRationalFiniteTranslateStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rational_finite_translate : GlobalTheory.FunPr.Hypotheses₂ → (∀ D, GlobalTheory.NormSum.Inp D) → ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type}
    {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
    (ch : Choice R), ch.Is → ∀ (X : Node), DefNode D.R.m X → ∀ (Q : Finset ℕ), (∀ q ∈ Q, q.Prime) → ∀ x : FinPt ch.G X,
    ∃ r s x₀ : FinPt ch.G X, GlobalTheory.MovedKappaEx.RatFin _ r ∧ s ∈ GlobalTheory.MovedKappaEx.splitOff _ Q ∧
      GlobalTheory.SumSize.latAt ch.S.toGridChoice X x₀ = stdL D _ ∧ (∀ q ∈ Q, EqAt D q (GlobalTheory.SumSize.latAt ch.S.toGridChoice X (s * x₀)) (stdL D _)) ∧ x = r * s * x₀ := by
  first | exact @GlobalTheory.MovedKappaDec.exists_dec | exact GlobalTheory.MovedKappaDec.exists_dec | (intros; apply GlobalTheory.MovedKappaDec.exists_dec <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExtCastMulReal
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries GlobalTheory.RowReal
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowReal

section Move

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem integral_ker_move (W : G.Weil) (M : Vol G) (p : Pair T) (hp : p.InRange D.R.m)
    {K : Subgroup (GL (Fin (G.V p.small).rank) (Lev.EAf D))} (hM : M.IsAt p.small K)
    (k : GA D (G.V p.small)) (k' : GA D (G.V p.big))
    (hk : MeasurePreserving (fun g : GA D (G.V p.small) => g * k) (M.ν p.small) (M.ν p.small))
    (hk' : Measurable fun g : GA D (G.V p.small) => g * k⁻¹)
    (f : WO (G.pS p) (G.pT p) → ℂ) (hf : IsThetaFunO W.ψ (G.pS p) (G.pT p) f)
    (F : GA D (G.V p.small) → ℂ) (hF : ∀ γ ∈ GQ (G.V p.small), ∀ g, F (γ * g) = F g) (h : GA D (G.V p.big)) :
    ∫ g in M.fd p.small, W.ker p f g (h * k') * F g ∂M.ν p.small =
      ∫ g in M.fd p.small, W.ker p (W.om p (G.toPair p k k') f) g h * F (g * k) ∂M.ν p.small := by
  rw [← setIntegral_fd_mul_right M hM k hk hk' (fun g => W.ker p f g (h * k') * F g) ?_]
  · congr 1
    funext g
    rw [ker_mul]
  · intro γ hγ g
    have e := ker_rat_left W p hp f hf γ hγ 1 (one_mem _) g (h * k')
    rw [one_mul] at e
    simp only [e, hF γ hγ g]

theorem integral_ker_left (W : G.Weil) (M : Vol G) (p : Pair T) (hp : p.InRange D.R.m)
    (f : WO (G.pS p) (G.pT p) → ℂ) (hf : IsThetaFunO W.ψ (G.pS p) (G.pT p) f)
    (F : GA D (G.V p.small) → ℂ) (γ : GA D (G.V p.big)) (hγ : γ ∈ GQ (G.V p.big)) (h : GA D (G.V p.big)) :
    ∫ g in M.fd p.small, W.ker p f g (γ * h) * F g ∂M.ν p.small =
      ∫ g in M.fd p.small, W.ker p f g h * F g ∂M.ν p.small := by
  congr 1
  funext g
  have e := ker_rat_left W p hp f hf 1 (one_mem _) γ hγ g h
  rw [one_mul] at e
  rw [e]

end Move

end GlobalTheory.RowReal

namespace GlobalTheory.RowReal

section Paths

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem pathLift_column_leftInvariant (W : G.Weil) (M : Vol G) (t : T) : ∀ (n : ℕ), n ≤ D.R.m →
    ∀ (f : ∀ j : Fin n, Sch G (.col t j)), (∀ j : Fin n, IsThetaFunO W.ψ (G.pS (.top t j)) (G.pT (.top t j)) (f j)) →
    ∀ (φ : Fn G (.top 0)), (∀ γ ∈ GQ (G.V (.top 0)), ∀ g, φ (γ * g) = φ g) →
    ∀ γ ∈ GQ (G.V (.top n)), ∀ h,
      liftP W M (colPath t n) (colFam t n f) φ (γ * h) = liftP W M (colPath t n) (colFam t n f) φ h
  | 0, _, _, _, _, hφ, γ, hγ, h => hφ γ hγ h
  | n + 1, hn, f, hf, φ, _, γ, hγ, h => by
    show liftA W M (.col t n) (f (Fin.last n)) _ (γ * h) = liftA W M (.col t n) (f (Fin.last n)) _ h
    simp only [liftA_apply]
    exact integral_ker_left W M (.top t n) hn _ (hf (Fin.last n)) _ γ hγ h

theorem pathLift_row_leftInvariant (W : G.Weil) (M : Vol G) : ∀ (n : ℕ), n ≤ D.R.m →
    ∀ (f : ∀ i : Fin n, Sch G (.right i D.R.m)),
      (∀ i : Fin n, IsThetaFunO W.ψ (G.pS (.chi i D.R.m)) (G.pT (.chi i D.R.m)) (f i)) →
    ∀ (F : Fn G (.grid 0 D.R.m)), (∀ γ ∈ GQ (G.V (.grid 0 D.R.m)), ∀ g, F (γ * g) = F g) →
    ∀ γ ∈ GQ (G.V (.grid n D.R.m)), ∀ h,
      liftP W M (rowPath T D.R.m n) (rowFam D.R.m n f) F (γ * h) = liftP W M (rowPath T D.R.m n) (rowFam D.R.m n f) F h
  | 0, _, _, _, _, hF, γ, hγ, h => hF γ hγ h
  | n + 1, hn, f, hf, F, _, γ, hγ, h => by
    show liftA W M (.right n D.R.m) (f (Fin.last n)) _ (γ * h) = liftA W M (.right n D.R.m) (f (Fin.last n)) _ h
    simp only [liftA_apply]
    exact integral_ker_left W M (.chi n D.R.m) ⟨hn, le_rfl⟩ _ (hf (Fin.last n)) _ γ hγ h

theorem pathLift_column_translate (W : G.Weil) (M : Vol G) (t : T) (κ : ∀ n : ℕ, GA D (G.V (.top n))) : ∀ (n : ℕ), n ≤ D.R.m →
    (∀ j, j < n → (∃ K, M.IsAt (.top j) K) ∧
      MeasurePreserving (fun g : GA D (G.V (.top j)) => g * κ j) (M.ν (.top j)) (M.ν (.top j)) ∧
      Measurable (fun g : GA D (G.V (.top j)) => g * (κ j)⁻¹)) →
    ∀ (f f' : ∀ j : Fin n, Sch G (.col t j)), (∀ j : Fin n, IsThetaFunO W.ψ (G.pS (.top t j)) (G.pT (.top t j)) (f j)) →
    (∀ j : Fin n, W.om (.top t j) (G.toPair (.top t j) (κ j) (κ (j + 1))) (f j) = f' j) →
    ∀ (φ : Fn G (.top 0)), (∀ γ ∈ GQ (G.V (.top 0)), ∀ g, φ (γ * g) = φ g) →
    ∀ h, liftP W M (colPath t n) (colFam t n f) φ (h * κ n) =
      liftP W M (colPath t n) (colFam t n f') (fun x => φ (x * κ 0)) h
  | 0, _, _, _, _, _, _, _, _, _ => rfl
  | n + 1, hn, hκ, f, f', hf, hff, φ, hφ, h => by
    obtain ⟨⟨K, hK⟩, hm, hm'⟩ := hκ n (Nat.lt_succ_self n)
    show liftA W M (.col t n) (f (Fin.last n)) (liftP W M (colPath t n) (colFam t n fun j => f j.castSucc) φ) (h * κ (n + 1)) =
      liftA W M (.col t n) (f' (Fin.last n))
        (liftP W M (colPath t n) (colFam t n fun j => f' j.castSucc) (fun x => φ (x * κ 0))) h
    simp only [liftA_apply]
    have e := integral_ker_move W M (.top t n) hn hK (κ n) (κ (n + 1)) hm hm' (f (Fin.last n)) (hf (Fin.last n)) _
      (pathLift_column_leftInvariant W M t n (by omega) _ (fun j => hf j.castSucc) φ hφ) h
    refine e.trans ?_
    rw [← hff (Fin.last n)]
    congr 1
    funext g
    rw [pathLift_column_translate W M t κ n (by omega) (fun j hj => hκ j (by omega)) _ _ (fun j => hf j.castSucc)
      (fun j => hff j.castSucc) φ hφ g]
    rfl

theorem pathLift_row_translate (W : G.Weil) (M : Vol G) (κ : ∀ n : ℕ, GA D (G.V (.grid n D.R.m))) : ∀ (n : ℕ), n ≤ D.R.m →
    (∀ i, i < n → (∃ K, M.IsAt (.grid i D.R.m) K) ∧
      MeasurePreserving (fun g : GA D (G.V (.grid i D.R.m)) => g * κ i) (M.ν (.grid i D.R.m)) (M.ν (.grid i D.R.m)) ∧
      Measurable (fun g : GA D (G.V (.grid i D.R.m)) => g * (κ i)⁻¹)) →
    ∀ (f f' : ∀ i : Fin n, Sch G (.right i D.R.m)),
      (∀ i : Fin n, IsThetaFunO W.ψ (G.pS (.chi i D.R.m)) (G.pT (.chi i D.R.m)) (f i)) →
    (∀ i : Fin n, W.om (.chi i D.R.m) (G.toPair (.chi i D.R.m) (κ i) (κ (i + 1))) (f i) = f' i) →
    ∀ (F : Fn G (.grid 0 D.R.m)), (∀ γ ∈ GQ (G.V (.grid 0 D.R.m)), ∀ g, F (γ * g) = F g) →
    ∀ h, liftP W M (rowPath T D.R.m n) (rowFam D.R.m n f) F (h * κ n) =
      liftP W M (rowPath T D.R.m n) (rowFam D.R.m n f') (fun x => F (x * κ 0)) h
  | 0, _, _, _, _, _, _, _, _, _ => rfl
  | n + 1, hn, hκ, f, f', hf, hff, F, hF, h => by
    obtain ⟨⟨K, hK⟩, hm, hm'⟩ := hκ n (Nat.lt_succ_self n)
    show liftA W M (.right n D.R.m) (f (Fin.last n)) (liftP W M (rowPath T D.R.m n) (rowFam D.R.m n fun i => f i.castSucc) F)
        (h * κ (n + 1)) =
      liftA W M (.right n D.R.m) (f' (Fin.last n))
        (liftP W M (rowPath T D.R.m n) (rowFam D.R.m n fun i => f' i.castSucc) (fun x => F (x * κ 0))) h
    simp only [liftA_apply]
    have e := integral_ker_move W M (.chi n D.R.m) ⟨hn, le_rfl⟩ hK (κ n) (κ (n + 1)) hm hm' (f (Fin.last n)) (hf (Fin.last n)) _
      (pathLift_row_leftInvariant W M n (by omega) _ (fun i => hf i.castSucc) F hF) h
    refine e.trans ?_
    rw [← hff (Fin.last n)]
    congr 1
    funext g
    rw [pathLift_row_translate W M κ n (by omega) (fun i hi => hκ i (by omega)) _ _ (fun i => hf i.castSucc)
      (fun i => hff i.castSucc) F hF g]
    rfl

end Paths

end GlobalTheory.RowReal

namespace GlobalTheory.RowReal

section Coef

variable {D : D7}

theorem pairVec_mul_real {V : HSp D} (c : CoefA V) (ξ : Module.Dual ℂ c.W) (Ψ : Bridge.Gf V → c.W) {k : GA D V}
    (hk : k ∈ GinfC V) (x : GA D V) :
    pairVec c (ξ ∘ₗ c.ρ k⁻¹) Ψ x = pairVec c ξ Ψ (x * k) := by
  have e : (finHom V).rangeRestrict (x * k) = (finHom V).rangeRestrict x := by
    have hk1 : (finHom V).rangeRestrict k = 1 := Subtype.ext (by simpa using MonoidHom.mem_ker.1 hk)
    rw [map_mul, hk1, mul_one]
  have h3 : c.ρ (x * k)⁻¹ = c.ρ k⁻¹ * c.ρ x⁻¹ := (congrArg c.ρ (mul_inv_rev x k)).trans (c.ρ.map_mul _ _)
  show ξ (c.ρ k⁻¹ (c.ρ x⁻¹ (Ψ ((finHom V).rangeRestrict x)))) =
    ξ (c.ρ (x * k)⁻¹ (Ψ ((finHom V).rangeRestrict (x * k))))
  exact (congrArg (fun A : Module.End ℂ c.W => ξ (A (Ψ ((finHom V).rangeRestrict x)))) h3.symm).trans
    (congrArg (fun z => ξ (c.ρ (x * k)⁻¹ (Ψ z))) e.symm)

theorem ext_cast_mul_real {X Y : LSp D} (e : X = Y) (c : CoefA Y.sp) (v : Bridge.Gf Y.sp → c.W) (η : Module.Dual ℂ c.W)
    {k : GA D X.sp} (hk : k ∈ GinfC X.sp) (g : GA D X.sp) :
    (η ∘ₗ c.ρ (cast (congrArg (fun Z : LSp D => GA D Z.sp) e) k)⁻¹) (c.ext v (cast (congrArg (fun Z : LSp D => GA D Z.sp) e) g)) =
      η (c.ext v (cast (congrArg (fun Z : LSp D => GA D Z.sp) e) (g * k))) := by
  subst e
  exact pairVec_mul_real c η v hk g

end Coef

section Gen

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R)

theorem formGen_mul_real (t : T) (y : (R.HX t).H) (η : Module.Dual ℂ R.cX.W) {k : GA D (ch.G.V (.grid 0 D.R.m))}
    (hk : k ∈ GinfC (ch.G.V (.grid 0 D.R.m))) (g : GA D (ch.G.V (.grid 0 D.R.m))) :
    formGen ch t y (η ∘ₗ R.cX.ρ (cast (congrArg (fun X : LSp D => GA D X.sp) (colY_m R.toLevCh)) k)⁻¹) g =
      formGen ch t y η (g * k) :=
  ext_cast_mul_real (colY_m R.toLevCh) R.cX _ η hk g

end Gen

end GlobalTheory.RowReal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockSubstitutionColumnStepRenameConjStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockSubstitution_columnStep_rename_conj : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (i : Fin D.R.m)
    (u : UG D.what₂.Tau ((GlobalTheory.RowReal.rowSizes D).nC i)) (v : UG D.what₂.Tau ((GlobalTheory.RowReal.rowSizes D).nC (i + 1)))
    (Q : PolF D (G.V (.grid i D.R.m)).rank (G.V (.grid (i + 1) D.R.m)).rank),
    GlobalTheory.RowReal.trRow G i (GlobalTheory.RowReal.fockSubAll (fun _ => 0) (fun _ => (G.V (.grid i D.R.m)).rank)
      (fun τ => ((v τ : Matrix.unitaryGroup _ ℂ) : Matrix _ _ ℂ).submatrix (Fin.cast (GlobalTheory.RowReal.rank_gridM G (i := i + 1) i.2))
        (Fin.cast (GlobalTheory.RowReal.rank_gridM G (i := i + 1) i.2)))
      (fun τ => ((u τ : Matrix.unitaryGroup _ ℂ) : Matrix _ _ ℂ).submatrix (Fin.cast (GlobalTheory.RowReal.rank_gridM G (i := i) i.2.le))
        (Fin.cast (GlobalTheory.RowReal.rank_gridM G (i := i) i.2.le))) Q) =
      linSub (homMat _ _ (u, v)) (GlobalTheory.RowReal.trRow G i Q) := by
  first | exact @GlobalTheory.RowReal.trRow_fockSubAll | exact GlobalTheory.RowReal.trRow_fockSubAll | (intros; apply GlobalTheory.RowReal.trRow_fockSubAll <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockSubstitutionRowStepRenameUnitaryStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockSubstitution_rowStep_rename_unitary : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (j : Fin D.R.m)
    (u : UG D.what₂.Tau ((GlobalTheory.RowReal.rowSizes D).nR j)) (v : UG D.what₂.Tau ((GlobalTheory.RowReal.rowSizes D).nR (j + 1)))
    (Q : PolF D (G.V (.top (j + 1))).rank (G.V (.top j)).rank),
    GlobalTheory.RowReal.trCol G j (GlobalTheory.RowReal.fockSubAll (fun _ => (G.V (.top j)).rank) (fun _ => (G.V (.top (j + 1))).rank)
      (fun τ => ((u τ : Matrix.unitaryGroup _ ℂ) : Matrix _ _ ℂ).submatrix (Fin.cast (GlobalTheory.RowReal.rank_top G (j := j) j.2.le))
        (Fin.cast (GlobalTheory.RowReal.rank_top G (j := j) j.2.le)))
      (fun τ => ((v τ : Matrix.unitaryGroup _ ℂ) : Matrix _ _ ℂ).submatrix (Fin.cast (GlobalTheory.RowReal.rank_top G (j := j + 1) j.2))
        (Fin.cast (GlobalTheory.RowReal.rank_top G (j := j + 1) j.2))) Q) =
      linSub (homMat _ _ (u, v)) (GlobalTheory.RowReal.trCol G j Q) := by
  first | exact @GlobalTheory.RowReal.trCol_fockSubAll_unitary | exact GlobalTheory.RowReal.trCol_fockSubAll_unitary | (intros; apply GlobalTheory.RowReal.trCol_fockSubAll_unitary <;> assumption)
end

