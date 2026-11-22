import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0102
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0104
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0272
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0451
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0303
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0503
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0765
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0519
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0513
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0547
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHasLocalSmall
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0761
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0766
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0740
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0650
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0522
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0752
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle0001
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0010
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0009
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0029
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SqrtDivMulEqSqrtMul
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0484
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0427
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulEqZeroOfInf
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0565
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1553
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0663
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0602
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0261
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0273
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0002
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0767
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsCoreLat
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0012
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0674
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0037

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierJacobiToBesselNonvanishingTower
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

namespace GlobalTheory.AscRungB

theorem rapidDec_star {D : D7} {V : HSp D} {f : GA D V → ℂ} (h : RapidDec V f) : RapidDec V (star f) := by
  first
  | exact h.conj
  | exact RapidDec.of_le h (fun γ hγ g => by simp only [Pi.star_apply]; rw [h.left hγ g])
      h.continuous.star (fun g => by simp only [Pi.star_apply, norm_star, le_refl])

theorem exists_step {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {V V₀ W W₀ : HSp D} {ρ σ : ℕ} (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ)
    {χV χW : (AE D)ˣ →* Circle} {om : Om V W} (h : IsWeilDatumO ψ V W χV χW om) (vW : GlobalTheory.Unf.Vol W) :
    ∃ s : Step ψ V V₀ W W₀ ρ σ, s.χV = χV ∧ s.χW = χW ∧ s.om = om ∧ s.vW = vW := by
  have hDesc := GlobalTheory.Unf.descent_of_weilDatumExists D (GlobalTheory.WeilDatumExistence.weilDatumExists D)
  obtain ⟨om₁, h₁⟩ := (hDesc ψ V W χV χW om h).1 V₀ ρ dV
  obtain ⟨om₀, h₀⟩ := (hDesc ψ V₀ W χV χW om₁ h₁).2 W₀ σ dW
  obtain ⟨vS⟩ := GlobalTheory.Unf.VolExist.nonempty_volM D W.rank ρ
  obtain ⟨vT⟩ := GlobalTheory.Unf.VolExist.nonempty_volM D σ V₀.rank
  obtain ⟨vU⟩ := GlobalTheory.Unf.VolExist.nonempty_volU D ρ
  exact ⟨⟨χV, χW, om, om₀, h, h₀, vW, vS, vT, vU⟩, rfl, rfl, rfl, rfl⟩

theorem rungB : FockTot → PartFixed → RungB := by
  intro hF hP
  unfold RungB OnTower
  intro D hD T L μ0 hL sc G W M hM v F ΓL _hEnds hGood Ψ hΨ u hu k h hJ

  have hi : 2 * k + 1 < D.R.m := by omega
  obtain ⟨hw1, hw2, hodd, -, hdepiff, hdn, hpart, hpartEq, hhaar, hfund⟩ :=
    GlobalTheory.T.gridConjugation_weilData_inverseCharacter D hD T L μ0 hL sc G W M hM (2 * k + 1) hi
  obtain ⟨hχS, hχT⟩ := hodd (odd_two_mul_add_one k)
  obtain ⟨hrap, hchain⟩ := hΨ
  obtain ⟨f, hdep, hΨeq⟩ := hchain (2 * k + 1) hi
  obtain ⟨χ', omz, hwz, ρ, Φ, Φ₀, hΦ₀, hne⟩ := hJ

  let vW : GlobalTheory.Unf.Vol (G.V (.grid (2 * k + 1) 0)) := ⟨M.ν _, M.fd _, hhaar, hfund⟩
  obtain ⟨s, hsV, hsW, hsom, hsvW⟩ := exists_step (F.dB k h) (F.dJ k h) hw1 vW
  obtain ⟨𝒮, Γ₀, hLoc, hvacS, hbox⟩ := hGood.bf k h s hsom

  set φ : GA D (G.V (.core (2 * k + 2))) → ℂ := star (Ψ (2 * k + 2))
  set G' : GA D (G.V (.grid (2 * k + 1) 0)) → ℂ := star (part W M ρ Φ u (2 * k + 1) (by omega))
  have hφ : RapidDec _ φ := rapidDec_star (hrap (2 * k + 2) h)
  have hG' : RapidDec _ G' := rapidDec_star (hu ρ Φ (2 * k + 1) (by omega))
  have hfix : ∀ k' ∈ lev G (.grid (2 * k + 1) 0), ∀ g, G' (g * k') = G' g := fun k' hk' g =>
    congrArg star (hP D hD T L μ0 hL sc G W M hM ρ Φ u (2 * k) (by omega) k' hk' g)

  have hvac1 : VacG W.ψ _ _ (latCore G (2 * k + 1)) (star f) := (hdepiff f).1 hdep
  obtain ⟨-, hlink⟩ := GlobalTheory.T.linkedLineVectors_invertible_on_theta_functions D W.ψ W.ψ_std (negSp F.Lz) (negSp F.Lz) (G.V (.core (2 * k + 1)))
    (F.ζ (k + 1)) (F.ζ k) (F.line (k + 1)) (F.line k) (F.lnk k)
  obtain ⟨Ξ₂, hΞ₂, hΦ₀eq⟩ := hlink Φ₀ hΦ₀.1
  have hbox' := hbox (star f) Ξ₂ hvac1 hΞ₂ (by rw [← hΦ₀eq]; exact hΦ₀)

  have hlift : liftT (omCore W (2 * k + 1)) (v (2 * k + 2)).μ (v (2 * k + 2)).𝓕 φ (star f) = star (Ψ (2 * k + 1)) := by
    rw [hΨeq]; exact (hdn v f (Ψ (2 * k + 2))).symm
  have hJper : (F.jac v k h).per W.ψ (F.ζ k) omz
      (liftT (omCore W (2 * k + 1)) (v (2 * k + 2)).μ (v (2 * k + 2)).𝓕 φ (star f)) G'
      (fun w => star (Ξ₂ ((F.lnk k).κ _ w))) ≠ 0 := by
    rw [hlift, ← hΦ₀eq]; exact hne
  have hsχ : s.χV = (G.ch.chi (D.R.m - (2 * k + 1)))⁻¹ * L.eta := by rw [hsV, hχS]
  have hWA : IsWeilDatumO W.ψ _ _ (G.ch.chi (D.R.m - (2 * k + 1)))⁻¹ s.χW (omCore W (2 * k + 1)) := by
    rw [hsW, hχT]; exact hw2
  obtain ⟨Φ₁, hΦ₁S, hper₁⟩ := GlobalTheory.T.fourierJacobi_period_gives_bessel_period_of_lift D W.ψ k (F.bes v k h) (F.jac v k h) s 𝒮 Γ₀ _ hLoc (negSp F.Lz) (F.ζ k)
    (F.line k) (F.lnk k) _ _ χ' (omCore W (2 * k + 1)) omz hsχ hWA hwz φ G' hφ hG' hfix (star f) Ξ₂ hvac1.1 hΞ₂ hbox' hJper

  set ℓ : (WO (G.V (.grid (2 * k + 2) 0)) (G.V (.grid (2 * k + 1) 0)) → ℂ) → ℂ :=
    fun Φ' => (F.bes v k h).per W.ψ φ (liftS (omRow W (2 * k + 1)) vW.μ vW.𝓕 G' Φ')
  have htame : Tame W.ψ _ _ ℓ :=
    (GlobalTheory.T.thetaLift_periods_isTameThetaFunctional D W.ψ _ vW G' hG').1 k (F.bes v k h) _ _ (omRow W (2 * k + 1)) hw1 φ hφ
  have hℓ₁ : ℓ Φ₁ ≠ 0 := by
    have e : s.lift G' Φ₁ = liftS (omRow W (2 * k + 1)) vW.μ vW.𝓕 G' Φ₁ := by
      unfold GlobalTheory.Unf.Step.lift; rw [hsom, hsvW]
    rw [e] at hper₁; exact hper₁

  by_contra hall
  apply hℓ₁
  refine hF D hD T L μ0 hL sc G W M hM ⟨2 * k + 1, hi⟩ ℓ htame ?_ Φ₁ (hvacS Φ₁ hΦ₁S)
  intro κ P
  let ρ' : G.RealVec := Function.update ρ ⟨2 * k + 1, hi⟩ P
  let Φ' : G.Datum := Function.update Φ ⟨2 * k + 1, hi⟩ κ
  have hagree : ∀ j : Fin D.R.m, j.1 < 2 * k + 1 → ρ' j = ρ j ∧ Φ' j = Φ j := by
    intro j hj
    have hne' : j ≠ ⟨2 * k + 1, hi⟩ := fun e => by rw [e] at hj; exact lt_irrefl _ hj
    exact ⟨Function.update_of_ne hne' _ _, Function.update_of_ne hne' _ _⟩
  have hdat : W.datum ρ' Φ' ⟨2 * k + 1, hi⟩ = W.fock (.chi (2 * k + 1) 0) (W.cosVec (2 * k + 1) κ) P := by
    simp only [GlobalTheory.ChiGrid.GridData.Weil.datum, ρ', Φ', Function.update_self]
  have htop := hpart ρ' Φ' u
  rw [hpartEq ρ' Φ' ρ Φ u hagree, hdat] at htop
  have h0 : (F.bes v k h).per W.ψ φ (star (part W M ρ' Φ' u (2 * k + 1 + 1) hi)) = 0 := by
    by_contra hne0
    exact hall ⟨ρ', Φ', hne0⟩
  rw [htop] at h0
  exact h0

end GlobalTheory.AscRungB

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GivenFiniteRepresentationChain
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

theorem GlobalTheory.FlipStart.startFin : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.RowClaim.Big fun {D} _ _ _ _ {T} _ _ _ _ _ {R} ch => ∀ (t : T) (f : ∀ j : Fin D.R.m, Sch ch.G (.down t 0 j)), GlobalTheory.FlipStart.ChainVecs ch t f → ∃ z : ℂˣ, z ∈ xiVals R.toLevCh t ∧ ∀ Φ : ch.G.Datum, RepFin ch.S.B ch.rm t (givenPath t D.R.m) (Finsupp.single (GlobalTheory.FlipStart.givenFin ch.W t f Φ) (z : ℂ)) (fun w => (givenStage t w ch.S.B Φ).tensor) := by
  intro hP
  obtain ⟨C, h⟩ := Big.and (Big.and (GlobalTheory.T.local_vector_down_edge_interior hP) (GlobalTheory.T.local_vector_down_edge_boundary hP)) (GlobalTheory.T.local_vector_right_edge_cosine hP)
  refine ⟨C, fun ε CF hC => ?_⟩
  obtain ⟨x₀, h⟩ := h ε CF hC
  refine ⟨x₀, fun D large₂ he hx Γ _ _ Pl0 T A Ks _ _ _ R F s ch hi ha => ?_⟩
  obtain ⟨⟨hc1, hc2⟩, hr⟩ := h D large₂ he hx Γ Pl0 T A Ks R F s ch hi ha
  intro t f hf
  have hc : ∀ j : Fin D.R.m, ∃ c : ℂˣ, c ∈ xiVals R.toLevCh t ∧ ∀ e : AE D, IsIdemSum e (locPl ch.G t) →
      ∀ Φ : ch.G.Datum, IsLocVec ch.W (.mu t 0 j) e (ch.rm.vT 0 j) ((c : ℂ) • GlobalTheory.FlipStart.givenFn ch.S.B t Φ e (.down t 0 j)) (f j) := by
    intro j
    by_cases hj : (j : ℕ) + 1 < D.R.m
    · exact hc1 t j (f j) hj ((hf j).1 hj)
    · have hj' : (j : ℕ) + 1 = D.R.m := by have := j.2; omega
      exact hc2 t j (f j) hj' ((hf j).2 hj')
  choose c hcx hcv using hc
  obtain ⟨e, he⟩ := GlobalTheory.FunObj.LocTensor.exists_idemSum_locPl s.core.lev ch.G t
  refine ⟨(∏ j, c j)⁻¹, Subgroup.inv_mem _ (Subgroup.prod_mem _ fun j _ => hcx j), fun Φ => ?_⟩
  refine GlobalTheory.FlipStart.repFin_of ch.W ch.S.B ch.rm t f Φ e he (fun j => (c j : ℂ)) _ ?_ (fun j => hcv j e he Φ) (hr t e he Φ)
  rw [← Units.coe_prod, ← Units.val_mul, inv_mul_cancel, Units.val_one]

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GoodPositionOffBadPlacesFromBesselLevel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.GoodPosBF

theorem goodPosition_offBadPlaces_from_besselLevel : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), ∀ v ∉ G.pl.S0, GoodAt (F.dB ρ h) (F.dJ ρ h) (xZero (F.dJ ρ h)) W.ψ (G.Λ (.grid (2 * ρ + 2) 0)) (lat0 F ρ h) (G.Λ (.grid (2 * ρ + 1) 0)) (G.Λ (.core (2 * ρ + 1))) v ∧ StdAt (F.dB ρ h) (F.dJ ρ h) (pcBF W F ρ h) (G.Λ (.grid (2 * ρ + 2) 0)) (G.Λ (.grid (2 * ρ + 1) 0)) v ∧ (0 < ρ → ∀ a ∈ idAt D (· = v), (F.dJ ρ h).incAdj (F.V₀ ρ) (a • yBF F ρ h) ∈ latO (F.V₀ ρ) _ (lat0 F ρ h : Set _) (G.Λ (.grid (2 * ρ + 1) 0) : Set _) (· = v) ↔ a ∈ intAt D (· = v)) := by
  intro D hq T L μ0 hL sc G W M hM F hF ρ h v hv
  have I := GlobalTheory.T.grid_lattices_compact_selfDual_splitting D hq T L μ0 hL sc G W M hM F hF
  have sd : ∀ X : Node, X.InRange D.R.m → (∀ j, X ≠ .grid 0 j) → IsSelfDualC (G.V X) (G.Λ X) :=
    fun X h1 h2 => (G.isV h1 h2).sd
  refine ⟨⟨sd _ ⟨h, Nat.zero_le _⟩ (fun j e => by cases e), (I.2.1 ρ h).1,
    sd _ ⟨by omega, Nat.zero_le _⟩ (fun j e => by cases e),
    sd (.core (2 * ρ + 1)) (show 2 * ρ + 1 ≤ D.R.m by omega) (fun j e => by cases e),
    ((I.2.1 ρ h).2.1 v).1, ((I.2.1 ρ h).2.1 v).2,
    GlobalTheory.T.psi_primitive_standardFrames_besselLevel D hq T L μ0 hL sc G W M hM F hF ρ h v hv, GlobalTheory.T.besselLevel_columns_carry_latticeLines_offExceptional D hq T L μ0 hL sc G W M hM F hF ρ h v hv⟩,
    GlobalTheory.T.standard_lattice_off_S0 D hq T L μ0 hL sc G W M hM F hF ρ h v hv, GlobalTheory.T.lattice_membership_adjoint_iff D hq T L μ0 hL sc G W M hM F hF ρ h v hv⟩

end GlobalTheory.GoodPosBF
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergCommutantPermutesFirstRowCosetVectorsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenbergCommutant_permutes_firstRowCosetVectors : All fun {D} _ _ _ {G} W _ => ∀ i, i < D.R.m → ∀ κ, W.cosVec i κ ≠ 0 ∧ (∀ τ, IsFockVacAt (heisO W.ψ (G.pS (.chi i 0)) (G.pT (.chi i 0))) W.θ τ (cplxO (G.cartS W.cart (.chi i 0) τ) (G.onT W.cart (.chi i 0) τ)) (W.cosVec i κ)) ∧ VacG W.ψ _ _ (latRow G i) (star (W.cosVec i κ)) ∧ ∀ w ∈ Ann W.ψ _ _ (latRow G i), w.map (infPart D) = 0 → heisO W.ψ (G.V (.grid (i + 1) 0)) (G.V (.grid i 0)) w (star (W.cosVec i κ)) ∈ Submodule.span ℂ (Set.range fun κ' => (star (W.cosVec i κ') : WO (G.V (.grid (i + 1) 0)) (G.V (.grid i 0)) → ℂ)) := by
  first | exact @GlobalTheory.CosPerm.cosVec_perm | exact GlobalTheory.CosPerm.cosVec_perm | (intros; apply GlobalTheory.CosPerm.cosVec_perm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergTranslateVacuumReadRationalPoints
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj Formalism.IndefR.Datum ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.NTheta (IsIdemAt)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.HeisRatRead

open GlobalTheory.FinTranslate Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

variable {D : D7}

theorem ratW_sub_realPt_inf (S T : HSp D) (ℓ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    (ratW T S ℓ - GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt S T ℓ).map (infPart D) = 0 := by
  ext i j
  change infPart D (incA D (ℓ i j) - pairA D.host.F 1 0 ⊗ₜ[D.host.F] ℓ i j) = 0
  rw [map_sub]
  change Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E) (1 ⊗ₜ ℓ i j) -
    Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E) (pairA D.host.F 1 0 ⊗ₜ ℓ i j) = 0
  rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, map_one]
  exact sub_eq_zero.2 rfl

theorem realPt_sub (S T : HSp D) (X Y : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt S T (X - Y) = GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt S T X - GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt S T Y := by
  ext i j
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt, Matrix.of_apply, Matrix.sub_apply, TensorProduct.tmul_sub]

theorem actO_inf (S T : HSp D) (h : GA D T) {w : WO S T} (hw : w.map (infPart D) = 0) :
    (actO S T 1 h w).map (infPart D) = 0 := by
  have hw' : ∀ k l, infPart D (w k l) = 0 := fun k l => congrFun (congrFun hw k) l
  ext i j
  rw [Matrix.map_apply, Matrix.zero_apply]
  unfold actO
  simp only [Matrix.mul_apply, map_sum, map_mul, hw', mul_zero, zero_mul, Finset.sum_const_zero]

theorem actO_add (S T : HSp D) (h : GA D T) (u v : WO S T) :
    actO S T 1 h (u + v) = actO S T 1 h u + actO S T 1 h v := by
  simp only [actO, Matrix.mul_add, Matrix.add_mul]

end GlobalTheory.HeisRatRead

namespace GlobalTheory.HeisRatRead

open GlobalTheory.FinTranslate Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

theorem heis_translate_read : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
    (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F),
    R.toLevCh.Is A.μ0 → R.IsFam → R.IsThP → ∀ (i : Fin D.R.m) (g : GA D (Wc D i)) (x : WO (Vc D i) (Wc D i)),
    x.map (infPart D) = 0 → ∀ (ℓ : Matrix (Fin (Wc D i).rank) (Fin (Vc D i).rank) D.host.E) (w : WO (Vc D i) (Wc D i)),
    w.map (infPart D) = 0 → heisO R.ψ (Vc D i) (Wc D i) w (R.vacP i) = R.vacP i →
    x = actO (Vc D i) (Wc D i) 1 g⁻¹ (ratW (Wc D i) (Vc D i) ℓ - GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt (Vc D i) (Wc D i) ℓ) + w →
    ∀ X : Matrix (Fin (Wc D i).rank) (Fin (Vc D i).rank) D.host.E,
      R.ωP i A.μ0 (1, g) (heisO R.ψ (Vc D i) (Wc D i) x (R.vacP i)) (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt (Vc D i) (Wc D i) X) =
        R.ψ (-(symplOH (Vc D i) (Wc D i) (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt (Vc D i) (Wc D i) ℓ) (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt (Vc D i) (Wc D i) (X - ℓ)) +
            symplOH (Vc D i) (Wc D i) (ratW (Wc D i) (Vc D i) ℓ - GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt (Vc D i) (Wc D i) ℓ) (actO (Vc D i) (Wc D i) 1 g w))) *
          R.ωP i A.μ0 (1, g) (R.vacP i) (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt (Vc D i) (Wc D i) (X - ℓ)) := by
  intro D G _ _ Pl0 T0 A T _ R hL hF hT i g x hx ℓ w hw hρw hxe X
  have hW := hT.ωP i A.μ0
  have hv := hT.vP i A.μ0
  have hf : IsThetaFunO R.ψ (Vc D i) (Wc D i) (R.vacP i) := hv.1.2.theta
  set F := R.ωP i A.μ0 (1, g) (R.vacP i) with hFdef
  have hFθ : IsThetaFunO R.ψ (Vc D i) (Wc D i) F := hW.om_pres _ _ hf
  set lf := ratW (Wc D i) (Vc D i) ℓ - GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt (Vc D i) (Wc D i) ℓ with hlf
  have hlf0 : lf.map (infPart D) = 0 := ratW_sub_realPt_inf (Vc D i) (Wc D i) ℓ
  set gw := actO (Vc D i) (Wc D i) 1 g w with hgw
  have hgw0 : gw.map (infPart D) = 0 := actO_inf (Vc D i) (Wc D i) g hw
  have hgx : actO (Vc D i) (Wc D i) 1 g x = lf + gw := by
    rw [hxe, actO_add, ← GlobalTheory.HeckeVacuum.act_mul, mul_inv_cancel, GlobalTheory.HeckeVacuum.act_one]
  have hFw : heisO R.ψ (Vc D i) (Wc D i) gw F = F := by
    have := hW.om_heis 1 g w (R.vacP i) hf
    rw [hρw] at this
    exact this.symm
  set P := GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt (Vc D i) (Wc D i) X
  set z := GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt (Vc D i) (Wc D i) (X - ℓ)
  have hP0 : P.map (finPart D) = 0 := GlobalTheory.FrameConst.realPt_fin (Vc D i) (Wc D i) X
  have hz0 : z.map (finPart D) = 0 := GlobalTheory.FrameConst.realPt_fin (Vc D i) (Wc D i) (X - ℓ)
  have hl0 : (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt (Vc D i) (Wc D i) ℓ).map (finPart D) = 0 := GlobalTheory.FrameConst.realPt_fin (Vc D i) (Wc D i) ℓ
  have hzF : F (z + gw) = F z := by
    have := congrFun hFw z
    simp only [heisO, symplOH_real_fin hgw0 hz0, AddChar.map_zero_eq_one, one_mul] at this
    exact this
  have hpt : P + (lf + gw) = ratW (Wc D i) (Vc D i) ℓ + (z + gw) := by
    simp only [z, P, hlf, realPt_sub]
    abel
  have hratW : ratW (Wc D i) (Vc D i) ℓ = GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt (Vc D i) (Wc D i) ℓ + lf := by
    rw [hlf]; abel
  rw [hW.om_heis 1 g x (R.vacP i) hf, ← hFdef]
  show R.ψ (symplOH (Vc D i) (Wc D i) P (actO (Vc D i) (Wc D i) 1 g x)) * F (P + actO (Vc D i) (Wc D i) 1 g x) = _
  rw [hgx, hpt, hFθ.quasi, hzF, ← mul_assoc, ← AddChar.map_add_eq_mul]
  congr 2
  rw [hratW, symplOH_add_right, symplOH_add_left, symplOH_add_right, symplOH_add_right,
    symplOH_real_fin hlf0 hP0, symplOH_real_fin hgw0 hP0, symplOH_real_fin hgw0 hl0, symplOH_fin_real hlf0 hz0]
  ring

end GlobalTheory.HeisRatRead
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.JetScalarIdempotentValue
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

noncomputable section

namespace GlobalTheory.SplitMoveKappa

theorem qbar_of_root {ζ : ℂ} {n : ℕ} (hn : 0 < n) (hζ : ζ ^ n = 1) : ζ ∈ TaylorLogMetric.Qbar := by
  have halg : IsAlgebraic ℚ ζ := by
    refine ⟨Polynomial.X ^ n - Polynomial.C 1, ?_, ?_⟩
    · exact Polynomial.X_pow_sub_C_ne_zero hn 1
    · simp [hζ]
  exact mem_algebraicClosure_iff.2 halg

theorem mod1All_root {ζ : ℂ} {n : ℕ} (hn : 0 < n) (hζ : ζ ^ n = 1) : Mod1All ζ := by
  refine ⟨qbar_of_root hn hζ, fun σ => ?_⟩
  have h1 : (⟨ζ, qbar_of_root hn hζ⟩ : TaylorLogMetric.Qbar) ^ n = 1 := by ext; simpa using hζ
  have h2 : (σ ⟨ζ, qbar_of_root hn hζ⟩) ^ n = 1 := by rw [← map_pow, h1, map_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 (by rw [← norm_pow, h2, norm_one])

theorem lamC_mem {q : ℕ} [Fact q.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[q]) {x : ℂ} (h : x ∈ TaylorLogMetric.Qbar) :
    TaylorLogMetric.lamC lam x = lam ⟨x, h⟩ := dif_pos h

theorem unitAt_mul {q : ℕ} [Fact q.Prime] {x y : ℂ} (hx : x ∈ TaylorLogMetric.Qbar) (hy : y ∈ TaylorLogMetric.Qbar)
    (ux : GlobalTheory.MovedKappaEx.UnitAt q x) (uy : GlobalTheory.MovedKappaEx.UnitAt q y) : GlobalTheory.MovedKappaEx.UnitAt q (x * y) := by
  intro lam
  have e : (⟨x * y, mul_mem hx hy⟩ : TaylorLogMetric.Qbar) = ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
  have hx' := ux lam
  have hy' := uy lam
  rw [lamC_mem lam hx] at hx'
  rw [lamC_mem lam hy] at hy'
  rw [lamC_mem lam (mul_mem hx hy), e, map_mul, norm_mul, hx', hy', one_mul]

theorem unitAt_inv {q : ℕ} [Fact q.Prime] {x : ℂ} (hx : x ∈ TaylorLogMetric.Qbar)
    (ux : GlobalTheory.MovedKappaEx.UnitAt q x) : GlobalTheory.MovedKappaEx.UnitAt q x⁻¹ := by
  intro lam
  have e : (⟨x⁻¹, inv_mem hx⟩ : TaylorLogMetric.Qbar) = (⟨x, hx⟩ : TaylorLogMetric.Qbar)⁻¹ := rfl
  have hx' := ux lam
  rw [lamC_mem lam hx] at hx'
  rw [lamC_mem lam (inv_mem hx), e, map_inv₀, norm_inv, hx', inv_one]

theorem unitAt_root (q : ℕ) [Fact q.Prime] {ζ : ℂ} {n : ℕ} (hn : 0 < n) (hζ : ζ ^ n = 1) :
    GlobalTheory.MovedKappaEx.UnitAt q ζ := by
  intro lam
  have h1 : (⟨ζ, qbar_of_root hn hζ⟩ : TaylorLogMetric.Qbar) ^ n = 1 := by ext; simpa using hζ
  have h2 : (lam ⟨ζ, qbar_of_root hn hζ⟩) ^ n = 1 := by rw [← map_pow, h1, map_one]
  rw [lamC_mem lam (qbar_of_root hn hζ)]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 (by rw [← norm_pow, h2, norm_one])

theorem moved_split : GlobalTheory.FunPr.Hypotheses₂ → (∀ D, GlobalTheory.NormSum.Inp D) → ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type}
    {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
    (ch : Choice R), ch.Is → ∀ (p : Pair T), DefPair D.R.m p → ∀ (x : FinPt ch.G p.small) (y : FinPt ch.G p.big) (κ : ℂ), GlobalTheory.MovedKappaEx.JetKap ch p x y κ →
    ∀ (e : Formalism.L2.Theta.AE D), IsSplitIdem D e → ∀ (s : FinPt ch.G p.small) (s' : FinPt ch.G p.big),
    SuppAt e _ (s : GA D (ch.G.V p.small)) → SuppAt e _ (s' : GA D (ch.G.V p.big)) →
    ∃ c : ℂ, Mod1All c ∧ (∀ (q : ℕ) [Fact q.Prime], GlobalTheory.MovedKappaEx.OffPrime e q → GlobalTheory.MovedKappaEx.UnitAt q c) ∧
      GlobalTheory.MovedKappaEx.JetKap ch p (s * x) (s' * y) (c * κ) := by

  intro hP hI D Γ _ _ Pl0 T A Ks _ _ _ R ch hch p hp x y κ hJ e he s s' hs hs'
  obtain ⟨x₀, y₀, hx₀, hy₀, ζ, ⟨n, hn, hζ⟩, r, hr, hJ'⟩ := GlobalTheory.T.jet_scalar_local_identity hP hI ch hch p hp x y κ hJ e he s s' hs hs'
  have h1 := GlobalTheory.T.jet_scalar_unit_modulus hP hI ch hch p hp x y κ hJ
  have h2 := GlobalTheory.T.jet_scalar_unit_modulus hP hI ch hch p hp _ _ _ hJ'
  have hζn : ‖ζ‖ = 1 := (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 (by rw [← norm_pow, hζ, norm_one])
  have hχn : ‖((((ch.G.chrT p x₀)⁻¹ * ch.G.chrS p y₀ : Circle)) : ℂ)‖ = 1 := Circle.norm_coe _
  have hr1 : (r : ℂ) = 1 := by
    rw [norm_mul, norm_mul, norm_mul, hζn, hχn, h1, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr] at h2
    simp only [mul_one] at h2
    rw [h2]; simp
  rw [hr1, one_mul] at hJ'
  have hA := GlobalTheory.T.split_idempotent_unit_decomposition hP hI ch hch p hp e he x₀ hx₀
  have hB := GlobalTheory.T.split_idempotent_unit_decomposition hP hI ch hch p hp e he y₀ hy₀
  have hco : ((((ch.G.chrT p x₀)⁻¹ * ch.G.chrS p y₀ : Circle)) : ℂ) =
      ((ch.G.chrT p x₀ : Circle) : ℂ)⁻¹ * ((ch.G.chrS p y₀ : Circle) : ℂ) := by
    rw [Circle.coe_mul, Circle.coe_inv]
  have hm : Mod1All ((((ch.G.chrT p x₀)⁻¹ * ch.G.chrS p y₀ : Circle)) : ℂ) := by
    rw [hco]
    exact GlobalTheory.FamilyTieProof.mod1All_mul' (GlobalTheory.FamilyTieProof.mod1All_inv hA.1.2) hB.1.1
  refine ⟨ζ * ((((ch.G.chrT p x₀)⁻¹ * ch.G.chrS p y₀ : Circle)) : ℂ), GlobalTheory.FamilyTieProof.mod1All_mul' (mod1All_root hn hζ) hm,
    fun q _ hq => ?_, hJ'⟩
  refine unitAt_mul (qbar_of_root hn hζ) hm.1 (unitAt_root q hn hζ) ?_
  rw [hco]
  exact unitAt_mul (inv_mem hA.1.2.1) hB.1.1.1 (unitAt_inv hA.1.2.1 ((hA.2 q hq).2)) ((hB.2 q hq).1)

end GlobalTheory.SplitMoveKappa
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatchedMapsGaussianSumStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matched_maps_gaussian_sum : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.Published.MinguezThetaGL →
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W)
    (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs G Xc om om' R Rf →
    ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, Nonempty (E →ₐ[F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) →
      (∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ ((Fin a' × Fin (a + a') → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ)),
        StrictMono N → (∀ i, GlobalTheory.Published.ThetaSub om' v (N i)) → m ≤ L) ∧
      ∀ N : Submodule ℂ ((Fin a' × Fin (a + a') → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ), GlobalTheory.Published.ThetaSub om' v N →
        N ≠ GlobalTheory.WeilM.SB _ → ∀ φ ∈ N, Rf.p' v φ = 0 := by
  first | exact @GlobalTheory.HoweSplitSmall.howe_split_ker_small | exact GlobalTheory.HoweSplitSmall.howe_split_ker_small | (intros; apply GlobalTheory.HoweSplitSmall.howe_split_ker_small <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemCongruenceSubgroupOfStabilisesAndCongruentStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexConjugate TensorProduct
open Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_congruenceSubgroup_of_stabilises_and_congruent : ∀ (D : D7) (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), IsSelfDualC V Λ →
    ∀ (Z : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e Z → ∀ 𝔪 : Ideal (𝓞 D.host.E),
    (∀ PP : Pl D.host.E, 𝔪 ≤ PP.asIdeal → PP ∈ Z) → ∀ g : GA D V,
    (∀ v, (∀ PP ∈ Z, PP.under (𝓞 D.host.F) ≠ v) →
      GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v g ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig V.gram Λ v) →
    (∀ x ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ,
      toEAf D e • ((Lev.finE V g).1 *ᵥ x) ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ ∧
      toEAf D e • (((Lev.finE V g)⁻¹).1 *ᵥ x) ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ ∧
      toEAf D e • ((Lev.finE V g).1 *ᵥ x - x) ∈ Formalism.L2.Herm.hatL (F := D.host.F) (𝔪 • Λ)) →
    Lev.finE V g ∈ congLev D.sp.cm V.gram Λ 𝔪 := by
  first | exact @GlobalTheory.CongAssemble.cong_assemble | exact GlobalTheory.CongAssemble.cong_assemble | (intros; apply GlobalTheory.CongAssemble.cong_assemble <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestColumnInductionLocalToGlobalExpansionStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowTest_columnInduction_localToGlobalExpansion : Big fun {D} _ _ _ _ {T} _ _ _ _ _ _ ch => ∀ (s : ℤˣ) (t : T) (β : CosFam ch.G t) (ζ : locPl ch.G t → ℂ), (∀ w : locPl ch.G t, GlobalTheory.LocAsm.PlaceCl ch s t w (β w) (ζ w)) → ∀ (M : Vol ch.G) (hM : M.Is t) (b b₀ : Pts ch.G), IsRep t ch.S.B s β b → IsBase t ch.S.B b₀ → ∀ e : AE D, IsIdemSum e (locPl ch.G t) → ∀ (φ : (∀ w : locPl ch.G t, ∀ b : GlobalTheory.SplitFlip.Edge, Matrix (Fin ((locGrid ch.G t w.1).rank b.tgt)) (Fin ((locGrid ch.G t w.1).rank b.src)) (Kw w.1) → ℂ)), (∀ w : locPl ch.G t, ∀ b ∈ GlobalTheory.SplitFlip.oppositePath D.R.m, GlobalTheory.SplitFlip.IsNatDatum (unifAt w.1) (depthAt ch.G w.1) (φ w b)) → ∀ (fd : SchDown ch.G t), (∀ j : Fin D.R.m, IsLocVec ch.W (.mu t D.R.m j) e (ch.rm.vT D.R.m j) (fun y => if IsHalf e y then ∏ w : locPl ch.G t, φ w (.theta D.R.m j) (ch.S.B.coord t w.1 (X := (D.R.m, j + 1)) (Y := (D.R.m, j)) ⟨le_rfl, j.2⟩ ⟨le_rfl, j.2.le⟩ (y.map fun a => cpt w.1 (toEAf D a))) else 0) (fd j)) → ∀ (eL : locPl ch.G t → AE D), (∀ w, IsIdemSum (eL w) {w.1}) → ∀ (I : locPl ch.G t → Type) (S : ∀ w, Finset (I w)) (x : ∀ w, I w → ℂ) (d : ∀ w, I w → ∀ j : Fin D.R.m, FinDatum ch.G t (.top t j)) (c : ∀ w, I w → Combs ch.G), (∀ w, ∀ i ∈ S w, ∀ j : Fin D.R.m, (d w i j).e = eL w ∧ IsCombOf ch.W (d w i j) ((c w i).1 j)) → (∀ w (y : ∀ j : Fin D.R.m, WO (ch.G.V (.top j)) (ch.G.V (.top (j + 1)))), (∀ j, IsHalf (eL w) (y j)) → ∑ i ∈ S w, x w i * ∏ j, (d w i j).fn (y j) = flatTensor one_le_sLen (psiAt ch.W w.1) (unitVol w.1) (moved (locGrid ch.G t w.1) (keepAt ch.G w.1) ((repsAt ch.G t w.1).elt (β w)) ((locGrid ch.G t w.1).lines₂ (GlobalTheory.SplitFlip.oppositePath D.R.m) (GlobalTheory.LocAsm.exOne (φ w)))) (ch.S.colAt t w.1 y) 0) → ∃ (J : Type) (SJ : Finset J) (xJ : J → ℂ) (dJ : J → ∀ j : Fin D.R.m, FinDatum ch.G t (.top t j)) (cJ : J → ∀ j : ℕ, WO (ch.G.V (.top j)) (ch.G.V (.top (j + 1))) →₀ ℂ), (∀ a ∈ SJ, ∀ j : Fin D.R.m, (dJ a j).e = e ∧ IsCombOf ch.W (dJ a j) (cJ a j)) ∧ (∀ u : ∀ j : Fin D.R.m, WO (ch.G.V (.top j)) (ch.G.V (.top (j + 1))), (∀ j, IsHalf e (u j)) → ∑ a ∈ SJ, xJ a * ∏ j, (dJ a j).fn (u j) = ∏ w : locPl ch.G t, flatTensor one_le_sLen (psiAt ch.W w.1) (unitVol w.1) (moved (locGrid ch.G t w.1) (keepAt ch.G w.1) ((repsAt ch.G t w.1).elt (β w)) ((locGrid ch.G t w.1).lines₂ (GlobalTheory.SplitFlip.oppositePath D.R.m) (GlobalTheory.LocAsm.exOne (φ w)))) (ch.S.colAt t w.1 u) 0) ∧ ∀ (P : PolDown ch.G) (p : Pts ch.G), IsRealPt p → ∀ u : ColPt ch.G, evT (conAt ch.W hM (fockD ch.W t fd P) (p * b)) 1 u 0 = (∏ w, ζ w) * ∑ a ∈ SJ, xJ a * evT (combC ch.W (cJ a, 0) (conAt ch.W hM (fockD ch.W t (fun j => ch.rm.vT D.R.m j) P) (p * b₀))) 1 u 0 := by
  first | exact @GlobalTheory.LocAsm.columnInduction | exact GlobalTheory.LocAsm.columnInduction | (intros; apply GlobalTheory.LocAsm.columnInduction <;> assumption)
end

