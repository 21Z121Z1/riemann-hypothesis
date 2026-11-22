import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0785
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0756
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0764
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0754
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0760
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0769
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0288
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0339
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0777
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0261
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0174
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0002
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0360
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0381
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0533
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0006
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0570
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0567
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0516
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0129
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0221
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0150
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0250
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0140
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0572
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0599
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0203
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0524
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0125
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0310
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AutomorphicCuspFormsHermitianSpaceSignTwist

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselLevelOneCosetAtExceptionalPlacesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselLevel_oneCoset_at_exceptionalPlaces : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), ∀ g ∈ grpAt _ (fun v => v ∈ G.pl.S0), Cond (F.dJ ρ h) (pcBF W F ρ h) (xZero (F.dJ ρ h)) (yBF F ρ h) W.ψ (fun v => v ∈ G.pl.S0) g → ∃ r ∈ Rgrp _ (xZero (F.dJ ρ h)), r ∈ grpAt _ (fun v => v ∈ G.pl.S0) ∧ ∃ k ∈ lev G (.grid (2 * ρ + 1) 0), k ∈ grpAt _ (fun v => v ∈ G.pl.S0) ∧ g = r * k := by
  first | exact @GlobalTheory.OneCosetBF.one_coset_bf | exact GlobalTheory.OneCosetBF.one_coset_bf | (intros; apply GlobalTheory.OneCosetBF.one_coset_bf <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselToFourierJacobiMixedPiecesAdmissible
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.PcBF

variable {D : D7}

theorem symplO_add_right' (S T : HSp D) (x y y' : WO S T) :
    symplO S T x (y + y') = symplO S T x y + symplO S T x y' := by
  simp only [symplO, hO, Matrix.add_apply, map_add, mul_add, add_mul, Finset.sum_add_distrib]

theorem symplO_zero_right' (S T : HSp D) (x : WO S T) : symplO S T x 0 = 0 := by
  simp [symplO, hO]

theorem symplO_neg_right' (S T : HSp D) (x y : WO S T) : symplO S T x (-y) = - symplO S T x y := by
  have := symplO_add_right' S T x y (-y)
  rw [add_neg_cancel, symplO_zero_right'] at this
  exact eq_neg_of_add_eq_zero_right this.symm

theorem ann_of_mem {V V₀ W W₀ : HSp D} {ρ σ : ℕ} (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ)
    (ψ : AddChar (AF D.host.F) ℂ) (Γ Γ' : AddSubgroup (WO V W)) {a' : Mx D W.rank ρ}
    (ha' : a' ∈ (piecesOf (W₀ := W₀) dV dW ψ Γ Γ').A₂) :
    ∀ a ∈ (piecesOf (W₀ := W₀) dV dW ψ Γ Γ').A₁, ψ (symplO V W (dV.extX W a) (dV.extY W a')) = 1 := by
  intro a ha
  induction ha' using AddSubgroup.closure_induction with
  | mem b hb => exact hb.2 a ha
  | zero => rw [map_zero, symplO_zero_right', AddChar.map_zero_eq_one]
  | add b c _ _ hb hc => rw [map_add, symplO_add_right', AddChar.map_add_eq_mul, hb, hc, one_mul]
  | neg b _ hb => rw [map_neg, symplO_neg_right', AddChar.map_neg_eq_inv, hb, inv_one]

end GlobalTheory.PcBF

namespace GlobalTheory.PcBF

theorem pieces_bf : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), (pcBF W F ρ h).Is (F.dB ρ h) (F.dJ ρ h) (xZero (F.dJ ρ h)) W.ψ ∧ Splits (F.dB ρ h) (F.dJ ρ h) (pcBF W F ρ h) (xZero (F.dJ ρ h)) (yBF F ρ h) W.ψ (latRow G (2 * ρ + 1)) := by
  intro D hD T L μ0 hL sc G W M hM F hF ρ h
  refine ⟨⟨GlobalTheory.T.finite_lattice_standard_parabolic D hD T L μ0 hL sc G W M hM F hF ρ h, ⟨?_, (GlobalTheory.T.besselToFourierJacobi_annihilatorPiece_compactOpen D hD T L μ0 hL sc G W M hM F hF ρ h).1, (GlobalTheory.T.besselToFourierJacobi_annihilatorPiece_compactOpen D hD T L μ0 hL sc G W M hM F hF ρ h).2⟩,
    (GlobalTheory.T.bessel_step_pieces_B_finite_adelic_lattices D hD T L μ0 hL sc G W M hM F hF ρ h).1, (GlobalTheory.T.bessel_step_pieces_B_finite_adelic_lattices D hD T L μ0 hL sc G W M hM F hF ρ h).2, ?_, ?_,
    (GlobalTheory.T.bessel_step_pieces_B_mutual_annihilators D hD T L μ0 hL sc G W M hM F hF ρ h).1, (GlobalTheory.T.bessel_step_pieces_B_mutual_annihilators D hD T L μ0 hL sc G W M hM F hF ρ h).2,
    GlobalTheory.T.genericCharacter_trivial_besselStep_unitriangular D hD T L μ0 hL sc G W M hM F hF ρ h, (GlobalTheory.T.bessel_step_core_piece_finite_nonzero_vacuum D hD T L μ0 hL sc G W M hM F hF ρ h).1, (GlobalTheory.T.bessel_step_core_piece_finite_nonzero_vacuum D hD T L μ0 hL sc G W M hM F hF ρ h).2⟩,
    GlobalTheory.T.besselToFourierJacobi_depthLattice_splits D hD T L μ0 hL sc G W M hM F hF ρ h⟩
  · intro a' ha'
    induction ha' using AddSubgroup.closure_induction with
    | mem b hb => exact hb.1
    | zero => intro i j; simp only [Matrix.zero_apply]; exact zero_mem _
    | add b c _ _ hb hc => intro i j; simp only [Matrix.add_apply]; exact add_mem (hb i j) (hc i j)
    | neg b _ hb => intro i j; simp only [Matrix.neg_apply]; exact neg_mem (hb i j)
  · intro a ha
    exact ⟨fun h1 a' h2 => ann_of_mem _ _ _ _ _ h2 a h1, GlobalTheory.T.biduality_depth_lattice_piece_bessel_step D hD T L μ0 hL sc G W M hM F hF ρ h a ha⟩
  · intro a' ha'
    exact ⟨fun h2 a h1 => ann_of_mem _ _ _ _ _ h2 a h1, fun H => AddSubgroup.subset_closure ⟨ha', fun a h1 => H a h1⟩⟩

end GlobalTheory.PcBF
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BoxDepthDataMulLineVacuaBesselLevel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.AscFin.BoxBF

theorem isHalf_mul {D : D7} {m n k : ℕ} {e : AE D} {u : Mx D m n} (h : IsHalf e u) (M : Mx D n k) : IsHalf e (u ⬝ M) := by
  intro i j
  simp only [Matrix.mul_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => by rw [← mul_assoc, h i l]

theorem main : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), ∀ Ξ₁ Ξ₂, VacG W.ψ _ _ (latCore G (2 * ρ + 1)) Ξ₁ → IsThetaFunO W.ψ _ _ Ξ₂ →
    VacG W.ψ _ _ (lineLat F ρ) (fun w => star (Ξ₂ ((F.lnk ρ).κ _ w))) → VacG W.ψ _ _ (pcBF W F ρ h).Γ₀ ((F.oB ρ h).boxS _ Ξ₁ Ξ₂) := by
  intro D hq T L μ0 hL sc G W M hM F hF ρ h Ξ₁ Ξ₂ h1 h2 h3
  have hn : ∀ x, ‖W.ψ x‖ = 1 := W.ψ_std.1.2.1
  refine ⟨(F.oB ρ h).isThetaFunO_boxS h1.1 h2, ?_, ?_⟩
  · intro u hu
    obtain ⟨w, hw, hw'⟩ := GlobalTheory.T.besselStep_lineComponent_eq_kappa_lattice_point D hq T L μ0 hL sc G W M hM F hF ρ h u hu
    rw [OrthDec.heisO_boxS, map_nsmul, Prod.smul_fst, Prod.smul_snd,
      h1.2.1 _ (GlobalTheory.T.besselStep_coreComponent_mem_depthLatticeGridCore D hq T L μ0 hL sc G W M hM F hF ρ h u hu), hw',
      (GlobalTheory.T.linked_line_hom_transport_lattice_vacua D W.ψ hn _ _ _ _ (F.line ρ) (F.lnk ρ) _ Ξ₂ h3.2 w hw).1]
  · intro e he u hu hh
    obtain ⟨w, hw, hw'⟩ := GlobalTheory.T.besselStep_lineComponent_eq_kappa_lattice_point D hq T L μ0 hL sc G W M hM F hF ρ h u hu
    have ha : IsHalf e ((F.oB ρ h).resS (G.V (.core (2 * ρ + 1))) u).1 := isHalf_mul hh _
    have hb : IsHalf e ((F.oB ρ h).resS (G.V (.core (2 * ρ + 1))) u).2 := isHalf_mul hh _
    rw [OrthDec.heisO_boxS, h1.2.2 e he _ (GlobalTheory.T.besselStep_coreComponent_mem_depthLatticeGridCore D hq T L μ0 hL sc G W M hM F hF ρ h u hu) ha, hw']
    rw [hw'] at hb
    rw [(GlobalTheory.T.linked_line_hom_transport_lattice_vacua D W.ψ hn _ _ _ _ (F.line ρ) (F.lnk ρ) _ Ξ₂ h3.2 w hw).2 e he hb]

end GlobalTheory.AscFin.BoxBF
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ColumnsMemPeriodLatticeIffFinitePartMovedLatticeStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj Formalism.IndefR.Datum ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.Geo.Tor
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.columns_mem_periodLattice_iff_finitePart_movedLattice : ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.HeckePointLaws → GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.SplitLinearModel D → GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.VacFixed D →
    ∀ (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
    (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A)
    (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec),
    R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsThP → TieIn T R κ v₀ →
    ∀ (i : Fin D.R.m) (σ : T.Q.c.F →+* ℂ), σ = T.σ₀ → ∀ (hV : T.V ((i : ℕ) + 1) σ = Wc D i) (ph : ℂ)
    (b : Matrix (Fin (Vc D i).rank) (Fin (Vc D i).rank) D.host.E), ‖ph‖ = 1 → GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.IsONLatBasis (Vc D i) b →
    ∀ γ ∈ GQ (Wc D i), ∀ (g : GA D (Wc D i)),
      FrAt (R.MW i (sg0 D A)) R.θ (rank_Wc i) (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV) γ g →
    ∀ (hx : (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV g).2 ∈ ((T.U ((i : ℕ) + 1) σ).X (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV g).1).dom)
      (Wt : UnfAt (T.U ((i : ℕ) + 1) σ) (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV g).1 ⟨(GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV g).2, hx⟩)
      (Y : UnitAt Wt), GlobalTheory.AHPhase.PinAt T R i σ hV ph b γ g hx Wt Y →
    ∀ Yr : Matrix (Fin (Wc D i).rank) (Fin (Vc D i).rank) D.host.E,
      (∀ a, GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.perVec Wt (GlobalTheory.AHPhase.colB b Yr a) ∈ Set.range Wt.Pm) ↔
        actO (Vc D i) (Wc D i) 1 (γ * g)⁻¹ (ratW (Wc D i) (Vc D i) Yr - GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt (Vc D i) (Wc D i) Yr) ∈
          latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True := by
  first | exact @GlobalTheory.AHPhase.cols_per_iff_latO | exact GlobalTheory.AHPhase.cols_per_iff_latO | (intros; apply GlobalTheory.AHPhase.cols_per_iff_latO <;> assumption)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAlgebraicDatumNotMatchedZeroStatement
section
open NumberField IsDedekindDomain
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_algebraicDatum_not_matched_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a')
    (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs G Xc om om' R Rf → ∃ Φ ∈ GlobalTheory.SquareAgree.algD G.M Bs.ψ Bs.emb, ¬ GlobalTheory.PolKer.PolZero Bs G Xc R Rf (Φ) := by
  first | exact @GlobalTheory.PolKer.exists_not_polZero | exact GlobalTheory.PolKer.exists_not_polZero | (intros; apply GlobalTheory.PolKer.exists_not_polZero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsArchimedeanUnitaryWeights
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

noncomputable section

open scoped Matrix

namespace GlobalTheory.BottomRealAct

theorem substF_one_eq_colSub {ι : Type} {N n : ℕ} (M : ι → Matrix (Fin n) (Fin n) ℂ) :
    GlobalTheory.CompactHowe.substF (fun _ => (1 : Matrix (Fin N) (Fin N) ℂ)) M = GlobalTheory.MinorFrame.colSub M := by
  refine MvPolynomial.algHom_ext fun v => ?_
  rw [GlobalTheory.CompactHowe.substF_X]
  simp only [GlobalTheory.MinorFrame.colSub, MvPolynomial.aeval_X]
  rw [Finset.sum_eq_single v.2.1]
  · simp only [Matrix.one_apply_eq, one_mul]
  · intro x _ hx
    simp only [Matrix.one_apply_ne hx, zero_mul, MvPolynomial.C_0, Finset.sum_const_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem rightRegularAction_list_dLR_eq_append {G : Type*} [CommGroup G] (a x y e c : G) : a * x * e / (c * e) = a * y * e / (c * e) * (x * y⁻¹) := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_div, ofMul_inv]
  abel

theorem realAction : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, GlobalTheory.FunPr.Hypotheses₂ → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X →
    ∃ (m : D.what₂.Tau → ℤ) (ρ : GinfC A' →* (D.what₂.Tau → Matrix.unitaryGroup (Fin A'.rank) ℂ)),
      (∀ τ a b, Measurable fun g => (ρ g τ : Matrix (Fin A'.rank) (Fin A'.rank) ℂ) a b) ∧ Function.Surjective ρ ∧
      ∀ (t : T), ∀ x ∈ GfC A', ∀ h ∈ GfC WW, ∀ (g : GinfC A') (P : MvPolynomial (FVar D WW.rank A'.rank) ℂ),
        X.ker' W.ψ W.θ t P h (x * (g : GA D A')) =
          (∏ τ, (ρ g τ : Matrix (Fin A'.rank) (Fin A'.rank) ℂ).det ^ (m τ)) *
            X.ker' W.ψ W.θ t (GlobalTheory.MinorFrame.colSub (fun τ => (ρ g τ : Matrix (Fin A'.rank) (Fin A'.rank) ℂ)) P) h x := by
  intro D T _ L μ₀ sc G W i j A A' WW X hP hI hL hX
  have hθ : IsInfFam W.θ := hX.is.isVac.2.inf
  have hV : HSpace.gram A' = 1 := hX.std'.1
  have hVW : HSpace.gram WW = 1 := hX.stdW.1
  have hW := fun t => GlobalTheory.RowTest.BottomClassSum.weil' hX t

  have hxi : ∀ t τ, HasInfExp D (L.xi t) τ 0 := fun t τ => by
    obtain ⟨n, hn, ho⟩ := hL.xi_fin t
    exact GlobalTheory.Chain.StepVac.hasInfExp_of_order hθ (hL.xi t) hn ho τ
  choose b hb using fun τ => GlobalTheory.SplitCharExp.exists_hasInfExp D W.θ _ WW.rank τ hθ (hW μ₀).hecT (hW μ₀).resT
  have hrel : ∀ t, (L.mu t (↑j + 1) * L.eta ^ (rankV D ↑i ↑j % 2)) /
      (G.ch.chi (D.R.m - ↑i) * L.eta ^ (rankV D ↑i ↑j % 2)) =
      (L.mu μ₀ (↑j + 1) * L.eta ^ (rankV D ↑i ↑j % 2)) / (G.ch.chi (D.R.m - ↑i) * L.eta ^ (rankV D ↑i ↑j % 2)) *
        (L.xi t * (L.xi μ₀)⁻¹) := by
    intro t
    simp only [LevCh.mu, Lift.tup]
    exact rightRegularAction_list_dLR_eq_append _ _ _ _ _
  have hbt : ∀ t τ, HasInfExp D ((L.mu t (↑j + 1) * L.eta ^ (rankV D ↑i ↑j % 2)) /
      (G.ch.chi (D.R.m - ↑i) * L.eta ^ (rankV D ↑i ↑j % 2))) τ (b τ) := by
    intro t τ
    rw [hrel t]
    have := GlobalTheory.Mem.HeckeExp.hasInfExp_mul (hb τ)
      (GlobalTheory.Mem.HeckeExp.hasInfExp_mul (hxi t τ) (GlobalTheory.Mem.HeckeExp.hasInfExp_inv (hxi μ₀ τ)))
    simpa using this
  choose k hk using fun τ => GlobalTheory.T.exists_int_eq_exponent_add_half_index D _ WW.rank τ (b τ) (hW μ₀).hecT (hW μ₀).resT (hb τ)
  refine ⟨k, GlobalTheory.RealColAct.realCol W.θ hθ A' hV, ?_, GlobalTheory.T.realUnitaryFockColumnAction_surjective hθ A' hV, ?_⟩
  · intro τ a c
    simp only [GlobalTheory.RealColAct.realCol_apply, Matrix.transpose_apply]
    exact (((continuous_apply a).comp ((continuous_apply c).comp ((GlobalTheory.RealWeil.continuous_compAt hθ τ _ _).comp
      ((GlobalTheory.RealWeil.continuous_mt A').2.comp continuous_subtype_val))))).measurable
  · intro t x _ h _ g P
    choose a ha using fun τ => GlobalTheory.SplitCharExp.exists_hasInfExp D W.θ _ A'.rank τ hθ (hW t).hecS (hW t).resS
    choose e₁ he₁ using fun τ => GlobalTheory.T.exists_int_eq_exponent_add_half_index D _ A'.rank τ (a τ) (hW t).hecS (hW t).resS (ha τ)
    have hψ : Continuous W.ψ := hX.is.isVac.1.1.1
    have es : X.rA'.s = fun _ => 1 := funext fun τ => (hX.std'.2.2 τ).1
    have eB : X.rA'.B = fun _ => 1 := funext fun τ => (hX.std'.2.2 τ).2
    have esW : X.rW.s = fun _ => 1 := funext fun τ => (hX.stdW.2.2 τ).1
    have eBW : X.rW.B = fun _ => 1 := funext fun τ => (hX.stdW.2.2 τ).2
    have hf : IsThetaFunO W.ψ A' WW (X.f' t) := (GlobalTheory.ConstRatio.theta_f hX.is t).2
    have ho := GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum (hX.is.idem t)
    have hv : ∀ τ, IsFockVacAt (heisO W.ψ A' WW) W.θ τ (cplxO 1 1) (X.f' t) := fun τ => by
      have h0 := hX.is.isVac'.2.fock τ
      rw [es, esW] at h0
      exact GlobalTheory.DatumFock.isFockVacAt_of_isThetaAt hψ hθ ho.conj.infPart_eq ho.conj.conj.infPart_eq (hX.is.snd t)
        hX.is.isVac'.2.theta hf h0
    have hBS : ∀ τ, ((fun _ => (1 : Matrix (Fin A'.rank) (Fin A'.rank) ℂ)) τ)ᴴ * gramAt D A' τ * 1 = 1 := fun τ => by
      rw [GlobalTheory.RealColAct.gramAt_of_gram_one hV]; simp
    have hBT : ∀ τ, ((fun _ => (1 : Matrix (Fin WW.rank) (Fin WW.rank) ℂ)) τ)ᴴ * gramAt D WW τ * 1 = 1 := fun τ => by
      rw [GlobalTheory.RealColAct.gramAt_of_gram_one hVW]; simp
    have key0 := GlobalTheory.RealFockPos.om_pureTensorO_pos D W.ψ W.θ A' WW _ _ (X.ω' t) (hW t) hθ (fun _ => 1) (fun _ => 1) hBS hBT
      a b ha (hbt t) e₁ (fun τ => -k τ) he₁ (fun τ => by push_cast; rw [hk τ]) (X.f' t) hf hv (g : GA D A') g.2 1 (one_mem _) P
    simp only [inv_one, Matrix.one_mul, Matrix.mul_one, GlobalTheory.StdUnn.CartanMove.compAt_mt_one, Matrix.det_one, one_zpow, mul_one]
      at key0
    have hinv : ∀ τ, (compAt W.θ τ (Formalism.L2.Theta.mt A' (g : GA D A')))⁻¹ =
        compAt W.θ τ (Formalism.L2.Theta.mt A' (g : GA D A')⁻¹) := fun τ =>
      Matrix.inv_eq_right_inv (GlobalTheory.OrientedHeis.compAt_mt_mul_inv (θ := W.θ) τ (g : GA D A'))
    have hsc : ∀ τ, (compAt W.θ τ (Formalism.L2.Theta.mt A' (g : GA D A'))).det ^ (-k τ) =
        ((GlobalTheory.RealColAct.realCol W.θ hθ A' hV g τ : Matrix (Fin A'.rank) (Fin A'.rank) ℂ)).det ^ (k τ) := fun τ => by
      rw [GlobalTheory.RealColAct.realCol_apply, Matrix.det_transpose, ← hinv, Matrix.det_nonsing_inv, Ring.inverse_eq_inv',
        inv_zpow', zpow_neg]
    have hsub : GlobalTheory.CompactHowe.substF (fun _ => (1 : Matrix (Fin WW.rank) (Fin WW.rank) ℂ))
        (fun τ => ((compAt W.θ τ (Formalism.L2.Theta.mt A' (g : GA D A')))⁻¹)ᵀ) =
        GlobalTheory.MinorFrame.colSub (fun τ => (GlobalTheory.RealColAct.realCol W.θ hθ A' hV g τ : Matrix (Fin A'.rank) (Fin A'.rank) ℂ)) := by
      rw [substF_one_eq_colSub]
      congr 1
      funext τ
      rw [GlobalTheory.RealColAct.realCol_apply, hinv]
    have key : (X.ω' t) ((g : GA D A'), 1) ((pureTensorO W.ψ W.θ A' WW (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 1) (X.f' t)) P) =
        (∏ τ, ((GlobalTheory.RealColAct.realCol W.θ hθ A' hV g τ : Matrix (Fin A'.rank) (Fin A'.rank) ℂ)).det ^ (k τ)) •
          (pureTensorO W.ψ W.θ A' WW (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 1) (X.f' t))
            (GlobalTheory.MinorFrame.colSub (fun τ => (GlobalTheory.RealColAct.realCol W.θ hθ A' hV g τ : Matrix (Fin A'.rank) (Fin A'.rank) ℂ)) P) := by
      rw [key0, ← hsub]
      congr 1
      exact Finset.prod_congr rfl fun τ _ => hsc τ
    unfold Tri.ker' thetaKO
    rw [es, eB, esW, eBW]
    have e : ((x * (g : GA D A'), h) : GA D A' × GA D WW) = (x, h) * ((g : GA D A'), 1) := by simp
    rw [e, map_mul, Module.End.mul_apply, key, map_smul, Pi.smul_apply, smul_eq_mul]

end GlobalTheory.BottomRealAct
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsWeightedAverageHaar
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

noncomputable section
open scoped ComplexOrder
open GlobalTheory.ClassRegroup GlobalTheory.DefiniteClassAvg GlobalTheory.DefiniteClassReal
open GlobalTheory.Grid (neg sgn ofSgn)

namespace GlobalTheory.RowTest.BottomClassSumNeg

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {i j : Fin D.R.m}
    {A A' WW : HSp D} {X : Tri T A A' WW}

theorem theta (hX : IsBottomTri W i j X) (t : T) (P : PolF D WW.rank A.rank) :
    IsThetaFunO W.ψ (neg A) WW (pureTensorO W.ψ W.θ (neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) P) :=
  GlobalTheory.Chain.InnerSteps.theta_pureTensorO (S := neg A) (T := WW) hX.is.isVac.1 hX.is.isVac.2.inf (fun τ => -X.rA.s τ) X.rA.B X.rW.s X.rW.B
    (GlobalTheory.ConstRatio.theta_f hX.is t).1 P

theorem ker_eq (t : T) (P : PolF D WW.rank A.rank) (h : GA D WW) (g : GA D A) :
    X.ker W.ψ W.θ t P h g = thetaKO ((X.ω t).toSgn true) ((ofSgn true A).symm g) h
      (pureTensorO W.ψ W.θ (neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) P) := by
  show thetaKO (X.ω t) g h _ = (X.ω t) ((ofSgn true A) ((ofSgn true A).symm g), h) _ 0
  rw [MulEquiv.apply_symm_apply]
  rfl

theorem ker_left (hX : IsBottomTri W i j X) (t : T) (P : PolF D WW.rank A.rank) (h : GA D WW) :
    ∀ γ ∈ GQ A, ∀ g, X.ker W.ψ W.θ t P h (γ * g) = X.ker W.ψ W.θ t P h g := by
  intro γ hγ g
  have hK := GlobalTheory.thetaKO_rat_left_and_eigen_right W.ψ (neg A) WW _ _ _ (hX.is.weil t) _ (theta hX t P)
  rw [ker_eq, ker_eq, map_mul]
  have := hK.1 _ ((GlobalTheory.SgnIdent.mem_GQ_sgn true A _).2 (by rwa [MulEquiv.apply_symm_apply])) 1 (one_mem _)
    ((ofSgn true A).symm g) h
  rwa [one_mul] at this

theorem ker_cont (hX : IsBottomTri W i j X) (t : T) (P : PolF D WW.rank A.rank) (h : GA D WW) (x : GA D A) :
    Continuous fun k : GinfC A => X.ker W.ψ W.θ t P h (x * k) := by
  have hW := hX.is.weil t
  have hF := theta hX t P
  simp_rw [ker_eq]
  exact (hW.om_cont _ hF 0).comp (((GlobalTheory.Grid.continuous_ofSgn_symm true A).comp
    (continuous_const.mul continuous_subtype_val)).prodMk continuous_const)

end GlobalTheory.RowTest.BottomClassSumNeg

namespace GlobalTheory.RowTest.BottomClassSumNeg

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {i j : Fin D.R.m}
    {A A' WW : HSp D} {X : Tri T A A' WW}

theorem level_all [Finite T] (t₀ : T) (hX : IsBottomTri W i j X) :
    ∃ K : Subgroup (GL (Fin A.rank) (Lev.EAf D)), GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.IsOpenCompactLevel A K ∧
      ∀ (t : T) (P : PolF D WW.rank A.rank) (h : GA D WW), ∀ k ∈ Lev.levA A K, ∀ g,
        X.ker W.ψ W.θ t P h (g * k) = X.ker W.ψ W.θ t P h g := by
  choose K hK hinv using GlobalTheory.T.exists_openCompactLevel_thetaKernel_source hX
  refine ⟨⨅ t, K t, ⟨?_, ?_⟩, fun t P h k hk g => hinv t P h k ?_ g⟩
  · have e : (((⨅ t, K t).comap (Lev.finE A) : Subgroup (GA D A)) : Set (GA D A)) =
        ⋂ t, (((K t).comap (Lev.finE A) : Subgroup (GA D A)) : Set (GA D A)) := by
      ext x; simp [Subgroup.mem_iInf]
    rw [e]
    exact isOpen_iInter_of_finite fun t => (hK t).1
  · have hcl : IsClosed ((((⨅ t, K t).comap (Lev.finE A) : Subgroup (GA D A)) : Set (GA D A))) := by
      have e : (((⨅ t, K t).comap (Lev.finE A) : Subgroup (GA D A)) : Set (GA D A)) =
          ⋂ t, (((K t).comap (Lev.finE A) : Subgroup (GA D A)) : Set (GA D A)) := by
        ext x; simp [Subgroup.mem_iInf]
      rw [e]
      exact isClosed_iInter fun t => Subgroup.isClosed_of_isOpen _ (hK t).1
    have e2 : ((Lev.levA A (⨅ t, K t) : Subgroup (GA D A)) : Set (GA D A)) =
        (Lev.levA A (K t₀) : Set (GA D A)) ∩ (((⨅ t, K t).comap (Lev.finE A) : Subgroup (GA D A)) : Set (GA D A)) := by
      ext x
      simp only [SetLike.mem_coe, Set.mem_inter_iff, Lev.mem_levA, Subgroup.mem_comap]
      exact ⟨fun ⟨h1, h2⟩ => ⟨⟨h1, (Subgroup.mem_iInf.1 h2) t₀⟩, h2⟩, fun ⟨⟨h1, _⟩, h2⟩ => ⟨h1, h2⟩⟩
    rw [e2]
    exact (hK t₀).2.inter_right hcl
  · obtain ⟨hk1, hk2⟩ := Lev.mem_levA.1 hk
    exact Lev.mem_levA.2 ⟨hk1, (Subgroup.mem_iInf.1 hk2) t⟩

theorem integral_eq_classSum_bottom : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, GlobalTheory.FunPr.Hypotheses₂ → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X →
    ∃ (v : ℝ) (N : ℕ) (z : Fin N → GA D A) (w : Fin N → ℕ) (κ : Measure (GinfC A)), 0 < v ∧ (∀ l, z l ∈ GfC A) ∧
      (∀ l, 0 < w l) ∧ κ.IsMulLeftInvariant ∧ IsProbabilityMeasure κ ∧
      ∀ (t : T) (P : PolF D WW.rank A.rank), ∀ h ∈ GfC WW,
        X.I W.ψ W.θ t P h = (v : ℂ) * ∑ l, ((w l : ℂ))⁻¹ * ∫ g, X.ker W.ψ W.θ t P h (z l * (g : GA D A)) ∂κ := by
  intro D T _ L μ₀ sc G W i j A A' WW X _ _ hL hX
  have hV : ∀ φ : D.host.E →+* ℂ, (A.gram.map φ).PosDef := fun φ => by
    rw [hX.std.1, Matrix.map_one φ (map_zero φ) (map_one φ)]
    exact Matrix.PosDef.one
  let V' : HSp D := { A with sig := fun _ => (A.rank, 0) }
  have hS' : V'.SigOK := fun τ => GlobalTheory.Proof.GenusMassSignature.hasSignature_of_posDef (hV τ)
  have hD' : V'.IsDefinite := fun τ => Or.inl rfl
  have hGc : IsCompact (GinfC A : Set (GA D A)) := Formalism.IndefR.Eqv.isCompact_GinfC (V := V') hS' hD'
  haveI : CompactSpace (GinfC A) := isCompact_iff_compactSpace.1 hGc
  have hT := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D A
  have hLC := hT.1
  have hSC := hT.2.1
  have hB := hT.2.2.2.1
  have hG := hT.2.2.2.2.1
  have hC := hT.2.2.2.2.2.2
  obtain ⟨K'', hK'', hr⟩ := level_all μ₀ hX
  have hfin0 : Finite (FinCl A K'') := (finite_finCl_and_gamOrd A K'' hV hK'').1
  let μ := X.m
  haveI : μ.IsHaarMeasure := hX.is.meas.1
  have hfd : IsFundamentalDomain (GQ A) X.fd μ := hX.is.meas.2
  let J : Subgroup (GA D A) := K''.comap (Lev.finE A)
  have hJo : IsOpen (J : Set (GA D A)) := hK''.1
  have hJc : IsCompact (J : Set (GA D A)) := by
    refine (hK''.2.mul hGc).of_isClosed_subset (Subgroup.isClosed_of_isOpen J hK''.1) ?_
    intro k hk
    exact ⟨finPart A k, finPart_mem_levA A hk, realPart A k, realPart_mem A k, finPart_mul_realPart A k⟩
  have hJtop : μ J ≠ ⊤ := hJc.measure_lt_top.ne
  have hJ0 : μ J ≠ 0 := (hJo.measure_pos μ ⟨1, J.one_mem⟩).ne'
  have hinfJ : GinfC A ≤ J := by
    show GinfC A ≤ K''.comap (Lev.finE A)
    rw [GlobalTheory.Mass.Levels.comap_finE]
    exact le_sup_right
  let κ : Measure (GinfC A) := Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts (GinfC A))
  haveI hκH : κ.IsHaarMeasure := Measure.isHaarMeasure_haarMeasure _
  have hκ1 : κ Set.univ = 1 := by
    have := Measure.haarMeasure_self (K₀ := (⊤ : TopologicalSpace.PositiveCompacts (GinfC A)))
    simpa using this
  haveI : IsProbabilityMeasure κ := ⟨hκ1⟩
  let e := finEquiv A
  have he : ∀ γ, e (((finPt A).comp (GQ A).subtype) γ) = Bridge.ratF A γ := fun γ => e.apply_symm_apply _
  have hJe : ∀ a, e a ∈ GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.levelFin A K'' ↔ a ∈ K''.comap (finG A) := fun a => Iff.rfl
  have hy := isReps_transfer _ _ e he _ _ hJe _ (isReps_out A K'')
  let N := Nat.card (FinCl A K'')
  let eq : FinCl A K'' ≃ Fin N := Finite.equivFin _
  let y : FinCl A K'' → Bridge.Gf A := fun c => e (Quotient.out c)
  let zc : FinCl A K'' → GA D A := fun c => ((Quotient.out c : GfC A) : GA D A)
  have hz : ∀ c, (finHom A).rangeRestrict (zc c) = y c := fun c => rfl
  have hu0 : ∀ x : GA D A, ∃! c, ∃ γ ∈ GQ A, ∃ k ∈ J, x = γ * zc c * k :=
    existsUnique_doubleCoset (finHom A).rangeRestrict (GQ A) (GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.levelFin A K'') y hy zc hz
  let z : Fin N → GA D A := fun l => zc (eq.symm l)
  have hu : ∀ x : GA D A, ∃! l, ∃ γ ∈ GQ A, ∃ k ∈ J, x = γ * z l * k := fun x =>
    (eq.existsUnique_congr_left (p := fun c => ∃ γ ∈ GQ A, ∃ k ∈ J, x = γ * zc c * k)).1 (hu0 x)
  have hfinΓ : ∀ l, {γ : GQ A | (z l)⁻¹ * (γ : GA D A) * z l ∈ J}.Finite := fun l =>
    GlobalTheory.InnerClassSum.finite_stab_of_measure μ (GQ A) J hfd hJ0 hJtop (z l)
  have him : ∀ l, {γ : GA D A | γ ∈ GQ A ∧ (z l)⁻¹ * γ * z l ∈ J} =
      Subtype.val '' {γ : GQ A | (z l)⁻¹ * (γ : GA D A) * z l ∈ J} := by
    intro l
    ext γ
    simp only [Set.mem_setOf_eq, Set.mem_image, Subtype.exists, exists_and_right, exists_eq_right]
    exact ⟨fun h => ⟨h.1, h.2⟩, fun ⟨h, h'⟩ => ⟨h, h'⟩⟩
  have hfin : ∀ l, {γ : GA D A | γ ∈ GQ A ∧ (z l)⁻¹ * γ * z l ∈ J}.Finite := fun l =>
    him l ▸ (hfinΓ l).image _
  have hdec : ∀ k ∈ J, ∃ k' ∈ Lev.levA A K'', ∃ w : GinfC A, k = k' * (GinfC A).subtype w := fun k hk =>
    ⟨finPart A k, finPart_mem_levA A hk, ⟨realPart A k, realPart_mem A k⟩, (finPart_mul_realPart A k).symm⟩
  have hcomm : ∀ k ∈ Lev.levA A K'', ∀ w : GinfC A, k * (GinfC A).subtype w = (GinfC A).subtype w * k :=
    fun k hk w => (Formalism.IndefR.Eqv.Act.comm_inf_fin w.2 (Subgroup.mem_inf.1 hk).1).symm
  have hrt : ∀ w : GinfC A, MeasurePreserving (· * (GinfC A).subtype w) μ μ := fun w =>
    measurePreserving_mul_right_of_mem μ J hJo hJ0 hJtop (hinfJ w.2)
  refine ⟨(μ J).toReal, N, z, fun l => {γ : GA D A | γ ∈ GQ A ∧ (z l)⁻¹ * γ * z l ∈ J}.ncard, κ,
    ENNReal.toReal_pos hJ0 hJtop, fun l => (Quotient.out (eq.symm l)).2, fun l => ?_, inferInstance, inferInstance,
    fun t P h _ => ?_⟩
  · exact (Set.ncard_pos (hfin l)).2 ⟨1, (GQ A).one_mem, by simp [J.one_mem]⟩
  · have hcont : Continuous (X.ker W.ψ W.θ t P h) :=
      continuous_of_level A K'' hK''.1 _ (fun k hk g => hr t P h k hk g) (ker_cont hX t P h)
    obtain ⟨-, heq⟩ := integral_eq_sum_avg (GA D A) μ (GQ A) J (Lev.levA A K'') X.fd hfd hJo hJtop (GinfC A) κ
      (GinfC A).subtype continuous_subtype_val hrt hdec hcomm (Fin N) z hu hfin (X.ker W.ψ W.θ t P h) hcont
      (ker_left hX t P h) (fun k hk g => hr t P h k hk g)
    exact heq

end GlobalTheory.RowTest.BottomClassSumNeg

end
end

