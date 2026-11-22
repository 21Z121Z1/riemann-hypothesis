import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0032
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0010
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0450
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0461
import Formalism.LocalToGlobal.Divisibility.TiedLemmas
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0480
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0486
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0481
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0482
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotRelZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0195
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1674
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1689
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlockDetBlockTriangular
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLatticeHomApproxIntegralMatrixMod
import Formalism.LocalToGlobal.Divisibility.DefGroupLemmas
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0165
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.RowHighestLeSpanColWordComplex
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0061
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaKernelOrthonormalFrameInDomainPeriodLinear
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0445
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RealSmulSplit
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RadicalNoFixedVectors
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0012
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0003
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0135
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0382
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0397
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0415
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0411
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0485
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0483
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0182
import Formalism.LocalToGlobal.IndefiniteReal.SquareIntegrableTransfer
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0384
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0407
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0290
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0284
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0375
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0484
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0472
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFrameReductionEqFlagBasisOtherInstance
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead

noncomputable section

namespace GlobalTheory.SeeConjRead

theorem cT_mul_entry {A : Type} [CommRing A] {n : ℕ} (σ : A →+* A) (U J W : Matrix (Fin n) (Fin n) A) (a b : Fin n) :
    (Formalism.UG.cT σ U * J * W) a b = Formalism.UG.hform σ J (fun i => U i a) (fun i => W i b) := by
  unfold Formalism.UG.cT Formalism.UG.hform
  simp only [Matrix.mul_apply, Finset.sum_mul, Matrix.transpose_apply, Matrix.map_apply]
  exact Finset.sum_comm

theorem over_g {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type}
    [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (hL : R.toLevCh.Is A.μ0) {Q : Pl D.host.E}
    (hQ : Q ∈ R.Pg) : ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ Q.asIdeal := by
  obtain ⟨k, hk⟩ := (hL.Pg Q).1 hQ
  have hmem : ((D.host.g k : ℕ) : 𝓞 D.host.K) ∈ (Q.under (𝓞 D.host.K)).asIdeal := by
    rw [show Q.under (𝓞 D.host.K) = R.C.P.pb k from hk]
    exact R.C.P.pb_over k
  rw [IsDedekindDomain.HeightOneSpectrum.under_asIdeal, Ideal.under_def, Ideal.mem_comap, map_natCast] at hmem
  rw [Nat.cast_mul]
  fin_cases k
  · exact Ideal.mul_mem_right _ _ hmem
  · exact Ideal.mul_mem_left _ _ hmem

theorem exists_frame_redIs : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → ∃ β : GL (Fin (Yc D 0).rank) (EAf D), IsFrame β (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) ∧ ∀ PP ∈ R.Pg, RedIs β PP (flagAt X h PP) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F X h hL _
  have hn : (Yc D 0).rank = 2 * D.R.rS + D.R.k + 1 := by
    rw [show (Yc D 0).rank = D.R.rankY 0 from D.sp.Y_rank 0 (Nat.zero_le _)]
    have hm := D.R.m_even
    have h2 := D.R.two_le_m
    unfold Formalism.BasicNotions.Ranks.rankY Formalism.BasicNotions.Ranks.rS Formalism.BasicNotions.Ranks.r
    obtain ⟨c, hc⟩ := hm
    omega
  obtain ⟨β₀, hβ₀⟩ := GlobalTheory.StdFrames.exists_base (Yc D 0)
  have hG := (GlobalTheory.StdFrames.unimod_of_isSD (GlobalTheory.StdFrames.isSD_one hβ₀)).1
  have hint := fun PP i j => GlobalTheory.T.flagPairingVectors_integral_inFrame X h β₀ hβ₀ PP i j
  have hdet : ∀ Q ∈ R.Pg,
      Valued.v (GlobalTheory.StdFrames.cpt Q ((β₀⁻¹).val * colMat (flagAt X h Q)).det) = 1 := by
    intro Q hQ
    have hg := over_g R hL hQ
    refine GlobalTheory.T.standard_frame_integrality_conditions β₀ (GlobalTheory.IndefiniteRowSideFullHecke.ChainMatrices.ratM (Yc D 0).gram) (colMat (pairAt X h Q))
      (colMat (flagAt X h Q)) Q (fun a => sgnD D.R.rS D.R.k a) hG (fun i j => (hint Q i j).2)
      (fun i j => (hint Q i j).1) ?_ ?_
    · intro a
      unfold sgnD
      split_ifs <;> simp
    · intro a b
      rw [cT_mul_entry]
      change SmallAt Q (hY D (pairAt X h Q a) (flagAt X h Q b) - _)
      by_cases hc : GlobalTheory.StdFrames.cpt Q (ewT X h) = 1
      · rw [pairAt, flagAt, if_pos hc, if_pos hc]
        exact GlobalTheory.T.flagPairingTable_diagonal_modSmall (hY D) (SmallAt Q) D.R.rS D.R.k _ hn _ _ _ _ _ (GlobalTheory.T.flagPairingTable_idempotentComponent_one X h Q hg hc) a b
      · rw [pairAt, flagAt, if_neg hc, if_neg hc]
        exact GlobalTheory.T.flagPairingTable_diagonal_modSmall (hY D) (SmallAt Q) D.R.rS D.R.k _ hn _ _ _ _ _ (GlobalTheory.T.flagPairingTable_idempotentComponent_ne_one X h Q hg hc) a b
  obtain ⟨β, hβ, hred⟩ := GlobalTheory.T.exists_frame_lifting_prescribed_reductions β₀ R.Pg (flagAt X h) (fun Q _ i j => (hint Q i j).1) hdet
  refine ⟨β, ?_, hred⟩
  rw [hβ₀, ← hβ]
  exact GlobalTheory.StdFrames.isFrame_lat β

end GlobalTheory.SeeConjRead

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsGridFr
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.RouteSeesaw GlobalTheory.ChainFr

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.SquareDict

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

def datumA (W : G.Weil) {t : T} {i j : ℕ} (Θ : TotT G (routeBig t i j)) :
    WO (G.V (.grid (i + 1) (j + 1))) (GlobalTheory.Doubling.hsum (G.V (.grid i (j + 1))) (G.V (.grid (i + 1) j))) → ℂ :=
  Θ.sum fun d c => c • box2 (S := negSp (G.V (.grid (i + 1) (j + 1)))) (A := G.V (.grid i (j + 1))) (B := G.V (.grid (i + 1) j))
    d.1.2 (fun y => d.2 (adjM (G.V (.grid (i + 1) (j + 1))) (G.V (.grid (i + 1) j)) y))

def datumB (W : G.Weil) {t : T} {i j : ℕ} (Θ : TotT G (routeSmall t i j)) :
    WO (G.V (.grid i j)) (GlobalTheory.Doubling.hsum (G.V (.grid i (j + 1))) (G.V (.grid (i + 1) j))) → ℂ :=
  Θ.sum fun d c => c • box2 (S := G.V (.grid i j)) (A := G.V (.grid i (j + 1))) (B := G.V (.grid (i + 1) j))
    d.1.2 (fun y => d.2 (adjM (G.V (.grid i j)) (negSp (G.V (.grid (i + 1) j))) y))

def IsGridFr (W : G.Weil) (X : Node) (A : Fr (G.V X)) : Prop :=
  ∀ τ, A.onb τ = W.onb X τ ∧ A.cart τ = W.cart X τ

theorem exists_isGridFr (W : G.Weil) {X : Node} (hX : X.InRange D.R.m) : ∃ A : Fr (G.V X), IsGridFr W X A := by
  choose ε hε using W.onb_is X hX
  have hu : ∀ τ, IsUnit (W.onb X τ) := fun τ => by
    have h1 : IsUnit ((W.onb X τ)ᴴ * gramAt D (G.V X) τ * W.onb X τ) := by
      rw [(hε τ).1]
      refine ⟨⟨Formalism.REAL.Jm (ε τ), Formalism.REAL.Jm (ε τ), ?_, ?_⟩, rfl⟩ <;>
      · ext a b
        by_cases h : a = b
        · subst h; cases h' : ε τ a <;> simp [Formalism.REAL.Jm, Matrix.mul_apply, Matrix.diagonal_apply, h', Matrix.one_apply]
        · simp [Formalism.REAL.Jm, Matrix.mul_apply, Matrix.diagonal_apply, h, Matrix.one_apply]
    rw [Matrix.isUnit_iff_isUnit_det] at h1 ⊢
    rw [Matrix.det_mul] at h1
    exact isUnit_of_mul_isUnit_right h1
  refine ⟨⟨ε, fun τ => (W.onb X τ)⁻¹, fun τ => (Matrix.isUnit_nonsing_inv_iff).2 (hu τ), fun τ => ?_⟩, fun τ => ⟨?_, ?_⟩⟩
  · have hd : IsUnit (W.onb X τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (hu τ)
    rw [← (hε τ).1, Matrix.conjTranspose_nonsing_inv]
    simp only [← Matrix.mul_assoc]
    rw [Matrix.nonsing_inv_mul _ (by simpa [Matrix.det_conjTranspose] using hd.star), Matrix.one_mul, Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ hd, Matrix.mul_one]
  · have hd : IsUnit (W.onb X τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (hu τ)
    show ((W.onb X τ)⁻¹)⁻¹ = W.onb X τ
    exact Matrix.nonsing_inv_nonsing_inv _ hd
  · have hd : IsUnit (W.onb X τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (hu τ)
    show ((W.onb X τ)⁻¹)⁻¹ * Formalism.REAL.Jm (ε τ) * (W.onb X τ)⁻¹ = W.cart X τ
    rw [Matrix.nonsing_inv_nonsing_inv _ hd, ← (hε τ).2, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.mul_one]

def zact {S X : HSp D} (ω : GlobalTheory.Grid.WRep S X) (z : GA D S →₀ ℂ) (Φ : WO S X → ℂ) : WO S X → ℂ :=
  z.sum fun k c => c • ω (k, 1) Φ

end GlobalTheory.SquareDict
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRationalHomApproxHalfModIdeal
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.CosRatApprox

open GlobalTheory.FunObj.Comparison₂

theorem infPart_idemSum_mul {D : D7} {e : AE D} {P : Finset (Formalism.L2.DIV.Pl D.host.E)} (he : IsIdemSum e P) (a : AE D) :
    infPart D (e * a) = 0 := by
  obtain ⟨e0, -, -⟩ := cpt_idemSum he
  rw [(infPart D).map_mul, e0, zero_mul]

set_option maxHeartbeats 1000000 in

theorem exists_rat_approx : ∀ {D : D7} {m n : ℕ} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} {Λ' : Submodule (𝓞 D.host.E) (Fin m → D.host.E)} {𝔪 : Ideal (𝓞 D.host.E)}, 𝔪 ≠ ⊥ → Submodule.IsLattice D.host.E Λ → Submodule.IsLattice D.host.E Λ' → ∀ {e : AE D} {P : Finset (Formalism.L2.DIV.Pl D.host.E)}, IsIdemSum e P → ∀ z : Mx D m n, IsHalf e z → z ∈ hatMx (homLat Λ Λ') → ∃ x₁ : homLat Λ Λ', z - e • (x₁ : Matrix (Fin m) (Fin n) D.host.E).map (incA D) ∈ hatMx (𝔪 • homLat Λ Λ') := by
  intro D m n Λ Λ' 𝔪 h𝔪 hΛ hΛ' e P he z hz hzmem
  obtain ⟨β, hβ⟩ := Formalism.L2.DIV.frame_exists_alt D.host.F D.host.E n Λ hΛ
  obtain ⟨β', hβ'⟩ := Formalism.L2.DIV.frame_exists_alt D.host.F D.host.E m Λ' hΛ'
  have hz' : z ∈ hatMx ((⊤ : Ideal (𝓞 D.host.E)) • homLat Λ Λ') := by rwa [Submodule.top_smul]
  obtain ⟨-, hs⟩ := (mem_hatMx_iff hβ hβ' ⊤ z).1 hz'
  choose s _ hs' using hs
  obtain ⟨x₀, hx₀, ht⟩ := GlobalTheory.FunObj.HatFrame.homLat_approx_mod Λ Λ' β β' hβ hβ' 𝔪 h𝔪 s
  choose t htI htv using ht
  have k1 : ∀ i j, (z - e • x₀.map (incA D)) i j = e * (z i j - incA D (x₀ i j)) :=
    fun i j => by rw [mul_sub, hz i j]; rfl
  have k2 : ∀ i j, fr β' β ((z - e • x₀.map (incA D)).map (toEAf D)) i j =
      toEAf D e * (fr β' β (z.map (toEAf D)) i j - fr β' β (x₀.map (eToEAf D)) i j) := fun i j => by
    have : (z - e • x₀.map (incA D)).map (toEAf D) = toEAf D e • (z.map (toEAf D) - x₀.map (eToEAf D)) :=
      Matrix.ext fun i j => by rw [Matrix.map_apply, k1, RingHom.map_mul, RingHom.map_sub]; rfl
    rw [this, fr_smul, fr_sub]; rfl
  refine ⟨⟨x₀, hx₀⟩, ?_⟩
  show z - e • x₀.map (incA D) ∈ hatMx (𝔪 • homLat Λ Λ')
  refine (mem_hatMx_iff hβ hβ' 𝔪 _).2 ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [k1 i j]; exact infPart_idemSum_mul he _
  · let eS : {x // x ∈ Formalism.L2.Herm.intAf D.host.F D.host.E} := ⟨toEAf D e, GlobalTheory.CosToCoset.idem_mem_OA he⟩
    refine ⟨eS * -t i j, Ideal.mul_mem_left _ eS (neg_mem (htI i j)), ?_⟩
    rw [k2, ← hs' i j]
    show toEAf D e * -((t i j : Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) = _
    rw [htv i j, neg_sub]

end GlobalTheory.CosRatApprox
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRealPointStandardSourceUnitaryComponentsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_realPoint_standardSource_unitaryComponents : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (v : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ), (∀ τ, (v τ)ᴴ * v τ = 1) → ∃ h ∈ GinfC S, ∀ τ, compAt C.θ τ (mt S h) = v τ := by
  first | exact @GlobalTheory.StdRealLift.exists_real_point | exact GlobalTheory.StdRealLift.exists_real_point | (intros; apply GlobalTheory.StdRealLift.exists_real_point <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSplitFramePrincipalLevelFiniteGroupStatement
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Cx
open GlobalTheory.LiftRows
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_splitFrame_principalLevel_finiteGroup : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ) (L : LevDat D.host.E ℂ V.rank) (h : L.r = V.rank), IsBaseFrame V β Λ N → L.Q = ∅ → (∀ PP ∈ L.Pg, ∀ PP' ∈ L.Pg, ¬ Formalism.IndefR.Lev.IsConjPl PP PP') → ∃ (a : GfC V) (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) (pl : S ≃ L.Pg) (s : ∀ v : S, SplitAt D.sp.cm.sig V.gram (frameLat V) v) (ρ : ∀ v : S, ResF v.1 ≃+* kP (pl v).1), (∀ v ∉ S, ∀ k ∈ Kv V v, ((a * locFin V v k * a⁻¹ : GfC V) : GA D V) ∈ levG V β (flag1L L)) ∧ ∀ (v : S) (k : Kv V v), ∃ g0 : G0 L.Pg L.r, IsLevelLift V β L g0 ((a * locFin V v k * a⁻¹ : GfC V) : GA D V) ∧ (∀ PP, PP ≠ pl v → g0 PP = 1) ∧ ∀ i j : Fin L.r, (g0 (pl v)).1 i j = ρ v (((s v).red k).1 (i.cast h) (j.cast h)) := by
  first | exact @GlobalTheory.TrPtFrame.exists_splitFrame_levG | exact GlobalTheory.TrPtFrame.exists_splitFrame_levG | (intros; apply GlobalTheory.TrPtFrame.exists_splitFrame_levG <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsTestGridFromLevelChoiceGridStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_testGrid_from_levelChoiceGrid : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : GlobalTheory.ChiGrid.Consts}, GlobalTheory.Published.DiscreteSeriesUpqExists → HostHyp D → ∀ {F : Face D A}, GlobalTheory.Hk3.Core R F → sc.cGap = 1 → ∀ {G' : GlobalTheory.ChiGrid.GridData R.toLevCh sc} (W : G'.Weil), W.Over R → (∀ X : GlobalTheory.ChiGrid.Node, X.InRange D.R.m → (∀ j, X ≠ .grid 0 j) → (G'.Λ X : Set _) = L0c D (G'.V X)) → (∀ PP ∈ R.Pg, ∀ PP' ∈ R.Pg, PP.under (𝓞 D.host.F) = PP'.under (𝓞 D.host.F) → PP = PP') → Formalism.L2.Host.SplitsCompletely {G'.pl.w G'.pl.v0} → (∀ k, GlobalTheory.ChiGrid.q0 D ≠ D.host.g k) → (GlobalTheory.ChiGrid.q0 D ≠ D.sp.T ∧ ∀ u : D.what₂.Word, GlobalTheory.ChiGrid.q0 D ≠ (D.mem u).A.T) → (∀ i j, 1 ≤ i → i ≤ D.R.m → j ≤ D.R.m → ∀ τ, ∃ (lam : Fin (G'.V (.grid i j)).rank → ℝ) (ε : Fin (G'.V (.grid i j)).rank → Bool), IsEnum (GlobalTheory.Grid.parV D i j τ) lam ε ∧ (W.onb (.grid i j) τ)ᴴ * gramAt D (G'.V (.grid i j)) τ * W.onb (.grid i j) τ = Formalism.REAL.Jm ε) → (∀ i, i ≤ D.R.m → ∀ τ, ∃ (lam : Fin (G'.V (.core i)).rank → ℝ) (ε : Fin (G'.V (.core i)).rank → Bool), IsEnum (GlobalTheory.Grid.parP D i τ) lam ε ∧ (W.onb (.core i) τ)ᴴ * gramAt D (G'.V (.core i)) τ * W.onb (.core i) τ = Formalism.REAL.Jm ε) → (∀ j, 1 ≤ j → j ≤ D.R.m → ∀ τ, ∃ (lam : Fin (G'.V (.top j)).rank → ℝ) (ε : Fin (G'.V (.top j)).rank → Bool), IsEnum (GlobalTheory.Grid.parXp D j τ) lam ε ∧ (W.onb (.top j) τ)ᴴ * gramAt D (G'.V (.top j)) τ * W.onb (.top j) τ = Formalism.REAL.Jm ε) → W.cart (.top 0) = W.cart (.core D.R.m) → W.onb (.top 0) = W.onb (.core D.R.m) → ∀ e : AE D, IsIdemSum e G'.pl.W0 → ∃ G : GlobalTheory.Grid.GridPre R, G.idem = e ∧ G.IsSpaces ∧ G.IsChars ∧ SpAgree G W := by
  first | exact @GlobalTheory.GridJoin.exists_gridPre_spaces | exact GlobalTheory.GridJoin.exists_gridPre_spaces | (intros; apply GlobalTheory.GridJoin.exists_gridPre_spaces <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsThetaFunctionMixedCoordinateBumpMulCore
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.BumpMix

theorem coreA : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (H Z T : HSp D) (ρ : ℕ) (dH : HypDec H Z ρ), Z.rank = 0 → ∀ (v : VolM D T.rank ρ) (β : Mx D T.rank ρ → ℂ), IsBump β → ∃ f, IsThetaFunO ψ H T f ∧ ∀ x, dH.mixS T ψ v.μ v.𝓕 f x 0 = β x := by
  intro D ψ hψ H Z T ρ dH hZ v β hβ
  exact ⟨poinX ψ dH T β, ⟨GlobalTheory.T.poincareSumOverRationalHom_thetaLaw_zeroCore D ψ hψ H Z T ρ dH hZ β, GlobalTheory.T.poincareSumHalfWitt_heisenberg_level_of_zero_core D ψ hψ H Z T ρ dH hZ β hβ,
    GlobalTheory.T.continuous_poincareSumOverRationalHom_bump D ψ hψ H Z T ρ dH β hβ, GlobalTheory.T.contDiff_poincareSumOverRationalHom_realDirections D ψ hψ H Z T ρ dH β hβ⟩, GlobalTheory.T.mixedCoordinate_poincareSum_halfWitt_eq_bump D ψ hψ H Z T ρ dH v β hβ⟩

theorem bump_mul_theta_mixS : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (v : VolM D T.rank ρ) (β : Mx D T.rank ρ → ℂ) (g : WO S₀ T → ℂ), IsBump β → IsThetaFunO ψ S₀ T g → ∃ Φ, IsThetaFunO ψ S T Φ ∧ ∀ x, d.mixS T ψ v.μ v.𝓕 Φ x = β x • g := by
  intro D ψ hψ S S₀ T ρ d v β g hβ hg
  let P : HSp D := Examples₂.posSpace (E := D.host.E) Examples₂.star_isIntegral ρ
  let dH : HypDec (GlobalTheory.Doubling.dblSp P) (GlobalTheory.Core.Rk.SWLaw.zeroSp D) ρ := GlobalTheory.Core.Rk.SWLaw.dblDec P
  have hZ : (GlobalTheory.Core.Rk.SWLaw.zeroSp D).rank = 0 := rfl
  obtain ⟨fH, hfH, hmix⟩ := coreA D ψ hψ _ _ T ρ dH hZ v β hβ
  refine ⟨_, isThetaFunO_prod 1 d.i₀ 1 (GlobalTheory.TowerSurj.embMat d dH) (GlobalTheory.TowerSurj.symplOH_split d dH T hZ) hg hfH,
    fun x => ?_⟩
  funext w₀
  have hz : ∀ z : WO (GlobalTheory.Core.Rk.SWLaw.zeroSp D) T, z = 0 := fun z => Matrix.ext fun _ j => by
    haveI : IsEmpty (Fin (GlobalTheory.Core.Rk.SWLaw.zeroSp D).rank) := by rw [hZ]; infer_instance
    exact isEmptyElim j
  have e2 : ∀ a : Mx D T.rank ρ, sandwich (rat 1) (rat (GlobalTheory.TowerSurj.embMat d dH)) (d.extY T a + d.extX T x + d.ext0 T w₀) =
      dH.extY T a + dH.extX T x + dH.ext0 T 0 := by
    intro a
    have hX : sandwich (rat 1) (rat (GlobalTheory.TowerSurj.embMat d dH)) (d.extY T a + d.extX T x + d.ext0 T w₀) ⬝ dH.jX = x := by
      rw [sandwich_apply, rat_one, Matrix.one_mul, GlobalTheory.TowerSurj.mul_embMat_jX, coord_jX]
    have hY : sandwich (rat 1) (rat (GlobalTheory.TowerSurj.embMat d dH)) (d.extY T a + d.extX T x + d.ext0 T w₀) ⬝ dH.jY = a := by
      rw [sandwich_apply, rat_one, Matrix.one_mul, GlobalTheory.TowerSurj.mul_embMat_jY, coord_jY]
    have h0 := hz (sandwich (rat 1) (rat (GlobalTheory.TowerSurj.embMat d dH)) (d.extY T a + d.extX T x + d.ext0 T w₀) ⬝ dH.j0)
    rw [eq_coords dH (sandwich (rat 1) (rat (GlobalTheory.TowerSurj.embMat d dH)) (d.extY T a + d.extX T x + d.ext0 T w₀)), hX, hY, h0]
    abel
  have e1 : ∀ a : Mx D T.rank ρ, sandwich (rat 1) (rat d.i₀) (d.extY T a + d.extX T x + d.ext0 T w₀) = w₀ := by
    intro a
    rw [sandwich_apply, rat_one, Matrix.one_mul]
    exact witt_extension_sum_mul_middle_coordinate d x a w₀
  have key : ∀ a : Mx D T.rank ρ,
      heisO ψ S T (d.extY T a) (heisO ψ S T (d.extX T x) (heisO ψ S T (d.ext0 T w₀)
        (fun w => g (sandwich (rat 1) (rat d.i₀) w) * fH (sandwich (rat 1) (rat (GlobalTheory.TowerSurj.embMat d dH)) w)))) 0 =
      g w₀ * heisO ψ _ T (dH.extY T a) (heisO ψ _ T (dH.extX T x) (heisO ψ _ T (dH.ext0 T 0) fH)) 0 := by
    intro a
    rw [d.integrandS_eq, dH.integrandS_eq, symplOH_Y_X, symplOH_Y_X]
    show _ * (g _ * fH _) = _
    rw [e1, e2]
    ring
  have h2 : ∫ a in v.𝓕, heisO ψ _ T (dH.extY T a) (heisO ψ _ T (dH.extX T x) (heisO ψ _ T (dH.ext0 T 0) fH)) 0 ∂v.μ =
      β x := hmix x
  show ∫ a in v.𝓕, _ ∂v.μ = β x * g w₀
  rw [show (fun a => heisO ψ S T (d.extY T a) (heisO ψ S T (d.extX T x) (heisO ψ S T (d.ext0 T w₀)
        (fun w => g (sandwich (rat 1) (rat d.i₀) w) * fH (sandwich (rat 1) (rat (GlobalTheory.TowerSurj.embMat d dH)) w)))) 0) =
      fun a => g w₀ * heisO ψ _ T (dH.extY T a) (heisO ψ _ T (dH.extX T x) (heisO ψ _ T (dH.ext0 T 0) fH)) 0 from funext key,
    integral_const_mul, h2, mul_comm]

end GlobalTheory.BumpMix

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteLevelDatumVectorTransformsByLevelCharacterStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteLevelDatumVector_transforms_by_levelCharacter : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) i t σ s P cμ cη m ω BW f₀ f c io, IsLiftDataC R F i t σ s P cμ cη m ω BW f₀ f c io → ∀ k ∈ levG (Wc D i) (R.βW i) (R.datWp i P), ω (1, k) f = levChi (Wc D i) (R.βW i) (R.datWp i P) k • f := by
  first | exact @GlobalTheory.ZetaLaw.zeta_law | exact GlobalTheory.ZetaLaw.zeta_law | (intros; apply GlobalTheory.ZetaLaw.zeta_law <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockPolynomialVectorInjectiveNonzeroVacuumStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockPolynomialVector_injective_nonzeroVacuum : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (B : C.Bas), C.IsB B → ∀ f, C.IsTh f → C.IsFock B f → f ≠ 0 → Function.Injective (C.fvec B f) := by
  first | exact @GlobalTheory.FockPolyInj.fvec_injective | exact GlobalTheory.FockPolyInj.fvec_injective | (intros; apply GlobalTheory.FockPolyInj.fvec_injective <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GoodRowsCompareByLevelMatchingEvaluation
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeEval
section SlopeTestRemainingChoices
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem postOn_eq_of_mem (R : RealDat D A Ks) (F : Face D A) {S : MMap (MP R)} (hS : S ∈ EP R F) :
    postOn (MP R) R.e0 S = S :=
  sub_eq_zero.mp (LinearMap.mem_ker.mp hS.2)

theorem rg_fix (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Gd : GoodOp X) (φ : L2X X) (h2 : star (Gd.Rg (star φ)) = φ) :
    Gd.Rg (star φ) = star φ :=
  calc Gd.Rg (star φ) = star (star (Gd.Rg (star φ))) := (star_star _).symm
    _ = star φ := by rw [h2]

theorem ev_sub (R : RealDat D A Ks) (v₀ : (MP R).Vec) (S S' : MMap (MP R)) (y : GA D (Yc D 0)) :
    ev (MP R) v₀ (S - S') y = ev (MP R) v₀ S y - ev (MP R) v₀ S' y := by
  simp [ev_apply]
  rfl

end SlopeTestRemainingChoices

theorem evalTieT_of_levelMatch : GlobalTheory.Published.DiscreteSeriesClassification → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → HostHyp D → (∀ x : X.B.I.E, HEq (X.ιE x) x) → ∀ (Gd : GoodOp X) (t : GA D (Yc D 0)), t ∈ GfC (Yc D 0) → ConjLevel (t)⁻¹ (levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) ((iotaX X h).toMulEquiv ⁻¹' {x : X.B.I.GA | x.1 = 1 ∧ x.2 ∈ X.K2}) (fun k => star (X.chi2 ((iotaX X h).toMulEquiv k).2)) → RowLevelMatchAt R F X h t → ∃ c' : ℝ, EvalTieT (R.MY 0) R.ν0 R.fd0 (R.EEat (R.levR F true)) X Gd (iotaX X h).toMulEquiv t c' := by
  intro hDS D G _ _ Pl0 T A Ks _ _ _ R F X h hLev hGrp hMod hHost hE Gd t ht hConj hRow
  obtain ⟨c, hc, hsm⟩ := GlobalTheory.T.exists_linearIsometryEquiv_intertwining_modelRep hDS R F X h hLev hGrp hMod hHost hE
  let v₀ : (MP R).Vec := fun τ => ⟨(c τ).symm (X.B.w (X.pl.symm τ)), hsm τ⟩
  have hv₀ : ∀ τ, c τ (v₀ τ : (MP R).H τ) = X.B.w (X.pl.symm τ) := fun τ => by
    simp [v₀]
  have hnorm : ∀ τ, ‖(v₀ τ : (MP R).H τ)‖ = 1 := fun τ => by
    show ‖(c τ).symm (X.B.w (X.pl.symm τ))‖ = 1
    rw [LinearIsometryEquiv.norm_map]
    exact (X.low _).1
  have hne : ∀ τ, (v₀ τ : (MP R).H τ) ≠ 0 := fun τ h0 => by
    have := hnorm τ
    rw [h0, norm_zero] at this
    exact zero_ne_one this
  obtain ⟨σ, red, hA, -, -⟩ := id hRow
  obtain ⟨c0, hc0, hN⟩ := GlobalTheory.T.translatedRowEvaluation_squareIntegrable_norm R F X h hLev hGrp hMod t ht
  refine ⟨c0, Formalism.IndefR.AutomorphicEvaluation.evalTieT_of _ _ _ _ X Gd _ t c0 v₀ hnorm ?_ ?_ ?_⟩
  · intro S hS
    obtain ⟨hmem, hint, -⟩ := hN v₀ hnorm S hS
    have hHH := GlobalTheory.T.conj_rowEvaluation_translate_mem_rowSpace R F X h hLev hGrp hMod hHost hE t c v₀ ht hA hc hv₀ S hS _ hmem.coeFn_toLp
    have h1 := GlobalTheory.T.goodOp_star_translatedEval_eq_goodProjector R F X h hLev hGrp hMod Gd t v₀ hRow S hS.1 _ hmem.coeFn_toLp
    rw [postOn_eq_of_mem R F hS] at h1
    have hfix : Gd.Rg (star (hmem.toLp _)) = star (hmem.toLp _) :=
      rg_fix X Gd _ (Lp.ext (h1.trans hmem.coeFn_toLp.symm))
    refine ⟨⟨hmem.toLp _, Submodule.mem_inf.mpr ⟨hHH, LinearMap.mem_ker.mpr (sub_eq_zero.mpr hfix)⟩⟩,
      hmem.coeFn_toLp, ?_⟩
    show ‖(hmem.toLp _ : L2X X)‖ ^ 2 = _
    rw [Formalism.IndefR.AutomorphicEvaluation.norm_sq_toLp hmem]
    exact hint
  · intro Φ
    have hF : star (Φ : L2X X) ∈ goodSub X Gd := Φ.2
    have hfix : Gd.Rg (star (Φ : L2X X)) = star (Φ : L2X X) :=
      sub_eq_zero.mp (LinearMap.mem_ker.mp (Submodule.mem_inf.mp hF).2)
    obtain ⟨S, hSM, hSF⟩ := GlobalTheory.T.conjRow_eq_translatedEvaluation_cuspFormMap hDS R F X h hLev hGrp hMod hHost hE t c v₀ ht hConj hc hv₀ (Φ : L2X X)
      (Submodule.mem_inf.mp hF).1
    have h1 := GlobalTheory.T.goodOp_star_translatedEval_eq_goodProjector R F X h hLev hGrp hMod Gd t v₀ hRow S hSM _ hSF
    rw [hfix, star_star] at h1
    have hz := GlobalTheory.T.multiplicityMap_eq_zero_of_translated_evaluation_ae_zero R F X h hLev hGrp hMod t v₀ hne S hSM _ rfl (by
      filter_upwards [h1, hSF] with x h1x h2x
      refine (ev_sub R v₀ _ _ _).trans ?_
      exact sub_eq_zero.mpr (h1x.symm.trans h2x))
    exact ⟨S, ⟨hSM, LinearMap.mem_ker.mpr hz⟩, hSF⟩
  · intro S hS h0
    obtain ⟨-, hint, hzero⟩ := hN v₀ hnorm S hS
    have hI : ∫ x, ‖(fun x => ev (MP R) v₀ S (@HMul.hMul (GA D (Yc D 0)) (GA D (Yc D 0)) (GA D (Yc D 0)) _ ((iotaX X h).symm x) t)) x‖ ^ 2 ∂(muX X) = 0 := by
      refine (integral_congr_ae ?_).trans (integral_zero _ _)
      filter_upwards [h0] with x hx
      have : ev (MP R) v₀ S (@HMul.hMul (GA D (Yc D 0)) (GA D (Yc D 0)) (GA D (Yc D 0)) _ ((iotaX X h).symm x) t) = 0 := hx
      simp [this]
    rw [hI] at hint
    have hre : (ipM (MP R) R.ν0 R.fd0 S S).re = 0 := by
      rcases mul_eq_zero.mp hint.symm with h' | h'
      · exact absurd h' hc0.ne'
      · exact h'
    exact hzero hre

end GlobalTheory.SeeEval
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeUniversalIsogenyOnFibresPreservesOriginStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeUniversalIsogenyOnFibres_preserves_origin : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (P : Ideal (𝓞 E)) (p i : ℕ) (Z : Corr Xo P p i) (T : Type) [CommRing T] (h : Sp T ⟶ Z.Hk) (x x' : Sp T ⟶ Xo.X) (hx : x = h ≫ Z.π₁) (hx' : x' = h ≫ Z.π₂), (ptSecT Xo.univ.t.G (1 : Over.mk x ⟶ Xo.univ.t.G)).left ≫ hkMap Z hx hx' = (ptSecT Xo.univ.t.G (1 : Over.mk x' ⟶ Xo.univ.t.G)).left := by
  first | exact @GlobalTheory.HeckeEx.hkMap_ptSec_one | exact GlobalTheory.HeckeEx.hkMap_ptSec_one | (intros; apply GlobalTheory.HeckeEx.hkMap_ptSec_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentSumScalarSmulMemCompletedModulusStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idempotentSum_scalar_smul_mem_completedModulus : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) {m n : ℕ} (M : Submodule (𝓞 D.host.E) (Matrix (Fin m) (Fin n) D.host.E)) (e : AE D), IsIdemSum e G.pl.W0 → ∀ α ∈ intAf D.host.F, ∀ b : D.host.E, (∀ w ∈ G.pl.W0, Valued.v (algebraMap D.host.E (Kw w) b) ≤ WithZero.exp (-(cosExp G w : ℤ))) → ∀ g ∈ M, e • (Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F] (b * g i j) : Mx D m n) ∈ hatMx (G.modul • M) := by
  first | exact @GlobalTheory.HalfScalarHat.idemSum_smul_mem_hatMx | exact GlobalTheory.HalfScalarHat.idemSum_smul_mem_hatMx | (intros; apply GlobalTheory.HalfScalarHat.idemSum_smul_mem_hatMx <;> assumption)
end

