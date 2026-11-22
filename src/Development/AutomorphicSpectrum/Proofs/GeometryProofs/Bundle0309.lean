import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArithVarietyModelPrimeHeight
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsLatFamilyCongr
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0007
import Development.AutomorphicSpectrum.ParallelStatements.ParallelGeometry.CuspMeanBound
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0308
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0261
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0029
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0063
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0003
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0067
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0033
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0076
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGeneratedEffectiveSection
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0111
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0064
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0077
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0036
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0016
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0017
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSegreDimGe
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0019
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0033
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0015
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSheetCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0039
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0171
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0208
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0251
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.ThreeLeLevel
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0009
import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0141
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0252
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0198
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0242
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0206
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0005
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import GroundTheory.HeightsAndTheta.Heights.Regularisation.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0004
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0010
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0002
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0003
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpSt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.NumberField
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.LocalAtPlaces
import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExists
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0201
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0192
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0196
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0205
import Development.AutomorphicSpectrum.Statements.GeometryStatements.KeyBadSt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsThetaMeanSquareNorm
import Development.AutomorphicSpectrum.Statements.GeometryStatements.ZhangDimensionPushDownGrassmannianHeightBounds
import GroundTheory.HeightsAndTheta.Heights.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsBundles
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0105
import Development.WeilBound.CoreStatements.HodgeTatePoints.QacInt

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArithVarietyModelPrimeHeightStatement
section
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arith_variety_model_prime_height : GlobalTheory.CompanionTheory.Ar.HT.FarguesHodgeTate → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → 0 < D.p + D.q → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → HT.HTFree 𝔐 p → p ≠ 2 → ¬ (p : ℤ) ∣ NumberField.discr E → ∀ (b : ∀ t, Fin (labelRk D t) → 𝔐.Li), (∀ t, LinearIndependent Ω (b t) ∧ Submodule.span Ω (Set.range (b t)) = 𝔐.Vgen t) → ∀ φ : Equiv.Perm (CMType H ⊕ CMType H), IsFrobLabels c p φ → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω], ∀ (t₀ : CMType H ⊕ CMType H) (Sg : Type) [Fintype Sg] (e : Sg → CMType H ⊕ CMType H) (φ' : Equiv.Perm Sg) (F : Type) [Field F] [Fintype F] [CharP F p] (pq : (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)}) →+* F) (sc : F →+ (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)})) (w : O) (σ : Sg → F →+* IsLocalRing.ResidueField O), IsOrbit O 𝔐 p φ t₀ e φ' pq w σ → IsSec pq sc → ∀ (G : GenTors 𝔐 p) (P : ∀ c' : ∀ k, J k, mseg y c' ≠ 0 → ChartPack G O c') (i : ∀ (c' : ∀ k, J k) (τ), (Fin (labelRk D (e τ)) → Ω) →ₗ[Ω] (Fin (D.p + D.q) → Ω)), (∀ (c' : ∀ k, J k) (h : mseg y c' ≠ 0) (τ : Sg), SeqHyp (CR O y c') (algebraMap O Ω w) (coordLat O y (𝔐.HT p (e τ)) (b (e τ)) c') (dotDual (CR O y c') (coordLat O y (𝔐.HT p (e τ).swap) (b (e τ).swap) c')) (i c' τ) (qMap (P c' h) (b (e τ).swap)) ∧ ∀ σE : E →+* Ω, (∀ a : 𝓞 E, σE (a : E) = 𝔐.emb (e τ) a) → DualSeq (P c' h) σE (𝔐.R p - 2) (coordLat O y (𝔐.HT p (e τ)) (b (e τ)) c') (b (e τ)) (i c' τ)) → ∀ τ : Sg, IsLatFamily O y (fun c' => (famD e b pq sc w P i c').Gam τ) ∧ IsLatFamily O y (fun c' => (famD e b pq sc w P i c').Del τ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.FamEx.SeqFam.seqfam_holds | exact GlobalTheory.CompanionTheory.Ar.Num.FamEx.SeqFam.seqfam_holds | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.FamEx.SeqFam.seqfam_holds <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CuspClausesOfNineGeoU
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.NineEq

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel GlobalTheory.CompanionTheory.Ar.Small
open GroundTheory.Heights₂.Heights.LowerBoundFree (AmpleOnGenericFibre)

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

section Field

variable {F : Type} [Field F]

def EffOn (V : Ideal (MRingOver F ι)) (β : K → ℤ) : Prop :=
  ∀ W : Ideal (MRingOver F ι), IsMultiProjPrime W → V ≤ W →
    ∃ f g, IsRatSection W β f g ∧ ∀ W', 0 ≤ ratDiv W f g W'

end Field

variable {Ω : Type} [Field Ω]

open Classical in

abbrev numQ : IFamily ℚ ι := fun V _ L => NumbersDVR.intNum ℚ V L

theorem geomDeg_eq (hD : DegreeStatement) {W : Ideal (MRing ι)} {d : ℕ} (hW : IsArithVar W (d + 1))
    {A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} (hA : IsSmoothHerm A) : geomDeg W A d = genDeg W d A.a := by
  classical
  have h := GlobalTheory.CompanionTheory.Ar.Giv.degreeGeneric_of_degree hD K ι W d (fun _ => A) hW (fun _ => hA)
  have hpot : pot (fun _ : Fin d => A) = fun (_ : Fin d) z => Real.log (A.h z) := rfl
  rw [hpot] at h
  unfold geomDeg genDeg
  rw [h]

section Values

variable {y : (Σ k, ι k) → Ω} {L : Type} [Field L] {z : (Σ k, ι k) → L} {c : ∀ k, ι k}

def ChartVal (y : (Σ k, ι k) → Ω) (z : (Σ k, ι k) → L) (c : ∀ k, ι k) (s : Ω) (v : L) : Prop :=
  ∃ (e : K → ℕ) (G : MRing ι), IsMultiHomog G e ∧ aeval y G = s * aeval y (GenOnFibres.cmon c e) ∧
    aeval z G = v * aeval z (GenOnFibres.cmon c e)

theorem ChartVal.add {s s' : Ω} {v v' : L} (h : ChartVal y z c s v) (h' : ChartVal y z c s' v') :
    ChartVal y z c (s + s') (v + v') := by
  obtain ⟨e, G, hG, h1, h2⟩ := h
  obtain ⟨e', G', hG', h1', h2'⟩ := h'
  refine ⟨e + e', G * GenOnFibres.cmon c e' + GenOnFibres.cmon c e * G',
    GenOnFibres.homog_add (GenOnFibres.homog_mul hG (GenOnFibres.homog_cmon c e'))
      (GenOnFibres.homog_mul (GenOnFibres.homog_cmon c e) hG'), ?_, ?_⟩
  · simp only [GenOnFibres.cmon_add, map_add, map_mul, h1, h1']; ring
  · simp only [GenOnFibres.cmon_add, map_add, map_mul, h2, h2']; ring

theorem ChartVal.mul {s s' : Ω} {v v' : L} (h : ChartVal y z c s v) (h' : ChartVal y z c s' v') :
    ChartVal y z c (s * s') (v * v') := by
  obtain ⟨e, G, hG, h1, h2⟩ := h
  obtain ⟨e', G', hG', h1', h2'⟩ := h'
  refine ⟨e + e', G * G', GenOnFibres.homog_mul hG hG', ?_, ?_⟩
  · simp only [GenOnFibres.cmon_add, map_mul, h1, h1']; ring
  · simp only [GenOnFibres.cmon_add, map_mul, h2, h2']; ring

end Values

end GlobalTheory.CompanionTheory.Ar.Cusp.NineEq

end

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.NineEq

open NumberField Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.IndefiniteRowSideFullHecke.CuspMeanBound

section Systems

open ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4

end Systems

section Clauses

variable {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]
  {Ω : Type} [Field Ω] [Algebra ℚ Ω] {W : Ψ → Type} [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)]
  {Dc : ComponentData II Ψ K J Ω W} (Hd : HodgeData Dc)

variable {w : ((Σ k, J k) → ℂ) → ℝ} {M : XModel Dc} (S : BoundedRegularisationSetting M Dc.Xo Hd.aMu w)

end Clauses

def FrameFamilyExists : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H)
    (Xo : ∀ l : Level H, Moduli D l) (l : Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F))
    (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω]
    [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)]
    (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (B₁ : ℕ)
    (U : ((Σ k, J k) → ℂ) → ℝ),
    IsFullIntersectionSystem II → admitted Xo l c Y Or B₁ → Or.𝔐.IsCuspWeight Or.sm U → 1 ≤ Dc.j' → 3 * Dc.j' + 1 ≤ Dc.N →
      ∃ (M : XModel Dc) (S' : BoundedRegularisationSetting M Dc.Xo Hd.aMu (corrW Hd U)), S'.IsTied

end GlobalTheory.CompanionTheory.Ar.Cusp.NineEq
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CuspVolumeSum
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp MeasureTheory

namespace GlobalTheory.CompanionTheory.Ar.Cusp

namespace TopMean

theorem bracket_le (f j' B : ℕ) (rd L : ℝ) (hrd : 2 ≤ rd) (hf : 1 ≤ f) (hj : 1 ≤ j')
    (hB : 2 * f * j' ≤ B) (hB64 : 64 ≤ B) :
    6 + Real.log (2 * (f : ℝ) * rd) + Real.log (2 * (f : ℝ) * j' * rd) ≤
      4 * (Real.log ((B : ℝ) * rd) + |L|) := by
  have hf' : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have hj' : (1 : ℝ) ≤ j' := by exact_mod_cast hj
  have hB' : 2 * (f : ℝ) * j' ≤ B := by exact_mod_cast hB
  have hB64' : (64 : ℝ) ≤ B := by exact_mod_cast hB64
  have hrd0 : 0 < rd := by linarith
  have h1 : Real.log (2 * (f : ℝ) * rd) ≤ Real.log ((B : ℝ) * rd) := by
    apply Real.log_le_log (by positivity)
    apply mul_le_mul_of_nonneg_right _ hrd0.le
    nlinarith
  have h2 : Real.log (2 * (f : ℝ) * j' * rd) ≤ Real.log ((B : ℝ) * rd) := by
    apply Real.log_le_log (by positivity)
    exact mul_le_mul_of_nonneg_right hB' hrd0.le
  have h3 : 3 ≤ Real.log ((B : ℝ) * rd) := by
    have h128 : (128 : ℝ) ≤ (B : ℝ) * rd := by nlinarith
    have hl : Real.log (128 : ℝ) = 7 * Real.log 2 := by
      rw [show (128 : ℝ) = 2 ^ 7 by norm_num, Real.log_pow]; norm_num
    have := Real.log_le_log (by norm_num) h128
    have := Real.log_two_gt_d9
    linarith
  have := abs_nonneg L
  linarith

end TopMean

open TopMean in

theorem top_mean_cusp_weight : Top.Given → ∃ Cu : ℝ, ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (B₁ : ℕ) (U : ((Σ k, J k) → ℂ) → ℝ), IsFullIntersectionSystem II → admitted Xo l c Y Or B₁ → Or.𝔐.IsCuspWeight Or.sm U → MeanU Hd U Cu (hostRd E) (hostLval H) := by
  intro hG
  refine ⟨4, ?_⟩
  intro E _ _ _ _ H D Xo l c Y II K _ J _ Ω _ _ W _ _ Dc Hd S₀ Or B₁ U _ _ hU
  obtain ⟨Q⟩ := GlobalTheory.T.cusp_volume_left hG E H D Xo l c Y II K J Ω W Dc Hd S₀ Or
  obtain ⟨κ, hκ, htr⟩ := GlobalTheory.T.ptsIntegral_eq_sum_ballDens_integrals E H D Xo l c Y II K J Ω W Dc Hd S₀ Or Q
  have hw := GlobalTheory.T.cusp_volume_middle E H D Xo l c Y II K J Ω W Dc Hd S₀ Or Q U hU
  obtain ⟨hrd, ⟨τ₀⟩, -⟩ := GlobalTheory.CompanionTheory.Ar.Top.HostNumbers.host_numbers E H
  intro hj' hN B hB
  have hjN : Dc.j + Dc.j' = Dc.N := by
    have := Dc.j_le; have := Dc.two_le_N
    show Dc.j + (Dc.N - Dc.j) = Dc.N
    omega
  have hball := fun k => GlobalTheory.T.cusp_weight_integrable_on_fundamental_set E (CMType H) Dc.j Dc.j' Dc.n Q.g (Q.Λ k) H (Q.F k) (Q.Γ k) (Q.FF k)
    (Q.arith k) (Q.fund k) hj' (by omega)
  set C : ℝ := (Fintype.card (CMType H) : ℝ) * Dc.j' * (6 + Real.log (2 * Fintype.card (CMType H) * hostRd E) +
    Real.log (2 * Fintype.card (CMType H) * Dc.j' * hostRd E)) with hC
  have hdeg : GroundTheory.Heights₂.Heights.LowerBoundFree.degMu Hd =
      κ * ∑ k, (Q.d k : ℝ) * ∫ t in Q.FF k, ballDens (Q.F k).q t := by
    have e1 : GroundTheory.Heights₂.Heights.LowerBoundFree.degMu Hd =
        ptsIntegral (e := Dc.n) (mCoordIdeal Dc.y) (fun _ => phMu Hd) (fun _ => 1) := rfl
    rw [e1, htr (fun _ => 1) (fun _ _ => 1) (fun _ _ _ _ => rfl) (fun _ _ _ => rfl)
      (fun k => by simpa using (hball k).1)]
    refine congrArg (κ * ·) (Finset.sum_congr rfl fun k _ => ?_)
    simp
  have hnum : ptsIntegral (e := Dc.n) (mCoordIdeal Dc.y) (fun _ => phMu Hd) U =
      κ * ∑ k, (Q.d k : ℝ) * ∫ t in Q.FF k, ((Q.F k).R t).cuspW (Q.F k).σ * ballDens (Q.F k).q t :=
    htr U (fun k t => ((Q.F k).R t).cuspW (Q.F k).σ) hw.1 hw.2 (fun k => (hball k).2.2.1)
  have hle : ∀ k, (Q.d k : ℝ) * (∫ t in Q.FF k, ((Q.F k).R t).cuspW (Q.F k).σ * ballDens (Q.F k).q t) ≤
      C * ((Q.d k : ℝ) * ∫ t in Q.FF k, ballDens (Q.F k).q t) := fun k => by
    have h := mul_le_mul_of_nonneg_left (hball k).2.2.2 (Nat.cast_nonneg (α := ℝ) (Q.d k))
    calc _ ≤ _ := h
      _ = _ := by rw [hC]; ring
  have hDpos : 0 < GroundTheory.Heights₂.Heights.LowerBoundFree.degMu Hd := by
    rw [hdeg]
    apply mul_pos hκ
    obtain ⟨k0, hk0⟩ := Q.d_pos
    exact Finset.sum_pos' (fun k _ => mul_nonneg (Nat.cast_nonneg _) (hball k).2.1.le)
      ⟨k0, Finset.mem_univ _, mul_pos (by exact_mod_cast hk0) (hball k0).2.1⟩
  have hmean : meanOf Hd U ≤ C := by
    unfold meanOf
    rw [div_le_iff₀ hDpos, hnum]
    calc κ * ∑ k, (Q.d k : ℝ) * (∫ t in Q.FF k, ((Q.F k).R t).cuspW (Q.F k).σ * ballDens (Q.F k).q t)
        ≤ κ * ∑ k, C * ((Q.d k : ℝ) * ∫ t in Q.FF k, ballDens (Q.F k).q t) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k _ => hle k) hκ.le
      _ = C * GroundTheory.Heights₂.Heights.LowerBoundFree.degMu Hd := by
          rw [hdeg, ← Finset.mul_sum]; ring
  have hf : 1 ≤ Fintype.card (CMType H) := Fintype.card_pos_iff.mpr ⟨τ₀⟩
  have hfD : Dc.f = Fintype.card (CMType H) := rfl
  have hN4 : 4 ≤ Dc.N := by omega
  have hB64 : 64 ≤ B := by
    have : 4 * 1 * 4 ^ 2 ≤ 4 * Dc.f * Dc.N ^ 2 := by
      rw [hfD]; gcongr
    omega
  have hB2 : 2 * Fintype.card (CMType H) * Dc.j' ≤ B := by
    have hjN' : Dc.j' ≤ Dc.N ^ 2 := le_trans (by omega) (Nat.le_self_pow (by norm_num) _)
    have : 2 * Fintype.card (CMType H) * Dc.j' ≤ 4 * Dc.f * Dc.N ^ 2 := by
      rw [hfD]
      calc 2 * Fintype.card (CMType H) * Dc.j' ≤ 4 * Fintype.card (CMType H) * Dc.N ^ 2 := by
            have := Nat.mul_le_mul_left (4 * Fintype.card (CMType H)) hjN'
            nlinarith
        _ = _ := rfl
    omega
  have hbr := bracket_le (Fintype.card (CMType H)) Dc.j' B (hostRd E) (hostLval H) hrd hf hj' hB2 hB64
  have hfj : (0 : ℝ) ≤ (Fintype.card (CMType H) : ℝ) * Dc.j' := by positivity
  calc meanOf Hd U ≤ C := hmean
    _ ≤ (Fintype.card (CMType H) : ℝ) * Dc.j' * (4 * (Real.log ((B : ℝ) * hostRd E) + |hostLval H|)) := by
        rw [hC]; exact mul_le_mul_of_nonneg_left hbr hfj
    _ = 4 * Dc.f * Dc.j' * abelian₂ B (hostRd E) (hostLval H) := by
        rw [hfD, GroundTheory.Heights₂.Heights.LowerBoundFree.abelian₂]; ring

end GlobalTheory.CompanionTheory.Ar.Cusp
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlatZeroFromResolutionAndGaga
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.A0

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat

theorem exists_typeFn {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (p q : ℕ) :
    ∃ (g : ℕ) (ty : Fin g → (E →+* ℂ)), IsTypeFn H p q ty := by
  classical
  let m : (E →+* ℂ) → ℕ := fun τ => if τ (H.rt : E) = H.rt0 then p else q
  let e := (Fintype.equivFin (Σ τ : E →+* ℂ, Fin (m τ))).symm
  have h : ∀ τ, Nat.card {i // (e i).1 = τ} = m τ := fun τ => by
    rw [Nat.card_congr ((e.subtypeEquiv (q := fun x => x.1 = τ) fun _ => Iff.rfl).trans
      (Equiv.sigmaSubtype τ))]
    simp
  exact ⟨_, fun i => (e i).1, fun τ => ⟨fun hτ => by rw [h]; simp [m, hτ], fun hτ => by rw [h]; simp [m, hτ]⟩⟩

theorem exists_basis_of_isVBOn {X : Scheme.{0}} {Ω : Type} [Field Ω] {V : Type} [AddCommGroup V] [Module Ω V]
    {ξ : Spec (CommRingCat.of Ω) ⟶ X} {L : Lat ξ V} {T : Set (Cpt ξ)} {r : ℕ} {S : Submodule Ω V}
    (h : L.IsVBOn T r S) (hT : T.Nonempty) :
    ∃ b : Fin r → V, LinearIndependent Ω b ∧ Submodule.span Ω (Set.range b) = S := by
  obtain ⟨p, hp⟩ := hT
  obtain ⟨U, hU, b, hb, hf⟩ := h p hp
  exact ⟨b, (hf p hp hU).1, hb⟩

theorem flat_zero_of_resolution_gaga (hres : Geo.ResK.ResKStatement) (hgaga : GagaSections) : FlatLineGenerator := by
  intro E _ _ _ H D l Xo c O _ β Y U Z τ hO hpq hτ hZ
  let σ : c.F →+* ℂ := c.F.val.toRingHom
  obtain ⟨g, ty, hty⟩ := exists_typeFn H D.p D.q
  have hσρ : (σ.comp (IntermediateField.inclusion c.le).toRingHom) (baseKA l).ρ = H.rt0 := rfl
  obtain ⟨FU⟩ := GlobalTheory.familyUnif_of_laws GlobalTheory.abelianSchemeLaws_all.1 E H D l Xo
    (σ.comp (IntermediateField.inclusion c.le).toRingHom) g ty hpq hσρ hty
  have hστ : ∀ a : 𝓞 E, σ (tauIn c τ a) = τ (a : E) := fun a => rfl
  obtain ⟨Φ, hΦ, -⟩ := GlobalTheory.T.exists_unit_analytic_function E H D l Xo c τ τ σ g ty FU hty hτ hστ
  obtain ⟨h1, h2, -, hne⟩ := GlobalTheory.T.eigen_lattice_vector_bundle E H D l Xo c O β Y U Z τ hO hτ
  obtain ⟨b₁, hb₁, hs₁⟩ := exists_basis_of_isVBOn h1 hne
  obtain ⟨b₂, hb₂, hs₂⟩ := exists_basis_of_isVBOn h2 hne
  have hσrt : σ (tauIn c τ H.rt) = H.rt0 := (hστ H.rt).trans hτ
  obtain ⟨f, κ, W, -, -, hgen, -⟩ := GlobalTheory.T.eigen_frames_analytic hres hgaga E H D l Xo c O β Y U Z τ σ Φ b₁ b₂ hO hpq hτ hσrt hZ
    hΦ hb₁ hs₁ hb₂ hs₂
  obtain ⟨φ, hφ, hrep⟩ := GlobalTheory.T.wedge_eigen_line_generator E H D l Xo c O β Y U Z τ _ _ hO hτ hgen
  exact ⟨φ, hφ, FlatOnModel.of_gen hφ hgen hrep, fun φ' h1' h2' =>
    GlobalTheory.T.frame_functions_flat_agree E H D l Xo c O β Y U Z τ φ φ' hO hτ hZ hφ (FlatOnModel.of_gen hφ hgen hrep) h1' h2'⟩

end GlobalTheory.CompanionTheory.Ar.Flat.A0
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GoodOriginIntersectionRelayStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)
open ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.good_origin_intersection_relay : PB.AgreementPos → PB.Proportional → Cmp.CmpSt → Top.Given → PtsIntegrableStatement → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : Top.RootTower (CMType H) (D.p + D.q)) (o : Top.GoodOrigin Y T) (II : IntersectionSystem), Top.IsGlobal Xo l c Y → o.Extra → IsFullIntersectionSystem II → 1 ≤ D.p → 1 ≤ D.q → ∀ (B B₁ : ℕ) (a : T.Comp) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (O Lt : Type) [CommRing O] [AddCommGroup Lt] [Module O Lt] (X : ComponentSetting Dc O Lt) (Or : CptOrigin Y T.bad Dc X.H), 2 ≤ B → B ≤ B₁ → D.q ≤ D.p → Or.bg = Sum.inl → Or.sm = Sum.inr → Or.Good → genPt Or.𝔐.ξ₀ = genPt (o.Fx a).ξf → (∀ r : ℕ, r ∈ Dc.S ↔ r.Prime ∧ r ≤ B₁ ∧ r ∉ T.bad) → ∃ (K₃ : Type) (_ : Fintype K₃) (ι₃ : K₃ → Type) (_ : ∀ k, Fintype (ι₃ k)) (κ : K → K₃) (v : (Σ k, J k) → Σ k, ι₃ k) (P₃ : Ideal (MRing ι₃)) (e r : ℕ) (cf : Fin r → ℝ) (Mt : ℝ → HermLine ι₃) (Nt : ℝ → Fin r → Fin e → HermLine ι₃) (δ : ℝ), IsBlockMap κ v ∧ IsArithVar P₃ (Dc.n + 1 + e) ∧ imageZ v P₃ = mCoordIdeal Dc.y ∧ 0 < δ ∧ (∀ t m i, (Nt t m i).a = (Nt 1 m i).a) ∧ (∀ t m i, IsSmoothHerm (Nt t m i)) ∧ (∀ᶠ t in 𝓝[>] (0 : ℝ), IsPullHerm κ v (muReg X.H X.S B t) (Mt t)) ∧ Tendsto (fun t => ∑ m, cf m * II K₃ ι₃ P₃ (Dc.n + 1 + e) (Fin.append (fun _ : Fin (Dc.n + 1) => Mt t) (Nt t m))) (𝓝[>] 0) (𝓝 (δ * T.PPc II B a (Top.testPoly T.j))) ∧ ∀ᶠ t in 𝓝[>] (0 : ℝ), ∑ m, cf m * ptsIntegral (e := Dc.n + e) P₃ (fun i z => Real.log ((Fin.append (fun _ : Fin Dc.n => Mt t) (Nt 1 m) i).h z)) (fun _ => 1) = δ * (T.M B a).geoFun (Top.toA (Top.muSmall T.j ^ Top.dimX (CMType H) (D.p + D.q) T.j * Top.fibClass T.j : Top.RP (CMType H) (D.p + D.q))) := by
  first | exact @GlobalTheory.CompanionTheory.Relay.good_origin_intersection_relay | exact GlobalTheory.CompanionTheory.Relay.good_origin_intersection_relay | (intros; apply GlobalTheory.CompanionTheory.Relay.good_origin_intersection_relay <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCompCoverCmSigns
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.hodge_comp_cover_cm_signs : Top.Given → Out.WeilSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (dg : ℕ) (sm : CMType H → CMType H ⊕ CMType H) (m : ℕ) (s : CMType H → Fin m → 𝔐.Li) (a : K → ℤ) (e₀ : Ω), Top.IsGlobal Xo l c Y → 1 ≤ D.p → 1 ≤ D.q → 𝔐.IsCover dg → (∀ p ∈ S, HT.HTFree 𝔐 p) → (∀ p : ℕ, p.Prime → p ∉ S → ¬ (p : ℤ) ∣ discr E ∧ 4 * Fintype.card (CMType H) + 2 ≤ p ∧ 2 < p) → (sm = Sum.inl ∨ sm = Sum.inr) → (∀ τ, LinearIndependent Ω (s τ) ∧ Submodule.span Ω (Set.range (s τ)) = 𝔐.Vgen (sm τ)) → (Lat.tens (fun τ => detLat (𝔐.V (sm τ)) (s τ)) (fun _ => -1)).IsDegOn Set.univ y a e₀ → NefOnFibres (mCoordIdeal y) a := by
  intro hG hW E _ _ _ H D Xo l c Y S Ω _ _ K _ J _ y 𝔐 dg sm m s a e₀ hY hp hq hcov hS hS' hsm hs hdeg
  have hI : PB.Inputs := hG.2.2.2.2.2.2.2.2.2.1
  obtain ⟨M, 𝔐', Fl, e, i, g, bk, bx, j, hbk, hy, hd, hS2, hR, hj, hli, hV⟩ :=
    GlobalTheory.T.hodge_comp_cover_primes hW E H D Xo l c Y S Ω K J y 𝔐 dg hcov
      (fun p hp hdv => by by_contra h; exact (hS' p hp h).1 hdv) hS
  haveI : CharZero M.Ω := charZero_of_injective_ringHom i.injective
  obtain ⟨n1, n2⟩ := GlobalTheory.T.nefOnFibres_block_xdeg_sums_of_rootLines hG E H D Xo l c Y S M 𝔐' Fl e hY hp hq hS2 hS' hR
  have hb₀ : ∀ σ, LinearIndependent M.Ω (Fl.b σ) := by
    obtain ⟨_, _, -, -, -, h, -⟩ := Fl.generic
    exact h
  have hu := fun τ => GlobalTheory.CompanionTheory.Ar.Cusp.DetNef.det_pull (L := 𝔐.V (sm τ)) hd hj hli (hs τ).1 (hs τ).2 (𝔐.vb (sm τ)) (hb₀ (sm τ))
    (by rw [← hV]; exact Fl.sub (sm τ))
  choose u hu0 hu using hu
  let a' : M.K → ℤ := Function.extend bk a 0
  have ha : ∀ k, a' (bk k) = a k := fun k => hbk.extend_apply _ _ k
  have ha' : ∀ k', k' ∉ Set.range bk → a' k' = 0 := fun k' h => Function.extend_apply' _ _ _ h
  have hB := GlobalTheory.CompanionTheory.Ar.Cusp.DetNef.deg_pull hu0 hd 𝔐.tie.cover hu hbk hy ha ha' hdeg
  simp only [← hV] at hB
  have hgr : ∀ (r : CMType H × Fin (D.p + D.q)) (σ : Σ s, Fin (labelRk D s)), HodgeCpt.rootIdx D r = σ →
      ((𝔐'.V σ.1).gr (Fl.b σ.1) σ.2).IsDegOn Set.univ M.y (HodgeCpt.rootSgn D r • M.xdeg r)
        (e r ^ HodgeCpt.rootSgn D r) := by
    rintro r _ rfl
    refine GlobalTheory.CompanionTheory.Ar.Cusp.DetNef.deg_untens ?_ (hR r)
    unfold HodgeCpt.rootSgn
    split_ifs <;> norm_num
  have hA : ∃ A e₁, (Lat.tens (fun τ => detLat (𝔐'.V (sm τ)) (Fl.b (sm τ))) fun _ => -1).IsDegOn Set.univ M.y A e₁ ∧
      NefOnFibres (mCoordIdeal M.y) A := by
    have hdet : ∀ σ, detLat (𝔐'.V σ) (Fl.b σ) = Lat.tens (fun k => (𝔐'.V σ).gr (Fl.b σ) k) fun _ => 1 := fun σ =>
      GlobalTheory.CompanionTheory.Relay.det_lattice_flag_tensor _ _ _ _ _ _ _ (hb₀ σ) (Fl.sub σ)
    simp only [hdet]
    rcases hsm with rfl | rfl
    · have h1 : ∀ τ (k : Fin D.p), HodgeCpt.rootIdx D (τ, Fin.castAdd D.q k) = ⟨.inl τ, k⟩ := fun τ k => by
        unfold HodgeCpt.rootIdx
        rw [dif_pos (show ((Fin.castAdd D.q k : Fin _) : ℕ) < D.p from k.2)]
        rfl
      refine ⟨_, _, Lat.tens_isDegOn _ _ _ _ _ _ _ _ _ _ _ (fun τ => Lat.tens_isDegOn _ _ _ _ _ _ _ _ _ _ _
        (fun k => hgr _ _ (h1 τ k)) _) _, ?_⟩
      convert n2 using 1
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun τ _ => ?_
      rw [Finset.sum_filter, Fin.sum_univ_add]
      simp [HodgeCpt.rootSgn]
    · have h1 : ∀ τ (k : Fin D.q), HodgeCpt.rootIdx D (τ, Fin.natAdd D.p k.rev) = ⟨.inr τ, k⟩ := fun τ k => by
        unfold HodgeCpt.rootIdx
        rw [dif_neg (by simp)]
        congr 1
        apply Fin.ext
        have := k.2
        simp only [Fin.val_natAdd, Fin.val_rev]
        omega
      refine ⟨_, _, Lat.tens_isDegOn _ _ _ _ _ _ _ _ _ _ _ (fun τ => Lat.tens_isDegOn _ _ _ _ _ _ _ _ _ _ _
        (fun k => hgr _ _ (h1 τ k)) _) _, ?_⟩
      convert n1 using 1
      refine Finset.sum_congr rfl fun τ _ => ?_
      rw [Finset.sum_filter, Fin.sum_univ_add]
      have h2 : ∀ k : Fin D.p, ¬ D.p ≤ (k : ℕ) := fun k => not_le.2 k.2
      have h3 := Equiv.sum_comp Fin.revPerm fun k : Fin D.q => M.xdeg (τ, Fin.natAdd D.p k)
      simp [HodgeCpt.rootSgn, h2, ← h3]
  obtain ⟨A, e₁, hA1, hA2⟩ := hA
  have hN := GlobalTheory.CompanionTheory.Relay.nef_degree_scale_invariant hI _ M.Ω M.K M.ι M.y 𝔐'.ξ _ A a' e₁ _ _ 𝔐'.tie
    (Finset.prod_ne_zero_iff.2 fun τ _ => hu0 τ) hA1 hB hA2
  obtain ⟨c₀, hc₀⟩ := 𝔐'.tie.cover ⟨genPt 𝔐'.ξ, specializes_rfl⟩
  exact GlobalTheory.T.coords_reindex_degree hI Ω M.Ω i K M.K J M.ι y M.y bk bx a a' hbk hy (fun k => ⟨_, GlobalTheory.CompanionTheory.Ar.Cusp.DetNef.chart_ne hc₀ k⟩) ha ha' hN
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.KeyBadReductionHoldsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.key_bad_reduction_holds : KeyBadSt := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Sl.KP.key_bad | exact GlobalTheory.CompanionTheory.Ar.Sl.KP.key_bad | (intros; apply GlobalTheory.CompanionTheory.Ar.Sl.KP.key_bad <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.KeyOverLieBasisDegree
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.key_over_lie_basis_degree : KeyBadSt → ∀ κ : GlobalTheory.KeyCl.Rule, GlobalTheory.KeyCl.Homog (fun _ => 1) κ → GlobalTheory.KeyCl.Funct κ → GlobalTheory.KeyCl.UnitSp κ → GlobalTheory.KeyCl.ThetaOne κ → GlobalTheory.KeyCl.ArchNorm (fun _ => 1) κ → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (t : SAB H (Sp (𝓞 L))) (th : t.PP.L.Sec) (x : KeyIn L) (v : Fin x.P.g → (epsR (𝓞 L) ⟶ t.G)), KeyOver (algebraMap (𝓞 L) L) t th x v → IsLieBasis v → KeyDeg.NonVan t.G.hom th → IsIntegral ℤ (κ L x : L) := by
  first | exact @PositivityTheory.HtPt.Qac.keydeg_integral | exact PositivityTheory.HtPt.Qac.keydeg_integral
end

