import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0024
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0271
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0285
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0343
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0341
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0027
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.DiagSmall
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0028
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0029
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ToGlob0
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0028
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0010
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CollSBound
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0083
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0048
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0161
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1048
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteAdeleBaseChangeEquiv
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumTransportSourceRationalIsometry
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0104
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0296
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0354
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0214
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0054
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.DegenerateConstant
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LoopTerm
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0342
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlockDetBlockTriangular

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AbsThetaIntegralLeSobolevSeminorm
section
open scoped ComplexConjugate Matrix NNReal ENNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec delta ThetaClause)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
open GlobalTheory.Size (sobO thetaLevel)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ThetaDens

namespace GlobalTheory.ThetaDens

theorem tendsto_enorm_of_le {v : ℕ → ℂ} {a : ℂ} {s : ℕ → ℝ≥0∞} (C : ℝ≥0) (hs : Filter.Tendsto s Filter.atTop (nhds 0))
    (h : ∀ j, ‖v j - a‖ₑ ≤ C * s j) : Filter.Tendsto (fun j => ‖v j‖ₑ) Filter.atTop (nhds ‖a‖ₑ) := by
  have h1 : Filter.Tendsto (fun j => (C : ℝ≥0∞) * s j) Filter.atTop (nhds 0) := by
    simpa using ENNReal.Tendsto.const_mul (a := (C : ℝ≥0∞)) hs (Or.inr ENNReal.coe_ne_top)
  have h2 : Filter.Tendsto (fun j => edist (v j) a) Filter.atTop (nhds 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h1 (fun _ => zero_le)
      (fun j => by simpa [edist_eq_enorm_sub] using h j)
  exact (continuous_enorm.tendsto a).comp (tendsto_iff_edist_tendsto_0.2 h2)

theorem sobBdd_absThetaInt : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ θ : InfFam D, IsInfFam θ → ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ m : Measure (GA D T), m.IsHaarMeasure → ∀ Z : (WO S T → ℂ) → WO S T → ℂ, (∀ f f', IsThetaFunO ψ S T f → IsThetaFunO ψ S T f' → Z (f + f') = Z f + Z f') → (∀ (c : ℂ) f, IsThetaFunO ψ S T f → Z (c • f) = c • Z f) → Sobolev₂ ψ θ μ 𝓕 μ 𝓕 Z → (∀ f, IsThetaFunO ψ S T f → ∀ x, om (x, 1) (Z f) = Z (om (x, 1) f)) → (∀ f, IsThetaFunO ψ S T f → Integrable (descend (GQ T) fun h => thetaKO om 1 h (Z f)) (autMeasure T m)) → SobBdd ψ θ μ 𝓕 fun f x => ∫⁻ q, ‖descend (GQ T) (fun h => thetaKO om x h (Z f)) q‖ₑ ∂autMeasure T m := by
  intro D ψ S T χS χT om hom θ hθ μ 𝓕 hc m _ Z hadd hsm hZ hcomm hint U hU K hK
  obtain ⟨U', hU', hl, hb⟩ := GlobalTheory.T.exists_common_level_sobolev_bound_weil_compact D ψ S T χS χT om hom θ hθ μ 𝓕 hc (K ×ˢ {1})
    (hK.prod isCompact_singleton) U hU
  have pt : ∀ h : GA D T, ∃ (d : ℕ) (C : ℝ≥0), ∀ g ∈ thetaLevel ψ S T U',
      ‖thetaKO om 1 h (Z g)‖ₑ ≤ C * sobO ψ θ μ 𝓕 d g := by
    intro h
    obtain ⟨U₁, hU₁, hl₁, hb₁⟩ := hZ U' hU'
    obtain ⟨U₂, hU₂, hl₂, hb₂⟩ := GlobalTheory.T.exists_common_level_sobolev_bound_weil_compact D ψ S T χS χT om hom θ hθ μ 𝓕 hc {(1, h)}
      isCompact_singleton U₁ hU₁
    obtain ⟨d₃, C₃, hb₃⟩ := GlobalTheory.T.exists_sobolev_bound_theta_pointwise D ψ hom.std θ hθ S T μ 𝓕 hc U₂ hU₂
    obtain ⟨d₂, C₂, hb₂⟩ := hb₂ d₃
    obtain ⟨d₁, C₁, hb₁⟩ := hb₁ d₂
    refine ⟨d₁, C₃ * (C₂ * C₁), fun g hg => ?_⟩
    refine (hb₃ _ (hl₂ _ (hl₁ g hg) _ rfl) 0).trans ?_
    rw [ENNReal.coe_mul, ENNReal.coe_mul, mul_assoc, mul_assoc]
    gcongr
    refine (hb₂ _ (hl₁ g hg) _ rfl).trans ?_
    gcongr
    exact hb₁ g hg
  obtain ⟨d, C, hN⟩ := GlobalTheory.T.lsc_seminorm_thetaFunctionsLevel_le_sobolev D ψ hom.std θ hθ S T μ 𝓕 hc U' hU'
    (fun f => ∫⁻ q, ‖descend (GQ T) (fun h => thetaKO om 1 h (Z f)) q‖ₑ ∂autMeasure T m)
    (fun f hf g hg => by
      rw [← lintegral_add_left' (hint f hf.1).1.enorm]
      refine lintegral_mono fun q => ?_
      simp only [GlobalTheory.AutomorphicL2Unitary.descend, thetaKO, hadd f g hf.1 hg.1, map_add, Pi.add_apply]
      exact enorm_add_le _ _)
    (fun c f hf => by
      rw [← lintegral_const_mul' _ _ enorm_ne_top]
      refine lintegral_congr fun q => ?_
      simp only [GlobalTheory.AutomorphicL2Unitary.descend, thetaKO, hsm c f hf.1, map_smul, Pi.smul_apply, enorm_smul])
    (fun f hf => (hint f hf.1).2.ne)
    (fun u hu f hf ht => by
      refine le_trans (lintegral_mono fun q => ?_) (lintegral_liminf_le' fun j => (hint _ (hu j).1).1.enorm)
      obtain ⟨d, C, hp⟩ := pt (Quotient.out q)
      refine (tendsto_enorm_of_le C (ht d) fun j => ?_).liminf_eq.ge
      refine le_of_eq_of_le ?_ (hp _ (sub_mem (hu j) hf))
      have e : u j - f = u j + (-1 : ℂ) • f := by rw [neg_one_smul, sub_eq_add_neg]
      have hf' : (-1 : ℂ) • f ∈ thetaLevel ψ S T U' := Submodule.smul_mem _ _ hf
      rw [e, hadd _ _ (hu j).1 hf'.1, hsm _ _ hf.1]
      simp only [GlobalTheory.AutomorphicL2Unitary.descend, thetaKO, map_add, Pi.add_apply, neg_one_smul,
        sub_eq_add_neg, map_neg, Pi.neg_apply])
  obtain ⟨d', C', hb⟩ := hb d
  refine ⟨d', C * C', fun f hf x hx => ?_⟩
  have hx' : ((x, 1) : GA D S × GA D T) ∈ K ×ˢ {1} := ⟨hx, rfl⟩
  refine le_of_eq_of_le ?_ ((hN _ (hl f hf _ hx')).trans ?_)
  · refine lintegral_congr fun q => ?_
    simp only [GlobalTheory.AutomorphicL2Unitary.descend, thetaKO]
    rw [← hcomm f hf.1 x, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, one_mul, mul_one]
  · rw [ENNReal.coe_mul, mul_assoc]
    gcongr
    exact hb f hf _ hx'

end GlobalTheory.ThetaDens
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AbstractDiagonalBoundCollisionsCountedOnceStatement
section
open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 GlobalTheory.Core.Diag GlobalTheory.Core.Deg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abstractDiagonalBound_collisions_counted_once : ∀ (τ Rw I H H₁ : Type) [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁] (X : Formalism.FourierDecayAlt.PB.Terms τ Rw I H H₁) (one : H) (Pg B A₁ A₂ : ℝ), 0 ≤ Pg → X.AbsConv → X.NormExpansionOn X.genSet → X.NormExpansionOn X.ngSet → X.GGBound Pg → X.RowOrth → X.CorankPos → Formalism.L2.SG.RowsOther.IdOne X one → X.pairAbs (X.big X.nzSet) ≤ B → X.pairSum (X.one X.genSet) ≤ A₁ → X.pairSum (X.one X.ngSet) ≤ A₂ → ‖X.K0 - one‖ ^ 2 ≤ 2 * Pg * (B + A₁ + A₂) := by
  first | exact @GlobalTheory.diag_abstract_collisions_once | exact GlobalTheory.diag_abstract_collisions_once | (intros; apply GlobalTheory.diag_abstract_collisions_once <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdAtToEAfOfIsIdemSum
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdForm.CongAtIdem

theorem read_rel {A B K E : Type} [CommRing A] [CommRing B] [CommRing K] [CommRing E] {m n : Type} [Fintype m] [Fintype n]
    (t : A →+* B) (φ : B →+* K) (i : E →+* A) (j : E →+* B) (hij : ∀ x, t (i x) = j x) {e : A} (he : φ (t e) = 1)
    (X : Matrix m m A) (Z : Matrix n n A) (γ γ₀ : Matrix m n E) (v : Matrix m n A) (k : ℕ)
    (h : γ₀.map (fun r => e * i r) = X * γ.map (fun r => e * i r) * Z + k • v) (r : m) (s : n) :
    φ ((X.map t * γ.map j * Z.map t - γ₀.map j) r s) = -((k : K) * φ (t (v r s))) := by
  have h1 := congrArg (fun W : Matrix m n A => φ (t (W r s))) h
  simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.mul_apply, map_add, map_sum, map_mul, he,
    one_mul, hij, nsmul_eq_mul, map_natCast] at h1
  simp only [Matrix.map_apply, Matrix.sub_apply, Matrix.mul_apply, map_sub, map_sum, map_mul, h1]
  ring

end GlobalTheory.AdForm.CongAtIdem

namespace GlobalTheory.AdForm.CongAtIdem

variable {D : D7}

theorem adAt_toEAf_of_isIdemAt {f : AE D} {P : HeightOneSpectrum (𝓞 D.host.E)}
    (hf : Formalism.L2.NTheta.IsIdemAt f P) : adAt D.host.F P (toEAf D f) = 1 := by
  let ι : Af D.host.F ⊗[D.host.F] D.host.E ≃+* FiniteAdeleRing (𝓞 D.host.E) D.host.E :=
    (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).toRingEquiv.trans (afIso D.host.F D.host.E)
  have h1 : ∀ x : D.host.E, ι ((1 : Af D.host.F) ⊗ₜ[D.host.F] x) =
      algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E) x := fun x =>
    afIso_tmul_one D.host.F D.host.E x
  have h2 : ∀ y, y ∈ intAE D ↔ ∀ Q : HeightOneSpectrum (𝓞 D.host.E), Valued.v (ι y Q) ≤ 1 := fun y =>
    (GlobalTheory.IdemSupport.mem_intAE_iff y).trans (mem_rInt_iff D.host.F D.host.E _)
  exact GlobalTheory.ChrOff.comp_idem ι h1 h2 hf

theorem adAt_toEAf_of_isIdemSum {e : AE D} {Ps : Finset (HeightOneSpectrum (𝓞 D.host.E))}
    (he : IsIdemSum e Ps) {P : HeightOneSpectrum (𝓞 D.host.E)} (hP : P ∈ Ps) :
    adAt D.host.F P (toEAf D e) = 1 := by
  obtain ⟨a, ha, hae⟩ := GlobalTheory.OffIdem.idemSum_mul_idemAt he hP
  have h := congrArg (fun z => adAt D.host.F P (toEAf D z)) hae
  simp only [map_mul, adAt_toEAf_of_isIdemAt ha, one_mul] at h
  exact h

end GlobalTheory.AdForm.CongAtIdem

namespace GlobalTheory.AdForm.CongAtIdem

variable {D : D7}

theorem isIntegral_of_eq {x : D.host.E} (h : ∃ r : 𝓞 D.host.E, algebraMap (𝓞 D.host.E) D.host.E r = x) :
    IsIntegral ℤ x := by
  obtain ⟨r, rfl⟩ := h
  exact r.2

theorem tmul_one_mem_rInt {x : D.host.E} (hx : IsIntegral ℤ x) :
    x ⊗ₜ[D.host.F] (1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ∈ Formalism.L2.DIV.RInt D.host.F D.host.E :=
  Subring.subset_closure (Or.inl ⟨⟨x, ⟨⟨x, hx⟩, rfl⟩⟩, rfl⟩)

theorem one_tmul_mem_rInt {α : FiniteAdeleRing (𝓞 D.host.F) D.host.F} (hα : α ∈ intAf D.host.F) :
    (1 : D.host.E) ⊗ₜ[D.host.F] α ∈ Formalism.L2.DIV.RInt D.host.F D.host.E :=
  Subring.subset_closure (Or.inr ⟨⟨α, fun v => hα v⟩, rfl⟩)

theorem exists_den_stdHom (S T : HSp D) : ∃ d : ℕ, 0 < d ∧ ∀ v ∈ stdHom S T, ∀ r s,
    ((d : EF D) * toEAf D (v r s) : Formalism.L2.DIV.AfE D.host.F D.host.E) ∈ Formalism.L2.DIV.RInt D.host.F D.host.E := by
  obtain ⟨a0, ha0, hfrac⟩ := D.host.AA.isFractional
  have ha0' : ((a0 : 𝓞 D.host.E) : D.host.E) ≠ 0 := by
    intro h
    exact nonZeroDivisors.coe_ne_zero ⟨a0, ha0⟩ (RingOfIntegers.coe_eq_zero_iff.1 h)
  obtain ⟨d, hd, hint⟩ := GlobalTheory.AdeleBaseChange.exists_nat_mul_integral
    (insert ((a0 : D.host.E))⁻¹ (Finset.image (fun p : Fin S.rank × Fin S.rank => S.gram p.1 p.2) Finset.univ))
  have hx0 : IsIntegral ℤ ((d : D.host.E) * ((a0 : D.host.E))⁻¹) := by
    rw [← nsmul_eq_mul]; exact isIntegral_of_eq (hint _ (Finset.mem_insert_self _ _))
  have hG : ∀ k j, IsIntegral ℤ ((d : D.host.E) * S.gram k j) := fun k j => by
    rw [← nsmul_eq_mul]
    exact isIntegral_of_eq (hint _ (Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨(k, j), Finset.mem_univ _, rfl⟩)))
  refine ⟨d * d, Nat.mul_pos hd hd, fun v hv => ?_⟩
  induction hv using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, -, a, ha, s, hs, t, ht, rfl⟩ := hw
    intro r c
    have hint' : IsIntegral ℤ (((d * d : ℕ) : D.host.E) * (a * t r * ∑ k, star (s k) * S.gram k c)) := by
      have hA : IsIntegral ℤ ((a0 : D.host.E) * a) := by
        obtain ⟨y, hy⟩ := hfrac a ha
        refine isIntegral_of_eq ⟨y, ?_⟩
        rw [hy, Algebra.smul_def]
      have hsum : IsIntegral ℤ (∑ k, star (s k) * ((d : D.host.E) * S.gram k c)) :=
        IsIntegral.sum _ fun k _ => IsIntegral.mul
          ((hs k).map (starRingEnd D.host.E).toIntAlgHom) (hG k c)
      have e : ((d * d : ℕ) : D.host.E) * (a * t r * ∑ k, star (s k) * S.gram k c) =
          ((d : D.host.E) * ((a0 : D.host.E))⁻¹) * ((a0 : D.host.E) * a) * t r *
            ∑ k, star (s k) * ((d : D.host.E) * S.gram k c) := by
        have hx : ((a0 : D.host.E))⁻¹ * (a0 : D.host.E) = 1 := inv_mul_cancel₀ ha0'
        have e2 : ∑ k, star (s k) * ((d : D.host.E) * S.gram k c) = (d : D.host.E) * ∑ k, star (s k) * S.gram k c := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
        rw [e2]; push_cast
        linear_combination (-((d : D.host.E) * d * a * t r * ∑ k, star (s k) * S.gram k c)) * hx
      rw [e]
      exact ((hx0.mul hA).mul (ht r)).mul hsum
    change ((d * d : ℕ) : EF D) * ((a * t r * ∑ k, star (s k) * S.gram k c) ⊗ₜ[D.host.F] α) ∈ _
    have e3 : ((d * d : ℕ) : EF D) * ((a * t r * ∑ k, star (s k) * S.gram k c) ⊗ₜ[D.host.F] α) =
        ((((d * d : ℕ) : D.host.E) * (a * t r * ∑ k, star (s k) * S.gram k c)) ⊗ₜ[D.host.F]
          (1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F)) * ((1 : D.host.E) ⊗ₜ[D.host.F] α) := by
      have hc : ((d * d : ℕ) : EF D) = ((d * d : ℕ) : D.host.E) ⊗ₜ[D.host.F] (1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) :=
        (map_natCast (Algebra.TensorProduct.includeLeftRingHom (R := D.host.F) (A := D.host.E)
          (B := FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (d * d)).symm
      rw [hc]
      simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [e3]
    exact mul_mem (tmul_one_mem_rInt hint') (one_tmul_mem_rInt hα)
  | zero => intro r s; simp
  | add x y _ _ hx hy => intro r s; rw [Matrix.add_apply, RingHom.map_add (toEAf D), mul_add]; exact add_mem (hx r s) (hy r s)
  | neg x _ hx => intro r s; rw [Matrix.neg_apply, RingHom.map_neg (toEAf D), mul_neg]; exact neg_mem (hx r s)

end GlobalTheory.AdForm.CongAtIdem

namespace GlobalTheory.AdForm.CongAtIdem

variable {D : D7}

theorem finM_rfl (V : HSp D) (x : GA D V) : finM V rfl x = (Formalism.L2.Theta.mt V x).map (toEAf D) := by
  simp [finM, finCongr_refl]

theorem mt_mul' (V : HSp D) (x y : GA D V) :
    Formalism.L2.Theta.mt V (x * y) = Formalism.L2.Theta.mt V x * Formalism.L2.Theta.mt V y := by
  show (matHom V (x * y)).1 = (matHom V x).1 * (matHom V y).1
  rw [map_mul, Units.val_mul]

theorem mt_one' (V : HSp D) : Formalism.L2.Theta.mt V 1 = 1 := by
  show (matHom V 1).1 = 1
  rw [map_one, Units.val_one]

theorem inv_val_eq (V : HSp D) (x : GA D V) (Y : GL (Fin V.rank) (EF D)) (hY : finM V rfl x = Y.1) :
    (Y⁻¹ : GL (Fin V.rank) (EF D)).1 = (Formalism.L2.Theta.mt V x⁻¹).map (toEAf D) := by
  have h1 : (Formalism.L2.Theta.mt V x⁻¹).map (toEAf D) * Y.1 = 1 := by
    rw [← hY, finM_rfl, ← Matrix.map_mul, ← mt_mul', inv_mul_cancel, mt_one',
      Matrix.map_one _ (map_zero _) (map_one _)]
  calc (Y⁻¹ : GL (Fin V.rank) (EF D)).1
      = ((Formalism.L2.Theta.mt V x⁻¹).map (toEAf D) * Y.1) * (Y⁻¹ : GL (Fin V.rank) (EF D)).1 := by
        rw [h1, Matrix.one_mul]
    _ = (Formalism.L2.Theta.mt V x⁻¹).map (toEAf D) := by
        rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]

end GlobalTheory.AdForm.CongAtIdem

namespace GlobalTheory.AdForm.CongAtIdem

theorem cong_at_idem : ∀ {D : D7} (S T : HSp D) {a b : ℕ} (hS : S.rank = a) (hT : T.rank = b) (e : AE D)
    (Ps : Finset (HeightOneSpectrum (𝓞 D.host.E))), IsIdemSum e Ps → ∃ d : ℕ, 0 < d ∧
    ∀ (g : GA D S) (h : GA D T) (Y : GL (Fin a) (EF D)) (Y' : GL (Fin b) (EF D)), finM S hS g = Y.1 → finM T hT h = Y'.1 →
    ∀ (M : ℕ) (γ γ₀ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) (v : WO S T), v ∈ stdHom S T →
      γ₀.map (fun r => e * incA D r) = actO S T g⁻¹ h⁻¹ (γ.map fun r => e * incA D r) + (d * M) • v →
      ∀ P ∈ Ps, ∀ r s, Valued.v (adAt D.host.F P
        ((HMul.hMul (HMul.hMul ((Y'⁻¹ : GL (Fin b) (EF D)).1 : Matrix (Fin b) (Fin b) (EF D))
          (((LinearMap.toMatrix' (toHom S T hS hT γ)).map (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) : Matrix (Fin b) (Fin a) (EF D))))
          (Y.1 : Matrix (Fin a) (Fin a) (EF D)) -
          ((LinearMap.toMatrix' (toHom S T hS hT γ₀)).map (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) : Matrix (Fin b) (Fin a) (EF D))) r s)) ≤
        Valued.v ((M : ℕ) : P.adicCompletion D.host.E) := by
  intro D S T a b hS hT e Ps he
  subst hS; subst hT
  obtain ⟨d, hd, hden⟩ := exists_den_stdHom S T
  refine ⟨d, hd, ?_⟩
  intro g h Y Y' hY hY' M γ γ₀ v hv hH P hP r s
  rw [← hY, finM_rfl, inv_val_eq T h Y' hY']
  simp only [toHom, LinearMap.toMatrix'_toLin', finCongr_refl, Matrix.reindex_refl_refl]
  rw [actO, inv_inv] at hH
  have key := read_rel (toEAf D) (adAt D.host.F P) (incA D)
    (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (fun _ => rfl)
    (adAt_toEAf_of_isIdemSum he hP) _ _ γ γ₀ v (d * M) hH r s
  have hint : Valued.v (adAt D.host.F P ((d : EF D) * toEAf D (v r s))) ≤ 1 :=
    (mem_rInt_iff D.host.F D.host.E _).1 (hden v hv r s) P
  rw [RingHom.map_mul, map_natCast (adAt D.host.F P)] at hint
  refine (congrArg Valued.v key).trans_le ?_
  rw [Valuation.map_neg, Nat.cast_mul, mul_right_comm, Valuation.map_mul]
  exact mul_le_of_le_one_left' hint

end GlobalTheory.AdForm.CongAtIdem
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicUnitaryRealMulFiniteDecomposition
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdelicSplitParts

variable {D : D7}

theorem infMat_eq_map (V : HSp D) (θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) (h : GA D V) :
    infMat D.sp.cm.sig V.gram θ h = (infHom V h).1.map θ := rfl

theorem split_parts : ∀ (D : D7) (V : HSp D), (∀ h : GA D V, ∃ a ∈ GinfC V, ∃ k ∈ GfC V, h = a * k) ∧ ∀ a ∈ GinfC V, ∀ k ∈ GfC V, Lev.finE V (a * k) = Lev.finE V k ∧ ∀ θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ, infMat D.sp.cm.sig V.gram θ (a * k) = infMat D.sp.cm.sig V.gram θ a := by
  intro D V
  refine ⟨fun h => ?_, fun a ha k hk => ⟨?_, fun θ => ?_⟩⟩
  · obtain ⟨p, hp⟩ := (GlobalTheory.AdelicSplit.splitEquiv V).surjective h
    exact ⟨p.1.1, p.1.2, p.2.1, p.2.2, hp.symm⟩
  · have h1 : finE V a = 1 := by
      have : finHom V a = 1 := ha
      simp only [finE, MonoidHom.comp_apply, this, map_one]
    rw [map_mul, h1, one_mul]
  · have h1 : infHom V k = 1 := hk
    rw [infMat_eq_map, infMat_eq_map, map_mul, h1, mul_one]

end GlobalTheory.AdelicSplitParts
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CharConjFixedEqOne
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CharConjFixed

theorem nontrivial_AF (D : D7) : Nontrivial (AF D.host.F) :=
  inferInstanceAs (Nontrivial (InfiniteAdeleRing D.host.F × FiniteAdeleRing (𝓞 D.host.F) D.host.F))

theorem finrank_AE (D : D7) : Module.finrank (AF D.host.F) (AE D) = 2 := by
  haveI := nontrivial_AF D
  rw [Module.finrank_baseChange]; exact D.sp.cm.deg2

theorem cA_tmul (D : D7) (a : AF D.host.F) (e : D.host.E) :
    cA D (a ⊗ₜ[D.host.F] e) = a ⊗ₜ[D.host.F] star e := rfl

set_option synthInstance.maxHeartbeats 200000 in

theorem trace_mem (D : D7) (y : AE D) :
    ∃ b : AF D.host.F, algebraMap (AF D.host.F) (AE D) b = y + cA D y := by
  induction y using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | add a b ha hb =>
    obtain ⟨u, hu⟩ := ha
    obtain ⟨v, hv⟩ := hb
    refine ⟨u + v, ?_⟩
    rw [map_add, hu, hv, map_add]; abel
  | tmul a e =>
    have hfix : star (e + star e) = e + star e := by
      rw [star_add, star_star, add_comm]
    obtain ⟨f, hf⟩ := (D.sp.cm.fixed _).1 hfix
    refine ⟨f • a, ?_⟩
    rw [cA_tmul, ← TensorProduct.tmul_add, ← hf, Algebra.algebraMap_eq_smul_one (A := D.host.E) f,
      ← TensorProduct.smul_tmul]
    rfl

theorem fixed_mem (D : D7) (y : AE D) (hy : cA D y = y) :
    ∃ b : AF D.host.F, algebraMap (AF D.host.F) (AE D) b = y := by
  obtain ⟨b, hb⟩ := trace_mem D y
  refine ⟨algebraMap D.host.F (AF D.host.F) (2⁻¹) * b, ?_⟩
  have h2 : algebraMap (AF D.host.F) (AE D) (algebraMap D.host.F (AF D.host.F) (2⁻¹)) * 2 = 1 := by
    rw [show (2 : AE D) = algebraMap (AF D.host.F) (AE D) (algebraMap D.host.F (AF D.host.F) 2) by rw [map_ofNat, map_ofNat],
      ← map_mul, ← map_mul, inv_mul_cancel₀ (two_ne_zero : (2 : D.host.F) ≠ 0), map_one, map_one]
  rw [map_mul, hb, hy, ← two_mul, ← mul_assoc, h2, one_mul]

theorem norm_scalar (D : D7) (b : AF D.host.F) :
    Algebra.norm (AF D.host.F) (algebraMap (AF D.host.F) (AE D) b) = b ^ 2 := by
  rw [Algebra.norm_algebraMap, finrank_AE]

theorem fixed_unit (D : D7) (x : (AE D)ˣ) (hx : cA D (x : AE D) = x) :
    ∃ a : (AF D.host.F)ˣ, idF D a = x := by
  obtain ⟨b, hb⟩ := fixed_mem D x hx
  have hn : IsUnit (Algebra.norm (AF D.host.F) (x : AE D)) := x.isUnit.map _
  rw [← hb, norm_scalar] at hn
  obtain ⟨a, ha⟩ := (isUnit_pow_iff two_ne_zero).1 hn
  refine ⟨a, Units.ext ?_⟩
  rw [← hb, ← ha]; rfl

end GlobalTheory.CharConjFixed

open GlobalTheory.CharConjFixed in

theorem GlobalTheory.char_conj_fixed_eq_one : ∀ (D : D7) (μ : (AE D)ˣ →* Circle) (n : ℕ), ResEta D μ n → Even n →
    ∀ (V : HSp D) (x : (AE D)ˣ), IsDetRoot V 1 x → μ x = 1 := by
  intro D μ n hμ hn V x hx
  have hfix : cA D (x : AE D) = x := by
    have h := hx
    simp only [IsDetRoot, map_one, Units.val_one, Matrix.det_one, one_mul] at h
    exact h.symm
  obtain ⟨a, ha⟩ := fixed_unit D x hfix
  obtain ⟨⟨η, hη⟩, hall⟩ := hμ
  have hμa : μ (idF D a) = η a ^ n := hall η hη a
  have hsq : η a ^ 2 = 1 := by
    rw [← map_pow]
    have : Units.map (↑(Algebra.norm (AF D.host.F)) : AE D →* AF D.host.F) (idF D a) = a ^ 2 := by
      ext
      exact norm_scalar D (a : AF D.host.F)
    rw [← this]; exact hη.2.2.1 _
  obtain ⟨k, rfl⟩ := hn
  rw [← ha, hμa, ← two_mul, pow_mul, hsq, one_pow]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CollisionAbsSumBoundOfTwoRowBoundsStatement
section
open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.collisionAbsSum_bound_of_two_rowBounds : Formalism.HermitianLatticesTheory.SiegelMassRatio → ∀ CT C : ℝ, 408 * (Real.exp 1 * Real.pi) ≤ C → CT ≤ C → ∃ thr : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (hF : FinX Y) (hI : SIso D.s (sOf hF)) (u : D.what₂.Word) (T : TermTie D) (Z : LoopTie D large₂ T u u 1) (C' Cl Cg cb Cu cT C0 : ℝ), thr ≤ C' → thr ≤ Cl → Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0 → ConcTie X Y → (Y.tO u u).AbsConv → TieAt hF hI large₂ u T Z → UnitaryVolumeMass.FormAt D u → BridgeLemma.RowsND T Z C → BridgeLemma.RowsDeg T Z C → CollS Y u := by
  first | exact @GlobalTheory.Core.Deg.collS_of_rowBounds | exact GlobalTheory.Core.Deg.collS_of_rowBounds | (intros; apply GlobalTheory.Core.Deg.collS_of_rowBounds <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ColumnDimensionWindowThreeOfColumnCountStatement
section
open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 GlobalTheory.Core.Diag GlobalTheory.Core.Deg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.columnDimension_window_three_of_columnCount : ∀ D : D7, DataNW D → (∀ u, GlobalTheory.Core.Rk.RankMu D u) → StandingNumericalData D 3 := by
  first | exact @GlobalTheory.Core.Diag.standingNumericalData_three_of_dataNW_rankMu | exact GlobalTheory.Core.Diag.standingNumericalData_three_of_dataNW_rankMu | (intros; apply GlobalTheory.Core.Diag.standingNumericalData_three_of_dataNW_rankMu <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CongAt
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Transport

def CongAt (B : Base) {a b : ℕ} (P : HeightOneSpectrum (𝓞 B.host.E)) (M₀ : ℕ) (y : TC.GA B a) (y' : TC.GA B b)
    (x x₀ : Formalism.L2.Col.HomE B.fields.E a b) : Prop :=
  ∀ r s, Valued.v (adAt B.host.F P
    ((HMul.hMul (HMul.hMul ((y'⁻¹ : TC.GA B b).1 : Matrix (Fin b) (Fin b) (Formalism.L2.DIV.AfE B.host.F B.host.E))
      ((LinearMap.toMatrix' x).map (inclE (F := B.host.F) (FiniteAdeleRing (𝓞 B.host.F) B.host.F)) : Matrix (Fin b) (Fin a) (Formalism.L2.DIV.AfE B.host.F B.host.E)))
      (y.1 : Matrix (Fin a) (Fin a) (Formalism.L2.DIV.AfE B.host.F B.host.E)) -
      ((LinearMap.toMatrix' x₀).map (inclE (F := B.host.F) (FiniteAdeleRing (𝓞 B.host.F) B.host.F)) : Matrix (Fin b) (Fin a) (Formalism.L2.DIV.AfE B.host.F B.host.E))) r s)) ≤
    Valued.v ((M₀ : ℕ) : P.adicCompletion B.host.E)

end GlobalTheory.Transport
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DiscreteSeriesDetSqrtCoverOfUnitaryClassificatioStatement
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible Formalism.L2.Theta Matrix GlobalTheory.RealPar GlobalTheory.CoverDS
open GlobalTheory.IndefiniteRowSideFullHecke.IsotypicSignedParameters (SignedPar IsDSPar)
open Formalism.MainNotions.S (IsURepOn IsIrredOn IsKFin IsKStableOn IsWtOn IsKTypeOf IsDS IsSqIntOn UJset)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.discreteSeries_detSqrtCover_of_unitary_classification : GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Published.DiscreteSeriesCover := by
  first | exact @GlobalTheory.CoverDS.discreteSeriesCover_of_classification | exact GlobalTheory.CoverDS.discreteSeriesCover_of_classification | (intros; apply GlobalTheory.CoverDS.discreteSeriesCover_of_classification <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFiniteAdeleProjectionIntegralReductionStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.StepData NumberField
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finiteAdele_projection_integral_reduction : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (PP : Formalism.L2.DIV.Pl D.host.E), Formalism.L2.NTheta.IsIdemAt q.e PP → ∃ π' : EAf D →+* k, (∀ a, π' (toEAf D a) = q.pr a) ∧ GlobalTheory.FunObj.Comparison₂.IsRed (Formalism.L2.DIV.resS D.host.F PP) (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) ∧ (∀ z : EAf D, z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ↔ (1 - toEAf D q.e) * z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ∧ π' z ∈ 𝒪[k]) ∧ ∀ PP' : Formalism.L2.DIV.Pl D.host.E, PP' ≠ PP → ∀ (z : EAf D) (hz : z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) (hz' : (1 - toEAf D q.e) * z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E), Formalism.L2.DIV.resS D.host.F PP' ⟨(1 - toEAf D q.e) * z, hz'⟩ = Formalism.L2.DIV.resS D.host.F PP' ⟨z, hz⟩ := by
  first | exact @GlobalTheory.FinPl.SplitPt.exists_lift_isRed | exact GlobalTheory.FinPl.SplitPt.exists_lift_isRed | (intros; apply GlobalTheory.FinPl.SplitPt.exists_lift_isRed <;> assumption)
end

