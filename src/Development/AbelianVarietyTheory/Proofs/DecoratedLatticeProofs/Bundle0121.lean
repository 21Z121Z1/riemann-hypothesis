import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0109
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0012
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0009
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0106
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0102
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0114
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0105
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0110
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.AutomorphicFormsFiniteIdeal
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsSigmaList
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0028
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0330
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0321
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0095
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0097
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0109
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0112
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0055

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCommonHeisenbergLevelWeilTransformCompactStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_common_heisenbergLevel_weilTransform_compact : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T χS χT om → ∀ f, IsThetaFunO ψ S T f → ∀ K : Set (GA D S × GA D T), IsCompact K → ∃ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) ∧ ∀ p ∈ K, om p f ∈ GlobalTheory.Size.thetaLevel ψ S T U := by
  first | exact @GlobalTheory.LevelCompact.exists_level_compact | exact GlobalTheory.LevelCompact.exists_level_compact | (intros; apply GlobalTheory.LevelCompact.exists_level_compact <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFiniteComponentUnitaryActingOnFiniteSuppor
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel
open IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000

theorem GlobalTheory.GlobFin.cong_entry {D : D7} {S : HSp D} {I : Ideal (AE D)} {h : GA D S} (hh : h ∈ congGrp S I) (i j : Fin S.rank) :
    mt S h i j - (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) i j ∈ I := by
  have h1 := congrArg (fun A : GL (Fin S.rank) (AE D ⧸ I) => A.1 i j) (MonoidHom.mem_ker.mp hh)
  rw [← Ideal.Quotient.eq]
  have h2 : Ideal.Quotient.mk I ((1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) i j) = (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D ⧸ I)) i j := by
    rcases eq_or_ne i j with rfl | hij <;> simp [Matrix.one_apply, *]
  rw [h2]
  simpa [Formalism.L2.Theta.mt, Matrix.GeneralLinearGroup.map] using h1

theorem GlobalTheory.GlobFin.mem_GfC {D : D7} {S : HSp D} {x : GA D S} (hx : x ∈ congGrp S (idAt D (fun _ => True))) : x ∈ GfC S := by
  show infHom S x = 1
  ext i j
  have h := GlobalTheory.GlobFin.cong_entry hx i j
  have hk : mt S x i j - (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) i j ∈ RingHom.ker (infPart D) :=
    (inf_le_left : idAt D (fun _ => True) ≤ _) h
  rw [RingHom.mem_ker, map_sub, sub_eq_zero] at hk
  have : ((infHom S x : GL _ _) : Matrix _ _ _) i j = infPart D (mt S x i j) := rfl
  rw [this, hk]
  simp [Matrix.one_apply, apply_ite]

theorem GlobalTheory.GlobFin.fin_rep : ∀ (D : D7) (S : HSp D) (g : GA D S), ∃ x ∈ GfC S, ∀ (P : Pl D → Prop) (y : Fin S.rank → AE D), (∀ i, y i ∈ idAt D P) → mt S g *ᵥ y = mt S x *ᵥ y := by
  intro D S g
  obtain ⟨⟨ε, -, -, -, hAt, hOff⟩, hS⟩ := GlobalTheory.T.adelicPoint_components_atPlaces_lattices_vacua D (fun _ => True)
  obtain ⟨x, hx, u, hu, rfl⟩ := (hS S).1 g
  refine ⟨x, GlobalTheory.GlobFin.mem_GfC hx, fun P y hy => ?_⟩
  have hy0 : ∀ j, y j ∈ idAt D (fun _ => True) := by
    intro j
    refine Ideal.mem_inf.mpr ⟨(Ideal.mem_inf.mp (hy j)).1, ?_⟩
    simp only [Submodule.mem_iInf]
    intro w
    exact absurd trivial w.2
  have hu1 : Formalism.L2.Theta.mt S u *ᵥ y = y := by
    funext i
    have hz : ∀ j, (Formalism.L2.Theta.mt S u i j - (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) i j) * y j = 0 := by
      intro j
      have ha := (hOff _).mp (GlobalTheory.GlobFin.cong_entry hu i j)
      have hb := (hAt _).mp (hy0 j)
      calc (Formalism.L2.Theta.mt S u i j - (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) i j) * y j
          = (Formalism.L2.Theta.mt S u i j - (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) i j) * (ε * y j) := by rw [hb]
        _ = (ε * (Formalism.L2.Theta.mt S u i j - (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) i j)) * y j := by ring
        _ = 0 := by rw [ha, zero_mul]
    have hsum : ((Formalism.L2.Theta.mt S u - 1) *ᵥ y) i = 0 := by
      simp only [Matrix.mulVec, dotProduct, Matrix.sub_apply]
      exact Finset.sum_eq_zero fun j _ => hz j
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply, sub_eq_zero] at hsum
    exact hsum
  rw [mt_mul, ← Matrix.mulVec_mulVec, hu1]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsHaarCovolumeOneSkewHermitianAdelicStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_haar_covolume_one_skewHermitian_adelic : ∀ (D : D7) (ρ : ℕ), ∃ (lC : Measure (skewA D ρ)) (𝓒 : Set (skewA D ρ)), lC.IsAddHaarMeasure ∧ SFinite lC ∧ IsAddFundamentalDomain ((ratMx D ρ ρ).addSubgroupOf (skewA D ρ)) 𝓒 lC ∧ lC 𝓒 = 1 := by
  first | exact @GlobalTheory.SkewVol.exists_haar_covol_one | exact GlobalTheory.SkewVol.exists_haar_covol_one | (intros; apply GlobalTheory.SkewVol.exists_haar_covol_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIntegerOfRelativeTraceNormIntegralStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl IsDedekindDomain NumberField GlobalTheory.FixedUnitNorm
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integer_of_relative_trace_norm_integral : ∀ (D : D7) (w : D.host.E) (t n : 𝓞 D.host.F), w + D.sp.cm.sig w = algebraMap D.host.F D.host.E t → w * D.sp.cm.sig w = algebraMap D.host.F D.host.E n → ∃ x : 𝓞 D.host.E, (x : D.host.E) = w := by
  first | exact @GlobalTheory.FixedUnitNorm.integral_of_trace_norm_integral | exact GlobalTheory.FixedUnitNorm.integral_of_trace_norm_integral | (intros; apply GlobalTheory.FixedUnitNorm.integral_of_trace_norm_integral <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIntegralAdeleAtPlaceWithComponent
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl IsDedekindDomain NumberField GlobalTheory.FixedUnitNorm
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.FixedUnitNorm

theorem evalAtPlace_singleAtPlace_self (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (y : Fv F v) :
    evalV F v (singleV F v y) = y := by
  classical
  exact RestrictedProduct.single_eq_same (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) v y

theorem evalAtPlace_singleAtPlace_of_ne (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (y : Fv F v)
    {w : HeightOneSpectrum (𝓞 F)} (hw : w ≠ v) : evalV F w (singleV F v y) = 0 := by
  classical
  exact RestrictedProduct.single_eq_of_ne (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) y hw

theorem exists_integralAdele_atPlace_component_tmul (D : D7) (v : Pl D) (a : Fv D.host.F v) (ha : a ∈ v.adicCompletionIntegers D.host.F)
    (x : 𝓞 D.host.E) : ∃ y ∈ intAt D (· = v), compAt D v y = a ⊗ₜ[D.host.F] (x : D.host.E) := by
  have hc : ∀ w : Pl D, compAt D w (pairA D.host.F 0 (singleV D.host.F v a) ⊗ₜ[D.host.F] (x : D.host.E)) =
      evalV D.host.F w (singleV D.host.F v a) ⊗ₜ[D.host.F] (x : D.host.E) := by
    intro w
    change Algebra.TensorProduct.map (evalV D.host.F w) (AlgHom.id D.host.F D.host.E)
      (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)
        (pairA D.host.F 0 (singleV D.host.F v a) ⊗ₜ[D.host.F] (x : D.host.E))) = _
    rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul]
    rfl
  refine ⟨pairA D.host.F 0 (singleV D.host.F v a) ⊗ₜ[D.host.F] (x : D.host.E), ⟨?_, ?_⟩, ?_⟩
  · rw [mem_supportedOnPlacesIdeal_iff_components_zero_elsewhere]
    refine ⟨?_, fun w hw => ?_⟩
    · change Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E)
        (pairA D.host.F 0 (singleV D.host.F v a) ⊗ₜ[D.host.F] (x : D.host.E)) = 0
      rw [Algebra.TensorProduct.map_tmul]
      exact TensorProduct.zero_tmul _ _
    · rw [hc, evalAtPlace_singleAtPlace_of_ne _ v a hw, TensorProduct.zero_tmul]
  · change Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)
      (pairA D.host.F 0 (singleV D.host.F v a) ⊗ₜ[D.host.F] (x : D.host.E)) ∈ intAE D
    rw [Algebra.TensorProduct.map_tmul]
    refine AddSubgroup.subset_closure ⟨singleV D.host.F v a, fun w => ?_, x, rfl⟩
    by_cases hw : w = v
    · subst hw; rw [evalAtPlace_singleAtPlace_self]; exact ha
    · rw [evalAtPlace_singleAtPlace_of_ne _ v a hw]; exact zero_mem _
  · rw [hc, evalAtPlace_singleAtPlace_self]

theorem exists_intAt_compAt_eq : ∀ (D : D7) (v : Pl D) (z : Fv D.host.F v ⊗[D.host.F] D.host.E), z ∈ intV D v →
    ∃ x ∈ intAt D (· = v), compAt D v x = z := by
  intro D v z hz
  induction hz using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨a, ha, x, rfl⟩ := hy
    exact exists_integralAdele_atPlace_component_tmul D v a ha x
  | zero =>
    exact ⟨0, ⟨zero_mem _, by rw [map_zero]; exact zero_mem _⟩, map_zero _⟩
  | add y z _ _ h1 h2 =>
    obtain ⟨a, ha, hya⟩ := h1
    obtain ⟨b, hb, hzb⟩ := h2
    exact ⟨a + b, GlobalTheory.IwaPlace.SdComap.intAt_add ha hb, by rw [RingHom.map_add, hya, hzb]⟩
  | neg y _ h =>
    obtain ⟨a, ha, hya⟩ := h
    exact ⟨-a, ⟨neg_mem ha.1, by rw [RingHom.map_neg]; exact neg_mem ha.2⟩, by rw [RingHom.map_neg, hya]⟩

end GlobalTheory.FixedUnitNorm

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIntegralTraceIdempotentAtTamePlaceStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.IwaPlace Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_trace_idempotent_at_tamePlace : ∀ (D : D7) (v : Pl D) (ε : AE D) (hεε : ε * ε = ε) (hεc : cA D ε = ε) (hεI : ε ∈ intAt D (· = v)) (hε : ∀ a, a ∈ idAt D (· = v) ↔ ε * a = a), Tame D v → ∃ w ∈ intAt D (· = v), w + cA D w = ε := by
  first | exact @GlobalTheory.IwaPlace.exists_trace_one_at_tame | exact GlobalTheory.IwaPlace.exists_trace_one_at_tame | (intros; apply GlobalTheory.IwaPlace.exists_trace_one_at_tame <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIsotropicDualColumnsSelfDualLatticeAtPlaceStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.IwaPlace Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isotropic_dual_columns_selfDualLatticeAtPlace : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (v : Pl D) (ε : AE D) (hεε : ε * ε = ε) (hεc : cA D ε = ε) (hεI : ε ∈ intAt D (· = v)) (hε : ∀ a, a ∈ idAt D (· = v) ↔ ε * a = a) (M : AddSubgroup (Fin S.rank → AE D)), IsSDAt S v M → ∀ w ∈ intAt D (· = v), w + cA D w = ε → ∀ (b : Mx D ρ ρ) (c' : Mx D S.rank ρ), (∀ i j, b i j ∈ idAt D (· = v)) → (∀ i, (fun k => (d.jX ⬝ b) k i) ∈ M) → (∀ i, (fun k => c' k i) ∈ M) → adj c' ⬝ (gA S ⬝ (d.jX ⬝ b)) = ε • (1 : Mx D ρ ρ) → ∃ c'' : Mx D S.rank ρ, (∀ i, (fun k => c'' k i) ∈ M) ∧ adj c'' ⬝ (gA S ⬝ (d.jX ⬝ b)) = ε • (1 : Mx D ρ ρ) ∧ adj c'' ⬝ (gA S ⬝ c'') = 0 := by
  first | exact @GlobalTheory.IwaPlace.DualIso.dual_isotropic | exact GlobalTheory.IwaPlace.DualIso.dual_isotropic | (intros; apply GlobalTheory.IwaPlace.DualIso.dual_isotropic <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsMaxCompactRealPointsOfOrthonormalFrames
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory GlobalTheory.AutFinLit GlobalTheory.Published.AutFin
open GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies (LieAt LieInf atPlace IsExpFam IsSmoothInf wordDer)
open scoped TensorProduct DirectSum Classical

noncomputable section

namespace GlobalTheory.FrameCompact

open GlobalTheory.SmoothForms Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D}
  {ε : D.what₂.Tau → Fin V.rank → Bool} {fr : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ}

def comps (fr : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (k : ∀ τ, Formalism.REAL.KG (ε τ)) : AlgInf V :=
  fun τ => (fr τ)⁻¹ * Formalism.REAL.toMK (k τ) * fr τ

theorem comps_unit (R : RealPoints θ V) (h : IsFrameFam V ε fr) (k : ∀ τ, Formalism.REAL.KG (ε τ)) :
    sigInf V (comps fr k) * comps fr k = 1 :=
  (unit_iff R _).2 fun τ => conj_mem_UH (h τ).1 (h τ).2 (k τ)

theorem continuous_comps : Continuous (comps (ε := ε) fr) := by
  have key : Continuous fun (k : ∀ τ, Formalism.REAL.KG (ε τ)) (τ : D.what₂.Tau) =>
      (fr τ)⁻¹ * Formalism.REAL.toMK (k τ) * fr τ := by
    refine continuous_pi fun τ => ?_
    have h1 : Continuous fun k : Formalism.REAL.KG (ε τ) => Formalism.REAL.toMK k :=
      (Formalism.REAL.isClosedEmbeddingMatrix _ (ε τ)).1.continuous.comp continuous_subtype_val
    exact (continuous_const.matrix_mul (h1.comp (continuous_apply τ))).matrix_mul continuous_const
  exact key

def frameHom (R : RealPoints θ V) (h : IsFrameFam V ε fr) : (∀ τ, Formalism.REAL.KG (ε τ)) →* GA D V :=
  MonoidHom.mk' (fun k => secInf θ V (comps fr k)) fun k l => by
    have a := secInf_spec R (comps_unit R h k)
    have b := secInf_spec R (comps_unit R h l)
    have c := secInf_spec R (comps_unit R h (k * l))
    refine R.2.2.1 _ c.1 _ (mul_mem a.1 b.1) fun τ => ?_
    have hd : IsUnit (fr τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (h τ).1
    rw [R.2.2.2.1, c.2, a.2, b.2]
    change (fr τ)⁻¹ * (Formalism.REAL.toMK (k τ) * Formalism.REAL.toMK (l τ)) * fr τ =
      (fr τ)⁻¹ * Formalism.REAL.toMK (k τ) * fr τ * ((fr τ)⁻¹ * Formalism.REAL.toMK (l τ) * fr τ)
    simp only [Matrix.mul_assoc]
    rw [mul_nonsing_inv_cancel_left _ _ hd]

theorem frameHom_spec (R : RealPoints θ V) (h : IsFrameFam V ε fr) (k : ∀ τ, Formalism.REAL.KG (ε τ)) :
    frameHom R h k ∈ GinfC V ∧ ∀ τ, infMat D.sp.cm.sig V.gram (θ τ) (frameHom R h k) =
      (fr τ)⁻¹ * Formalism.REAL.toMK (k τ) * fr τ :=
  secInf_spec R (comps_unit R h k)

theorem frameHom_single (hθ : IsInfFam θ) (R : RealPoints θ V) (h : IsFrameFam V ε fr) (τ : D.what₂.Tau)
    (k : Formalism.REAL.KG (ε τ)) : frameHom R h (Pi.mulSingle τ k) = kAt θ V τ (ε τ) (fr τ) k := by
  have a := frameHom_spec R h (Pi.mulSingle τ k)
  have b := isAtTau_kAt θ V hθ τ (h τ).1 (h τ).2 k
  refine R.2.2.1 _ a.1 _ b.1 fun τ' => ?_
  rw [a.2]
  by_cases c : τ' = τ
  · subst c
    rw [b.2.1, Pi.mulSingle_eq_same]
  · rw [b.2.2 _ c, Pi.mulSingle_eq_of_ne c]
    change (fr τ')⁻¹ * 1 * fr τ' = 1
    rw [Matrix.mul_one, nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 (h τ').1)]

theorem isCompact_frameRange (hθ : IsInfFam θ) (R : RealPoints θ V) (h : IsFrameFam V ε fr) :
    IsCompact ((frameHom R h).range : Set (GA D V)) := by
  have hc : Continuous (frameHom R h) :=
    (GlobalTheory.Mem.DerClosed.continuousOn_secInf hθ V).comp_continuous continuous_comps (comps_unit R h)
  rw [MonoidHom.coe_range]
  exact _root_.isCompact_range hc

theorem conj_mem_Kset (hθ : IsInfFam θ) (R : RealPoints θ V) (h : IsFrameFam V ε fr) (K' : Subgroup (GA D V))
    (hc : IsCompact (K' : Set (GA D V))) (hle : (frameHom R h).range ≤ K') (τ : D.what₂.Tau) {g : GA D V}
    (hg : g ∈ K') : fr τ * infMat D.sp.cm.sig V.gram (θ τ) g * (fr τ)⁻¹ ∈ Formalism.REAL.Kset (ε τ) := by
  have hd : IsUnit (fr τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (h τ).1
  let f : GA D V → Matrix (Fin V.rank) (Fin V.rank) ℂ :=
    fun g => fr τ * infMat D.sp.cm.sig V.gram (θ τ) g * (fr τ)⁻¹
  have fc : Continuous f :=
    (continuous_const.matrix_mul (GlobalTheory.Mem.VolExists.continuous_infMat V.gram (hθ τ))).matrix_mul continuous_const
  have fm : ∀ a b, f (a * b) = f a * f b := fun a b => by
    simp only [f, R.2.2.2.1, Matrix.mul_assoc]
    rw [nonsing_inv_mul_cancel_left _ _ hd]
  have fk : ∀ k, f (frameHom R h k) = Formalism.REAL.toMK (k τ) := fun k => by
    simp only [f, (frameHom_spec R h k).2, Matrix.mul_assoc]
    rw [mul_nonsing_inv_cancel_left _ _ hd, mul_nonsing_inv _ hd, Matrix.mul_one]
  have f1 : f 1 = 1 := by
    rw [← map_one (frameHom R h), fk]
    rfl
  have key := GlobalTheory.T.bounded_subgroup_of_indefinite_unitary_eq_maximalCompact V.rank (ε τ) (f '' K') ?_ ?_ ?_ ?_ ?_
  · rw [← key]
    exact ⟨g, hg, rfl⟩
  · rintro _ ⟨a, -, rfl⟩
    have hu : (infMat D.sp.cm.sig V.gram (θ τ) a)ᴴ * gramAt D V τ * infMat D.sp.cm.sig V.gram (θ τ) a = gramAt D V τ :=
      GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V a τ
    have h1 : ((fr τ)⁻¹)ᴴ * (fr τ)ᴴ = 1 := by rw [← conjTranspose_mul, mul_nonsing_inv _ hd, conjTranspose_one]
    change (f a)ᴴ * Formalism.REAL.Jm (ε τ) * f a = Formalism.REAL.Jm (ε τ)
    calc (f a)ᴴ * Formalism.REAL.Jm (ε τ) * f a
        = ((fr τ)⁻¹)ᴴ * ((infMat D.sp.cm.sig V.gram (θ τ) a)ᴴ * ((fr τ)ᴴ * Formalism.REAL.Jm (ε τ) * fr τ) *
            infMat D.sp.cm.sig V.gram (θ τ) a) * (fr τ)⁻¹ := by
          simp only [f, conjTranspose_mul, Matrix.mul_assoc]
      _ = (((fr τ)⁻¹)ᴴ * (fr τ)ᴴ) * Formalism.REAL.Jm (ε τ) * (fr τ * (fr τ)⁻¹) := by
          rw [(h τ).2, hu, ← (h τ).2]
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [h1, mul_nonsing_inv _ hd, Matrix.one_mul, Matrix.mul_one]
  · rw [← Formalism.REAL.range_toMK]
    rintro _ ⟨k, rfl⟩
    refine ⟨frameHom R h (Pi.mulSingle τ k), hle ⟨_, rfl⟩, ?_⟩
    rw [fk, Pi.mulSingle_eq_same]
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    exact ⟨a * b, mul_mem ha hb, fm a b⟩
  · rintro _ ⟨a, ha, rfl⟩
    refine ⟨a⁻¹, inv_mem ha, (inv_eq_left_inv ?_).symm⟩
    rw [← fm, inv_mul_cancel, f1]
  · have : ∀ i j, ∃ C : ℝ, ∀ a ∈ K', ‖f a i j‖ ≤ C := fun i j =>
      hc.exists_bound_of_continuousOn (fc.matrix_elem i j).continuousOn
    choose C hC using this
    obtain ⟨B, hB⟩ := (Set.finite_range fun p : Fin V.rank × Fin V.rank => C p.1 p.2).bddAbove
    refine ⟨B, ?_⟩
    rintro _ ⟨a, ha, rfl⟩ i j
    exact (hC i j a ha).trans (hB ⟨(i, j), rfl⟩)

theorem isMaxCompactInf_range (hθ : IsInfFam θ) (R : RealPoints θ V) (h : IsFrameFam V ε fr) :
    IsMaxCompactInf V (frameHom R h).range := by
  refine ⟨?_, isCompact_frameRange hθ R h, fun K' hi hc hle => le_antisymm (fun g hg => ?_) hle⟩
  · rintro _ ⟨k, rfl⟩
    exact (frameHom_spec R h k).1
  · have : ∀ τ, ∃ k : Formalism.REAL.KG (ε τ),
        Formalism.REAL.toMK k = fr τ * infMat D.sp.cm.sig V.gram (θ τ) g * (fr τ)⁻¹ := fun τ => by
      have := conj_mem_Kset hθ R h K' hc hle τ hg
      rw [← Formalism.REAL.range_toMK] at this
      exact this
    choose k hk using this
    refine ⟨k, R.2.2.1 _ (frameHom_spec R h k).1 _ (hi g hg) fun τ => ?_⟩
    have hd : IsUnit (fr τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (h τ).1
    rw [(frameHom_spec R h k).2, hk]
    simp only [Matrix.mul_assoc]
    rw [nonsing_inv_mul_cancel_left _ _ hd, nonsing_inv_mul _ hd, Matrix.mul_one]

theorem exists_maxCompact_of_frames : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ → ∀ (V : HSp D), ∀ (ε : D.what₂.Tau → Fin V.rank → Bool) (fr : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ), IsFrameFam V ε fr → ∃ K : Subgroup (GA D V), IsMaxCompactInf V K ∧ (∃ j : (∀ τ, Formalism.REAL.KG (ε τ)) →* K, Function.Surjective j ∧ ∀ τ k, (j (Pi.mulSingle τ k) : GA D V) = kAt θ V τ (ε τ) (fr τ) k) := by
  intro D θ hθ V ε fr h
  have R := (GlobalTheory.SmoothForms.RealPts.realPoints D).2 θ hθ V
  exact ⟨(frameHom R h).range, isMaxCompactInf_range hθ R h, (frameHom R h).rangeRestrict,
    (frameHom R h).rangeRestrict_surjective, fun τ k => frameHom_single hθ R h τ k⟩

end GlobalTheory.FrameCompact

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNatMulSplitHalfLatticeCoordinatesIntegralStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.FinPl
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nat_mul_splitHalf_latticeCoordinates_integral : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (S T : HSp D) (α : Frame p S n') (β : Frame p T n) (LS : Lat S) (LT : Lat T), IsSelfDualC S LS → IsSelfDualC T LT → ∃ N : ℕ, 0 < N ∧ ∀ u ∈ latO S T (LS : Set _) (LT : Set _) (· = p.v), IsHalf p.e u → ∀ i j, (N : k) * rd α β u i j ∈ 𝒪[k] := by
  first | exact @GlobalTheory.FinPl.RdBound.exists_nat_mul_rd_mem | exact GlobalTheory.FinPl.RdBound.exists_nat_mul_rd_mem | (intros; apply GlobalTheory.FinPl.RdBound.exists_nat_mul_rd_mem <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsOpenAddSubgroupFinitePointsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_openAddSubgroup_finite_points_alt : ∀ (D : D7) (V : Set (AE D)), V ∈ nhds (0 : AE D) → ∃ U : AddSubgroup (AE D), IsOpen (U : Set (AE D)) ∧ ∀ a ∈ U, infPart D a = 0 → a ∈ V := by
  first | exact @GlobalTheory.FinSubgroup.exists_openAddSubgroup_finite_points | exact GlobalTheory.FinSubgroup.exists_openAddSubgroup_finite_points | (intros; apply GlobalTheory.FinSubgroup.exists_openAddSubgroup_finite_points <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsPadicCoordinatesOfDegreeOneSplitPlace
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl ValuativeRel NumberField
open IsDedekindDomain
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.FinPl.SplitQT

open GlobalTheory.IdemModTwo GlobalTheory.SplitIdem GlobalTheory.SplitChart GlobalTheory.SplitHecke

def intEquiv (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    v.adicCompletionIntegers F ≃+* 𝒪[Fv F v] where
  toFun x := ⟨x.1, (GlobalTheory.FinPl.SplitPoint.mem_integer_iff F v x.1).2 x.2⟩
  invFun y := ⟨y.1, (GlobalTheory.FinPl.SplitPoint.mem_integer_iff F v y.1).1 y.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

theorem exists_coord_padic : ∀ (D : D7) (T : ℕ) [Fact T.Prime] (w : Formalism.L2.DIV.Pl D.host.E) (e : AE D), Formalism.L2.NTheta.IsIdemAt e w → IsSplitIdem D e → Ideal.absNorm w.asIdeal = T → ¬ (w.asIdeal ^ 2 ∣ Ideal.span {(T : 𝓞 D.host.E)}) → ∃ (v : Pl D) (pr : AE D →+* ℚ_[T]) (sec : ℚ_[T] →+ AE D), (∃ ε, IsPlaceIdem D v ε ∧ e + cA D e = algebraMap (AF D.host.F) (AE D) ε) ∧ (∀ a, pr (sec a) = a) ∧ (∀ x, sec (pr x) = e * x) ∧ Continuous pr ∧ Continuous sec ∧ ∀ a, ‖a‖ ≤ 1 ↔ finPart D (sec a) ∈ intAE D := by
  intro D T _ w e hw hs hT hT2
  obtain ⟨_, _, v, ε, hε, he⟩ := id hs
  have hsa : SplitAt D v e := GlobalTheory.FinPl.SplitPoint.splitAt_of hs hε he
  have hch : Chart e v (comp hsa) := chart_comp hsa
  have hTw : ((T : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal := by
    have := Ideal.absNorm_mem w.asIdeal
    rwa [hT] at this
  have hTw2 : ((T : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal ^ 2 := fun h =>
    hT2 (Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 h))
  obtain ⟨⟨p, hp, hirr⟩, hcard⟩ := GlobalTheory.SplitUnif.unif_chart e w v (comp hsa) hw hch _ hTw hTw2
  have hpT : p = (T : Ov D v) := by
    apply Subtype.ext
    rw [show ((p : Fv D.host.F v)) = algebraMap (Ov D v) (Fv D.host.F v) p from rfl, hp]
    simp
  subst hpT
  haveI : CharZero (Fv D.host.F v) :=
    charZero_of_injective_ringHom (algebraMap D.host.F (v.adicCompletion D.host.F)).injective
  have hc1 : Nat.card (IsLocalRing.ResidueField 𝒪[Fv D.host.F v]) = T := by
    rw [← hT, ← hcard]
    exact (Nat.card_congr (IsLocalRing.ResidueField.mapEquiv (intEquiv D.host.F v)).toEquiv).symm
  have hc2 : Irreducible (T : 𝒪[Fv D.host.F v]) := by
    rw [← map_natCast (intEquiv D.host.F v) T]
    exact (MulEquiv.irreducible_iff (intEquiv D.host.F v).toMulEquiv).2 hirr
  obtain ⟨φ, hφ, hφ', hφO⟩ := GlobalTheory.T.exists_ringEquiv_padic_of_residueCard_uniformizer (Fv D.host.F v) T hc1 hc2
  obtain ⟨sp, hse, -⟩ := GlobalTheory.FinPl.SplitPoint.exists_splitPt D v e ε hs hε he
  refine ⟨v, φ.symm.toRingHom.comp sp.pr, sp.sec.comp φ.toRingHom.toAddMonoidHom, ⟨ε, hε, he⟩,
    fun a => ?_, fun x => ?_, hφ'.comp sp.cont_pr, sp.cont_sec.comp hφ, fun a => ?_⟩
  · change φ.symm (sp.pr (sp.sec (φ a))) = a
    rw [sp.pr_sec, RingEquiv.symm_apply_apply]
  · change sp.sec (φ (φ.symm (sp.pr x))) = e * x
    rw [RingEquiv.apply_symm_apply, sp.sec_pr, hse]
  · exact (hφO a).symm.trans (sp.int_iff (φ a))

end GlobalTheory.FinPl.SplitQT

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsPlace
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil ValuativeRel GlobalTheory.LocMod

namespace GlobalTheory.PlaceOfIdem

open GlobalTheory.IdemModTwo GlobalTheory.SplitChart GlobalTheory.SplitIdem

theorem exists_place : ∀ (D : D7) (e : Formalism.L2.Theta.AE D), IsSplitIdem D e →
    ∃ (k : Type) (_ : Field k) (_ : ValuativeRel k) (_ : TopologicalSpace k) (_ : IsNonarchimedeanLocalField k)
      (p : Place D k), p.e = e := by
  intro D e h
  obtain ⟨v, he⟩ := (isSplitIdem_iff e).1 h
  let := GlobalTheory.LocalData.complRel v
  have := GlobalTheory.LocalData.isLocalField v
  have : IsModuleTopology (AF D.host.F) (Formalism.L2.Theta.AE D) := ⟨rfl⟩
  have : IsTopologicalRing (Formalism.L2.Theta.AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) _
  have hev : Continuous (evalV D.host.F v) := RestrictedProduct.continuous_eval v
  have hal : Continuous (algebraMap (AF D.host.F) (Formalism.L2.Theta.AE D)) :=
    IsModuleTopology.continuous_of_linearMap (Algebra.linearMap (AF D.host.F) (Formalism.L2.Theta.AE D))
  have hp : Continuous fun a : Fv D.host.F v => pairA D.host.F 0 (singleV D.host.F v a) :=
    Continuous.prodMk continuous_const (GlobalTheory.LocalComponentChar.continuous_singleV D.host.F v)
  refine ⟨v.adicCompletion D.host.F, inferInstance, inferInstance, inferInstance, inferInstance,
    { e := e
      split := h
      π := comp he
      ι := AddMonoidHom.ofMapSub (fun a => fj D (singleV D.host.F v a) * e) fun a b => by
        rw [singleV_sub, map_sub, sub_mul]
      π_ι := fun x => ?_
      ι_π := fun a => (sc_spec he a).symm
      cont_π := ?_
      cont_ι := (hal.comp hp).mul continuous_const }, rfl⟩
  · show comp he (fj D (singleV D.host.F v x) * e) = x
    rw [map_mul, comp_fj, comp_self, evalV_singleV_same, mul_one]
  · refine IsModuleTopology.continuous_of_ringHom (R := AF D.host.F) (comp he) ?_
    have : ⇑((comp he).comp (algebraMap (AF D.host.F) (Formalism.L2.Theta.AE D))) = fun y => evalV D.host.F v y.2 :=
      funext (comp_algebraMap he)
    rw [this]
    exact hev.comp continuous_snd

end GlobalTheory.PlaceOfIdem
end
end

