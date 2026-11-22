import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0572
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0556
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.AdelicGaussians.UpperRightUnipotentInvariance
import GroundTheory.AutomorphicForms.ReductionFinite
import GroundTheory.AutomorphicForms.ReductionMahler
import GroundTheory.AutomorphicForms.ReductionSiegel
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0543
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0557
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsHeight
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.DecayUniform
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.GKStable
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0515
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0915
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0522
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecondCountableHermC
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0544
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0505
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.UnramifiedSchwartzDensity.SchCut
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0024
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0026
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0040
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0539
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0005
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0014
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0560

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ActWOneApply
section
noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Unf

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep

variable {F E : Type} [Field F] [Field E] [Algebra F E]

section Stab

variable (R : Type) [CommRing R] [Algebra F R]

theorem actW_mul_apply (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E) (g h : HA R σ J)
    (X : Fin n → Fin M → R ⊗[F] E) :
    actW R σ J (g * h) X = actW R σ J g (actW R σ J h X) := by
  funext a
  change ((HA.mat R σ J g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) *
      (HA.mat R σ J h : Matrix (Fin M) (Fin M) (R ⊗[F] E))) *ᵥ X a =
    (HA.mat R σ J g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) *ᵥ
      ((HA.mat R σ J h : Matrix (Fin M) (Fin M) (R ⊗[F] E)) *ᵥ X a)
  rw [Matrix.mulVec_mulVec]

theorem actW_one_apply (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (X : Fin n → Fin M → R ⊗[F] E) : actW R σ J 1 X = X := by
  funext a
  change (1 : Matrix (Fin M) (Fin M) (R ⊗[F] E)) *ᵥ X a = X a
  exact Matrix.one_mulVec _

def stabilizer₂ (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) : Subgroup (HA R σ (hypOne J)) where
  carrier := {h | actW R σ (hypOne J) h (e0 _ M) = e0 _ M}
  one_mem' := actW_one_apply R σ (hypOne J) _
  mul_mem' := by
    intro g h hg hh
    change actW R σ (hypOne J) (g * h) (e0 _ M) = e0 _ M
    rw [actW_mul_apply, show actW R σ (hypOne J) h (e0 _ M) = e0 _ M from hh]
    exact hg
  inv_mem' := by
    intro g hg
    change actW R σ (hypOne J) g⁻¹ (e0 _ M) = e0 _ M
    have hg' : actW R σ (hypOne J) g (e0 _ M) = e0 _ M := hg
    conv_lhs => rw [← hg']
    rw [← actW_mul_apply, inv_mul_cancel, actW_one_apply]

def ratP (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) : Subgroup (stabilizer₂ R σ J) :=
  Subgroup.comap (stabilizer₂ R σ J).subtype
    (show Subgroup (HA R σ (hypOne J)) from HFinIn R σ (hypOne J))

end Stab

def framesOne (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (n : ℕ) :
    Set (Fin (n + 1) → Fin (M + 2) → E) :=
  {X | X ∈ framesE σ (hypOne J) (0 : Matrix (Fin (n + 1)) (Fin (n + 1)) E) ∧ X 0 = e0 E M 0}

end GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Unf
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdelicNormRatVectorBoundStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm Ad3 Ad3.GA
open scoped NumberField.AdeleRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelic_norm_rat_vector_bound : ∀ M : ℕ, 0 < M → ∀ z : Fin 3 → ℚ, (∀ i, ∃ k : ℤ, (M : ℚ) * z i = k) → Reduction.adelicNorm (Reduction.ratVec z : Fin 3 → 𝔸[ℚ]) ≤ M * ∑ i, |((z i : ℚ) : ℝ)| := by
  first | exact @GlobalTheory.CompanionTheory.MajHeight.adelicNorm_ratVec_le | exact GlobalTheory.CompanionTheory.MajHeight.adelicNorm_ratVec_le | (intros; apply GlobalTheory.CompanionTheory.MajHeight.adelicNorm_ratVec_le <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdelicVectorIntegralProductStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter GlobalTheory.CuspGeneric GlobalTheory.CuspRep PositivityTheory.jumpWindows PositivityTheory.AdelicQuotientData GroundTheory.Automorphic.FourierWhittaker GlobalTheory.CompanionTheory.CutOff
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelic_vector_integral_product : ∀ {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {k : ℕ} (A : (Fin k → Cinf E) → ℂ) (B : (Fin k → Af E) → ℂ), ∫ y, A (fun i => pInf E (y i)) * B (fun i => pFin E (y i)) ∂vecMeasure E (Fin k) = (∫ x, A x ∂nuInf E k) * ∫ f, B f ∂nuFin E k := by
  first | exact @GlobalTheory.CompanionTheory.CutOff.Split.integral_split | exact GlobalTheory.CompanionTheory.CutOff.Split.integral_split | (intros; apply GlobalTheory.CompanionTheory.CutOff.Split.integral_split <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AnnihilatorAdelicLatticeCompactStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter GlobalTheory.CuspGeneric GlobalTheory.CuspRep PositivityTheory.jumpWindows PositivityTheory.AdelicQuotientData GroundTheory.Automorphic.FourierWhittaker GlobalTheory.CompanionTheory.CutOff
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.annihilator_adelic_lattice_compact : ∀ {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {ψ : AddChar (Ad E) ℂ}, StdPsi ψ → ∀ (S : Finset (Pl E)), (∀ w, w ∉ S → Cond ψ w) → ∀ (L : Set (Af E)), (∀ w, w ∉ S → ∀ t ∈ Formalism.UG.Ov E w, sLoc E w t ∈ L) → (∀ w ∈ S, ∃ N ∈ 𝓝 (0 : w.adicCompletion E), ∀ t ∈ N, sLoc E w t ∈ L) → ∃ C : Set (Af E), IsCompact C ∧ ∀ z : Af E, (∀ a ∈ L, ψ (sFin E (a * z)) = 1) → z ∈ C := by
  first | exact @GlobalTheory.CompanionTheory.AnnLattice.exists_isCompact_annihilator | exact GlobalTheory.CompanionTheory.AnnLattice.exists_isCompact_annihilator | (intros; apply GlobalTheory.CompanionTheory.AnnLattice.exists_isCompact_annihilator <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchLieDerivativeExistsStatement
section
open NumberField GlobalTheory.CuspRep GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
open scoped NumberField.AdeleRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arch_lie_derivative_exists : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (φ : Sm E a) (hs : φ.1 ∈ AutomorphicForm.archSmooth E a), IsAutForm φ → (∀ [MeasurableSpace (AutomorphicForm.archGroup E a)] [BorelSpace (AutomorphicForm.archGroup E a)]
    (μ : MeasureTheory.Measure (AutomorphicForm.archGroup E a)) [μ.IsHaarMeasure]
    (k : ℕ) (J : Fin k → Fin (CuspidalSpectrum.archDim E a)),
    ∃ D : AutomorphicForm.archGroup E a → ℂ, Continuous D ∧ HasCompactSupport D ∧ ∀ g : AdelicGLn.AdelicGL E a,
      ((AutomorphicForm.uAction (CuspidalSpectrum.uJ (K := E) (n := a) k J) (⟨φ.1, hs⟩ : ↥(AutomorphicForm.archSmooth E a)) :
        ↥(AutomorphicForm.archSmooth E a)) : AdelicGLn.AdelicGL E a → ℂ) g = ∫ y, φ.1 (g * AutomorphicForm.infEmb E a y) * D y ∂μ) := by
  first | exact @GlobalTheory.CompanionTheory.HCRep.uJ_eq_conv | exact GlobalTheory.CompanionTheory.HCRep.uJ_eq_conv | (intros; apply GlobalTheory.CompanionTheory.HCRep.uJ_eq_conv <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanCharacterInCoordinatesStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch NumberField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_character_in_coordinates : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
  (ρ : InfinitePlace F → (F →+* ℝ)) (e : Ainf F ≃+* (InfinitePlace F → ℝ)) (τ : InfinitePlace F → (E →+* ℂ))
  (Θ : Ainf F ⊗[F] E ≃+* (InfinitePlace F → ℂ)), IsCoord σ e τ Θ →
  (∀ x w, e (algebraMap F (Ainf F) x) w = ρ w x) →
  ∀ (a : F) (ψ : AddChar (AF F) ℂ),
  (∀ x : Ainf F, ψ (pairA F x 0) = Complex.exp (2 * Real.pi * Complex.I * ((∑ w, ρ w a * e x w : ℝ) : ℂ))) →
  ∀ (M n : ℕ) (J : Matrix (Fin M) (Fin M) E) (B : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E))
    (X : Fin n → Fin M → Ainf F ⊗[F] E),
  psiInf F ψ (algebraMap F (Ainf F) (1 / 2) * Algebra.trace (Ainf F) (Ainf F ⊗[F] E)
      (Matrix.trace (B * gramR (Ainf F) σ J X))) =
    Complex.exp (2 * Real.pi * Complex.I * ((phaseM (fun w => ((ρ w a : ℝ) : ℂ) • J.map (τ w))
      (fun w => matC Θ B w) (tupC Θ X) : ℝ) : ℂ)) := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.PhaseCoord.psiInf_phase | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.PhaseCoord.psiInf_phase | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.PhaseCoord.psiInf_phase <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanCharacterRealPairingStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter GlobalTheory.CuspGeneric GlobalTheory.CuspRep PositivityTheory.jumpWindows PositivityTheory.AdelicQuotientData GroundTheory.Automorphic.FourierWhittaker GlobalTheory.CompanionTheory.CutOff
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_character_real_pairing : ∀ {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {k : ℕ} {ψ : AddChar (Ad E) ℂ}, S8 → StdPsi ψ → ∃ β : (Fin k → Cinf E) →L[ℝ] (Fin k → Cinf E) →L[ℝ] ℝ, (∀ y, (∀ x, β x y = 0) → y = 0) ∧ ∀ x z : Fin k → Cinf E, ψ (sInf E (∑ i, x i * z i)) = Complex.exp (-((β x z : ℝ) : ℂ) * Complex.I) := by
  first | exact @GlobalTheory.CompanionTheory.JSPair.exists_pairing | exact GlobalTheory.CompanionTheory.JSPair.exists_pairing | (intros; apply GlobalTheory.CompanionTheory.JSPair.exists_pairing <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanCoordinates
section
noncomputable section

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.CoordR

theorem coordInf : PositivityTheory.PfSWUS.SchInf.CoordInf := by
  intro F E _ _ _ _ _ σ hσ n M
  obtain ⟨-, e, -, he, -⟩ := GlobalTheory.T.infinite_adele_haar_map_eq_scaled_volume F hσ.1
  let eh : Ainf F ≃ₜ (InfinitePlace F → ℝ) := he.homeomorph _
  have heh : ∀ y, eh y = e y := fun _ => rfl
  haveI : SecondCountableTopology (Ainf F) := eh.secondCountableTopology
  haveI : T2Space (Ainf F) := eh.symm.t2Space
  obtain ⟨i1, i2, i3, i4, -, -, hb, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hσ (Ainf F)
  let d := Module.finrank F E
  let b : Module.Basis (Fin d) F E := Module.finBasis F E
  let B := Algebra.TensorProduct.basis (Ainf F) b
  let Hs : (Ainf F ⊗[F] E) ≃ₜ (Fin d → Ainf F) := (hb d b).homeomorph _
  have hHs : ∀ y k, Hs y k = B.repr y k := fun _ _ => rfl
  let I := Fin n × Fin M × Fin d × InfinitePlace F
  let q : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
  let eH : (Fin n → Fin M → Ainf F ⊗[F] E) ≃ₜ (Fin (Fintype.card I) → ℝ) :=
    { toFun := fun X t => eh (Hs (X (q.symm t).1 (q.symm t).2.1) (q.symm t).2.2.1) (q.symm t).2.2.2
      invFun := fun y a j => Hs.symm fun k => eh.symm fun w => y (q (a, j, k, w))
      left_inv := fun X => by simp
      right_inv := fun y => by
        funext t
        simp
      continuous_toFun := continuous_pi fun t =>
        (continuous_apply _).comp (eh.continuous.comp ((continuous_apply _).comp
          (Hs.continuous.comp ((continuous_apply _).comp (continuous_apply _)))))
      continuous_invFun := continuous_pi fun a => continuous_pi fun j =>
        Hs.symm.continuous.comp (continuous_pi fun k => eh.symm.continuous.comp
          (continuous_pi fun w => continuous_apply _)) }
  have hadd : ∀ X Y, eH (X + Y) = eH X + eH Y := by
    intro X Y
    funext t
    change eh (Hs (X _ _ + Y _ _) _) _ = eh (Hs (X _ _) _) _ + eh (Hs (Y _ _) _) _
    simp only [hHs, heh, map_add, Finsupp.add_apply, Pi.add_apply]
  let eV : (Fin n → Fin M → Ainf F ⊗[F] E) ≃+ (Fin (Fintype.card I) → ℝ) :=
    { eH.toEquiv with map_add' := hadd }
  have hV : ∀ X, eV X = eH X := fun _ => rfl
  have hVs : ∀ y, eV.symm y = eH.symm y := fun _ => rfl
  have hc : Continuous fun p : (Fin n → Fin M → Ainf F ⊗[F] E) × Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E) =>
      rmul (Ainf F) p.1 p.2 := by
    refine continuous_pi fun a => continuous_pi fun i => continuous_finset_sum _ fun c _ => ?_
    have h1 : Continuous fun p : (Fin n → Fin M → Ainf F ⊗[F] E) ×
        Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E) => p.1 c i :=
      (continuous_apply i).comp ((continuous_apply c).comp continuous_fst)
    exact h1.mul (continuous_snd.matrix_elem c a)
  have hrad : ∀ (g : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) (X Y : Fin n → Fin M → Ainf F ⊗[F] E),
      rmul (Ainf F) (X + Y) g = rmul (Ainf F) X g + rmul (Ainf F) Y g := by
    intro g X Y
    funext a i
    simp [rmul, add_mul, Finset.sum_add_distrib]
  let L0 : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E) → (Fin (Fintype.card I) → ℝ) →+ (Fin (Fintype.card I) → ℝ) :=
    fun g => AddMonoidHom.mk' (fun y => eV (rmul (Ainf F) (eV.symm y) g)) fun y z => by
      rw [map_add, hrad, map_add]
  have hL0 : ∀ g, Continuous (L0 g) := fun g =>
    eH.continuous.comp (hc.comp (eH.symm.continuous.prodMk continuous_const))
  let L : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E) → (Fin (Fintype.card I) → ℝ) →L[ℝ] (Fin (Fintype.card I) → ℝ) :=
    fun g => (L0 g).toRealLinearMap (hL0 g)
  refine ⟨Fintype.card I, eV, eH.continuous, eH.symm.continuous, L, ?_, ?_⟩
  · refine continuous_clm_apply.2 fun y => ?_
    exact eH.continuous.comp (hc.comp (continuous_const.prodMk continuous_id))
  · intro g X
    change eV _ = eV (rmul (Ainf F) (eV.symm (eV X)) g)
    rw [AddEquiv.symm_apply_apply]

end GlobalTheory.CompanionTheory.SW.CoordR

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanFamilyContinuity
section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace GlobalTheory.CompanionTheory.PushFam

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable [MeasurableSpace E] [BorelSpace E]

lemma decay_comp_of_norm_le (g : E → ℂ) (k : ℕ) (C : ℝ)
    (hC : ∀ y, ‖g y‖ ≤ C * (1 + ‖y‖) ^ (-(k : ℝ))) (K : ℝ) :
    ∃ C' : ℝ, ∀ x y : E, ‖y‖ ≤ K * ‖x‖ → ‖g x‖ ≤ C' * (1 + ‖y‖) ^ (-(k : ℝ)) := by
  refine ⟨max C 0 * (1 + |K|) ^ k, fun x y hxy => ?_⟩
  have hx : 0 ≤ ‖x‖ := norm_nonneg _
  have h2 : 1 + ‖y‖ ≤ (1 + |K|) * (1 + ‖x‖) := by
    have h3 : K * ‖x‖ ≤ |K| * ‖x‖ := mul_le_mul_of_nonneg_right (le_abs_self K) hx
    have h4 : 0 ≤ |K| := abs_nonneg K
    nlinarith
  have h3 : (1 + ‖x‖) ^ (-(k : ℝ)) ≤ (1 + |K|) ^ k * (1 + ‖y‖) ^ (-(k : ℝ)) := by
    rw [Real.rpow_neg (by positivity), Real.rpow_neg (by positivity), Real.rpow_natCast,
      Real.rpow_natCast, ← div_eq_mul_inv, inv_eq_one_div,
      div_le_div_iff₀ (by positivity) (by positivity), one_mul]
    calc (1 + ‖y‖) ^ k ≤ ((1 + |K|) * (1 + ‖x‖)) ^ k := pow_le_pow_left₀ (by positivity) h2 k
      _ = (1 + |K|) ^ k * (1 + ‖x‖) ^ k := mul_pow _ _ _
  calc ‖g x‖ ≤ C * (1 + ‖x‖) ^ (-(k : ℝ)) := hC x
    _ ≤ max C 0 * (1 + ‖x‖) ^ (-(k : ℝ)) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    _ ≤ max C 0 * ((1 + |K|) ^ k * (1 + ‖y‖) ^ (-(k : ℝ))) :=
        mul_le_mul_of_nonneg_left h3 (le_max_right _ _)
    _ = max C 0 * (1 + |K|) ^ k * (1 + ‖y‖) ^ (-(k : ℝ)) := by ring

theorem integrable_continuousAt_clm_comp (m : Measure E) (k : ℕ)
    (hW : Integrable (fun y : E => (1 + ‖y‖) ^ (-(k : ℝ))) m)
    (g : E → ℂ) (hg : Continuous g) (C : ℝ) (hC : ∀ y, ‖g y‖ ≤ C * (1 + ‖y‖) ^ (-(k : ℝ)))
    (A₀ : E →L[ℝ] E) (M : ℝ) (hM : 0 < M) (hA₀ : ∀ y, ‖y‖ ≤ M * ‖A₀ y‖) :
    (∀ᶠ A in 𝓝 A₀, Integrable (fun y => g (A y)) m) ∧
      ContinuousAt (fun A : E →L[ℝ] E => ∫ y, g (A y) ∂m) A₀ := by
  have hev : ∀ᶠ A in 𝓝 A₀, ∀ y, ‖y‖ ≤ (2 * M) * ‖A y‖ := by
    filter_upwards [Metric.ball_mem_nhds A₀ (show (0 : ℝ) < 1 / (2 * M) by positivity)] with A hA y
    rw [Metric.mem_ball, dist_eq_norm] at hA
    have e1 : A₀ y = A y - (A - A₀) y := by simp
    have h2 : ‖A₀ y‖ ≤ ‖A y‖ + 1 / (2 * M) * ‖y‖ := by
      calc ‖A₀ y‖ = ‖A y - (A - A₀) y‖ := by rw [← e1]
        _ ≤ ‖A y‖ + ‖(A - A₀) y‖ := norm_sub_le _ _
        _ ≤ ‖A y‖ + ‖A - A₀‖ * ‖y‖ := by gcongr; exact (A - A₀).le_opNorm y
        _ ≤ ‖A y‖ + 1 / (2 * M) * ‖y‖ := by
            gcongr
    have h3 : M * (1 / (2 * M) * ‖y‖) = ‖y‖ / 2 := by field_simp
    have h4 := hA₀ y
    have h5 : M * ‖A₀ y‖ ≤ M * ‖A y‖ + ‖y‖ / 2 := by
      rw [← h3, ← mul_add]; exact mul_le_mul_of_nonneg_left h2 hM.le
    linarith
  obtain ⟨C', hC'⟩ := decay_comp_of_norm_le g k C hC (2 * M)
  refine ⟨?_, ?_⟩
  · filter_upwards [hev] with A hA
    exact (hW.const_mul C').mono' (hg.comp A.continuous).aestronglyMeasurable
      (ae_of_all _ fun y => hC' _ _ (hA y))
  · refine tendsto_integral_filter_of_dominated_convergence
      (fun y => C' * (1 + ‖y‖) ^ (-(k : ℝ))) ?_ ?_ (hW.const_mul C') (ae_of_all _ fun y => ?_)
    · exact Eventually.of_forall fun A => (hg.comp A.continuous).aestronglyMeasurable
    · filter_upwards [hev] with A hA
      exact ae_of_all _ fun y => hC' _ _ (hA y)
    · exact (hg.comp (continuous_id.clm_apply continuous_const)).continuousAt.tendsto

end GlobalTheory.CompanionTheory.PushFam

namespace GlobalTheory.CompanionTheory.PushFam

theorem integrable_continuousAt_of_linear_push : PositivityTheory.PfSWUS.SchInf.FamCont := by
  intro N X _ μ' hμ' n c O hO hcO hfin hL g hg hdecay
  haveI := hμ'
  set k : ℕ := N + 1 with hk
  set W : (Fin N → ℝ) → ℝ := fun y => (1 + ‖y‖) ^ (-(k : ℝ)) with hWdef
  have hWnonneg : ∀ y, 0 ≤ W y := fun y => by positivity
  have hWμ : Integrable W μ' :=
    integrable_one_add_norm (by rw [Module.finrank_fin_fun, hk]; push_cast; linarith)
  have hWmeas : Measurable W := (measurable_const.add measurable_norm).pow_const _
  obtain ⟨s0, hs0O, hs0fin⟩ := hfin (fun y => ENNReal.ofReal (W y))
    (ENNReal.measurable_ofReal.comp hWmeas)
    ((hasFiniteIntegral_iff_ofReal (ae_of_all _ hWnonneg)).1 hWμ.2).ne O hO ⟨c, hcO⟩
  have hWm : Integrable W (n s0) := ⟨hWmeas.aestronglyMeasurable,
    (hasFiniteIntegral_iff_ofReal (ae_of_all _ hWnonneg)).2 (lt_top_iff_ne_top.2 hs0fin)⟩
  obtain ⟨L, Linv, Λ, hLc, _hLinvc, hΛc, hinv, hpush⟩ := hL s0 hs0O
  obtain ⟨C, hC⟩ := hdecay k
  have hA₀ : ∀ y, ‖y‖ ≤ (‖Linv c‖ + 1) * ‖L c y‖ := fun y => by
    calc ‖y‖ = ‖Linv c (L c y)‖ := by rw [hinv c hcO]
      _ ≤ ‖Linv c‖ * ‖L c y‖ := (Linv c).le_opNorm _
      _ ≤ (‖Linv c‖ + 1) * ‖L c y‖ := by gcongr; linarith
  obtain ⟨hint, hcont⟩ := integrable_continuousAt_clm_comp (n s0) k hWm g hg C hC (L c)
    (‖Linv c‖ + 1) (by positivity) hA₀
  have hint' : ∀ᶠ s in 𝓝 c, Integrable (fun y => g (L s y)) (n s0) := hLc.eventually hint
  have hO' : O ∈ 𝓝 c := hO.mem_nhds hcO
  refine ⟨?_, ?_⟩
  · filter_upwards [hint', hO'] with s hs hsO
    rw [hpush s hsO]
    exact ((integrable_map_measure hg.aestronglyMeasurable
      (L s).continuous.aemeasurable).2 hs).smul_measure_nnreal
  · have hH : ContinuousAt (fun s => (Λ s : ℝ) • ∫ y, g (L s y) ∂(n s0)) c :=
      (NNReal.continuous_coe.continuousAt.comp hΛc).smul
        (ContinuousAt.comp (f := L) (g := fun A : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ) =>
          ∫ y, g (A y) ∂(n s0)) hcont hLc)
    refine hH.congr ?_
    filter_upwards [hO'] with s hs
    rw [hpush s hs, integral_smul_nnreal_measure,
      integral_map (L s).continuous.aemeasurable hg.aestronglyMeasurable, NNReal.smul_def]

end GlobalTheory.CompanionTheory.PushFam
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanMeasureScalingByUnits
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.CompanionTheory.SW.Dil

theorem pi_smul_nnreal {ι : Type} [Fintype ι] {X : ι → Type} [∀ i, MeasurableSpace (X i)]
    (μ : ∀ i, Measure (X i)) [∀ i, SigmaFinite (μ i)] (c : ι → ℝ≥0) :
    Measure.pi (fun i => c i • μ i) = (∏ i, c i) • Measure.pi μ := by
  classical
  refine Measure.pi_eq (μ := fun i => c i • μ i) fun s hs => ?_
  rw [Measure.smul_apply, Measure.pi_pi]
  simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, ENNReal.coe_finset_prod,
    Finset.prod_mul_distrib]

theorem coordW_map_units : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n M d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure (Ainf F)), lam.IsAddHaarMeasure → ∀ e : Ainf F ≃+* (NumberField.InfinitePlace F → ℝ), IsHomeomorph e → ∀ t : Fin n → Ainf F, (∀ a, IsUnit (t a)) → (GlobalTheory.CompanionTheory.SW.coordW (Ainf F) b lam n M).map (fun X a i => algebraMap (Ainf F) (Ainf F ⊗[F] E) (t a) * X a i) = (∏ a, ((∏ w, ‖e (t a) w‖₊)⁻¹) ^ (d * M)) • GlobalTheory.CompanionTheory.SW.coordW (Ainf F) b lam n M := by
  intro F E _ _ _ _ _ σ hσ n M d b lam hlam e he t ht
  obtain ⟨j1, j2, j3, j4, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hσ (Ainf F)
  haveI : BorelSpace (Ainf F ⊗[F] E) := ⟨rfl⟩
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  obtain ⟨hK, -, -⟩ := GlobalTheory.T.coordinate_haar_measure F E σ hσ (Ainf F) d b lam hlam
  haveI := hK
  have hfm : ∀ a, Measurable (fun y : Ainf F ⊗[F] E => algebraMap (Ainf F) (Ainf F ⊗[F] E) (t a) * y) :=
    fun a => (continuous_const.mul continuous_id).measurable
  have hrow : ∀ a, (Measure.pi fun _ : Fin M => GlobalTheory.CompanionTheory.SW.coordK (Ainf F) b lam).map
      (fun (x : Fin M → Ainf F ⊗[F] E) i => algebraMap (Ainf F) (Ainf F ⊗[F] E) (t a) * x i) =
      (((∏ w, ‖e (t a) w‖₊)⁻¹) ^ (d * M)) • Measure.pi fun _ : Fin M => GlobalTheory.CompanionTheory.SW.coordK (Ainf F) b lam := by
    intro a
    obtain ⟨u, hu⟩ := ht a
    have h := GlobalTheory.CompanionTheory.HaarScale.unit_mul_map_haar F e he lam hlam (t a) (ht a)
    rw [← hu] at h
    have hk := coordK_map_unit (Ainf F) σ hσ b lam u _ h
    rw [hu] at hk
    have hk1 := pi_map_scale (ι := Fin M) (GlobalTheory.CompanionTheory.SW.coordK (Ainf F) b lam) _ (hfm a) _ hk
    simp only [Fintype.card_fin, ← pow_mul] at hk1
    exact hk1
  have hrm : ∀ a, Measurable (fun (x : Fin M → Ainf F ⊗[F] E) i =>
      algebraMap (Ainf F) (Ainf F ⊗[F] E) (t a) * x i) := fun a =>
    measurable_pi_iff.2 fun i => (hfm a).comp (measurable_pi_apply i)
  haveI : ∀ a, SigmaFinite ((Measure.pi fun _ : Fin M => GlobalTheory.CompanionTheory.SW.coordK (Ainf F) b lam).map
      (fun (x : Fin M → Ainf F ⊗[F] E) i => algebraMap (Ainf F) (Ainf F ⊗[F] E) (t a) * x i)) := fun a => by
    rw [hrow a]; infer_instance
  have hmap := Measure.pi_map_pi (μ := fun _ : Fin n => Measure.pi fun _ : Fin M => GlobalTheory.CompanionTheory.SW.coordK (Ainf F) b lam)
    (f := fun a (x : Fin M → Ainf F ⊗[F] E) i => algebraMap (Ainf F) (Ainf F ⊗[F] E) (t a) * x i) (fun a => (hrm a).aemeasurable)
  unfold GlobalTheory.CompanionTheory.SW.coordW
  refine hmap.trans ?_
  simp only [hrow]
  exact pi_smul_nnreal _ _

end GlobalTheory.CompanionTheory.SW.Dil
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanRankOneFreeOfPlaces
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.Inf0 GlobalTheory.CompanionTheory.SW.BB

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.Inf0.FreeVec

open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.CoordCM

theorem real_indep {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (b : Module.Basis (Fin 2) F E) (τ : E →+* ℂ) (s t : ℝ)
    (hst : (s : ℂ) * τ (b 0) + (t : ℂ) * τ (b 1) = 0) : s = 0 ∧ t = 0 := by
  obtain ⟨θ₀, hθ₀⟩ := exists_moved h
  have hb0 : b 0 ≠ 0 := b.ne_zero 0
  obtain ⟨θ, hθ⟩ : ∃ θ : E, θ * b 0 = b 1 := ⟨b 1 / b 0, div_mul_cancel₀ _ hb0⟩
  have hmoved : σ θ ≠ θ := by
    intro hfix
    apply hθ₀
    obtain ⟨A, B, hAB⟩ : ∃ A B : F,
        θ₀ * b 0 = algebraMap F E A * b 0 + algebraMap F E B * b 1 :=
      ⟨_, _, by
        have := b.sum_repr (θ₀ * b 0)
        rw [Fin.sum_univ_two, Algebra.smul_def, Algebra.smul_def] at this
        exact this.symm⟩
    have h1 : θ₀ = algebraMap F E A + algebraMap F E B * θ := by
      apply mul_right_cancel₀ hb0
      rw [add_mul, mul_assoc, hθ]
      exact hAB
    rw [h1, map_add, map_mul, hfix, AlgHom.commutes, AlgHom.commutes]
  have him : (τ θ).im ≠ 0 := im_ne_zero h hmoved τ
  have hb1 : τ (b 1) = τ θ * τ (b 0) := by rw [← map_mul, hθ]
  have ht0 : τ (b 0) ≠ 0 := (map_ne_zero τ).2 hb0
  have h2 : (s : ℂ) + t * τ θ = 0 := by
    apply mul_right_cancel₀ ht0
    rw [zero_mul, add_mul, mul_assoc, ← hb1]
    exact hst
  have hi := congrArg Complex.im h2
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, zero_add,
    zero_mul, add_zero, Complex.zero_im] at hi
  have ht : t = 0 := (mul_eq_zero.1 hi).resolve_right him
  subst ht
  refine ⟨?_, rfl⟩
  simpa using h2

theorem eq_coord {F E R : Type} [Field F] [Field E] [Algebra F E] [CommRing R] [Algebra F R]
    (b : Module.Basis (Fin 2) F E) (y : R ⊗[F] E) :
    y = (Algebra.TensorProduct.basis R b).repr y 0 ⊗ₜ[F] b 0 +
      (Algebra.TensorProduct.basis R b).repr y 1 ⊗ₜ[F] b 1 := by
  conv_lhs => rw [← (Algebra.TensorProduct.basis R b).sum_repr y]
  rw [Fin.sum_univ_two, Algebra.TensorProduct.basis_apply, Algebra.TensorProduct.basis_apply,
    TensorProduct.smul_tmul', TensorProduct.smul_tmul']
  simp

theorem linearIndependent_of_xw_ne_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M d : ℕ) (b : Module.Basis (Fin d) F E) (ρ : InfinitePlace F → (F →+* ℝ)) (e : Ainf F ≃+* (InfinitePlace F → ℝ)), (∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x) → IsHomeomorph e → (∀ x w, e (algebraMap F (Ainf F) x) w = ρ w x) → ∀ X : Fin 1 → Fin M → Ainf F ⊗[F] E, (∀ w, xw e b X w ≠ 0) → LinearIndependent (Ainf F ⊗[F] E) X := by
  intro F E _ _ _ _ _ σ h M d b ρ e hρ he hx X hX
  classical
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [h.2.2.1]; norm_num)
  obtain rfl : d = 2 := by
    have := Module.finrank_eq_card_basis b
    rw [h.2.2.1] at this
    simpa using this.symm
  have hex : ∀ w : InfinitePlace F, ∃ t : E →+* ℂ, ∀ x, t (algebraMap F E x) = w.embedding x := by
    intro w
    letI : Algebra F ℂ := w.embedding.toAlgebra
    let t : E →ₐ[F] ℂ := IsAlgClosed.lift
    exact ⟨t, fun x => t.commutes x⟩
  choose τ hτ using hex
  obtain ⟨Θ, hΘ⟩ := exists_hom e τ (fun x w => by rw [hx, hρ, hτ])
  have key : ∀ (y : Ainf F ⊗[F] E) (w : InfinitePlace F), Θ y w = 0 →
      ∀ k, e ((Algebra.TensorProduct.basis (Ainf F) b).repr y k) w = 0 := by
    intro y w hy k
    have h1 : Θ y w = (e ((Algebra.TensorProduct.basis (Ainf F) b).repr y 0) w : ℂ) * τ w (b 0) +
        (e ((Algebra.TensorProduct.basis (Ainf F) b).repr y 1) w : ℂ) * τ w (b 1) := by
      conv_lhs => rw [eq_coord b y, map_add, Pi.add_apply, hΘ, hΘ]
    rw [hy] at h1
    obtain ⟨h0, h1'⟩ := real_indep h b (τ w) _ _ h1.symm
    fin_cases k
    · exact h0
    · exact h1'
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  obtain rfl : i = 0 := Subsingleton.elim _ _
  have hg' : ∀ j, g 0 * X 0 j = 0 := fun j => by simpa using congrFun hg j
  have hw : ∀ w, Θ (g 0) w = 0 := by
    intro w
    obtain ⟨⟨j, k⟩, hjk⟩ := Function.ne_iff.1 (hX w)
    have hne : Θ (X 0 j) w ≠ 0 := fun h0 => hjk (key _ _ h0 k)
    have h3 := congrFun (congrArg Θ (hg' j)) w
    rw [map_mul, Pi.mul_apply, map_zero] at h3
    exact (mul_eq_zero.1 h3).resolve_right hne
  refine (Algebra.TensorProduct.basis (Ainf F) b).ext_elem fun k => ?_
  rw [map_zero, Finsupp.zero_apply]
  apply e.injective
  rw [map_zero]
  funext w
  exact key _ _ (hw w) k

end GlobalTheory.CompanionTheory.WeilSiegel.Inf0.FreeVec
end
end

