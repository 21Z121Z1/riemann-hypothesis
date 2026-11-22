import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0515
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0915
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0522
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecondCountableHermC
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0544
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OneVectorCcOfSiegelWeil
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.NDDefs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqSplitFinMulSplitInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0750
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0535
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsFinitePartOfBot
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0524
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.EulerProducts.GenStable
import GroundTheory.GlobalFields.TateThesis.RootNumberLocalPlace
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0536
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.JointGeneralisedEigenvectors.IsJointGenEig
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.WeylSplitting.WeylSplit

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ComplexCoordinatesExistAtInfinity
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch NumberField

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.CoordCM

section Field

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem exists_moved (h : IsCMExt F E σ) : ∃ θ : E, σ θ ≠ θ := by
  by_contra hc
  push_neg at hc
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hc' := h.2.1
  refine IsTotallyComplex.complexEmbedding_not_isReal τ ?_
  rw [ComplexEmbedding.isReal_iff]
  ext y
  have := h.2.2.2 τ y
  rw [hc y] at this
  simpa using this.symm

theorem im_ne_zero (h : IsCMExt F E σ) {θ : E} (hθ : σ θ ≠ θ) (τ : E →+* ℂ) : (τ θ).im ≠ 0 := by
  intro h0
  apply hθ
  apply τ.injective
  rw [h.2.2.2]
  exact Complex.conj_eq_iff_im.2 h0

theorem linInd_one (h : IsCMExt F E σ) {θ : E} (hθ : σ θ ≠ θ) :
    LinearIndependent F ![(1 : E), θ] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have h1 : s • (1 : E) + t • σ θ = 0 := by
    have := congrArg σ hst
    simp only [Algebra.smul_def, map_add, map_mul, AlgHom.commutes, map_one, map_zero] at this ⊢
    exact this
  have h2 : t • (σ θ - θ) = 0 := by
    rw [smul_sub, sub_eq_zero]
    exact add_left_cancel (h1.trans hst.symm)
  have ht : t = 0 := by
    rcases smul_eq_zero.1 h2 with h3 | h3
    · exact h3
    · exact absurd (sub_eq_zero.1 h3) hθ
  subst ht
  refine ⟨?_, rfl⟩
  simpa using hst

def basisOne (h : IsCMExt F E σ) {θ : E} (hθ : σ θ ≠ θ) : Module.Basis (Fin 2) F E :=
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [h.2.2.1]; norm_num)
  basisOfLinearIndependentOfCardEqFinrank (linInd_one h hθ) (by rw [h.2.2.1]; simp)

theorem basisOne_zero (h : IsCMExt F E σ) {θ : E} (hθ : σ θ ≠ θ) : basisOne h hθ 0 = 1 := by
  simp [basisOne]

theorem basisOne_one (h : IsCMExt F E σ) {θ : E} (hθ : σ θ ≠ θ) : basisOne h hθ 1 = θ := by
  simp [basisOne]

end Field

section Top

variable {F E : Type} [Field F] [Field E] [Algebra F E]

def coordHomeo (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] {d : ℕ}
    (b : Module.Basis (Fin d) F E) : (R ⊗[F] E) ≃ₜ (Fin d → R) :=
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  haveI : ContinuousAdd (R ⊗[F] E) := IsModuleTopology.toContinuousAdd R _
  { (Algebra.TensorProduct.basis R b).equivFun.toEquiv with
    continuous_toFun :=
      IsModuleTopology.continuous_of_linearMap (Algebra.TensorProduct.basis R b).equivFun.toLinearMap
    continuous_invFun :=
      IsModuleTopology.continuous_of_linearMap (Algebra.TensorProduct.basis R b).equivFun.symm.toLinearMap }

def planeHomeo {W : Type} (t : W → ℂ) (ht : ∀ w, (t w).im ≠ 0) : (Fin 2 → W → ℝ) ≃ₜ (W → ℂ) where
  toFun f w := (f 0 w : ℂ) + (f 1 w : ℂ) * t w
  invFun g := ![fun w => (g w).re - (g w).im / (t w).im * (t w).re, fun w => (g w).im / (t w).im]
  left_inv f := by
    funext k w
    have := ht w
    fin_cases k
    · simp
      field_simp
      ring
    · simp
      field_simp
  right_inv g := by
    funext w
    have := ht w
    apply Complex.ext
    · simp
    · simp
      field_simp
  continuous_toFun := by
    refine continuous_pi fun w => ?_
    have h0 : Continuous fun f : Fin 2 → W → ℝ => f 0 w := (continuous_apply w).comp (continuous_apply 0)
    have h1 : Continuous fun f : Fin 2 → W → ℝ => f 1 w := (continuous_apply w).comp (continuous_apply 1)
    exact (Complex.continuous_ofReal.comp h0).add ((Complex.continuous_ofReal.comp h1).mul continuous_const)
  continuous_invFun := by
    refine continuous_pi fun k => continuous_pi fun w => ?_
    have hr : Continuous fun g : W → ℂ => (g w).re := Complex.continuous_re.comp (continuous_apply w)
    have hi : Continuous fun g : W → ℂ => (g w).im := Complex.continuous_im.comp (continuous_apply w)
    fin_cases k
    · exact hr.sub ((hi.div_const _).mul continuous_const)
    · exact hi.div_const _

end Top

section Map

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem exists_hom (e : Ainf F ≃+* (InfinitePlace F → ℝ)) (τ : InfinitePlace F → (E →+* ℂ))
    (hc : ∀ x w, ((e (algebraMap F (Ainf F) x) w : ℝ) : ℂ) = τ w (algebraMap F E x)) :
    ∃ Θ : Ainf F ⊗[F] E →+* (InfinitePlace F → ℂ),
      ∀ a x w, Θ (a ⊗ₜ[F] x) w = (e a w : ℂ) * τ w x := by
  letI : Algebra F (InfinitePlace F → ℂ) :=
    (Pi.ringHom fun w => (τ w).comp (algebraMap F E)).toAlgebra
  let fA : Ainf F →ₐ[F] (InfinitePlace F → ℂ) :=
    { toRingHom := Pi.ringHom fun w =>
        Complex.ofRealHom.comp ((Pi.evalRingHom (fun _ => ℝ) w).comp (e : Ainf F →+* (InfinitePlace F → ℝ)))
      commutes' := fun x => funext fun w => hc x w }
  let fE : E →ₐ[F] (InfinitePlace F → ℂ) :=
    { toRingHom := Pi.ringHom τ
      commutes' := fun _ => rfl }
  exact ⟨(Algebra.TensorProduct.productMap fA fE).toRingHom, fun a x w => by
    simp [Algebra.TensorProduct.productMap_apply_tmul, fA, fE]
    rfl⟩

end Map

end GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.CoordCM

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Arch

open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.CoordCM in
theorem exists_isCoord : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
  IsCMExt F E σ → ∀ (ρ : InfinitePlace F → (F →+* ℝ)) (e : Ainf F ≃+* (InfinitePlace F → ℝ)),
  (∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x) → IsHomeomorph e → (∀ x w, e (algebraMap F (Ainf F) x) w = ρ w x) →
  ∃ (τ : InfinitePlace F → (E →+* ℂ)) (Θ : Ainf F ⊗[F] E ≃+* (InfinitePlace F → ℂ)),
    IsCoord σ e τ Θ := by
  intro F E _ _ _ _ _ σ h ρ e hρ he hx
  classical
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [h.2.2.1]; norm_num)
  have hex : ∀ w : InfinitePlace F, ∃ t : E →+* ℂ, ∀ x, t (algebraMap F E x) = w.embedding x := by
    intro w
    letI : Algebra F ℂ := w.embedding.toAlgebra
    let t : E →ₐ[F] ℂ := IsAlgClosed.lift
    exact ⟨t, fun x => t.commutes x⟩
  choose τ hτ using hex
  obtain ⟨θ, hθ⟩ := exists_moved h
  obtain ⟨Θ, hΘ⟩ := exists_hom e τ (fun x w => by rw [hx, hρ, hτ])
  let eH : Ainf F ≃ₜ (InfinitePlace F → ℝ) := he.homeomorph
  let b := basisOne h hθ
  let H : (Ainf F ⊗[F] E) ≃ₜ (InfinitePlace F → ℂ) :=
    (coordHomeo (Ainf F) b).trans ((Homeomorph.piCongrRight fun _ => eH).trans
      (planeHomeo (fun w => τ w θ) (fun w => im_ne_zero h hθ (τ w))))
  have hH : ∀ y, H y = Θ y := by
    intro y
    have hy : y = (Algebra.TensorProduct.basis (Ainf F) b).repr y 0 ⊗ₜ[F] (1 : E) +
        (Algebra.TensorProduct.basis (Ainf F) b).repr y 1 ⊗ₜ[F] θ := by
      conv_lhs => rw [← (Algebra.TensorProduct.basis (Ainf F) b).sum_repr y]
      rw [Fin.sum_univ_two, Algebra.TensorProduct.basis_apply, Algebra.TensorProduct.basis_apply,
        basisOne_zero, basisOne_one, TensorProduct.smul_tmul', TensorProduct.smul_tmul']
      simp
    funext w
    conv_rhs => rw [hy, map_add, Pi.add_apply, hΘ, hΘ, map_one, mul_one]
    rfl
  have hbij : Function.Bijective Θ := by
    have : (Θ : Ainf F ⊗[F] E → _) = H := funext fun y => (hH y).symm
    rw [this]
    exact H.bijective
  refine ⟨τ, RingEquiv.ofBijective Θ hbij, ?_, ?_, ?_, ?_⟩
  · have : ((RingEquiv.ofBijective Θ hbij : Ainf F ⊗[F] E ≃+* _) : Ainf F ⊗[F] E → _) = H :=
      funext fun y => (hH y).symm
    rw [this]
    exact H.isHomeomorph
  · intro z w
    simp only [RingEquiv.ofBijective_apply]
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a x =>
      have : sigR (Ainf F) σ (a ⊗ₜ[F] x) = a ⊗ₜ[F] σ x := by simp [sigR]
      rw [this, hΘ, hΘ, h.2.2.2, map_mul, Complex.conj_ofReal]
      rfl
    | add y y' hy hy' => simp only [map_add, Pi.add_apply, hy, hy']
  · intro x w
    simp only [RingEquiv.ofBijective_apply]
    rw [hΘ, map_one]
    simp
  · intro z w
    simp only [RingEquiv.ofBijective_apply]
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a x =>
      have h1 : τ w x + conj (τ w x) = ((ρ w (Algebra.trace F E x) : ℝ) : ℂ) := by
        rw [hρ, ← hτ, ← GlobalTheory.GaussMean.OneVec.add_sigma h, map_add, h.2.2.2]
        rfl
      rw [GlobalTheory.GaussMean.OneVec.trace_tmul, map_mul, Pi.mul_apply, hx, hΘ, map_mul, Complex.conj_ofReal,
        Complex.ofReal_mul, ← h1]
      ring
    | add y y' hy hy' =>
      simp only [map_add, Pi.add_apply, Complex.ofReal_add, hy, hy']
      ring

end GlobalTheory.CompanionTheory.SiegelND.Integ.Arch
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousBiadditiveBounded
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.Arch

theorem continuous_biadditive_bounded :
    ∀ (N₁ N₂ N₃ : ℕ) (β : (Fin N₁ → ℝ) → (Fin N₂ → ℝ) → (Fin N₃ → ℝ)),
      (∀ u u' v, β (u + u') v = β u v + β u' v) →
      (∀ u v v', β u (v + v') = β u v + β u v') →
      Continuous (fun p : (Fin N₁ → ℝ) × (Fin N₂ → ℝ) => β p.1 p.2) →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ u v, ‖β u v‖ ≤ C * ‖u‖ * ‖v‖ := by
  intro N₁ N₂ N₃ β h₁ h₂ hβ
  have smul₁ : ∀ (c : ℝ) u v, β (c • u) v = c • β u v := by
    intro c u v
    exact map_real_smul (AddMonoidHom.mk' (fun u => β u v) fun u u' => h₁ u u' v)
      (hβ.comp (continuous_id.prodMk continuous_const)) c u
  have smul₂ : ∀ (c : ℝ) u v, β u (c • v) = c • β u v := by
    intro c u v
    exact map_real_smul (AddMonoidHom.mk' (fun v => β u v) fun v v' => h₂ u v v')
      (hβ.comp (continuous_const.prodMk continuous_id)) c v
  have zero₁ : ∀ v, β 0 v = 0 := fun v => by simpa using smul₁ 0 0 v
  have zero₂ : ∀ u, β u 0 = 0 := fun u => by simpa using smul₂ 0 u 0
  obtain ⟨δ, hδ, hsmall⟩ := Metric.continuous_iff.mp hβ 0 1 one_pos
  have key : ∀ u v, ‖u‖ < δ → ‖v‖ < δ → ‖β u v‖ < 1 := by
    intro u v hu hv
    have h := hsmall (u, v) (by rw [dist_zero_right, Prod.norm_def]; exact max_lt hu hv)
    simpa [zero₁, dist_zero_right] using h
  obtain ⟨s, rfl⟩ : ∃ s, δ = 2 * s := ⟨δ / 2, by ring⟩
  have hs0 : 0 < s := by linarith
  have hsδ : s < 2 * s := by linarith
  refine ⟨4 / (2 * s) ^ 2, by positivity, fun u v => ?_⟩
  by_cases hu : u = 0
  · simp [hu, zero₁]
  by_cases hv : v = 0
  · simp [hv, zero₂]
  have hu' : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have hv' : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hnu : ‖(s / ‖u‖) • u‖ = s := by
    rw [norm_smul, Real.norm_of_nonneg (div_pos hs0 hu').le]
    field_simp
  have hnv : ‖(s / ‖v‖) • v‖ = s := by
    rw [norm_smul, Real.norm_of_nonneg (div_pos hs0 hv').le]
    field_simp
  have hb := key ((s / ‖u‖) • u) ((s / ‖v‖) • v) (by rw [hnu]; exact hsδ) (by rw [hnv]; exact hsδ)
  rw [smul₁, smul₂, smul_smul, norm_smul,
    Real.norm_of_nonneg (mul_pos (div_pos hs0 hu') (div_pos hs0 hv')).le] at hb
  have e : s / ‖u‖ * (s / ‖v‖) * ‖β u v‖ = (‖β u v‖ * (s * s)) / (‖u‖ * ‖v‖) := by ring
  rw [e, div_lt_one (mul_pos hu' hv')] at hb
  rw [show 4 / (2 * s) ^ 2 * ‖u‖ * ‖v‖ = (‖u‖ * ‖v‖) / (s * s) by ring,
    le_div_iff₀ (mul_pos hs0 hs0)]
  exact hb.le

end GlobalTheory.CompanionTheory.Arch
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousCoeffRowAct
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.TrKer
open scoped Classical TensorProduct Topology
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.WInfCont

theorem continuous_coeff_rowAct {r m : ℕ} (f : MvPolynomial (Fin r × Fin m) ℂ) :
    ∀ s : (Fin r × Fin m) →₀ ℕ, Continuous fun M : Matrix (Fin r) (Fin r) ℂ =>
      MvPolynomial.coeff s (Formalism.GradedWeylDivisibility.rowAct ℂ (n := m) M f) := by
  induction f using MvPolynomial.induction_on with
  | C a =>
    intro s
    simpa [MvPolynomial.algebraMap_eq] using
      (continuous_const : Continuous fun _ : Matrix (Fin r) (Fin r) ℂ => MvPolynomial.coeff s (MvPolynomial.C a))
  | add p q hp hq =>
    intro s
    simp only [map_add, MvPolynomial.coeff_add]
    exact (hp s).add (hq s)
  | mul_X p v hp =>
    intro s
    have key : ∀ M : Matrix (Fin r) (Fin r) ℂ, MvPolynomial.coeff s (Formalism.GradedWeylDivisibility.rowAct ℂ (n := m) M (p * MvPolynomial.X v)) =
        ∑ b : Fin r, M v.1 b * (if (b, v.2) ∈ s.support then
          MvPolynomial.coeff (s - Finsupp.single (b, v.2) 1) (Formalism.GradedWeylDivisibility.rowAct ℂ (n := m) M p) else 0) := by
      intro M
      have hX : Formalism.GradedWeylDivisibility.rowAct ℂ (n := m) M (MvPolynomial.X v) =
          ∑ b : Fin r, MvPolynomial.C (M v.1 b) * MvPolynomial.X (b, v.2) := by
        simp [Formalism.GradedWeylDivisibility.rowAct, MvPolynomial.aeval_X]
      rw [map_mul, hX, Finset.mul_sum, MvPolynomial.coeff_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [mul_left_comm, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_mul_X']
    simp only [key]
    refine continuous_finset_sum _ fun b _ => ?_
    refine ((continuous_id.matrix_elem v.1 b)).mul ?_
    split_ifs
    · exact hp _
    · exact continuous_const

theorem continuous_detPow (n : ℕ) (c : ℤ) : Continuous fun g : GL (Fin n) ℂ => detPow ℂ n g c := by
  have h0 : Continuous (Matrix.detMonoidHom : Matrix (Fin n) (Fin n) ℂ →* ℂ) := continuous_id.matrix_det
  have h1 : Continuous (Matrix.GeneralLinearGroup.det : GL (Fin n) ℂ →* ℂˣ) :=
    Continuous.units_map _ h0
  exact Units.continuous_val.comp (h1.zpow c)

theorem continuous_coeff_sqAct {n : ℕ} (lam : DomWeight n) (f : MvPolynomial (Fin n × Fin n) ℂ)
    (s : (Fin n × Fin n) →₀ ℕ) :
    Continuous fun g : GL (Fin n) ℂ => MvPolynomial.coeff s (sqAct ℂ n lam g f) := by
  simp only [sqAct, MvPolynomial.coeff_smul, smul_eq_mul]
  exact (continuous_detPow n _).mul
    ((continuous_coeff_rowAct f s).comp Units.continuous_val.matrix_transpose)

theorem exists_finset_factor {σ : Type} (W : Submodule ℂ (MvPolynomial σ ℂ)) [FiniteDimensional ℂ W]
    (φ : Module.Dual ℂ W) : ∃ (S : Finset (σ →₀ ℕ)) (c : S → ℂ),
      ∀ p : W, φ p = ∑ s : S, c s * MvPolynomial.coeff s.1 p.1 := by
  let b := Module.finBasis ℂ W
  let S : Finset (σ →₀ ℕ) := Finset.univ.biUnion fun i => (b i : MvPolynomial σ ℂ).support
  let L : W →ₗ[ℂ] (S → ℂ) :=
    { toFun := fun p s => MvPolynomial.coeff s.1 p.1
      map_add' := fun p q => by funext s; simp
      map_smul' := fun a p => by funext s; simp }
  have hL : LinearMap.ker L = ⊥ := by
    refine LinearMap.ker_eq_bot'.2 fun p hp => ?_
    apply Subtype.ext
    refine MvPolynomial.ext _ _ fun s => ?_
    by_cases hs : s ∈ S
    · simpa [L] using congrFun hp ⟨s, hs⟩
    · have h0 : ∀ i, MvPolynomial.coeff s (b i : MvPolynomial σ ℂ) = 0 := fun i => by
        by_contra h
        exact hs (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, MvPolynomial.mem_support_iff.2 h⟩)
      have hp' : (p : MvPolynomial σ ℂ) = ∑ i, b.repr p i • (b i : MvPolynomial σ ℂ) := by
        have h := congrArg Subtype.val (b.sum_repr p)
        rw [AddSubmonoidClass.coe_finset_sum] at h
        exact h.symm
      rw [hp']
      simp [MvPolynomial.coeff_sum, h0]
  obtain ⟨ψ, hψ⟩ := LinearMap.exists_leftInverse_of_injective L hL
  refine ⟨S, fun s => (φ ∘ₗ ψ) fun j => if s = j then 1 else 0, fun p => ?_⟩
  have e : φ p = (φ ∘ₗ ψ) (L p) := by
    have h := LinearMap.congr_fun hψ p
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at h ⊢
    rw [h]
  rw [e, LinearMap.pi_apply_eq_sum_univ (φ ∘ₗ ψ) (L p)]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [smul_eq_mul, mul_comm]
  rfl

theorem continuous_sqRep_coeff {n : ℕ} (lam : DomWeight n) (f : nablaSq ℂ n lam)
    (φ : Module.Dual ℂ (nablaSq ℂ n lam)) :
    Continuous fun g : GL (Fin n) ℂ => φ (GlobalTheory.Branching.sqRep ℂ n lam g f) := by
  obtain ⟨S, c, h⟩ := exists_finset_factor (nablaSq ℂ n lam) φ
  simp only [h]
  exact continuous_finset_sum _ fun s _ => continuous_const.mul (continuous_coeff_sqAct lam f.1 s.1)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

end GlobalTheory.CompanionTheory.WInfCont
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousOnRingInverseOfIsOpenEmbeddingUnits
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.GLOpen

theorem continuousOn_ringInverse_of_isOpenEmbedding_units
    (A : Type) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    (hA : IsOpenEmbedding (Units.val : Aˣ → A)) :
    ContinuousOn (Ring.inverse : A → A) {x | IsUnit x} := by
  rintro _ ⟨u, rfl⟩
  refine ContinuousAt.continuousWithinAt ?_
  rw [← hA.continuousAt_iff]
  have h : (Ring.inverse ∘ Units.val : Aˣ → A) = fun v => ((v⁻¹ : Aˣ) : A) := by
    funext v
    exact Ring.inverse_unit v
  rw [h]
  exact Units.continuous_coe_inv.continuousAt

theorem isOpenEmbedding_val_GL
    (A : Type) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    (hA : IsOpenEmbedding (Units.val : Aˣ → A)) (n : ℕ) :
    IsOpenEmbedding (Units.val : GL (Fin n) A → Matrix (Fin n) (Fin n) A) := by
  have hdet : Continuous (fun M : Matrix (Fin n) (Fin n) A => M.det) :=
    continuous_id.matrix_det
  have hunit : ∀ M : Matrix (Fin n) (Fin n) A, IsUnit M ↔ IsUnit M.det :=
    fun M => Matrix.isUnit_iff_isUnit_det M
  have hadj : Continuous (fun M : Matrix (Fin n) (Fin n) A => M.adjugate) :=
    continuous_id.matrix_adjugate
  have hopen : IsOpen {x : A | IsUnit x} := hA.isOpen_range
  refine ⟨Units.isEmbedding_val_mk' (f := fun M : Matrix (Fin n) (Fin n) A => M⁻¹) ?_
    fun u => (Matrix.coe_units_inv u).symm, ?_⟩
  · have hinv : ContinuousOn
        (fun M : Matrix (Fin n) (Fin n) A => Ring.inverse M.det • M.adjugate) {M | IsUnit M} := by
      have hri : ContinuousOn (fun M : Matrix (Fin n) (Fin n) A => Ring.inverse M.det)
          {M | IsUnit M} :=
        (GlobalTheory.CompanionTheory.SW.GLOpen.continuousOn_ringInverse_of_isOpenEmbedding_units A hA).comp hdet.continuousOn
          fun M hM => (hunit M).mp hM
      exact hri.smul hadj.continuousOn
    exact hinv.congr fun M _ => Matrix.inv_def M
  · have h : Set.range (Units.val : GL (Fin n) A → Matrix (Fin n) (Fin n) A) =
        (fun M : Matrix (Fin n) (Fin n) A => M.det) ⁻¹' {x | IsUnit x} := by
      ext M
      exact hunit M
    rw [h]
    exact hopen.preimage hdet

end GlobalTheory.CompanionTheory.SW.GLOpen
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConvolutionMaximalCompactEquivariantStatement
section
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CompanionTheory.SmoothRep
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.convolution_maximal_compact_equivariant : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (U : Subgroup (GL (Fin a) (Af E))) (β : Lie E a → ℂ), ConjInv β → ∀ (F : L2 (latticeGL E a) μ) (k : Kinf E a) (x : GA E a), convR μ (tst U β) (lift (latticeGL E a) (R (latticeGL E a) μ (infGL E a (Unitary.toUnits k)) F)) x = convR μ (tst U β) (lift (latticeGL E a) F) (x * infGL E a (Unitary.toUnits k)) := by
  first | exact @GlobalTheory.CompanionTheory.SmoothRep.convR_tst_cpt | exact GlobalTheory.CompanionTheory.SmoothRep.convR_tst_cpt | (intros; apply GlobalTheory.CompanionTheory.SmoothRep.convR_tst_cpt <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConvolutionRightInvariantOpenCompactStatement
section
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CompanionTheory.SmoothRep
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.convolution_right_invariant_open_compact : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (U : Subgroup (GL (Fin a) (Af E))) (β : Lie E a → ℂ) (Fl : GA E a → ℂ) (u : GL (Fin a) (Af E)), u ∈ U → ∀ x : GA E a, convR μ (tst U β) Fl (x * finGL E a u) = convR μ (tst U β) Fl x := by
  first | exact @GlobalTheory.CompanionTheory.SmoothRep.convR_tst_right_invariant | exact GlobalTheory.CompanionTheory.SmoothRep.convR_tst_right_invariant | (intros; apply GlobalTheory.CompanionTheory.SmoothRep.convR_tst_right_invariant <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalConvolutionSplitCentreInvariantStatement
section
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CompanionTheory.SmoothRep
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspidal_convolution_split_centre_invariant : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (f : GA E a → ℂ) (F : L2 (latticeGL E a) μ), F ∈ L2cusp μ → ∀ (t : ℝ) (x : GA E a), convR μ f (lift (latticeGL E a) F) (splitCentre E a t * x) = convR μ f (lift (latticeGL E a) F) x := by
  first | exact @GlobalTheory.CompanionTheory.SmoothRep.convR_lift_splitCentre_mul | exact GlobalTheory.CompanionTheory.SmoothRep.convR_lift_splitCentre_mul | (intros; apply GlobalTheory.CompanionTheory.SmoothRep.convR_lift_splitCentre_mul <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DifferentIdealRat
section
open NumberField IsDedekindDomain GroundTheory.Global GroundTheory.LocalField

namespace GlobalTheory.CompanionTheory.StdCharQ

theorem differentIdeal_rat : differentIdeal ℤ (𝓞 ℚ) = ⊤ := by
  rw [← Ideal.absNorm_eq_one_iff, NumberField.absNorm_differentIdeal (K := ℚ), NumberField.discr_rat]
  rfl

theorem differentExp_rat (v : HeightOneSpectrum (𝓞 ℚ)) : differentExp v = 0 := by
  simp only [GroundTheory.Global.differentExp, differentIdeal_rat, FractionalIdeal.coeIdeal_top, FractionalIdeal.count_one]

theorem stdChar : Ad3.GP.StdChar := by
  intro v
  unfold Ad3.IsStd Ad3.GP.psiF
  refine ⟨continuous_localAdelicChar v, localAdelicChar_ne_one v, ?_⟩
  rw [addCharConductor_localAdelicChar, differentExp_rat, neg_zero]

end GlobalTheory.CompanionTheory.StdCharQ
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DominantHeckeOperatorsCommuteStatement
section
open GlobalTheory.PRep PositivityTheory.SphericalProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dominant_hecke_operators_commute : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (D : PositivityTheory.SphericalProduct.CassData G), (∀ a ∈ D.T, ∀ b ∈ D.T, a * b * a⁻¹ * b⁻¹ ∈ D.J) → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V), IsSmooth π → ∀ t t' : D.T, D.IsDom t → D.IsDom t' → ∀ U U' : Module.End ℂ (fixed π D.J), PositivityTheory.Lbc.IsHeckeOpG π D.J (t : G) U → PositivityTheory.Lbc.IsHeckeOpG π D.J (t' : G) U' → U * U' = U' * U := by
  first | exact @GlobalTheory.CompanionTheory.CassHecke.heckeOp_commute | exact GlobalTheory.CompanionTheory.CassHecke.heckeOp_commute | (intros; apply GlobalTheory.CompanionTheory.CassHecke.heckeOp_commute <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EllipticLocalIdentityStatement
section
open NumberField IsDedekindDomain Polynomial GlobalTheory.BCT PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.G2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.elliptic_local_identity : EllLocal := by
  first | exact @GlobalTheory.CompanionTheory.EllLoc.ellLocal | exact GlobalTheory.CompanionTheory.EllLoc.ellLocal | (intros; apply GlobalTheory.CompanionTheory.EllLoc.ellLocal <;> assumption)
end

