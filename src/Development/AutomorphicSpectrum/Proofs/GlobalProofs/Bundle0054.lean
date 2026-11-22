import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0051
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1281
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0177
import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0048
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeTateFunctionalEquationCM
import GroundTheory.GlobalFields.TateThesis.RootNumberLocalFinite
import GroundTheory.GlobalFields.AnalyticClassNumber.HeckeContinued
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0049
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0052
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0053

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.AnalyticSectionIsAlgebraicStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.analytic_section_is_algebraic : ∀ (Y : Scheme.{0}) (p : Y ⟶ Sp ℂ) (D : ℕ), SmoothOfRelativeDimension D p → IsProper p → ∀ (R : AnRead p (RingHom.id ℂ) D) (B : LB Y), B.IsLB → ∀ s ∈ R.holSec B, ∃ t : B.Sec, secVal p (RingHom.id ℂ) t = s := by
  first | exact @GlobalTheory.CompanionTheory.Gaga.holomorphicSections_algebraic_of_isProper | exact GlobalTheory.CompanionTheory.Gaga.holomorphicSections_algebraic_of_isProper | (intros; apply GlobalTheory.CompanionTheory.Gaga.holomorphicSections_algebraic_of_isProper <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.AnalyticVectorExponentialSeriesStatement
section
open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.LinRed GlobalTheory.FlagMeas GlobalTheory.RealInd GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.HCA
open scoped InnerProductSpace ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.analytic_vector_exponential_series : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hG : IsLinRed G) (hrep : Formalism.QuantumDeterminants.IsCRepOn G π) (hc : ∀ v, ContinuousOn (fun g => π g v) G) {v : H} (hs : IsSmoothVec G π v) (hw : WordBound G π v), ∃ r : ℝ, 0 < r ∧ ∀ X ∈ HCSS.lieOf G, mnorm X < r → HasSum (fun m : ℕ => ((m.factorial : ℂ)⁻¹) • (dRep π X)^[m] v) (π (NormedSpace.exp X) v) := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.HCA.hasSum_orbit_of_wordBound | exact GlobalTheory.CompanionTheory.Hypotheses₂.HCA.hasSum_orbit_of_wordBound | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.HCA.hasSum_orbit_of_wordBound <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.CmHeckeCharacterInfinityTypeStatement
section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds GlobalTheory.HeckeEps GlobalTheory.CompanionTheory.HeckeBridge GroundTheory.Global GroundTheory.LocalField GroundTheory.Global.IdeleGroup
open GroundTheory.Automorphic.GodementSection (localChar)
open Formalism.L2.Host (unif atFin unif_spec)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_hecke_character_infinity_type : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (I : Type) [Fintype I] (φ : I → E →+* ℂ), IsCMType φ → ∀ (χ : HChar E) (hu : IsUnitary χ) (n : I → ℤ), Formalism.L2.Host.HChar.HasInf χ φ n → ∀ i : I, (toHecke χ hu).infiniteTau (InfinitePlace.mk (φ i)) = 0 ∧ ((toHecke χ hu).infiniteWeight (InfinitePlace.mk (φ i))).natAbs = (n i).natAbs := by
  first | exact @GlobalTheory.CompanionTheory.HeckeArch.infiniteParams_of_hasInf | exact GlobalTheory.CompanionTheory.HeckeArch.infiniteParams_of_hasInf | (intros; apply GlobalTheory.CompanionTheory.HeckeArch.infiniteParams_of_hasInf <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.CmHeckeCharacterNotNormPowerStatement
section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds GlobalTheory.HeckeEps GlobalTheory.CompanionTheory.HeckeBridge GroundTheory.Global GroundTheory.LocalField GroundTheory.Global.IdeleGroup
open GroundTheory.Automorphic.GodementSection (localChar)
open Formalism.L2.Host (unif atFin unif_spec)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_hecke_character_not_norm_power : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (I : Type) [Fintype I] (φ : I → E →+* ℂ), IsCMType φ → ∀ (χ : HChar E) (hu : IsUnitary χ) (n : I → ℤ), Formalism.L2.Host.HChar.HasInf χ φ n → (∃ i, n i ≠ 0) → ¬ ∃ τ : ℝ, ∀ x : IdeleGroup E, ((toHecke χ hu).toIdele x : ℂ) = ((ideleModule E x : ℝ) : ℂ) ^ ((τ : ℂ) * Complex.I) := by
  first | exact @GlobalTheory.CompanionTheory.HeckeBridge.NotPow.not_modulePow | exact GlobalTheory.CompanionTheory.HeckeBridge.NotPow.not_modulePow | (intros; apply GlobalTheory.CompanionTheory.HeckeBridge.NotPow.not_modulePow <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.DerivedActionAdditive
section
noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.LinRed GlobalTheory.FlagMeas GlobalTheory.RealInd GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.HCA
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.CompanionTheory.Hypotheses₂.HCA.SmoothLin

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem hasDerivAt_exp_entries (X : Matrix (Fin n) (Fin n) ℂ) :
    HasDerivAt (fun t : ℝ => (Matrix.of.symm (NormedSpace.exp (t • X)) : Fin n → Fin n → ℂ))
      (Matrix.of.symm X) 0 := by
  letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
  have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) X (0 : ℝ)
  rw [zero_smul, NormedSpace.exp_zero, one_mul] at h
  let L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] (Fin n → Fin n → ℂ) :=
    { toFun := fun M => Matrix.of.symm M
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact (LinearMap.toContinuousLinearMap L).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h

theorem hasDerivAt_orbit {G : Set (Matrix (Fin n) (Fin n) ℂ)} {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {v : H}
    {F : (Fin n → Fin n → ℂ) → H} (hF : ContDiff ℝ ∞ F) (hFG : ∀ z, Matrix.of z ∈ G → π (Matrix.of z) v = F z)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ HCSS.lieOf G) :
    HasDerivAt (fun t : ℝ => π (NormedSpace.exp (t • X)) v)
      (fderiv ℝ F (Matrix.of.symm (1 : Matrix (Fin n) (Fin n) ℂ)) (Matrix.of.symm X)) 0 := by
  have hfun : (fun t : ℝ => π (NormedSpace.exp (t • X)) v) =
      fun t : ℝ => F (Matrix.of.symm (NormedSpace.exp (t • X))) := by
    funext t
    have hmem : Matrix.of (Matrix.of.symm (NormedSpace.exp (t • X))) ∈ G := by
      simpa using hX t
    simpa using hFG _ hmem
  rw [hfun]
  have hdiff : DifferentiableAt ℝ F (Matrix.of.symm (NormedSpace.exp ((0 : ℝ) • X))) :=
    (hF.differentiable (by simp)) _
  have h := hdiff.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hasDerivAt_exp_entries X)
  rw [zero_smul, NormedSpace.exp_zero] at h
  exact h

theorem differentiableAt_orbit {G : Set (Matrix (Fin n) (Fin n) ℂ)} {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    {v : H} (hv : IsSmoothVec G π v) {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ HCSS.lieOf G) :
    DifferentiableAt ℝ (fun t : ℝ => π (NormedSpace.exp (t • X)) v) 0 := by
  obtain ⟨F, hF, hFG⟩ := hv
  exact (hasDerivAt_orbit hF hFG hX).differentiableAt

theorem dRep_linear : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hG : IsLinRed G)
    (hrep : Formalism.QuantumDeterminants.IsCRepOn G π) {u v : H} (hu : IsSmoothVec G π u) (hv : IsSmoothVec G π v)
    {X Y : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ HCSS.lieOf G) (hY : Y ∈ HCSS.lieOf G),
    dRep π (X + Y) v = dRep π X v + dRep π Y v ∧ dRep π X (u + v) = dRep π X u + dRep π X v ∧
      ∀ c : ℂ, dRep π X (c • v) = c • dRep π X v := by
  intro n G H _ _ π hG _hrep u v hu hv X Y hX hY
  have hXY : X + Y ∈ HCSS.lieOf G := (lieOf_isLieSubalgebra hG).1 X Y hX hY
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨F, hF, hFG⟩ := hv
    simp only [dRep]
    rw [(hasDerivAt_orbit hF hFG hXY).deriv, (hasDerivAt_orbit hF hFG hX).deriv,
      (hasDerivAt_orbit hF hFG hY).deriv]
    exact (fderiv ℝ F (Matrix.of.symm (1 : Matrix (Fin n) (Fin n) ℂ))).map_add
      (Matrix.of.symm X) (Matrix.of.symm Y)
  · simp only [dRep, map_add]
    exact deriv_add (differentiableAt_orbit hu hX) (differentiableAt_orbit hv hX)
  · intro c
    simp only [dRep, map_smul]
    exact deriv_const_smul c (differentiableAt_orbit hv hX)

end GlobalTheory.CompanionTheory.Hypotheses₂.HCA.SmoothLin

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.DerivedActionCommutator
section
noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.LinRed GlobalTheory.FlagMeas GlobalTheory.RealInd GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.HCA
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.CompanionTheory.Hypotheses₂.HCA.Bracket

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def rightMul (Y : Matrix (Fin n) (Fin n) ℂ) : (Fin n → Fin n → ℂ) →L[ℝ] (Fin n → Fin n → ℂ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun z => Matrix.of.symm (Matrix.of z * Y)
      map_add' := fun x y => by
        ext a b
        simp [Matrix.mul_apply, add_mul, Finset.sum_add_distrib]
      map_smul' := fun r x => by
        ext a b
        simp [Matrix.mul_apply, Finset.mul_sum, mul_assoc] }

theorem rightMul_apply (Y : Matrix (Fin n) (Fin n) ℂ) (z : Fin n → Fin n → ℂ) :
    rightMul Y z = Matrix.of.symm (Matrix.of z * Y) := rfl

open scoped Matrix.Norms.Operator in
theorem hasDerivAt_entry (X : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    HasDerivAt (fun t : ℝ => (NormedSpace.exp (t • X)) i j) (X i j) 0 := by
  have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) X (0 : ℝ)
  simp only [zero_smul, NormedSpace.exp_zero, one_mul] at h
  let L : Matrix (Fin n) (Fin n) ℂ →L[ℝ] ℂ :=
    LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ i j)
  exact L.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h

theorem hasDerivAt_curve (z : Fin n → Fin n → ℂ) (X : Matrix (Fin n) (Fin n) ℂ) :
    HasDerivAt (fun t : ℝ => (Matrix.of.symm (Matrix.of z * NormedSpace.exp (t • X)) : Fin n → Fin n → ℂ))
      (rightMul X z) 0 := by
  rw [hasDerivAt_pi]
  intro a
  rw [hasDerivAt_pi]
  intro b
  simp only [rightMul_apply, Matrix.of_symm_apply, Matrix.mul_apply, Matrix.of_apply]
  exact HasDerivAt.fun_sum (fun c _ => (hasDerivAt_entry X c b).const_mul (z a c))

def one : Fin n → Fin n → ℂ := Matrix.of.symm (1 : Matrix (Fin n) (Fin n) ℂ)

theorem of_one : Matrix.of (one (n := n)) = 1 := by simp [one]

section Smooth

variable {G : Set (Matrix (Fin n) (Fin n) ℂ)} {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {v : H}
  {F : (Fin n → Fin n → ℂ) → H}

theorem hasDerivAt_along (hG : IsLinRed G) (hF : ContDiff ℝ ∞ F)
    (hFv : ∀ z, Matrix.of z ∈ G → π (Matrix.of z) v = F z) {X : Matrix (Fin n) (Fin n) ℂ}
    (hX : X ∈ HCSS.lieOf G) {z : Fin n → Fin n → ℂ} (hz : Matrix.of z ∈ G) :
    HasDerivAt (fun t : ℝ => π (Matrix.of z * NormedSpace.exp (t • X)) v)
      (fderiv ℝ F z (rightMul X z)) 0 := by
  have hd : HasFDerivAt F (fderiv ℝ F z) (Matrix.of.symm (Matrix.of z * NormedSpace.exp ((0 : ℝ) • X))) := by
    have : (Matrix.of.symm (Matrix.of z * NormedSpace.exp ((0 : ℝ) • X)) : Fin n → Fin n → ℂ) = z := by
      simp
    rw [this]
    exact (hF.differentiable (by simp) z).hasFDerivAt
  have h := hd.comp_hasDerivAt (0 : ℝ) (hasDerivAt_curve z X)
  refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
  have hm : Matrix.of z * NormedSpace.exp (t • X) ∈ G := hG.mul_mem _ hz _ (hX t)
  have := hFv (Matrix.of.symm (Matrix.of z * NormedSpace.exp (t • X))) (by simpa using hm)
  simpa using this

theorem hasDerivAt_exp_along (hG : IsLinRed G) (hF : ContDiff ℝ ∞ F)
    (hFv : ∀ z, Matrix.of z ∈ G → π (Matrix.of z) v = F z) {X : Matrix (Fin n) (Fin n) ℂ}
    (hX : X ∈ HCSS.lieOf G) :
    HasDerivAt (fun t : ℝ => π (NormedSpace.exp (t • X)) v) (fderiv ℝ F one (rightMul X one)) 0 := by
  have h := hasDerivAt_along hG hF hFv hX (z := one) (by rw [of_one]; exact hG.one_mem)
  simpa [of_one] using h

theorem dRep_eq (hG : IsLinRed G) (hF : ContDiff ℝ ∞ F)
    (hFv : ∀ z, Matrix.of z ∈ G → π (Matrix.of z) v = F z) {X : Matrix (Fin n) (Fin n) ℂ}
    (hX : X ∈ HCSS.lieOf G) : dRep π X v = fderiv ℝ F one (rightMul X one) :=
  (hasDerivAt_exp_along hG hF hFv hX).deriv

theorem rep_dRep (hG : IsLinRed G) (hrep : Formalism.QuantumDeterminants.IsCRepOn G π) (hF : ContDiff ℝ ∞ F)
    (hFv : ∀ z, Matrix.of z ∈ G → π (Matrix.of z) v = F z) {X : Matrix (Fin n) (Fin n) ℂ}
    (hX : X ∈ HCSS.lieOf G) {z : Fin n → Fin n → ℂ} (hz : Matrix.of z ∈ G) :
    π (Matrix.of z) (dRep π X v) = fderiv ℝ F z (rightMul X z) := by
  have h1 := hasDerivAt_exp_along hG hF hFv hX
  have h2 := ((π (Matrix.of z)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1
  have h3 := hasDerivAt_along hG hF hFv hX hz
  rw [dRep_eq hG hF hFv hX]
  refine HasDerivAt.unique ?_ h3
  refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
  have := hrep.2 _ hz _ (hX t)
  simp [this]

theorem dRep_dRep (hG : IsLinRed G) (hrep : Formalism.QuantumDeterminants.IsCRepOn G π) (hF : ContDiff ℝ ∞ F)
    (hFv : ∀ z, Matrix.of z ∈ G → π (Matrix.of z) v = F z) {X Y : Matrix (Fin n) (Fin n) ℂ}
    (hX : X ∈ HCSS.lieOf G) (hY : Y ∈ HCSS.lieOf G) :
    dRep π X (dRep π Y v) =
      fderiv ℝ (fderiv ℝ F) one (rightMul X one) (rightMul Y one) +
        fderiv ℝ F one (rightMul Y (rightMul X one)) := by
  have hF1 : ContDiff ℝ 1 (fderiv ℝ F) := hF.fderiv_right (by norm_cast)
  have hdF : HasFDerivAt (fderiv ℝ F) (fderiv ℝ (fderiv ℝ F) one) one :=
    (hF1.differentiable (by simp) one).hasFDerivAt
  have hG1 := hdF.clm_apply (rightMul Y).hasFDerivAt
  have hc := hasDerivAt_curve (one (n := n)) X
  have h0 : (Matrix.of.symm (Matrix.of (one (n := n)) * NormedSpace.exp ((0 : ℝ) • X)) : Fin n → Fin n → ℂ) = one := by
    simp [one]
  have h := hG1.comp_hasDerivAt_of_eq (0 : ℝ) hc h0.symm
  have h' : HasDerivAt (fun t : ℝ => π (NormedSpace.exp (t • X)) (dRep π Y v)) _ 0 :=
    h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => by
      have := rep_dRep hG hrep hF hFv hY (z := Matrix.of.symm (NormedSpace.exp (t • X)))
        (by simpa using hX t)
      simpa [of_one, Function.comp_def] using this)
  refine h'.deriv.trans ?_
  simp [add_comm]

end Smooth

theorem dRep_bracket {G : Set (Matrix (Fin n) (Fin n) ℂ)} {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hG : IsLinRed G) (hrep : Formalism.QuantumDeterminants.IsCRepOn G π) {v : H} (hv : IsSmoothVec G π v)
    {X Y : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ HCSS.lieOf G) (hY : Y ∈ HCSS.lieOf G) :
    dRep π (X * Y - Y * X) v = dRep π X (dRep π Y v) - dRep π Y (dRep π X v) := by
  obtain ⟨F, hF, hFv⟩ := hv
  have hZ : X * Y - Y * X ∈ HCSS.lieOf G := (GlobalTheory.T.lie_algebra_of_linear_group_closed hG).2.2.1 X Y hX hY
  have hsymm : IsSymmSndFDerivAt ℝ F one :=
    (hF.contDiffAt).isSymmSndFDerivAt (by
      simp only [minSmoothness_of_isRCLikeNormedField]
      exact WithTop.coe_le_coe.2 le_top)
  rw [dRep_dRep hG hrep hF hFv hX hY, dRep_dRep hG hrep hF hFv hY hX, dRep_eq hG hF hFv hZ,
    hsymm.eq (rightMul X one) (rightMul Y one), add_sub_add_left_eq_sub, ← map_sub]
  congr 1
  ext a b
  simp [rightMul_apply, one, Matrix.sub_apply]

theorem smooth_bracket : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hG : IsLinRed G) (hrep : Formalism.QuantumDeterminants.IsCRepOn G π) {v : H} (hv : IsSmoothVec G π v) {X Y : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ HCSS.lieOf G) (hY : Y ∈ HCSS.lieOf G), dRep π (X * Y - Y * X) v = dRep π X (dRep π Y v) - dRep π Y (dRep π X v) :=
  fun hG hrep _ hv _ _ hX hY => dRep_bracket hG hrep hv hX hY

end GlobalTheory.CompanionTheory.Hypotheses₂.HCA.Bracket

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.FiniteEpsilonFactorDependenceOnSStatement
section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds GlobalTheory.HeckeEps GlobalTheory.CompanionTheory.HeckeBridge GroundTheory.Global GroundTheory.LocalField GroundTheory.Global.IdeleGroup
open GroundTheory.Automorphic.GodementSection (localChar)
open Formalism.L2.Host (unif atFin unif_spec)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_epsilon_factor_dependence_on_s : ∀ (E : Type) [Field E] [NumberField E] (χ : HChar E) (a : HeightOneSpectrum (𝓞 E) →₀ ℕ) (s : ℂ), finEps χ a s = finEps χ a (1 / 2) * (((discr E).natAbs * a.prod fun v k => Ideal.absNorm v.asIdeal ^ k : ℕ) : ℂ) ^ (1 / 2 - s) := by
  first | exact @GlobalTheory.CompanionTheory.HeckeBridge.finEps_shift | exact GlobalTheory.CompanionTheory.HeckeBridge.finEps_shift | (intros; apply GlobalTheory.CompanionTheory.HeckeBridge.finEps_shift <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.HaarIntegralIntegersFiniteSumStatement
section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds GlobalTheory.HeckeEps GlobalTheory.CompanionTheory.HeckeBridge GroundTheory.Global GroundTheory.LocalField GroundTheory.Global.IdeleGroup
open GroundTheory.Automorphic.GodementSection (localChar)
open Formalism.L2.Host (unif atFin unif_spec)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.haar_integral_integers_finite_sum : ∀ (E : Type) [Field E] [NumberField E] (v : HeightOneSpectrum (𝓞 E)) (m : ℕ) (g : v.adicCompletion E → ℂ), (∀ y, 1 < Valued.v y → g y = 0) → (∀ y h : v.adicCompletion E, Valued.v h ≤ WithZero.exp (-(m : ℤ)) → g (y + h) = g y) → ∫ y, g y ∂haarIntegers (v.adicCompletion E) = (((Ideal.absNorm v.asIdeal ^ m : ℕ) : ℂ))⁻¹ * ∑ᶠ r : 𝓞 E ⧸ v.asIdeal ^ m, g (algebraMap E (v.adicCompletion E) ((Quotient.out r : 𝓞 E) : E)) := by
  first | exact @GlobalTheory.CompanionTheory.PeriodicInt.integral_eq_finsum | exact GlobalTheory.CompanionTheory.PeriodicInt.integral_eq_finsum | (intros; apply GlobalTheory.CompanionTheory.PeriodicInt.integral_eq_finsum <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.HeckeCharacterConductorExponentStatement
section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds GlobalTheory.HeckeEps GlobalTheory.CompanionTheory.HeckeBridge GroundTheory.Global GroundTheory.LocalField GroundTheory.Global.IdeleGroup
open GroundTheory.Automorphic.GodementSection (localChar)
open Formalism.L2.Host (unif atFin unif_spec)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hecke_character_conductor_exponent : ∀ (E : Type) [Field E] [NumberField E] (χ : HChar E) (hu : IsUnitary χ) (v : HeightOneSpectrum (𝓞 E)) (m : ℕ), ExpAt χ v m → multiplicity v.asIdeal (toHecke χ hu).conductor = m := by
  first | exact @GlobalTheory.CompanionTheory.HeckeBridge.multiplicity_conductor_toHecke | exact GlobalTheory.CompanionTheory.HeckeBridge.multiplicity_conductor_toHecke | (intros; apply GlobalTheory.CompanionTheory.HeckeBridge.multiplicity_conductor_toHecke <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.HeckeGaussSumLocalTermStatement
section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds GlobalTheory.HeckeEps GlobalTheory.CompanionTheory.HeckeBridge GroundTheory.Global GroundTheory.LocalField GroundTheory.Global.IdeleGroup
open GroundTheory.Automorphic.GodementSection (localChar)
open Formalism.L2.Host (unif atFin unif_spec)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hecke_gauss_sum_local_term : ∀ (E : Type) [Field E] [NumberField E] (χ : HChar E) (hu : IsUnitary χ) (v : HeightOneSpectrum (𝓞 E)) (m : ℕ), m ≠ 0 → ExpAt χ v m → ∑ᶠ r : 𝓞 E ⧸ v.asIdeal ^ m, (toHecke χ hu).finiteTest v (algebraMap E (v.adicCompletion E) ((Quotient.out r : 𝓞 E) : E)) * psiAt v (((atFin v (unif v ^ (m + diffExp v)) : (v.adicCompletion E)ˣ) : v.adicCompletion E)⁻¹ * algebraMap E (v.adicCompletion E) ((Quotient.out r : 𝓞 E) : E)) = gaussSumAt χ v m (unif v ^ (m + diffExp v)) := by
  first | exact @GlobalTheory.CompanionTheory.HeckeBridge.GaussSum.finiteTest_sum_eq_gaussSumAt | exact GlobalTheory.CompanionTheory.HeckeBridge.GaussSum.finiteTest_sum_eq_gaussSumAt | (intros; apply GlobalTheory.CompanionTheory.HeckeBridge.GaussSum.finiteTest_sum_eq_gaussSumAt <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.HeckeLFunctionEulerProductStatement
section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds GlobalTheory.HeckeEps GlobalTheory.CompanionTheory.HeckeBridge GroundTheory.Global GroundTheory.LocalField GroundTheory.Global.IdeleGroup
open GroundTheory.Automorphic.GodementSection (localChar)
open Formalism.L2.Host (unif atFin unif_spec)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hecke_L_function_euler_product : ∀ (E : Type) [Field E] [NumberField E] (χ : HChar E) (hu : IsUnitary χ) (s : ℂ), 1 < s.re → HasProd (eulerFactor χ s) ((toHecke χ hu).LFunction s) := by
  first | exact @GlobalTheory.CompanionTheory.HeckeBridge.hasProd_eulerFactor_toHecke | exact GlobalTheory.CompanionTheory.HeckeBridge.hasProd_eulerFactor_toHecke | (intros; apply GlobalTheory.CompanionTheory.HeckeBridge.hasProd_eulerFactor_toHecke <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.HermitianFormLieWordGrowth
section
open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.LinRed GlobalTheory.FlagMeas GlobalTheory.RealInd GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.HCA
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.CompanionTheory.HCForm

theorem skew_of_diag {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (T : Module.End ℂ E) (A : ℝ) (hA : 0 ≤ A)
    (h : ∀ x, |(⟪T x, x⟫_ℂ + ⟪x, T x⟫_ℂ).re| ≤ A * ‖x‖ ^ 2) (u v : E) :
    |(⟪T u, v⟫_ℂ + ⟪u, T v⟫_ℂ).re| ≤ A * ‖u‖ * ‖v‖ := by
  set R : E → E → ℝ := fun u v => (⟪T u, v⟫_ℂ + ⟪u, T v⟫_ℂ).re with hR
  have hsym : ∀ u v, R v u = R u v := by
    intro u v
    simp only [hR, Complex.add_re]
    rw [← inner_conj_symm (T v) u, ← inner_conj_symm v (T u)]
    simp only [Complex.conj_re]
    ring
  have hpol : ∀ u v, 4 * R u v = R (u + v) (u + v) - R (u - v) (u - v) := by
    intro u v
    have := hsym u v
    simp only [hR, map_add, map_sub, inner_add_left, inner_add_right, inner_sub_left,
      inner_sub_right, Complex.add_re, Complex.sub_re] at this ⊢
    linarith
  have hhalf : ∀ u v, |R u v| ≤ A * (‖u‖ ^ 2 + ‖v‖ ^ 2) / 2 := by
    intro u v
    have h1 := abs_le.mp (h (u + v))
    have h2 := abs_le.mp (h (u - v))
    have hp := parallelogram_law_with_norm ℂ u v
    have e := hpol u v
    have hp' : ‖u + v‖ ^ 2 + ‖u - v‖ ^ 2 = 2 * (‖u‖ ^ 2 + ‖v‖ ^ 2) := by nlinarith
    have hb : A * ‖u + v‖ ^ 2 + A * ‖u - v‖ ^ 2 = 2 * A * (‖u‖ ^ 2 + ‖v‖ ^ 2) := by
      rw [← mul_add, hp']; ring
    change |R u v| ≤ _
    have g1 : R (u + v) (u + v) ≤ A * ‖u + v‖ ^ 2 := h1.2
    have g2 : -(A * ‖u + v‖ ^ 2) ≤ R (u + v) (u + v) := h1.1
    have g3 : R (u - v) (u - v) ≤ A * ‖u - v‖ ^ 2 := h2.2
    have g4 : -(A * ‖u - v‖ ^ 2) ≤ R (u - v) (u - v) := h2.1
    rw [abs_le]
    constructor <;> nlinarith
  change |R u v| ≤ _
  rcases eq_or_ne u 0 with rfl | hu
  · simp [hR]
  rcases eq_or_ne v 0 with rfl | hv
  · simp [hR]
  have hs : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have ht : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hscale : R (((‖v‖ : ℝ) : ℂ) • u) (((‖u‖ : ℝ) : ℂ) • v) = ‖v‖ * ‖u‖ * R u v := by
    simp only [hR, map_smul, inner_smul_left, inner_smul_right, Complex.conj_ofReal,
      Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    ring
  have hb := hhalf (((‖v‖ : ℝ) : ℂ) • u) (((‖u‖ : ℝ) : ℂ) • v)
  rw [hscale, norm_smul, norm_smul, abs_mul, abs_of_pos (mul_pos ht hs)] at hb
  simp only [Complex.norm_real, norm_norm] at hb
  have hst : 0 < ‖v‖ * ‖u‖ := mul_pos ht hs
  have : ‖v‖ * ‖u‖ * |R u v| ≤ ‖v‖ * ‖u‖ * (A * ‖u‖ * ‖v‖) := by
    calc _ ≤ _ := hb
      _ = _ := by ring
  exact le_of_mul_le_mul_left this hst

theorem nelson_inner {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {d : ℕ}
    (X : Fin d → Module.End ℂ E) (c : Fin d → Fin d → Fin d → ℂ)
    (hc : ∀ i j, X i * X j - X j * X i = ∑ l, c i j l • X l) (A : ℝ) (hA : 0 ≤ A)
    (hs : ∀ i x, |2 * (⟪X i x, x⟫_ℂ).re| ≤ A * (⟪x, x⟫_ℂ).re)
    (V : Submodule ℂ E) [FiniteDimensional ℂ V] (hV : ∀ u ∈ V, (∑ i, X i * X i) u ∈ V) :
    ∃ C : ℝ, 0 < C ∧ ∀ (l : List (Fin d)), ∀ u ∈ V,
      Real.sqrt (⟪(l.map X).prod u, (l.map X).prod u⟫_ℂ).re ≤
        C ^ (l.length + 1) * l.length.factorial * Real.sqrt (⟪u, u⟫_ℂ).re := by
  have hsq : ∀ x : E, Real.sqrt (⟪x, x⟫_ℂ).re = ‖x‖ := by
    intro x
    rw [inner_self_eq_norm_sq_to_K]
    norm_cast
    exact Real.sqrt_sq (norm_nonneg x)
  have hskew : ∀ i u v, |(⟪X i u, v⟫_ℂ + ⟪u, X i v⟫_ℂ).re| ≤ A * ‖u‖ * ‖v‖ := by
    intro i
    refine skew_of_diag (X i) A hA ?_
    intro x
    have e : (⟪X i x, x⟫_ℂ + ⟪x, X i x⟫_ℂ).re = 2 * (⟪X i x, x⟫_ℂ).re := by
      rw [Complex.add_re, ← inner_conj_symm x (X i x), Complex.conj_re]
      ring
    have n : (⟪x, x⟫_ℂ).re = ‖x‖ ^ 2 := by
      rw [inner_self_eq_norm_sq_to_K]
      norm_cast
    rw [e, ← n]
    exact hs i x
  obtain ⟨C, hC, hb⟩ := GlobalTheory.T.nelson_exists_word_growth_constant X c hc A hA hskew V hV
  refine ⟨C, hC, fun l u hu => ?_⟩
  rw [hsq, hsq]
  exact hb l u hu

theorem nelson_form : ∀ {M : Type} [AddCommGroup M] [Module ℂ M] (Q : M → M → ℂ)
    (hadd : ∀ x y z, Q x (y + z) = Q x y + Q x z)
    (hsmul : ∀ (c : ℂ) x y, Q x (c • y) = c * Q x y)
    (hconj : ∀ x y, Q y x = star (Q x y))
    (hpos : ∀ x, x ≠ 0 → 0 < (Q x x).re) {d : ℕ} (X : Fin d → Module.End ℂ M)
    (c : Fin d → Fin d → Fin d → ℂ) (hc : ∀ i j, X i * X j - X j * X i = ∑ l, c i j l • X l)
    (A : ℝ) (hA : 0 ≤ A) (hs : ∀ i x, |2 * (Q (X i x) x).re| ≤ A * (Q x x).re)
    (V : Submodule ℂ M) [FiniteDimensional ℂ V] (hV : ∀ u ∈ V, (∑ i, X i * X i) u ∈ V),
    ∃ C : ℝ, 0 < C ∧ ∀ (l : List (Fin d)), ∀ u ∈ V,
      Real.sqrt (Q ((l.map X).prod u) ((l.map X).prod u)).re ≤
        C ^ (l.length + 1) * l.length.factorial * Real.sqrt (Q u u).re := by
  intro M _ _ Q hadd hsmul hconj hpos d X c hc A hA hs V _ hV
  have hzero : ∀ x, Q x 0 = 0 := by
    intro x
    have := hsmul 0 x 0
    simpa using this
  have hzero' : Q 0 0 = 0 := hzero 0
  let core : InnerProductSpace.Core ℂ M :=
    { inner := Q
      conj_inner_symm := fun x y => by
        change star (Q y x) = Q x y
        rw [hconj x y, star_star]
      re_inner_nonneg := fun x => by
        change 0 ≤ (Q x x).re
        rcases eq_or_ne x 0 with rfl | hx
        · simp [hzero']
        · exact (hpos x hx).le
      add_left := fun x y z => by
        change Q (x + y) z = Q x z + Q y z
        rw [hconj z (x + y), hadd, star_add, ← hconj, ← hconj]
      smul_left := fun x y r => by
        change Q (r • x) y = star r * Q x y
        rw [hconj y (r • x), hsmul, star_mul', ← hconj]
      definite := fun x hx => by
        by_contra hne
        have h0 : Q x x = 0 := hx
        have := hpos x hne
        simp [h0] at this }
  letI : NormedAddCommGroup M := core.toNormedAddCommGroup
  letI : InnerProductSpace ℂ M := InnerProductSpace.ofCore core.toCore
  exact nelson_inner X c hc A hA hs V hV

end GlobalTheory.CompanionTheory.HCForm
end

