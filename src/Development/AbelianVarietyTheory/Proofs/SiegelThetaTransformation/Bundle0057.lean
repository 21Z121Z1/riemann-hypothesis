import Mathlib
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AdmissibleDoubledHermitianThetaFamily
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0036
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0042
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0056
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0050
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0051
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0073
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0079
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0054
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaSeriesTestFunctionHolomorphicWeight
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelTestFunctionFiniteSumEquivariant
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0045
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0034
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle0008

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AdmissibleDoubledHermitianThetaFamilyStatement
section
open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.admissible_doubledHermitianThetaFamily : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ (D : Level X) (hn : r ≤ n) (M : ℕ), 0 < M → (M : 𝓞 E) ∈ D.𝔪 → ∀ v₀ : Lt E r → TF n g, (∀ L ∈ D.lats, IsVac X bas D.w (tens (stdL E n) (D.sh L)) (v₀ L)) → ∀ L ∈ D.lats, ∀ L' ∈ D.lats, ∃ R, admitted M R fun Λ => dbl X bas idx (D.phi bas hn v₀ L Λ) (D.phi bas hn v₀ L' Λ) := by
  first | exact @GlobalTheory.SW.DblAdm.adm_dbl_phi_of_isVac | exact GlobalTheory.SW.DblAdm.adm_dbl_phi_of_isVac | (intros; apply GlobalTheory.SW.DblAdm.adm_dbl_phi_of_isVac <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AnnihilationCreationPeriodCoordinates
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Ker.HeisDeriv

section Classical

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g n : ℕ} (X : Data E r)
  (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (x : Frame X.Ψ r)

theorem hx_add_left (z z' w : Fin g → ℂ) :
    hx X bas idx x (z + z') w = hx X bas idx x z w + hx X bas idx x z' w := by
  simp only [hx, Matrix.mulVec_add, add_dotProduct]

theorem hx_add_right (z w w' : Fin g → ℂ) :
    hx X bas idx x z (w + w') = hx X bas idx x z w + hx X bas idx x z w' := by
  simp only [hx, Matrix.mulVec_add, star_add, dotProduct_add]

theorem hx_smul_left (c : ℂ) (z w : Fin g → ℂ) :
    hx X bas idx x (c • z) w = c * hx X bas idx x z w := by
  simp only [hx, Matrix.mulVec_smul, smul_dotProduct, smul_eq_mul]

theorem hx_smul_right (c : ℂ) (z w : Fin g → ℂ) :
    hx X bas idx x z (c • w) = conj c * hx X bas idx x z w := by
  simp only [hx, Matrix.mulVec_smul, star_smul, dotProduct_smul, smul_eq_mul, Complex.star_def]

theorem hx_rsmul_left (t : ℝ) (z w : Fin g → ℂ) :
    hx X bas idx x (t • z) w = t * hx X bas idx x z w := by
  rw [← Complex.coe_smul, hx_smul_left]

theorem hx_rsmul_right (t : ℝ) (z w : Fin g → ℂ) :
    hx X bas idx x z (t • w) = t * hx X bas idx x z w := by
  rw [← Complex.coe_smul, hx_smul_right, Complex.conj_ofReal]

theorem hasDerivAt_translate (hs : ∀ z w, hx X bas idx x w z = conj (hx X bas idx x z w))
    (Φ : (Fin n → Fin g → ℂ) → ℂ) (hΦ : Differentiable ℝ Φ) (ζ u : Fin n → Fin g → ℂ) :
    HasDerivAt (fun t : ℝ => cexp (π * I * ((∑ k, hx X bas idx x (ζ k) ((t • u) k)).im : ℝ)) *
      (gaussR X bas idx x (ζ + t • u) * Φ (ζ + t • u)))
      (gaussR X bas idx x ζ * (-(π * ∑ k, hx X bas idx x (u k) (ζ k)) * Φ ζ + fderiv ℝ Φ ζ u)) 0 := by
  have hab : ∑ k, hx X bas idx x (ζ k) (u k) = conj (∑ k, hx X bas idx x (u k) (ζ k)) := by
    rw [map_sum]
    exact Finset.sum_congr rfl fun k _ => hs (u k) (ζ k)
  have hph : ∀ t : ℝ, (((∑ k, hx X bas idx x (ζ k) ((t • u) k)).im : ℝ) : ℂ) =
      (t : ℂ) * (((∑ k, hx X bas idx x (ζ k) (u k)).im : ℝ) : ℂ) := by
    intro t
    have h : ∑ k, hx X bas idx x (ζ k) ((t • u) k) = (t : ℂ) * ∑ k, hx X bas idx x (ζ k) (u k) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by rw [Pi.smul_apply, hx_rsmul_right]
    rw [h, Complex.im_ofReal_mul, Complex.ofReal_mul]
  have hq : ∀ t : ℝ, ∑ k, hx X bas idx x ((ζ + t • u) k) ((ζ + t • u) k) =
      ∑ k, hx X bas idx x (ζ k) (ζ k) +
        (t : ℂ) * (∑ k, hx X bas idx x (ζ k) (u k) + ∑ k, hx X bas idx x (u k) (ζ k)) +
        (t : ℂ) ^ 2 * ∑ k, hx X bas idx x (u k) (u k) := by
    intro t
    rw [← Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [Pi.add_apply, Pi.smul_apply, hx_add_left, hx_add_right, hx_rsmul_left, hx_rsmul_right]
    ring
  have hT : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).ofReal_comp
  have hE : HasDerivAt (fun t : ℝ => (Real.pi : ℂ) * I * ((t : ℂ) * (((∑ k, hx X bas idx x (ζ k) (u k)).im : ℝ) : ℂ)) -
        (Real.pi : ℂ) / 2 * (∑ k, hx X bas idx x (ζ k) (ζ k) +
          (t : ℂ) * (∑ k, hx X bas idx x (ζ k) (u k) + ∑ k, hx X bas idx x (u k) (ζ k)) +
          (t : ℂ) ^ 2 * ∑ k, hx X bas idx x (u k) (u k)))
      ((Real.pi : ℂ) * I * (((∑ k, hx X bas idx x (ζ k) (u k)).im : ℝ) : ℂ) -
        (Real.pi : ℂ) / 2 * (∑ k, hx X bas idx x (ζ k) (u k) + ∑ k, hx X bas idx x (u k) (ζ k))) 0 := by
    have h := ((hT.mul_const (((∑ k, hx X bas idx x (ζ k) (u k)).im : ℝ) : ℂ)).const_mul ((Real.pi : ℂ) * I)).sub
      ((((hT.mul_const (∑ k, hx X bas idx x (ζ k) (u k) + ∑ k, hx X bas idx x (u k) (ζ k))).const_add
        (∑ k, hx X bas idx x (ζ k) (ζ k))).add ((hT.pow 2).mul_const (∑ k, hx X bas idx x (u k) (u k)))).const_mul
          ((Real.pi : ℂ) / 2))
    exact h.congr_deriv (by simp)
  have hL : HasDerivAt (fun t : ℝ => ζ + t • u) u 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const u).const_add ζ
  have hΦt : HasDerivAt (fun t : ℝ => Φ (ζ + t • u)) (fderiv ℝ Φ ζ u) 0 :=
    (hΦ ζ).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hL (by simp)
  have hF := hE.cexp.mul hΦt
  refine (hF.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
  · have key : (Real.pi : ℂ) * I * (((∑ k, hx X bas idx x (ζ k) (u k)).im : ℝ) : ℂ) -
        (Real.pi : ℂ) / 2 * (∑ k, hx X bas idx x (ζ k) (u k) + ∑ k, hx X bas idx x (u k) (ζ k)) =
        -((Real.pi : ℂ) * ∑ k, hx X bas idx x (u k) (ζ k)) := by
      rw [hab]
      generalize ∑ k, hx X bas idx x (u k) (ζ k) = b
      have e1 : conj b = (b.re : ℂ) - (b.im : ℂ) * I := by apply Complex.ext <;> simp
      have e2 : b = (b.re : ℂ) + (b.im : ℂ) * I := (Complex.re_add_im b).symm
      rw [Complex.conj_im, e1]
      push_cast
      linear_combination ((Real.pi : ℂ) / 2) * e2
    rw [key]
    simp only [Complex.ofReal_zero, zero_mul, mul_zero, add_zero, zero_smul, zero_sub,
      ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    unfold GlobalTheory.Ker.gaussR
    ring
  · beta_reduce
    rw [hph t]
    unfold GlobalTheory.Ker.gaussR
    rw [hq t, ← mul_assoc, ← Complex.exp_add]
    congr 2

end Classical

variable {D : D7} {S T : HSp D}

theorem dRho_eq (C : Ctx S T) (B : C.Bas) (hB : C.IsB B) (G : WO S T → ℂ)
    (Φ : (Fin S.rank → Fin C.g → ℂ) → ℂ) (hΦ : Differentiable ℝ Φ)
    (hG : ∀ w, IsRealPt w → G w = gaussR C.X C.bas C.idx (C.xB B) (C.zOf (C.xB B) w) * Φ (C.zOf (C.xB B) w))
    (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (u : Fin S.rank → Fin C.g → ℂ)
    (hu : u = zR C.X C.idx (C.xB B) (Pi.single (C.m.e τ) (fun k a => conj (z a k)) : WR C.X S.rank))
    (w : WO S T) (hw : IsRealPt w) :
    Formalism.IndefR.Datum.dRho (heisO C.ψ S T) C.θ τ z G w =
      gaussR C.X C.bas C.idx (C.xB B) (C.zOf (C.xB B) w) *
        (-(π * ∑ k, hx C.X C.bas C.idx (C.xB B) (u k) (C.zOf (C.xB B) w k)) * Φ (C.zOf (C.xB B) w) +
          fderiv ℝ Φ (C.zOf (C.xB B) w) u) := by
  obtain ⟨R, -, -, -, hR1, hR2, -, -, hline, -⟩ := GlobalTheory.T.realPoints_classicalModel_realVectorSpace D S T C
  have hdom : C.xB B ∈ C.X.dom := ((GlobalTheory.T.thetaKernel_orthonormalFrame_inDomain_periodLinear D S T C).2 B hB).2.1
  have hs := (GlobalTheory.Dict.hx_laws D.host.E T.rank C.X C.g C.bas C.idx S.rank C.sympl C.even (C.xB B) hdom).1
  have hE := (zR_laws D.host.E T.rank C.X C.g C.q0 C.hr C.bas C.idx S.rank C.sympl C.even (C.xB B) hdom).2.1
  have hψ := (GlobalTheory.T.symplecticCharacter_real_finite_points_match D S T C).2.1
  have hlin : ∀ (a : WR C.X S.rank) (t : ℝ) (b : WR C.X S.rank),
      zR C.X C.idx (C.xB B) (a + t • b) = zR C.X C.idx (C.xB B) a + t • zR C.X C.idx (C.xB B) b := by
    intro a t b
    have h := (zRLin C.X C.idx (C.xB B) (n := S.rank)).map_add a (t • b)
    rw [map_smul] at h
    exact h
  have hsm : ∀ (t : ℝ) (b : WR C.X S.rank),
      zR C.X C.idx (C.xB B) (t • b) = t • zR C.X C.idx (C.xB B) b := fun t b =>
    (zRLin C.X C.idx (C.xB B) (n := S.rank)).map_smul t b
  have hT := hasDerivAt_translate C.X C.bas C.idx (C.xB B) hs Φ hΦ (C.zOf (C.xB B) w) u
  unfold Formalism.IndefR.Datum.dRho heisO
  refine (hT.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)).deriv
  beta_reduce
  have hw' : w + lineAt C.θ τ z t =
      R (C.realPt w + t • (Pi.single (C.m.e τ) (fun k a => conj (z a k)) : WR C.X S.rank)) := by
    rw [hline, map_add, hR2 w hw]
  have hz : C.zOf (C.xB B)
      (R (C.realPt w + t • (Pi.single (C.m.e τ) (fun k a => conj (z a k)) : WR C.X S.rank))) =
      C.zOf (C.xB B) w + t • u := by
    unfold Ctx.zOf
    rw [(hR1 _).2, hlin, hu]
  rw [hw', hG _ (hR1 _).1, hz, hline, hψ w _ hw (hR1 _).1, (hR1 _).2, ← hE, hsm, ← hu]
  rfl

end GlobalTheory.Ker.HeisDeriv

theorem GlobalTheory.Ker.annih_crea_coord : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), ∀ B, C.IsB B → ∀ (G : WO S T → ℂ) (Φ : (Fin S.rank → Fin C.g → ℂ) → ℂ), Differentiable ℝ Φ → (∀ w, IsRealPt w → G w = gaussR C.X C.bas C.idx (C.xB B) (C.zOf (C.xB B) w) * Φ (C.zOf (C.xB B) w)) → ∀ (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (u : Fin S.rank → Fin C.g → ℂ), u = zR C.X C.idx (C.xB B) (Pi.single (C.m.e τ) (fun k a => conj (z a k)) : WR C.X S.rank) → ∀ w, IsRealPt w → annih (heisO C.ψ S T) C.θ τ (cplxO 1 (C.sB B τ)) z G w = gaussR C.X C.bas C.idx (C.xB B) (C.zOf (C.xB B) w) * (fderiv ℝ Φ (C.zOf (C.xB B) w) u + I * fderiv ℝ Φ (C.zOf (C.xB B) w) (I • u)) ∧ crea (heisO C.ψ S T) C.θ τ (cplxO 1 (C.sB B τ)) z G w = gaussR C.X C.bas C.idx (C.xB B) (C.zOf (C.xB B) w) * (2 * ((-(π * ∑ k, hx C.X C.bas C.idx (C.xB B) (u k) (C.zOf (C.xB B) w k))) * Φ (C.zOf (C.xB B) w) + (1 / 2 : ℂ) * (fderiv ℝ Φ (C.zOf (C.xB B) w) u - I * fderiv ℝ Φ (C.zOf (C.xB B) w) (I • u)))) := by
  intro D S T C B hB G Φ hΦ hG τ z u hu w hw
  have h1 := GlobalTheory.Ker.HeisDeriv.dRho_eq C B hB G Φ hΦ hG τ z u hu w hw
  have hJ : I • u = zR C.X C.idx (C.xB B)
      (Pi.single (C.m.e τ) (fun k a => conj ((cplxO 1 (C.sB B τ) z) a k)) : WR C.X S.rank) := by
    rw [hu]
    exact (((GlobalTheory.T.thetaKernel_orthonormalFrame_inDomain_periodLinear D S T C).2 B hB).2.2.2.1 τ z).symm
  have h2 := GlobalTheory.Ker.HeisDeriv.dRho_eq C B hB G Φ hΦ hG τ (cplxO 1 (C.sB B τ) z) (I • u) hJ w hw
  simp only [Pi.smul_apply, GlobalTheory.Ker.HeisDeriv.hx_smul_left, ← Finset.mul_sum] at h2
  unfold Formalism.IndefR.Datum.annih Formalism.IndefR.Datum.crea
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [h1, h2]
  constructor
  · linear_combination (-(gaussR C.X C.bas C.idx (C.xB B) (C.zOf (C.xB B) w) * (Real.pi : ℂ) *
      (∑ k, hx C.X C.bas C.idx (C.xB B) (u k) (C.zOf (C.xB B) w k)) * Φ (C.zOf (C.xB B) w))) * I_sq
  · linear_combination (gaussR C.X C.bas C.idx (C.xB B) (C.zOf (C.xB B) w) * (Real.pi : ℂ) *
      (∑ k, hx C.X C.bas C.idx (C.xB B) (u k) (C.zOf (C.xB B) w k)) * Φ (C.zOf (C.xB B) w)) * I_sq
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaFunctionSpaceHeisenbergLaws
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ThetaSpace

open GlobalTheory.WeilVacMove

variable {D : D7} {S T : HSp D}

theorem stdL_full (E : Type) [Field E] [NumberField E] (r : ℕ) :
    (stdL E r).FG ∧ Submodule.span E (stdL E r : Set (Fin r → E)) = ⊤ := by
  refine ⟨Submodule.fg_span (Set.finite_range _), ?_⟩
  rw [eq_top_iff, ← (Pi.basisFun E (Fin r)).span_eq]
  refine Submodule.span_mono ?_
  rintro _ ⟨a, rfl⟩
  exact Submodule.subset_span ⟨a, by simp⟩

theorem map_sub_eq_zero {A B : Type} [Ring A] [Ring B] (φ : A →+* B) {a b : A} (ha : φ a = 0) (hb : φ b = 0) :
    φ (a - b) = 0 := by rw [map_sub, ha, hb, sub_zero]

theorem map_nsmul_eq_zero {A B : Type} [Ring A] [Ring B] (φ : A →+* B) {a : A} (ha : φ a = 0) (N : ℕ) :
    φ (N • a) = 0 := by rw [map_nsmul, ha, smul_zero]

theorem isRealPt_sub {u v : WO S T} (hu : IsRealPt u) (hv : IsRealPt v) : IsRealPt (u - v) := by
  ext i j
  have h1 : finPart D (u i j) = 0 := congrFun (congrFun hu i) j
  have h2 : finPart D (v i j) = 0 := congrFun (congrFun hv i) j
  exact map_sub_eq_zero (finPart D) h1 h2

theorem isFinPt_nsmul {u : WO S T} (hu : IsFinPt u) (N : ℕ) : IsFinPt (N • u) := by
  ext i j
  have h1 : infPart D (u i j) = 0 := congrFun (congrFun hu i) j
  exact map_nsmul_eq_zero (infPart D) h1 N

theorem exists_fin_add_real (C : Ctx S T) (w : WO S T) : ∃ u v, IsFinPt u ∧ IsRealPt v ∧ w = u + v := by
  obtain ⟨R, -, -, -, h1, -, h2, -⟩ := GlobalTheory.T.realPoints_classicalModel_realVectorSpace D S T C
  exact ⟨_, _, h2 w, (h1 _).1, (sub_add_cancel _ _).symm⟩

theorem isTh_rho (C : Ctx S T) {f : WO S T → ℂ} (hf : C.IsTh f) (w : WO S T) : C.IsTh (C.rho w f) := by
  obtain ⟨u, v, hu, hv, rfl⟩ := exists_fin_add_real C w
  have h := GlobalTheory.FinTranslate.isTheta_heisO_fin C.std.1 hu (isTheta_heisO_real C.std hv hf)
  rwa [heisO_heisO, (symplOH_fin_real S T u v hu hv).1, AddChar.map_zero_eq_one, one_smul] at h

theorem exists_level (C : Ctx S T) {f : WO S T → ℂ} (hf : C.IsTh f) :
    ∃ N : ℕ, 0 < N ∧ ∀ u ∈ hatA S T (tens (stdL D.host.E S.rank) C.X.Λ), C.rho (N • u) f = f := by
  obtain ⟨-, -, h3, h4, -⟩ := GlobalTheory.T.completedTensorLattice_strongApprox_open_compact D S T C _ _ (stdL_full D.host.E S.rank) ⟨C.X.Λ_fg, C.X.Λ_span⟩
  obtain ⟨U, hU, h⟩ := hf.level
  obtain ⟨N, hN, hNU⟩ := h4 U hU
  exact ⟨N, hN, fun u hu => h _ (hNU u hu) (isFinPt_nsmul (h3 u hu).1 N)⟩

theorem eq_zero_of_real (C : Ctx S T) {f : WO S T → ℂ} (hf : C.IsTh f) (h0 : ∀ w, IsRealPt w → f w = 0) :
    f = 0 := by
  obtain ⟨h1, -, h3, -⟩ := GlobalTheory.T.completedTensorLattice_strongApprox_open_compact D S T C _ _ (stdL_full D.host.E S.rank) ⟨C.X.Λ_fg, C.X.Λ_span⟩
  have h7 := (GlobalTheory.T.symplecticCharacter_real_finite_points_match D S T C).2.2.2.2.2.2.2
  obtain ⟨N, hN, hl⟩ := exists_level C hf
  funext w
  obtain ⟨u, v, hu, hv, rfl⟩ := exists_fin_add_real C w
  obtain ⟨y, hy⟩ := h1 u hu
  obtain ⟨-, hy2⟩ := h3 _ hy
  obtain ⟨y', -, u', hu', e⟩ := hy2 N hN
  have hr := isRealPt_sub hv (h7 (y + y')).2.2.1
  have e1 : u + v = ratW T S (y + y')ᵀ + ((v - (ratW T S (y + y')ᵀ - finW S T (y + y'))) + N • u') := by
    rw [(h7 y).2.2.2 y', sub_eq_iff_eq_add.1 e]
    abel
  have e2 := congrFun (hl u' hu') (v - (ratW T S (y + y')ᵀ - finW S T (y + y')))
  rw [h0 _ hr] at e2
  unfold Ctx.rho heisO at e2
  rw [(symplOH_fin_real S T _ _ (isFinPt_nsmul (h3 u' hu').1 N) hr).2, AddChar.map_zero_eq_one, one_mul] at e2
  rw [e1, hf.quasi, e2, mul_zero, Pi.zero_apply]

theorem rho_finW (C : Ctx S T) {f : WO S T → ℂ} (hf : C.IsTh f) (y : Matrix (Fin S.rank) (Fin T.rank) D.host.E)
    (w : WO S T) (hw : IsRealPt w) : C.rho (finW S T y) f w =
      cexp (π * I * (EFR C.X (C.realPt w) (embR C.X y) : ℝ)) * f (w - (ratW T S yᵀ - finW S T y)) := by
  obtain ⟨-, h2, -, -, -, -, -, h7⟩ := GlobalTheory.T.symplecticCharacter_real_finite_points_match D S T C
  obtain ⟨-, -, -, hadd, -, -, -, hfin, -⟩ := GlobalTheory.T.realPoints_classicalModel_realVectorSpace D S T C
  obtain ⟨a1, a2, a3, -⟩ := h7 y
  set z := ratW T S yᵀ - finW S T y with hz
  have hr : ratW T S yᵀ = finW S T y + z := by rw [hz]; abel
  have hp : C.realPt z = embR C.X y := by
    rw [← a1, hr, hadd, hfin _ a2, zero_add]
  have e1 : w + finW S T y = ratW T S yᵀ + (w - z) := by rw [hz]; abel
  have hzz : symplOH S T z z = 0 := by
    unfold symplOH
    rw [(GlobalTheory.T.symplecticCharacter_real_finite_points_match D S T C).2.2.2.2.1, mul_zero]
  have e2 : -symplOH S T (ratW T S yᵀ) (w - z) = symplOH S T w z := by
    have e3 : symplOH S T z w = symplOH S T z (w - z) + symplOH S T z z := by
      rw [← symplOH_add_right, sub_add_cancel]
    rw [hr, symplOH_add_left, (symplOH_fin_real S T _ _ a2 (isRealPt_sub hw a3)).1, zero_add, symplOH_skew S T z w,
      e3, hzz, add_zero]
  unfold Ctx.rho heisO
  rw [(symplOH_fin_real S T _ _ a2 hw).2, AddChar.map_zero_eq_one, one_mul, e1, hf.quasi, e2, h2 w z hw a3, hp]

theorem exists_mt_eq (V : HSp D) {γ : GA D V} (h : γ ∈ GQ V) :
    ∃ m : Matrix (Fin V.rank) (Fin V.rank) D.host.E, mt V γ = m.map (incA D) := by
  obtain ⟨γ', -, e⟩ := h
  exact ⟨γ'.1, (congrArg Units.val e).symm⟩

theorem isTh_actO (C : Ctx S T) {f : WO S T → ℂ} (hf : C.IsTh f) {γ : GA D S} (hγ : γ ∈ GQ S) {γ' : GA D T}
    (hγ' : γ' ∈ GQ T) : C.IsTh fun w => f (actO S T γ γ' w) := by
  have hs : ∀ w w', symplOH S T (actO S T γ γ' w) (actO S T γ γ' w') = symplOH S T w w' := fun w w' => by
    unfold symplOH
    rw [(GlobalTheory.T.symplecticCharacter_real_finite_points_match D S T C).2.2.2.2.2.2.1]
  obtain ⟨R, -, -, -, -, -, -, -, -, hact⟩ := GlobalTheory.T.realPoints_classicalModel_realVectorSpace D S T C
  let A : WO S T →+ WO S T := AddMonoidHom.mk' (actO S T γ γ') (actO_add γ γ')
  have hA : Continuous (actO S T γ γ') := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  refine ⟨fun x w => ?_, ?_, hf.cont.comp hA, fun k L h1 h2 w => ?_⟩
  · obtain ⟨m, hm⟩ := exists_mt_eq S ((GQ S).inv_mem hγ)
    obtain ⟨m', hm'⟩ := exists_mt_eq T hγ'
    have e : actO S T γ γ' (ratW T S x) = ratW T S (m' * x * m) := by
      unfold actO ratW
      rw [hm, hm', Matrix.map_mul, Matrix.map_mul]
    rw [actO_add, ← hs, e, hf.quasi]
  · obtain ⟨U, hU, h⟩ := hf.level
    refine ⟨U.comap A, hU.preimage hA, fun u hu h0 => ?_⟩
    funext w
    have e := congrFun (h _ hu ((hact γ γ' u).2.1 h0)) (actO S T γ γ' w)
    unfold heisO at e ⊢
    rw [← e, ← hs w u]
    exact congrArg (fun x => _ * f x) (actO_add γ γ' w u)
  · have := hf.smooth k (A.comp L) (hA.comp h1) (fun t => (hact γ γ' (L t)).1 (h2 t)) (actO S T γ γ' w)
    simp only [actO_add]
    exact this

theorem theta_space_laws : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), C.IsTh 0 ∧ (∀ f f', C.IsTh f → C.IsTh f' → C.IsTh (f + f') ∧ ((∀ w, IsRealPt w → f w = f' w) → f = f')) ∧ ∀ f, C.IsTh f → (∀ a : ℂ, C.IsTh (a • f)) ∧ (∀ w, C.IsTh (C.rho w f)) ∧ (∀ w w', C.rho w (C.rho w' f) = C.ψ (symplOH S T w w') • C.rho (w + w') f) ∧ (∀ (y : Matrix (Fin S.rank) (Fin T.rank) D.host.E) w, IsRealPt w → C.rho (finW S T y) f w = cexp (π * I * (EFR C.X (C.realPt w) (embR C.X y) : ℝ)) * f (w - (ratW T S yᵀ - finW S T y))) ∧ (∀ γ ∈ GQ S, ∀ γ' ∈ GQ T, C.IsTh fun w => f (actO S T γ γ' w)) ∧ ∃ N : ℕ, 0 < N ∧ ∀ u ∈ hatA S T (tens (stdL D.host.E S.rank) C.X.Λ), C.rho (N • u) f = f := by
  intro D S T C
  refine ⟨isTheta_zero, fun f f' hf hf' => ⟨isTheta_add hf hf', fun h => ?_⟩, fun f hf =>
    ⟨fun a => isTheta_smul a hf, isTh_rho C hf, fun w w' => heisO_heisO _ _ _ _ _ _, rho_finW C hf,
      fun γ hγ γ' hγ' => isTh_actO C hf hγ hγ', exists_level C hf⟩⟩
  exact sub_eq_zero.1 (eq_zero_of_real C (isTheta_sub hf hf') fun w hw => sub_eq_zero.2 (h w hw))

end GlobalTheory.ThetaSpace

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaSeriesLowerRowsZeroEqFreeLowerRows
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict.DiagFree

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g n : ℕ} {X : Data E r}
  {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ}

theorem vset_one {M : ℕ} {Λ : Lt E n} (h : Λ ∈ Vset E n M) : Λ ∈ Vset E n 1 := by
  obtain ⟨hfg, hdual, s, hs, -, h1, h2⟩ := h
  exact ⟨hfg, hdual, s, hs, Nat.coprime_one_right s, h1, h2⟩

theorem conjI_mono {P Q : Ideal (𝓞 E)} (h : P ≤ Q) : conjI P ≤ conjI Q := by
  unfold conjI
  exact Ideal.span_mono fun _ ⟨b, hb, e⟩ => ⟨b, h hb, e⟩

theorem isSB_smul (c : ℂ) {φ : TF n g} (h : IsSB φ) : IsSB (c • φ) := by
  obtain ⟨R, hR, h1, h2⟩ := h
  refine ⟨R, hR, fun x hx => h1 x fun h0 => hx ?_, fun x y hy => ?_⟩
  · simp [h0]
  · simp [h2 x y hy]

theorem thA_sum (idx : Fin g ≃ X.Ψ × Fin r) (hs : IsSympl X bas) {x : Frame X.Ψ r}
    (hx : x ∈ X.dom) {T : Type} (s : Finset T) (f : T → TF n g) (hf : ∀ i, IsSB (f i)) :
    thA X bas idx (∑ i ∈ s, f i) x = ∑ i ∈ s, thA X bas idx (f i) x := by
  classical
  refine Finset.induction_on s ?_ ?_
  · have h0 := GlobalTheory.SW.UnAct.thA_smul (bas := bas) idx x (0 : ℂ) (0 : TF n g)
    simpa using h0
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      GlobalTheory.SW.UnAct.thA_add idx hs hx (hf a) (GlobalTheory.SW.RecSum.isSB_sum s f hf), ih]

theorem isSB_unitv_projA (idx : Fin g ≃ X.Ψ × Fin r) (hs : IsSympl X bas) (hn : Even n) {w : E}
    (hw : IsIntegral ℤ w) (hw' : w + cc w = 1) {L : Lt E r} (hL : SelfD X L) {Λ : Lt E n}
    (hΛ : Λ ∈ Vset E n 1) {φ : TF n g} (hφ : IsSB φ) :
    IsSB (unitv (projA X bas w (tens Λ L) φ)) := by
  unfold unitv projA
  refine isSB_smul _ (isSB_smul _ ?_)
  refine finsum_mem_induction (fun ψ => IsSB ψ) isSB_zero
    (fun a b ha hb => (isSB_algebra_haar_linear ℚ (Fin n) (Fin g) a b ha hb).1) ?_
  rintro _ ⟨y, -, rfl⟩
  exact isSB_smul _ ((heisG_laws E r X g bas idx n hs hn).2.2.2 y φ hφ).1

private theorem thA_finset_sum_smul (idx : Fin g ≃ X.Ψ × Fin r) (hs : IsSympl X bas) {x : Frame X.Ψ r}
    (hx : x ∈ X.dom) {T : Type} (s : Finset T) (a : T → ℂ) (ψ : T → TF n g)
    (hψ : ∀ i, IsSB (ψ i)) (z : Fin n → Fin g → ℂ) :
    thA X bas idx (∑ i ∈ s, a i • ψ i) x z = ∑ i ∈ s, a i * thA X bas idx (ψ i) x z := by
  rw [thA_sum idx hs hx s _ (fun i => isSB_smul (a i) (hψ i)), Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [GlobalTheory.SW.UnAct.thA_smul (bas := bas) idx x (a i) (ψ i)]
  rfl

theorem thP_phi_eq_thP_phiF : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g q0 : ℕ) (hr : X.p0 + q0 = r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ (D : SW.Level X) (hn : r ≤ n) (M : ℕ) (𝔐 𝔍 : Ideal (𝓞 E)), 0 < M → (M : 𝓞 E) ∈ D.𝔪 → D.𝔪 = 𝔐 * 𝔍 → IsCoprime 𝔐 𝔍 → ∀ v₀ : Lt E r → TF n g, (∀ L ∈ D.lats, IsVac X bas D.w (tens (stdL E n) (D.sh L)) (v₀ L)) → ∀ (k : X.Ψ → Fin q0 → ℕ) (k' : X.Ψ → Fin X.p0 → ℕ), ∀ Λ ∈ Vset E n M, ∀ P ∈ Harm.rowHighest ℂ k k', ∃ Λ' ∈ Vset E n M, ∃ P' ∈ Harm.rowHighest ℂ k k', ∀ L ∈ D.lats, ∀ x ∈ X.dom, thP X hr bas idx (D.phi bas hn v₀ L Λ) P x = thP X hr bas idx (phiF bas D 𝔐 hn v₀ L Λ') P' x := by
  intro E _ _ _ r X g q0 hr bas idx n hs hn D hrn M 𝔐 𝔍 hM hMm hsplit hcop v₀ hv₀ k k' Λ hΛ P hP
  have hle : D.𝔪 ≤ 𝔍 := by
    rw [hsplit]
    exact Ideal.mul_le_inf.trans inf_le_right
  have h𝔍 : 𝔍 ≠ ⊥ := by
    intro h0
    apply D.ne_bot
    rw [hsplit, h0, Ideal.mul_bot]
  have hMJ : ((M : ℕ) : 𝓞 E) ∈ 𝔍 := hle hMm
  have hcopJ : IsCoprime 𝔍 (conjI 𝔍) := by
    have h1 := D.cop
    rw [Ideal.isCoprime_iff_sup_eq] at h1 ⊢
    exact top_unique (h1.symm.le.trans (sup_le_sup hle (conjI_mono hle)))
  obtain ⟨α, 𝔞, hα, hspan, hcopa⟩ := GlobalTheory.T.exists_cmField_generator_at_primes_dividing E 𝔍 M h𝔍 hM
  set H : Matrix (Fin n) (Fin n) E :=
    Matrix.diagonal (fun k : Fin n => if (k : ℕ) < r then 1 else cc (α : E) / (α : E)) with hHdef
  obtain ⟨hunit, hmove⟩ := GlobalTheory.T.selfDual_lattice_diagonal_unitary_patched_standard E n r M 𝔍 𝔞 α hM hMJ hcopJ hα hspan hcopa H hHdef
  obtain ⟨Λ', hΛ', Λ'', hΛ'', hmv, hle1, hle2⟩ := hmove Λ hΛ
  obtain ⟨t, ht0, ht⟩ := GlobalTheory.T.sum_moved_vacuum_translates_eq_freeRow_testFunction E r X g bas idx n hs hn D hrn M 𝔐 𝔍 𝔞 α hM hMm hsplit hcop hα
    hspan hcopa v₀ hv₀ H hHdef Λ hΛ Λ' hΛ' Λ'' hΛ'' hmv hle1 hle2
  obtain ⟨t', ht'1, ht'⟩ := GlobalTheory.T.thetaVacuum_unitary_column_change_unit_factor E r X g bas idx n hs hn D.w D.w_int D.w_tr H hunit Λ
    (vset_one hΛ) Λ'' hΛ'' hmv
  obtain ⟨P', hP', hPd⟩ := GlobalTheory.T.exists_rowHighest_harmonic_polyDeriv_unitaryAction E r X g q0 hr bas idx n hs hn H hunit k k' P hP
  have ht'0 : t' ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at ht'1
    exact zero_ne_one ht'1
  refine ⟨Λ', hΛ', (t / t') • P', Submodule.smul_mem _ _ hP', fun L hL x hx => ?_⟩
  have hSh : SelfD X (D.sh L) := ((GlobalTheory.T.level_structure_properties E r X g bas idx n hs hn D hrn).2.2.2.1 L hL).1
  have hv := hv₀ L hL
  have hφ := isSB_unitv_projA idx hs hn D.w_int D.w_tr hSh (vset_one hΛ) hv.1
  have hφ'' := isSB_unitv_projA idx hs hn D.w_int D.w_tr hSh hΛ'' hv.1
  have hheis : ∀ (y : Matrix (Fin n) (Fin r) E) (ψ : TF n g), IsSB ψ → IsSB (heisG X bas y ψ) :=
    fun y ψ hψ => ((heisG_laws E r X g bas idx n hs hn).2.2.2 y ψ hψ).1
  obtain ⟨s, hs1, hs2⟩ := ht L hL
  have hphiF : IsSB (phiF bas D 𝔐 hrn v₀ L Λ') := by
    have h2 : phiF bas D 𝔐 hrn v₀ L Λ' = t⁻¹ • (t • phiF bas D 𝔐 hrn v₀ L Λ') := by
      rw [smul_smul, inv_mul_cancel₀ ht0, one_smul]
    rw [h2, ← hs2]
    exact isSB_smul _ (GlobalTheory.SW.RecSum.isSB_sum s _ fun y => isSB_smul _ (hheis _ _ hφ''))
  have hDphi : IsSB (D.phi bas hrn v₀ L Λ) := by
    rw [hs1]
    exact GlobalTheory.SW.RecSum.isSB_sum s _ fun y => isSB_smul _ (hheis _ _ hφ)
  have key : ∀ z, t * thA X bas idx (phiF bas D 𝔐 hrn v₀ L Λ') x (GlobalTheory.Dict.hAct X idx H z) =
      t' * thA X bas idx (D.phi bas hrn v₀ L Λ) x z := by
    intro z
    have e1 := congrFun (GlobalTheory.SW.UnAct.thA_smul (bas := bas) idx x t (phiF bas D 𝔐 hrn v₀ L Λ'))
      (GlobalTheory.Dict.hAct X idx H z)
    rw [Pi.smul_apply, smul_eq_mul] at e1
    rw [← e1, ← hs2, thA_finset_sum_smul idx hs hx s _ _ (fun y => hheis _ _ hφ''), hs1,
      thA_finset_sum_smul idx hs hx s _ _ (fun y => hheis _ _ hφ), Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [GlobalTheory.T.theta_heisenberg_unitary_column_change E r X g bas idx n hs hn H hunit _ _ hφ hφ'' t' x hx
      (fun z => ht' (D.sh L) hSh (v₀ L) hv x hx z) y z]
    ring
  have hana := (theta_holomorphic_weight E r X g q0 hr bas idx n hs hn k k' _ hphiF P' hP').2.2.2 x hx
  have hdiff := ReciprocityTheory.ChartRestriction.G.I2.contDiff_of_diff (GlobalTheory.SW.ThetaHol.differentiable_thA idx hs hDphi hx)
  have hfun : (fun z => thA X bas idx (phiF bas D 𝔐 hrn v₀ L Λ') x (GlobalTheory.Dict.hAct X idx H z)) =
      (t' / t) • thA X bas idx (D.phi bas hrn v₀ L Λ) x := by
    funext z
    rw [Pi.smul_apply, smul_eq_mul]
    field_simp
    linear_combination key z
  unfold GlobalTheory.SW.thP
  rw [ReciprocityTheory.ChartRestriction.G.I2.polyDeriv_smul, ← hPd _ hana, hfun,
    ReciprocityTheory.ChartRestriction.G.I2.polyDeriv_smul_fun _ _ hdiff]
  field_simp

end GlobalTheory.Dict.DiagFree
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.WeakWeilRepCarriesDerivativesVacuaFockVectorsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weakWeilRep_carries_derivatives_vacua_fockVectors : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), ∀ om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ), IsWeak C.ψ S T om → ∀ (h : GA D S) (g : GA D T) f, C.IsTh f → (∀ (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ), om (h, g) (dRho (heisO C.ψ S T) C.θ τ z f) = dRho (heisO C.ψ S T) C.θ τ (compAt C.θ τ (mt T g) * z * compAt C.θ τ (mt S h⁻¹)) (om (h, g) f)) ∧ ∀ B, C.IsB B → (C.IsFock B f → C.IsFock (C.mvB g B) (om (h, g) f)) ∧ ∀ Q : MvPolynomial (FVar D T.rank S.rank) ℂ, om (h, g) (C.fvec B f Q) = pureTensorO C.ψ C.θ S T (fun _ => 1) (C.sB (C.mvB g B)) (fun τ => compAt C.θ τ (mt S h)) (C.mvB g B) (om (h, g) f) Q := by
  first | exact @GlobalTheory.Ker.WeakMove.om_move | exact GlobalTheory.Ker.WeakMove.om_move | (intros; apply GlobalTheory.Ker.WeakMove.om_move <;> assumption)
end

