import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0165
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicFormFrameExpansion
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0009
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PseudoCoefficientSeparation
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.RealPlaceAnalysis.Bundle0003
import Formalism.RealPlaceAnalysis.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0078
import Development.AbelianVarietyTheory.Proofs.HeightProofs.HilbertSchurUnitaryIrreducibleScalar
import Formalism.RealPlaceAnalysis.Bundle0004
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0025
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0051
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0052
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0094
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0021
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0025
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0210
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0221
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0209
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0196
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0211
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0005

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ApplyMulTorProd
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdSpan.ConjHol

variable {D : D7} {S T : HSp D}

def torProd (θ : InfFam D) (V : HSp D) (B : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (s : D.what₂.Tau → Fin V.rank → ℝ) : GA D V :=
  (Finset.univ.toList.map fun ρ => torAt θ V B ρ (s ρ)).prod

def conjL {E : Type} [Field E] {Ψ : Finset (E →+* ℂ)} {r : ℕ} : Frame Ψ r →ₗ[ℝ] Frame Ψ r where
  toFun Z := fun τ a b => conj (Z τ a b)
  map_add' Z Z' := funext fun τ => funext fun a => funext fun b => map_add (starRingEnd ℂ) _ _
  map_smul' c Z := funext fun τ => funext fun a => funext fun b => by
    change conj ((c : ℂ) * Z τ a b) = (c : ℂ) * conj (Z τ a b)
    rw [map_mul, Complex.conj_ofReal]

theorem mat_conjL {E : Type} [Field E] {Ψ : Finset (E →+* ℂ)} {r : ℕ} (Z : Frame Ψ r) (τ : Ψ) :
    mat (conjL Z) τ = (mat Z τ).map (starRingEnd ℂ) := rfl

def toLieC (C : Ctx S T) (R : GlobalTheory.SmoothForms.RealPoints C.θ T) (B : C.Bas) :
    Frame C.X.Ψ T.rank →ₗ[ℝ] GlobalTheory.SmoothForms.LieN T :=
  (GlobalTheory.HolRead.AdExt.toLie R B (fun ρ => C.m.e ρ)).comp conjL

theorem isUnit_det_B (C : Ctx S T) {B : C.Bas} (hB : C.IsB B) (ρ : D.what₂.Tau) : IsUnit (B ρ).det := by
  rw [isUnit_iff_ne_zero]
  intro h0
  have := congrArg det (hB ρ)
  rw [det_mul, det_mul, h0, mul_zero, sgnM, det_diagonal] at this
  refine Finset.prod_ne_zero_iff.2 (fun c _ => ?_) this.symm
  unfold sgn
  split_ifs <;> norm_num

theorem exp_map_conj {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    (NormedSpace.exp A).map (starRingEnd ℂ) = NormedSpace.exp (A.map (starRingEnd ℂ)) := by
  have h : ∀ M : Matrix (Fin n) (Fin n) ℂ, M.map (starRingEnd ℂ) = Mᴴᵀ := fun M => by
    ext i j
    simp [conjTranspose_apply]
  rw [h, h, Matrix.exp_transpose, Matrix.exp_conjTranspose]

def trLin (V : HSp D) (m : D.what₂.Tau → ℤ) : GlobalTheory.SmoothForms.LieN V →ₗ[ℝ] ℂ where
  toFun Y := ∑ ρ, (m ρ : ℂ) * trace (Y ρ).1
  map_add' Y Y' := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    change (m ρ : ℂ) * trace ((Y ρ).1 + (Y' ρ).1) = _
    rw [trace_add, mul_add]
  map_smul' c Y := by
    rw [RingHom.id_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    change (m ρ : ℂ) * trace (c • (Y ρ).1) = c • ((m ρ : ℂ) * trace (Y ρ).1)
    rw [trace_smul, mul_smul_comm]

def trCL (V : HSp D) (m : D.what₂.Tau → ℤ) : GlobalTheory.SmoothForms.LieN V →L[ℝ] ℂ where
  toLinearMap := trLin V m
  cont := continuous_finset_sum _ fun ρ _ =>
    continuous_const.mul ((continuous_subtype_val.comp (continuous_apply ρ)).matrix_trace)

theorem trCL_apply (V : HSp D) (m : D.what₂.Tau → ℤ) (Y : GlobalTheory.SmoothForms.LieN V) : trCL V m Y = trLin V m Y := rfl

end GlobalTheory.AdSpan.ConjHol

namespace GlobalTheory.AdSpan.ConjHol

variable {D : D7} {S T : HSp D}

theorem apply_mul_torProd (θ : InfFam D) (V : HSp D) (B : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (w : D.what₂.Tau → Fin V.rank → ℤ) (ψ : GA D V → ℂ)
    (h : ∀ (ρ : D.what₂.Tau) (t : Fin V.rank → ℝ) (g : GA D V),
      ψ (g * torAt θ V B ρ t) = cexp (((∑ a, (w ρ a : ℝ) * t a : ℝ) : ℂ) * I) * ψ g)
    (s : D.what₂.Tau → Fin V.rank → ℝ) (g : GA D V) :
    ψ (g * torProd θ V B s) = cexp (((∑ ρ, ∑ a, (w ρ a : ℝ) * s ρ a : ℝ) : ℂ) * I) * ψ g := by
  unfold torProd
  suffices H : ∀ l : List D.what₂.Tau, l.Nodup → ∀ g, ψ (g * (l.map fun ρ => torAt θ V B ρ (s ρ)).prod) =
      cexp (((∑ ρ ∈ l.toFinset, ∑ a, (w ρ a : ℝ) * s ρ a : ℝ) : ℂ) * I) * ψ g by
    have := H (Finset.univ : Finset D.what₂.Tau).toList (Finset.nodup_toList _) g
    rwa [Finset.toList_toFinset] at this
  intro l hl
  induction l with
  | nil => intro g; simp
  | cons ρ l ih =>
    intro g
    rw [List.nodup_cons] at hl
    rw [List.map_cons, List.prod_cons, ← mul_assoc, ih hl.2, h, List.toFinset_cons,
      Finset.sum_insert (by simpa using hl.1), ← mul_assoc, ← Complex.exp_add, ← add_mul]
    congr 3
    push_cast
    ring

theorem xB_mvB_mul (C : Ctx S T) (B : C.Bas) (hB : C.IsB B) (a k : GA D T) (b : Frame C.X.Ψ T.rank)
    (hk : ∀ ρ, compAt C.θ ρ (Formalism.L2.Theta.mt T k) = B ρ * (mat b (C.m.e ρ)).map (starRingEnd ℂ) * (B ρ)⁻¹) :
    C.xB (C.mvB (a * k) B) = rmul (C.xB (C.mvB a B)) b := by
  have R : GlobalTheory.SmoothForms.RealPoints C.θ T := (GlobalTheory.SmoothForms.RealPts.realPoints D).2 C.θ C.inf T
  funext σ i j
  obtain ⟨ρ, rfl⟩ := C.m.e.surjective σ
  have e1 : C.mvB (a * k) B ρ = C.mvB a B ρ * (mat b (C.m.e ρ)).map (starRingEnd ℂ) := by
    have hm : compAt C.θ ρ (Formalism.L2.Theta.mt T (a * k)) =
        compAt C.θ ρ (Formalism.L2.Theta.mt T a) * compAt C.θ ρ (Formalism.L2.Theta.mt T k) := R.2.2.2.1 a k ρ
    simp only [Ctx.mvB]
    rw [hm, hk]
    simp only [Matrix.mul_assoc, nonsing_inv_mul _ (isUnit_det_B C hB ρ), Matrix.mul_one]
  simp only [Ctx.xB, rmul, mat, Equiv.symm_apply_apply, e1, Matrix.mul_apply, Matrix.of_apply, Matrix.map_apply,
    map_sum, map_mul, Complex.conj_conj]

end GlobalTheory.AdSpan.ConjHol
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BoundedIntertwinerSchur
section
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace

namespace GlobalTheory

theorem jm_mul_self_uj {n : ℕ} (ε : Fin n → Bool) : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := by
  unfold Formalism.REAL.Jm
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  split_ifs <;> norm_num

theorem jm_conjTranspose_uj {n : ℕ} (ε : Fin n → Bool) : (Formalism.REAL.Jm ε)ᴴ = Formalism.REAL.Jm ε := by
  unfold Formalism.REAL.Jm
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext a
  by_cases h : ε a = true <;> simp [h]

theorem exists_inv_mem_UJset {n : ℕ} {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : g ∈ UJset ε) : ∃ h ∈ UJset ε, h * g = 1 ∧ g * h = 1 := by
  have hg' : gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε := hg
  have hJ := jm_mul_self_uj ε
  have hJs := jm_conjTranspose_uj ε
  set J := Formalism.REAL.Jm ε
  have hhg : (J * gᴴ * J) * g = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc gᴴ, hg', hJ]
  have hgh : g * (J * gᴴ * J) = 1 := mul_eq_one_comm.1 hhg
  refine ⟨J * gᴴ * J, ?_, hhg, hgh⟩
  have hgJ : g * J * gᴴ = J := by
    have : g * J * gᴴ * J * J = J := by
      rw [show g * J * gᴴ * J = g * (J * gᴴ * J) by simp only [Matrix.mul_assoc], hgh, Matrix.one_mul]
    rwa [Matrix.mul_assoc (g * J * gᴴ), hJ, Matrix.mul_one] at this
  show (J * gᴴ * J)ᴴ * J * (J * gᴴ * J) = J
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hJs]
  calc J * (g * J) * J * (J * gᴴ * J) = J * (g * J * (J * J) * gᴴ) * J := by
        simp only [Matrix.mul_assoc]
    _ = J := by rw [hJ, Matrix.mul_one, hgJ, hJ, Matrix.one_mul]

theorem star_eq_of_inv_UJset {n : ℕ} {ε : Fin n → Bool} {X : Type} [NormedAddCommGroup X]
    [InnerProductSpace ℂ X] [CompleteSpace X] {σ : Matrix (Fin n) (Fin n) ℂ → (X →L[ℂ] X)}
    (hσ : IsURepOn (UJset ε) σ) {g h : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset ε) (hh : h ∈ UJset ε)
    (hgh : g * h = 1) : star (σ g) = σ h := by
  have h1 : star (σ g) * σ g = 1 :=
    (ContinuousLinearMap.norm_map_iff_adjoint_comp_self (σ g)).1 (hσ.2.1 g hg)
  have h2 : σ g * σ h = 1 := by
    rw [ContinuousLinearMap.mul_def, ← hσ.1.2 g hg h hh, hgh, hσ.1.1]
  calc star (σ g) = star (σ g) * (σ g * σ h) := by rw [h2, mul_one]
    _ = σ h := by rw [← mul_assoc, h1, one_mul]

end GlobalTheory

namespace GlobalTheory

theorem uEquiv_of_intertwiner_ne_zero : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V] (π : Matrix (Fin n) (Fin n) ℂ → (V →L[ℂ] V)), IsURepOn (UJset ε) ρ → IsIrredOn (UJset ε) ρ → IsURepOn (UJset ε) π → IsIrredOn (UJset ε) π → ∀ B : H →L[ℂ] V, B ≠ 0 → (∀ g ∈ UJset ε, ∀ x, B (ρ g x) = π g (B x)) → UEquiv ε π ρ := by
  intro n ε H _ _ _ ρ V _ _ _ π hρ hρi hπ hπi B hB hBc

  have hBadj : ∀ g ∈ UJset ε, ∀ v, B.adjoint (π g v) = ρ g (B.adjoint v) := by
    intro g hg v
    obtain ⟨h, hh, hhg, hgh⟩ := exists_inv_mem_UJset hg
    have hcomp : B ∘L ρ h = π h ∘L B := ContinuousLinearMap.ext fun x => hBc h hh x
    have := congrArg ContinuousLinearMap.adjoint hcomp
    rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp,
      ← ContinuousLinearMap.star_eq_adjoint, ← ContinuousLinearMap.star_eq_adjoint,
      star_eq_of_inv_UJset hρ hh hg hhg, star_eq_of_inv_UJset hπ hh hg hhg] at this
    exact (DFunLike.congr_fun this v).symm
  set A : H →L[ℂ] H := B.adjoint ∘L B with hAdef
  have hAsa : IsSelfAdjoint A := by
    rw [IsSelfAdjoint, ContinuousLinearMap.star_eq_adjoint, hAdef, ContinuousLinearMap.adjoint_comp,
      ContinuousLinearMap.adjoint_adjoint]
  obtain ⟨c, hc⟩ := hilbert_schur_selfAdjoint H (UJset ε) (fun g => ρ g.1)
    (fun S hS hinv => hρi S hS (fun g hg v hv => hinv ⟨g, hg⟩ v hv)) A hAsa
    (fun g => ContinuousLinearMap.ext fun x => by
      simp only [ContinuousLinearMap.mul_apply, hAdef, ContinuousLinearMap.comp_apply]
      rw [hBc g.1 g.2 x, hBadj g.1 g.2])

  have hnorm : ∀ x, ((‖B x‖ ^ 2 : ℝ) : ℂ) = c * ((‖x‖ ^ 2 : ℝ) : ℂ) := by
    intro x
    have h1 : ⟪x, A x⟫_ℂ = ⟪B x, B x⟫_ℂ := by
      simp only [hAdef, ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right]
    rw [hc] at h1
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply, inner_smul_right] at h1
    rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h1
    push_cast
    exact_mod_cast h1.symm
  obtain ⟨x0, hx0⟩ : ∃ x0, B x0 ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hB (ContinuousLinearMap.ext hcon)
  have hx0' : x0 ≠ 0 := fun h => hx0 (by rw [h, map_zero])
  set r : ℝ := c.re with hr
  have hcr : c = (r : ℂ) := by
    have := hnorm x0
    have hpos : (0 : ℝ) < ‖x0‖ ^ 2 := by positivity
    have hc' : c = ((‖B x0‖ ^ 2 / ‖x0‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.ofReal_div, this, mul_div_assoc, div_self (by exact_mod_cast hpos.ne'), mul_one]
    rw [hr, hc', Complex.ofReal_re]
  have hnormr : ∀ x, ‖B x‖ ^ 2 = r * ‖x‖ ^ 2 := by
    intro x
    have := hnorm x
    rw [hcr, ← Complex.ofReal_mul] at this
    exact_mod_cast this
  have hrpos : 0 < r := by
    have := hnormr x0
    have h1 : (0 : ℝ) < ‖B x0‖ ^ 2 := by positivity
    have h2 : (0 : ℝ) < ‖x0‖ ^ 2 := by positivity
    nlinarith
  set s : ℝ := Real.sqrt r with hs
  have hspos : 0 < s := Real.sqrt_pos.2 hrpos

  let U : H →L[ℂ] V := ((s⁻¹ : ℝ) : ℂ) • B
  have hU : ∀ x, ‖U x‖ = ‖x‖ := by
    intro x
    have hBx : ‖B x‖ = s * ‖x‖ := by
      rw [hs, ← Real.sqrt_sq (norm_nonneg (B x)), hnormr x, Real.sqrt_mul hrpos.le,
        Real.sqrt_sq (norm_nonneg x)]
    simp only [U, ContinuousLinearMap.smul_apply, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_inv, abs_of_pos hspos, hBx]
    field_simp
  have hUc : ∀ g ∈ UJset ε, ∀ x, U (ρ g x) = π g (U x) := by
    intro g hg x
    simp only [U, ContinuousLinearMap.smul_apply, hBc g hg x, map_smul]
  let L : H →ₗᵢ[ℂ] V := { toLinearMap := U.toLinearMap, norm_map' := hU }
  have hrange : LinearMap.range L.toLinearMap = ⊤ := by
    rcases hπi (LinearMap.range L.toLinearMap)
      (L.antilipschitz.isClosed_range L.isometry.uniformContinuous) (by
        rintro g hg v ⟨x, rfl⟩
        exact ⟨ρ g x, (hUc g hg x)⟩) with h | h
    · exfalso
      have hmem : L x0 ∈ LinearMap.range L.toLinearMap := ⟨x0, rfl⟩
      rw [h, Submodule.mem_bot] at hmem
      apply hx0'
      rw [← norm_eq_zero, ← L.norm_map x0, hmem, norm_zero]
    · exact h
  have hsurj : Function.Surjective L := by
    intro y
    have : y ∈ LinearMap.range L.toLinearMap := by rw [hrange]; trivial
    obtain ⟨x, hx⟩ := this
    exact ⟨x, hx⟩
  let e : H ≃ₗᵢ[ℂ] V := LinearIsometryEquiv.ofSurjective L hsurj
  refine ⟨e.symm, fun g hg v => e.injective ?_⟩
  rw [LinearIsometryEquiv.apply_symm_apply]
  show π g v = U (ρ g (e.symm v))
  rw [hUc g hg]
  congr 1
  exact (e.apply_symm_apply v).symm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CapelliOfGelfand
section
open Formalism.REAL Finset Polynomial

open GlobalTheory.Dec (gelfVal)

namespace GlobalTheory.CapelliNewton

theorem gelfVal_zero (m : ℕ) (χ : Fin (m+1) → ℂ) : gelfVal χ 0 = (m:ℂ) + 1 := by
  simp [gelfVal, Matrix.one_apply]

theorem etr_apply_all {V : Type} [AddCommGroup V] [Module ℂ V] (m : ℕ)
    (E : Fin (m+1) → Fin (m+1) → Module.End ℂ V) (χ : Fin (m+1) → ℂ)
    (hetr : ∀ (k : ℕ) (v : V), etr E (k + 1) v = gelfVal χ (k + 1) • v) (k : ℕ) (w : V) :
    etr E k w = gelfVal χ k • w := by
  cases k with
  | zero => rw [gelfVal_zero]; simp [etr, epow, add_smul]; rw [Nat.cast_smul_eq_nsmul]
  | succ k => exact hetr k w

noncomputable def polyOf {V : Type} [AddCommGroup V] [Module ℂ V] (d : ℕ) (c : ℕ → Module.End ℂ V)
    (φ : Module.Dual ℂ V) (v : V) : ℂ[X] :=
  ∑ i ∈ range (d + 1), C (φ (c i v)) * X ^ i

theorem polyOf_eval {V : Type} [AddCommGroup V] [Module ℂ V] (d : ℕ) (c : ℕ → Module.End ℂ V)
    (φ : Module.Dual ℂ V) (v : V) (u : ℂ) :
    (polyOf d c φ v).eval u = φ ((∑ i ∈ range (d + 1), u ^ i • c i) v) := by
  unfold polyOf
  rw [eval_finset_sum, LinearMap.sum_apply, map_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [eval_mul, eval_C, eval_pow, eval_X, LinearMap.smul_apply, map_smul, smul_eq_mul, mul_comm]

theorem polyOf_natDegree {V : Type} [AddCommGroup V] [Module ℂ V] (d : ℕ) (c : ℕ → Module.End ℂ V)
    (φ : Module.Dual ℂ V) (v : V) : (polyOf d c φ v).natDegree ≤ d := by
  unfold polyOf
  refine natDegree_sum_le_of_forall_le _ _ fun i hi => ?_
  refine (natDegree_C_mul_X_pow_le _ _).trans ?_
  exact Nat.lt_succ_iff.mp (mem_range.mp hi)

theorem polyOf_coeff {V : Type} [AddCommGroup V] [Module ℂ V] (d : ℕ) (c : ℕ → Module.End ℂ V)
    (φ : Module.Dual ℂ V) (v : V) : (polyOf d c φ v).coeff d = φ (c d v) := by
  unfold polyOf
  rw [finset_sum_coeff, sum_eq_single d]
  · simp
  · intro b _ hb; simp [coeff_C_mul_X_pow, hb.symm]
  · intro h; exact absurd (self_mem_range_succ d) h

noncomputable def capQ (m : ℕ) (χ : Fin (m+1) → ℂ) : ℂ[X] := ∏ s, (X + C (χ s - (m : ℂ) / 2))

theorem capQ_eval (m : ℕ) (χ : Fin (m+1) → ℂ) (u : ℂ) :
    (capQ m χ).eval u = ∏ s, (u - (m : ℂ) / 2 + χ s) := by
  simp [capQ, eval_prod]; refine prod_congr rfl fun s _ => by ring

theorem capQ_monic (m : ℕ) (χ : Fin (m+1) → ℂ) : (capQ m χ).Monic :=
  monic_prod_of_monic _ _ fun s _ => monic_X_add_C _

theorem capQ_natDegree (m : ℕ) (χ : Fin (m+1) → ℂ) : (capQ m χ).natDegree = m + 1 := by
  unfold capQ
  rw [natDegree_prod_of_monic _ _ fun s _ => monic_X_add_C _]
  simp only [natDegree_X_add_C, sum_const, card_univ, Fintype.card_fin, smul_eq_mul, mul_one]

theorem main_succ (V : Type) [AddCommGroup V] [Module ℂ V] (m : ℕ)
    (E : Fin (m+1) → Fin (m+1) → Module.End ℂ V) (χ : Fin (m+1) → ℂ) (hE : GlRel E)
    (hetr : ∀ (k : ℕ) (v : V), etr E (k + 1) v = gelfVal χ (k + 1) • v) (u : ℂ) (v : V) :
    qdet E u v = (∏ s, (u - (m : ℂ) / 2 + χ s)) • v := by
  rw [← sub_eq_zero]
  refine (Module.forall_dual_apply_eq_zero_iff ℂ _).mp fun φ => ?_
  obtain ⟨c, hc1, hc⟩ := GlobalTheory.T.exists_monic_poly_eq_qdet (Module.End ℂ V) (m + 1) E
  set P := polyOf (m + 1) c φ v with hPdef
  have hP : ∀ w : ℂ, φ (qdet E w v) = P.eval w := fun w => by rw [polyOf_eval, hc]

  have hmin : ∀ i j : Fin (m + 1), ∃ c' : ℕ → Module.End ℂ V, ∀ w : ℂ,
      qminor E (Fin.succAbove j) (Fin.succAbove i) w = ∑ d ∈ range (m + 1), w ^ d • c' d := by
    intro i j
    obtain ⟨c', hc'⟩ := GlobalTheory.qminor_polyMap (Module.End ℂ V) (m + 1) m E (Fin.succAbove j) (Fin.succAbove i) 0
    exact ⟨c', fun w => by simpa using hc' w⟩
  choose cm hcm using hmin
  let N := m + 1
  let Rc : ℕ → Module.End ℂ V := fun d => ∑ i : Fin (m + 1), ∑ j : Fin (m + 1),
    (((-1 : ℤ) ^ ((i : ℕ) + (j : ℕ)) : ℤ) : Module.End ℂ V) * cm i j d * epow E (N + 1) j i
  have hR : ∀ w : ℂ, ∑ i : Fin (m + 1), ∑ j : Fin (m + 1), (((-1 : ℤ) ^ ((i : ℕ) + (j : ℕ)) : ℤ) : Module.End ℂ V) * qminor E (Fin.succAbove j) (Fin.succAbove i) w * epow E (N + 1) j i
      = ∑ d ∈ range (m + 1), w ^ d • Rc d := by
    intro w
    simp only [Rc, hcm, mul_sum, sum_mul, smul_sum, mul_smul_comm, smul_mul_assoc]
    conv_lhs => enter [2, x]; rw [sum_comm]
    rw [sum_comm]
  set Rp := polyOf m Rc φ v
  have hrec : ∀ w : ℂ, (w - m) ^ (N + 1) * (P.eval (w + 1) - P.eval w) - P.eval w * ∑ k ∈ range (N + 1), (-1) ^ k * (w - m) ^ (N - k) * gelfVal χ k = (C (-(-1) ^ N) * Rp).eval w := by
    intro w
    have h1 := congrArg (fun T : Module.End ℂ V => φ (T v)) (GlobalTheory.T.traced_qminor_comatrix_truncated_inverse (Module.End ℂ V) m E hE w N)
    rw [← GlobalTheory.T.qdet_add_one_sub_eq_sum_qminor', hR] at h1
    have h2 : (qdet E w * ∑ k ∈ range (N + 1), algebraMap ℂ (Module.End ℂ V) ((-1) ^ k * (w - m) ^ (N - k)) * etr E k) v
        = (∑ k ∈ range (N + 1), (-1) ^ k * (w - m) ^ (N - k) * gelfVal χ k) • qdet E w v := by
      rw [Module.End.mul_apply, LinearMap.sum_apply]
      simp only [Module.End.mul_apply, Module.algebraMap_end_apply, etr_apply_all m E χ hetr, smul_smul]
      rw [← sum_smul, map_smul]
    rw [h2] at h1
    simp only [LinearMap.add_apply, Module.End.mul_apply, Module.algebraMap_end_apply, map_add, map_smul, LinearMap.sub_apply, map_sub, smul_eq_mul] at h1
    rw [← polyOf_eval] at h1
    simp only [hP] at h1
    simp only [eval_mul, eval_neg, eval_pow, eval_C]
    linear_combination h1
  obtain ⟨rs, hrs, hrsE⟩ := GlobalTheory.T.scalar_capelli_truncated_perelomov_popov m N χ
  have hf := GlobalTheory.T.poly_eq_zero_of_newton_recursion m N (gelfVal χ) (P - C (φ v) * capQ m χ) (C (-(-1) ^ N) * Rp - C (φ v) * rs)
    (Nat.lt_succ_self m) (gelfVal_zero m χ) ?_ ?_ ?_
  · have := congrArg (eval u) hf
    simp only [eval_sub, eval_mul, eval_C, eval_zero, capQ_eval] at this
    rw [map_sub, map_smul, hP, smul_eq_mul]; linear_combination this
  · rw [natDegree_le_iff_coeff_eq_zero]
    intro k hk
    rw [coeff_sub, coeff_C_mul]
    rcases Nat.lt_or_ge (m + 1) k with h | h
    · rw [coeff_eq_zero_of_natDegree_lt ((polyOf_natDegree _ _ _ _).trans_lt h),
        coeff_eq_zero_of_natDegree_lt (by rw [capQ_natDegree]; exact h)]; simp
    · have hk' : k = m + 1 := le_antisymm h hk
      subst hk'
      have := (capQ_monic m χ).coeff_natDegree
      rw [capQ_natDegree] at this
      rw [this, polyOf_coeff, hc1]; simp
  · refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
    · exact natDegree_C_mul_le _ _ |>.trans (polyOf_natDegree _ _ _ _)
    · exact natDegree_C_mul_le _ _ |>.trans hrs
  · intro w
    have h1 := hrec w
    have h2 := hrsE w
    rw [← capQ_eval m χ (w + 1), ← capQ_eval m χ w] at h2
    simp only [eval_sub, eval_mul, eval_C] at h1 h2 ⊢
    linear_combination h1 - φ v * h2

end GlobalTheory.CapelliNewton

namespace GlobalTheory.CapelliNewton

theorem capelli_of_gelfand : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (n : ℕ) (E : Fin n → Fin n → Module.End ℂ V) (χ : Fin n → ℂ), GlRel E → (∀ (k : ℕ) (v : V), etr E (k + 1) v = gelfVal χ (k + 1) • v) → ∀ (Y : ℂ) (v : V), qdet E (Y + ((n : ℂ) - 1) / 2) v = (∏ s, (Y + χ s)) • v := by
  intro V _ _ n E χ hE hetr Y v
  cases n with
  | zero => simp [qdet, qminor]
  | succ m =>
    rw [main_succ V m E χ hE hetr]
    congr 1
    refine prod_congr rfl fun s _ => ?_
    push_cast; ring

end GlobalTheory.CapelliNewton
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ClassTermEqVolumeMulOrbitalIntegral
section
open MeasureTheory Set GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary
open scoped ENNReal

noncomputable section

namespace GlobalTheory.ClassUnfold

theorem hasClassInt_of_hasOrbInt : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [SecondCountableTopology H] [LocallyCompactSpace H] [T2Space H] [MeasurableSpace H] [BorelSpace H]
    (Γ : Subgroup H) [DiscreteTopology Γ] (γ : H), γ ∈ Γ → IsMulCommutative (cent γ) →
    ∀ (μ : Measure H) [μ.IsHaarMeasure] (dt : Measure (cent γ)) [dt.IsHaarMeasure] (𝓣 : Set (cent γ)),
    IsFundamentalDomain (Γ.subgroupOf (cent γ)) 𝓣 dt → dt 𝓣 < ⊤ →
    ∀ (f : H → ℂ) (c : ℂ), Continuous f → HasCompactSupport f → HasOrbInt μ γ dt f c →
    ∀ 𝓕 : Set H, IsFundamentalDomain Γ 𝓕 μ → GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.HasClassInt Γ μ 𝓕 γ f (dt.real 𝓣 * c) := by
  intro H _ _ _ _ _ _ _ _ Γ _ γ hγ hc μ _ dt _ 𝓣 h𝓣 hfin f c hf hfc hO 𝓕 h𝓕
  obtain ⟨α, hαm, hα1, hαI⟩ := GlobalTheory.T.exists_weight_bruhat_fundamental_domain_centralizer H Γ γ hc μ dt 𝓣 h𝓣
  have hL : ∀ G : H → ℝ≥0∞, Measurable G →
      ∫⁻ x in 𝓕, ∑' δ : GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.ratClass Γ γ, G (x⁻¹ * δ * x) ∂μ =
        dt 𝓣 * ∫⁻ q, G (q.out⁻¹ * γ * q.out) ∂(quotMeas (cent γ) dt μ) := by
    intro G hG
    have hψ : Measurable fun y : H => G (y⁻¹ * γ * y) := hG.comp (by fun_prop)
    have hinv : LeftInv (cent γ) fun y : H => G (y⁻¹ * γ * y) := fun t ht y => by
      have : (t * y)⁻¹ * γ * (t * y) = y⁻¹ * (t⁻¹ * (γ * t)) * y := by group
      simp only [this, ← mem_cent.1 ht, inv_mul_cancel_left]
    have hF : ∀ g : Γ, AEMeasurable (fun x : H => α ((g : H) * x) * G (((g : H) * x)⁻¹ * γ * ((g : H) * x)))
        (μ.restrict 𝓕) := fun g =>
      ((hαm.mul hψ).comp (measurable_const_mul (g : H))).aemeasurable
    calc ∫⁻ x in 𝓕, ∑' δ : GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.ratClass Γ γ, G (x⁻¹ * δ * x) ∂μ
        = ∫⁻ x in 𝓕, ∑' g : Γ, α ((g : H) * x) * G (((g : H) * x)⁻¹ * γ * ((g : H) * x)) ∂μ :=
          lintegral_congr fun x => GlobalTheory.T.tsum_subgroupConjugacyClass_eq_tsum_weighted H Γ γ hγ α hα1 G x
      _ = ∑' g : Γ, ∫⁻ x in 𝓕, α ((g : H) * x) * G (((g : H) * x)⁻¹ * γ * ((g : H) * x)) ∂μ :=
          lintegral_tsum hF
      _ = ∫⁻ y, α y * G (y⁻¹ * γ * y) ∂μ :=
          (h𝓕.lintegral_eq_tsum'' (fun y => α y * G (y⁻¹ * γ * y))).symm
      _ = dt 𝓣 * ∫⁻ q, G (q.out⁻¹ * γ * q.out) ∂(quotMeas (cent γ) dt μ) :=
          hαI _ hψ hinv
  exact GlobalTheory.T.classTerm_converges_of_lintegral_unfolding_eq H Γ γ hγ μ 𝓕 (quotMeas (cent γ) dt μ) (dt 𝓣) hfin hL f c hf hfc hO.1 hO.2

end GlobalTheory.ClassUnfold
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesPureInnerProductsTensorProductStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Matrix GlobalTheory.Chain GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.discreteSeries_pureInnerProducts_tensorProduct : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S), TensorLaw M := by
  first | exact @GlobalTheory.Chain.RealIt.tensorLaw | exact GlobalTheory.Chain.RealIt.tensorLaw | (intros; apply GlobalTheory.Chain.RealIt.tensorLaw <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EventuallyHermitianIntegrallyCongruentCmExtStatement
section
open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_hermitian_integrally_congruent_cmExt : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J J' : Matrix (Fin n) (Fin n) E), IsHermND σ J → IsHermND σ J' → ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, ∃ u : GL (Fin n) (Fv F v ⊗[F] E), Formalism.UG.cT (sigR (Fv F v) σ) u.1 * JR (Fv F v) J * u.1 = JR (Fv F v) J' ∧ ∀ y, u.1 *ᵥ y ∈ latLoc F (stdLattice E n) v ↔ y ∈ latLoc F (stdLattice E n) v := by
  first | exact @GlobalTheory.HermCongAlmostAll.eventually_congr_int | exact GlobalTheory.HermCongAlmostAll.eventually_congr_int | (intros; apply GlobalTheory.HermCongAlmostAll.eventually_congr_int <;> assumption)
end

