import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1728
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1897
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1678
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0943
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0521
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1167
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1183
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticePointSignEqThetaLawSemicharacter
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0542
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0108
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitVacuumEntireFactorIsThetaMovedLattices
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1549
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0273
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1577
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0172
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0213

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKernelArchimedeanUnipotentSupport
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

noncomputable section
namespace GlobalTheory.CptCoeff
open MeasureTheory Matrix ComplexConjugate

theorem mul_conj_polar (z w : ℂ) : z * conj w = (1 / 4 : ℂ) * ((((‖z + w‖ ^ 2 : ℝ) : ℂ) - ((‖z - w‖ ^ 2 : ℝ) : ℂ)) +
    Complex.I * (((‖z + Complex.I * w‖ ^ 2 : ℝ) : ℂ) - ((‖z - Complex.I * w‖ ^ 2 : ℝ) : ℂ))) := by
  have e : ∀ y : ℂ, (((‖y‖ ^ 2 : ℝ)) : ℂ) = y * conj y := fun y => by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [e, e, e, e]
  simp only [map_add, map_sub, map_mul, Complex.conj_I]
  linear_combination (1 / 2 : ℂ) * (z * conj w - w * conj z) * Complex.I_sq

theorem integral_sq_norm {X : Type} [MeasurableSpace X] {μ : Measure X} {h : X → ℂ} (hh : MemLp h 2 μ) :
    ∫ x, (((‖h x‖ ^ 2 : ℝ)) : ℂ) ∂μ = (((∫⁻ x, ‖h x‖ₑ ^ 2 ∂μ).toReal : ℝ) : ℂ) := by
  have hi : Integrable (fun x => ‖h x‖ ^ 2) μ := hh.integrable_norm_pow two_ne_zero
  rw [integral_complex_ofReal, integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun x => by positivity)
    hi.aestronglyMeasurable]
  congr 3
  funext x
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]

theorem integrable_sq_norm {X : Type} [MeasurableSpace X] {μ : Measure X} {h : X → ℂ} (hh : MemLp h 2 μ) :
    Integrable (fun x => (((‖h x‖ ^ 2 : ℝ)) : ℂ)) μ :=
  (hh.integrable_norm_pow two_ne_zero).ofReal

theorem integral_mul_conj {X : Type} [MeasurableSpace X] {μ : Measure X} {f g : X → ℂ} (hf : MemLp f 2 μ)
    (hg : MemLp g 2 μ) : ∫ x, f x * conj (g x) ∂μ = (1 / 4 : ℂ) *
      (((((∫⁻ x, ‖(f + g) x‖ₑ ^ 2 ∂μ).toReal : ℝ) : ℂ) - (((∫⁻ x, ‖(f - g) x‖ₑ ^ 2 ∂μ).toReal : ℝ) : ℂ)) +
      Complex.I * ((((∫⁻ x, ‖(f + Complex.I • g) x‖ₑ ^ 2 ∂μ).toReal : ℝ) : ℂ) -
        (((∫⁻ x, ‖(f - Complex.I • g) x‖ₑ ^ 2 ∂μ).toReal : ℝ) : ℂ))) := by
  have h1 := hf.add hg
  have h2 := hf.sub hg
  have h3 := hf.add (hg.const_smul Complex.I)
  have h4 := hf.sub (hg.const_smul Complex.I)
  rw [← integral_sq_norm h1, ← integral_sq_norm h2, ← integral_sq_norm h3, ← integral_sq_norm h4,
    ← integral_sub (integrable_sq_norm h1) (integrable_sq_norm h2),
    ← integral_sub (integrable_sq_norm h3) (integrable_sq_norm h4), ← integral_const_mul,
    ← integral_add, ← integral_const_mul]
  · congr 1
    funext x
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    exact mul_conj_polar (f x) (g x)
  · exact (integrable_sq_norm h1).sub (integrable_sq_norm h2)
  · exact ((integrable_sq_norm h3).sub (integrable_sq_norm h4)).const_mul _

theorem integral_mul_conj_map {X : Type} [MeasurableSpace X] {μ : Measure X} (P : Submodule ℂ (X → ℂ))
    (hP : ∀ f ∈ P, MemLp f 2 μ) (T : Module.End ℂ (X → ℂ)) (hT : ∀ f ∈ P, T f ∈ P)
    (hU : ∀ f ∈ P, ∫⁻ x, ‖T f x‖ₑ ^ 2 ∂μ = ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ) {f g : X → ℂ} (hf : f ∈ P) (hg : g ∈ P) :
    ∫ x, T f x * conj (T g x) ∂μ = ∫ x, f x * conj (g x) ∂μ := by
  rw [integral_mul_conj (hP _ (hT f hf)) (hP _ (hT g hg)), integral_mul_conj (hP f hf) (hP g hg),
    ← map_add, ← map_sub, ← map_smul, ← map_add, ← map_sub, hU _ (P.add_mem hf hg), hU _ (P.sub_mem hf hg),
    hU _ (P.add_mem hf (P.smul_mem _ hg)), hU _ (P.sub_mem hf (P.smul_mem _ hg))]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def infOne : AF F := ((1 : InfiniteAdeleRing F), (0 : FiniteAdeleRing (𝓞 F) F))

theorem at_infOne : At (evI F) (infOne (F := F)) := by
  intro t ht
  have h1 : t.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (by rw [map_zero]; exact ht)
  refine Prod.ext ?_ ?_
  · change t.1 * 1 = 0
    rw [h1, zero_mul]
  · change t.2 * 0 = 0
    exact mul_zero _

theorem evFin_liftV_ne {v w : Pl F} (h : w ≠ v) (a : Fv F v) : evFin F w (GlobalTheory.LatVac.liftV v a) = 0 :=
  evalV_singleFin_ne h a

theorem mul_eq_zero_of_supp (S : Finset (Pl F)) {m n k : ℕ} (A : Matrix (Fin m) (Fin n) (AE F E))
    (hI : ∀ t : AF F, At (evI F) t → t • A = 0) (hS : ∀ w ∈ S, ∀ t : AF F, At (evFin F w) t → t • A = 0)
    (u : Matrix (Fin n) (Fin k) (AE F E))
    (hu : ∀ t : AF F, evI F t = 0 → (∀ w ∈ S, evFin F w t = 0) → t • u = 0) : A * u = 0 := by
  classical
  set e : AF F := infOne + ∑ w ∈ S, GlobalTheory.LatVac.liftV w 1 with he
  have h1 : evI F (1 - e) = 0 := by
    change InfiniteAdeleRing.ringEquiv_mixedSpace F (fstA F (1 - e)) = 0
    have h0 : fstA F (infOne (F := F)) = 1 := rfl
    have hl : ∀ w : Pl F, fstA F (GlobalTheory.LatVac.liftV w 1) = 0 := fun w => rfl
    have : fstA F (1 - e) = 0 := by
      rw [he, map_sub, map_one, map_add, map_sum, h0, Finset.sum_eq_zero fun w _ => hl w, add_zero, sub_self]
    rw [this, map_zero]
  have h2 : ∀ w ∈ S, evFin F w (1 - e) = 0 := by
    intro w hw
    rw [he, map_sub, map_one, map_add, map_sum]
    have h0 : evFin F w (infOne (F := F)) = 0 := by
      change evalV F w (sndA F infOne) = 0
      have : sndA F (infOne (F := F)) = 0 := rfl
      rw [this, map_zero]
    have hs : ∑ x ∈ S, evFin F w (GlobalTheory.LatVac.liftV x 1) = ∑ x ∈ S, if w = x then (1 : Fv F w) else 0 := by
      refine Finset.sum_congr rfl fun x _ => ?_
      by_cases hx : w = x
      · subst hx; rw [if_pos rfl, GlobalTheory.LatVac.evFin_liftV]
      · rw [if_neg hx, evFin_liftV_ne hx]
    rw [h0, hs, Finset.sum_ite_eq S w (fun _ => (1 : Fv F w)), if_pos hw, zero_add, sub_self]
  have hue : u = e • u := by
    have := hu (1 - e) h1 h2
    rwa [sub_smul, one_smul, sub_eq_zero] at this
  have hA : e • A = 0 := by
    rw [he, add_smul, Finset.sum_smul, hI _ at_infOne, zero_add]
    exact Finset.sum_eq_zero fun w hw => hS w hw _ (GlobalTheory.LatVac.at_liftV w 1)
  rw [hue, Matrix.mul_smul, ← Matrix.smul_mul, hA, Matrix.zero_mul]

theorem matrix_coeff : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (S : Finset (Pl F)) (g : UA σ G.V'.J) (h : UA σ G.W.J),
    (∀ u : AF F, At (evI F) u → u • (mat g - 1) = 0) → (∀ u : AF F, At (evI F) u → u • (mat h - 1) = 0) →
    (∀ w ∈ S, ∀ u : AF F, At (evFin F w) u → u • (mat g - 1) = 0) →
    (∀ w ∈ S, ∀ u : AF F, At (evFin F w) u → u • (mat h - 1) = 0) →
    ∀ Φ ∈ schA F (Fin a' × Fin (a + a')), ∀ u : Matrix (Fin a') (Fin (a + a')) (AE F E),
    (∀ t : AF F, evI F t = 0 → (∀ w ∈ S, evFin F w t = 0) → t • u = 0) →
    ∀ μ : @MeasureTheory.Measure (Fin a' × Fin (a + a') → AF F) (borel _),
      @MeasureTheory.Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      (@MeasureTheory.integral _ ℂ _ _ (borel _) μ fun x =>
          om' (g, h) Φ x * starRingEnd ℂ (G.M'.co.rho B.ψ u (om' (g, h) Φ) x)) =
        @MeasureTheory.integral _ ℂ _ _ (borel _) μ fun x => Φ x * starRingEnd ℂ (G.M'.co.rho B.ψ u Φ x) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT S g h hgI hhI hgS hhS Φ hΦ u hu μ hμ
  letI : MeasurableSpace (Fin a' × Fin (a + a') → AF F) := borel _
  have hW := IsUWeilPair.isUSplitting hT.weil'
  have hg : mat g * u = u := by
    have := mul_eq_zero_of_supp S (mat g - 1) hgI hgS u hu
    rwa [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at this
  have hh : u * (mat h)ᵀ = u := by
    have := mul_eq_zero_of_supp S (mat h - 1) hhI hhS uᵀ
      (fun t h1 h2 => by rw [← Matrix.transpose_smul, hu t h1 h2, Matrix.transpose_zero])
    rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at this
    have := congrArg Matrix.transpose this
    rwa [Matrix.transpose_mul, Matrix.transpose_transpose] at this
  have hact : actAB (cA σ) (g, h) u = u := by
    change mat g * u * (mat h)ᵀ = u
    rw [hg, hh]
  have hcomm : om' (g, h) (G.M'.co.rho B.ψ u Φ) = G.M'.co.rho B.ψ u (om' (g, h) Φ) := by
    rw [hW.impl (g, h) u Φ hΦ, hact]
  rw [← hcomm]
  exact integral_mul_conj_map (μ := μ) (schA F _) (fun f hf => GlobalTheory.T.adelic_schwartz_mem_L2 F _ μ hμ f hf) (om' (g, h))
    (fun f hf => hW.pres (g, h) f hf) (fun f hf => hW.unit μ hμ (g, h) f hf) hΦ
    (GlobalTheory.HeisSchA.rho_mem_schA G.M' B.ψ hT.base.std u Φ hΦ)

end GlobalTheory.CptCoeff

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaOfUnitVacuum
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped TensorProduct

noncomputable section
namespace GlobalTheory.VacRead
open GlobalTheory.ThetaLawMoved GlobalTheory.ThetaLawOF

theorem theta_of_unit_vacuum : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (frS : GL (Fin S.rank) D.host.E) (frT : GL (Fin T.rank) D.host.E), Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frS.1 * S.gram * frS.1 = 1 → Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frT.1 * T.gram * frT.1 = 1 → ∀ δ : ℂ, δ ≠ 0 → ∀ (Ls : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (Lt : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), Formalism.MainNotions.StandardLatticesGL3.SD D Ls → Formalism.MainNotions.StandardLatticesGL3.SD D Lt → ∀ f : WO S T → ℂ, IsVacO ψ θ S T (fun _ => 1) (fun _ => 1) (GlobalTheory.MovedDict.inV frS Ls) (GlobalTheory.MovedDict.inV frT Lt) f → ∀ Φ : Formalism.MainNotions.TaylorLogMetric.VC D S.rank T.rank → ℂ, Differentiable ℂ Φ → (∀ w : WO S T, w.map (finPart D) = 0 → f w = GlobalTheory.FockPos.gaussO θ frS frT w * Φ (GlobalTheory.FockPos.zCo θ frS frT w)) → (fun Y => Φ (δ⁻¹ • Y)) ∈ Formalism.MainNotions.TaylorLogMetric.Th D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) Ls Lt := by
  intro D ψ θ S T frS frT hS hT δ hδ Ls Lt hLs hLt f hf Φ hΦd hΦ
  obtain ⟨ΛS, hΛS, hSd⟩ := GlobalTheory.MovedDict.isSelfDualC_inV S frS hS Ls hLs
  obtain ⟨ΛT, hΛT, hTd⟩ := GlobalTheory.MovedDict.isSelfDualC_inV T frT hT Lt hLt
  rw [← hΛS, ← hΛT] at hf
  have hψ := hf.1
  have hθ := hf.2.inf
  obtain ⟨σ, hch⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  obtain ⟨-, -, h3⟩ := GlobalTheory.T.self_dual_lattice_pairing_dual D ψ S T ΛS ΛT hψ hSd hTd
  refine ⟨hΦd.comp ((differentiable_id).const_smul δ⁻¹), ?_⟩
  intro x hx Y
  obtain ⟨v, hv, rfl⟩ := mem_La_frame_sd S T frS frT hS hT Ls Lt hLs δ x hx
  rw [← hΛS, ← hΛT] at hv
  have hv' : GlobalTheory.VacUnique.finRat S T (-v) ∈ latO S T (ΛS : Set _) (ΛT : Set _) (fun _ => True) := by
    rw [AddMonoidHom.map_neg]; exact neg_mem hv
  obtain ⟨ε, -, hε⟩ := h3 f hf.2.lat _ hv'
  have hsign := sign_eq_alpha_sd ψ S T frS frT hS hT hψ ΛS ΛT hSd hTd δ hδ v hv ε (fun g hg => hε g hg)
  have hlaw := GlobalTheory.VacUnique.apply_add_infRat hch hψ hf.2.theta v (hε f hf.2.lat)
  set X : Formalism.MainNotions.TaylorLogMetric.VC D S.rank T.rank := fun τ a b => ((GlobalTheory.FockPos.frAt frT τ)⁻¹ * Matrix.of (GlobalTheory.VacUnique.infRat S T v τ) * GlobalTheory.FockPos.frAt frS τ) a b with hX
  set Z : Formalism.MainNotions.TaylorLogMetric.VC D S.rank T.rank := δ⁻¹ • Y with hZ
  have hZY : Y = δ • Z := by rw [hZ, smul_smul, mul_inv_cancel₀ hδ, one_smul]
  set z : GlobalTheory.FockCompare.RW T S := fun τ => GlobalTheory.FockPos.frAt frT τ * Matrix.of (Z τ) * (GlobalTheory.FockPos.frAt frS τ)⁻¹ with hz
  have hzτ : ∀ τ, (GlobalTheory.FockPos.frAt frT τ)⁻¹ * Matrix.of (z τ) * GlobalTheory.FockPos.frAt frS τ = Matrix.of (Z τ) :=
    fun τ => coord_back frS frT Z τ
  have hz1 : GlobalTheory.FockPos.zCo θ frS frT (GlobalTheory.FockCompare.iotaW σ T S z) = Z := by
    rw [zCo_iota hch]; funext τ; exact coord_back frS frT Z τ
  have hz2 : GlobalTheory.FockPos.zCo θ frS frT (GlobalTheory.FockCompare.iotaW σ T S (z + GlobalTheory.VacUnique.infRat S T v)) = Z + X := by
    rw [zCo_iota hch]; funext τ
    show (GlobalTheory.FockPos.frAt frT τ)⁻¹ * (Matrix.of (z τ) + Matrix.of (GlobalTheory.VacUnique.infRat S T v τ)) * GlobalTheory.FockPos.frAt frS τ = Z τ + X τ
    rw [Matrix.mul_add, Matrix.add_mul, hzτ τ]
    rfl
  have hom : GlobalTheory.VacUnique.omO S T (GlobalTheory.VacUnique.infRat S T v) z = ∑ τ, ∑ a, ∑ b, 2 * (Complex.I * ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) *
      (starRingEnd ℂ (Z τ a b) * X τ a b)).re := by
    rw [omO_frame frS frT hS hT]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [hzτ τ]
    rfl
  have hl := hlaw z
  rw [hΦ _ (hch.real_iota T S _), hΦ _ (hch.real_iota T S _), GlobalTheory.FockPos.gaussO, GlobalTheory.FockPos.gaussO, hz1, hz2, hom, hsign] at hl

  simp only [Formalism.MainNotions.TaylorLogMetric.U]
  have e1 : δ⁻¹ • (Y + δ • X) = Z + X := by rw [smul_add, smul_smul, inv_mul_cancel₀ hδ, one_smul]
  rw [e1, hZY, torusHermitianForm_scaled_coordinate_eq hδ, torusHermitianForm_scaled_coordinate_eq hδ]
  have hZZ : δ⁻¹ • δ • Z = Z := by rw [smul_smul, inv_mul_cancel₀ hδ, one_smul]
  rw [hZZ]
  set a := Formalism.MainNotions.TaylorLogMetric.al D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) (δ • X) with ha
  have kE : Complex.exp (-(Real.pi * Complex.I) * ((-∑ τ, ∑ a, ∑ b, 2 * (Complex.I * ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) *
      (starRingEnd ℂ (Z τ a b) * X τ a b)).re : ℝ) : ℂ)) *
      Complex.exp (-((Real.pi * Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, ((‖Z τ a b‖ ^ 2 : ℝ) : ℂ)) *
      Complex.exp (-(Real.pi : ℂ) * (2 * ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, Z τ a b * starRingEnd ℂ (X τ a b)) -
        (Real.pi : ℂ) * (2 * ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, X τ a b * starRingEnd ℂ (X τ a b)) / 2) =
      Complex.exp (-((Real.pi * Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, ((‖(Z + X) τ a b‖ ^ 2 : ℝ) : ℂ)) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    simp only [Pi.add_apply]
    push_cast
    simp only [Finset.mul_sum, Finset.sum_div, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have h := entry (Z τ i j) (X τ i j) (Formalism.L2.Pj.xiR D)
    push_cast at h ⊢
    linear_combination h
  apply mul_left_cancel₀ (Complex.exp_ne_zero (-((Real.pi * Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, ((‖(Z + X) τ a b‖ ^ 2 : ℝ) : ℂ)))
  rw [← kE]
  calc _ = a * Complex.exp (-(Real.pi : ℂ) * (2 * ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, Z τ a b * starRingEnd ℂ (X τ a b)) -
        (Real.pi : ℂ) * (2 * ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, X τ a b * starRingEnd ℂ (X τ a b)) / 2) *
        (Complex.exp (-((Real.pi * Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, ((‖(Z + X) τ a b‖ ^ 2 : ℝ) : ℂ)) * Φ (Z + X)) := by
        rw [kE]; ring
    _ = _ := by
        rw [hl]
        have := al_mul_self (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) (δ • X)
        rw [← ha] at this
        linear_combination (Complex.exp (-(Real.pi * Complex.I) * ((-∑ τ, ∑ a, ∑ b, 2 * (Complex.I * ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) *
      (starRingEnd ℂ (Z τ a b) * X τ a b)).re : ℝ) : ℂ)) *
      Complex.exp (-((Real.pi * Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, ((‖Z τ a b‖ ^ 2 : ℝ) : ℂ)) *
      Complex.exp (-(Real.pi : ℂ) * (2 * ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, Z τ a b * starRingEnd ℂ (X τ a b)) -
        (Real.pi : ℂ) * (2 * ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, X τ a b * starRingEnd ℂ (X τ a b)) / 2) * Φ Z) * this

end GlobalTheory.VacRead

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTransformFixedBySmallFiniteHeisenberg
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Formalism.IndefR.Datum
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ThetaLevel

theorem uniform_locConst {X : Type} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
    [NonarchimedeanAddGroup X] (g : X → ℂ) (hg : IsLocallyConstant g) (hc : HasCompactSupport g) :
    ∃ H : OpenAddSubgroup X, ∀ z, ∀ a ∈ H, g (z + a) = g z :=
  GlobalTheory.T.exists_openAddSubgroup_invariant_of_locallyConstant g hg hc

theorem char_dot_compact {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
    [NonarchimedeanAddGroup K] (χ : AddChar K ℂ) (hχ : Continuous χ) (κ : Type) [Fintype κ] (C : Set (κ → K))
    (hC : IsCompact C) : ∃ H : OpenAddSubgroup (κ → K), ∀ z ∈ C, ∀ a ∈ H, ∀ b ∈ H, χ (z ⬝ᵥ b + a ⬝ᵥ b) = 1 :=
  GlobalTheory.T.exists_subgroup_addChar_dotProduct_trivial_on_compact χ hχ κ C hC

end GlobalTheory.ThetaLevel

namespace GlobalTheory.ThetaLevel

open Matrix

section Heis

variable {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) {κ : Type} [Fintype κ]

theorem schr_add (a b : (κ → R) × (κ → R)) (φ : (κ → R) → ℂ) (x : κ → R) :
    GlobalTheory.WeilM.schr ψ (a + b) φ x =
      ψ (-(⅟(2 : R) * (a.1 ⬝ᵥ b.2 - b.1 ⬝ᵥ a.2))) * GlobalTheory.WeilM.schr ψ a (GlobalTheory.WeilM.schr ψ b φ) x := by
  simp only [GlobalTheory.WeilM.schr, Prod.fst_add, Prod.snd_add]
  rw [← mul_assoc, ← AddChar.map_add_eq_mul, ← mul_assoc, ← AddChar.map_add_eq_mul, add_assoc x a.1 b.1]
  congr 2
  simp only [dotProduct_add, add_dotProduct]
  linear_combination (a.1 ⬝ᵥ b.2) * (invOf_two_add_invOf_two : ⅟(2 : R) + ⅟(2 : R) = 1)

end Heis

theorem symp_eq_symplO (D : D7) (S T : HSp D) (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E)
    (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E) (ξ : AF D.host.F ⊗[D.host.F] D.host.E) (hA : JA = T.gramᵀ)
    (hB : ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹)) (x y : Formalism.IndefR.Datum.WO S T) :
    GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB) x y =
      Formalism.IndefR.Datum.symplO S T x y := by
  have hB' : ∀ a b, ξ * incM D.host.F JB a b = incA (D := D) D.host.xi0 * incA (D := D) (S.gram⁻¹ a b) := by
    intro a b
    have h := congrFun (congrFun hB a) b
    rw [Matrix.smul_apply, smul_eq_mul] at h
    rw [h]
    show incA (D := D) (D.host.xi0 * S.gram⁻¹ a b) = _
    rw [map_mul]
  unfold GlobalTheory.WeilM.symp GlobalTheory.WeilM.hTens Formalism.IndefR.Datum.symplO Formalism.IndefR.Datum.hO
  congr 1
  simp only [Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  conv_lhs => rw [Finset.sum_comm]
  conv_lhs => enter [2, k]; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
  subst hA
  have hT : incM D.host.F T.gramᵀ i k = incA (D := D) (T.gram k i) := rfl
  rw [hT]
  have hc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig (y k l) = Formalism.L2.Theta.cA D (y k l) := rfl
  rw [hc]
  linear_combination (x i j * incA (D := D) (T.gram k i) * Formalism.L2.Theta.cA D (y k l)) * hB' j l

end GlobalTheory.ThetaLevel

namespace GlobalTheory.ThetaLevel

open Matrix

def infIncl (F : Type) [Field F] [NumberField F] : Ainf F →ₗ[F] AF F where
  toFun x := pairA F x 0
  map_add' _ _ := Prod.ext rfl (add_zero 0).symm
  map_smul' c _ := Prod.ext rfl (smul_zero c).symm

set_option maxHeartbeats 2000000 in

theorem infIdem_smul (D : D7) (z : AE D) :
    pairA D.host.F 1 0 • z = TensorProduct.map (infIncl D.host.F) LinearMap.id
      (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    rw [TensorProduct.smul_tmul']
    rw [Algebra.TensorProduct.map_tmul, TensorProduct.map_tmul]
    congr 1
    exact Prod.ext (one_mul _) (zero_mul _)
  | add z z' hz hz' =>
    rw [smul_add (pairA D.host.F 1 0) z z', hz, hz', map_add (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E)) z z',
      map_add]

theorem finIdem_smul (D : D7) (z : AE D) (hz : infPart D z = 0) : pairA D.host.F 0 1 • z = z := by
  have h1 : pairA D.host.F 0 1 + pairA D.host.F 1 0 = 1 := Prod.ext (zero_add 1) (add_zero 1)
  have h2 := infIdem_smul D z
  rw [show Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E) z = 0 from hz, map_zero] at h2
  calc pairA D.host.F 0 1 • z = pairA D.host.F 0 1 • z + pairA D.host.F 1 0 • z := by rw [h2, add_zero]
    _ = z := by rw [← add_smul, h1, one_smul]

theorem e_eq_fin (D : D7) (S T : HSp D) {B : Formalism.IndefR.Datum.WO S T → Formalism.IndefR.Datum.WO S T → AF D.host.F}
    {κ : Type} [Fintype κ] (co : GlobalTheory.WeilM.Darboux B κ) (u : Formalism.IndefR.Datum.WO S T)
    (hu : u.map (infPart D) = 0) :
    co.e u = ((fun i => pairA D.host.F 0 ((co.e u).1 i).2), (fun i => pairA D.host.F 0 ((co.e u).2 i).2)) := by
  have hu' : pairA D.host.F 0 1 • u = u := by
    ext a b
    exact finIdem_smul D (u a b) (congrFun (congrFun hu a) b)
  have h2 := congrArg co.e hu'
  rw [LinearEquiv.map_smul] at h2
  conv_lhs => rw [← h2]
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
  · exact Prod.ext (zero_mul _) (one_mul _)
  · exact Prod.ext (zero_mul _) (one_mul _)

theorem schr_fin_fix (F : Type) [Field F] [NumberField F] [Invertible (2 : AF F)] (ψ : AddChar (AF F) ℂ)
    (hψ : Continuous ψ) {κ : Type} [Fintype κ] (Φ : (κ → AF F) → ℂ) (hΦ : Φ ∈ GlobalTheory.WeilM.schA F κ) :
    ∃ K : OpenAddSubgroup (κ → Af F), ∀ a ∈ K, ∀ b ∈ K,
      GlobalTheory.WeilM.schr ψ ((fun i => pairA F 0 (a i)), (fun i => pairA F 0 (b i))) Φ = Φ := by
  haveI := GlobalTheory.HeisSchA.nonarch_finiteAdeleRing (F := F)
  haveI : NonarchimedeanAddGroup (κ → Af F) := GlobalTheory.HeisSchA.nonarch_pi
  induction hΦ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    obtain ⟨H1, hH1⟩ := uniform_locConst g hg.1 hg.2
    obtain ⟨H2, hH2⟩ := char_dot_compact (GlobalTheory.HeisSchA.finChar ψ)
      (hψ.comp (continuous_const.prodMk continuous_id)) κ (tsupport g) hg.2
    let c : Af F := (⅟(2 : AF F)).2
    let m : (κ → Af F) →+ (κ → Af F) := DistribMulAction.toAddMonoidHom _ c
    have hm : Continuous m := continuous_const_smul c
    refine ⟨H1 ⊓ H2 ⊓ H2.comap m hm, fun a ha b hb => funext fun x => ?_⟩
    obtain ⟨⟨ha1, -⟩, ha3⟩ := ha
    obtain ⟨⟨-, hb2⟩, -⟩ := hb
    let z : κ → Af F := fun i => (x i).2
    have hpa1 : GlobalTheory.WeilM.pureA F f g (x + fun i => pairA F 0 (a i)) =
        f (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1) * g (z + a) := by
      simp only [GlobalTheory.WeilM.pureA]
      congr 2
      funext i
      show InfiniteAdeleRing.ringEquiv_mixedSpace F ((x i).1 + 0) = _
      rw [add_zero]
    have hpa0 : GlobalTheory.WeilM.pureA F f g x = f (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1) * g z := rfl
    have harg : x ⬝ᵥ (fun i => pairA F 0 (b i)) + ⅟(2 : AF F) * ((fun i => pairA F 0 (a i)) ⬝ᵥ (fun i => pairA F 0 (b i)))
        = pairA F 0 (z ⬝ᵥ b + (c • a) ⬝ᵥ b) := by
      have e1 : GlobalTheory.HeisSchA.p1 (F := F) (x ⬝ᵥ (fun i => pairA F 0 (b i)) + ⅟(2 : AF F) *
          ((fun i => pairA F 0 (a i)) ⬝ᵥ (fun i => pairA F 0 (b i)))) = 0 := by
        rw [map_add, map_mul, RingHom.map_dotProduct, RingHom.map_dotProduct]
        have e0 : (fun i => GlobalTheory.HeisSchA.p1 (F := F) (pairA F 0 (b i))) = 0 := funext fun i => rfl
        simp only [Function.comp_def, e0, dotProduct_zero, mul_zero, add_zero]
      have e2 : GlobalTheory.HeisSchA.p2 (F := F) (x ⬝ᵥ (fun i => pairA F 0 (b i)) + ⅟(2 : AF F) *
          ((fun i => pairA F 0 (a i)) ⬝ᵥ (fun i => pairA F 0 (b i)))) = z ⬝ᵥ b + (c • a) ⬝ᵥ b := by
        rw [map_add, map_mul, RingHom.map_dotProduct, RingHom.map_dotProduct, smul_dotProduct, smul_eq_mul]
        rfl
      exact Prod.ext e1 e2
    show ψ (x ⬝ᵥ (fun i => pairA F 0 (b i)) + ⅟(2 : AF F) * ((fun i => pairA F 0 (a i)) ⬝ᵥ
      (fun i => pairA F 0 (b i)))) * GlobalTheory.WeilM.pureA F f g (x + fun i => pairA F 0 (a i)) = GlobalTheory.WeilM.pureA F f g x
    rw [harg, hpa1, hpa0, hH1 z a ha1]
    by_cases hz : g z = 0
    · rw [hz, mul_zero, mul_zero]
    · have h3 : GlobalTheory.HeisSchA.finChar ψ (z ⬝ᵥ b + (c • a) ⬝ᵥ b) = 1 := hH2 z (subset_tsupport _ hz) _ ha3 b hb2
      rw [show ψ (pairA F 0 (z ⬝ᵥ b + (c • a) ⬝ᵥ b)) = 1 from h3, one_mul]
  | zero => exact ⟨⊤, fun a _ b _ => funext fun x => mul_zero _⟩
  | add Φ₁ Φ₂ _ _ h1 h2 =>
    obtain ⟨K1, hK1⟩ := h1
    obtain ⟨K2, hK2⟩ := h2
    refine ⟨K1 ⊓ K2, fun a ha b hb => funext fun x => ?_⟩
    have e1 := congrFun (hK1 a ha.1 b hb.1) x
    have e2 := congrFun (hK2 a ha.2 b hb.2) x
    simp only [GlobalTheory.WeilM.schr] at e1 e2 ⊢
    rw [Pi.add_apply, Pi.add_apply, mul_add, e1, e2]
  | smul r Φ₁ _ h1 =>
    obtain ⟨K1, hK1⟩ := h1
    refine ⟨K1, fun a ha b hb => funext fun x => ?_⟩
    have e1 := congrFun (hK1 a ha b hb) x
    simp only [GlobalTheory.WeilM.schr] at e1 ⊢
    rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, mul_left_comm, e1]

end GlobalTheory.ThetaLevel

namespace GlobalTheory.ThetaLevel

open Matrix

set_option maxHeartbeats 1000000 in

theorem thetaTr_level : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
      (ξ : AF D.host.F ⊗[D.host.F] D.host.E), JA = T.gramᵀ →
      ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
      ∀ (κ : Type) [Fintype κ]
        (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
        (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
          co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
        ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F κ, ∃ U : AddSubgroup (Formalism.IndefR.Datum.WO S T), IsOpen (U : Set (Formalism.IndefR.Datum.WO S T)) ∧
          ∀ u ∈ U, u.map (infPart D) = 0 → Formalism.IndefR.Datum.heisO ψ S T u (GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ Φ) = GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ Φ := by
  intro D ψ hψ S T JA JB ξ hA hB κ _ co _ Φ hΦ
  haveI : IsModuleTopology (AF D.host.F) (Formalism.IndefR.Datum.WO S T) :=
    inferInstanceAs (IsModuleTopology (AF D.host.F) (Fin T.rank → Fin S.rank → AE D))
  obtain ⟨K, hK⟩ := schr_fin_fix D.host.F ψ hψ.1.1 Φ hΦ
  have hcont : Continuous co.e := IsModuleTopology.continuous_of_linearMap co.e.toLinearMap
  let f1 : Formalism.IndefR.Datum.WO S T →+ (κ → Af D.host.F) :=
    AddMonoidHom.mk' (fun u i => ((co.e u).1 i).2) (fun u v => by funext i; rw [map_add]; rfl)
  let f2 : Formalism.IndefR.Datum.WO S T →+ (κ → Af D.host.F) :=
    AddMonoidHom.mk' (fun u i => ((co.e u).2 i).2) (fun u v => by funext i; rw [map_add]; rfl)
  have hf1 : Continuous f1 :=
    continuous_pi fun i => continuous_snd.comp ((continuous_apply i).comp (continuous_fst.comp hcont))
  have hf2 : Continuous f2 :=
    continuous_pi fun i => continuous_snd.comp ((continuous_apply i).comp (continuous_snd.comp hcont))
  let U : OpenAddSubgroup (Formalism.IndefR.Datum.WO S T) := K.comap f1 hf1 ⊓ K.comap f2 hf2
  refine ⟨(U : AddSubgroup _), U.isOpen, fun u hu hinf => funext fun w => ?_⟩
  have hfix : GlobalTheory.WeilM.schr ψ (co.e u) Φ = Φ := by
    rw [e_eq_fin D S T co u hinf]
    exact hK _ hu.1 _ hu.2
  show ψ (Formalism.IndefR.Datum.symplOH S T w u) * GlobalTheory.WeilM.thetaSum D.host.F (GlobalTheory.WeilM.schr ψ (co.e (w + u)) Φ) =
    GlobalTheory.WeilM.thetaSum D.host.F (GlobalTheory.WeilM.schr ψ (co.e w) Φ)
  rw [map_add]
  have h1 : GlobalTheory.WeilM.schr ψ (co.e w + co.e u) Φ = fun x =>
      ψ (-(⅟(2 : AF D.host.F) * ((co.e w).1 ⬝ᵥ (co.e u).2 - (co.e u).1 ⬝ᵥ (co.e w).2))) *
        GlobalTheory.WeilM.schr ψ (co.e w) (GlobalTheory.WeilM.schr ψ (co.e u) Φ) x :=
    funext (schr_add ψ _ _ Φ)
  rw [h1, hfix]
  simp only [GlobalTheory.WeilM.thetaSum]
  rw [tsum_mul_left, ← mul_assoc, ← AddChar.map_add_eq_mul]
  have h2 : Formalism.IndefR.Datum.symplOH S T w u =
      ⅟(2 : AF D.host.F) * ((co.e w).1 ⬝ᵥ (co.e u).2 - (co.e u).1 ⬝ᵥ (co.e w).2) := by
    rw [← co.form, symp_eq_symplO D S T JA JB ξ hA hB, Formalism.IndefR.Datum.symplOH]
    congr 1
    refine (invOf_eq_right_inv ?_).symm
    rw [← map_ofNat (algebraMap D.host.F (AF D.host.F)) 2, ← map_mul]
    norm_num
  rw [h2, add_neg_cancel, AddChar.map_zero_eq_one, one_mul]

end GlobalTheory.ThetaLevel
end
end

