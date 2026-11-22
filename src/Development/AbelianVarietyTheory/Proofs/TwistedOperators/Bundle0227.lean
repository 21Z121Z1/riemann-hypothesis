import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0210
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0213
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.L2UnitaryRepresentationData
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0212
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0196
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0182
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0218
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0205
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0048
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SelfDualLatticesAtLevel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNsmulIntMemLatO
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0195
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0164
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0201
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CompletedTensorLatticeStrongApproxOpenCompact
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0215
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0004

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCoverKFinitePairingOfRealIntertwiner
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Matrix GlobalTheory.Chain GlobalTheory.Chain.RealIt GlobalTheory.Chain.RealLine
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix GlobalTheory.Chain.RealIt.LocalFromCover
open scoped TensorProduct InnerProductSpace

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Chain.RealLine.CoverFromLocal

section General

variable {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]

private theorem hasDerivAt_exp_smul_of_smoothVec {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {Lie : Set (Matrix (Fin n) (Fin n) ℂ)} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {w : H}
    (hw : SmoothVec Lie σ w) {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ Lie) :
    HasDerivAt (fun t : ℝ => σ (NormedSpace.exp (t • X)) w) (dRep σ X w) 0 := by
  have h1 := hw 1 (fun _ => X) (fun _ => hX)
  have hc : ContDiff ℝ 1 (fun t : ℝ => (fun _ : Fin 1 => t)) := contDiff_pi.2 (fun _ => contDiff_id)
  have h2 := (h1.of_le (by first | simp | exact_mod_cast le_top)).comp hc
  have h3 := ((h2.differentiable one_ne_zero) 0).hasDerivAt
  have e : ((fun t : Fin 1 → ℝ => σ (List.ofFn fun i => NormedSpace.exp (t i • X)).prod w) ∘
      fun t : ℝ => (fun _ : Fin 1 => t)) = fun t : ℝ => σ (NormedSpace.exp (t • X)) w := by
    funext t
    simp [List.ofFn_succ]
  rw [e] at h3
  exact h3

private theorem barMat_map_conj_eq_reindex {p q n : ℕ} (e : Ix p q ≃ Fin n) (Z : Mat p q) :
    (barMat e Z).map (starRingEnd ℂ) = Matrix.reindex e e Z := by
  ext i j
  simp [barMat]

private theorem trace_map_conj' {p q : ℕ} (Z : Mat p q) :
    (Z.map (starRingEnd ℂ)).trace = (starRingEnd ℂ) Z.trace := by
  rw [Matrix.trace, Matrix.trace, map_sum]
  rfl

private theorem norm_apply_sub_I_smul_apply (U : E ≃ₗᵢ⋆[ℂ] F) (x y : E) :
    ‖U y - Complex.I • U x‖ = ‖x - Complex.I • y‖ := by
  have hU : U y - Complex.I • U x = U (y + Complex.I • x) := by
    rw [map_add, LinearIsometryEquiv.map_smulₛₗ, Complex.conj_I, neg_smul, sub_eq_add_neg]
  have hv : x - Complex.I • y = (-Complex.I) • (y + Complex.I • x) := by
    rw [smul_add, smul_smul, neg_mul, Complex.I_mul_I, neg_neg, one_smul, neg_smul]
    abel
  rw [hU, U.norm_map, hv, norm_smul, norm_neg, Complex.norm_I, one_mul]

private theorem norm_apply_add_I_smul_apply (U : E ≃ₗᵢ⋆[ℂ] F) (x y : E) :
    ‖U y + Complex.I • U x‖ = ‖x + Complex.I • y‖ := by
  have hU : U y + Complex.I • U x = U (y - Complex.I • x) := by
    rw [map_sub, LinearIsometryEquiv.map_smulₛₗ, Complex.conj_I, neg_smul, sub_neg_eq_add]
  have hv : x + Complex.I • y = Complex.I • (y - Complex.I • x) := by
    rw [smul_sub, smul_smul, Complex.I_mul_I, neg_smul, one_smul, sub_neg_eq_add]
    abel
  rw [hU, U.norm_map, hv, norm_smul, Complex.norm_I, one_mul]

theorem inner_conjIso (U : E ≃ₗᵢ⋆[ℂ] F) (x y : E) : ⟪U y, U x⟫_ℂ = ⟪x, y⟫_ℂ := by
  have h1 : ‖U y + U x‖ = ‖x + y‖ := by rw [← map_add, U.norm_map, add_comm]
  have h2 : ‖U y - U x‖ = ‖x - y‖ := by rw [← map_sub, U.norm_map, norm_sub_rev]
  rw [inner_eq_sum_norm_sq_div_four (U y) (U x), inner_eq_sum_norm_sq_div_four x y]
  simp only [RCLike.I_to_complex]
  rw [h1, h2, norm_apply_sub_I_smul_apply, norm_apply_add_I_smul_apply]

def realOf (U : E ≃ₗᵢ⋆[ℂ] F) : E →L[ℝ] F where
  toFun := U
  map_add' := map_add U
  map_smul' r x := by
    rw [← Complex.coe_smul, LinearIsometryEquiv.map_smulₛₗ, Complex.conj_ofReal, Complex.coe_smul]
    rfl
  cont := U.continuous

end General

theorem exists_coverW : ∀ (D : D7) (V W : HSp D) (S S' : D.what₂.Tau → SPar) (M : DSModel V S) (M' : DSModel W S') (τ : D.what₂.Tau) (p q r s : ℕ) (T₁ : GrpData p q) (T₂ : GrpData r s) (R₁ : DSRep T₁) (R₂ : DSRep T₂) (e : Ix p q ≃ Fin V.rank) (e' : Ix r s ≃ Fin W.rank) (m m' : ℤ) (aS aT : ℚ) (U : M.H τ ≃ₗᵢ[ℂ] R₁.U.H) (U' : M'.H τ ≃ₗᵢ⋆[ℂ] R₂.U.H) (κ : LPol W.rank V.rank ≃ₗ[ℂ] Pol p q r s) (A : LPol W.rank V.rank →ₗ[ℂ] M'.sm τ →ₗ[ℂ] M.H τ), (m : ℚ) = 2 * aT → (m' : ℚ) = 2 * aS → GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.Matches R₁ M τ (GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.barMat e) m U → GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.Matches R₂ M' τ (GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.plainMat e') m' U' → IsPolyIso (M.ε τ) (M'.ε τ) e e' κ → LocW M M' τ aS aT A → ∃ B : Pol p q r s →ₗ[ℂ] R₂.HK.V →ₛₗ[starRingEnd ℂ] R₁.HK.V, CoverW R₁ R₂ B ∧ ∀ (P : LPol W.rank V.rank) (x : R₂.HK.V) (y : M'.sm τ), U' (y : M'.H τ) = R₂.ι x → R₁.ι (B (κ P) x) = U (A P y) := by
  intro D V W S S' M M' τ p q r s T₁ T₂ R₁ R₂ e e' m m' aS aT U U' κ A hm hm' h₁ h₂ hκ hA
  have hinj₁ : Function.Injective R₁.ι := R₁.ι_inj

  have hsm : ∀ x : R₂.HK.V, U'.symm (R₂.ι x) ∈ M'.sm τ := fun x =>
    Submodule.subset_span (h₂.smooth _ (by
      rw [LinearIsometryEquiv.apply_symm_apply]; exact Set.mem_range_self _))
  let w : R₂.HK.V → M'.sm τ := fun x => ⟨U'.symm (R₂.ι x), hsm x⟩
  have hUw : ∀ x, U' (w x : M'.H τ) = R₂.ι x := fun x => U'.apply_symm_apply _
  have hw_add : ∀ x x', w (x + x') = w x + w x' := by
    intro x x'
    apply Subtype.ext
    show U'.symm (R₂.ι (x + x')) = U'.symm (R₂.ι x) + U'.symm (R₂.ι x')
    rw [map_add, map_add]
  have hw_smul : ∀ (c : ℂ) x, w (c • x) = (starRingEnd ℂ) c • w x := by
    intro c x
    apply Subtype.ext
    show U'.symm (R₂.ι (c • x)) = (starRingEnd ℂ) c • U'.symm (R₂.ι x)
    rw [map_smul, LinearIsometryEquiv.map_smulₛₗ]

  have hex : ∀ (P : LPol W.rank V.rank) (y : M'.sm τ), ∃ v, R₁.ι v = U (A P y) :=
    fun P y => (h₁.kfin _).1 (hA.kS P y)
  choose g hg using hex
  let Bf : Pol p q r s → R₂.HK.V → R₁.HK.V := fun P x => g (κ.symm P) (w x)
  have key : ∀ P x, R₁.ι (Bf P x) = U (A (κ.symm P) (w x)) := fun P x => hg _ _
  let Bi : Pol p q r s → (R₂.HK.V →ₛₗ[starRingEnd ℂ] R₁.HK.V) := fun P =>
    { toFun := Bf P
      map_add' := by
        intro x x'
        apply hinj₁
        show R₁.ι (Bf P (x + x')) = R₁.ι (Bf P x + Bf P x')
        rw [map_add, key, key, key, hw_add, map_add, map_add]
      map_smul' := by
        intro c x
        apply hinj₁
        show R₁.ι (Bf P (c • x)) = R₁.ι ((starRingEnd ℂ) c • Bf P x)
        rw [map_smul, key, key, hw_smul, map_smul, map_smul] }
  let B : Pol p q r s →ₗ[ℂ] R₂.HK.V →ₛₗ[starRingEnd ℂ] R₁.HK.V :=
    { toFun := Bi
      map_add' := by
        intro P P'
        ext x
        apply hinj₁
        show R₁.ι (Bf (P + P') x) = R₁.ι (Bf P x + Bf P' x)
        rw [map_add, key, key, key, map_add, map_add, LinearMap.add_apply, map_add]
      map_smul' := by
        intro c P
        ext x
        apply hinj₁
        show R₁.ι (Bf (c • P) x) = R₁.ι (c • Bf P x)
        rw [map_smul, key, key, map_smul, map_smul, LinearMap.smul_apply, map_smul] }
  have hB : ∀ P x, R₁.ι (B P x) = U (A (κ.symm P) (w x)) := key
  refine ⟨B, { adj := ?_, src := ?_, tgt := ?_ }, ?_⟩
  ·
    intro P x
    obtain ⟨b0, hb0K, hb0⟩ := hA.kT (κ.symm P) (U.symm (R₁.ι x))
    obtain ⟨b, hb⟩ := (h₂.kfin b0).1 hb0K
    refine ⟨b, fun y => ?_⟩
    have e2 : R₁.ι x = U (U.symm (R₁.ι x)) := (U.apply_symm_apply _).symm
    rw [hB, hb, ← hUw y, inner_conjIso, ← hb0]
    conv_lhs => rw [e2]
    exact LinearIsometryEquiv.inner_map_map U _ _
  ·
    intro Z hZ P y
    apply hinj₁
    have hloc : κ.symm (fockAct1 p q r s Z P) =
        locS (M.ε τ) (M'.ε τ) (Matrix.reindex e e Z) (κ.symm P) := by
      rw [LinearEquiv.symm_apply_eq, hκ.1, LinearEquiv.apply_symm_apply]
    have hX : toFrame M τ (barMat e Z) ∈ lieAt V τ := by
      rw [← h₁.lie]; exact ⟨Z, hZ, rfl⟩
    have hsx : SmoothVec (lieAt V τ) (M.rep τ) (A (κ.symm P) (w y)) :=
      h₁.smooth _ ⟨_, hB P y⟩
    have hd1 := hasDerivAt_exp_smul_of_smoothVec hsx hX
    have hdr : dRep (M.rep τ) (toFrame M τ (barMat e Z)) (A (κ.symm P) (w y)) =
        A (locS (M.ε τ) (M'.ε τ) ((M.fr τ * toFrame M τ (barMat e Z) * (M.fr τ)⁻¹).map (starRingEnd ℂ))
          (κ.symm P) - ((aT : ℂ) * (toFrame M τ (barMat e Z)).trace) • κ.symm P) (w y) := by
      apply ext_inner_left ℂ
      intro u
      have hd2 := hA.src _ hX (κ.symm P) (w y) u
      have hd3 := (hasDerivAt_const (0 : ℝ) u).inner ℂ hd1
      simp only [inner_zero_left, add_zero] at hd3
      exact hd3.unique hd2
    have htr : (toFrame M τ (barMat e Z)).trace = -Z.trace := by
      rw [trace_toFrame, barMat, trace_reindex', trace_map_conj', trace_conj hZ]
    rw [fr_toFrame, barMat_map_conj_eq_reindex, htr] at hdr
    have hder := h₁.der Z hZ (B P y) _ (hB P y).symm
    rw [hdr] at hder
    have hc : ((m : ℂ) / 2 * Z.trace) = (aT : ℂ) * Z.trace := by
      have h2 : (m : ℂ) = 2 * (aT : ℂ) := by exact_mod_cast hm
      rw [h2]; ring
    simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, map_add, hc, hB] at hder
    rw [hB, hloc]
    rw [mul_neg, neg_smul, sub_neg_eq_add] at hder
    exact add_right_cancel hder
  ·
    intro Z hZ P y
    apply hinj₁
    rw [map_add, map_zero, hB, hB]
    have hp : plainMat e' Z = Matrix.reindex e' e' Z := rfl
    have hloc : κ.symm (fockAct2 p q r s Z P) =
        locT (M.ε τ) (M'.ε τ) (plainMat e' Z) (κ.symm P) := by
      rw [hp, LinearEquiv.symm_apply_eq, hκ.2, LinearEquiv.apply_symm_apply]
    have hY : toFrame M' τ (plainMat e' Z) ∈ lieAt W τ := by
      rw [← h₂.lie]; exact ⟨Z, hZ, rfl⟩
    have hsw : SmoothVec (lieAt W τ) (M'.rep τ) (w y : M'.H τ) :=
      h₂.smooth _ (by rw [hUw]; exact Set.mem_range_self _)
    have hd := hasDerivAt_exp_smul_of_smoothVec hsw hY
    have hder := h₂.der Z hZ y (w y) (hUw y)
    have hsm' : dRep (M'.rep τ) (toFrame M' τ (plainMat e' Z)) (w y : M'.H τ) ∈ M'.sm τ :=
      Submodule.subset_span (h₂.smooth _ (by rw [hder]; exact Set.mem_range_self _))
    have ht := hA.tgt _ hY (κ.symm P) (w y) ⟨_, hsm'⟩ hd
    have htr : (toFrame M' τ (plainMat e' Z)).trace = Z.trace := by
      rw [trace_toFrame, plainMat, trace_reindex']
    rw [htr, fr_toFrame] at ht
    have hcs : ((m' : ℂ) / 2 * Z.trace) + (starRingEnd ℂ) ((aS : ℂ) * Z.trace) = 0 := by
      have h2 : (m' : ℂ) = 2 * (aS : ℂ) := by exact_mod_cast hm'
      rw [map_mul, trace_conj hZ, map_ratCast, h2]; ring
    have hw2 : w (R₂.HK.act Z y) = ⟨_, hsm'⟩ + ((aS : ℂ) * Z.trace) • w y := by
      apply Subtype.ext
      apply U'.injective
      rw [Submodule.coe_add, Submodule.coe_smul, map_add, LinearIsometryEquiv.map_smulₛₗ, hder, hUw, hUw,
        map_add, map_smul, add_assoc, ← add_smul, hcs, zero_smul, add_zero]
    rw [hloc, hw2, map_add, map_smul, ← map_add, ← map_zero U]
    congr 1
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply] at ht
    rw [← ht]
    abel
  ·
    intro P x y hy
    have hwy : w x = y := by
      apply Subtype.ext
      show U'.symm (R₂.ι x) = (y : M'.H τ)
      rw [← hy, LinearIsometryEquiv.symm_apply_apply]
    rw [hB, LinearEquiv.symm_apply_apply, hwy]

end GlobalTheory.Chain.RealLine.CoverFromLocal

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFockPolynomialIsoGradedIsometry
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open Formalism.IndefR.Mult (DSModel dualPar parA parB)
open Formalism.MainNotions.SchurIrreducible (AdmGK ARi ARiiiUp ARiiiDown ARiiiLine DiscreteSeriesBlattner admQ5)
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction hiding Mat
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix (SignCompat plainMat barMat)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (fockIp)
open GlobalTheory.Chain (signed)
open GlobalTheory.Chain.RealIt (LPol locS locT IsPolyIso)
open MeasureTheory Matrix
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ArchRec

namespace GlobalTheory.ArchRec.SignedRename

open MvPolynomial

section General

variable {ι κ : Type} (σ : ι ≃ κ) (s : ι → ℂ)

def ren : MvPolynomial ι ℂ →ₐ[ℂ] MvPolynomial κ ℂ := aeval fun v => s v • (X (σ v) : MvPolynomial κ ℂ)

theorem ren_monomial (k : ι →₀ ℕ) (c : ℂ) :
    ren σ s (monomial k c) = monomial (k.mapDomain σ) ((k.prod fun v n => s v ^ n) * c) := by
  classical
  have h1 : ∀ (v : ι) (n : ℕ), (s v • (X (σ v) : MvPolynomial κ ℂ)) ^ n =
      C (s v ^ n) * monomial (Finsupp.single (σ v) n) 1 := by
    intro v n
    rw [smul_pow, X_pow_eq_monomial, smul_eq_C_mul]
  rw [ren, aeval_monomial, Finsupp.mapDomain, monomial_finsupp_sum_index]
  simp only [Finsupp.prod, h1, Finset.prod_mul_distrib, algebraMap_eq]
  rw [← map_prod, C_mul]
  ring

theorem coeff_ren (k : ι →₀ ℕ) (P : MvPolynomial ι ℂ) :
    coeff (k.mapDomain σ) (ren σ s P) = (k.prod fun v n => s v ^ n) * coeff k P := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial m c =>
    rw [ren_monomial, coeff_monomial, coeff_monomial]
    by_cases hm : m = k
    · subst hm
      simp
    · rw [if_neg hm, if_neg (fun h => hm (Finsupp.mapDomain_injective σ.injective h)), mul_zero]
  | add P Q hP hQ => rw [map_add, coeff_add, coeff_add, hP, hQ, mul_add]

theorem isHomogeneous_ren {ι κ : Type} (f : ι → κ) (s : ι → ℂ) (d : ℕ) (P : MvPolynomial ι ℂ) (h : P.IsHomogeneous d) :
    (aeval (fun v => s v • (X (f v) : MvPolynomial κ ℂ)) P).IsHomogeneous d := by
  have hg : ∀ v, (s v • (X (f v) : MvPolynomial κ ℂ)).IsHomogeneous 1 := by
    intro v
    rw [smul_eq_C_mul]
    exact isHomogeneous_C_mul_X _ _
  have h0 : ∀ r : ℂ, (algebraMap ℂ (MvPolynomial κ ℂ) r).IsHomogeneous 0 := fun r => isHomogeneous_C κ r
  rw [aeval_def]
  simpa only [one_mul] using h.eval₂ (algebraMap ℂ (MvPolynomial κ ℂ)) _ h0 hg

theorem fockIp_ren (hs : ∀ v, s v * conj (s v) = 1) (P Q : MvPolynomial ι ℂ) :
    fockIp (ren σ s P) (ren σ s Q) = fockIp P Q := by
  classical
  have hs0 : ∀ v, s v ≠ 0 := fun v h0 => by simpa [h0] using hs v
  have hp : ∀ k : ι →₀ ℕ, (k.prod fun v n => s v ^ n) ≠ 0 := by
    intro k
    rw [Finsupp.prod]
    exact Finset.prod_ne_zero_iff.mpr fun v _ => pow_ne_zero _ (hs0 v)
  have hpc : ∀ k : ι →₀ ℕ, (k.prod fun v n => s v ^ n) * conj (k.prod fun v n => s v ^ n) = 1 := by
    intro k
    rw [Finsupp.prod, map_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun v _ => ?_
    rw [map_pow, ← mul_pow, hs v, one_pow]
  have hback : ∀ k' : κ →₀ ℕ, (k'.mapDomain σ.symm).mapDomain σ = k' := by
    intro k'
    rw [← Finsupp.mapDomain_comp, Equiv.self_comp_symm, Finsupp.mapDomain_id]
  have hfwd : ∀ k : ι →₀ ℕ, (k.mapDomain σ).mapDomain σ.symm = k := by
    intro k
    rw [← Finsupp.mapDomain_comp, Equiv.symm_comp_self, Finsupp.mapDomain_id]
  have hc : ∀ (R : MvPolynomial ι ℂ) (k' : κ →₀ ℕ), coeff k' (ren σ s R) =
      ((k'.mapDomain σ.symm).prod fun v n => s v ^ n) * coeff (k'.mapDomain σ.symm) R := by
    intro R k'
    conv_lhs => rw [← hback k']
    exact coeff_ren σ s _ R
  unfold fockIp
  refine Finset.sum_nbij' (fun k' => k'.mapDomain σ.symm) (fun k => k.mapDomain σ) ?_ ?_ ?_ ?_ ?_
  · intro k' hk'
    rw [mem_support_iff] at hk' ⊢
    rw [hc] at hk'
    exact right_ne_zero_of_mul hk'
  · intro k hk
    rw [mem_support_iff] at hk ⊢
    rw [coeff_ren]
    exact mul_ne_zero (hp k) hk
  · intro k' _
    exact hback k'
  · intro k _
    exact hfwd k
  · intro k' _
    have hF : ((k'.prod fun _ e => e.factorial : ℕ) : ℂ) =
        (((k'.mapDomain σ.symm).prod fun _ e => e.factorial : ℕ) : ℂ) := by
      have := Finsupp.prod_mapDomain_index_inj (h := fun (_ : κ) (e : ℕ) => e.factorial) σ.injective
        (s := k'.mapDomain σ.symm)
      rw [hback] at this
      rw [this]
    rw [hc P, hc Q, hF, map_mul]
    have := hpc (k'.mapDomain σ.symm)
    calc _ = (((k'.mapDomain σ.symm).prod fun v n => s v ^ n) *
          conj ((k'.mapDomain σ.symm).prod fun v n => s v ^ n)) *
          (coeff (k'.mapDomain σ.symm) P * conj (coeff (k'.mapDomain σ.symm) Q) *
          (((k'.mapDomain σ.symm).prod fun _ e => e.factorial : ℕ) : ℂ)) := by ring
      _ = _ := by rw [this, one_mul]

end General

open GlobalTheory.Chain.RealIt.PolyIso in

theorem exists_isPolyIso_graded_isometry : ∀ (p q r s a b : ℕ) (ε : Fin a → Bool) (ε' : Fin b → Bool) (e : Ix p q ≃ Fin a) (e' : Ix r s ≃ Fin b), SignCompat ε e → SignCompat ε' e' → ∃ κ : LPol b a ≃ₗ[ℂ] Pol p q r s, IsPolyIso ε ε' e e' κ ∧ Graded κ ∧ ∀ P Q, fockIp (κ P) (κ Q) = fockIp P Q := by
  intro p q r s a b ε ε' e e' h h'
  refine ⟨(kap ε e e').toLinearEquiv, ⟨fun Z P => fwd_locS h h' Z P, fun Z P => fwd_locT h h' Z P⟩, ?_, ?_⟩
  · intro d P
    constructor
    · intro hP
      have hb : bwd ε e e' ((kap ε e e').toLinearEquiv P) = P := (kap ε e e').symm_apply_apply P
      rw [← hb]
      exact isHomogeneous_ren (fun l : Ix p q × Ix r s => (e' l.2, e l.1))
        (fun l => GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.sgn (ε (e l.1))) d _ hP
    · intro hP
      exact isHomogeneous_ren (fun v : Fin b × Fin a => (e.symm v.2, e'.symm v.1))
        (fun v => GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.sgn (ε v.2)) d P hP
  · intro P Q
    let τ : Fin b × Fin a ≃ Ix p q × Ix r s := (Equiv.prodComm _ _).trans (Equiv.prodCongr e.symm e'.symm)
    have hs : ∀ v : Fin b × Fin a, GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.sgn (ε v.2) * conj (GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.sgn (ε v.2)) = 1 := by
      intro v
      unfold GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.sgn
      split <;> simp
    exact fockIp_ren τ (fun v => GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.sgn (ε v.2)) hs P Q

end GlobalTheory.ArchRec.SignedRename

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsGlobalFockIntertwinerTensorRealPlacesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Matrix GlobalTheory.Chain GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_globalFockIntertwiner_tensor_realPlaces : ∀ (D : D7) (V W : HSp D) (S S' : D.what₂.Tau → SPar) (M : DSModel V S) (M' : DSModel W S') (aS aT : D.what₂.Tau → ℚ) (A : ∀ τ, LPol W.rank V.rank →ₗ[ℂ] M'.H τ →ₗ[ℂ] M.H τ), GlobalTheory.IndefiniteRowSideFullHecke.ContractionTensorModels.ContrTensor → GlueLaw D V.rank W.rank → (∀ τ, LocIt M M' τ (aS τ) (aT τ) (A τ)) → ∃ It I, GlobIt M M' aS aT It I := by
  first | exact @GlobalTheory.Chain.RealIt.TensorGlob.exists_globIt | exact GlobalTheory.Chain.RealIt.TensorGlob.exists_globIt | (intros; apply GlobalTheory.Chain.RealIt.TensorGlob.exists_globIt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIdempotentComponentOfGroupElementStatement
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
theorem _root_.GlobalTheory.T.exists_idempotent_component_of_group_element : ∀ {D : D7} (T : HSp D) (g : GA D T) (ε : AE D), g ∈ GfC T → ε * ε = ε → cA D ε = ε → ∃ k : GA D T, k ∈ GfC T ∧ Formalism.L2.Theta.mt T k = ε • Formalism.L2.Theta.mt T g + (1 - ε) • (1 : Matrix (Fin T.rank) (Fin T.rank) (AE D)) := by
  first | exact @GlobalTheory.GfCut.exists_cut | exact GlobalTheory.GfCut.exists_cut | (intros; apply GlobalTheory.GfCut.exists_cut <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIntegerConjPrescribedResiduesPlaces
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SW.Lev

theorem exists_bar_mk_eq_at_places : ∀ (D : D7) (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (b : ∀ PP : Formalism.L2.DIV.Pl D.host.E, Formalism.L2.DIV.kP PP), ∃ c : 𝓞 D.host.E, ∀ PP ∈ P, Ideal.Quotient.mk PP.asIdeal (GlobalTheory.SW.Lev.bar c) = b PP := by
  intro D P b
  obtain ⟨y, hy⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal
    (s := P) (fun PP : Formalism.L2.DIV.Pl D.host.E => PP.asIdeal) (fun _ => 1)
    (fun PP _ => PP.prime) (fun i _ j _ hij h => hij (HeightOneSpectrum.ext h))
    (fun PP => Classical.choose (Ideal.Quotient.mk_surjective (b PP.1)))
  refine ⟨GlobalTheory.SW.Lev.bar y, fun PP hPP => ?_⟩
  rw [GlobalTheory.SW.Lev.bar_bar]
  have h := hy PP hPP
  rw [pow_one] at h
  have hc := Classical.choose_spec (Ideal.Quotient.mk_surjective (b PP))
  rw [← hc]
  exact Ideal.Quotient.eq.2 h

end GlobalTheory.SW.Lev
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIntegralInverseOnConjugateHalfStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LiftLevel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_inverse_on_conjugate_half : ∀ (D : D7) (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D), IsIdemSum e P → ∀ s : 𝓞 D.host.E, (∀ PP ∈ P, s ∉ conjI PP.asIdeal) → ∃ t : AE D, finPart D t ∈ intAE D ∧ t * incA D (s : D.host.E) * cA D e = cA D e := by
  first | exact @GlobalTheory.HalfUnit.exists_int_inv_half | exact GlobalTheory.HalfUnit.exists_int_inv_half | (intros; apply GlobalTheory.HalfUnit.exists_int_inv_half <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLocalFockIntertwinerRealPlaceOfCoverContraStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Matrix GlobalTheory.Chain GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_localFockIntertwiner_realPlace_of_coverContraction : ∀ (D : D7) (V W : HSp D) (S S' : D.what₂.Tau → SPar) (M : DSModel V S) (M' : DSModel W S') (τ : D.what₂.Tau) (p q r s : ℕ) (T₁ : GrpData p q) (T₂ : GrpData r s) (R₁ : DSRep T₁) (R₂ : DSRep T₂) (e : Ix p q ≃ Fin V.rank) (e' : Ix r s ≃ Fin W.rank) (m m' : ℤ) (aS aT : ℚ) (U : M.H τ ≃ₗᵢ[ℂ] R₁.U.H) (U' : M'.H τ ≃ₗᵢ⋆[ℂ] R₂.U.H) (κ : LPol W.rank V.rank ≃ₗ[ℂ] Pol p q r s) (B : Pol p q r s →ₗ[ℂ] R₂.U.H →ₛₗ[starRingEnd ℂ] R₁.U.H), (m : ℚ) = 2 * aT → (m' : ℚ) = 2 * aS → GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.Matches R₁ M τ (GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.barMat e) m U → GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.Matches R₂ M' τ (GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.plainMat e') m' U' → Nontrivial R₂.HK.V → IsPolyIso (M.ε τ) (M'.ε τ) e e' κ → IsCoverIt R₁ R₂ B → ∃ A : LPol W.rank V.rank →ₗ[ℂ] M'.H τ →ₗ[ℂ] M.H τ, LocIt M M' τ aS aT A := by
  first | exact @GlobalTheory.Chain.RealIt.LocalFromCover.exists_locIt | exact GlobalTheory.Chain.RealIt.LocalFromCover.exists_locIt | (intros; apply GlobalTheory.Chain.RealIt.LocalFromCover.exists_locIt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsMultiplierShiftedLatticeAwayFromPlacesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_multiplier_shifted_lattice_away_from_places : ∀ (D : D7) (r : ℕ) (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (L : Lt D.host.E r) (w : HeightOneSpectrum (𝓞 D.host.F)), (∀ PP ∈ Pg ∪ Q, HeightOneSpectrum.under (𝓞 D.host.F) PP ≠ w) → ∀ u ∈ idq (GlobalTheory.LiftLevel.liftI Pg Q) (conjI (GlobalTheory.LiftLevel.liftI Pg Q)) L, ∃ t : 𝓞 D.host.F, t ∉ w.asIdeal ∧ algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t • u ∈ L := by
  first | exact @GlobalTheory.TrOffShift.shift_mult | exact GlobalTheory.TrOffShift.shift_mult | (intros; apply GlobalTheory.TrOffShift.shift_mult <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsMultiplierStandardLatticeOfMoverTrivialStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_multiplier_standard_lattice_of_mover_trivial : ∀ (D : D7) (S : HSp D) (k₀ : GA D S) (Λ' : Lt D.host.E S.rank) (σ : Af D.host.F) (w : HeightOneSpectrum (𝓞 D.host.F)), evalV D.host.F w σ = 0 → (∀ i j, (1 - algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 σ)) * (mt S k₀⁻¹ - 1) i j = 0) → IsMov (fmtC S k₀⁻¹) Λ' (stdL D.host.E S.rank) → ∀ v ∈ Λ', ∃ t : 𝓞 D.host.F, t ∉ w.asIdeal ∧ algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t • v ∈ stdL D.host.E S.rank := by
  first | exact @GlobalTheory.Ker.MoverStd.exists_mul_std | exact GlobalTheory.Ker.MoverStd.exists_mul_std | (intros; apply GlobalTheory.Ker.MoverStd.exists_mul_std <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockCreationPreservesFockVectorsTwoFramesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockCreation_preserves_fockVectors_two_frames : ∀ (D : D7) (V W : HSp D) (A : GlobalTheory.ChainFr.Fr V) (B : GlobalTheory.ChainFr.Fr W) (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → IsInfFam θ → ∀ f, IsThetaFunO ψ V W f → ∀ (τ : D.what₂.Tau) (z : Matrix (Fin W.rank) (Fin V.rank) ℂ) (P : PolF D W.rank V.rank), ∃ Q : PolF D W.rank V.rank, crea (heisO ψ V W) θ τ (cplxO (A.cart τ) (B.cart τ)) z (GlobalTheory.ChainFr.ptF ψ θ A B f P) = GlobalTheory.ChainFr.ptF ψ θ A B f Q := by
  first | exact @GlobalTheory.FockCreaDir.crea_ptF | exact GlobalTheory.FockCreaDir.crea_ptF | (intros; apply GlobalTheory.FockCreaDir.crea_ptF <;> assumption)
end

