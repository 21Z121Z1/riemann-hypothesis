import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfMemWeakIn
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0323
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0325
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1345
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1241
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import ReciprocityTheory.SemistableReduction.Bundle0025
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1041
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0074
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1346
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundedHolomorphicFormEqMultiplicitySpaceValue
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1347
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsSplitCentreExponentLeOfConjMemCompact
section
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CuspQuot GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace MeasureTheory

noncomputable section

namespace GlobalTheory.CentralExponent

open Matrix GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele GlobalTheory.IdeleCovolume GlobalTheory.UnitaryBC

theorem abs_le_of_conj_mem : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), 0 < a →
    ∀ W : Set (GA E a), IsCompact W → ∃ n₀ : ℕ, ∀ (γ : GL (Fin a) E) (n : ℤ) (g : GA E a),
      g⁻¹ * (ratGL E a γ * GlobalTheory.UnitaryBC.splitCentre E a 1 ^ n) * g ∈ W → |n| ≤ n₀ := by
  intro E _ _ _ a ha W hW
  have hL : 0 < Real.log (ideleNorm (E := E) (eIdele E)) := Real.log_pos (one_lt_ideleNorm_eIdele E)
  have hc : Continuous fun x : GA E a => Real.log (ideleNorm (E := E) (GeneralLinearGroup.det x)) :=
    (continuous_ideleNorm.comp GeneralLinearGroup.continuous_det).log fun _ => ideleNorm_ne_zero _
  obtain ⟨C, hC⟩ := hW.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨⌈C / Real.log (ideleNorm (E := E) (eIdele E))⌉₊, fun γ n g hmem => ?_⟩
  have hd : GeneralLinearGroup.det (ratGL E a γ) = diag E (GeneralLinearGroup.det γ) :=
    Units.ext (by rw [ratGL, GlobalTheory.CuspRep.det_map]; rfl)
  have e : GeneralLinearGroup.det (g⁻¹ * (ratGL E a γ * splitCentre E a 1 ^ n) * g) =
      diag E (GeneralLinearGroup.det γ) * eIdele E ^ ((a : ℤ) * n) := by
    rw [map_mul, map_mul, map_mul, map_inv, map_zpow, hd, det_splitCentre_one, ← zpow_natCast, ← _root_.zpow_mul,
      mul_comm _ (GeneralLinearGroup.det g), mul_inv_cancel_left]
  have key : Real.log (ideleNorm (E := E) (GeneralLinearGroup.det
      (g⁻¹ * (ratGL E a γ * splitCentre E a 1 ^ n) * g))) =
      ((a : ℤ) * n : ℤ) * Real.log (ideleNorm (E := E) (eIdele E)) := by
    rw [e, map_mul, show ideleNorm (E := E) (diag E _) = 1 from ideleNorm_principalIdele _, one_mul, map_zpow,
      Real.log_zpow]
  have h1 := hC _ hmem
  rw [key, Real.norm_eq_abs, abs_mul, abs_of_pos hL] at h1
  have h2 : (|n| : ℝ) ≤ |(((a : ℤ) * n : ℤ) : ℝ)| := by
    push_cast
    rw [abs_mul, Nat.abs_cast]
    exact le_mul_of_one_le_left (abs_nonneg _) (by exact_mod_cast ha)
  have h3 : (|n| : ℝ) ≤ ⌈C / Real.log (ideleNorm (E := E) (eIdele E))⌉₊ :=
    (h2.trans ((le_div_iff₀ hL).2 h1)).trans (Nat.le_ceil _)
  exact_mod_cast h3

end GlobalTheory.CentralExponent
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdicCompletionDistribHaarCharEqAbsHalfSqStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adicCompletion_distribHaarChar_eq_absHalf_sq : ∀ (E : Type) [Field E] [NumberField E] (w : Pl E) (x : w.adicCompletion E) (hx : x ≠ 0), (((MeasureTheory.distribHaarChar (w.adicCompletion E) (Units.mk0 x hx) : NNReal) : ℝ) : ℂ) = absHalf w x ^ 2 := by
  first | exact @GlobalTheory.ModAbs.haar_eq_absHalf_sq | exact GlobalTheory.ModAbs.haar_eq_absHalf_sq | (intros; apply GlobalTheory.ModAbs.haar_eq_absHalf_sq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlternatingMapDetFiltrationWithSymbolsStatement
section
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.alternatingMap_det_filtration_with_symbols : ∀ (E A' : Type) [Field E] [AddCommGroup A'] [Module E A'] (r d : ℕ) (I : Fin r → Type) [∀ a, Fintype (I a)] [∀ a, DecidableEq (I a)] (U : ℕ → Submodule E A') (sym : ∀ a : Fin r, U a →ₗ[E] (I a → E)), (∀ a < r, U (a + 1) ≤ U a) → (∀ (a : Fin r) (x : U a), sym a x = 0 ↔ x.1 ∈ U (a + 1)) → ∀ (ix : (Σ a, I a) ↪ Fin d) (J : Finset (Fin d)) (v : Fin d → A') (hv : ∀ q, v (ix q) ∈ U q.1), (∀ k ∈ J, k ∉ Set.range ix ∧ v k ∈ U r) → ∀ [FiniteDimensional E (U r)], Module.finrank E (U r) ≤ J.card → ∀ (z : Fin d → A') (hz : ∀ q, z (ix q) ∈ U q.1), (∀ q, sym q.1 ⟨z (ix q), hz q⟩ = Pi.single q.2 1) → (∀ k, k ∉ Set.range ix → z k = v k) → ∀ ω : A' [⋀^Fin d]→ₗ[E] E, ω v = (∏ a, (Matrix.of fun i i' : I a => sym a ⟨v (ix ⟨a, i'⟩), hv ⟨a, i'⟩⟩ i).det) * ω z := by
  first | exact @GlobalTheory.FiltDet.det_filtration_symbols | exact GlobalTheory.FiltDet.det_filtration_symbols | (intros; apply GlobalTheory.FiltDet.det_filtration_symbols <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchActionReadingsCompatible
section
noncomputable section

open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.RealLift

section Laws

open scoped Classical

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

variable (F κ) in

def intPts : Set (κ → Af F) :=
  Set.univ.pi fun _ => {a : Af F | ∀ v, a v ∈ v.adicCompletionIntegers F}

theorem indicator_intPts_mem_SB : (intPts F κ).indicator (1 : (κ → Af F) → ℂ) ∈ SB (κ → Af F) := by
  haveI := GlobalTheory.IntegralFinAdele.t2Space_finiteAdeleRing' F
  have hO : IsOpen {a : Af F | ∀ v, a v ∈ v.adicCompletionIntegers F} :=
    RestrictedProduct.isOpen_forall_mem fun v => Valued.isOpen_valuationSubring _
  have hC : IsCompact {a : Af F | ∀ v, a v ∈ v.adicCompletionIntegers F} :=
    (GlobalTheory.IntegralFinAdele.integral_finiteAdele_properties F).1
  have hU : IsOpen (intPts F κ) := isOpen_set_pi Set.finite_univ fun _ _ => hO
  have hK : IsCompact (intPts F κ) := isCompact_univ_pi fun _ => hC
  refine ⟨?_, HasCompactSupport.intro' hK hK.isClosed fun x hx => Set.indicator_of_notMem hx _⟩
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  by_cases hx : x ∈ intPts F κ
  · filter_upwards [hU.mem_nhds hx] with y hy
    simp [Set.indicator_of_mem hy, Set.indicator_of_mem hx]
  · filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hx] with y hy
    simp [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]

theorem zero_mem_intPts : (0 : κ → Af F) ∈ intPts F κ := fun _ _ v => zero_mem _

def ptAt (a : κ → mixedEmbedding.mixedSpace F) (y : κ → Af F) : κ → AF F :=
  fun i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (a i), y i)

theorem pureA_ptAt (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (g : (κ → Af F) → ℂ) (a : κ → mixedEmbedding.mixedSpace F)
    (y : κ → Af F) : pureA F f g (ptAt a y) = f a * g y := by
  simp [pureA, ptAt]

theorem fin_eq_zero_of_at {z : κ → AF F} (hz : At (evI F) z) (i : κ) : (z i).2 = 0 := by
  have h := congrFun (hz ((0, 1) : AF F) (map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F))) i
  have h2 : (1 : Af F) * (z i).2 = 0 := congrArg Prod.snd h
  rwa [one_mul] at h2

theorem at_of_fin_eq_zero {z : κ → AF F} (hz : ∀ i, (z i).2 = 0) : At (evI F) z := by
  intro u hu
  have hu1 : u.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (by rw [map_zero]; exact hu)
  funext i
  refine Prod.ext ?_ ?_
  · change u.1 * (z i).1 = 0
    rw [hu1, zero_mul]
  · change u.2 * (z i).2 = 0
    rw [hz i, mul_zero]

theorem tens_eq_pureA (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) {r : (κ → AF F) → ℂ}
    (hr : ∀ x z, At (evI F) z → r (x + z) = r x) :
    tens (evI F) f r = pureA F f (fun y => r (fun i => ((0 : Ainf F), y i))) := by
  funext x
  simp only [tens, pureA, evI]
  congr 1
  have h := hr (fun i => ((0 : Ainf F), (x i).2)) (fun i => ((x i).1, (0 : Af F)))
    (at_of_fin_eq_zero fun i => rfl)
  rw [← h]
  congr 1
  funext i
  exact Prod.ext (zero_add _).symm (add_zero _).symm

theorem mem_SB_of_pureA_mem {f : SInf F κ} (hf : f ≠ 0) {g : (κ → Af F) → ℂ} (h : pureA F f g ∈ schA F κ) :
    g ∈ SB (κ → Af F) := by
  obtain ⟨a, ha⟩ : ∃ a, f a ≠ 0 := by
    by_contra h0
    push_neg at h0
    exact hf (SchwartzMap.ext h0)
  let L : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → Af F) → ℂ) := LinearMap.funLeft ℂ ℂ (ptAt a)
  have hle : schA F κ ≤ (SB (κ → Af F)).comap L := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨f', g', hg', rfl⟩
    change (fun y => pureA F f' g' (ptAt a y)) ∈ SB (κ → Af F)
    simp_rw [pureA_ptAt]
    exact (SB (κ → Af F)).smul_mem (f' a) hg'
  have h1 : L (pureA F f g) ∈ SB (κ → Af F) := hle h
  have h2 : L (pureA F f g) = f a • g := by
    funext y
    change pureA F f g (ptAt a y) = _
    rw [pureA_ptAt]
    rfl
  rw [h2] at h1
  have h3 := (SB (κ → Af F)).smul_mem (f a)⁻¹ h1
  rwa [smul_smul, inv_mul_cancel₀ ha, one_smul] at h3

theorem eval_mem_adm (x : κ → AF F) :
    (LinearMap.proj x : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ) ∈ (adeleClass F).adm κ := by
  intro g _
  refine ⟨g (fun i => (x i).2) • ((BoundedContinuousFunction.evalCLM ℂ
    (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1)).comp
      (SchwartzMap.toBoundedContinuousFunctionCLM ℂ _ ℂ)), fun f => ?_⟩
  simp [pureA, mul_comm]

end Laws

section Main

open scoped Classical

theorem actsLaws : ActsLaws := by
  intro F _ _ κ _ f f₁ f₂
  set g₀ : (κ → Af F) → ℂ := (intPts F κ).indicator 1 with hg₀def
  have hg₀ : g₀ ∈ SB (κ → Af F) := indicator_intPts_mem_SB
  have hg₀0 : g₀ 0 = 1 := by rw [hg₀def, Set.indicator_of_mem zero_mem_intPts]; rfl

  set r₀ : (κ → AF F) → ℂ := fun x => g₀ (fun i => (x i).2) with hr₀def
  have hr₀inv : ∀ x z, At (evI F) z → r₀ (x + z) = r₀ x := by
    intro x z hz
    change g₀ (fun i => (x i + z i).2) = g₀ (fun i => (x i).2)
    congr 1
    funext i
    change (x i).2 + (z i).2 = (x i).2
    rw [fin_eq_zero_of_at hz, add_zero]
  have htens₀ : ∀ φ : (κ → mixedEmbedding.mixedSpace F) → ℂ, tens (evI F) φ r₀ = pureA F φ g₀ := fun φ => rfl
  have hrest₀ : Rest (evI F) (⇑f) r₀ := ⟨hr₀inv, by rw [htens₀]; exact Submodule.subset_span ⟨f, g₀, hg₀, rfl⟩⟩

  have hext : ∀ h₁ h₂ : SInf F κ, (∀ a, pureA F h₁ g₀ (ptAt a 0) = pureA F h₂ g₀ (ptAt a 0)) → h₁ = h₂ := by
    intro h₁ h₂ h
    ext a
    simpa [pureA_ptAt, hg₀0] using h a

  have hzero : ∀ g : (κ → Af F) → ℂ, pureA F ⇑(0 : SInf F κ) g = 0 := by
    intro g; funext x; simp [pureA]
  have hzeroT : ∀ r : (κ → AF F) → ℂ, tens (evI F) ⇑(0 : SInf F κ) r = 0 := by
    intro r; funext x; simp [tens]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro T hT0 hSD r hr x
    by_cases hf : f = 0
    · subst hf
      have hf₁ : f₁ = 0 := hext _ _ fun a => by
        have h := hSD g₀ hg₀ _ (eval_mem_adm (ptAt a 0))
        simp only [LinearMap.proj_apply, hzero, hT0] at h
        rw [hzero]
        exact (h.unique (hasDerivAt_const 0 (0 : ℂ)))
      subst hf₁
      rw [hzeroT]
      simp only [hT0, Pi.zero_apply]
      exact hasDerivAt_const 0 (0 : ℂ)
    · have hg : (fun y => r (fun i => ((0 : Ainf F), y i))) ∈ SB (κ → Af F) :=
        mem_SB_of_pureA_mem hf (tens_eq_pureA (⇑f) hr.1 ▸ hr.2)
      have h := hSD _ hg _ (eval_mem_adm x)
      rw [tens_eq_pureA (⇑f) hr.1, tens_eq_pureA (⇑f₁) hr.1]
      exact h
  · intro T hT0 hSA r hr
    by_cases hf : f = 0
    · subst hf
      have hf₁ : f₁ = 0 := hext _ _ fun a => by
        have h := hSA g₀ hg₀
        rw [hzero, hT0] at h
        rw [← h, hzero]
      subst hf₁
      rw [hzeroT, hT0]
    · have hg : (fun y => r (fun i => ((0 : Ainf F), y i))) ∈ SB (κ → Af F) :=
        mem_SB_of_pureA_mem hf (tens_eq_pureA (⇑f) hr.1 ▸ hr.2)
      rw [tens_eq_pureA (⇑f) hr.1, tens_eq_pureA (⇑f₁) hr.1]
      exact hSA _ hg
  · intro T h₁ h₂
    refine hext _ _ fun a => ?_
    have e₁ := h₁ r₀ hrest₀ (ptAt a 0)
    have e₂ := h₂ r₀ hrest₀ (ptAt a 0)
    rw [htens₀] at e₁ e₂
    exact e₁.unique e₂
  · intro T h₁ h₂
    refine hext _ _ fun a => ?_
    have e := (h₁ r₀ hrest₀).symm.trans (h₂ r₀ hrest₀)
    rw [htens₀, htens₀] at e
    exact congrFun e (ptAt a 0)
  · intro T h₁ h₂
    refine hext _ _ fun a => ?_
    have e₁ := h₁ g₀ hg₀ _ (eval_mem_adm (ptAt a 0))
    have e₂ := h₂ g₀ hg₀ _ (eval_mem_adm (ptAt a 0))
    exact e₁.unique e₂

end Main

end GlobalTheory.RealLift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchHeisenbergDerivativeAdditiveCommutator
section
open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

namespace GlobalTheory.HeisDerivLaws

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

noncomputable def evIHom : AF F →+* mixedEmbedding.mixedSpace F :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.comp (RingHom.fst _ _)

lemma evI_eq (a : AF F) : evI F a = evIHom a := rfl

lemma evI_realAd' (r : ℝ) : evI F (realAd F r) = algebraMap ℝ (mixedEmbedding.mixedSpace F) r := by
  simp [evI, realAd]

noncomputable def trPair (w : κ → mixedEmbedding.mixedSpace F) :
    (κ → mixedEmbedding.mixedSpace F) →ₗ[ℝ] ℂ where
  toFun y := ((Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, y i * w i) : ℝ) : ℂ)
  map_add' a b := by
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, map_add, Complex.ofReal_add]
  map_smul' c a := by
    simp [smul_mul_assoc, ← Finset.smul_sum, Complex.real_smul]

lemma trPair_apply (w y : κ → mixedEmbedding.mixedSpace F) :
    trPair w y = ((Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, y i * w i) : ℝ) : ℂ) := rfl

lemma trPair_add (w w' y : κ → mixedEmbedding.mixedSpace F) :
    trPair (w + w') y = trPair w y + trPair w' y := by
  simp only [trPair_apply, Pi.add_apply, mul_add, Finset.sum_add_distrib, map_add, Complex.ofReal_add]

lemma trPair_smul (r : ℝ) (w y : κ → mixedEmbedding.mixedSpace F) :
    trPair (r • w) y = (r : ℂ) * trPair w y := by
  simp [trPair_apply, mul_smul_comm, ← Finset.smul_sum]

lemma hasFDerivAt_trPair (w x : κ → mixedEmbedding.mixedSpace F) :
    HasFDerivAt (fun y => trPair w y) (LinearMap.toContinuousLinearMap (trPair w)) x :=
  (LinearMap.toContinuousLinearMap (trPair w)).hasFDerivAt

lemma fderiv_step (f : SInf F κ) (c : ℂ) (w v' x v : κ → mixedEmbedding.mixedSpace F) :
    fderiv ℝ (fun y => fderiv ℝ (⇑f) y v' - c * trPair w y * f y) x v =
      fderiv ℝ (fderiv ℝ (⇑f)) x v v' - c * (trPair w x * fderiv ℝ (⇑f) x v + f x * trPair w v) := by
  have hf2 : DifferentiableAt ℝ (fderiv ℝ (⇑f)) x :=
    ((f.smooth ⊤).fderiv_right (m := 1) (WithTop.coe_le_coe.2 le_top)).differentiable
      one_ne_zero x
  have h1 : HasFDerivAt (fun y => fderiv ℝ (⇑f) y v')
      ((fderiv ℝ (⇑f) x).comp 0 + (fderiv ℝ (fderiv ℝ (⇑f)) x).flip v') x :=
    hf2.hasFDerivAt.clm_apply (hasFDerivAt_const v' x)
  have h2 := ((hasFDerivAt_trPair w x).const_mul c).mul (f.differentiableAt (x := x)).hasFDerivAt
  have h3 : HasFDerivAt (fun y => fderiv ℝ (⇑f) y v' - c * trPair w y * f y) _ x := h1.sub h2
  rw [h3.fderiv]
  simp
  ring

lemma evV_add (a b : κ → AF F) :
    (fun i => evI F ((a + b) i)) = (fun i => evI F (a i)) + (fun i => evI F (b i)) := by
  funext i
  show evI F (a i + b i) = evI F (a i) + evI F (b i)
  rw [evI_eq, map_add]; rfl

lemma evV_smul (r : ℝ) (a : κ → AF F) :
    (fun i => evI F ((realAd F r • a) i)) = r • (fun i => evI F (a i)) := by
  funext i
  show evI F (realAd F r * a i) = r • evI F (a i)
  rw [evI_eq, map_mul, ← evI_eq, ← evI_eq, evI_realAd', Algebra.smul_def]

lemma isSymm (f : SInf F κ) (x : κ → mixedEmbedding.mixedSpace F) : IsSymmSndFDerivAt ℝ (⇑f) x :=
  ((f.smooth ⊤).contDiffAt).isSymmSndFDerivAt (by simp; exact WithTop.coe_le_coe.2 le_top)

theorem heis_deriv_laws : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {α β κ : Type}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (JA : Matrix α α (AE F E))
    (JB : Matrix β β (AE F E)) (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ)
    (D : Matrix α β (AE F E) → (SInf F κ →L[ℂ] SInf F κ)),
    (∀ u, At (evI F) u → ∀ (f : SInf F κ) x, D u f x =
        fderiv ℝ f x (fun i => evI F ((d.e u).1 i)) - 2 * Real.pi * Complex.I *
          (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, x i * evI F ((d.e u).2 i)) : ℝ) * f x) →
    (∀ u u', At (evI F) u → At (evI F) u' → D (u + u') = D u + D u') ∧
    (∀ u (r : ℝ), At (evI F) u → D (realAd F r • u) = (r : ℂ) • D u) ∧
    (∀ u u', At (evI F) u → At (evI F) u' → ∀ f, D u (D u' f) - D u' (D u f) =
      ((-2 * Real.pi * Complex.I : ℂ) *
        ((Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F (symp (R := AF F) (cA σ) (-1) JA JB u u')) : ℝ) : ℂ)) • f) := by
  intro F E _ _ _ _ _ σ α β κ _ _ _ _ _ JA JB d D hD
  have at_add : ∀ u u' : Matrix α β (AE F E), At (evI F) u → At (evI F) u' → At (evI F) (u + u') :=
    fun u u' h h' a ha => by rw [smul_add, h a ha, h' a ha, add_zero]
  have at_smul : ∀ (u : Matrix α β (AE F E)) (r : AF F), At (evI F) u → At (evI F) (r • u) :=
    fun u r h a ha => by rw [smul_comm, h a ha, smul_zero]
  have hD' : ∀ u, At (evI F) u → ∀ (f : SInf F κ) x, D u f x =
      fderiv ℝ (⇑f) x (fun i => evI F ((d.e u).1 i)) - 2 * Real.pi * Complex.I *
        trPair (fun i => evI F ((d.e u).2 i)) x * f x := hD
  refine ⟨fun u u' hu hu' => ?_, fun u r hu => ?_, fun u u' hu hu' f => ?_⟩
  · ext f x
    rw [ContinuousLinearMap.add_apply, SchwartzMap.add_apply, hD' _ (at_add u u' hu hu'), hD' u hu,
      hD' u' hu', map_add, Prod.fst_add, Prod.snd_add, evV_add, evV_add, map_add, trPair_add]
    ring
  · ext f x
    rw [ContinuousLinearMap.smul_apply, SchwartzMap.smul_apply, hD' _ (at_smul u _ hu), hD' u hu,
      map_smul, Prod.smul_fst, Prod.smul_snd, evV_smul, evV_smul, map_smul, trPair_smul]
    simp only [Complex.real_smul, smul_eq_mul]
    ring
  · have e : ⇑(D u f) = fun y => fderiv ℝ (⇑f) y (fun i => evI F ((d.e u).1 i)) -
        2 * Real.pi * Complex.I * trPair (fun i => evI F ((d.e u).2 i)) y * f y := funext (hD' u hu f)
    have e' : ⇑(D u' f) = fun y => fderiv ℝ (⇑f) y (fun i => evI F ((d.e u').1 i)) -
        2 * Real.pi * Complex.I * trPair (fun i => evI F ((d.e u').2 i)) y * f y :=
      funext (hD' u' hu' f)
    have key : ((Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
        (evI F (symp (R := AF F) (cA σ) (-1) JA JB u u')) : ℝ) : ℂ) =
        trPair (fun i => evI F ((d.e u').2 i)) (fun i => evI F ((d.e u).1 i)) -
        trPair (fun i => evI F ((d.e u).2 i)) (fun i => evI F ((d.e u').1 i)) := by
      rw [d.form u u', evI_eq, map_sub]
      simp only [dotProduct, map_sum, map_mul, ← evI_eq, trPair_apply]
      simp only [map_sub, map_sum, Complex.ofReal_sub]
    ext x
    rw [SchwartzMap.sub_apply, SchwartzMap.smul_apply, hD' u hu (D u' f), hD' u' hu' (D u f), e', e,
      fderiv_step, fderiv_step, (isSymm f x).eq (fun i => evI F ((d.e u').1 i)), key, smul_eq_mul]
    ring

end GlobalTheory.HeisDerivLaws
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AtAlgebraMapSgnAdSubOne
section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.RealLift

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU Classical

section SignAdele

variable {F : Type} [Field F] [NumberField F]

def sgnAd (w : InfinitePlace F) : AF F :=
  (((fun v : InfinitePlace F => (if v = w then -1 else 1 : v.Completion)) : Ainf F), (1 : Af F))

theorem sgnAd_mul_self (w : InfinitePlace F) : sgnAd w * sgnAd w = 1 := by
  refine Prod.ext (funext fun v => ?_) (mul_one _)
  show (if v = w then -1 else 1 : v.Completion) * (if v = w then -1 else 1) = 1
  split_ifs <;> simp

theorem evInf_sgnAd (w v : InfinitePlace F) : evInf F v (sgnAd w) = if v = w then -1 else 1 := rfl

variable {E : Type} [Field E] [NumberField E] [Algebra F E]

theorem piInf_algebraMap {v : InfinitePlace F} (τ : EmbOver E v) (y : AF F) :
    piInf τ (algebraMap (AF F) (AE F E) y) = InfinitePlace.Completion.extensionEmbedding v (evInf F v y) := by
  unfold piInf
  rw [RingHom.comp_apply, Algebra.TensorProduct.algebraMap_apply]
  simp [compInf]

theorem at_algebraMap_sgnAd_sub_one (w : InfinitePlace F) :
    At (evI F) (algebraMap (AF F) (AE F E) (sgnAd w) - 1) := by
  intro u hu
  have h1 : u.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (by rw [map_zero]; exact hu)
  have h2 : u * (sgnAd w - 1) = 0 := by
    refine Prod.ext ?_ ?_
    · show u.1 * _ = 0
      rw [h1, zero_mul]
    · show u.2 * ((1 : Af F) - 1) = 0
      rw [sub_self, mul_zero]
  rw [← map_one (algebraMap (AF F) (AE F E)), ← map_sub, Algebra.smul_def, ← map_mul, h2, map_zero]

end SignAdele

theorem even_im_hermitian_sub : Parity := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT w
  let u : (AF F)ˣ := ⟨sgnAd w, sgnAd w, sgnAd_mul_self w, sgnAd_mul_self w⟩
  let z : (AE F E)ˣ := Units.map (algebraMap (AF F) (AE F E) : AF F →* AE F E) u
  have hz : At (evI F) ((z : AE F E) - 1) := at_algebraMap_sgnAd_sub_one w
  have hpi : ∀ v, piInf (B.emb v) (z : AE F E) = if v = w then -1 else 1 := by
    intro v
    show piInf (B.emb v) (algebraMap (AF F) (AE F E) (sgnAd w)) = _
    rw [piInf_algebraMap, evInf_sgnAd]
    split_ifs <;> simp
  have hexp : ∀ m : InfinitePlace F → ℤ,
      ∏ v, (piInf (B.emb v) (z : AE F E) / ‖piInf (B.emb v) (z : AE F E)‖) ^ m v = (-1 : ℂ) ^ m w := by
    intro m
    rw [Finset.prod_eq_single w (fun v _ hv => by rw [hpi, if_neg hv]; simp) (fun h => absurd (Finset.mem_univ w) h),
      hpi, if_pos rfl]
    simp
  have eα := hT.chars.expα z hz
  have eβ := hT.chars.expβ z hz
  rw [hexp] at eα eβ
  have rα : (X.α z : ℂ) = _ := hT.chars.resα u
  have rβ : (X.β z : ℂ) = _ := hT.chars.resβ u
  have hpar : ((-1 : ℂ)) ^ a' = (-1) ^ a := by
    have he := hT.geo.even
    rcases Nat.even_or_odd a with ha | ha
    · rw [ha.neg_one_pow, ((Nat.even_add.1 he).1 ha).neg_one_pow]
    · have ha' : Odd a' := Nat.not_even_iff_odd.1 fun h => Nat.not_even_iff_odd.2 ha ((Nat.even_add.1 he).2 h)
      rw [ha.neg_one_pow, ha'.neg_one_pow]
  have hab : (-1 : ℂ) ^ B.mα w = (-1) ^ B.mβ w := by
    rw [← eα, ← eβ, rα, rβ, hpar]
  rcases Int.even_or_odd (B.mα w - B.mβ w) with h | h
  · exact h
  · exfalso
    have h1 := h.neg_one_zpow (α := ℂ)
    rw [zpow_sub₀ (by norm_num), hab, div_self (zpow_ne_zero _ (by norm_num))] at h1
    norm_num at h1
end GlobalTheory.RealLift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BasisDetIntegralSpanEqOneStatement
section
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.span_basis_det_integral_eq_one : ∀ (F V : Type) [Field F] [NumberField F] [AddCommGroup V] [Module F V] [Module (𝓞 F) V] [IsScalarTower (𝓞 F) F V] (d : ℕ) (β : Module.Basis (Fin d) F V), Submodule.span (𝓞 F) {y | ∃ w : Fin d → V, (∀ i, w i ∈ Submodule.span (𝓞 F) (Set.range β)) ∧ y = β.det w} = 1 := by
  first | exact @GlobalTheory.basis_det_integral_span_eq_one | exact GlobalTheory.basis_det_integral_span_eq_one | (intros; apply GlobalTheory.basis_det_integral_span_eq_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundedHolomorphicFormEqMultiplicitySpaceValueStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.boundedHolomorphicForm_eq_multiplicitySpace_value : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (w : D.what₂.Tau → Fin V.rank → ℤ) (v : M.Vec), IsInfFam θ → HolShape M → WtIs M w → IsExtVec M v → (∃ μ 𝓕, FinPair V μ 𝓕) → ∀ (J : Set (GA D V)) (χ φ : GA D V → ℂ), J ⊆ (GfC V : Set (GA D V)) → HolForm θ M w J χ φ → ZCusp V φ → ∃ T : MMap M, IsMultMap θ M J χ T ∧ T v = φ := by
  first | exact @GlobalTheory.BackForm.exists_multMap | exact GlobalTheory.BackForm.exists_multMap | (intros; apply GlobalTheory.BackForm.exists_multMap <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffDetMemSpanDetIntegralPolynomialVectorsStatement
section
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeff_det_mem_span_det_integral_polynomial_vectors : ∀ (F V : Type) [Field F] [NumberField F] [AddCommGroup V] [Module F V] [Module (𝓞 F) V] [IsScalarTower (𝓞 F) F V] (M : Submodule (𝓞 F) V) (d : ℕ) (b : Module.Basis (Fin d) F V) (τ : Type) (P : Matrix (Fin d) (Fin d) (MvPolynomial τ F)), (∀ k m, ∑ i, coeff m (P i k) • b i ∈ M) → ∀ m, coeff m P.det ∈ Submodule.span (𝓞 F) {y | ∃ v : Fin d → V, (∀ i, v i ∈ M) ∧ y = b.det v} := by
  first | exact @GlobalTheory.DetCoeff.coeff_det_mem_span_det | exact GlobalTheory.DetCoeff.coeff_det_mem_span_det | (intros; apply GlobalTheory.DetCoeff.coeff_det_mem_span_det <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermSmoothParabolicStatement
section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.constant_term_smooth_parabolic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (C : Matrix (Fin n) (Fin r) E) (d : Fin r → ℕ), IsIsoCols σ J C → ∀ (H K : Subgroup (GAd σ J)) (φ c : GAd σ J → ℂ), ratPts σ J ⊓ parFlag σ J C d ≤ H → IsAutOn σ J H K φ → IsConstTermOn σ J (unipFlag σ J C d) φ c → IsSm σ J c := by
  first | exact @GlobalTheory.ConstTermSmooth.isSm_of_isConstTermOn | exact GlobalTheory.ConstTermSmooth.isSm_of_isConstTermOn | (intros; apply GlobalTheory.ConstTermSmooth.isSm_of_isConstTermOn <;> assumption)
end

