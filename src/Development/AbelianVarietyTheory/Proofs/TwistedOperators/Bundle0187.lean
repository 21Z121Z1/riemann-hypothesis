import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0176
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0104
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0186
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0149
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0038
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0049
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0172
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1010
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1039
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0070
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1021
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0165
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0078
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0068
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
import Formalism.LocalToGlobal.IndefiniteReal.PHeisFC
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0175
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InstAddCommGroupTwo
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0177
import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergEquivariantIsometry
section
open MeasureTheory
open scoped SchwartzMap

noncomputable section

namespace GlobalTheory.HeisenbergL2

section Real

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

def heisS (a : V) (L : V →L[ℝ] ℝ) (c t : ℝ) (f : 𝓢(V, ℂ)) : 𝓢(V, ℂ) :=
  SchwartzMap.smulLeftCLM ℂ
    (fun x => Complex.exp (-(2 * Real.pi * Complex.I) * ((t * L x + t ^ 2 * c : ℝ) : ℂ)))
    (SchwartzMap.compSubConstCLM ℂ (-(t • a)) f)

def derS (a : V) (L : V →L[ℝ] ℝ) (f : 𝓢(V, ℂ)) : 𝓢(V, ℂ) :=
  LineDeriv.lineDerivOpCLM ℂ 𝓢(V, ℂ) a f -
    (2 * Real.pi * Complex.I) • SchwartzMap.smulLeftCLM ℂ (fun x => ((L x : ℝ) : ℂ)) f

theorem heisS_apply (a : V) (L : V →L[ℝ] ℝ) (c t : ℝ) (f : 𝓢(V, ℂ)) (x : V) :
    heisS a L c t f x =
      Complex.exp (-(2 * Real.pi * Complex.I) * ((t * L x + t ^ 2 * c : ℝ) : ℂ)) * f (x + t • a) := by
  rw [heisS, SchwartzMap.smulLeftCLM_apply_apply (by
      rw [GlobalTheory.LinPhaseSeminorm.phase_eq]; exact GlobalTheory.LinPhaseSeminorm.hasTemperateGrowth_phase L c t),
    SchwartzMap.compSubConstCLM_apply, smul_eq_mul, sub_neg_eq_add]

theorem derS_apply (a : V) (L : V →L[ℝ] ℝ) (f : 𝓢(V, ℂ)) (x : V) :
    derS a L f x = fderiv ℝ f x a - 2 * Real.pi * Complex.I * ((L x : ℝ) : ℂ) * f x := by
  have hL : Function.HasTemperateGrowth (fun x => ((L x : ℝ) : ℂ)) :=
    (Complex.ofRealCLM.comp L).hasTemperateGrowth
  rw [derS, SchwartzMap.sub_apply, SchwartzMap.smul_apply, SchwartzMap.smulLeftCLM_apply_apply hL,
    LineDeriv.lineDerivOpCLM_apply, SchwartzMap.lineDerivOp_apply_eq_fderiv, smul_eq_mul, smul_eq_mul]
  ring

theorem seminorm_heisS_sub_le (a : V) (L : V →L[ℝ] ℝ) (c : ℝ) (f : 𝓢(V, ℂ)) (k n : ℕ) :
    ∃ C : ℝ, ∀ t : ℝ, |t| ≤ 1 →
      SchwartzMap.seminorm ℂ k n (heisS a L c t f - f - (t : ℂ) • derS a L f) ≤ C * t ^ 2 := by
  set P : 𝓢(V, ℂ) →L[ℂ] 𝓢(V, ℂ) := SchwartzMap.smulLeftCLM ℂ (fun x => ((L x : ℝ) : ℂ)) with hP
  set d := LineDeriv.lineDerivOpCLM ℂ 𝓢(V, ℂ) a f with hd
  obtain ⟨C3, hC3⟩ := GlobalTheory.LinPhaseSeminorm.seminorm_smulLeft_phase_le L c k n
  choose C1 hC1 using fun m => GlobalTheory.SchwartzTranslate.seminorm_translate_sub_le a f k m
  obtain ⟨C2, hC2⟩ := GlobalTheory.LinearPhase.seminorm_phase_sub_le L c d k n
  obtain ⟨C0, hC0⟩ := GlobalTheory.LinearPhase.seminorm_phase_sub_le L c f k n
  set p := SchwartzMap.seminorm ℂ k n (E := V) (F := ℂ) with hp
  refine ⟨|C3| * ∑ m ∈ Finset.range (n + 1), |C1 m| + |C2| + 2 * Real.pi * p (P d) + |C0|, fun t ht => ?_⟩
  set M : 𝓢(V, ℂ) →L[ℂ] 𝓢(V, ℂ) := SchwartzMap.smulLeftCLM ℂ
    (fun x => Complex.exp (-(2 * Real.pi * Complex.I) * ((t * L x + t ^ 2 * c : ℝ) : ℂ))) with hM
  set X := SchwartzMap.compSubConstCLM ℂ (-(t • a)) f - f - (t : ℂ) • d with hX
  set Y := M d - d + ((t : ℂ) * (2 * Real.pi * Complex.I)) • P d with hY
  set Z := M f - f + ((t : ℂ) * (2 * Real.pi * Complex.I)) • P f with hZ
  have e : heisS a L c t f - f - (t : ℂ) • derS a L f =
      M X + (t : ℂ) • Y - ((t : ℂ) ^ 2 * (2 * Real.pi * Complex.I)) • P d + Z := by
    rw [heisS, derS, ← hM, ← hP, ← hd, hX, hY, hZ, map_sub, map_sub, map_smul]
    module
  rw [e]
  have t1 : p (M X) ≤ |C3| * (∑ m ∈ Finset.range (n + 1), |C1 m|) * t ^ 2 := by
    refine (hC3 t ht X).trans ?_
    calc C3 * ∑ m ∈ Finset.range (n + 1), SchwartzMap.seminorm ℂ k m X
        ≤ |C3| * ∑ m ∈ Finset.range (n + 1), SchwartzMap.seminorm ℂ k m X :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (Finset.sum_nonneg fun _ _ => apply_nonneg _ _)
      _ ≤ |C3| * ∑ m ∈ Finset.range (n + 1), |C1 m| * t ^ 2 :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun m _ =>
            (hC1 m t ht).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (sq_nonneg _))) (abs_nonneg _)
      _ = |C3| * (∑ m ∈ Finset.range (n + 1), |C1 m|) * t ^ 2 := by rw [← Finset.sum_mul]; ring
  have t2 : p ((t : ℂ) • Y) ≤ |C2| * t ^ 2 := by
    rw [map_smul_eq_mul, Complex.norm_real, Real.norm_eq_abs]
    have h2 := hC2 t ht
    calc |t| * p Y ≤ 1 * (C2 * t ^ 2) := mul_le_mul ht h2 (apply_nonneg _ _) zero_le_one
      _ ≤ |C2| * t ^ 2 := by rw [one_mul]; exact mul_le_mul_of_nonneg_right (le_abs_self _) (sq_nonneg _)
  have t3 : p (((t : ℂ) ^ 2 * (2 * Real.pi * Complex.I)) • P d) = 2 * Real.pi * p (P d) * t ^ 2 := by
    rw [map_smul_eq_mul]
    simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, Complex.norm_ofNat, Complex.norm_I,
      abs_of_pos Real.pi_pos, sq_abs]
    ring
  have t4 : p Z ≤ |C0| * t ^ 2 := (hC0 t ht).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (sq_nonneg _))
  have tri : p (M X + (t : ℂ) • Y - ((t : ℂ) ^ 2 * (2 * Real.pi * Complex.I)) • P d + Z) ≤
      p (M X) + p ((t : ℂ) • Y) + p (((t : ℂ) ^ 2 * (2 * Real.pi * Complex.I)) • P d) + p Z := by
    refine (map_add_le_add p _ _).trans (add_le_add ?_ le_rfl)
    refine (map_sub_le_add p _ _).trans (add_le_add ?_ le_rfl)
    exact map_add_le_add p _ _
  rw [t3] at tri
  nlinarith [t1, t2, t4, tri]

end Real

section L2

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V]

theorem toLp_heisS_sub_le (μ : Measure V) [μ.HasTemperateGrowth] (a : V) (L : V →L[ℝ] ℝ) (c : ℝ)
    (f : 𝓢(V, ℂ)) : ∃ K : ℝ, ∀ t : ℝ, |t| ≤ 1 →
      ‖(heisS a L c t f - f - (t : ℂ) • derS a L f).toLp 2 μ‖ ≤ K * t ^ 2 := by
  obtain ⟨k, C, hC0, hC⟩ := SchwartzMap.norm_toLp_le_seminorm ℂ ℂ 2 μ
  choose K hK using fun p : ℕ × ℕ => seminorm_heisS_sub_le a L c f p.1 p.2
  refine ⟨C * ∑ p ∈ Finset.Iic (k, 0), |K p|, fun t ht => ?_⟩
  refine (hC _).trans ?_
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hC0
  rw [Finset.sum_mul]
  refine Seminorm.finset_sup_apply_le (Finset.sum_nonneg fun _ _ => by positivity) fun p hp => ?_
  refine ((hK p t ht).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (sq_nonneg t))).trans ?_
  exact Finset.single_le_sum (f := fun q => |K q| * t ^ 2) (fun _ _ => by positivity) hp

theorem norm_toLp_two (μ : Measure V) [μ.HasTemperateGrowth] (u : 𝓢(V, ℂ)) :
    ‖u.toLp 2 μ‖ = Real.sqrt (∫ x, ‖u x‖ ^ 2 ∂μ) := by
  rw [SchwartzMap.norm_toLp' (by norm_num) (by norm_num), ENNReal.toReal_ofNat]
  simp only [Real.rpow_two]
  rw [Real.sqrt_eq_rpow, one_div]

theorem map_dHeis_of_isometry : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (β : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (T : SchwartzMap V ℂ →ₗ[ℂ] SchwartzMap V ℂ), (∀ f, ∫ x, ‖T f x‖ ^ 2 ∂μ = ∫ x, ‖f x‖ ^ 2 ∂μ) →
    ∀ w w' : V × V, (∀ (s : ℝ) (f g : SchwartzMap V ℂ), ⇑g = GlobalTheory.GaussLine.heisFun β (s • w).1 (s • w).2 ⇑f →
      ⇑(T g) = GlobalTheory.GaussLine.heisFun β (s • w').1 (s • w').2 ⇑(T f)) →
    ∀ f g : SchwartzMap V ℂ, (∀ x, g x = GlobalTheory.GaussLine.dHeis β w ⇑f x) →
    ∀ x, T g x = GlobalTheory.GaussLine.dHeis β w' ⇑(T f) x := by
  intro V _ _ _ _ _ μ _ β T hT w w' hw f g hg x
  haveI : μ.HasTemperateGrowth := MeasureTheory.Measure.IsAddHaarMeasure.instHasTemperateGrowth
  let Lf : V × V → (V →L[ℝ] ℝ) := fun p => LinearMap.toContinuousLinearMap (β.flip p.2)
  have hLf : ∀ p y, Lf p y = β y p.2 := fun p y => rfl
  have hheis : ∀ (p : V × V) (F : 𝓢(V, ℂ)) (t : ℝ),
      ⇑(heisS p.1 (Lf p) (β p.1 p.2 / 2) t F) = GlobalTheory.GaussLine.heisFun β (t • p).1 (t • p).2 ⇑F := by
    intro p F t
    funext y
    rw [heisS_apply, GlobalTheory.GaussLine.heisFun_apply, hLf, Prod.smul_fst, Prod.smul_snd]
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    congr 3
    ring_nf
  have hder : ∀ (p : V × V) (F : 𝓢(V, ℂ)) y, derS p.1 (Lf p) F y = GlobalTheory.GaussLine.dHeis β p ⇑F y := by
    intro p F y
    rw [derS_apply, GlobalTheory.GaussLine.dHeis, hLf]
  have hgS : g = derS w.1 (Lf w) f := by
    ext y
    rw [hg, hder]
  set G := derS w'.1 (Lf w') (T f) with hG
  set c := β w.1 w.2 / 2
  set c' := β w'.1 w'.2 / 2
  have hHT : ∀ t : ℝ, T (heisS w.1 (Lf w) c t f) = heisS w'.1 (Lf w') c' t (T f) := fun t =>
    DFunLike.coe_injective ((hw t f _ (hheis w f t)).trans (hheis w' (T f) t).symm)
  obtain ⟨K, hK⟩ := toLp_heisS_sub_le μ w.1 (Lf w) c f
  obtain ⟨K', hK'⟩ := toLp_heisS_sub_le μ w'.1 (Lf w') c' (T f)
  set ℓ := SchwartzMap.toLpCLM ℂ ℂ 2 μ with hℓ
  have hiso : ∀ u, ‖ℓ (T u)‖ = ‖ℓ u‖ := by
    intro u
    rw [hℓ, SchwartzMap.toLpCLM_apply, SchwartzMap.toLpCLM_apply, norm_toLp_two, norm_toLp_two, hT]
  have key : ∀ t : ℝ, 0 < t → t ≤ 1 → ‖ℓ (T g - G)‖ ≤ (K + K') * t := by
    intro t ht0 ht1
    have hta : |t| ≤ 1 := by rw [abs_of_pos ht0]; exact ht1
    have e1 : (t : ℂ) • (T g - G) = (heisS w'.1 (Lf w') c' t (T f) - T f - (t : ℂ) • G) -
        T (heisS w.1 (Lf w) c t f - f - (t : ℂ) • g) := by
      rw [map_sub, map_sub, map_smul, hHT, smul_sub]
      abel
    have h1 : ‖ℓ ((t : ℂ) • (T g - G))‖ = t * ‖ℓ (T g - G)‖ := by
      rw [map_smul, norm_smul, Complex.norm_real, Real.norm_of_nonneg ht0.le]
    have h2 : ‖ℓ ((t : ℂ) • (T g - G))‖ ≤ K' * t ^ 2 + K * t ^ 2 := by
      rw [e1, map_sub]
      refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
      · have := hK' t hta
        rw [hℓ, SchwartzMap.toLpCLM_apply]
        exact this
      · rw [hiso, hgS, hℓ, SchwartzMap.toLpCLM_apply]
        exact hK t hta
    rw [h1] at h2
    have h3 : t * ‖ℓ (T g - G)‖ ≤ t * ((K + K') * t) := by nlinarith
    exact le_of_mul_le_mul_left h3 ht0
  have ha : ‖ℓ (T g - G)‖ = 0 := by
    by_contra hne
    have hpos : 0 < ‖ℓ (T g - G)‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
    set a := ‖ℓ (T g - G)‖
    set M := |K + K'| + 1 with hMdef
    have hM : 0 < M := by positivity
    set t := min 1 (a / (2 * M)) with htdef
    have ht0 : 0 < t := lt_min one_pos (by positivity)
    have h1 := key t ht0 (min_le_left _ _)
    have h2 : t ≤ a / (2 * M) := min_le_right _ _
    have h3 : (K + K') * t ≤ M * t := mul_le_mul_of_nonneg_right ((le_abs_self _).trans (by linarith)) ht0.le
    have h4 : M * t ≤ M * (a / (2 * M)) := mul_le_mul_of_nonneg_left h2 hM.le
    have h5 : M * (a / (2 * M)) = a / 2 := by field_simp
    linarith
  have h0 : (T g - G).toLp 2 μ = (0 : 𝓢(V, ℂ)).toLp 2 μ := by
    have := norm_eq_zero.1 ha
    rw [hℓ, SchwartzMap.toLpCLM_apply] at this
    rw [this]
    exact ((map_zero ℓ).symm.trans (SchwartzMap.toLpCLM_apply))
  have h00 : T g - G = 0 := SchwartzMap.injective_toLp 2 μ h0
  have := congrArg (fun u : 𝓢(V, ℂ) => u x) (sub_eq_zero.1 h00)
  rw [this, hG, hder]

end L2

end GlobalTheory.HeisenbergL2
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergQuotientOpSumVacuumCommensurableSelfDu
section
open Matrix Formalism.UG GlobalTheory.Hk3 GlobalTheory.FinWeil GlobalTheory.SphTheta ValuativeRel Classical
open GlobalTheory.LFun (HasSatU IsSatVecU heckeVec)
open GlobalTheory.LGrp (bcParam extProd)
open GlobalTheory.WeilM (UG IsQuad Darboux symp sbClass SB IsWeilB IsWeilPair TestClass schr dbl diagCols)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlace (str chi IsUnramAdd)
open scoped TensorProduct

namespace GlobalTheory.SphTheta

theorem sumOp_vec_zero {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M]
    (W : X → M →ₗ[ℂ] M) (A B : Submodule R X) : sumOp W A B 0 = 0 := by
  unfold sumOp; simp

theorem form_translate_vacuum {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M]
    {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M} (h : IsHeis σ w γ W) {Λ : Submodule R X}
    (hΛ : SelfDual γ Λ) {s : M} (hs : Fixes W Λ s) (e : M →ₗ[ℂ] ℂ) (he : ∀ a ∈ Λ, ∀ v, e (W a v) = e v) (x : X) :
    e (W x s) = if x ∈ Λ then e s else 0 := by
  split_ifs with hx
  · rw [hs x hx]
  · obtain ⟨a, ha, hne⟩ : ∃ a ∈ Λ, γ x a ≠ 1 := by
      by_contra hc
      push_neg at hc
      exact hx ((hΛ x).2 hc)
    have h1 : e (W x s) = γ a x * e (W x s) := by
      conv_lhs => rw [← he a ha (W x s)]
      rw [h.comm a x s, hs a ha, map_smul, smul_eq_mul]
    have h2 : γ a x ≠ 1 := by
      rw [h.swap x a]
      intro h3
      exact hne (inv_eq_one.1 h3)
    have h3 : (1 - γ a x) * e (W x s) = 0 := by rw [sub_mul, one_mul, ← h1, sub_self]
    exact (mul_eq_zero.1 h3).resolve_left (sub_ne_zero.2 (Ne.symm h2))

theorem sumOp_vacuum_lift : ∀ {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}, IsHeis σ w γ W → ∀ Λ : Submodule R X, SelfDual γ Λ → ∀ s : M, s ≠ 0 → Fixes W Λ s → Submodule.span ℂ (Set.range fun x => W x s) = ⊤ → ∀ Λ' : Submodule R X, SelfDual γ Λ' → idx Λ Λ' ≠ 0 → (sumOp W Λ Λ' s ≠ 0 ∧ Fixes W Λ' (sumOp W Λ Λ' s) ∧ Submodule.span ℂ (Set.range fun x => W x (sumOp W Λ Λ' s)) = ⊤) ∧ ∀ e : M →ₗ[ℂ] ℂ, e s = 1 → (∀ a ∈ Λ, ∀ v, e (W a v) = e v) → ∀ v, Fixes W Λ' v → v = e v • sumOp W Λ Λ' s := by
  intro R X M _ _ _ _ _ σ w γ W h Λ hΛ s hs0 hs hspan Λ' hΛ' hidx
  obtain ⟨hidx', hss⟩ := sumOp_sumOp_eq_idx_smul h Λ Λ' hΛ hΛ' hidx
  obtain ⟨⟨n, f, hf, ht⟩, hfix, -⟩ := (sumOp_transversal h Λ Λ' hΛ').2.1 hidx
  have hs'fix : Fixes W Λ' (sumOp W Λ Λ' s) := hfix s hs
  have hback := hss s hs
  have hidxC : (idx Λ Λ' : ℂ) ≠ 0 := by exact_mod_cast hidx
  have hne : sumOp W Λ Λ' s ≠ 0 := by
    intro h0
    rw [h0, sumOp_vec_zero] at hback
    exact hs0 ((smul_eq_zero.1 hback.symm).resolve_left hidxC)
  have hidx2 : idx Λ' Λ ≠ 0 := by rw [hidx']; exact hidx
  obtain ⟨⟨m, g, hg, hgt⟩, -, -⟩ := (sumOp_transversal h Λ' Λ hΛ).2.1 hidx2
  have hsum := ((sumOp_transversal h Λ' Λ hΛ).1 _ hs'fix (Fin m) g hg hgt).1
  have hsE : s = ((idx Λ Λ' : ℂ))⁻¹ • ∑ i, W (g i) (sumOp W Λ Λ' s) := by
    rw [← hsum, hback, smul_smul, inv_mul_cancel₀ hidxC, one_smul]
  have hmem : ∀ x, W x s ∈ Submodule.span ℂ (Set.range fun y => W y (sumOp W Λ Λ' s)) := by
    intro x
    rw [congrArg (W x) hsE, map_smul, map_sum]
    refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun i _ => ?_)
    rw [h.comp]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
  have hspan' : Submodule.span ℂ (Set.range fun y => W y (sumOp W Λ Λ' s)) = ⊤ := by
    rw [eq_top_iff, ← hspan, Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    exact hmem x
  refine ⟨⟨hne, hs'fix, hspan'⟩, fun e he1 he v hv => ?_⟩
  obtain ⟨c, rfl⟩ := GlobalTheory.T.heisenbergVacuum_unique_of_selfDual h Λ' hΛ' _ hne hs'fix hspan' v hv
  have hes' : e (sumOp W Λ Λ' s) = 1 := by
    rw [((sumOp_transversal h Λ Λ' hΛ').1 s hs (Fin n) f hf ht).1, map_sum]
    simp only [form_translate_vacuum h hΛ hs e he, he1]
    obtain ⟨i0, hi0, huniq⟩ := ht 0 Λ'.zero_mem
    rw [Finset.sum_eq_single i0]
    · rw [if_pos (by simpa using hi0)]
    · intro j _ hj
      rw [if_neg]
      intro hjΛ
      exact hj (huniq j (by simpa using hjΛ))
    · simp
  rw [map_smul, hes', smul_eq_mul, mul_one]

end GlobalTheory.SphTheta
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.InnerEqZeroOfMemRangeAdjoint
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjScalar

theorem ker_le_span_of_rel {K X Y H W : Type} [Field K] [AddCommGroup X] [Module K X] [FiniteDimensional K X] [AddCommGroup Y]
    [Module K Y] [AddCommGroup H] [Module ℂ H] [AddCommGroup W] [Module ℂ W] (σ : K →+* ℂ) (j : X →ₛₗ[σ] H)
    (jW : Y →ₛₗ[σ] W) (T : H →ₗ[ℂ] W) (Rel : X → Y → Prop) (hex : ∀ x, ∃ y, Rel x y)
    (hsp : Submodule.span ℂ (Set.range j) = ⊤)
    (hind : ∀ (n : ℕ) (b : Fin n → Y), LinearIndependent K b → LinearIndependent ℂ fun k => jW (b k))
    (hT : ∀ x y, Rel x y → jW y = T (j x)) :
    LinearMap.ker T ≤ Submodule.span ℂ (j '' {u | Rel u 0}) := by
  have hinj : Function.Injective jW := by
    refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
    by_contra h0
    exact (hind 1 (fun _ => x) (linearIndependent_unique_iff.2 h0)).ne_zero 0 hx
  choose f hf using hex
  have e : ∀ x, jW (f x) = T (j x) := fun x => hT x _ (hf x)
  let θ : X →ₗ[K] Y :=
    { toFun := f
      map_add' := fun x y => hinj (by rw [map_add, e, e, e, map_add, map_add])
      map_smul' := fun a x => hinj (by rw [RingHom.id_apply, map_smulₛₗ, e, e, map_smulₛₗ, map_smul]) }
  refine (GlobalTheory.ker_le_span_image_ker_of_semilinear K X Y H W σ θ j jW T hsp hind fun x => (e x).symm).trans
    (Submodule.span_mono (Set.image_mono fun u hu => ?_))
  have h0 : f u = 0 := hu
  exact h0 ▸ hf u

theorem mem_orthogonal_of_le_span {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {N : Submodule ℂ H} {s : Set H}
    (h : N ≤ Submodule.span ℂ s) {v : H} (hv : ∀ u ∈ s, ⟪v, u⟫_ℂ = 0) : v ∈ Nᗮ := by
  refine Submodule.orthogonal_le h ((Submodule.mem_orthogonal' _ _).2 fun u hu => ?_)
  induction hu using Submodule.span_induction with
  | mem u hu => exact hv u hu
  | zero => exact inner_zero_right _
  | add u u' _ _ h h' => rw [inner_add_right, h, h', add_zero]
  | smul a u _ h => rw [inner_smul_right, h, mul_zero]

theorem toF_mem {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 : Type}
    (B : BlockDat K G Pl0) (ℓ : Lvl K G) (Z : Submodule K B.S.Forms) (y : Fin (B.dZ ℓ Z) → K) : B.toF ℓ Z y ∈ Z := by
  obtain ⟨f, hf, e⟩ : (B.zE ℓ Z).mulVec y ∈ B.Z0 ℓ Z := (subspace_image_spec _ _ _).2.le ⟨y, rfl⟩
  have : B.toF ℓ Z y = f := (congrArg B.S.basis.equivFun.symm e.symm).trans (B.S.basis.equivFun.symm_apply_apply f)
  exact this ▸ hf

theorem inner_eq_zero_of_mem_range_adjoint {H W : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] (T : H →ₗ[ℂ] W) {a b : H}
    (ha : a ∈ LinearMap.range (LinearMap.adjoint T)) (hb : T b = 0) : ⟪a, b⟫_ℂ = 0 := by
  obtain ⟨w, rfl⟩ := ha
  rw [LinearMap.adjoint_inner_left, hb, inner_zero_right]

theorem mem_orthogonal_of_rel {K X Y H W : Type} [Field K] [AddCommGroup X] [Module K X] [FiniteDimensional K X] [AddCommGroup Y]
    [Module K Y] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup W] [InnerProductSpace ℂ W] (σ : K →+* ℂ)
    (j : X →ₛₗ[σ] H) (jW : Y →ₛₗ[σ] W) (th : H →ₗ[ℂ] W) (U : W ≃ₗᵢ[ℂ] W) (κ : ℂ) (g : W →ₗ[ℂ] W) (Rel : X → Y → Prop)
    (hex : ∀ x, ∃! y, Rel x y) (hsp : Submodule.span ℂ (Set.range j) = ⊤)
    (hind : ∀ (n : ℕ) (b : Fin n → Y), LinearIndependent K b → LinearIndependent ℂ fun k => jW (b k))
    (hT : ∀ x y, Rel x y → U (jW y) = κ • g (th (j x))) {v : H} (hv : ∀ u, Rel u 0 → ⟪v, j u⟫_ℂ = 0) :
    v ∈ (LinearMap.ker th)ᗮ := by
  have hk := ker_le_span_of_rel σ j jW ((U.symm.toLinearEquiv.toLinearMap ∘ₗ (κ • g)) ∘ₗ th) Rel (fun x => (hex x).exists) hsp
    hind (fun x y h => U.toLinearEquiv.eq_symm_apply.2 (hT x y h))
  refine mem_orthogonal_of_le_span ((LinearMap.ker_le_ker_comp _ _).trans hk) ?_
  rintro _ ⟨u, hu, rfl⟩
  exact hv u hu

section

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks]
  [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

theorem csum_eq_zero_of_adjoint (h1 : R.models_HV) (h2 : R.models_jV) (i : Fin D.R.m) (t : T0) {f g : A.fam.amb.FL i t}
    (hf : R.jV i t f ∈ LinearMap.range (LinearMap.adjoint (R.thG i t))) (hg : R.thG i t (R.jV i t g) = 0) :
    (A.fam.L i t).S.csum f.1 g.1 = 0 := by
  have h3 : inner ℂ (R.jV i t f) (R.jV i t g) = D.what₂.embLL ((A.fam.L i t).S.csum f.1 g.1) := by
    refine ((h1 i t).2.2 (R.jV i t f) (R.jV i t g)).trans ?_
    refine (congrArg₂ (Bridge.adInner (Bridge.ratF (Vc D i)) (levEnv _ (R.βV i) (R.datVt i t)).J (R.B.L i t).pres.y)
      (h2 i t f) (h2 i t g)).trans ?_
    exact GlobalTheory.PresBasic.isom (R.B.L i t).pres f g
  exact (map_eq_zero _).1 (h3.symm.trans (inner_eq_zero_of_mem_range_adjoint _ hf hg))

end

set_option maxHeartbeats 1600000 in

theorem conjForms_mem_orthogonal_ker : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.IsModels → R.LUnif → ∀ gramR c0R c0L, GlobalTheory.GalLift.Comparison₂ R gramR c0R c0L → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (c : CoefA (Vc D i)) (c₁ : VsV D i D.what₂.LL →ₛₗ[σ] c.W) (H : HMod (Bridge.Gf (Vc D i) → c.W)) (j : A.fam.amb.FL i A.μ0 →ₛₗ[σ] H.H), ∀ (μ' η' : (AE D)ˣ →* Circle) (th : H.H →ₗ[ℂ] (R.HW i σ).H), ∀ ph : ℂ, ph ≠ 0 → (∀ x, ∃! y, GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.IsRatLift R i ph x y) → GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.ConjAt R i σ ph (c0L i) → GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.IsConjDatum R i σ (c0L i) μ' η' c c₁ H j th → ∀ (ℓ : Lvl D.what₂.LL G) (Z : Submodule D.what₂.LL (A.fam.L i A.μ0).S.Forms), Formalism.DivisionValues.IsRatHerm (Formalism.DivisionValues.cmMax D.what₂.LL) ((A.fam.L i A.μ0).HZ ℓ Z) ((A.fam.L i A.μ0).XQ ℓ Z) → (∀ a k, (A.fam.L i A.μ0).fE ℓ Z a k ∈ Formalism.DivisionValues.cmMax D.what₂.LL) → (∀ z ∈ Z, R.jV i A.μ0 z ∈ LinearMap.range (LinearMap.adjoint (R.thG i A.μ0))) → ∀ x, j ((A.fam.L i A.μ0).toF ℓ Z x) ∈ (LinearMap.ker th)ᗮ := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R hM hU gramR c0R c0L hT i σ c c₁ H j μ' η' th ph hph hex hC hD ℓ Z hH hE hZ x
  obtain ⟨-, -, u, U, z, ζ, -, -, -, hall⟩ := hC
  obtain ⟨-, κ, -, hκ⟩ := hall μ' η' c c₁ H j th hD
  have hsp := GlobalTheory.ConjSpan.span_conjForms R hM.jV gramR c0R c0L hT i σ c c₁ H j hD.2.2.1
  have : FiniteDimensional D.what₂.LL (A.fam.amb.FL i A.μ0) := Module.Finite.of_basis (A.fam.L i A.μ0).S.basis
  refine mem_orthogonal_of_rel σ j ((R.FW i).j σ) th U κ (R.gW i σ z) (GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.IsRatLift R i ph) hex hsp (hU i σ).1
    hκ fun v hv => ?_
  have h0 : R.thG i A.μ0 (R.jV i A.μ0 v) = 0 :=
    (smul_eq_zero.1 ((map_zero _).symm.trans hv).symm).resolve_left hph
  refine (GlobalTheory.LiftLower.inner_conjForms_eq_csumAt R hM.jV gramR c0R c0L hT i σ c c₁ H j hD.2.2.1 _ v).trans ?_
  exact (GlobalTheory.Proof.ConjugateTransposeMajorant.majAt_eq_csumAt (A.fam.L i A.μ0) ℓ Z hH hE).2 v
    (fun y => csum_eq_zero_of_adjoint hM.HV hM.jV i A.μ0 (hZ _ (toF_mem _ ℓ Z y)) h0) σ x

end GlobalTheory.ConjScalar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsFockVacuumAtReframeFunctionOnHoms
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open GlobalTheory.AdSpan.ReVec
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdSpan.ReVec.FockVac

variable {D : D7}

theorem continuous_reW (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V) : Continuous (reW S T b) := by
  unfold reW
  exact Continuous.matrix_mul continuous_id continuous_const

theorem compAt_frPinv {θ : InfFam D} (hθ : IsInfFam θ) (S : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V)
    (τ : D.what₂.Tau) : compAt θ τ ((frPinv S b).map (incA D)) = (frPinv S b).map (tauE D τ) := by
  unfold compAt
  rw [Matrix.map_map]
  congr 1
  funext e
  exact GlobalTheory.FockCompare.comp_incA hθ τ e

theorem lineAt_reW {θ : InfFam D} (hθ : IsInfFam θ) (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V)
    (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (t : ℝ) :
    reW S T b (lineAt θ τ z t) = lineAt θ τ (z * (frPinv S b).map (tauE D τ)) t := by
  have hL := GlobalTheory.OrientedHeis.isLineAt_lineAt hθ τ z
  let L : ℝ →+ WO S T := (reWHom S T b).comp (lineAt θ τ z)
  have hL' : IsLineAt θ τ (z * (frPinv S b).map (tauE D τ)) L := by
    refine ⟨(continuous_reW S T b).comp hL.1, fun t => ?_, fun t τ' => ?_⟩
    · show (reW S T b (lineAt θ τ z t)).map (finPart D) = 0
      unfold reW
      rw [Matrix.map_mul, hL.2.1, Matrix.zero_mul]
    · show compAt θ τ' (reW S T b (lineAt θ τ z t)) = _
      unfold reW
      rw [GlobalTheory.OrientedHeis.compAt_mul, hL.2.2, compAt_frPinv hθ]
      split_ifs with h
      · subst h
        rw [Matrix.smul_mul]
      · rw [Matrix.zero_mul]
  rw [GlobalTheory.RealLineAt.lineAt_unique D θ hθ _ _ τ _ _ _ (GlobalTheory.OrientedHeis.isLineAt_lineAt hθ τ _) hL']
  rfl

theorem lineAt_reW' {θ : InfFam D} (hθ : IsInfFam θ) (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V)
    (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin (reS S b).rank) ℂ) (t : ℝ) :
    reW S T b (lineAt θ τ z t) =
      lineAt θ τ (HMul.hMul (α := Matrix (Fin T.rank) (Fin S.rank) ℂ) z ((frPinv S b).map (tauE D τ))) t :=
  lineAt_reW hθ S T b τ z t

theorem dRho_reF (ψ : AddChar (AF D.host.F) ℂ) {θ : InfFam D} (hθ : IsInfFam θ) (S T : HSp D)
    (b : Module.Basis (Fin S.rank) D.host.E S.V)
    (hs : ∀ x y : WO (reS S b) T, symplO (reS S b) T x y = symplO S T (reW S T b x) (reW S T b y))
    (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin (reS S b).rank) ℂ) (f : WO S T → ℂ) :
    Formalism.IndefR.Datum.dRho (heisO ψ (reS S b) T) θ τ z (reF S T b f) =
      reF S T b (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ
        (HMul.hMul (α := Matrix (Fin T.rank) (Fin S.rank) ℂ) z ((frPinv S b).map (tauE D τ))) f) := by
  funext x
  rw [reF_apply]
  unfold Formalism.IndefR.Datum.dRho
  congr 1
  funext t
  rw [heisO_reF S T b ψ hs, reF_apply, lineAt_reW' hθ]

theorem isFockVacAt_reF : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D)
    (b : Module.Basis (Fin S.rank) D.host.E S.V), IsInfFam θ →
    (∀ x y : WO (reS S b) T, symplO (reS S b) T x y = symplO S T (reW S T b x) (reW S T b y)) →
    ∀ (τ : D.what₂.Tau) (sT : Matrix (Fin T.rank) (Fin T.rank) ℂ) (f : WO S T → ℂ),
      IsFockVacAt (heisO ψ S T) θ τ (cplxO 1 sT) f → IsFockVacAt (heisO ψ (reS S b) T) θ τ (cplxO 1 sT) (reF S T b f) := by
  intro D ψ θ S T b hθ hs τ sT f hf z
  let P' : Matrix (Fin S.rank) (Fin S.rank) ℂ := (frPinv S b).map (tauE D τ)
  let z' : Matrix (Fin T.rank) (Fin S.rank) ℂ := z
  have hJ : HMul.hMul (α := Matrix (Fin T.rank) (Fin S.rank) ℂ) (cplxO 1 sT z) P' = cplxO 1 sT (z' * P') := by
    show Complex.I • (sT * z' * 1) * P' = Complex.I • (sT * (z' * P') * 1)
    rw [Matrix.mul_one, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_assoc]
  funext x
  have h0 : Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ (z' * P') f (reW S T b x) +
      Complex.I • Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ (cplxO 1 sT (z' * P')) f (reW S T b x) = 0 :=
    congrFun (hf (z' * P')) (reW S T b x)
  rw [← hJ] at h0
  have e1 := congrFun (dRho_reF ψ hθ S T b hs τ z f) x
  have e2 := congrFun (dRho_reF ψ hθ S T b hs τ (cplxO 1 sT z) f) x
  refine (congrArg₂ (fun a c : ℂ => a + Complex.I • c) e1 e2).trans ?_
  exact h0

end GlobalTheory.AdSpan.ReVec.FockVac

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.JordanHolderMultiplicityNormalizedBorelJacquetUnStatement
section
open GlobalTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SmGL.Exponents ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jordanHolderMultiplicity_normalizedBorelJacquet_unramified : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V), IsSmooth π → ∀ θ : (Fin n → kˣ) →* ℂˣ, (∀ t ∈ torusO k (Fin n), θ t = 1) → jhMult (ofChar θ) (jacB π) = expMult π (θ * (deltaHalf k fun _ : Fin n => Unit).comp (leviTorus k (Fin n)).toMonoidHom) := by
  first | exact @GlobalTheory.SmGL.UnramFixed.jhMult_jacB_eq_expMult | exact GlobalTheory.SmGL.UnramFixed.jhMult_jacB_eq_expMult | (intros; apply GlobalTheory.SmGL.UnramFixed.jhMult_jacB_eq_expMult <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.QuadraticPowerCharacterSplitPlacesValuesInverseStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.PRep GlobalTheory.AdelicU GlobalTheory.LFun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quadraticPowerCharacter_splitPlaces_values_inverse : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (μ : (TensorProduct F (AF F) E)ˣ →* Circle) (b : ℕ), ResEta F E μ b → ∀ (w w' : HeightOneSpectrum (𝓞 E)), w.under (𝓞 F) = w'.under (𝓞 F) → w ≠ w' → UnrAt μ w → UnrAt μ w' → val μ w * val μ w' = 1 := by
  first | exact @GlobalTheory.LFun.SplitVal.val_mul_val_eq_one | exact GlobalTheory.LFun.SplitVal.val_mul_val_eq_one | (intros; apply GlobalTheory.LFun.SplitVal.val_mul_val_eq_one <;> assumption)
end

