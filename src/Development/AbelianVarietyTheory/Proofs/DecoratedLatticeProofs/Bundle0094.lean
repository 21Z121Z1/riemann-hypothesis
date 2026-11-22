import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HermCoord
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0078
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0253
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueSelfDualMeasuresFinitePlace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0080
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothVectorsModerateGrowthSmoothFrechetRep
import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0163
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0360

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualProdIff
section
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal
open GlobalTheory.SWC

noncomputable section

namespace GlobalTheory.HermSD

end GlobalTheory.HermSD

namespace GlobalTheory.HermSD

theorem eq_of_test_haar {V : Type} [AddCommGroup V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [LocallyCompactSpace V] [SecondCountableTopology V]
    [MeasurableSpace V] [BorelSpace V] {κ P : Measure V} {χ : V → V → ℂ}
    (hκ : SelfDual κ χ) (hP : P.IsAddHaarMeasure) (Φ : V → ℂ) (hc : Continuous Φ)
    (hs : HasCompactSupport Φ) (hI : Integrable (fun y => ∫ x, Φ x * χ x y ∂P) P) (z : V)
    (h1 : ∫ y, (∫ x, Φ x * χ x y ∂P) * χ y z ∂P = Φ (-z)) (hz : Φ (-z) ≠ 0) : κ = P := by
  have := hκ.1
  have e : κ = Measure.addHaarScalarFactor κ P • P := Measure.isAddLeftInvariant_eq_smul κ P
  set c : NNReal := Measure.addHaarScalarFactor κ P with hcdef
  have hT : ∀ y, ∫ x, Φ x * χ x y ∂κ = (c : ℂ) * ∫ x, Φ x * χ x y ∂P := by
    intro y
    rw [e, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]
  have hI' : Integrable (fun y => ∫ x, Φ x * χ x y ∂κ) κ := by
    simp only [hT]
    rw [e]
    exact (hI.const_mul (c : ℂ)).smul_measure_nnreal
  have h2 := hκ.2 Φ hc hs hI' z
  simp only [hT] at h2
  rw [e, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul] at h2
  have h3 : ∫ y, ((c : ℂ) * ∫ x, Φ x * χ x y ∂P) * χ y z ∂P =
      (c : ℂ) * ∫ y, (∫ x, Φ x * χ x y ∂P) * χ y z ∂P := by
    rw [← integral_const_mul]
    exact integral_congr_ae (ae_of_all _ fun y => by ring)
  rw [h3, h1, ← mul_assoc] at h2
  have h4 : ((c : ℂ)) * (c : ℂ) = 1 := mul_right_cancel₀ hz (by rw [h2, one_mul])
  have h5 : c * c = 1 := by exact_mod_cast h4
  have h6 : c = 1 := by
    have : (c : ℝ) * c = 1 := by exact_mod_cast h5
    have h7 : (c : ℝ) = 1 := by nlinarith [c.coe_nonneg]
    exact_mod_cast h7
  rw [e, h6, one_smul]

end GlobalTheory.HermSD

namespace GlobalTheory.HermSD

end GlobalTheory.HermSD

namespace GlobalTheory.HermSD

theorem isHermND_one {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) :
    IsHermND σ (1 : Matrix (Fin 1) (Fin 1) E) := by
  refine ⟨fun i j => ?_, by simp⟩
  rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
  simp

end GlobalTheory.HermSD
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SmoothVecHeadOfDerivativeFamily
section
noncomputable section

open Filter Topology Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum GlobalTheory.TypeSum.SmoothFrechet
open scoped ContDiff

namespace GlobalTheory.FamSmooth

section Mat
variable {n : ℕ} {k : ℕ}

theorem ofFn_update_eq_set {M : Type} (f : Fin k → M) (i : Fin k) (a : M) :
    List.ofFn (Function.update f i a) = (List.ofFn f).set i a := by
  refine List.ext_getElem (by simp) fun j h1 h2 => ?_
  simp only [List.getElem_ofFn, List.getElem_set, Function.update_apply, Fin.ext_iff, eq_comm]

def facs (Xs : Fin k → Mx n) : List ((Fin k → ℝ) → Mx n) := List.ofFn fun i t => NormedSpace.exp (t i • Xs i)

theorem list_prod_mem {ε : Fin n → Bool} : ∀ l : List (Mx n), (∀ x ∈ l, x ∈ UJset ε) → l.prod ∈ UJset ε
  | [], _ => one_mem_UJ ε
  | x :: l, h => by
    rw [List.prod_cons]
    exact mul_mem_UJ (h x List.mem_cons_self) (list_prod_mem l fun y hy => h y (List.mem_cons_of_mem _ hy))

theorem contDiff_listProd (fs : List ((Fin k → ℝ) → Mx n)) :
    letI := Matrix.linftyOpNormedRing (n := Fin n) (α := ℂ)
    letI := Matrix.linftyOpNormedAlgebra (R := ℝ) (n := Fin n) (α := ℂ)
    (∀ f ∈ fs, ContDiff ℝ ∞ f) → ContDiff ℝ ∞ (fun t => (fs.map (· t)).prod) := by
  letI := Matrix.linftyOpNormedRing (n := Fin n) (α := ℂ)
  letI := Matrix.linftyOpNormedAlgebra (R := ℝ) (n := Fin n) (α := ℂ)
  induction fs with
  | nil => intro _; simpa using contDiff_const
  | cons f fs ih =>
    intro h
    simp only [List.map_cons, List.prod_cons]
    exact (h f List.mem_cons_self).mul (ih fun g hg => h g (List.mem_cons_of_mem _ hg))

theorem contDiff_facs (Xs : Fin k → Mx n) :
    letI := Matrix.linftyOpNormedRing (n := Fin n) (α := ℂ)
    letI := Matrix.linftyOpNormedAlgebra (R := ℝ) (n := Fin n) (α := ℂ)
    ∀ f ∈ facs Xs, ContDiff ℝ ∞ f := by
  letI := Matrix.linftyOpNormedRing (n := Fin n) (α := ℂ)
  letI := Matrix.linftyOpNormedAlgebra (R := ℝ) (n := Fin n) (α := ℂ)
  intro f hf
  obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hf
  have he : ContDiff ℝ ∞ (NormedSpace.exp : Mx n → Mx n) :=
    contDiff_iff_contDiffAt.2 fun x => (NormedSpace.exp_analytic (𝕂 := ℝ) x).contDiffAt
  exact he.comp ((contDiff_apply ℝ ℝ i).smul contDiff_const)

def ctL : Mx n →ₗ[ℝ] Mx n where
  toFun M := Mᴴ
  map_add' := conjTranspose_add
  map_smul' r M := by simp [conjTranspose_smul]

theorem contDiff_coef (ε : Fin n → Bool) (φ : Mx n →ₗ[ℝ] ℝ) (X : Mx n) (B : (Fin k → ℝ) → Mx n)
    (hB : letI := Matrix.linftyOpNormedRing (n := Fin n) (α := ℂ)
      letI := Matrix.linftyOpNormedAlgebra (R := ℝ) (n := Fin n) (α := ℂ)
      ContDiff ℝ ∞ B) (hU : ∀ t, B t ∈ UJset ε) :
    ContDiff ℝ ∞ fun t => φ ((B t)⁻¹ * X * B t) := by
  letI := Matrix.linftyOpNormedRing (n := Fin n) (α := ℂ)
  letI := Matrix.linftyOpNormedAlgebra (R := ℝ) (n := Fin n) (α := ℂ)
  have e : (fun t => φ ((B t)⁻¹ * X * B t)) = fun t => φ (Jm ε * ctL (B t) * Jm ε * X * B t) := by
    funext t; rw [inv_eq_UJ (hU t)]; rfl
  rw [e]
  have hc : ContDiff ℝ ∞ fun t => ctL (B t) := ((LinearMap.toContinuousLinearMap ctL).contDiff.comp hB :)
  exact (LinearMap.toContinuousLinearMap φ).contDiff.comp
    ((((contDiff_const.mul hc).mul contDiff_const).mul contDiff_const).mul hB)

end Mat

section Partials
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem continuous_cons_pair {k : ℕ} :
    Continuous (fun p : ℝ × (Fin k → ℝ) => (Fin.cons p.1 p.2 : Fin (k+1) → ℝ)) := by
  refine continuous_pi fun i => ?_
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa using continuous_fst
  · simp only [Fin.cons_succ]
    exact (continuous_apply j).comp continuous_snd

theorem hasFDerivAt_of_partials :
    ∀ (k : ℕ) (F : (Fin k → ℝ) → E) (d : Fin k → (Fin k → ℝ) → E),
      (∀ i t, HasDerivAt (fun s : ℝ => F (Function.update t i s)) (d i t) (t i)) →
      (∀ i, Continuous (d i)) →
      ∀ t, HasFDerivAt F (∑ i, (ContinuousLinearMap.proj i : (Fin k → ℝ) →L[ℝ] ℝ).smulRight (d i t)) t := by
  intro k
  induction k with
  | zero =>
    intro F d _ _ t
    simpa using hasFDerivAt_of_subsingleton F t
  | succ k ih =>
    intro F d hd hc t
    let f : ℝ → (Fin k → ℝ) → E := fun x y => F (Fin.cons x y)
    let f₁ : ℝ → (Fin k → ℝ) → ℝ →L[ℝ] E :=
      fun x y => (1 : ℝ →L[ℝ] ℝ).smulRight (d 0 (Fin.cons x y))
    let f₂ : ℝ → (Fin k → ℝ) → (Fin k → ℝ) →L[ℝ] E :=
      fun x y => ∑ j, (ContinuousLinearMap.proj j : (Fin k → ℝ) →L[ℝ] ℝ).smulRight
        (d j.succ (Fin.cons x y))
    have df₁ : ∀ v : ℝ × (Fin k → ℝ), HasFDerivAt (f · v.2) (↿f₁ v) v.1 := by
      intro v
      have h := hd 0 (Fin.cons v.1 v.2)
      simp only [Fin.update_cons_zero, Fin.cons_zero] at h
      exact h.hasFDerivAt
    have df₂ : ∀ v : ℝ × (Fin k → ℝ), HasFDerivAt (f v.1 ·) (↿f₂ v) v.2 := by
      intro v
      refine ih (fun y => F (Fin.cons v.1 y)) (fun j y => d j.succ (Fin.cons v.1 y)) ?_ ?_ v.2
      · intro j y
        have h := hd j.succ (Fin.cons v.1 y)
        simp only [Fin.cons_succ] at h
        refine h.congr_of_eventuallyEq (Eventually.of_forall fun s => ?_)
        simp [Fin.cons_update]
      · intro j
        exact (hc j.succ).comp (continuous_cons_pair.comp (continuous_const.prodMk continuous_id))
    have cf₁ : Continuous ↿f₁ :=
      (ContinuousLinearMap.smulRightL ℝ ℝ E (1 : ℝ →L[ℝ] ℝ)).continuous.comp
        ((hc 0).comp continuous_cons_pair)
    have cf₂ : Continuous ↿f₂ := by
      show Continuous fun p : ℝ × (Fin k → ℝ) => ∑ j, (ContinuousLinearMap.proj j : (Fin k → ℝ) →L[ℝ] ℝ).smulRight (d j.succ (Fin.cons p.1 p.2))
      refine continuous_finset_sum _ fun j _ => ?_
      exact (ContinuousLinearMap.smulRightL ℝ (Fin k → ℝ) E
        (ContinuousLinearMap.proj j)).continuous.comp ((hc j.succ).comp continuous_cons_pair)
    let ι : (Fin (k+1) → ℝ) →L[ℝ] ℝ × (Fin k → ℝ) :=
      (ContinuousLinearMap.proj 0).prod (ContinuousLinearMap.pi fun j => ContinuousLinearMap.proj j.succ)
    have key := hasStrictFDerivAt_uncurry_coprod (𝕜 := ℝ) (u := ι t) (f := f) (f₁ := f₁) (f₂ := f₂)
      (Eventually.of_forall df₁) (Eventually.of_forall df₂) cf₁.continuousAt cf₂.continuousAt
    have k2 := key.hasFDerivAt.comp t ι.hasFDerivAt
    have ht : (Fin.cons (t 0) (fun j => t j.succ) : Fin (k+1) → ℝ) = t := Fin.cons_self_tail t
    refine (k2.congr_of_eventuallyEq (Eventually.of_forall fun v => ?_)).congr_fderiv ?_
    · show F v = F (Fin.cons (v 0) (Fin.tail v))
      rw [Fin.cons_self_tail]
    · refine ContinuousLinearMap.ext fun v => ?_
      simp [ι, f₁, f₂, Function.HasUncurry.uncurry, Fin.sum_univ_succ, ht]

theorem contDiff_succ_of_partials {k : ℕ} (m : ℕ) (F : (Fin k → ℝ) → E) (d : Fin k → (Fin k → ℝ) → E)
    (hd : ∀ i t, HasDerivAt (fun s : ℝ => F (Function.update t i s)) (d i t) (t i))
    (hc : ∀ i, ContDiff ℝ m (d i)) : ContDiff ℝ (m + 1) F := by
  rw [contDiff_succ_iff_hasFDerivAt]
  refine ⟨fun t => ∑ i, (ContinuousLinearMap.proj i : (Fin k → ℝ) →L[ℝ] ℝ).smulRight (d i t), ?_,
    hasFDerivAt_of_partials k F d hd fun i => (hc i).continuous⟩
  exact ContDiff.sum fun i _ =>
    (ContinuousLinearMap.smulRightL ℝ (Fin k → ℝ) E (ContinuousLinearMap.proj i)).contDiff.comp (hc i)

end Partials

section Main

variable {n k : ℕ}

theorem modRep_of_isURepOn {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Mx n → (H →L[ℂ] H)} (hσ : IsURepOn (UJset ε) σ) : ModRep ε σ :=
  ⟨hσ.1.1, hσ.1.2, 1, 0, fun g hg => by
    rw [pow_zero, mul_one]
    exact ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by rw [hσ.2.1 g hg x, one_mul]⟩

theorem prod_update (Xs : Fin k → Mx n) (t : Fin k → ℝ) (i : Fin k) (s : ℝ) :
    ((facs Xs).map (· (Function.update t i s))).prod =
      (((facs Xs).map (· t)).take i).prod * NormedSpace.exp (s • Xs i) *
        (((facs Xs).drop (i + 1)).map (· t)).prod := by
  have e : (facs Xs).map (· (Function.update t i s)) =
      ((facs Xs).map (· t)).set i (NormedSpace.exp (s • Xs i)) := by
    rw [facs, List.map_ofFn, List.map_ofFn, ← ofFn_update_eq_set]
    congr 1
    funext j
    simp only [Function.comp_apply, Function.update_apply]
    split_ifs with hj
    · subst hj; rfl
    · rfl
  rw [e, List.prod_set, if_pos (by simp [facs]), List.map_drop]

theorem famSmooth : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ →
    ∀ v ∈ GlobalTheory.TypeSum.Fam ε σ, Formalism.L2.Theta.SmoothVec (GlobalTheory.SmoothGlob.lieSet ε) σ (v []) := by
  intro n ε H _ _ _ σ hσ v hv k Xs hX
  have h := modRep_of_isURepOn hσ
  obtain ⟨d, b, φ, hb⟩ := exists_frame ε
  have hmem : ∀ t, ∀ x ∈ (facs Xs).map (· t), x ∈ UJset ε := by
    intro t x hx
    obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hx
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hf
    exact exp_mem_UJ (hX i) (t i)
  have hmemD : ∀ (i : ℕ) t, ∀ x ∈ ((facs Xs).drop i).map (· t), x ∈ UJset ε := fun i t x hx =>
    hmem t x (by rw [List.map_drop] at hx; exact List.mem_of_mem_drop hx)
  have hmemT : ∀ (i : ℕ) t, ∀ x ∈ ((facs Xs).map (· t)).take i, x ∈ UJset ε := fun i t x hx =>
    hmem t x (List.mem_of_mem_take hx)
  let P : (Fin k → ℝ) → Mx n := fun t => ((facs Xs).map (· t)).prod
  have hPU : ∀ t, P t ∈ UJset ε := fun t => list_prod_mem _ (hmem t)
  have hPc : Continuous P := by
    letI := Matrix.linftyOpNormedRing (n := Fin n) (α := ℂ)
    letI := Matrix.linftyOpNormedAlgebra (R := ℝ) (n := Fin n) (α := ℂ)
    exact (contDiff_listProd _ (contDiff_facs Xs)).continuous
  let B : Fin k → (Fin k → ℝ) → Mx n := fun i t => (((facs Xs).drop (i + 1)).map (· t)).prod
  have hBU : ∀ i t, B i t ∈ UJset ε := fun i t => list_prod_mem _ (hmemD _ t)
  let c : Fin k → Fin d → (Fin k → ℝ) → ℝ := fun i j t => φ j ((B i t)⁻¹ * Xs i * B i t)
  have hc : ∀ i j, ContDiff ℝ ∞ (c i j) := fun i j => contDiff_coef ε (φ j) (Xs i) (B i)
    (contDiff_listProd _ fun f hf => contDiff_facs Xs f (List.mem_of_mem_drop hf)) (hBU i)
  let F : Fam ε σ → (Fin k → ℝ) → H := fun u t => σ (P t) (u.1 [])
  have hd : ∀ (u : Fam ε σ) i t, HasDerivAt (fun s : ℝ => F u (Function.update t i s))
      (∑ j, c i j t • F (der σ (b j) u) t) (t i) := by
    intro u i t
    have hA : (((facs Xs).map (· t)).take i).prod ∈ UJset ε := list_prod_mem _ (hmemT _ t)
    have hB := hBU i t
    let Y : lie (Jm ε) := ⟨Xs i, hX i⟩
    have e1 : ∀ s, F u (Function.update t i s) =
        σ (((facs Xs).map (· t)).take i).prod ((act h (exp_mem_UJ (hX i) s) (act h hB u)).1 []) := by
      intro s
      show σ (((facs Xs).map (· (Function.update t i s))).prod) (u.1 []) = _
      rw [prod_update, sigma_mul hσ (mul_mem_UJ hA (exp_mem_UJ (hX i) s)) hB, sigma_mul hσ hA (exp_mem_UJ (hX i) s)]
      rfl
    have h1 := ((σ (((facs Xs).map (· t)).take i).prod).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (t i)
      (hasDerivAt_act h Y [] (act h hB u) (t i))
    refine (h1.congr_of_eventuallyEq (Eventually.of_forall e1)).congr_deriv ?_
    have eP : P t = (((facs Xs).map (· t)).take i).prod * NormedSpace.exp (t i • Xs i) * B i t := by
      have := prod_update Xs t i (t i)
      rwa [Function.update_eq_self] at this
    show σ _ ((act h _ (der σ Y (act h hB u))).1 []) = _
    rw [der_act]
    have e2 := map_der_eq hb 1 (adInv hB Y) u []
    simp only [ContinuousLinearMap.one_apply] at e2
    show σ _ (σ (NormedSpace.exp (t i • Xs i)) (σ (B i t) ((der σ (adInv hB Y) u).1 []))) = _
    rw [e2, ← sigma_mul hσ hA (exp_mem_UJ (hX i) (t i)),
      ← sigma_mul hσ (mul_mem_UJ hA (exp_mem_UJ (hX i) (t i))) hB, ← eP, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact (σ (P t)).map_smul_of_tower _ _
  have key : ∀ m : ℕ, ∀ u : Fam ε σ, ContDiff ℝ m (F u) := by
    intro m
    induction m with
    | zero =>
      intro u
      rw [Nat.cast_zero, contDiff_zero]
      exact (hσ.2.2 (u.1 [])).comp_continuous hPc hPU
    | succ m ih =>
      intro u
      rw [Nat.cast_succ]
      exact contDiff_succ_of_partials m (F u) _ (hd u) fun i =>
        ContDiff.sum fun j _ => (contDiff_infty.1 (hc i j) m).smul (ih _)
  have eF : F ⟨v, hv⟩ = fun t => σ ((List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod) (v []) := by
    funext t
    simp [F, P, facs, List.map_ofFn, Function.comp_def]
  rw [← eF]
  exact contDiff_infty.2 fun m => key m ⟨v, hv⟩

end Main

end GlobalTheory.FamSmooth
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TensorWeylModuleMapsInjectiveOnPureSpan
section
open Formalism.BasicNotions Formalism.L2.Forms
open scoped TensorProduct

namespace GlobalTheory.TenInj

noncomputable def tenMap {ι : Type} [Fintype ι] {n : ℕ} {V : ι → Type} [∀ τ, AddCommGroup (V τ)] [∀ τ, Module ℂ (V τ)]
    (j : ∀ τ, V τ →ₗ[ℂ] MvPolynomial (Fin n × Fin n) ℂ) :
    (⨂[ℂ] τ, V τ) →ₗ[ℂ] MvPolynomial (ι × Fin n × Fin n) ℂ :=
  PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra ℂ ι (MvPolynomial (ι × Fin n × Fin n) ℂ)).compLinearMap
    (fun τ => (MvPolynomial.rename (Prod.mk τ)).toLinearMap ∘ₗ j τ))

theorem tenMap_tprod {ι : Type} [Fintype ι] {n : ℕ} {V : ι → Type} [∀ τ, AddCommGroup (V τ)] [∀ τ, Module ℂ (V τ)]
    (j : ∀ τ, V τ →ₗ[ℂ] MvPolynomial (Fin n × Fin n) ℂ) (x : ∀ τ, V τ) :
    tenMap j (PiTensorProduct.tprod ℂ x) = ten (fun τ => j τ (x τ)) := by
  unfold tenMap ten
  rw [PiTensorProduct.lift.tprod, MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply]
  rfl

theorem nfAll_zero_left {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n)
    (q : MvPolynomial (ι × Fin n × Fin n) ℂ) : nfAll lam 0 q = 0 := by
  have h := GlobalTheory.TenTypes.nfAll_smul_left lam 0 0 q
  simpa using h

theorem main : ∀ (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n) (V : ι → Type) [∀ τ, AddCommGroup (V τ)] [∀ τ, Module ℂ (V τ)] (j : ∀ τ, V τ →ₗ[ℂ] MvPolynomial (Fin n × Fin n) ℂ) (d : ι → ℕ) (b : ∀ τ, Module.Basis (Fin (d τ)) ℂ (V τ)), (∀ τ ξ, j τ ξ ∈ delSq ℂ n (lam τ)) → (∀ τ, ∀ p ∈ delSq ℂ n (lam τ), ∃ ξ, j τ ξ = p) → (∀ τ a a', normFock (lam τ) (j τ (b τ a)) (j τ (b τ a')) = if a = a' then 1 else 0) → ∃ Jt : (⨂[ℂ] τ, V τ) →ₗ[ℂ] MvPolynomial (ι × Fin n × Fin n) ℂ, Function.Injective Jt ∧ LinearMap.range Jt = CSpan lam ∧ ∀ x : (∀ τ, V τ), Jt (PiTensorProduct.tprod ℂ x) = ten (fun τ => j τ (x τ)) := by
  intro ι _ n lam V _ _ j d b hin hon hortho
  refine ⟨tenMap j, ?_, ?_, tenMap_tprod j⟩
  ·
    let B := Basis.piTensorProduct b
    have hB : ∀ i, B i = PiTensorProduct.tprod ℂ (fun τ => b τ (i τ)) := fun i => Basis.piTensorProduct_apply b i
    obtain ⟨hprod, -, -⟩ := GlobalTheory.FockTen.nfAll_ten ι n lam
    have hpair : ∀ i i', nfAll lam (tenMap j (B i)) (tenMap j (B i')) = if i = i' then 1 else 0 := by
      intro i i'
      rw [hB, hB, tenMap_tprod, tenMap_tprod, hprod]
      simp_rw [hortho]
      by_cases h : i = i'
      · subst h; simp
      · rw [if_neg h]
        obtain ⟨τ, hτ⟩ : ∃ τ, i τ ≠ i' τ := by
          by_contra hc; push_neg at hc; exact h (funext hc)
        exact Finset.prod_eq_zero (Finset.mem_univ τ) (if_neg hτ)
    have hcoord : ∀ i' x, nfAll lam (tenMap j x) (tenMap j (B i')) = B.coord i' x := by
      intro i'
      let L : (⨂[ℂ] τ, V τ) →ₗ[ℂ] ℂ :=
        { toFun := fun x => nfAll lam (tenMap j x) (tenMap j (B i'))
          map_add' := fun x y => by rw [map_add, GlobalTheory.TenTypes.nfAll_add_left]
          map_smul' := fun c x => by rw [map_smul, GlobalTheory.TenTypes.nfAll_smul_left]; rfl }
      have hL : L = B.coord i' := by
        refine B.ext fun i => ?_
        show nfAll lam (tenMap j (B i)) (tenMap j (B i')) = B.coord i' (B i)
        rw [hpair, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
      intro x
      exact LinearMap.congr_fun hL x
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    refine B.ext_elem fun i' => ?_
    rw [map_zero, Finsupp.zero_apply, ← Module.Basis.coord_apply, ← hcoord, hx, nfAll_zero_left]
  ·
    rw [LinearMap.range_eq_map, ← PiTensorProduct.span_tprod_eq_top, Submodule.map_span]
    unfold CSpan
    congr 1
    ext p
    constructor
    · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨fun τ => j τ (x τ), fun τ => hin τ _, tenMap_tprod j x⟩
    · rintro ⟨f, hf, rfl⟩
      choose ξ hξ using fun τ => hon τ (f τ) (hf τ)
      refine ⟨PiTensorProduct.tprod ℂ ξ, ⟨ξ, rfl⟩, ?_⟩
      rw [tenMap_tprod]
      congr 1
      funext τ
      exact hξ τ

end GlobalTheory.TenInj
end

