import Mathlib
import ReciprocityTheory.L2DbarEstimates.IsLocalHomeomorph
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCyclotomicExtensionQI
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0013
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0012
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0007
import ReciprocityTheory.Chebotarev.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0088
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0056

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousOnCosSq
section
set_option autoImplicit false

noncomputable section

open Set Matrix
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ComplexOrder

namespace GlobalTheory.LineCos

def hform (G : Matrix (Fin 2) (Fin 2) ℂ) (a b : Fin 2 → ℂ) : ℂ :=
  ∑ i, ∑ j, a i * starRingEnd ℂ (b j) * G i j

def lineVec (s : Bool) (x : ℂ) : Fin 2 → ℂ := if s then ![x, 1] else ![1, x]

def cosSq (s : Bool) (G : Matrix (Fin 2) (Fin 2) ℂ) (x : ℂ) : ℝ :=
  ‖hform G (lineVec s x) (Pi.single 0 1)‖ ^ 2 / ((hform G (lineVec s x) (lineVec s x)).re * (G 0 0).re)

def base {d : ℕ} (z : V (d + 1)) : Fin d → ℂ := fun i => z (Fin.castSucc i)

def fib {d : ℕ} (z : V (d + 1)) : ℂ := z (Fin.last d)

theorem hform_self (G : Matrix (Fin 2) (Fin 2) ℂ) (a : Fin 2 → ℂ) :
    hform G a a = star (starRingEnd ℂ ∘ a) ⬝ᵥ (G *ᵥ (starRingEnd ℂ ∘ a)) := by
  simp only [hform, dotProduct, mulVec, Fin.sum_univ_two, Function.comp_apply, Pi.star_apply, RCLike.star_def,
    Complex.conj_conj]
  ring

theorem re_hform_pos {G : Matrix (Fin 2) (Fin 2) ℂ} (hG : G.PosDef) {a : Fin 2 → ℂ} (ha : a ≠ 0) :
    0 < (hform G a a).re := by
  have hne : (starRingEnd ℂ ∘ a) ≠ 0 := fun h => ha (funext fun i => by
    simpa using congrFun h i)
  have := hG.dotProduct_mulVec_pos hne
  rw [hform_self]
  exact (Complex.pos_iff.1 this).1

theorem lineVec_ne_zero (s : Bool) (x : ℂ) : lineVec s x ≠ 0 := by
  intro h
  cases s
  · simpa [lineVec] using congrFun h 0
  · simpa [lineVec] using congrFun h 1

theorem re_corner_pos {G : Matrix (Fin 2) (Fin 2) ℂ} (hG : G.PosDef) : 0 < (G 0 0).re := by
  have := re_hform_pos hG (a := Pi.single 0 1) (by simp)
  simpa [hform, Fin.sum_univ_two, Pi.single_apply] using this

theorem continuousOn_cosSq {d : ℕ} {O : Set (V (d + 1))} {G : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ} (s : Bool)
    (hc : ContinuousOn (fun z => G (base z)) O) (hp : ∀ z ∈ O, (G (base z)).PosDef) :
    ContinuousOn (fun z => cosSq s (G (base z)) (fib z)) O := by
  have he : ∀ i j, ContinuousOn (fun z => G (base z) i j) O := fun i j =>
    (continuous_apply j).comp_continuousOn ((continuous_apply i).comp_continuousOn hc)
  have hx : Continuous (fun z : V (d + 1) => fib z) := by
    unfold fib
    fun_prop
  have hw : ∀ i, Continuous (fun z : V (d + 1) => lineVec s (fib z) i) := fun i => by
    cases s
    · fin_cases i
      · exact continuous_const
      · exact hx
    · fin_cases i
      · exact hx
      · exact continuous_const
  have hh : ∀ (b : V (d + 1) → Fin 2 → ℂ), (∀ j, Continuous fun z => b z j) →
      ContinuousOn (fun z => hform (G (base z)) (lineVec s (fib z)) (b z)) O := fun b hb => by
    unfold hform
    refine continuousOn_finset_sum _ fun i _ => continuousOn_finset_sum _ fun j _ => ?_
    exact (((hw i).mul ((Complex.continuous_conj).comp (hb j))).continuousOn).mul (he i j)
  have hn : ContinuousOn (fun z => ‖hform (G (base z)) (lineVec s (fib z)) (Pi.single (0 : Fin 2) (1 : ℂ))‖ ^ 2) O :=
    (hh (fun _ => Pi.single (0 : Fin 2) (1 : ℂ)) fun j => continuous_const).norm.pow 2
  have hd : ContinuousOn (fun z => (hform (G (base z)) (lineVec s (fib z)) (lineVec s (fib z))).re * (G (base z) 0 0).re) O :=
    (Complex.continuous_re.comp_continuousOn (hh (fun z => lineVec s (fib z)) hw)).mul (Complex.continuous_re.comp_continuousOn (he 0 0))
  have h0 : ∀ z ∈ O, (hform (G (base z)) (lineVec s (fib z)) (lineVec s (fib z))).re * (G (base z) 0 0).re ≠ 0 :=
    fun z hz => (mul_pos (re_hform_pos (hp z hz) (lineVec_ne_zero s _)) (re_corner_pos (hp z hz))).ne'
  exact hn.div hd h0

end GlobalTheory.LineCos
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousRestr
section
open IsDedekindDomain

namespace GlobalTheory.LKTrip

theorem AfP.continuous_restr (p : ℕ) : Continuous (AfP.restr p) :=
  RestrictedProduct.mapAlong_continuous (fun v : HeightOneSpectrum ℤ ↦ v.adicCompletion ℚ)
    (fun v : AwayP p ↦ v.1.adicCompletion ℚ) Subtype.val Subtype.val_injective.tendsto_cofinite
    (fun _ ↦ RingHom.id _) (Filter.Eventually.of_forall fun _ ↦ Set.mapsTo_id _)
    (fun _ ↦ continuous_id)

end GlobalTheory.LKTrip
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CotangentMapInjectiveOfSquarePresentationAtPointStatement
section
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cotangent_map_injective_of_square_presentation_at_point : ∀ (O B A σ : Type) [CommRing O] [IsDomain O] [CommRing B] [CommRing A] [Algebra O B] [Algebra O A] [Algebra B A] [IsScalarTower O B A] [Fintype σ] (ε : A →ₐ[O] O) (x : σ → A) (f : σ → MvPolynomial σ B) (c : O), c ≠ 0 → Function.Surjective (MvPolynomial.aeval x : MvPolynomial σ B →ₐ[B] A) → (∀ i, MvPolynomial.aeval x (f i) = 0) → RingHom.ker (MvPolynomial.aeval x : MvPolynomial σ B →ₐ[B] A) ≤ Ideal.span (Set.range f) ⊔ (RingHom.ker ε).comap (MvPolynomial.aeval x : MvPolynomial σ B →ₐ[B] A) * RingHom.ker (MvPolynomial.aeval x : MvPolynomial σ B →ₐ[B] A) → (∀ a ∈ RingHom.ker ε, c • a ∈ RingHom.ker ε ^ 2 ⊔ ((RingHom.ker ε).comap (algebraMap B A)).map (algebraMap B A)) → ∀ b : B, algebraMap B A b ∈ RingHom.ker ε ^ 2 → b ∈ ((RingHom.ker ε).comap (algebraMap B A)) ^ 2 := by
  first | exact @GlobalTheory.CotangentSquare.cotangent_map_injective_of_square_presentation | exact GlobalTheory.CotangentSquare.cotangent_map_injective_of_square_presentation | (intros; apply GlobalTheory.CotangentSquare.cotangent_map_injective_of_square_presentation <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CovolumeNumericalBoundsCollectStatement
section
open Real
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.covolume_numerical_bounds_collect : ∀ (CG CB f r Lb S N0 sz c₁ q ℓ lb dd : ℝ), 0 ≤ CG → 0 ≤ CB → 1 ≤ f → 1 ≤ r → 1 ≤ Lb → 0 ≤ S → 0 ≤ q → q ≤ r → 0 ≤ ℓ → ℓ ≤ 3 * Lb → |c₁| ≤ 9 * r * Lb → 0 ≤ N0 → N0 ≤ S + f * (4 * (f * r + 1) + 1) → 0 ≤ sz → sz ≤ (1 + r) * S + r * f * (4 * (f * r + 1) + 1) → lb ≤ CB * (f * r * Lb) ^ 2 → dd ≤ 391 / 2 * (f * r * Lb) ^ 2 → (f * r + 1) * (2 * (f * r) * Real.log (2 * Real.pi)) + ((|c₁| + q * ℓ) * N0 + lb + dd + 1) + CG * (f * r * Lb) ^ 2 * sz ≤ (11 * CG + CB + 500) * ((f * r * Lb) ^ 3 * S + (f * r * Lb) ^ 5) := by
  first | exact @GlobalTheory.covol_numerical_collect | exact GlobalTheory.covol_numerical_collect | (intros; apply GlobalTheory.covol_numerical_collect <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubicalFunctionOfHomomorphismStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cubical_function_of_homomorphism : ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (A : Type) [CommGroup A] (h : X → A), (∀ a b, h (a + b) = h a * h b) → ∃ k : X → A, (∀ a a' b : X, k (a + a' + b) * k a * k a' * k b = k (a + a') * k (a + b) * k (a' + b)) ∧ ∀ a, k (-a) = h a * k a := by
  first | exact @GlobalTheory.hom_eq_evenness_defect_of_cube | exact GlobalTheory.hom_eq_evenness_defect_of_cube | (intros; apply GlobalTheory.hom_eq_evenness_defect_of_cube <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CutoffPolynomialConjugationDerivMemShapeSpan
section
open MvPolynomial
open scoped ContDiff
open GlobalTheory.PsCo.Pc1

noncomputable section

namespace GlobalTheory.PsCo.Pc1.B

theorem sb_derivcut (H : ℝ → ℝ) (hH : IsCutFn H) : IsCutFn (deriv H) := by
  obtain ⟨hc, R, hR⟩ := hH
  refine ⟨(contDiff_infty_iff_deriv.1 hc).2, R + 1, fun x hx => ?_⟩
  have h : H =ᶠ[nhds x] fun _ => (0 : ℝ) := by
    filter_upwards [Ioi_mem_nhds (show R < x by linarith)] with y hy
    exact hR y (le_of_lt hy)
  rw [h.deriv_eq]
  simp

theorem sb_evrp {n : ℕ} (ε : Fin n → Bool) (g : Mat n) : ev g (rP ε) = ((rM ε g : ℝ) : ℂ) := by
  simp only [rP, rM, map_sum, map_mul, ev, eval_X, Sum.elim_inl, Sum.elim_inr]
  push_cast
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  ring

theorem sb_degmono {n : ℕ} (ε : Fin n → Bool) (Z : Mat n) (s : _) (a : ℂ) :
    (dZ ε Z (monomial s a)).totalDegree ≤ (monomial s a).totalDegree := by
  refine induction_on_monomial (motive := fun p => (dZ ε Z p).totalDegree ≤ p.totalDegree) ?_ ?_ s a
  · intro a
    have : dZ ε Z (C a) = 0 := by
      rw [← MvPolynomial.algebraMap_eq]; exact (dZ ε Z).map_algebraMap a
    rw [this]; simp
  · intro p v ih
    by_cases hp : p = 0
    · simp [hp]
    rw [Derivation.leibniz, totalDegree_mul_of_isDomain hp (X_ne_zero v), totalDegree_X, smul_eq_mul, smul_eq_mul]
    refine (totalDegree_add _ _).trans (max_le ?_ ?_)
    · refine (totalDegree_mul _ _).trans (add_le_add le_rfl ?_)
      simp only [dZ, mkDerivation_X]
      cases v with
      | inl x =>
        simp only [Sum.elim_inl]
        refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun c _ => ?_)
        refine (totalDegree_sub _ _).trans (max_le ?_ ?_)
        · exact (totalDegree_mul _ _).trans (by simp)
        · exact (totalDegree_mul _ _).trans (by simp)
      | inr x =>
        simp only [Sum.elim_inr]
        refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun c _ => ?_)
        refine (totalDegree_sub _ _).trans (max_le ?_ ?_)
        · exact (totalDegree_mul _ _).trans (by simp)
        · exact (totalDegree_mul _ _).trans (by simp)
    · refine (totalDegree_mul _ _).trans ?_
      rw [totalDegree_X]
      omega

theorem sb_degdz {n : ℕ} (ε : Fin n → Bool) (Z : Mat n) (P : Poly n) :
    (dZ ε Z P).totalDegree ≤ P.totalDegree := by
  conv_lhs => rw [P.as_sum]
  rw [map_sum]
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun m hm => ?_)
  refine (sb_degmono ε Z m _).trans ?_
  exact (totalDegree_monomial_le _ _).trans (le_totalDegree hm)

theorem sb_degrp {n : ℕ} (ε : Fin n → Bool) : (rP ε : Poly n).totalDegree ≤ 2 := by
  unfold rP
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun c _ => ?_)
  refine (totalDegree_mul _ _).trans ?_
  simp

theorem sb_evderiv {σ : Type} (D : Derivation ℂ (MvPolynomial σ ℂ) (MvPolynomial σ ℂ)) (γ : ℝ → σ → ℂ) (s : ℝ)
    (hγ : ∀ v, HasDerivAt (fun u => γ u v) (MvPolynomial.eval (γ s) (D (MvPolynomial.X v))) s) (P : MvPolynomial σ ℂ) :
    HasDerivAt (fun u => MvPolynomial.eval (γ u) P) (MvPolynomial.eval (γ s) (D P)) s := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    have : D (C a) = 0 := by
      rw [← MvPolynomial.algebraMap_eq]; exact D.map_algebraMap a
    simp only [this, eval_C, map_zero]
    exact hasDerivAt_const _ _
  | add p q hp hq =>
    simp only [map_add]
    exact hp.add hq
  | mul_X p v hp =>
    have h := hp.fun_mul (hγ v)
    simp only [map_mul, eval_X]
    refine h.congr_deriv ?_
    rw [Derivation.leibniz, map_add, smul_eq_mul, smul_eq_mul, map_mul, map_mul, eval_X]
    ring

theorem sb_curve {n : ℕ} (Z g : Matrix (Fin n) (Fin n) ℂ) (s : ℝ) (a b : Fin n) :
    HasDerivAt (fun u : ℝ => (NormedSpace.exp (-((u : ℂ) • Z)) * g * NormedSpace.exp ((u : ℂ) • Z)) a b)
      (((NormedSpace.exp (-((s : ℂ) • Z)) * g * NormedSpace.exp ((s : ℂ) • Z)) * Z -
        Z * (NormedSpace.exp (-((s : ℂ) • Z)) * g * NormedSpace.exp ((s : ℂ) • Z))) a b) s := by
  let : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
  let : NormedAlgebra ℂ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
  let : NormedAlgebra ℝ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
  have h1 : HasDerivAt (fun u : ℝ => NormedSpace.exp (u • (-Z))) (NormedSpace.exp (s • (-Z)) * (-Z)) s :=
    hasDerivAt_exp_smul_const _ _
  have h2 : HasDerivAt (fun u : ℝ => NormedSpace.exp (u • Z)) (NormedSpace.exp (s • Z) * Z) s :=
    hasDerivAt_exp_smul_const _ _
  have h3 := (h1.mul_const g).mul h2
  have hc : Commute Z (NormedSpace.exp (s • Z)) := ((Commute.refl Z).smul_right s).exp_right
  have hc' : Commute (-Z) (NormedSpace.exp (s • (-Z))) := ((Commute.refl (-Z)).smul_right s).exp_right
  let L : Matrix (Fin n) (Fin n) ℂ →L[ℝ] ℂ := (Matrix.entryLinearMap ℝ ℂ a b).toContinuousLinearMap
  have h4 := L.hasFDerivAt.comp_hasDerivAt s h3
  simp only [Function.comp_def] at h4
  have e : ∀ u : ℝ, (u : ℂ) • Z = u • Z := fun u => by simp
  simp only [e, smul_neg] at *
  refine HasDerivAt.congr_deriv (f := fun u : ℝ => (NormedSpace.exp (-(u • Z)) * g * NormedSpace.exp (u • Z)) a b) h4 ?_
  show (NormedSpace.exp (-(s • Z)) * -Z * g * NormedSpace.exp (s • Z) +
        NormedSpace.exp (-(s • Z)) * g * (NormedSpace.exp (s • Z) * Z)) a b = _
  have hm : NormedSpace.exp (-(s • Z)) * -Z * g * NormedSpace.exp (s • Z) +
        NormedSpace.exp (-(s • Z)) * g * (NormedSpace.exp (s • Z) * Z) =
      NormedSpace.exp (-(s • Z)) * g * NormedSpace.exp (s • Z) * Z -
        Z * (NormedSpace.exp (-(s • Z)) * g * NormedSpace.exp (s • Z)) := by
    rw [← hc'.eq]; noncomm_ring
  rw [hm]

theorem sb_evcurve {n : ℕ} (ε : Fin n → Bool) (Z g : Mat n) (s : ℝ) (P : Poly n) (hZ : LieU ε Z) :
    HasDerivAt (fun u : ℝ => ev (NormedSpace.exp (-((u : ℂ) • Z)) * g * NormedSpace.exp ((u : ℂ) • Z)) P) (ev (NormedSpace.exp (-((s : ℂ) • Z)) * g * NormedSpace.exp ((s : ℂ) • Z)) (dZ ε Z P)) s := by
  refine sb_evderiv (dZ ε Z)
    (fun u : ℝ => Sum.elim (fun x : Fin n × Fin n => (NormedSpace.exp (-((u : ℂ) • Z)) * g * NormedSpace.exp ((u : ℂ) • Z)) x.1 x.2) (fun x => star ((NormedSpace.exp (-((u : ℂ) • Z)) * g * NormedSpace.exp ((u : ℂ) • Z)) x.1 x.2))) s ?_ P
  have hZ' : ∀ a b, barM ε Z a b = (starRingEnd ℂ) (Z a b) := fun a b => (hZ a b).symm
  rintro (x | x)
  · refine (sb_curve Z g s x.1 x.2).congr_deriv ?_
    simp [dZ, mkDerivation_X, Matrix.mul_apply, Matrix.sub_apply, Finset.sum_sub_distrib]
  · refine (sb_curve Z g s x.1 x.2).star.congr_deriv ?_
    simp [dZ, mkDerivation_X, Matrix.mul_apply, Matrix.sub_apply, Finset.sum_sub_distrib, hZ', star_sum, star_mul']

theorem cutoffPolynomial_conjugation_deriv_mem_shapeSpan : StBasDeriv := by
  intro n ε Z H P hZ hH
  refine ⟨?_, fun g s => ?_⟩
  · have h1 : bas ε (deriv H) (dZ ε Z (rP ε) * P) ∈ ShapeM ε (P.totalDegree + 2) := by
      refine Submodule.subset_span ⟨deriv H, _, sb_derivcut H hH, ?_, rfl⟩
      have := (sb_degdz ε Z (rP ε)).trans (sb_degrp ε)
      exact (totalDegree_mul _ _).trans (by omega)
    have h2 : bas ε H (dZ ε Z P) ∈ ShapeM ε (P.totalDegree + 2) := by
      refine Submodule.subset_span ⟨H, _, hH, ?_, rfl⟩
      exact (sb_degdz ε Z P).trans (by omega)
    have e : adBas ε Z H P = bas ε (deriv H) (dZ ε Z (rP ε) * P) + bas ε H (dZ ε Z P) := rfl
    rw [e]
    exact Submodule.add_mem _ h1 h2
  · have hE := sb_evcurve ε Z g s (rP ε) hZ
    simp only [sb_evrp] at hE
    obtain ⟨c, hc⟩ : ∃ c, c = ev (NormedSpace.exp (-((s : ℂ) • Z)) * g * NormedSpace.exp ((s : ℂ) • Z)) (dZ ε Z (rP ε)) := ⟨_, rfl⟩
    rw [← hc] at hE
    have hre : HasDerivAt (fun u : ℝ => rM ε (NormedSpace.exp (-((u : ℂ) • Z)) * g * NormedSpace.exp ((u : ℂ) • Z))) c.re s := by
      have := Complex.reCLM.hasFDerivAt.comp_hasDerivAt s hE
      simpa [Function.comp_def] using this
    have him : c.im = 0 := by
      have h1 := Complex.imCLM.hasFDerivAt.comp_hasDerivAt s hE
      simp [Function.comp_def] at h1
      exact h1.unique (hasDerivAt_const _ _)
    have hcre : ((c.re : ℝ) : ℂ) = c := Complex.ext (by simp) (by simp [him])
    have hHd : HasDerivAt H (deriv H (rM ε (NormedSpace.exp (-((s : ℂ) • Z)) * g * NormedSpace.exp ((s : ℂ) • Z)))) (rM ε (NormedSpace.exp (-((s : ℂ) • Z)) * g * NormedSpace.exp ((s : ℂ) • Z))) :=
      ((hH.1.differentiable (by simp)) _).hasDerivAt
    have hcomp := (hHd.comp s hre).ofReal_comp
    have hP := sb_evcurve ε Z g s P hZ
    have htot := hcomp.fun_mul hP
    refine htot.congr_deriv ?_
    simp only [adBas, bas, map_mul, ← hc, Function.comp_apply]
    rw [← hcre]
    simp only [Complex.ofReal_re, Complex.ofReal_mul]
    ring

end GlobalTheory.PsCo.Pc1.B
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CycleListPermInvariant
section
open scoped TensorProduct
open GlobalTheory.LKInvGood

namespace GlobalTheory.SepModel

theorem tmul_mem_cenOrder {F : Type} [Field F] [NumberField F] (ℓ : ℕ) [Fact ℓ.Prime] {N : ℕ}
    (hN : ¬ ℓ ∣ N) {c : F} (hc : IsIntegral ℤ ((N : F) * c)) :
    (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] c ∈ cenOrder ℓ F := by
  have hu : IsUnit (N : ℤ_[ℓ]) := by
    rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
    exact (Nat.Prime.coprime_iff_not_dvd Fact.out).2 hN
  obtain ⟨u, hu⟩ := hu
  have hmem : (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] ((N : F) * c) ∈ cenOrder ℓ F :=
    Algebra.subset_adjoin ⟨⟨_, hc⟩, rfl⟩
  have heq : (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] c = (↑u⁻¹ : ℤ_[ℓ]) • ((1 : ℚ_[ℓ]) ⊗ₜ[ℚ] ((N : F) * c)) := by
    have h1 : (u : ℤ_[ℓ]) • ((1 : ℚ_[ℓ]) ⊗ₜ[ℚ] c) = (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] ((N : F) * c) := by
      rw [hu, Nat.cast_smul_eq_nsmul, ← TensorProduct.tmul_smul, nsmul_eq_mul]
    rw [← h1, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]
  rw [heq]
  exact Subalgebra.smul_mem _ hmem _

theorem exists_nat_integral {F : Type} [Field F] [NumberField F] (s : Finset F) :
    ∃ N : ℕ, 0 < N ∧ ∀ c ∈ s, IsIntegral ℤ ((N : F) * c) := by
  obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ (L := F) s
  refine ⟨y.natAbs, Int.natAbs_pos.2 hy0, fun c hc => ?_⟩
  have h := hy c hc
  rw [zsmul_eq_mul] at h
  rcases Int.natAbs_eq y with e | e
  · rw [e] at h; simpa using h
  · rw [e] at h
    have := h.neg
    simpa [neg_mul] using this

end GlobalTheory.SepModel

namespace GlobalTheory.SepModel

theorem exists_lift {F : Type} [Field F] [NumberField F] (ℓ : ℕ) [Fact ℓ.Prime] {N : ℕ}
    (hN : ¬ ℓ ∣ N) (r : Polynomial F) (hr : ∀ n, IsIntegral ℤ ((N : F) * r.coeff n)) :
    ∃ q : Polynomial (cenOrder ℓ F), q.map ((cenOrder ℓ F).val : cenOrder ℓ F →+* ℚ_[ℓ] ⊗[ℚ] F) =
      r.map (Algebra.TensorProduct.includeRight : F →ₐ[ℚ] ℚ_[ℓ] ⊗[ℚ] F).toRingHom := by
  have hl : r.map (Algebra.TensorProduct.includeRight : F →ₐ[ℚ] ℚ_[ℓ] ⊗[ℚ] F).toRingHom ∈
      Polynomial.lifts ((cenOrder ℓ F).val : cenOrder ℓ F →+* ℚ_[ℓ] ⊗[ℚ] F) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    rw [Polynomial.coeff_map]
    exact ⟨⟨_, tmul_mem_cenOrder ℓ hN (hr n)⟩, rfl⟩
  obtain ⟨q, hq⟩ := hl
  exact ⟨q, hq⟩

theorem separable_model (F : Type) [Field F] [NumberField F] (p : Polynomial F) (hp : p.Separable) :
    ∃ N : ℕ, 0 < N ∧ ∀ (ℓ : ℕ) [Fact ℓ.Prime], ¬ ℓ ∣ N →
      ∃ q : Polynomial (cenOrder ℓ F), q.map ((cenOrder ℓ F).val : cenOrder ℓ F →+* ℚ_[ℓ] ⊗[ℚ] F) =
        p.map (Algebra.TensorProduct.includeRight : F →ₐ[ℚ] ℚ_[ℓ] ⊗[ℚ] F).toRingHom ∧ q.Separable := by
  classical
  obtain ⟨a, b, hab⟩ := hp
  obtain ⟨N, hN0, hN⟩ := exists_nat_integral (p.coeffs ∪ a.coeffs ∪ b.coeffs)
  have hcoef : ∀ r : Polynomial F, r.coeffs ⊆ p.coeffs ∪ a.coeffs ∪ b.coeffs →
      ∀ n, IsIntegral ℤ ((N : F) * r.coeff n) := by
    intro r hs n
    by_cases h0 : r.coeff n = 0
    · rw [h0, mul_zero]; exact isIntegral_zero
    · exact hN _ (hs (Polynomial.coeff_mem_coeffs h0))
  refine ⟨N, hN0, fun ℓ _ hℓ => ?_⟩
  obtain ⟨q, hq⟩ := exists_lift ℓ hℓ p (hcoef p (fun x hx => by simp [hx]))
  obtain ⟨a', ha'⟩ := exists_lift ℓ hℓ a (hcoef a (fun x hx => by simp [hx]))
  obtain ⟨b', hb'⟩ := exists_lift ℓ hℓ b (hcoef b (fun x hx => by simp [hx]))
  refine ⟨q, hq, a', b', ?_⟩
  apply Polynomial.map_injective ((cenOrder ℓ F).val : cenOrder ℓ F →+* ℚ_[ℓ] ⊗[ℚ] F) Subtype.val_injective
  rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul, ← Polynomial.derivative_map,
    ha', hb', hq, Polynomial.derivative_map, ← Polynomial.map_mul, ← Polynomial.map_mul,
    ← Polynomial.map_add, hab, Polynomial.map_one, Polynomial.map_one]

end GlobalTheory.SepModel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CyclotomicIrreducibleOfNotDvdDiscr
section
namespace GlobalTheory

open Polynomial NumberField

theorem cyclotomic_irreducible_of_not_dvd_discr :
    ∀ (E : Type) [Field E] [NumberField E] (l : ℕ), l.Prime → ¬ (l : ℤ) ∣ NumberField.discr E →
      Irreducible (Polynomial.cyclotomic l E) := by
  intro E _ _ l hl hd
  refine ReciprocityTheory.Cheb.cyclotomic_irreducible_of_forall_isUnramifiedAt hl fun P hP hlP => ?_
  exact (not_dvd_discr_iff_forall_mem E (𝓞 E) (Nat.prime_iff_prime_int.1 hl)).1 hd P hP
    (by simpa using hlP)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DMBlockEntries
section
open MvPolynomial GlobalTheory.PsCo.Pc1 GlobalTheory.PsCo.Pc1.A

namespace GlobalTheory.PsCo.Cw2a

theorem dM_X_inl_entry {n : ℕ} (ε : Fin n → Bool) (x : Mode ε) (a b : Fin n) :
    dM ε x (X (Sum.inl (a, b))) =
      (if x.1.1 = b then X (Sum.inl (a, x.1.2)) else 0) - (if a = x.1.2 then X (Sum.inl (x.1.1, b)) else 0) := by
  classical
  simp only [dM, dZ, mkDerivation_X, Sum.elim_inl]
  rw [Finset.sum_sub_distrib]
  congr 1
  · rw [Finset.sum_eq_single x.1.2]
    · by_cases h : x.1.1 = b <;> simp [Matrix.single_apply, h]
    · intro c _ hc
      simp [Matrix.single_apply, Ne.symm hc]
    · simp
  · rw [Finset.sum_eq_single x.1.1]
    · by_cases h : a = x.1.2
      · simp [Matrix.single_apply, h]
      · simp [Matrix.single_apply, h, Ne.symm h]
    · intro c _ hc
      simp [Matrix.single_apply, Ne.symm hc]
    · simp

theorem dM_block_entries : BlockDeterminantCondition := by
  intro n ε a b hab
  classical
  cases ha : ε a with
  | true =>
    refine ⟨fun x y => if x.1.1 = b ∧ y = ⟨(a, x.1.2), ha, x.2.2⟩ then 1 else 0, fun x => ?_⟩
    have hne : a ≠ x.1.2 := by
      intro h
      have := x.2.2
      rw [← h, ha] at this
      exact Bool.noConfusion this
    rw [dM_X_inl_entry, if_neg hne, sub_zero, Finset.sum_eq_single (⟨(a, x.1.2), ha, x.2.2⟩ : Mode ε)]
    · by_cases h : x.1.1 = b <;> simp [h]
    · intro y _ hy
      simp [hy]
    · simp
  | false =>
    have hb : ε b = false := by rw [← hab, ha]
    refine ⟨fun x y => if a = x.1.2 ∧ y = ⟨(x.1.1, b), x.2.1, hb⟩ then -1 else 0, fun x => ?_⟩
    have hne : x.1.1 ≠ b := by
      intro h
      have := x.2.1
      rw [h, hb] at this
      exact Bool.noConfusion this
    rw [dM_X_inl_entry, if_neg hne, zero_sub, Finset.sum_eq_single (⟨(x.1.1, b), x.2.1, hb⟩ : Mode ε)]
    · by_cases h : a = x.1.2 <;> simp [h]
    · intro y _ hy
      simp [hy]
    · simp

end GlobalTheory.PsCo.Cw2a
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DMuEqExtDerivation
section
open MvPolynomial GlobalTheory.PsCo.Pc1 GlobalTheory.PsCo.Pc1.A

namespace GlobalTheory.PsCo.Cw2a

theorem coefM_apply_eq_coeff {n L : ℕ} (k : ℕ) (s : PolyM n L) :
    coefM n L k s = (optionEquivLeft ℂ (Fin L ⊕ EntIdx n) s).coeff k := by
  simp only [coefM, LinearMap.comp_apply, LinearMap.restrictScalars_apply, AlgEquiv.toLinearMap_apply,
    Polynomial.lcoeff_apply]

theorem dMu_eq_extDerivation {n L : ℕ} (ε : Fin n → Bool) (x : Mode ε) :
    dMu L ε x = mkDerivation ℂ (fun w : Option (Fin L ⊕ EntIdx n) => match w with
      | none => (0 : MvPolynomial (Option (Fin L ⊕ EntIdx n)) ℂ)
      | some v => rename some (dL L ε x (X v))) := by
  unfold dMu
  refine congrArg _ (funext fun w => ?_)
  cases w with
  | none => rfl
  | some v => simp only [inM]

theorem coefM_dMu : T_coefM_dMu := by
  intro n L ε x k s
  have h := GlobalTheory.coeff_optionEquivLeft_extDerivation (dL L ε x) k s
  rw [coefM_apply_eq_coeff, coefM_apply_eq_coeff, ← h]
  have e : dMu L ε x = mkDerivation ℂ (fun w : Option (Fin L ⊕ EntIdx n) => match w with
      | none => (0 : MvPolynomial (Option (Fin L ⊕ EntIdx n)) ℂ)
      | some v => rename some (dL L ε x (X v))) := dMu_eq_extDerivation ε x
  refine congrArg (fun D : Derivation ℂ (PolyM n L) (PolyM n L) => (optionEquivLeft ℂ (Fin L ⊕ EntIdx n) (D s)).coeff k) (e.trans ?_)
  refine congrArg _ (funext fun w => ?_)
  cases w <;> rfl

end GlobalTheory.PsCo.Cw2a
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DedekindPowerLocalization
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dedekind_power_localization : ∀ (B : Type) [CommRing B] [IsDedekindDomain B] (f : B), f ≠ 0 → ∀ (P : Ideal B), P.IsMaximal → ∃ N : ℕ, ∀ b ∈ P ^ N, ∃ s : B, s ∉ P ∧ s * b ∈ Ideal.span {f} := by
  first | (exact @GlobalTheory.dedekind_pow_maximal_mul_mem_span) | (exact GlobalTheory.dedekind_pow_maximal_mul_mem_span) | (intros; apply GlobalTheory.dedekind_pow_maximal_mul_mem_span <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivationDetEqDoubleSumAdjugateEntryStatement
section
open MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.derivation_det_eq_double_sum_adjugate_entry : ∀ {K R : Type} [CommRing K] [CommRing R] [Algebra K R] (δ : Derivation K R R) {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι R), δ M.det = ∑ i, ∑ j, M.adjugate j i * δ (M i j) := by
  first | exact @GlobalTheory.DetDeriv.main | exact GlobalTheory.DetDeriv.main | (intros; apply GlobalTheory.DetDeriv.main <;> assumption)
end

