import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1457
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1459
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1465
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1462
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1455
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1450
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1416
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0750
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1449
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1464
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1376
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0264
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0262

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusElementUnitaryMatrixIdentity
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThKSoDecay

noncomputable section

namespace GlobalTheory.TorusTranslate

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

variable (F E) in

abbrev finPart : AE F E →+* Af F ⊗[F] E := (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)).toRingHom

theorem ae_ext {σ : E →ₐ[F] E} (h : IsCMExt F E σ) {z z' : AE F E} (hf : finPart F E z = finPart F E z')
    (hi : ∀ (w : InfinitePlace F) (τ : EmbOver E w), infEmb τ (compInf F E w z) = infEmb τ (compInf F E w z')) :
    z = z' := by
  have key : ∀ z : AE F E, z = LinearMap.rTensor E (LinearMap.inl F (Ainf F) (Af F))
        (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) z) +
      LinearMap.rTensor E (LinearMap.inr F (Ainf F) (Af F))
        (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero, map_zero, map_zero, add_zero]; exact rfl
    | tmul x y =>
      simp only [Algebra.TensorProduct.map_tmul, LinearMap.rTensor_tmul, AlgHom.id_apply, ← TensorProduct.add_tmul]
      congr 1
      exact Prod.ext (by change x.1 = x.1 + 0; simp) (by change x.2 = 0 + x.2; simp)
    | add x y hx hy =>
      rw [map_add, map_add, map_add, map_add, add_add_add_comm, ← hx, ← hy]; exact rfl
  have e : ∀ (w : InfinitePlace F) (z : AE F E), Algebra.TensorProduct.map (GlobalTheory.AutFunCompare.evW w) (AlgHom.id F E)
      (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) z) = compInf F E w z := fun w z => by
    rw [← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp, AlgHom.comp_id]
    rfl
  have hinf : Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) z = Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) z' :=
    GlobalTheory.AutFunCompare.infTens_ext fun w => (infEmb_bijective h (Classical.arbitrary (EmbOver E w))).1
      (by rw [e, e]; exact hi w _)
  rw [key z, key z', hinf]
  exact congrArg _ (congrArg (LinearMap.rTensor E (LinearMap.inr F (Ainf F) (Af F))) hf)

theorem finPart_realAd_smul (s : ℝ) (x : AE F E) : finPart F E (realAd F s • x) = 0 := by
  rw [Algebra.smul_def, map_mul, Algebra.TensorProduct.algebraMap_apply]
  have : sndA F (realAd F s) = 0 := rfl
  simp [this]

theorem infEmb_realAd_smul {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (w : InfinitePlace F) (τ : EmbOver E w) (s : ℝ) (x : AE F E) :
    infEmb τ (compInf F E w (realAd F s • x)) = (s : ℂ) * infEmb τ (compInf F E w x) := by
  have := h.1
  have hw : w.IsReal := IsTotallyReal.isReal w
  rw [Algebra.smul_def, map_mul, map_mul, Algebra.TensorProduct.algebraMap_apply]
  congr 1
  change InfinitePlace.Completion.extensionEmbedding w (evInf F w (realAd F s)) * τ.1 1 = _
  rw [map_one, mul_one, ← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hw]
  congr 1
  change InfinitePlace.Completion.extensionEmbeddingOfIsReal hw
    ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (algebraMap ℝ (mixedEmbedding.mixedSpace F) s) w) = s
  have hy := (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply (algebraMap ℝ (mixedEmbedding.mixedSpace F) s)
  rw [InfiniteAdeleRing.ringEquiv_mixedSpace_apply] at hy
  have := congrFun (congrArg Prod.fst hy) ⟨w, hw⟩
  simpa using this

end GlobalTheory.TorusTranslate

namespace GlobalTheory.TorusTranslate

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem mulVec_col {n q : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} {B : Matrix (Fin n) (Fin q) ℂ} {d : Fin q → ℂ}
    (h : A * B = B * Matrix.diagonal d) (i : Fin q) : A *ᵥ (fun k => B k i) = fun k => B k i * d i := by
  funext k
  have := congrFun (congrFun h k) i
  rw [Matrix.mul_apply, Matrix.mul_diagonal] at this
  simpa [Matrix.mulVec, dotProduct] using this

end GlobalTheory.TorusTranslate

namespace GlobalTheory.TorusTranslate

theorem isTorusU_of_isTorusElt : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), (∀ i j, σ (J j i) = J i j) →
    ∀ (q : ℕ) (Xf Yf : Matrix (Fin n) (Fin q) E) (t : Fin q → ℝ) (a : GAd σ ((1 : E) • J.map σ)),
      GlobalTheory.SiegelSet.IsTorusElt σ ((1 : E) • J.map σ) Xf Yf t a →
      ∀ a' : UA σ J, (a' : GL (Fin n) (AE F E)) = HA.mat (AF F) σ ((1 : E) • J.map σ) a →
      IsTorusU (fun i k => Xf k i) (fun i k => Yf k i) t a' := by
  intro F E _ _ _ _ _ σ h n J hJ q Xf Yf t a ha a' ha'
  have hMa : mat a' = (HA.mat (AF F) σ ((1 : E) • J.map σ) a).1 := congrArg Units.val ha'

  have hfin : ∀ v : Fin n → AE F E, ∀ k, finPart F E (((mat a' - 1) *ᵥ v) k) = 0 := fun v k => by
    rw [RingHom.map_mulVec]
    have h0 : (mat a' - 1).map (finPart F E) = 0 := Matrix.ext fun i j => by
      have := congrArg (fun g : GL (Fin n) (Af F ⊗[F] E) => (g : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) i j)
        (MonoidHom.mem_ker.1 ha.1)
      rw [Matrix.map_apply, Matrix.sub_apply, map_sub, hMa]
      have e1 : finPart F E ((1 : Matrix (Fin n) (Fin n) (AE F E)) i j) = (1 : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) i j := by
        by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
      rw [e1]
      exact sub_eq_zero.2 this
    rw [h0, Matrix.zero_mulVec]
    rfl

  have harch : ∀ (w : InfinitePlace F) (τ : EmbOver E w) (v : Fin n → AE F E) k,
      infEmb τ (compInf F E w (((mat a' - 1) *ᵥ v) k)) =
        (GlobalTheory.Orb.archMat σ ((1 : E) • J.map σ) τ (projArch σ ((1 : E) • J.map σ) w a) *ᵥ
          (fun j => infEmb τ (compInf F E w (v j)))) k - infEmb τ (compInf F E w (v k)) := fun w τ v k => by
    have e : ((infEmb τ).comp (compInf F E w)) (((mat a' - 1) *ᵥ v) k) = _ := RingHom.map_mulVec _ _ _ _
    refine e.trans ?_
    rw [Matrix.map_sub _ (map_sub _), Matrix.sub_mulVec, Pi.sub_apply, hMa]
    congr 1
    rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec]
    rfl
  have h0 : ∀ (w : InfinitePlace F) (τ : EmbOver E w) (x : E), infEmb τ (compInf F E w (inclR (F := F) (AF F) x)) = τ.1 x :=
    fun w τ x => by
      change infEmb τ (evInf F w 1 ⊗ₜ[F] x) = _
      simp
  refine ⟨fun i => funext fun k => ae_ext h ?_ ?_, fun i => funext fun k => ae_ext h ?_ ?_, fun z hx hy => funext fun k => ae_ext h ?_ ?_⟩
  · rw [hfin, Pi.smul_apply, finPart_realAd_smul]
  · intro w τ
    rw [harch, Pi.smul_apply, infEmb_realAd_smul h]
    simp only [incV, h0]
    have hc := mulVec_col (ha.2 w τ).1 i
    simp only [Matrix.map_apply] at hc
    rw [hc]
    push_cast
    ring
  · rw [hfin, Pi.smul_apply, finPart_realAd_smul]
  · intro w τ
    rw [harch, Pi.smul_apply, infEmb_realAd_smul h]
    simp only [incV, h0]
    have hc := mulVec_col (ha.2 w τ).2.1 i
    simp only [Matrix.map_apply] at hc
    rw [hc]
    push_cast
    ring
  · rw [hfin, Pi.zero_apply, map_zero]
  · intro w τ
    have hc : ∀ (Z : Matrix (Fin n) (Fin q) E), (∀ i, form σ J z (fun k => Z k i) = 0) →
        (Formalism.UG.cT (σ : E →+* E) Z * ((1 : E) • J.map σ)) *ᵥ z = 0 := fun Z hZ => funext fun i => by
      rw [Pi.zero_apply, ← hZ i]
      simp only [one_smul, Formalism.UG.cT, Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.map_apply,
        Matrix.transpose_apply, form, RingHom.coe_coe, hJ, Pi.zero_apply]
      simp only [Finset.sum_mul, Finset.mul_sum]
      first
        | exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
        | (rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring)
    have e := (ha.2 w τ).2.2 z (hc Xf hx) (hc Yf hy)
    rw [harch, Pi.zero_apply, map_zero, map_zero]
    simp only [incV, h0]
    rw [e, sub_self]

end GlobalTheory.TorusTranslate
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceMemOfPowBdd
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.TraceBdd

theorem trace_mem_valuationSubring_of_pow_bounded {K : Type} [Field K] (O : ValuationSubring K) [IsNoetherianRing O]
    (n : ℕ) (y : Matrix (Fin n) (Fin n) K) (a : K) (ha : a ≠ 0)
    (h : ∀ k : ℕ, ∀ i j, a * (y ^ k) i j ∈ O) : y.trace ∈ O := by
  classical

  let N : Submodule O (Matrix (Fin n) (Fin n) K) :=
    Submodule.span O (Set.range fun p : Fin n × Fin n => a⁻¹ • Matrix.single p.1 p.2 (1 : K))
  have hNfg : N.FG := Submodule.fg_span (Set.finite_range _)
  haveI : IsNoetherian O N := isNoetherian_of_fg_of_noetherian N hNfg
  have hpow : ∀ k : ℕ, y ^ k ∈ N := by
    intro k
    rw [Matrix.matrix_eq_sum_single (y ^ k)]
    refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => ?_
    have hc : a * (y ^ k) i j ∈ O := h k i j
    have : Matrix.single i j ((y ^ k) i j) =
        (⟨a * (y ^ k) i j, hc⟩ : O) • (a⁻¹ • Matrix.single i j (1 : K)) := by
      rw [← algebraMap_smul K (⟨a * (y ^ k) i j, hc⟩ : O), smul_smul, Matrix.smul_single, smul_eq_mul]
      congr 1
      change (y ^ k) i j = a * (y ^ k) i j * a⁻¹ * 1
      field_simp
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨(i, j), rfl⟩)
  have hle : Subalgebra.toSubmodule (Algebra.adjoin O {y}) ≤ N := by
    rw [Algebra.adjoin_eq_span, Submodule.span_le]
    rintro x hx
    obtain ⟨k, rfl⟩ := Submonoid.mem_closure_singleton.mp hx
    exact hpow k
  have hint : IsIntegral O y :=
    isIntegral_of_submodule_noetherian _ (isNoetherian_of_le hle) y (Algebra.self_mem_adjoin_singleton O y)
  obtain ⟨p, hpm, hp⟩ := hint

  have hpL : aeval (y.map (algebraMap K (AlgebraicClosure K))) (p.map (algebraMap O (AlgebraicClosure K))) = 0 := by
    have h1 : aeval y (p.map (algebraMap O K)) = 0 := by
      rw [aeval_map_algebraMap]; exact hp
    have h2 : aeval (y.map (algebraMap K (AlgebraicClosure K)))
          ((p.map (algebraMap O K)).map (algebraMap K (AlgebraicClosure K))) =
        (Algebra.ofId K (AlgebraicClosure K)).mapMatrix (aeval y (p.map (algebraMap O K))) := by
      rw [aeval_map_algebraMap]
      rw [← aeval_algHom_apply]
      rfl
    rw [IsScalarTower.algebraMap_eq O K (AlgebraicClosure K), ← Polynomial.map_map, h2, h1, map_zero]
  have hroot : ∀ μ ∈ (y.map (algebraMap K (AlgebraicClosure K))).charpoly.roots, IsIntegral O μ := by
    intro μ hμ
    have hs : μ ∈ spectrum (AlgebraicClosure K) (y.map (algebraMap K (AlgebraicClosure K))) :=
      Matrix.mem_spectrum_iff_isRoot_charpoly.2 (isRoot_of_mem_roots hμ)
    have hs2 := spectrum.subset_polynomial_aeval (y.map (algebraMap K (AlgebraicClosure K)))
      (p.map (algebraMap O (AlgebraicClosure K))) ⟨μ, hs, rfl⟩
    rw [hpL] at hs2
    have h0 : eval μ (p.map (algebraMap O (AlgebraicClosure K))) = 0 := by
      by_contra hc
      rw [spectrum.mem_iff, sub_zero] at hs2
      exact hs2 ((Ne.isUnit hc).map _)
    exact ⟨p, hpm, by rwa [eval_map] at h0⟩
  have htr : algebraMap K (AlgebraicClosure K) y.trace = (y.map (algebraMap K (AlgebraicClosure K))).trace := by
    simp [Matrix.trace, map_sum]
  have hL : IsIntegral O (algebraMap K (AlgebraicClosure K) y.trace) := by
    rw [htr, Matrix.trace_eq_sum_roots_charpoly]
    exact multiset_sum_mem _ (fun μ hμ => (mem_integralClosure_iff _ _).2 (hroot μ hμ))
  have hK : IsIntegral O y.trace :=
    (isIntegral_algHom_iff (IsScalarTower.toAlgHom O K (AlgebraicClosure K))
      (algebraMap K (AlgebraicClosure K)).injective).1 hL
  obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.1 hK
  rw [← hz]
  exact z.2

end GlobalTheory.TraceBdd

theorem GlobalTheory.trace_mem_of_pow_bdd : ∀ (E : Type) [Field E] [NumberField E] (w : Pl E) (n : ℕ)
    (y : Matrix (Fin n) (Fin n) (w.adicCompletion E)) (a : w.adicCompletion E), a ≠ 0 →
    (∀ k : ℕ, ∀ i j, a * (y ^ k) i j ∈ Ov E w) → y.trace ∈ Ov E w := by
  intro E _ _ w n y a ha h
  exact GlobalTheory.TraceBdd.trace_mem_valuationSubring_of_pow_bounded (w.adicCompletionIntegers E) n y a ha h
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralSphericalUnitStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_orbital_integral_spherical_unit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (S : Set (Pl E)), IsSection S → ∀ P ∈ Ell E n, ∀ᶠ w in cofinite, ∀ y : GLw n w, (nrmL n w y).val.charpoly = atPl w P → twOrb (thL n w) (GlobalTheory.LFun.KGL w n) y ((GlobalTheory.LFun.KGL w n : Set (GLw n w)).indicator 1) = if ∃ g : GLw n w, g⁻¹ * y * thL n w g ∈ GlobalTheory.LFun.KGL w n then 1 else 0 := by
  first | exact @GlobalTheory.UnitOrb.twOrb_unit_eventually | exact GlobalTheory.UnitOrb.twOrb_unit_eventually | (intros; apply GlobalTheory.UnitOrb.twOrb_unit_eventually <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentMemIffUnipotentRadical
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.ThKCtFin

noncomputable section

namespace GlobalTheory.UnipMem

open GlobalTheory.LeviPlane Formalism.UG

theorem row_mulVec {R : Type} [CommRing R] {s : R →+* R} (hs : ∀ x, s (s x) = x) {n : ℕ} (J : Matrix (Fin n) (Fin n) R)
    (a : R) (x v : Fin n → R) (k : Fin 1) :
    ((cT s (Matrix.of fun i (_ : Fin 1) => x i) * (a • J.map s)) *ᵥ v) k = a * s (fm s J x v) := by
  simp only [fm, cT, Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.of_apply,
    Matrix.smul_apply, smul_eq_mul, map_sum, map_mul, hs, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem fm_mulVec {R : Type} [CommRing R] {s : R →+* R} {n : ℕ} {J g : Matrix (Fin n) (Fin n) R}
    (hg : gᵀ * J * g.map s = J) (u v : Fin n → R) : fm s J (g *ᵥ u) (g *ᵥ v) = fm s J u v := by
  have e : (fun i => s ((g *ᵥ v) i)) = g.map s *ᵥ fun i => s (v i) := funext fun i => RingHom.map_mulVec s g v i
  conv_rhs => rw [← hg]
  simp only [fm, e, ← Matrix.mulVec_mulVec]
  rw [Matrix.dotProduct_mulVec u, Matrix.vecMul_transpose]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem incV_mulVec {m n : ℕ} (M : Matrix (Fin m) (Fin n) E) (u : Fin n → E) :
    incV F (M *ᵥ u) = incM F M *ᵥ incV F u :=
  funext fun i => RingHom.map_mulVec (inclR (F := F) (AF F)) M u i

theorem exists_split {σ : E →ₐ[F] E} {B : Base F E} {d r s : ℕ} {W : Spc F E d} (hW : W.IsSkew σ B r s) {d₁ : ℕ}
    {W₁ : Spc F E d₁} {H' : Plane E d d₁} {i₀ i₁ : ℕ} (hH : H'.IsAdapted σ B W W₁ i₀ i₁) (v : Fin d → E) :
    ∃ (a t : E) (u : Fin d₁ → E), v = a • H'.x + H'.ι *ᵥ u + t • H'.y := by
  have hv : v ∈ Submodule.span E (W.L : Set (Fin d → E)) := by
    rw [hW.lat.span_eq_top]; trivial
  induction hv using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨a, t, u, -, -, -, h⟩ := hH.split z hz
    exact ⟨a, t, u, h⟩
  | zero => exact ⟨0, 0, 0, by simp⟩
  | add p q _ _ hp hq =>
    obtain ⟨a, t, u, rfl⟩ := hp
    obtain ⟨a', t', u', rfl⟩ := hq
    exact ⟨a + a', t + t', u + u', by rw [Matrix.mulVec_add, add_smul, add_smul]; abel⟩
  | smul b p _ hp =>
    obtain ⟨a, t, u, rfl⟩ := hp
    exact ⟨b * a, b * t, b • u, by rw [Matrix.mulVec_smul, smul_add, smul_add, smul_smul, smul_smul]⟩

theorem gen_iff {σ : E →ₐ[F] E} {B : Base F E} {d r s : ℕ} {W : Spc F E d} (hW : W.IsSkew σ B r s)
    (hσ : ∀ x, σ (σ x) = x) {c : E} (hc : c ≠ 0) {d₁ : ℕ}
    {W₁ : Spc F E d₁} {H' : Plane E d d₁} {i₀ i₁ : ℕ} (hH : H'.IsAdapted σ B W W₁ i₀ i₁) (u : UA σ W.J) :
    (mat u *ᵥ incV F H'.x = incV F H'.x ∧
      ∀ z, ∃ a : AE F E, mat u *ᵥ (incM F H'.ι *ᵥ z) = incM F H'.ι *ᵥ z + a • incV F H'.x) ↔
    ((mat u - 1) * adMat F (Matrix.of fun i (_ : Fin 1) => H'.x i) = 0 ∧
      adMat F (cT (σ : E →+* E) (Matrix.of fun i (_ : Fin 1) => H'.x i) * (c • W.J.map σ)) * (mat u - 1) = 0 ∧
      ∀ x : Fin d → E, (cT (σ : E →+* E) (Matrix.of fun i (_ : Fin 1) => H'.x i) * (c • W.J.map σ)) *ᵥ x = 0 →
        ∃ a : Fin 1 → AE F E, (mat u - 1) *ᵥ incV F x = adMat F (Matrix.of fun i (_ : Fin 1) => H'.x i) *ᵥ a) := by
  have hcol : ∀ a : Fin 1 → AE F E, adMat F (Matrix.of fun i (_ : Fin 1) => H'.x i) *ᵥ a = a 0 • incV F H'.x := fun a => by
    funext i; simp [Matrix.mulVec, dotProduct, incV, mul_comm]
  have h1 : (mat u - 1) * adMat F (Matrix.of fun i (_ : Fin 1) => H'.x i) = 0 ↔ mat u *ᵥ incV F H'.x = incV F H'.x := by
    rw [← sub_eq_zero (a := mat u *ᵥ _), show mat u *ᵥ incV F H'.x - incV F H'.x = (mat u - 1) *ᵥ incV F H'.x by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec]]
    exact ⟨fun h => funext fun i => congrFun (congrFun h i) 0, fun h => Matrix.ext fun i _ => congrFun h i⟩
  have hrow : ∀ (v : Fin d → E) k, ((cT (σ : E →+* E) (Matrix.of fun i (_ : Fin 1) => H'.x i) * (c • W.J.map σ)) *ᵥ v) k =
      c * σ (fm (σ : E →+* E) W.J H'.x v) := fun v k => row_mulVec (s := (σ : E →+* E)) hσ W.J c H'.x v k
  have hxι : ∀ w, fm (σ : E →+* E) W.J H'.x (H'.ι *ᵥ w) = 0 := fun w => by
    rw [fm_skew (σ : E →+* E) hσ W.J hW.skew, show fm (σ : E →+* E) W.J (H'.ι *ᵥ w) H'.x = 0 from (hH.orth w).1, map_zero,
      neg_zero]
  rw [h1]
  refine and_congr_right fun hx => ⟨fun h => ⟨?_, fun v hv => ?_⟩, fun h z => ?_⟩
  · have e : adMat F (cT (σ : E →+* E) (Matrix.of fun i (_ : Fin 1) => H'.x i) * (c • W.J.map σ)) =
        cT (cA σ).toRingHom (Matrix.of fun i (_ : Fin 1) => incV F H'.x i) *
          (inclR (F := F) (AF F) c • (incM F W.J).map (cA σ).toRingHom) := by
      ext k j
      simp only [adMat, cT, Matrix.map_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, Matrix.smul_apply,
        smul_eq_mul, map_sum, map_mul, incV, incM, cAr_inclR, RingHom.coe_coe]
    have hu : (mat u)ᵀ * incM F W.J * (mat u).map (cA σ).toRingHom = incM F W.J := u.2
    rw [e]
    refine Matrix.ext_of_mulVec_single fun j => funext fun k => ?_
    rw [← Matrix.mulVec_mulVec, row_mulVec (cA_invol hσ), Matrix.sub_mulVec, Matrix.one_mulVec, fm_sub_right]
    conv_lhs => enter [2, 2, 1]; rw [← hx, fm_mulVec hu]
    simp
  · obtain ⟨a, t, w, rfl⟩ := exists_split hW hH v
    have ht := congrFun hv 0
    rw [hrow, fm_add_right, fm_add_right, fm_smul_right, fm_smul_right, hxι,
      show fm (σ : E →+* E) W.J H'.x H'.x = 0 from hH.xx, show fm (σ : E →+* E) W.J H'.x H'.y = 1 from hH.xy] at ht
    have ht0 : t = 0 := by simpa [hc] using ht
    obtain ⟨b, hb⟩ := h (incV F w)
    refine ⟨fun _ => b, ?_⟩
    have e : incV F (a • H'.x + H'.ι *ᵥ w + t • H'.y) = inclR (F := F) (AF F) a • incV F H'.x + incM F H'.ι *ᵥ incV F w := by
      rw [ht0, zero_smul, add_zero, ← incV_mulVec]; funext i; simp [incV]
    rw [hcol, e, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_add, Matrix.mulVec_smul, hx, hb]
    abel
  · have h3 : ∀ j : Fin d₁, ∃ a : AE F E, (mat u - 1) *ᵥ (incM F H'.ι *ᵥ Pi.single j 1) = a • incV F H'.x := fun j => by
      obtain ⟨a, ha⟩ := h.2 (H'.ι *ᵥ Pi.single j 1) (funext fun k => by rw [hrow, hxι]; simp)
      refine ⟨a 0, ?_⟩
      rw [← hcol, ← ha, incV_mulVec]
      congr 2
      funext i; by_cases hij : i = j <;> simp [incV, Pi.single_apply, hij]
    choose a ha using h3
    refine ⟨∑ j, z j * a j, ?_⟩
    rw [← sub_eq_iff_eq_add', show mat u *ᵥ (incM F H'.ι *ᵥ z) - incM F H'.ι *ᵥ z = (mat u - 1) *ᵥ (incM F H'.ι *ᵥ z) by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec]]
    conv_lhs => rw [show z = ∑ j, z j • Pi.single j 1 from by funext i; simp [Finset.sum_apply, Pi.single_apply]]
    simp only [Matrix.mulVec_sum, Matrix.mulVec_smul, ha, smul_smul, Finset.sum_smul]

end GlobalTheory.UnipMem

theorem GlobalTheory.UnipMem.mem_unip_iff : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (d r s : ℕ) (W : Spc F E d), W.IsSkew σ B r s → ∀ (hσ : ∀ x, σ (σ x) = x) (c : E) (hc : c ≠ 0), σ c = -c → ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ), H'.IsAdapted σ B W W₁ i₀ i₁ → ∀ g : UA σ W.J, g ∈ unip σ W H' ↔ toGAd hσ W.J hc g ∈ unipRad σ (c • W.J.map σ) (Matrix.of fun i (_ : Fin 1) => H'.x i) := by
  intro F E _ _ _ _ _ σ B d r s W hW hσ c hc _ d₁ W₁ H' i₀ i₁ hH g
  have e : (unip σ W H').map (toGAd hσ W.J hc).toMonoidHom =
      unipRad σ (c • W.J.map σ) (Matrix.of fun i (_ : Fin 1) => H'.x i) := by
    rw [unip, MonoidHom.map_closure, unipRad]
    congr 1
    ext k
    obtain ⟨u, rfl⟩ := (toGAd hσ W.J hc).surjective k
    refine ((toGAd hσ W.J hc).injective.mem_set_image).trans ?_
    exact GlobalTheory.UnipMem.gen_iff hW hσ hc hH u
  rw [← e]
  exact (Subgroup.mem_map_iff_mem (f := (toGAd hσ W.J hc).toMonoidHom) (toGAd hσ W.J hc).injective).symm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentRadicalAdelicEqRatMulBoundedRealMulLeve
section
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction

noncomputable section

namespace GlobalTheory.RapCover

theorem unip_eq_rat_mul_inf_mul_fin : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (s : ℕ)
    (L : Set (GL (Fin a) (Af E))), L ∈ nhds (1 : GL (Fin a) (Af E)) → ∃ R : ℝ, 0 ≤ R ∧ ∀ x : BlockIx a s → Ad E,
    ∃ (ξ : BlockIx a s → E) (z : BlockIx a s → Cinf E) (k : GL (Fin a) (Af E)), k ∈ L ∧ ‖z‖ ≤ R ∧
    unip x = ratGL E a (unip ξ) * infGL E a (unip z) * finGL E a k := by
  intro E _ _ _ a s L hL
  have h0 : (unip (0 : BlockIx a s → Af E)) = 1 := by
    have h := unip_add (0 : BlockIx a s → Af E) 0
    rw [add_zero] at h
    exact (mul_eq_left.1 h.symm)
  have hpre : (fun y : BlockIx a s → Af E => unip y) ⁻¹' L ∈ nhds (0 : BlockIx a s → Af E) := by
    apply JointCont.continuous_unip.continuousAt.preimage_mem_nhds
    rw [h0]; exact hL
  rw [nhds_pi, Filter.mem_pi] at hpre
  obtain ⟨I, -, t, ht, hsub⟩ := hpre
  have hU : (⋂ p, t p) ∈ nhds (0 : Af E) := Filter.iInter_mem.2 fun p => by simpa using ht p
  obtain ⟨R, hR, hx⟩ := GlobalTheory.T.exists_rational_sub_bounded_infinite_small_finite E (⋂ p, t p) hU
  refine ⟨R, hR, fun x => ?_⟩
  choose ξ hξ1 hξ2 using fun p => hx (x p)
  refine ⟨ξ, fun p => pInf E (x p - algebraMap E (Ad E) (ξ p)),
    unip (fun p => pFin E (x p - algebraMap E (Ad E) (ξ p))), ?_, ?_, ?_⟩
  · apply hsub
    intro p _
    exact Set.mem_iInter.1 (hξ2 p) p
  · exact (pi_norm_le_iff_of_nonneg hR).2 hξ1
  · have hsplit : x = (fun p => algebraMap E (Ad E) (ξ p)) + (fun p => x p - algebraMap E (Ad E) (ξ p)) := by
      funext p; simp
    conv_lhs => rw [hsplit, unip_add, unip_algebraMap,
      ← infGL_mul_finGL (unip (fun p => x p - algebraMap E (Ad E) (ξ p))), JointCont.map_unip, JointCont.map_unip]
    rw [mul_assoc]

end GlobalTheory.RapCover
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedVectorGivesLocalComponentSphericalVectStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramifiedVector_gives_localComponent_sphericalVector : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, ∀ π : Submodule ℂ (UA E n → ℂ), IsAutRepU π → ∀ (w : Pl E) (σ : SmIrr (UL n w)), IsCompU π w σ → IsUnramU π w → fixed σ.ρ (KL n w) ≠ ⊥ := by
  first | exact @GlobalTheory.BCT.LocUnr.fixed_KL_ne_bot | exact GlobalTheory.BCT.LocUnr.fixed_KL_ne_bot | (intros; apply GlobalTheory.BCT.LocUnr.fixed_KL_ne_bot <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittRankLeHermitianSignatureStatement
section
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.witt_rank_le_hermitian_signature : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n : ℕ) (X : Spc F E n) (r s : ℕ), B.IsGood σ → X.IsHerm σ B r s →
    ∀ (r₀ : ℕ) (Xf Yf : Matrix (Fin n) (Fin r₀) E), GlobalTheory.SiegelSet.IsWittFrame σ ((1 : E) • X.J.map σ) Xf Yf →
      r₀ ≤ r ∧ r₀ ≤ s := by
  first | exact @GlobalTheory.WittFrameSig.wittFrame_le_signature | exact GlobalTheory.WittFrameSig.wittFrame_le_signature | (intros; apply GlobalTheory.WittFrameSig.wittFrame_le_signature <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WordEqSmoothingOfReproducedStatement
section
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_test_word_eq_smoothing : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (ν : Measure (Lie E a)) [ν.IsAddHaarMeasure] (α : Lie E a → ℂ), IsTest (invSet E a) α → ∀ φ : Sm E a, smoothing ν α φ.1 = φ.1 → ∀ l : List (Lie E a), ∃ β : Lie E a → ℂ, IsTest (invSet E a) β ∧ ((l.map (lie E a)).prod φ).1 = smoothing ν β φ.1 := by
  first | exact @GlobalTheory.AutGrowth.word_eq_smoothing_of_reproduced | exact GlobalTheory.AutGrowth.word_eq_smoothing_of_reproduced | (intros; apply GlobalTheory.AutGrowth.word_eq_smoothing_of_reproduced <;> assumption)
end

