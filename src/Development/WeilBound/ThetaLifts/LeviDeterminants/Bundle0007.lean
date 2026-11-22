import Development.WeilBound.CoreStatements.LocalThetaKernels.Locrep
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.AdaptC
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0048
import Development.AutomorphicSpectrum.Proofs.TwistedProofs.Bundle0008
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0019
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProductFormulaHaar.Bundle0002
import Mathlib
import Development.WeilBound.ThetaLifts.LeviDeterminants.Bundle0006

-- bundled from Development.WeilBound.ThetaLifts.LeviDeterminants.ActsEx
section
noncomputable section

namespace PositivityTheory.ThKF0

open scoped Matrix GlobalTheory.VacAny
open NumberField IsDedekindDomain Filter Topology GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PositivityTheory.ThK
open PositivityTheory.ThKH.Locrep

theorem actsEx : GlobalTheory.ThK.ActsEx := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP v
  obtain ⟨ω, ρ, L⟩ := locRepEx F E σ n d B X W M om ⟨hP.base, ⟨r, s, hP.herm⟩, ⟨r', s', hP.skew⟩, hP.good, χX, χW, hP.weil⟩ v
  refine ⟨fun g hg h hh φ hφ => ⟨ω (g, h) φ, ⟨L.pres g hg h hh φ hφ, (L.acts g hg h hh φ hφ _).2 rfl⟩,
      fun φ₁ h₁ => (L.acts g hg h hh φ hφ _).1 h₁.2⟩,
    fun u hu φ hφ => ⟨ρ u φ, ⟨L.presH u hu φ hφ, (L.actsH u hu φ hφ _).2 rfl⟩,
      fun φ₁ h₁ => (L.actsH u hu φ hφ _).1 h₁.2⟩, fun φ hφ => ?_⟩
  have hs := IsUWeilPair.isUSplitting hP.weil
  obtain ⟨r₀, x₀, h₀, h₁⟩ := exists_base (Fin n × Fin d) v
  let loc : UA σ X.J × UA σ W.J → Module.End ℂ (Fn F n d v) := fun p => res v x₀ ∘ₗ om p ∘ₗ tensL v r₀
  have hloc : ∀ p : UA σ X.J × UA σ W.J, p.1 ∈ UAt σ X (evFin F v) → p.2 ∈ UAt σ W (evFin F v) → ∀ φ ∈ SB _,
      loc p φ = ω p φ := fun p h1 h2 φ hφ =>
    (eq_of_acts v h₁ (h₀ φ hφ) ((L.acts p.1 h1 p.2 h2 φ hφ _).2 rfl)).symm
  obtain ⟨K, hK1, hK2, hK3, hK4⟩ := exists_small_subgroups σ X v
  obtain ⟨K', hK1', hK2', hK3', hK4'⟩ := exists_small_subgroups σ W v
  obtain ⟨m, hm⟩ := smooth_of_weak (SB _) (fun k => (K k).prod (K' k))
    (fun a b hab => Subgroup.prod_mono (hK1 hab) (hK1' hab))
    (fun U hU => by
      obtain ⟨U₁, h1, U₂, h2, h⟩ := mem_nhds_prod_iff.1 hU
      obtain ⟨a, ha⟩ := hK2 U₁ h1
      obtain ⟨b, hb⟩ := hK2' U₂ h2
      exact ⟨max a b, fun p hp => h ⟨ha (hK1 (le_max_left a b) hp.1), hb (hK1' (le_max_right a b) hp.2)⟩⟩)
    loc (fun p hp φ hφ => by
      rw [hloc p (hK3 0 hp.1) (hK3' 0 hp.2) φ hφ]
      exact L.pres p.1 (hK3 0 hp.1) p.2 (hK3' 0 hp.2) φ hφ)
    (fun φ hφ => by
      rw [hloc 1 (one_mem_UAt X v) (one_mem_UAt W v) φ hφ]
      exact L.one φ hφ)
    (fun p hp q hq φ hφ => by
      rw [hloc (p * q) (mul_mem_UAt (hK3 0 hp.1) (hK3 0 hq.1)) (mul_mem_UAt (hK3' 0 hp.2) (hK3' 0 hq.2)) φ hφ,
        hloc q (hK3 0 hq.1) (hK3' 0 hq.2) φ hφ,
        hloc p (hK3 0 hp.1) (hK3' 0 hp.2) _ (L.pres q.1 (hK3 0 hq.1) q.2 (hK3' 0 hq.2) φ hφ)]
      exact L.mul p.1 (hK3 0 hp.1) p.2 (hK3' 0 hp.2) q.1 (hK3 0 hq.1) q.2 (hK3' 0 hq.2) φ hφ)
    (fun l φ hφ => hs.cont _ (res_adm v x₀ l) _ (h₀ φ hφ).2) φ hφ
  obtain ⟨U, hU, hUK⟩ := hK4 m
  obtain ⟨U', hU', hUK'⟩ := hK4' m
  refine ⟨U ×ˢ U', prod_mem_nhds hU hU', fun x hx h1 h2 => ?_⟩
  refine (L.acts x.1 h1 x.2 h2 φ hφ φ).2 ?_
  rw [← hloc x h1 h2 φ hφ]
  exact (hm x ⟨hUK _ hx.1 h1, hUK' _ hx.2 h2⟩).symm

end PositivityTheory.ThKF0
end
end

-- bundled from Development.WeilBound.ThetaLifts.LeviDeterminants.CartanPos
section
noncomputable section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace PositivityTheory.ThKF0

open PositivityTheory.Mix.Adapt GlobalTheory.CompanionTheory.Ar.RT.Lie

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem tr_evI (h : IsTotallyReal F) (a : AF F) : Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F a) =
    ∑ w : InfinitePlace F, (InfinitePlace.Completion.extensionEmbedding w (a.1 w)).re := by
  classical
  haveI : IsEmpty {w : InfinitePlace F // w.IsComplex} :=
    ⟨fun w => InfinitePlace.not_isReal_iff_isComplex.2 w.2 (h.isReal w.1)⟩
  rw [evI, Algebra.trace_prod_apply, PI.ProdFormulaE.Tr.trace_pi, PI.ProdFormulaE.Tr.trace_pi,
    InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
  refine (congrArg₂ HAdd.hAdd ?_ (Finset.sum_of_isEmpty _)).trans (add_zero _)
  refine Fintype.sum_equiv (Equiv.subtypeUnivEquiv h.isReal) _ _ fun w => ?_
  rw [Equiv.subtypeUnivEquiv_apply, ← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply w.2, Complex.ofReal_re]
  simp

theorem tr_tr (h : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w) (z : AE F E) :
    Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F (Algebra.trace (AF F) (AE F E) z)) =
      ∑ w, 2 * (piInf (τ w) z).re := by
  rw [tr_evI h.1]
  refine Finset.sum_congr rfl fun w _ => ?_
  have h1 : algebraMap (AF F) (AE F E) (Algebra.trace (AF F) (AE F E) z) = z + cA σ z := by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]; ring
    | tmul a e =>
      rw [← GlobalTheory.VacIndic.smul_inclR_eq, map_smul (Algebra.trace _ _), map_smul (cA σ), GlobalTheory.VacIndic.trace_inclR, GlobalTheory.VacIndic.cA_inclR, ← smul_add,
        ← map_add, ← GlobalTheory.SelfDualLatticeCompare.trace_field h, smul_eq_mul, map_mul, Algebra.smul_def]
      congr 1
      generalize Algebra.trace F E e = t
      show algebraMap F (AF F) t ⊗ₜ[F] (1 : E) = (1 : AF F) ⊗ₜ[F] algebraMap F E t
      rw [Algebra.algebraMap_eq_smul_one (A := AF F), Algebra.algebraMap_eq_smul_one (A := E), TensorProduct.smul_tmul]
  have h2 := congrArg (piInf (τ w)) h1
  rw [map_add, piInf_cA h, Complex.add_conj] at h2
  have h3 : piInf (τ w) (algebraMap (AF F) (AE F E) (Algebra.trace (AF F) (AE F E) z)) =
      InfinitePlace.Completion.extensionEmbedding w ((Algebra.trace (AF F) (AE F E) z).1 w) * (τ w).1 1 := rfl
  rw [h3, map_one, mul_one] at h2
  rw [h2, Complex.ofReal_re]

abbrev cj : ℂ →ₐ[ℝ] ℂ := Complex.conjAe

variable {n d : ℕ}

def omega (σ : E →ₐ[F] E) (X : Spc F E n) (W : Spc F E d) (u u' : Matrix (Fin n) (Fin d) (AE F E)) : ℝ :=
  Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F (symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J) u u'))

variable {X : Spc F E n} {W : Spc F E d} {B : Base F E} {r s r' s' : ℕ}

theorem omega_eq (hB : B.IsGood σ) (u u' : Matrix (Fin n) (Fin d) (AE F E)) : omega σ X W u u' =
    ∑ w, 2 * (-hTens cj (X.J.map (B.emb w).1) (W.J.map (B.emb w).1) (u.map (piInf (B.emb w))) (u'.map (piInf (B.emb w)))).re := by
  rw [omega, symp, tr_tr hB.cm B.emb]
  refine Finset.sum_congr rfl fun w _ => ?_
  congr 2
  simp only [hTens, neg_one_mul, map_neg, map_sum, map_mul, piInf_cA hB.cm, incM, Matrix.map_apply, piInf_inclR]
  rfl

def Rel (B : Base F E) (X : Spc F E n) (W : Spc F E d) (e : InfinitePlace F → ℤˣ) (u u' : Matrix (Fin n) (Fin d) (AE F E)) : Prop :=
  ∀ w, u'.map (piInf (B.emb w)) = (((e w : ℤ) : ℂ) * Complex.I) • (X.θ w * u.map (piInf (B.emb w)) * (W.θ w)ᵀ)

variable {e : InfinitePlace F → ℤˣ} {u u' u₁ u₁' : Matrix (Fin n) (Fin d) (AE F E)}

theorem sq_sign (x : ℤˣ) : ((x : ℤ) : ℂ) * ((x : ℤ) : ℂ) = 1 := by
  rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]; simp

theorem Rel.add (h : Rel B X W e u u') (h₁ : Rel B X W e u₁ u₁') : Rel B X W e (u + u₁) (u' + u₁') := fun w => by
  rw [Matrix.map_add _ (map_add _), Matrix.map_add _ (map_add _), h w, h₁ w, Matrix.mul_add, Matrix.add_mul, smul_add]

theorem Rel.symm (hX : X.IsHerm σ B r s) (hW : W.IsSkew σ B r' s') (h : Rel B X W e u u') : Rel B X W e u' (-u) := fun w => by
  have h2 : (W.θ w)ᵀ * (W.θ w)ᵀ = 1 := by rw [← Matrix.transpose_mul, (hW.cartan w).1, Matrix.transpose_one]
  rw [h w, Matrix.map_neg _ (map_neg _), Matrix.mul_smul, Matrix.smul_mul, smul_smul, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    (hX.cartan w).1, Matrix.one_mul, Matrix.mul_assoc, h2, Matrix.mul_one,
    show ((e w : ℤ) : ℂ) * Complex.I * (((e w : ℤ) : ℂ) * Complex.I) = -1 by
      linear_combination (Complex.I * Complex.I) * sq_sign (e w) + Complex.I_mul_I, neg_one_smul]

theorem at_ext {α β : Type} (hB : B.IsGood σ) {u u' : Matrix α β (AE F E)} (hu : At (evI F) u) (hu' : At (evI F) u')
    (h : ∀ w, u.map (piInf (B.emb w)) = u'.map (piInf (B.emb w))) : u = u' := by
  ext i j
  refine sub_eq_zero.1 (GlobalTheory.CompanionTheory.CMAdele.eq_zero_of_piInf σ hB.cm B.emb _ (fun t ht => ?_) fun w => ?_)
  · rw [smul_sub, show t • u i j = 0 from congrFun (congrFun (hu t ht) i) j,
      show t • u' i j = 0 from congrFun (congrFun (hu' t ht) i) j, sub_zero]
  · rw [map_sub, sub_eq_zero]
    exact congrFun (congrFun (h w) i) j

theorem Rel.unique (hB : B.IsGood σ) (h : Rel B X W e u u') (h₁ : Rel B X W e u u₁') (hu : At (evI F) u') (hu' : At (evI F) u₁') :
    u' = u₁' := at_ext hB hu hu' fun w => (h w).trans (h₁ w).symm

theorem exists_vec {α : Type} (hB : B.IsGood σ) (z : InfinitePlace F → α → ℂ) :
    ∃ a : α → AE F E, At (evI F) a ∧ ∀ w i, piInf (B.emb w) (a i) = z w i := by
  choose a ha using fun i => GlobalTheory.CompanionTheory.RealPlaceAdele.exists_adele_piInf σ hB.cm B.emb fun w => z w i
  exact ⟨a, fun t ht => funext fun i => (ha i).1 t ht, fun w i => (ha i).2 w⟩

theorem exists_rel (hB : B.IsGood σ) (X : Spc F E n) (W : Spc F E d) (e) (u : Matrix (Fin n) (Fin d) (AE F E)) :
    ∃ u', At (evI F) u' ∧ Rel B X W e u u' := by
  obtain ⟨a, h1, h2⟩ := exists_vec hB fun w (k : Fin n × Fin d) =>
    ((((e w : ℤ) : ℂ) * Complex.I) • (X.θ w * u.map (piInf (B.emb w)) * (W.θ w)ᵀ)) k.1 k.2
  exact ⟨Matrix.of fun i j => a (i, j), fun t ht => Matrix.ext fun i j => congrFun (h1 t ht) (i, j),
    fun w => Matrix.ext fun i j => h2 w (i, j)⟩

theorem hTens_smul {α β : Type} [Fintype α] [Fintype β] (J : Matrix α α ℂ) (J' : Matrix β β ℂ) (a b : ℂ) (x y : Matrix α β ℂ) :
    hTens cj J J' (a • x) (b • y) = a * star b * hTens cj J J' x y := by
  simp only [hTens, Finset.mul_sum, Matrix.smul_apply, smul_eq_mul, map_mul]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => ?_
  change _ * (star b * _) = _
  ring

theorem omega_rel (hB : B.IsGood σ) (hX : X.IsHerm σ B r s) (hW : W.IsSkew σ B r' s') (h : Rel B X W e u u')
    (h₁ : Rel B X W e u₁ u₁') : omega σ X W u' u₁' = omega σ X W u u₁ := by
  rw [omega_eq hB, omega_eq hB]
  refine Finset.sum_congr rfl fun w _ => ?_
  have h2 : (W.θ w)ᵀ * W.J.map (B.emb w).1 * (W.θ w).map cj = W.J.map (B.emb w).1 := by
    have := (hW.cartan w).2.1
    rw [Matrix.mul_smul, Matrix.smul_mul] at this
    exact smul_right_injective _ Complex.I_ne_zero this
  have h3 : (X.θ w)ᵀ * X.J.map (B.emb w).1 * (X.θ w).map cj = X.J.map (B.emb w).1 := (hX.cartan w).2.1
  rw [h w, h₁ w, hTens_smul, hTens_mul, h2, h3,
    show ((e w : ℤ) : ℂ) * Complex.I * star (((e w : ℤ) : ℂ) * Complex.I) = 1 by
      simp only [star_mul, Complex.star_def, Complex.conj_I, map_intCast]
      linear_combination (-Complex.I * Complex.I) * sq_sign (e w) - Complex.I_mul_I, one_mul]

theorem cartan_pos {M θ : Matrix (Fin n) (Fin n) ℂ} (h : IsCartan M θ) (hM : ∀ i j, star (M j i) = M i j) (a : Fin n → ℂ) :
    ∃ p : ℝ, a ⬝ᵥ M *ᵥ star (θ *ᵥ a) = p ∧ (a = 0 → p = 0) ∧ (a ≠ 0 → 0 < p) := by
  have hs : ∀ x, star (θ *ᵥ x) = θ.map star *ᵥ star x := fun x => funext fun i => by
    simp [Matrix.mulVec, dotProduct, mul_comm]
  have h1 : a ⬝ᵥ M *ᵥ star (θ *ᵥ a) = (θ *ᵥ a) ⬝ᵥ M *ᵥ star a := by
    conv_lhs => rw [← h.2.1, ← Matrix.mulVec_mulVec, ← hs, Matrix.mulVec_mulVec a, h.1, Matrix.one_mulVec, ← Matrix.mulVec_mulVec,
      Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
  have h2 : star (a ⬝ᵥ M *ᵥ star (θ *ᵥ a)) = (θ *ᵥ a) ⬝ᵥ M *ᵥ star a := by
    generalize θ *ᵥ a = b
    simp only [dotProduct, Matrix.mulVec, star_sum, star_mul', Pi.star_apply, star_star, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [hM]; ring
  refine ⟨(a ⬝ᵥ M *ᵥ star (θ *ᵥ a)).re, (Complex.conj_eq_iff_re.1 (h2.trans h1.symm)).symm, fun h0 => by simp [h0], fun h0 => ?_⟩
  rw [h1]
  exact h.2.2 a h0

theorem omega_pure (hB : B.IsGood σ) (hX : X.IsHerm σ B r s) (hW : W.IsSkew σ B r' s') (a : Fin n → AE F E) {b : Fin d → E}
    (hb : b ≠ 0) (h : Rel B X W e (Matrix.vecMulVec a (incV F b)) u') :
    ∃ p : InfinitePlace F → ℝ, omega σ X W (Matrix.vecMulVec a (incV F b)) u' = ∑ w, ((e w : ℤ) : ℝ) * p w ∧
      ∀ w, ((fun i => piInf (B.emb w) (a i)) = 0 → p w = 0) ∧ ((fun i => piInf (B.emb w) (a i)) ≠ 0 → 0 < p w) := by
  choose p hp using fun w => cartan_pos (hX.cartan w) (fun i j => by
    rw [Matrix.map_apply, Matrix.map_apply, ← hB.cm.2.2.2, hX.herm]) fun i => piInf (B.emb w) (a i)
  choose q hq using fun w => cartan_pos (hW.cartan w) (fun i j => by
    rw [Matrix.smul_apply, Matrix.smul_apply, Matrix.map_apply, Matrix.map_apply, smul_eq_mul, star_mul', ← hB.cm.2.2.2, hW.skew]
    simp) fun i => (B.emb w).1 (b i)
  have hq' : ∀ w, 0 < q w := fun w => (hq w).2.2 fun h0 => hb (funext fun i => (B.emb w).1.injective
    ((congrFun h0 i).trans (map_zero _).symm))
  refine ⟨fun w => 2 * p w * q w, ?_, fun w => ⟨fun h0 => by simp [(hp w).2.1 h0],
    fun h0 => mul_pos (mul_pos two_pos ((hp w).2.2 h0)) (hq' w)⟩⟩
  rw [omega_eq hB]
  refine Finset.sum_congr rfl fun w _ => ?_
  have e1 : (Matrix.vecMulVec a (incV F b)).map (piInf (B.emb w)) =
      Matrix.vecMulVec (fun i => piInf (B.emb w) (a i)) fun i => (B.emb w).1 (b i) := by
    ext i j
    simp only [Matrix.map_apply, Matrix.vecMulVec_apply, map_mul, incV, piInf_inclR]
  have e2 : ∀ (J : Matrix (Fin n) (Fin n) ℂ) (J' : Matrix (Fin d) (Fin d) ℂ) x x' y y',
      hTens cj J J' (Matrix.vecMulVec x y) (Matrix.vecMulVec x' y') = (x ⬝ᵥ J *ᵥ star x') * (y ⬝ᵥ J' *ᵥ star y') := by
    intro J J' x x' y y'
    simp only [hTens, dotProduct, Matrix.mulVec, Matrix.vecMulVec_apply, map_mul, Pi.star_apply]
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
    change _ * (star _ * star _) = _
    ring
  have h1 := (hq w).1
  rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul] at h1
  rw [h w, e1, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.vecMul_transpose, ← one_smul ℂ (Matrix.vecMulVec _ _),
    hTens_smul, e2, (hp w).1]
  generalize (fun i => (B.emb w).1 (b i)) ⬝ᵥ _ = t at h1
  have h4 : -(1 * star (((e w : ℤ) : ℂ) * Complex.I) * (p w * t)) = ((((e w : ℤ) : ℝ) * (p w * q w) : ℝ) : ℂ) := by
    simp only [star_mul, Complex.star_def, Complex.conj_I, map_intCast]
    push_cast
    rw [← h1]
    ring
  rw [h4, Complex.ofReal_re]
  ring

end PositivityTheory.ThKF0
end
end

-- bundled from Development.WeilBound.ThetaLifts.LeviDeterminants.EvModel
section
noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace PositivityTheory.ThKF0

open PositivityTheory.Mix.Adapt

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁} {κ₀ : Type} [Fintype κ₀]
  (ε : Fin n × Fin d ≃ κ₀ ⊕ Fin n₁ × Fin d₁)

theorem exists_isEvS (B : Base F E) (Ma : Model σ X W) (M₁ : Model σ X₁ W₁)
    (p q : Matrix (Fin n) (Fin d) (AE F E) → κ₀ → AF F) (π : Matrix (Fin n) (Fin d) (AE F E) → Matrix (Fin n₁) (Fin d₁) (AE F E))
    (hco : ∀ z, Ma.co.e z = (glue ε (p z) (M₁.co.e (π z)).1, glue ε (q z) (M₁.co.e (π z)).2))
    (ι : Matrix (Fin n) (Fin n₁) E) (ι' : Matrix (Fin d) (Fin d₁) E) (I : Set (Matrix (Fin n) (Fin d) (AE F E)))
    (hj : ∀ z, p (incM F ι * z * (incM F ι')ᵀ) = 0 ∧ π (incM F ι * z * (incM F ι')ᵀ) = z)
    (hI : ∀ u ∈ I, p u = 0 ∧ π u = 0) (hvac : ∀ v b, Ma.vac v (glue ε 0 b) = M₁.vac v b) :
    ∃ e, IsEv B Ma M₁ ι ι' I e ∧ ∃ T : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n₁ × Fin d₁), (∀ f b, T f b = f (glue ε 0 b)) ∧
      ∃ ev : ∀ v : Pl F, ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Fin n₁ × Fin d₁ → Fv F v) → ℂ,
        (∀ v, ev v (Ma.vac v) = M₁.vac v ∧ (SB _).map (ev v) = SB _) ∧
        ∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = Ma.vac v) →
          e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (T f) fun v => ev v (φ v) := by
  classical
  obtain ⟨T, hT⟩ := exists_slice ε (0 : κ₀ → mixedEmbedding.mixedSpace F)
  suffices h : _ ∧ _ ∧ _ ∧ T ≠ 0 ∧ _ from
    ⟨LinearMap.funLeft ℂ ℂ fun b => glue ε 0 b, ⟨h.1, h.2.1, h.2.2.1, T, fun v => LinearMap.funLeft ℂ ℂ fun b => glue ε 0 b,
      h.2.2.2.1, h.2.2.2.2⟩, T, hT, _, h.2.2.2.2⟩
  refine ⟨fun Φ hΦ => slice_mem_schA ε 0 hΦ, fun z Φ _ => ?_, fun u hu Φ _ => ?_, ?_⟩
  · funext b
    simp only [LinearMap.funLeft_apply, Darboux.rho, schr, hco, (hj z).1, (hj z).2, glue_dot, glue_add, zero_dotProduct,
      zero_add]
  · funext b
    simp only [LinearMap.funLeft_apply, Darboux.rho, schr, hco, (hI u hu).1, (hI u hu).2, glue_dot, glue_add,
      zero_dotProduct, map_zero, Prod.fst_zero, Prod.snd_zero, add_zero, dotProduct_zero, mul_zero,
      AddChar.map_zero_eq_one, one_mul]
  · refine ⟨fun h => ?_, fun v => ⟨funext (hvac v), ?_⟩,
      fun f φ _ _ => ?_⟩
    · obtain ⟨f, hf⟩ := exists_schwartz_ne (Fin n × Fin d → mixedEmbedding.mixedSpace F)
      have := hT f 0
      rw [h, glue_zero] at this
      exact hf this.symm
    · refine le_antisymm ?_ fun φ hφ => ?_
      · rintro _ ⟨g, hg, rfl⟩
        exact slice_mem_SB ε 0 hg
      · have h1 : IsOpen (Set.univ.pi fun _ : κ₀ => (v.adicCompletionIntegers F : Set (Fv F v))) :=
          isOpen_set_pi Set.finite_univ fun _ _ => Valued.isOpen_valuationSubring _
        have h2 : IsCompact (Set.univ.pi fun _ : κ₀ => (v.adicCompletionIntegers F : Set (Fv F v))) :=
          isCompact_univ_pi fun _ => PI.AdicCompletionValuation.isCompact_adicCompletionIntegers F v
        refine ⟨_, box_mem_SB ε h1 h2 hφ, funext fun b => ?_⟩
        rw [LinearMap.funLeft_apply, box_glue, Set.indicator_of_mem (by exact fun _ _ => zero_mem _), Pi.one_apply, one_mul]
    · funext b
      simp only [LinearMap.funLeft_apply, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, hT]
      rw [glue_map ε (evI F)]
      congr 1
      · congr 2
        funext k
        exact map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)
      · refine finprod_congr fun v => ?_
        rw [glue_map ε (evFin F v)]
        simp only [Pi.zero_apply, map_zero]
        rfl

theorem exists_modelS {B : Base F E} {r s r' s' : ℕ} (hB : B.IsGood σ) (hX : X.IsHerm σ B r s) (hW : W.IsSkew σ B r' s')
    {M : Model σ X W} (hM : M.IsGood B.ψ) {M₁ : Model σ X₁ W₁} (hM₁ : M₁.IsGood B.ψ) {κ : Type} [Fintype κ]
    (hcard : n * d = Fintype.card κ * 2 + n₁ * d₁) (b D : Matrix (Fin n) (Fin d) (AE F E) → κ → AE F E)
    (π : Matrix (Fin n) (Fin d) (AE F E) → Matrix (Fin n₁) (Fin d₁) (AE F E)) (hb : IsLinearMap (AF F) b)
    (hD : IsLinearMap (AF F) D) (hπ : IsLinearMap (AF F) π)
    (hH : ∀ z z', hTens (cA σ) (incM F X.J) (incM F W.J) z z' =
      b z ⬝ᵥ D z' - cA σ (b z' ⬝ᵥ D z) + hTens (cA σ) (incM F X₁.J) (incM F W₁.J) (π z) (π z'))
    (hrat : ∀ x, (∃ y : κ → E, b (incM F x) = fun k => inclR (F := F) (AF F) (y k)) ∧
      (∃ y : κ → E, D (incM F x) = fun k => inclR (F := F) (AF F) (y k)) ∧ ∃ x₁, π (incM F x) = incM F x₁)
    (ι : Matrix (Fin n) (Fin n₁) E) (ι' : Matrix (Fin d) (Fin d₁) E) (I : Set (Matrix (Fin n) (Fin d) (AE F E)))
    (hj : ∀ z, b (incM F ι * z * (incM F ι')ᵀ) = 0 ∧ π (incM F ι * z * (incM F ι')ᵀ) = z)
    (hI : ∀ u ∈ I, b u = 0 ∧ π u = 0)
    (hlat : ∀ v, ∀ γ ∈ latAtV X W v, π γ ∈ latAtV X₁ W₁ v ∧ ∃ δ ∈ latAtV X W v, b δ = 0 ∧ π δ = 0 ∧ D δ = D γ) :
    ∃ (ε : Fin n × Fin d ≃ (κ × Fin 2) ⊕ Fin n₁ × Fin d₁) (Ma : Model σ X W) (e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁)
      (p q : Matrix (Fin n) (Fin d) (AE F E) → κ × Fin 2 → AF F), Ma.IsGood B.ψ ∧
      (∀ z, Ma.co.e z = (glue ε (p z) (M₁.co.e (π z)).1, glue ε (q z) (M₁.co.e (π z)).2)) ∧ (∀ z, b z = 0 → p z = 0) ∧
      (∀ z, D z = 0 → q z = 0) ∧ IsEv B Ma M₁ ι ι' I e ∧
      ∃ T : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n₁ × Fin d₁), (∀ f b, T f b = f (glue ε 0 b)) ∧
      ∃ ev : ∀ v : Pl F, ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Fin n₁ × Fin d₁ → Fv F v) → ℂ,
        (∀ v, ev v (Ma.vac v) = M₁.vac v ∧ (SB _).map (ev v) = SB _) ∧
        ∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = Ma.vac v) →
          e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (T f) fun v => ev v (φ v) := by
  classical
  let ε : Fin n × Fin d ≃ (κ × Fin 2) ⊕ Fin n₁ × Fin d₁ := Fintype.equivOfCardEq (by simp [hcard])
  let β := Module.finBasisOfFinrankEq F E hB.cm.2.2.1
  let βA := Algebra.TensorProduct.basis (AF F) β
  let Tr := Algebra.trace (AF F) (AE F E)
  let p : Matrix (Fin n) (Fin d) (AE F E) → κ × Fin 2 → AF F := fun z k => βA.repr (b z k.1) k.2
  let q : Matrix (Fin n) (Fin d) (AE F E) → κ × Fin 2 → AF F := fun z k => -Tr (βA k.2 * D z k.1)
  have hpq : ∀ z z', p z ⬝ᵥ q z' = -Tr (b z ⬝ᵥ D z') := fun z z' => by
    simp only [dotProduct, Fintype.sum_prod_type, map_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    conv_rhs => rw [← βA.sum_repr (b z k), Finset.sum_mul, map_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_mul_assoc, map_smul, smul_eq_mul, ← mul_neg]
  have hTr : ∀ z, Tr (cA σ z) = Tr z := GlobalTheory.VacCocycle.trace_conj (cA σ) (cA_cA hB)
  let Φ : Matrix (Fin n) (Fin d) (AE F E) →ₗ[AF F] (Fin n × Fin d → AF F) × (Fin n × Fin d → AF F) :=
    { toFun := fun z => (glue ε (p z) (M₁.co.e (π z)).1, glue ε (q z) (M₁.co.e (π z)).2)
      map_add' := fun z z' => by
        rw [Prod.mk_add_mk, glue_add, glue_add, hπ.map_add, map_add]
        congr 2 <;> funext k <;> simp [p, q, hb.map_add, hD.map_add, mul_add, add_comm]
      map_smul' := fun c z => by
        rw [Prod.smul_mk, glue_smul, glue_smul, hπ.map_smul, map_smul]
        congr 2 <;> funext k <;> simp [p, q, hb.map_smul, hD.map_smul] }
  have hΦ : ∀ z z', symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J) z z' =
      (Φ z).1 ⬝ᵥ (Φ z').2 - (Φ z').1 ⬝ᵥ (Φ z).2 := fun z z' => by
    have h1 := M₁.co.form (π z) (π z')
    show Tr _ = glue ε _ _ ⬝ᵥ glue ε _ _ - glue ε _ _ ⬝ᵥ glue ε _ _
    change Tr _ = _ at h1
    rw [glue_dot, glue_dot, hpq, hpq, hH, mul_add, map_add, h1, neg_one_mul, map_neg, map_sub, hTr]
    ring
  have hbij : Function.Bijective Φ := by
    have := (bijective_of_symp (Φ ∘ₗ M.co.e.symm.toLinearMap) fun u w => by
      have h1 := M.co.form (M.co.e.symm u) (M.co.e.symm w)
      rw [hΦ, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at h1
      exact h1).comp M.co.e.bijective
    convert this using 1
    funext z
    simp
  let co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J)) (Fin n × Fin d) :=
    ⟨LinearEquiv.ofBijective Φ hbij, hΦ⟩
  have hco : ∀ z, co.e z = (glue ε (p z) (M₁.co.e (π z)).1, glue ε (q z) (M₁.co.e (π z)).2) := fun z => rfl
  have hr : ∀ x : Matrix (Fin n) (Fin d) E, ∃ y z : Fin n × Fin d → F,
      co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i)) := fun x => by
    obtain ⟨⟨y, hy⟩, ⟨y', hy'⟩, x₁, hx₁⟩ := hrat x
    obtain ⟨u, w, huw⟩ := hM₁.rat x₁
    refine ⟨glue ε (fun k => β.repr (y k.1) k.2) u, glue ε (fun k => -Algebra.trace F E (β k.2 * y' k.1)) w, ?_⟩
    rw [hco, hx₁, huw, glue_map ε (algebraMap F (AF F)), glue_map ε (algebraMap F (AF F))]
    congr 2 <;> funext k
    · simp only [p, hy]
      show βA.repr ((1 : AF F) ⊗ₜ[F] y k.1) k.2 = _
      simp [βA, Algebra.TensorProduct.basis_repr_tmul]
    · simp only [q, hy']
      rw [map_neg, ← GlobalTheory.VacIndic.trace_inclR, map_mul (inclR (F := F) (AF F)), Algebra.TensorProduct.basis_apply]
      rfl
  have hδ : ∀ v, ∀ γ ∈ latAtV X W v, ∀ γ' ∈ latAtV X W v, ∀ θ : 𝓞 E,
      B.ψ (Tr (inclR (F := F) (AF F) (θ : E) * (b γ' ⬝ᵥ D γ))) = 1 := fun v γ hγ γ' hγ' θ => by
    obtain ⟨-, δ, h0, h1, h2, h3⟩ := hlat v γ hγ
    have := GlobalTheory.LatVacArith.psi_symp_latAtV σ B X W r s r' s' hB hX hW v θ 1 (by rw [map_one]; exact one_mem _) γ' hγ' δ h0
    rw [one_mul, symp, hH, h1, h2, h3] at this
    simpa [hTens] using this
  have hv : ∀ v, ∃ φa, Model.IsVac (⟨co, fun _ => 0, 0, ∅⟩ : Model σ X W) B.ψ v φa ∧ ∀ c, φa (glue ε 0 c) = M₁.vac v c := by
    intro v
    refine exists_isVac ε hX hW _ M₁ hr p q π hco v (fun γ hγ => (hlat v γ hγ).1) (fun γ hγ γ' hγ' => ?_)
      (fun θ hθ γ hγ => ?_) (hM₁.vac v)
    · have := hδ v γ hγ γ' hγ' (-1)
      rw [show ((-1 : 𝓞 E) : E) = -1 by simp, map_neg, map_one, neg_one_mul, map_neg] at this
      rw [hpq, this]
    · rw [← one_mul (B.ψ _ * B.ψ _), ← hδ v γ hγ γ hγ θ]
      simp only [← AddChar.map_add_eq_mul]
      congr 1
      have h1 : inclR (F := F) (AF F) (θ : E) + cA σ (inclR (F := F) (AF F) (θ : E)) = 1 := by
        rw [GlobalTheory.VacIndic.cA_inclR, ← map_add, hθ, map_one]
      have h2 : Tr (inclR (F := F) (AF F) (θ : E) * cA σ (b γ ⬝ᵥ D γ)) =
          Tr (b γ ⬝ᵥ D γ) - Tr (inclR (F := F) (AF F) (θ : E) * (b γ ⬝ᵥ D γ)) := by
        rw [← hTr, map_mul, cA_cA hB, ← map_sub, eq_sub_of_add_eq' h1, sub_mul, one_mul]
      have h3 : (⅟(2 : AF F)) * 2 = 1 := invOf_mul_self _
      show _ * Tr _ = _ + (_ + _ * Tr _)
      rw [hpq, hH, mul_add (inclR (F := F) (AF F) (θ : E)), mul_sub, map_add, map_sub, h2]
      generalize (⅟(2 : AF F)) = t at h3 ⊢
      linear_combination (Tr (inclR (F := F) (AF F) (θ : E) * (b γ ⬝ᵥ D γ))) * h3
  choose φa hφa hφb using hv
  let S : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ := fun v => Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1
  let G : Pl F → Prop := fun v => Model.IsVac (⟨co, fun _ => 0, 0, ∅⟩ : Model σ X W) B.ψ v (S v) ∧
    M₁.vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1
  let Ma : Model σ X W := ⟨co, fun v => if G v then S v else φa v, M.μ, M.dom⟩
  obtain ⟨e, he⟩ := exists_isEvS ε B Ma M₁ p q π hco ι ι' I
    (fun z => ⟨funext fun k => by simp [p, (hj z).1], (hj z).2⟩)
    (fun u hu => ⟨funext fun k => by simp [p, (hI u hu).1], (hI u hu).2⟩) fun v c => by
      by_cases h : G v
      · show (if G v then S v else φa v) _ = _
        rw [if_pos h, h.2]
        refine Set.indicator_eq_indicator ⟨fun hx i => ?_, fun hx i => ?_⟩ rfl
        · simpa using hx (ε.symm (.inr i))
        · obtain ⟨i, rfl⟩ := ε.symm.surjective i
          rcases i with i | i
          · rw [glue_inl]; exact zero_mem _
          · rw [glue_inr]; exact hx i
      · show (if G v then S v else φa v) _ = _
        rw [if_neg h, hφb]
  refine ⟨ε, Ma, e, p, q, ⟨hr, fun v => ?_, ?_, hM.haar, hM.dom⟩, hco, fun z h => funext fun k => by simp [p, h],
    fun z h => funext fun k => by simp [q, h], he⟩
  · show Model.IsVac _ _ _ (if G v then S v else φa v)
    split_ifs with h
    · exact h.1
    · exact hφa v
  · filter_upwards [GlobalTheory.VacIndic.eventually_isVac_indicator B hB X W r s r' s' hX hW co hr, hM₁.std] with v h1 h2
    exact if_pos ⟨h1, h2⟩

end PositivityTheory.ThKF0
end
end

-- bundled from Development.WeilBound.ThetaLifts.LeviDeterminants.ThetaSumInvariantRationalUnitary
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix

noncomputable section
namespace PositivityTheory.ThKF0

theorem rat_det_ne_zero_of_hasSig {n r s : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (h : HasSig M r s) : M.det ≠ 0 := by
  obtain ⟨hrs, A, hA⟩ := h
  let e : Fin r ⊕ Fin s ≃ Fin n := finSumFinEquiv.trans (finCongr hrs)
  have key : (A.submatrix id e.symm)ᵀ * M * (A.submatrix id e.symm).map star =
      (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℂ) 0 0 (-1)).submatrix e.symm e.symm := by
    rw [← hA, Matrix.submatrix_mul _ _ _ id _ Function.bijective_id,
      Matrix.submatrix_mul Aᵀ M e.symm id id Function.bijective_id]
    simp [Matrix.transpose_submatrix, Matrix.submatrix_map]
  intro h0
  have := congrArg Matrix.det key
  rw [Matrix.det_mul, Matrix.det_mul, h0, Matrix.det_submatrix_equiv_self] at this
  simp [Matrix.det_fromBlocks_zero₂₁, Matrix.det_neg] at this
  exact pow_ne_zero s (by norm_num : (-1 : ℂ) ≠ 0) this.symm

theorem rat_det_ne_zero_of_map {E : Type} [Field E] {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (f : E →+* ℂ)
    (h : (J.map f).det ≠ 0) : J.det ≠ 0 := by
  intro h0
  apply h
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]

theorem theta_sum_rational_invariance : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ γ ∈ ratU σ X.J, ∀ γ' ∈ ratU σ W.J, ∀ Φ ∈ schA F (Fin n × Fin d), thetaSum F (om (γ, γ') Φ) = thetaSum F Φ := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP γ hγ γ' hγ' Φ hΦ
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace F))
  have hX : X.J.det ≠ 0 := rat_det_ne_zero_of_map X.J (B.emb w).1 (rat_det_ne_zero_of_hasSig _ (hP.herm.sig w))
  have hW : W.J.det ≠ 0 := by
    refine rat_det_ne_zero_of_map W.J (B.emb w).1 fun h0 => rat_det_ne_zero_of_hasSig _ (hP.skew.sig w) ?_
    rw [Matrix.det_smul, h0, mul_zero]
  exact darboux_coordinates_rational_exist F E σ hP.base.cm B.ψ hP.base.std n d X.J W.J hP.herm.herm hX hP.skew.skew hW M.co
    hP.good.rat χX χW hP.hX hP.hW om hP.weil γ hγ γ' hγ' Φ hΦ

end PositivityTheory.ThKF0
end
end

