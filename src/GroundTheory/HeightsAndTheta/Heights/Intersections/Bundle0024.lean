import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0014
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0018
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0013
import GroundTheory.HeightsAndTheta.Heights.Intersections.PRFormula
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0011
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0018

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.PChartFormsRational
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ChartDualRational

noncomputable section

theorem ChartFormsRational.mem_of_mem_chartRing {Ω : Type*} [Field Ω] {ι : Type*} (x : ι → Ω) (i : ι) {a : Ω}
    (ha : a ∈ chartRing ℤ x i) : a ∈ chartFunField x i := by
  induction ha using Algebra.adjoin_induction with
  | mem y hy => exact Subfield.subset_closure hy
  | algebraMap r =>
    rw [eq_intCast]
    exact intCast_mem _ r
  | add y z _ _ hy hz => exact add_mem hy hz
  | mul y z _ _ hy hz => exact mul_mem hy hz

theorem ChartFormsRational.proof : ChartFormsRational.Statement := by
  intro Ω _ ι ν κ _ _ _ E _ _ x B e φ δ hsec hgen hδ i hx
  set K := chartFunField x i with hKdef
  have hR : ∀ a ∈ chartRing ℤ x i, a ∈ K := fun a ha ↦ ChartFormsRational.mem_of_mem_chartRing x i ha
  obtain ⟨r, f, c, hf, hc, hsum, hfr⟩ := B.frame i hx
  choose b hbli hbsp hbiff using hfr
  obtain ⟨lf, hlf⟩ : ∃ l, f l ≠ 0 := by
    by_contra h
    push Not at h
    simp [h] at hsum
  have hn1 : ∀ l p, ∃ m : ℕ, f l ^ m • b l p ∈ B.lat i := fun l p ↦
    (hbiff l (b l p)).2 ⟨Pi.single p 1, fun q ↦ ⟨0, by by_cases hq : q = p <;> simp [hq, one_mem, zero_mem]⟩,
      by simp [Pi.single_apply]⟩
  choose n hn using fun l ↦ exists_uniform (fun p m ↦ f l ^ m • b l p ∈ B.lat i)
    (fun p m m' hmm' h ↦ by
      rw [← pow_mul_pow_sub (f l) hmm', mul_comm, mul_smul]
      exact B.stable i _ (pow_mem (hf l) _) _ h) (hn1 l)
  obtain ⟨bb, hbb⟩ : ∃ bb : Module.Basis (Fin 2) Ω E, ∀ q, bb q = b lf q :=
    ⟨Module.Basis.mk (hbli lf) (hbsp lf).ge, fun q ↦ by simp⟩
  have hcoord : ∀ v ∈ B.lat i, ∀ q, ∃ t : ℕ, f lf ^ t * bb.coord q v ∈ chartRing ℤ x i := by
    intro v hv q
    obtain ⟨a, ha, rfl⟩ := (hbiff lf v).1 ⟨0, by simpa using hv⟩
    obtain ⟨t, ht⟩ := ha q
    refine ⟨t, ?_⟩
    have : bb.coord q (∑ p, a p • b lf p) = a q := by
      fin_cases q <;> simp [← hbb, Module.Basis.coord_apply, Module.Basis.repr_self]
    rwa [this]
  obtain ⟨M, hM⟩ := exists_uniform
    (fun (a : Fin r × Fin 2 × Fin 2) t ↦ f lf ^ t * bb.coord a.2.2 (f a.1 ^ n a.1 • b a.1 a.2.1) ∈ chartRing ℤ x i)
    (fun _ _ _ h h' ↦ pow_mul_mem_mono (hf lf) h h') (fun a ↦ hcoord _ (hn a.1 a.2.1) _)
  have hdual : ∀ q, f lf ^ M • bb.coord q ∈ T.dualLat B i := by
    intro q
    simp only [T.dualLat, Set.mem_ofPred_eq]
    intro v hv
    rw [LinearMap.smul_apply, smul_eq_mul]
    refine mem_of_cover hf hc hsum fun l ↦ ?_
    obtain ⟨a, ha, rfl⟩ := (hbiff l v).1 ⟨0, by simpa using hv⟩
    obtain ⟨m, hm⟩ := exists_uniform (fun p t ↦ f l ^ t * a p ∈ chartRing ℤ x i)
      (fun p _ _ h h' ↦ pow_mul_mem_mono (hf l) h h') ha
    refine ⟨m + n l, ?_⟩
    have : f l ^ (m + n l) * (f lf ^ M * bb.coord q (∑ p, a p • b l p)) =
        ∑ p, (f l ^ m * a p) * (f lf ^ M * bb.coord q (f l ^ n l • b l p)) := by
      simp only [map_sum, map_smul, smul_eq_mul, Finset.mul_sum, pow_add]
      exact Finset.sum_congr rfl fun p _ ↦ by ring
    rw [this]
    exact sum_mem fun p _ ↦ mul_mem (hm p) (hM (l, p, q))
  choose d hdR hd using fun q ↦ hgen i hx _ (hdual q)

  obtain ⟨g, hgdef⟩ : ∃ g : κ → Fin 2 → Ω, ∀ k q, g k q = φ k (bb q) / x i := ⟨_, fun _ _ ↦ rfl⟩
  have hφg : ∀ k q, φ k (bb q) = x i * g k q := fun k q ↦ by rw [hgdef]; field_simp
  have hfK : f lf ∈ K := hR _ (hf lf)
  have hgK : ∀ k q, g k q ∈ K := by
    intro k q
    have hs : f lf ^ n lf • bb q ∈ B.lat i := by rw [hbb]; exact hn lf q
    obtain ⟨a, ha, hae⟩ := (mem_lineLat x 1 i _).1 (hsec i hx k _ hs)
    rw [map_smul, smul_eq_mul, pow_one] at hae
    have : g k q = a / f lf ^ n lf := by
      rw [hgdef, div_eq_div_iff hx (pow_ne_zero _ hlf), hae]
      ring
    rw [this]
    exact div_mem (hR _ ha) (pow_mem hfK _)
  obtain ⟨k₀, k₁, hm⟩ : ∃ k₀ k₁, g k₀ 0 * g k₁ 1 - g k₀ 1 * g k₁ 0 ≠ 0 := by
    by_contra hmin
    push Not at hmin
    have hrow : ∀ q p, ∑ k, d q k * g k p = f lf ^ M * if p = q then 1 else 0 := by
      intro q p
      have h := LinearMap.congr_fun (hd q) (bb p)
      simp only [LinearMap.smul_apply, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply,
        LinearMap.sum_apply, smul_eq_mul] at h
      rw [h]
      exact Finset.sum_congr rfl fun k _ ↦ by rw [hgdef]; ring
    have hdet : (∑ k, d 0 k * g k 0) * (∑ k, d 1 k * g k 1) - (∑ k, d 0 k * g k 1) * (∑ k, d 1 k * g k 0) = 0 := by
      rw [Finset.sum_mul_sum, Finset.sum_mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_eq_zero fun k _ ↦ ?_
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_eq_zero fun k' _ ↦ ?_
      linear_combination (d 0 k * d 1 k') * hmin k k'
    rw [hrow 0 0, hrow 1 1, hrow 0 1, hrow 1 0] at hdet
    simp [hlf] at hdet
  set m := g k₀ 0 * g k₁ 1 - g k₀ 1 * g k₁ 0 with hmdef
  have hmK : m ∈ K := sub_mem (mul_mem (hgK _ _) (hgK _ _)) (mul_mem (hgK _ _) (hgK _ _))

  set Db := T.detE e (bb 0) (bb 1) with hDbdef
  have hDb : Db ≠ 0 := ChartDetRatio.detE_ne_zero e bb bb.linearIndependent (by rw [bb.span_eq])
  have hexp : ∀ k q, φ k (bb q) = e.repr (bb q) 0 * φ k (e 0) + e.repr (bb q) 1 * φ k (e 1) := by
    intro k q
    have h := congrArg (φ k) (e.sum_repr (bb q))
    rw [Fin.sum_univ_two, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul] at h
    exact h.symm
  have hDD : (φ k₀ (e 0) * φ k₁ (e 1) - φ k₁ (e 0) * φ k₀ (e 1)) * Db = x i ^ 2 * m := by
    have h2 : x i ^ 2 * m = φ k₀ (bb 0) * φ k₁ (bb 1) - φ k₀ (bb 1) * φ k₁ (bb 0) := by
      rw [hmdef, hφg k₀ 0, hφg k₁ 1, hφg k₀ 1, hφg k₁ 0]
      ring
    rw [h2, hexp k₀ 0, hexp k₁ 1, hexp k₀ 1, hexp k₁ 0, hDbdef, T.detE]
    ring
  have hDne : φ k₀ (e 0) * φ k₁ (e 1) - φ k₁ (e 0) * φ k₀ (e 1) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hDD
    exact mul_ne_zero (pow_ne_zero 2 hx) hm hDD.symm

  have hcoordK : ∀ u ∈ B.lat i, ∃ a : Fin 2 → Ω, (∀ q, a q ∈ K) ∧ u = ∑ q, a q • bb q := by
    intro u hu
    obtain ⟨a, ha, rfl⟩ := (hbiff lf u).1 ⟨0, by simpa using hu⟩
    refine ⟨a, fun q ↦ ?_, by simp only [hbb]⟩
    obtain ⟨t, ht⟩ := ha q
    have h2 : a q = (f lf ^ t)⁻¹ * (f lf ^ t * a q) := by
      rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hlf), one_mul]
    rw [h2]
    exact mul_mem (inv_mem (pow_mem hfK t)) (hR _ ht)
  have hdet : ∀ u ∈ B.lat i, ∀ w ∈ B.lat i, ∃ s ∈ K, T.detE e u w = Db * s := by
    intro u hu w hw
    obtain ⟨a, ha, rfl⟩ := hcoordK u hu
    obtain ⟨a', ha', rfl⟩ := hcoordK w hw
    refine ⟨a 0 * a' 1 - a 1 * a' 0, sub_mem (mul_mem (ha 0) (ha' 1)) (mul_mem (ha 1) (ha' 0)), ?_⟩
    rw [ChartDetRatio.detE_sum, mul_comm]
  have hspan : ∀ y ∈ Submodule.span (chartRing ℤ x i)
      {d | ∃ u ∈ B.lat i, ∃ w ∈ B.lat i, d = x i * T.detE e u w}, ∃ s ∈ K, y = x i * Db * s := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨u, hu, w, hw, rfl⟩ := hy
      obtain ⟨s, hs, h⟩ := hdet u hu w hw
      exact ⟨s, hs, by rw [h]; ring⟩
    | zero => exact ⟨0, zero_mem _, by ring⟩
    | add y z _ _ hy hz =>
      obtain ⟨s, hs, rfl⟩ := hy
      obtain ⟨t, ht, rfl⟩ := hz
      exact ⟨s + t, add_mem hs ht, by ring⟩
    | smul a y _ hy =>
      obtain ⟨s, hs, rfl⟩ := hy
      refine ⟨(a : Ω) * s, mul_mem (hR _ a.2) hs, ?_⟩
      rw [Subalgebra.smul_def, smul_eq_mul]
      ring
  have hδs : ∀ l, ∃ s ∈ K, δ l = x i * Db * s := fun l ↦ hspan _ ((hδ i hx).1 l)
  have h0 : f lf ^ n lf • bb 0 ∈ B.lat i := by rw [hbb]; exact hn lf 0
  have h1 : f lf ^ n lf • bb 1 ∈ B.lat i := by rw [hbb]; exact hn lf 1
  obtain ⟨l₀, hl₀⟩ : ∃ l₀, δ l₀ ≠ 0 := by
    by_contra h
    push Not at h
    have hmem := (hδ i hx).2 _ h0 _ h1
    have hbot : Submodule.span (chartRing ℤ x i) (Set.range fun l ↦ (x i)⁻¹ * δ l) = ⊥ := by
      rw [Submodule.span_eq_bot]
      rintro _ ⟨l, rfl⟩
      simp [h l]
    rw [hbot, Submodule.mem_bot] at hmem
    have hsm : T.detE e (f lf ^ n lf • bb 0) (f lf ^ n lf • bb 1) = f lf ^ n lf * f lf ^ n lf * Db := by
      simp only [T.detE, map_smul, Finsupp.smul_apply, smul_eq_mul, hDbdef]
      ring
    rw [hsm] at hmem
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ hlf) (pow_ne_zero _ hlf)) hDb hmem
  obtain ⟨s₀, hs₀, hδ₀⟩ := hδs l₀
  have hs₀ne : s₀ ≠ 0 := by
    rintro rfl
    exact hl₀ (by rw [hδ₀, mul_zero])
  refine ⟨l₀, k₀, k₁, hl₀, hDne, fun l ↦ ?_, ?_, ?_⟩
  · obtain ⟨s, hs, hδl⟩ := hδs l
    rw [hδl, hδ₀, mul_div_mul_left _ _ (mul_ne_zero hx hDb)]
    exact div_mem hs hs₀
  ·
    refine ⟨fun k ↦ (g k 0 * g k₁ 1 - g k 1 * g k₁ 0) / m, fun k ↦ (g k₀ 0 * g k 1 - g k₀ 1 * g k 0) / m,
      fun k ↦ div_mem (sub_mem (mul_mem (hgK _ _) (hgK _ _)) (mul_mem (hgK _ _) (hgK _ _))) hmK,
      fun k ↦ div_mem (sub_mem (mul_mem (hgK _ _) (hgK _ _)) (mul_mem (hgK _ _) (hgK _ _))) hmK, fun k ↦ ?_⟩
    have key : ∀ q : Fin 2, g k q = (g k 0 * g k₁ 1 - g k 1 * g k₁ 0) / m * g k₀ q +
        (g k₀ 0 * g k 1 - g k₀ 1 * g k 0) / m * g k₁ q := by
      rw [Fin.forall_fin_two]
      constructor <;>
        (rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, eq_div_iff hm, hmdef]; ring)
    refine bb.ext fun q ↦ ?_
    simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    rw [hφg k q, hφg k₀ q, hφg k₁ q, key q]
    ring
  · have : (φ k₀ (e 0) * φ k₁ (e 1) - φ k₁ (e 0) * φ k₀ (e 1)) * δ l₀ / x i ^ 3 = m * s₀ := by
      rw [hδ₀, show (φ k₀ (e 0) * φ k₁ (e 1) - φ k₁ (e 0) * φ k₀ (e 1)) * (x i * Db * s₀) =
        (φ k₀ (e 0) * φ k₁ (e 1) - φ k₁ (e 0) * φ k₀ (e 1)) * Db * x i * s₀ by ring, hDD,
        div_eq_iff (pow_ne_zero 3 hx)]
      ring
    rw [this]
    exact mul_mem hmK hs₀

end

end GroundTheory.Heights₂.Heights.Inter
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.PDiagOrd
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI

noncomputable section

namespace DiagonalOrder

section Orders

variable {K : Type} {ι : K → Type}

theorem multAt_eq_zero_of_not_le {J W : Ideal (MRing ι)} (hW : W.IsPrime) (h : ¬ J ≤ W) : multAt J W = 0 := by
  have := hW
  unfold multAt
  rw [dif_pos hW, Module.length_eq_zero_iff.mpr (NumbersDVR.localizedQuot_subsingleton_of_not_le _ W h)]
  rfl

theorem multAt_sup_span_eq {P W : Ideal (MRing ι)} [P.IsPrime] (hW : W.IsPrime) (hPW : P ≤ W)
    {g h u v : MRing ι} (hu : u ∉ W) (hv : v ∉ W) (hm : u * g - v * h ∈ P) :
    multAt (P ⊔ Ideal.span {g}) W = multAt (P ⊔ Ideal.span {h}) W := by
  have := hW
  have hlen : ∀ {s w : MRing ι}, w ∉ W →
      Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (MRing ι ⧸ (P ⊔ Ideal.span {w * s}))) =
        Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (MRing ι ⧸ (P ⊔ Ideal.span {s}))) := by
    intro s w hw
    rw [NumbersDVR.length_localizedQuot_sup_span_mul P W s (fun h' => hw (hPW h')),
      Module.length_eq_zero_iff.mpr (NumbersDVR.localizedQuot_subsingleton_of_not_le _ W
        (fun hle => hw (hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self w))))), add_zero]
  have heq : P ⊔ Ideal.span {u * g} = P ⊔ Ideal.span {v * h} := by
    apply le_antisymm
    · refine sup_le le_sup_left ((Ideal.span_singleton_le_iff_mem _).mpr ?_)
      have e : u * g = (u * g - v * h) + v * h := by ring
      rw [e]
      exact Ideal.add_mem _ (Ideal.mem_sup_left hm) (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
    · refine sup_le le_sup_left ((Ideal.span_singleton_le_iff_mem _).mpr ?_)
      have e : v * h = u * g - (u * g - v * h) := by ring
      rw [e]
      exact Ideal.sub_mem _ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)) (Ideal.mem_sup_left hm)
  unfold multAt
  rw [dif_pos hW, dif_pos hW, ← hlen (s := g) hu, heq, hlen hv]

end Orders

section Diagonal

variable {Ω : Type} [Field Ω] {ι ν κ : Type} [Fintype ι] [Fintype ν] [Fintype κ] {E : Type} [AddCommGroup E]
  [Module Ω E] {Φ : Type} [Field Φ] [Algebra Ω Φ]

def polyCoord (x : ι → Ω) (δ : ν → Ω) (e : Module.Basis (Fin 2) Ω E) (φ : κ → E →ₗ[Ω] Ω) :
    (Σ k, T.wwIdx ι ν κ k) → MvPolynomial (Fin 2) Ω
  | ⟨.base, i⟩ => C (x i)
  | ⟨.det, l⟩ => C (δ l)
  | ⟨.line0, k⟩ => C (φ k (e 0)) + X 0 * C (φ k (e 1))
  | ⟨.line1, k⟩ => C (φ k (e 0)) + X 1 * C (φ k (e 1))

def polyConeMap (x : ι → Ω) (δ : ν → Ω) (e : Module.Basis (Fin 2) Ω E) (φ : κ → E →ₗ[Ω] Ω) :
    MRing (T.wwIdx ι ν κ) →+* MvPolynomial T.WBlk (MvPolynomial (Fin 2) Ω) :=
  eval₂Hom (Int.castRingHom _) fun p => C (polyCoord x δ e φ p) * X p.1

omit [Fintype ι] [Fintype ν] [Fintype κ] in

theorem multiConeMap_eq (x : ι → Ω) (δ : ν → Ω) (e : Module.Basis (Fin 2) Ω E) (φ : κ → E →ₗ[Ω] Ω)
    (b : Fin 2 → Φ) :
    T.multiConeMap (T.wwCoord x δ e φ (b 0) (b 1)) =
      (MvPolynomial.map (aeval b : MvPolynomial (Fin 2) Ω →ₐ[Ω] Φ).toRingHom).comp (polyConeMap x δ e φ) := by
  refine MvPolynomial.ringHom_ext (fun r => ?_) (fun p => ?_)
  · simp [T.multiConeMap, polyConeMap]
  · rcases p with ⟨_ | _ | _ | _, i⟩ <;>
      simp [T.multiConeMap, polyConeMap, polyCoord, T.wwCoord, T.lineVal, mul_comm]

omit [Fintype ι] [Fintype ν] [Fintype κ] in

theorem wwIdeal_le_diag (x : ι → Ω) (δ : ν → Ω) (e : Module.Basis (Fin 2) Ω E) (φ : κ → E →ₗ[Ω] Ω)
    (a : Fin 2 → Φ) (ha : AlgebraicIndependent Ω a) :
    T.wwIdeal x δ e φ (a 0) (a 1) ≤ T.wwIdeal x δ e φ (a 0) (a 0) := by
  intro s hs
  rw [T.wwIdeal, RingHom.mem_ker, multiConeMap_eq x δ e φ a, RingHom.comp_apply] at hs
  have hinj : Function.Injective (aeval a : MvPolynomial (Fin 2) Ω →ₐ[Ω] Φ).toRingHom :=
    algebraicIndependent_iff_injective_aeval.mp ha
  have hz : polyConeMap x δ e φ s = 0 := MvPolynomial.map_injective _ hinj (hs.trans (map_zero _).symm)
  rw [T.wwIdeal, RingHom.mem_ker, multiConeMap_eq x δ e φ (fun _ => a 0), RingHom.comp_apply, hz, map_zero]

theorem aeval_diag_eq (x : ι → Ω) (δ : ν → Ω) (e : Module.Basis (Fin 2) Ω E) (φ : κ → E →ₗ[Ω] Ω)
    (a₀ a₁ : Φ) {m : ℕ} {h : MRing (T.wwIdx ι ν κ)} (hh : IsMultiHomog h (T.wwDeg m 0)) :
    aeval (T.wwCoord x δ e φ a₀ a₀) h = aeval (T.wwCoord x δ e φ a₀ a₁) h := by
  rw [aeval_def, aeval_def]
  apply eval₂_congr
  intro p c hp hc
  rcases p with ⟨_ | _ | _ | _, i⟩
  · rfl
  · rfl
  · rfl
  · exfalso
    have hs := hh c (mem_support_iff.mpr hc) .line1
    simp only [T.wwDeg] at hs
    exact (Finsupp.mem_support_iff.mp hp) ((Finset.sum_eq_zero_iff.mp hs) i (Finset.mem_univ _))

end Diagonal

end DiagonalOrder

open DiagonalOrder in

theorem DiagOrd.proof (hU : DiagOffUnit.Statement) (hO : DiagOrdOne.Statement) (hR : DiagRelevant.Statement) :
    DiagOrd.Statement := by
  intro Ω _ ι ν κ _ _ _ E _ _ Φ _ _ x B e φ δ hS hG hD hx a ha n g h hg hh hP hq
  have hrel := hR Ω ι ν κ E Φ x B e φ δ hS hG hD hx a ha
  have hone := hO Ω ι ν κ E Φ x B e φ δ hS hG hD hx a ha n g h hg hh hP hq
  have hunit := hU Ω ι ν κ E Φ x B e φ δ hS hG hD hx a ha
  set P := T.wwIdeal x δ e φ (a 0) (a 1) with hPdef
  set Δ := T.wwIdeal x δ e φ (a 0) (a 0) with hΔdef
  have hPp : P.IsPrime := RingHom.ker_isPrime _
  have hΔp : Δ.IsPrime := RingHom.ker_isPrime _
  have hPΔ : P ≤ Δ := wwIdeal_le_diag x δ e φ a ha
  have hhΔ : h ∉ Δ := by
    refine (DiagRAux.not_mem_ker_iff_aeval_ne _ h _ hh).2 ?_
    rw [aeval_diag_eq x δ e φ (a 0) (a 1) hh]
    exact (DiagRAux.not_mem_ker_iff_aeval_ne _ h _ hh).1 hP
  have hgΔ : g ∈ Δ := by
    by_contra hgn
    rw [multAt_eq_zero_of_not_le hΔp (fun hle => hgn (hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self g))))]
      at hone
    exact zero_ne_one hone
  have hJΔ : P ⊔ Ideal.span {g * h} ≤ Δ :=
    sup_le hPΔ ((Ideal.span_singleton_le_iff_mem _).mpr (Δ.mul_mem_right h hgΔ))
  have key : ∀ W : Ideal (MRing (T.wwIdx ι ν κ)), W.IsPrime → IsRelevant W → P ≤ W → ¬ Δ ≤ W →
      ∃ u v, u ∉ W ∧ v ∉ W ∧ u * g - v * h ∈ P := by
    intro W hW hWr hPW hΔW
    obtain ⟨α, β, u, v, hu, hv, hdeg, huW, hvW, huv⟩ := hunit W hW hWr hPW hΔW
    refine ⟨u, v, huW, hvW, ?_⟩
    have hβ : β + T.wwDeg (n + 3) 0 = α + T.wwDeg n 1 := by
      funext k
      have := hdeg k
      cases k <;> simp only [T.wwDeg, Pi.add_apply] at this ⊢ <;> omega
    have hd : IsMultiHomog (u * g - v * h) (α + T.wwDeg n 1) :=
      exHomog_sub (exHomog_mul hu hg) (hβ ▸ exHomog_mul hv hh)
    by_contra hn
    apply (DiagRAux.not_mem_ker_iff_aeval_ne _ _ _ hd).1 hn
    rw [map_sub, map_mul, map_mul, hq, ← huv]
    ring
  refine ⟨⟨⟨⟨hΔp, hJΔ⟩, fun Q hQ hQΔ => ?_⟩, hrel⟩, fun W hW => ?_⟩
  · by_contra hΔQ
    have hPQ : P ≤ Q := le_sup_left.trans hQ.2
    obtain ⟨u, v, huQ, hvQ, hm⟩ :=
      key Q hQ.1 (fun k => (hrel k).imp fun _ hi hq' => hi (hQΔ hq')) hPQ hΔQ
    have hhQ : h ∉ Q := fun hh' => hhΔ (hQΔ hh')
    have hgQ : g ∈ Q :=
      (hQ.1.mem_or_mem (hQ.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)))).resolve_right hhQ
    have hvh : v * h ∈ Q := by
      have e : v * h = u * g - (u * g - v * h) := by ring
      rw [e]
      exact Q.sub_mem (Q.mul_mem_left u hgQ) (hPQ hm)
    rcases hQ.1.mem_or_mem hvh with h1 | h1
    exacts [hvQ h1, hhQ h1]
  · have hWp : W.IsPrime := hW.1.1.1
    by_cases hWΔ : W = Δ
    · rw [if_pos hWΔ, hWΔ, hone, multAt_eq_zero_of_not_le hΔp
        (fun hle => hhΔ (hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self h))))]
      norm_num
    · rw [if_neg hWΔ]
      have hPW : P ≤ W := le_sup_left.trans hW.1.1.2
      have hΔW : ¬ Δ ≤ W := fun hle => hWΔ (le_antisymm (hW.1.2 ⟨hΔp, hJΔ⟩ hle) hle)
      obtain ⟨u, v, hu, hv, hm⟩ := key W hWp hW.2 hPW hΔW
      rw [multAt_sup_span_eq hWp hPW hu hv hm]
      simp

end

end GroundTheory.Heights₂.Heights.Inter
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.PDiagRatioBasis
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI

noncomputable section

def diagChart {ι ν κ : Type} (c : ∀ k, T.yyIdx ι ν κ k) : ∀ k, T.wwIdx ι ν κ k
  | .base => (c .base : ι)
  | .det => (c .det : ν)
  | .line0 => (c .line : κ)
  | .line1 => (c .line : κ)

theorem coneRatios_wwCoord_diag {Ω : Type} [Field Ω] {ι ν κ : Type} {E : Type} [AddCommGroup E] [Module Ω E]
    {Φ : Type} [Field Φ] [Algebra Ω Φ] (x : ι → Ω) (δ : ν → Ω) (e : Module.Basis (Fin 2) Ω E)
    (φ : κ → E →ₗ[Ω] Ω) (a : Φ) (c : ∀ k, T.yyIdx ι ν κ k) :
    coneRatios (T.wwCoord x δ e φ a a) (diagChart c) = coneRatios (T.yyCoord x δ e φ a) c := by
  ext r
  constructor
  · rintro ⟨⟨k, i⟩, rfl⟩
    cases k
    · exact ⟨⟨.base, (i : ι)⟩, rfl⟩
    · exact ⟨⟨.det, (i : ν)⟩, rfl⟩
    · exact ⟨⟨.line, (i : κ)⟩, rfl⟩
    · exact ⟨⟨.line, (i : κ)⟩, rfl⟩
  · rintro ⟨⟨k, i⟩, rfl⟩
    cases k
    · exact ⟨⟨.base, (i : ι)⟩, rfl⟩
    · exact ⟨⟨.det, (i : ν)⟩, rfl⟩
    · exact ⟨⟨.line0, (i : κ)⟩, rfl⟩

theorem DiagRatioBasis.proof (hY : YYRatioBasis.Statement) : DiagRatioBasis.Statement := by
  intro Ω _ _ ι ν κ _ _ _ E _ _ Φ _ _ _ x e b φ δ g i₀ l₀ k₀ k₁ d t a hx ht htF htA hδ hδF hφ hgF hg ha
  obtain ⟨c, t', hc, hind, hmem, halg⟩ :=
    hY Ω ι ν κ E Φ x e b φ δ g i₀ l₀ k₀ k₁ d t a hx ht htF htA hδ hδF hφ hgF hg ha
  refine ⟨diagChart c, t', fun k => ?_, hind, ?_, ?_⟩
  · cases k
    exacts [hc .base, hc .det, hc .line, hc .line]
  · rw [coneRatios_wwCoord_diag]; exact hmem
  · rw [coneRatios_wwCoord_diag]; exact halg

end

end GroundTheory.Heights₂.Heights.Inter
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.PHorizNotMem
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

theorem HorizNotMem.ringKrullDim_quotient_add_one_le {R : Type*} [CommRing R] {W₀ W : Ideal R}
    [hW₀ : W₀.IsPrime] [hW : W.IsPrime] (hlt : W₀ < W) :
    ringKrullDim (R ⧸ W) + 1 ≤ ringKrullDim (R ⧸ W₀) := by
  rw [ringKrullDim_quotient, ringKrullDim_quotient]
  have : Nonempty (PrimeSpectrum.zeroLocus (R := R) W) :=
    ⟨⟨⟨W, hW⟩, fun _ h => h⟩⟩
  rw [← Order.krullDim_withBot]
  let f : WithBot (PrimeSpectrum.zeroLocus (R := R) W) → PrimeSpectrum.zeroLocus (R := R) W₀ :=
    fun x => WithBot.recBotCoe ⟨⟨W₀, hW₀⟩, fun _ h => h⟩ (fun q => ⟨q.1, fun _ h => q.2 (hlt.le h)⟩) x
  refine Order.krullDim_le_of_strictMono f ?_
  intro a b hab
  induction a using WithBot.recBotCoe with
  | bot =>
    induction b using WithBot.recBotCoe with
    | bot => exact absurd hab (lt_irrefl _)
    | coe q =>
      change (⟨⟨W₀, hW₀⟩, _⟩ : PrimeSpectrum.zeroLocus (R := R) W₀) < ⟨q.1, _⟩
      exact Subtype.mk_lt_mk.mpr ((PrimeSpectrum.asIdeal_lt_asIdeal _ _).mp
        (hlt.trans_le (fun _ h => q.2 h)))
  | coe p =>
    induction b using WithBot.recBotCoe with
    | bot => exact absurd hab (WithBot.not_lt_bot _)
    | coe q =>
      change (⟨p.1, _⟩ : PrimeSpectrum.zeroLocus (R := R) W₀) < ⟨q.1, _⟩
      exact Subtype.mk_lt_mk.mpr (Subtype.mk_lt_mk.mp (WithBot.coe_lt_coe.mp hab))

theorem HorizNotMem.proof : HorizNotMem.Statement := by
  intro K _ ι _ P d s s' W hP hsP hs'P hnc hW hWh hs'W
  have : P.IsPrime := hP.2.1.1
  have hWp : W.IsPrime := hW.1.1.1
  have hle : P ⊔ Ideal.span {s'} ≤ W :=
    sup_le (le_sup_left.trans hW.1.1.2) ((Ideal.span_singleton_le_iff_mem _).mpr hs'W)
  obtain ⟨W₀, hW₀, hW₀W⟩ := Ideal.exists_minimalPrimes_le hle
  have : W₀.IsPrime := hW₀.1.1
  have h1 := dim_quot_minimal_add_one P W s hsP hW.1
  have h2 := dim_quot_minimal_add_one P W₀ s' hs'P hW₀
  have heq : W₀ = W := by
    by_contra hne
    have hstep := HorizNotMem.ringKrullDim_quotient_add_one_le (lt_of_le_of_ne hW₀W hne)
    have h3 := add_le_add hstep (le_refl (1 : WithBot ℕ∞))
    rw [h1, h2, hP.2.2.2] at h3
    have h4 : ((d + Fintype.card K + 1 : ℕ) : WithBot ℕ∞) ≤ ((d + Fintype.card K : ℕ) : WithBot ℕ∞) := by
      exact_mod_cast h3
    have h5 := WithBot.coe_le_coe.mp h4
    have h6 : d + Fintype.card K + 1 ≤ d + Fintype.card K := by exact_mod_cast h5
    omega
  exact hnc W hW ⟨heq ▸ hW₀, hW.2⟩ hWh

end GroundTheory.Heights₂.Heights.Inter
end
end

