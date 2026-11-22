import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0001
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DetMulVolMulConj
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0015
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0016
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0017
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsBinaryEqAdicCompletion
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0001
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HermFormConjDiag

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HermitianFormsSameSignatureSameSpace
section
open NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.OneSpace

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem emb_cc (τ : E →+* ℂ) (x : E) : τ (FD.cc x) = starRingEnd ℂ (τ x) :=
  IsCMField.complexEmbedding_complexConj E τ x

theorem rt_sq' (H : Host E) : (H.rt : E) ^ 2 = -(H.d : E) := by
  have := congrArg (algebraMap (𝓞 E) E) H.rt_sq
  simpa using this

theorem conj_of_sq {z : ℂ} {d : ℕ} (hd : 0 < d) (h : z ^ 2 = -(d : ℂ)) :
    starRingEnd ℂ z = -z := by
  first
  | exact @_root_.GlobalTheory.ConjNegSquareNat.conj_eq_neg_of_sq_eq_neg_nat
  | exact _root_.GlobalTheory.ConjNegSquareNat.conj_eq_neg_of_sq_eq_neg_nat
  | (apply _root_.GlobalTheory.ConjNegSquareNat.conj_eq_neg_of_sq_eq_neg_nat <;> assumption)
  | (intros; apply _root_.GlobalTheory.ConjNegSquareNat.conj_eq_neg_of_sq_eq_neg_nat <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ConjNegSquareNat.conj_eq_neg_of_sq_eq_neg_nat <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ConjNegSquareNat.conj_eq_neg_of_sq_eq_neg_nat ..)

theorem emb_rt_sq (H : Host E) (τ : E →+* ℂ) : τ (H.rt : E) ^ 2 = -(H.d : ℂ) := by
  rw [← map_pow, rt_sq']; simp

theorem cc_rt (H : Host E) : FD.cc (H.rt : E) = -(H.rt : E) := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [emb_cc, map_neg]
  exact conj_of_sq H.d_prime.pos (emb_rt_sq H τ)

theorem rt_ne (H : Host E) : (H.rt : E) ≠ 0 := by
  intro h
  have := rt_sq' H
  rw [h] at this
  have h2 : (H.d : E) = 0 := by simpa using this
  exact H.d_prime.ne_zero (by exact_mod_cast h2)

theorem gram_eq {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (Q : Matrix (Fin r) (Fin r) ℂ) :
    FD.gram τ G Q = Qᵀ * G.map τ * Q.map (starRingEnd ℂ) := by
  ext a b
  simp only [FD.gram, FD.hermC, FD.col, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.map_apply, Finset.sum_mul]
  exact Finset.sum_comm

theorem det_gram {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (Q : Matrix (Fin r) (Fin r) ℂ) :
    (FD.gram τ G Q).det = ((‖Q.det‖ ^ 2 : ℝ) : ℂ) * τ G.det := by
  rw [gram_eq, det_mul, det_mul, det_transpose]
  have h1 : (G.map τ).det = τ G.det := (RingHom.map_det τ G).symm
  have h2 : (Q.map (starRingEnd ℂ)).det = starRingEnd ℂ Q.det := (RingHom.map_det _ Q).symm
  rw [h1, h2, ← Complex.normSq_eq_norm_sq, ← Complex.mul_conj]
  ring

theorem gram_conj {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (p : ℕ)
    (h : ∃ Q : Matrix (Fin r) (Fin r) ℂ, Q.det ≠ 0 ∧
      FD.gram (ComplexEmbedding.conjugate τ) G Q =
        Matrix.diagonal fun a : Fin r => ((FD.sgn p (a : ℕ) : ℝ) : ℂ)) :
    ∃ Q : Matrix (Fin r) (Fin r) ℂ, Q.det ≠ 0 ∧
      FD.gram τ G Q = Matrix.diagonal fun a : Fin r => ((FD.sgn p (a : ℕ) : ℝ) : ℂ) := by
  obtain ⟨Q, hQ, h⟩ := h
  refine ⟨Q.map (starRingEnd ℂ), ?_, ?_⟩
  · have h2 : (Q.map (starRingEnd ℂ)).det = starRingEnd ℂ Q.det := (RingHom.map_det _ Q).symm
    rw [h2]
    simpa using hQ
  · ext a b
    have := congrArg (starRingEnd ℂ) (congrFun (congrFun h a) b)
    simp only [FD.gram, FD.hermC, FD.col, Matrix.of_apply, Matrix.map_apply, map_sum, map_mul,
      ComplexEmbedding.conjugate_coe_eq, Complex.conj_conj, Matrix.diagonal_apply] at this ⊢
    rw [this]
    split_ifs <;> simp

theorem cc_det {r : ℕ} (G : Matrix (Fin r) (Fin r) E) (h : ∀ a b, FD.cc (G a b) = G b a) :
    FD.cc G.det = G.det := by
  have h1 : IsCMField.complexConj E G.det = (G.map (IsCMField.complexConj E)).det :=
    RingHom.map_det (IsCMField.complexConj E).toRingEquiv.toRingHom G
  have h2 : G.map (IsCMField.complexConj E) = Gᵀ := by
    ext a b
    exact h a b
  rw [FD.cc, h1, h2, det_transpose]

theorem im_ne (τ : E →+* ℂ) {ξ : E} (h : FD.cc ξ = -ξ) (h0 : ξ ≠ 0) : (τ ξ).im ≠ 0 := by
  intro hi
  have h1 := emb_cc τ ξ
  rw [h, map_neg] at h1
  have h2 := congrArg Complex.re h1
  simp at h2
  apply h0
  apply τ.injective
  rw [map_zero]
  apply Complex.ext <;> simp [hi]
  linarith

end GlobalTheory.OneSpace

namespace GlobalTheory

open GlobalTheory.OneSpace

theorem model_in_same_space : (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G G' : Matrix (Fin r) (Fin r) E), (∀ a b, FD.cc (G a b) = G b a) → (∀ a b, FD.cc (G' a b) = G' b a) → G.det ≠ 0 → G'.det ≠ 0 → (∀ τ : E →+* ℂ, ∃ p0 : ℕ, (∃ Q : Matrix (Fin r) (Fin r) ℂ, Q.det ≠ 0 ∧ FD.gram τ G Q = Matrix.diagonal fun a : Fin r => ((FD.sgn p0 (a : ℕ) : ℝ) : ℂ)) ∧ (∃ Q : Matrix (Fin r) (Fin r) ℂ, Q.det ≠ 0 ∧ FD.gram τ G' Q = Matrix.diagonal fun a : Fin r => ((FD.sgn p0 (a : ℕ) : ℝ) : ℂ))) → (∃ z : E, G'.det = z * FD.cc z * G.det) → ∃ γ : GL (Fin r) E, ∀ x y, FD.herm G ((γ : Matrix (Fin r) (Fin r) E) *ᵥ x) ((γ : Matrix (Fin r) (Fin r) E) *ᵥ y) = FD.herm G' x y) → (∀ (F : Type) [Field F] [NumberField F] (δ x : F), δ ≠ 0 → x ≠ 0 → (∀ σ : F →+* ℝ, ∃ a b : ℝ, σ x = a ^ 2 - σ δ * b ^ 2) → (∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), ∃ a b : v.adicCompletion F, algebraMap F (v.adicCompletion F) x = a ^ 2 - algebraMap F (v.adicCompletion F) δ * b ^ 2) → ∃ a b : F, x = a ^ 2 - δ * b ^ 2) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D D' : Datum H) (r : ℕ) (ξ : E) (Gm : Matrix (Fin r) (Fin r) E) (φ : D.La →ₗ[𝓞 E] (Fin r → E)), D'.p = D.p → D'.q = D.q → FD.cc ξ = -ξ → (Function.Injective φ ∧ Submodule.span E (Set.range φ) = ⊤ ∧ (∀ a b, FD.cc (Gm a b) = Gm b a) ∧ Gm.det ≠ 0 ∧ ∀ x y, ((D.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (ξ * FD.herm Gm (φ x) (φ y))) → ∃ φ' : D'.La →ₗ[𝓞 E] (Fin r → E), (Function.Injective φ' ∧ Submodule.span E (Set.range φ') = ⊤ ∧ (∀ a b, FD.cc (Gm a b) = Gm b a) ∧ Gm.det ≠ 0 ∧ ∀ x y, ((D'.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (ξ * FD.herm Gm (φ' x) (φ' y))) := by
  intro hL hH E _ _ _ H D D' r ξ Gm φ hp hq hξ hM
  have hr : r = D'.p + D'.q := by
    rw [hp, hq]
    exact (GlobalTheory.HermModel.rank_integral_selfDual E H D r ξ Gm φ hξ hM).1
  by_cases h0 : ξ = 0
  · obtain ⟨Gm', ψ, hinj, hspan, -, -, -⟩ :=
      GlobalTheory.exists_herm_coord_of_datum E H D' (H.rt : E) (cc_rt H) (rt_ne H) r hr
    obtain ⟨-, hs, hG, hdet, hEF⟩ := hM
    have hz : ∀ x : D.La, x = 0 := by
      intro x
      apply D.unimod.1
      ext y
      have := hEF x y
      rw [h0, zero_mul, map_zero] at this
      rw [map_zero, LinearMap.zero_apply]
      exact_mod_cast this
    have hz' : ∀ v : Fin r → E, v = 0 := by
      intro v
      have hv : v ∈ Submodule.span E (Set.range φ) := hs ▸ Submodule.mem_top
      have : Submodule.span E (Set.range φ) ≤ ⊥ := by
        rw [Submodule.span_le]
        rintro _ ⟨x, rfl⟩
        rw [hz x, map_zero]
        exact Submodule.zero_mem _
      exact (Submodule.mem_bot E).1 (this hv)
    refine ⟨ψ, hinj, hspan, hG, hdet, fun x y => ?_⟩
    have : x = 0 := hinj ((hz' _).trans (hz' _).symm)
    rw [this, h0]
    simp
  obtain ⟨Gm', ψ, hM'⟩ := GlobalTheory.exists_herm_coord_of_datum E H D' ξ hξ h0 r hr
  have hsΨ : ∀ τ : E →+* ℂ, τ (H.rt : E) = H.rt0 → ∃ p0 : ℕ, (∃ Q : Matrix (Fin r) (Fin r) ℂ, Q.det ≠ 0 ∧ FD.gram τ Gm Q = Matrix.diagonal fun a : Fin r => ((FD.sgn p0 (a : ℕ) : ℝ) : ℂ)) ∧ (∃ Q : Matrix (Fin r) (Fin r) ℂ, Q.det ≠ 0 ∧ FD.gram τ Gm' Q = Matrix.diagonal fun a : Fin r => ((FD.sgn p0 (a : ℕ) : ℝ) : ℂ)) := by
    intro τ hτ
    have s1 := GlobalTheory.T.signature_hermitian_model_of_datum E H D r ξ Gm φ hξ hM τ hτ
    have s2 := GlobalTheory.T.signature_hermitian_model_of_datum E H D' r ξ Gm' ψ hξ hM' τ hτ
    rw [hp, hq] at s2
    rcases lt_or_gt_of_ne (im_ne τ hξ h0) with h | h
    · exact ⟨_, s1.2 h, s2.2 h⟩
    · exact ⟨_, s1.1 h, s2.1 h⟩
  have hs : ∀ τ : E →+* ℂ, ∃ p0 : ℕ, (∃ Q : Matrix (Fin r) (Fin r) ℂ, Q.det ≠ 0 ∧ FD.gram τ Gm Q = Matrix.diagonal fun a : Fin r => ((FD.sgn p0 (a : ℕ) : ℝ) : ℂ)) ∧ (∃ Q : Matrix (Fin r) (Fin r) ℂ, Q.det ≠ 0 ∧ FD.gram τ Gm' Q = Matrix.diagonal fun a : Fin r => ((FD.sgn p0 (a : ℕ) : ℝ) : ℂ)) := by
    intro τ
    have h1 : τ (H.rt : E) ^ 2 = H.rt0 ^ 2 := by rw [emb_rt_sq, H.sqrt_neg_disc_sq]
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 h1 with h | h
    · exact hsΨ τ h
    · obtain ⟨p0, a, b⟩ := hsΨ (ComplexEmbedding.conjugate τ) (by
        rw [ComplexEmbedding.conjugate_coe_eq, conj_of_sq H.d_prime.pos (emb_rt_sq H τ), h, neg_neg])
      exact ⟨p0, gram_conj τ _ _ a, gram_conj τ _ _ b⟩
  have hI := GlobalTheory.DetIdeal.det_ideal E H D D' r ξ Gm φ Gm' ψ hξ hM hM'
  obtain ⟨-, -, hG, hdet, -⟩ := hM
  obtain ⟨hinj, hspan, hG', hdet', hEF⟩ := hM'
  have hx : Gm'.det / Gm.det ∈ maximalRealSubfield E := by
    rw [← IsCMField.complexConj_eq_self_iff, map_div₀]
    have e1 := cc_det Gm hG
    have e2 := cc_det Gm' hG'
    rw [FD.cc] at e1 e2
    rw [e1, e2]
  set x : maximalRealSubfield E := ⟨Gm'.det / Gm.det, hx⟩ with hxdef
  have hx0 : x ≠ 0 := by
    intro h
    exact div_ne_zero hdet' hdet (congrArg Subtype.val h)
  have hloc := GlobalTheory.local_norm_of_ideal_norm E H x hx0 hI
  have hreal : ∀ σ : maximalRealSubfield E →+* ℝ, ∃ a b : ℝ,
      σ x = a ^ 2 - σ (-(H.d : maximalRealSubfield E)) * b ^ 2 := by
    intro σ
    let τ : E →+* ℂ := ComplexEmbedding.lift E (Complex.ofRealHom.comp σ)
    have hτ : τ (Gm'.det / Gm.det) = (σ x : ℂ) :=
      ComplexEmbedding.lift_algebraMap_apply E (Complex.ofRealHom.comp σ) x
    obtain ⟨p0, ⟨Q, hQ, e⟩, ⟨Q', hQ', e'⟩⟩ := hs τ
    have e2 := congrArg Matrix.det (e.trans e'.symm)
    rw [det_gram, det_gram] at e2
    have n1 : τ Gm.det ≠ 0 := by simpa using hdet
    have n2 : ((‖Q'.det‖ : ℝ) : ℂ) ≠ 0 := by simpa using hQ'
    refine ⟨‖Q.det‖ / ‖Q'.det‖, 0, ?_⟩
    apply Complex.ofReal_injective
    rw [← hτ, map_div₀]
    push_cast at e2 ⊢
    field_simp
    linear_combination -e2
  obtain ⟨a, b, hab⟩ := hH (maximalRealSubfield E) (-(H.d : maximalRealSubfield E)) x
    (by simpa using H.d_prime.ne_zero) hx0 hreal hloc
  have hz : ∃ z : E, Gm'.det = z * FD.cc z * Gm.det := by
    refine ⟨(a : E) + (b : E) * (H.rt : E), ?_⟩
    have e1 : FD.cc ((a : E) + (b : E) * (H.rt : E)) = (a : E) - (b : E) * (H.rt : E) := by
      have c := cc_rt H
      rw [FD.cc] at c ⊢
      rw [map_add, map_mul, c, IsCMField.complexConj_apply_eq_self,
        IsCMField.complexConj_apply_eq_self]
      ring
    have e2 : Gm'.det / Gm.det = (a : E) ^ 2 + (H.d : E) * (b : E) ^ 2 := by
      have := congrArg Subtype.val hab
      simpa using this
    rw [e1, (div_eq_iff hdet).1 e2]
    have := rt_sq' H
    linear_combination (b : E) ^ 2 * Gm.det * this
  obtain ⟨γ, hγ⟩ := hL E r Gm Gm' hG hG' hdet hdet' hs hz
  let g : (Fin r → E) ≃ₗ[E] (Fin r → E) := Matrix.toLin'OfInv γ.inv_mul γ.mul_inv
  have hg : ∀ v, g v = (γ : Matrix (Fin r) (Fin r) E) *ᵥ v := fun v => rfl
  refine ⟨(g.toLinearMap.restrictScalars (𝓞 E)).comp ψ, g.injective.comp hinj, ?_, hG, hdet, ?_⟩
  · have : Set.range ((g.toLinearMap.restrictScalars (𝓞 E)).comp ψ) =
        g.toLinearMap '' Set.range ψ := by
      rw [← Set.range_comp]; rfl
    rw [this, Submodule.span_image, hspan, Submodule.map_top, LinearEquiv.range]
  · intro u v
    rw [hEF, ← hγ, ← hg, ← hg]
    rfl

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.TypeFnPeriodExistModuliNonempty
section
open NumberField Matrix
open scoped nonZeroDivisors ComplexConjugate
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.PeriodExists

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

omit [IsCMField E] in

lemma card_cmType (Ψ : Finset (E →+* ℂ))
    (h : ∀ τ : E →+* ℂ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ) :
    Ψ.card = Module.finrank ℚ E / 2 := by
  classical
  have h1 : Ψ.card = Ψᶜ.card := by
    refine Finset.card_nbij' (fun σ => ComplexEmbedding.conjugate σ)
      (fun σ => ComplexEmbedding.conjugate σ) ?_ ?_ ?_ ?_
    · intro σ hσ
      simpa using (h σ).mp hσ
    · intro σ hσ
      have := h (ComplexEmbedding.conjugate σ)
      rw [ComplexEmbedding.involutive_conjugate E σ] at this
      exact this.mpr (by simpa using hσ)
    · intro σ _; exact ComplexEmbedding.involutive_conjugate E σ
    · intro σ _; exact ComplexEmbedding.involutive_conjugate E σ
  have h2 := Finset.card_add_card_compl Ψ
  rw [NumberField.Embeddings.card E ℂ] at h2
  omega

lemma exists_equiv_of_isTypeFn {H : Host E} {p q g g' : ℕ} {ty : Fin g → (E →+* ℂ)}
    {ty' : Fin g' → (E →+* ℂ)} (h : IsTypeFn H p q ty) (h' : IsTypeFn H p q ty') :
    ∃ e : Fin g ≃ Fin g', ∀ k, ty' (e k) = ty k := by
  have hc : ∀ τ, Nonempty ({i // ty i = τ} ≃ {i // ty' i = τ}) := by
    intro τ
    rw [← Finite.card_eq]
    by_cases hτ : τ (H.rt : E) = H.rt0
    · rw [(h τ).1 hτ, (h' τ).1 hτ]
    · rw [(h τ).2 hτ, (h' τ).2 hτ]
  exact ⟨Equiv.ofFiberEquiv fun τ => (hc τ).some, Equiv.ofFiberEquiv_map _⟩

lemma exists_isPeriod_of_equiv {H : Host E} {D : Datum H} {g g' : ℕ} {ty : Fin g → (E →+* ℂ)}
    {ty' : Fin g' → (E →+* ℂ)} (e : Fin g ≃ Fin g') (he : ∀ k, ty' (e k) = ty k)
    {P : D.La →+ (Fin g' → ℂ)} (hP : IsPeriod D ty' P) : ∃ P', IsPeriod D ty P' := by
  obtain ⟨h1, h2, h3, h4, Hm, hH, hpos, hE⟩ := hP
  let L : (Fin g' → ℂ) ≃L[ℝ] (Fin g → ℂ) :=
    (LinearEquiv.funCongrLeft ℝ ℂ e).toContinuousLinearEquiv
  have hL : ∀ z k, L z k = z (e k) := fun _ _ => rfl
  have hF : ∀ z w, hermForm (Hm.submatrix e e) (L z) (L w) = hermForm Hm z w := by
    intro z w
    simp only [hermForm, dotProduct, mulVec, submatrix_apply, Pi.star_apply, hL]
    rw [← e.sum_comp]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← e.sum_comp]
  let P' : D.La →+ (Fin g → ℂ) := L.toLinearEquiv.toLinearMap.toAddMonoidHom.comp P
  have hP' : ∀ x, P' x = L (P x) := fun _ => rfl
  refine ⟨P', ?_, ?_, ?_, ?_, Hm.submatrix e e, hH.submatrix e, ?_, ?_⟩
  · intro a x k
    rw [hP', hP', hL, hL, h1, he]
  · intro x y hxy
    exact h2 (L.injective hxy)
  · let f : P'.range → P.range := fun z => ⟨L.symm z.1, by
      obtain ⟨_, x, rfl⟩ := z
      exact ⟨x, by simp [hP']⟩⟩
    have hf : Continuous f := (L.symm.continuous.comp continuous_subtype_val).subtype_mk _
    exact DiscreteTopology.of_continuous_injective hf fun z w hzw =>
      Subtype.ext (L.symm.injective (congrArg Subtype.val hzw))
  · have : Set.range P' = L.toLinearEquiv.toLinearMap '' Set.range P := by
      rw [← Set.range_comp]; rfl
    rw [this, ← Submodule.map_span, h4, Submodule.map_top, LinearEquiv.range]
  · intro z hz
    obtain ⟨w, rfl⟩ := L.surjective z
    rw [hF]
    exact hpos w fun h => hz (by rw [h, map_zero])
  · intro x y
    rw [hP', hP', hF, hE]

lemma exists_imaginary (H : Host E) : ∃ ξ : E, FD.cc ξ = -ξ ∧ ξ ≠ 0 ∧
    ∀ τ : E →+* ℂ, τ (H.rt : E) = H.rt0 → 0 < (τ ξ).im := by
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  have hsq : (H.rt : E) ^ 2 = -(H.d : E) := by
    have := congrArg (fun a : 𝓞 E => (a : E)) H.rt_sq
    simpa using this
  have him : ∀ z : ℂ, z ^ 2 = -(H.d : ℂ) → z.im ≠ 0 := by
    intro z hz h0
    have := congrArg Complex.re hz
    simp [sq, h0] at this
    nlinarith [mul_self_nonneg z.re]
  obtain ⟨σ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hσ : (σ (H.rt : E)).im ≠ 0 := him _ (by rw [← map_pow, hsq]; simp)
  have hne : (H.rt : E) ≠ 0 := fun h => hσ (by rw [h]; simp)
  have hcc : FD.cc (H.rt : E) = -(H.rt : E) := by
    have h2 : (FD.cc (H.rt : E)) ^ 2 = (H.rt : E) ^ 2 := by
      unfold FD.cc
      rw [← map_pow, hsq]; simp
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 h2 with h | h
    · exfalso
      have h3 := congrArg Complex.im (FD.emb_cc σ (H.rt : E))
      rw [h, Complex.conj_im] at h3
      exact hσ (by linarith)
    · exact h
  rcases lt_or_gt_of_ne (him _ H.sqrt_neg_disc_sq) with h | h
  · refine ⟨-(H.rt : E), ?_, neg_ne_zero.2 hne, fun τ hτ => ?_⟩
    · unfold FD.cc at hcc ⊢
      rw [map_neg, hcc]
    · rw [map_neg, hτ, Complex.neg_im]; linarith
  · exact ⟨_, hcc, hne, fun τ hτ => by rw [hτ]; exact h⟩

lemma exists_typeFn_period (H : Host E) (D : Datum H) :
    ∃ (g : ℕ) (ty : Fin g → (E →+* ℂ)), IsTypeFn H D.p D.q ty ∧
      g = Module.finrank ℚ E / 2 * (D.p + D.q) ∧ ∃ P, IsPeriod D ty P := by
  classical
  obtain ⟨ξ, hξ, hξ0, hpos⟩ := exists_imaginary H
  obtain ⟨Gm, φ, hm⟩ := exists_herm_coord_of_datum E H D ξ hξ hξ0 _ rfl
  let Ψ : Finset (E →+* ℂ) := Finset.univ.filter fun τ => τ (H.rt : E) = H.rt0
  have hΨ : ∀ τ, τ ∈ Ψ ↔ τ (H.rt : E) = H.rt0 := fun τ => by simp [Ψ]
  let idx := (Fintype.equivFin (Ψ × Fin (D.p + D.q))).symm
  obtain ⟨h1, h2⟩ := FramePeriod.isPeriod_frame E H D _ ξ Gm φ Ψ hΨ _ idx _ (fun _ => rfl) hξ
    (fun τ hτ => hpos τ ((hΨ τ).1 hτ)) hm rfl
  choose Q hQ hG using fun τ : Ψ =>
    (GlobalTheory.T.signature_hermitian_model_of_datum E H D _ ξ Gm φ hξ hm τ.1 ((hΨ _).1 τ.2)).1 (hpos _ ((hΨ _).1 τ.2))
  have hx : (fun τ => Q τ : FD.Frame Ψ (D.p + D.q)) ∈ FD.GG Ψ Gm D.q := by
    intro τ
    refine ⟨hQ τ, fun i => ?_⟩
    have h3 : FD.dmin Gm (fun τ => Q τ : FD.Frame Ψ (D.p + D.q)) τ i = ((FD.psgn D.q i : ℝ) : ℂ) := by
      change FD.lminor (FD.gram τ.1 Gm (Q τ)) i = _
      rw [hG, FD.FrameDegreeData.lminor_diagonal, FD.psgn, ← Fin.prod_univ_eq_prod_range]
      push_cast
      rfl
    rw [h3, Complex.ofReal_re]
    refine mul_self_pos.2 (Finset.prod_ne_zero_iff.2 fun a _ => ?_)
    unfold FD.sgn
    split_ifs <;> norm_num
  obtain ⟨⟨P, hP⟩, h4⟩ := h2 _ hx
  refine ⟨_, _, h1, ?_, P, h4 P hP⟩
  rw [Fintype.card_prod, Fintype.card_coe, Fintype.card_fin,
    card_cmType Ψ (FramePeriod.cmType H Ψ hΨ)]

lemma period_of_isTypeFn (H : Host E) (D : Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ))
    (h : IsTypeFn H D.p D.q ty) :
    g = Module.finrank ℚ E / 2 * (D.p + D.q) ∧ ∃ P, IsPeriod D ty P := by
  obtain ⟨g', ty', h', hg, P, hP⟩ := exists_typeFn_period H D
  obtain ⟨e, he⟩ := exists_equiv_of_isTypeFn h h'
  exact ⟨(Fin.equiv_iff_eq.1 ⟨e⟩).trans hg, exists_isPeriod_of_equiv e he hP⟩

theorem typeFn_period_exist : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), (∃ (g : ℕ) (ty : Fin g → (E →+* ℂ)), IsTypeFn H D.p D.q ty) ∧ (∀ (g : ℕ) (ty : Fin g → (E →+* ℂ)), IsTypeFn H D.p D.q ty → g = Module.finrank ℚ E / 2 * (D.p + D.q) ∧ ∃ P, IsPeriod D ty P) ∧ (N1c → 1 ≤ D.p + D.q → ∀ (l : Level H) (Xo : Moduli D l) (c : Coeff l), Nonempty (Xo.XF c)) := by
  intro E _ _ _ H D
  obtain ⟨g, ty, h, -⟩ := exists_typeFn_period H D
  refine ⟨⟨g, ty, h⟩, period_of_isTypeFn H D, fun hN hr l Xo c => ?_⟩
  obtain ⟨U⟩ := hN E H D l Xo (KA l).val.toRingHom g ty hr rfl h
  let i : Fin U.n := ⟨0, U.n_pos⟩
  obtain ⟨-, P, hP⟩ := period_of_isTypeFn H (U.Di i) g ty (by rw [(U.sig i).1, (U.sig i).2]; exact h)
  have hw : CategoryTheory.CategoryStruct.comp (U.u i P) Xo.s =
      CategoryTheory.CategoryStruct.comp (spMap c.F.val.toRingHom)
        (spMap (IntermediateField.inclusion c.le).toRingHom) := by
    rw [U.over_σ i P hP]
    exact AlgebraicGeometry.Spec.map_comp (CommRingCat.ofHom (IntermediateField.inclusion c.le).toRingHom)
      (CommRingCat.ofHom c.F.val.toRingHom)
  exact ⟨(CategoryTheory.Limits.pullback.lift _ _ hw).base (IsLocalRing.closedPoint ℂ)⟩

end GlobalTheory.PeriodExists
end

