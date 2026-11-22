import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0006
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSheetCover
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsProved
import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.Assembly
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0147
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0001
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0145
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0035
import Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeCptFrameDivisorFormula
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ColFlags

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.CMFieldDegreeEqTwiceCard
section
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.Cusp.CMRank

theorem restrict_bijective (E : Type) [Field E] [NumberField E] :
    Function.Bijective (fun φ : E →+* ℂ => φ.comp (algebraMap (𝓞 E) E)) := by
  constructor
  · intro φ ψ h
    exact IsFractionRing.ringHom_ext (A := 𝓞 E) (K := E) (fun a => DFunLike.congr_fun h a)
  · intro s
    refine ⟨embOf s, ?_⟩
    ext a
    simp [embOf]

theorem natCard_intEmb (E : Type) [Field E] [NumberField E] :
    Nat.card (𝓞 E →+* ℂ) = Module.finrank ℚ E := by
  rw [← Nat.card_congr (Equiv.ofBijective _ (restrict_bijective E)), Nat.card_eq_fintype_card,
    NumberField.Embeddings.card]

theorem cmFam_sum_bijective {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Type} [Fintype Ψ]
    {σ : Ψ → (𝓞 E →+* ℂ)} (h : IsCMFam σ) :
    Function.Bijective
      (Sum.elim σ (fun τ => (starRingEnd ℂ).comp (σ τ)) : Ψ ⊕ Ψ → (𝓞 E →+* ℂ)) := by
  have hconj : ∀ s : 𝓞 E →+* ℂ, (starRingEnd ℂ).comp ((starRingEnd ℂ).comp s) = s := by
    intro s
    ext a
    simp
  obtain ⟨hinj, hiff⟩ := h
  constructor
  · rintro (a | a) (b | b) hab
    · exact congrArg Sum.inl (hinj hab)
    · exact absurd ⟨a, hab⟩ ((hiff (σ b)).1 ⟨b, rfl⟩)
    · exact absurd ⟨b, hab.symm⟩ ((hiff (σ a)).1 ⟨a, rfl⟩)
    · have hab' : (starRingEnd ℂ).comp (σ a) = (starRingEnd ℂ).comp (σ b) := hab
      have : σ a = σ b := by
        rw [← hconj (σ a), hab', hconj]
      exact congrArg Sum.inr (hinj this)
  · intro s
    by_cases hs : ∃ τ, σ τ = s
    · obtain ⟨τ, rfl⟩ := hs
      exact ⟨Sum.inl τ, rfl⟩
    · have hn : ∃ τ, σ τ = (starRingEnd ℂ).comp s := by
        by_contra hc
        exact hs ((hiff s).2 hc)
      obtain ⟨τ, hτ⟩ := hn
      refine ⟨Sum.inr τ, ?_⟩
      change (starRingEnd ℂ).comp (σ τ) = s
      rw [hτ, hconj]

theorem finrank_eq_two_mul_card : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ]
    (σ : Ψ → (𝓞 E →+* ℂ)), IsCMFam σ → Module.finrank ℚ E = 2 * Fintype.card Ψ := by
  intro E _ _ _ Ψ _ σ h
  rw [← natCard_intEmb E, ← Nat.card_congr (Equiv.ofBijective _ (cmFam_sum_bijective h)),
    Nat.card_eq_fintype_card, Fintype.card_sum]
  omega

end GlobalTheory.CompanionTheory.Ar.Cusp.CMRank
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.EmbeddingInverseRootImaginary
section
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Dict.LatXi

theorem conj_inv_mul_rt (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (s : 𝓞 E →+* ℂ) (m : ℕ)
    (hm : m ≠ 0) : ∃ ε : ℝ, ε ^ 2 = 1 ∧ embOf s (((m : E) * (H.rt : E))⁻¹) =
      Complex.I * (((1 / ((m : ℝ) * Real.sqrt H.d)) * ε : ℝ) : ℂ) := by
  have hcoe : embOf s (H.rt : E) = s H.rt := IsFractionRing.lift_algebraMap (intEmb_injective s) H.rt
  have hw : (s H.rt) ^ 2 = -(H.d : ℂ) := by
    have h := congrArg s H.rt_sq
    simpa [map_pow, map_neg, map_natCast] using h
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  have hr0 : 0 < Real.sqrt H.d := Real.sqrt_pos.2 hd
  have hrC : ((Real.sqrt H.d : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr0.ne'
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast hm
  have hr2 : ((Real.sqrt H.d : ℝ) : ℂ) ^ 2 = (H.d : ℂ) := by
    have h := Real.sq_sqrt hd.le
    exact_mod_cast h
  have hfac : (s H.rt - Complex.I * ((Real.sqrt H.d : ℝ) : ℂ)) *
      (s H.rt + Complex.I * ((Real.sqrt H.d : ℝ) : ℂ)) = 0 := by
    have : (s H.rt - Complex.I * ((Real.sqrt H.d : ℝ) : ℂ)) *
        (s H.rt + Complex.I * ((Real.sqrt H.d : ℝ) : ℂ)) =
        (s H.rt) ^ 2 - Complex.I ^ 2 * ((Real.sqrt H.d : ℝ) : ℂ) ^ 2 := by ring
    rw [this, hw, hr2, Complex.I_sq]; ring
  have hval : embOf s (((m : E) * (H.rt : E))⁻¹) = ((m : ℂ) * s H.rt)⁻¹ := by
    rw [map_inv₀, map_mul, map_natCast, hcoe]
  rcases mul_eq_zero.1 hfac with h | h
  · refine ⟨-1, by norm_num, ?_⟩
    have hw' : s H.rt = Complex.I * ((Real.sqrt H.d : ℝ) : ℂ) := sub_eq_zero.1 h
    rw [hval, hw']
    push_cast
    field_simp
    rw [Complex.I_sq]
    norm_num
  · refine ⟨1, by norm_num, ?_⟩
    have hw' : s H.rt = -(Complex.I * ((Real.sqrt H.d : ℝ) : ℂ)) := eq_neg_of_add_eq_zero_left h
    rw [hval, hw']
    push_cast
    field_simp
    rw [Complex.I_sq]

end GlobalTheory.CompanionTheory.Ar.Cusp.Dict.LatXi
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsMajorantOfPositiveFrame
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Dict.TauMaj

open NumberField Matrix GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ComplexOrder

section Conj

variable {ι : Type} [Fintype ι] [DecidableEq ι]

abbrev cj (A : Matrix ι ι ℂ) : Matrix ι ι ℂ := A.map (starRingEnd ℂ)

theorem cj_cj (A : Matrix ι ι ℂ) : cj (cj A) = A := by
  ext i k; simp [cj]

theorem cj_injective : Function.Injective (cj : Matrix ι ι ℂ → Matrix ι ι ℂ) :=
  Function.LeftInverse.injective cj_cj

theorem cj_mul (A B : Matrix ι ι ℂ) : cj (A * B) = cj A * cj B := Matrix.map_mul

theorem cj_eq (A : Matrix ι ι ℂ) : cj A = Aᴴᵀ := by
  ext i k; simp [cj]

theorem cj_inv (A : Matrix ι ι ℂ) : cj A⁻¹ = (cj A)⁻¹ := by
  rw [cj_eq, cj_eq, conjTranspose_nonsing_inv, transpose_nonsing_inv]

theorem cj_conjTranspose (A : Matrix ι ι ℂ) : cj Aᴴ = (cj A)ᴴ := by
  ext i k; simp [cj]

theorem posDef_cj {P : Matrix ι ι ℂ} (h : P.PosDef) : (cj P).PosDef := by
  have : cj P = Pᵀ := by rw [cj_eq, h.1.eq]
  rw [this]
  exact h.transpose

theorem cj_mulVec (A : Matrix ι ι ℂ) (v : ι → ℂ) : cj A *ᵥ star v = star (A *ᵥ v) := by
  ext i; simp [cj, mulVec, dotProduct, map_sum]

theorem re_term_cj (P G : Matrix ι ι ℂ) (v : ι → ℂ) :
    (star (G *ᵥ star v) ⬝ᵥ (cj P *ᵥ (G *ᵥ star v))).re = (star (cj G *ᵥ v) ⬝ᵥ (P *ᵥ (cj G *ᵥ v))).re := by
  have hu : G *ᵥ star v = star (cj G *ᵥ v) := by
    rw [← cj_mulVec, cj_cj]
  rw [hu, cj_mulVec, star_dotProduct_star, dotProduct_comm]
  simp

theorem stab_iff_cj (P G : Matrix ι ι ℂ) :
    (G.map (starRingEnd ℂ))ᵀ * cj P * G = cj P ↔ (cj G)ᴴ * P * cj G = P := by
  have h : (G.map (starRingEnd ℂ))ᵀ * cj P * G = cj ((cj G)ᴴ * P * cj G) := by
    rw [cj_mul, cj_mul, cj_conjTranspose, cj_cj]
    rfl
  rw [h]
  exact cj_injective.eq_iff

end Conj

section Arch

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Type} [Fintype Ψ] {j j' n g : ℕ} {Λ : Type}
  [AddCommGroup Λ] [Module (𝓞 E) Λ]

omit [IsCMField E] in
theorem embOf_coe (s : 𝓞 E →+* ℂ) (a : 𝓞 E) : embOf s (a : E) = s a :=
  IsFractionRing.lift_algebraMap (intEmb_injective s) a

omit [IsCMField E] in
theorem embOf_comp (φ : E →+* ℂ) : embOf (φ.comp (algebraMap (𝓞 E) E)) = φ :=
  IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) (by
    ext a; simpa using embOf_coe (φ.comp (algebraMap (𝓞 E) E)) a)

omit [IsCMField E] in
theorem embOf_injective : Function.Injective (embOf : (𝓞 E →+* ℂ) → (E →+* ℂ)) := by
  intro s s' h
  ext a
  have := congrArg (fun φ : E →+* ℂ => φ (a : E)) h
  simpa [embOf_coe] using this

theorem plc_bijective (F : UnivFam E Ψ j j' n g Λ) : Function.Bijective (plc F) := by
  have hcm := F.cm
  constructor
  · intro τ τ' h
    rcases InfinitePlace.mk_eq_iff.1 h with h | h
    · exact hcm.1 (embOf_injective h)
    · exfalso
      have hs : F.σ τ' = (starRingEnd ℂ).comp (F.σ τ) := by
        ext a
        have := congrArg (fun φ : E →+* ℂ => φ (a : E)) h
        simpa [embOf_coe, ComplexEmbedding.conjugate_coe_eq] using this.symm
      exact ((hcm.2 (F.σ τ)).1 ⟨τ, rfl⟩) ⟨τ', hs⟩
  · intro w
    set s : 𝓞 E →+* ℂ := w.embedding.comp (algebraMap (𝓞 E) E) with hs
    by_cases h : ∃ τ, F.σ τ = s
    · obtain ⟨τ, hτ⟩ := h
      refine ⟨τ, ?_⟩
      rw [plc, hτ, hs, embOf_comp, InfinitePlace.mk_embedding]
    · have h2 : ∃ τ, F.σ τ = (starRingEnd ℂ).comp s := by
        by_contra h3
        exact h ((hcm.2 s).2 h3)
      obtain ⟨τ, hτ⟩ := h2
      refine ⟨τ, ?_⟩
      have he : embOf (F.σ τ) = ComplexEmbedding.conjugate w.embedding := by
        rw [hτ]
        have : (starRingEnd ℂ).comp s =
            (ComplexEmbedding.conjugate w.embedding).comp (algebraMap (𝓞 E) E) := by
          ext a; simp [hs, ComplexEmbedding.conjugate_coe_eq]
        rw [this, embOf_comp]
      rw [plc, he, InfinitePlace.mk_conjugate_eq, InfinitePlace.mk_embedding]

theorem emb_ne (F : UnivFam E Ψ j j' n g Λ) (τ : Ψ) (h : (plc F τ).embedding ≠ embOf (F.σ τ)) :
    (plc F τ).embedding = ComplexEmbedding.conjugate (embOf (F.σ τ)) :=
  (InfinitePlace.embedding_mk_eq (embOf (F.σ τ))).resolve_left h

def atPlc (F : UnivFam E Ψ j j' n g Λ) (Pt : Ψ → Matrix (Fin (j + j')) (Fin (j + j')) ℂ) (τ : Ψ) :
    Matrix (Fin (j + j')) (Fin (j + j')) ℂ := by
  classical
  exact if (plc F τ).embedding = embOf (F.σ τ) then Pt τ else cj (Pt τ)

variable {F : UnivFam E Ψ j j' n g Λ} (C : LatEmb F)

theorem gramAt_of_eq {τ : Ψ} (h : (plc F τ).embedding = embOf (F.σ τ)) :
    gramAt C.h (Pi.basisFun E (Fin (j + j'))) (plc F τ) = C.gr τ := by
  rw [gramAt, h]; rfl

theorem gramAt_of_ne {τ : Ψ} (h : (plc F τ).embedding ≠ embOf (F.σ τ)) :
    gramAt C.h (Pi.basisFun E (Fin (j + j'))) (plc F τ) = cj (C.gr τ) := by
  rw [gramAt, emb_ne F τ h]
  ext i k
  simp [LatEmb.gr, ComplexEmbedding.conjugate_coe_eq]

theorem vecAt_of_eq (x : Λ) {τ : Ψ} (h : (plc F τ).embedding = embOf (F.σ τ)) :
    vecAt (Pi.basisFun E (Fin (j + j'))) (C.e x) (plc F τ) = C.vec x τ := by
  ext i
  simp [vecAt, LatEmb.vec, h]

theorem vecAt_of_ne (x : Λ) {τ : Ψ} (h : (plc F τ).embedding ≠ embOf (F.σ τ)) :
    vecAt (Pi.basisFun E (Fin (j + j'))) (C.e x) (plc F τ) = star (C.vec x τ) := by
  ext i
  simp [vecAt, LatEmb.vec, emb_ne F τ h, ComplexEmbedding.conjugate_coe_eq]

theorem tm_of_eq (a : C.Arch) {τ : Ψ} (h : (plc F τ).embedding = embOf (F.σ τ)) :
    C.tm a τ = ((a : InfinitePlace E → GL (Fin (j + j')) ℂ) (plc F τ) : Matrix (Fin (j + j')) (Fin (j + j')) ℂ) := by
  rw [LatEmb.tm, tauMat, if_pos h]

theorem tm_of_ne (a : C.Arch) {τ : Ψ} (h : (plc F τ).embedding ≠ embOf (F.σ τ)) :
    C.tm a τ = cj ((a : InfinitePlace E → GL (Fin (j + j')) ℂ) (plc F τ) : Matrix (Fin (j + j')) (Fin (j + j')) ℂ) := by
  rw [LatEmb.tm, tauMat, if_neg h]

theorem atPlc_of_eq (Pt : Ψ → Matrix (Fin (j + j')) (Fin (j + j')) ℂ) {τ : Ψ}
    (h : (plc F τ).embedding = embOf (F.σ τ)) : atPlc F Pt τ = Pt τ := by
  rw [atPlc]; exact if_pos h

theorem atPlc_of_ne (Pt : Ψ → Matrix (Fin (j + j')) (Fin (j + j')) ℂ) {τ : Ψ}
    (h : (plc F τ).embedding ≠ embOf (F.σ τ)) : atPlc F Pt τ = cj (Pt τ) := by
  rw [atPlc]; exact if_neg h

def majOf (Pt : Ψ → Matrix (Fin (j + j')) (Fin (j + j')) ℂ) (hP : ∀ τ, (Pt τ).PosDef)
    (hS : ∀ τ, Pt τ * (C.gr τ)⁻¹ * Pt τ = C.gr τ) : Majorant C.h (Pi.basisFun E (Fin (j + j'))) where
  P w := atPlc F Pt ((Equiv.ofBijective _ (plc_bijective F)).symm w)
  posDef w := by
    obtain ⟨τ, rfl⟩ := (plc_bijective F).2 w
    have hτ : (Equiv.ofBijective _ (plc_bijective F)).symm (plc F τ) = τ :=
      Equiv.ofBijective_symm_apply_apply _ _ _
    rw [hτ]
    by_cases h : (plc F τ).embedding = embOf (F.σ τ)
    · rw [atPlc_of_eq Pt h]; exact hP τ
    · rw [atPlc_of_ne Pt h]; exact posDef_cj (hP τ)
  siegel w := by
    obtain ⟨τ, rfl⟩ := (plc_bijective F).2 w
    have hτ : (Equiv.ofBijective _ (plc_bijective F)).symm (plc F τ) = τ :=
      Equiv.ofBijective_symm_apply_apply _ _ _
    rw [hτ]
    by_cases h : (plc F τ).embedding = embOf (F.σ τ)
    · rw [atPlc_of_eq Pt h, gramAt_of_eq C h]; exact hS τ
    · rw [atPlc_of_ne Pt h, gramAt_of_ne C h, ← cj_inv, ← cj_mul, ← cj_mul, hS τ]

theorem majOf_P (Pt : Ψ → Matrix (Fin (j + j')) (Fin (j + j')) ℂ) (hP : ∀ τ, (Pt τ).PosDef)
    (hS : ∀ τ, Pt τ * (C.gr τ)⁻¹ * Pt τ = C.gr τ) (τ : Ψ) : (majOf C Pt hP hS).P (plc F τ) = atPlc F Pt τ := by
  show atPlc F Pt ((Equiv.ofBijective _ (plc_bijective F)).symm (plc F τ)) = _
  rw [Equiv.ofBijective_symm_apply_apply]

theorem majOf_term (Pt : Ψ → Matrix (Fin (j + j')) (Fin (j + j')) ℂ) (hP : ∀ τ, (Pt τ).PosDef)
    (hS : ∀ τ, Pt τ * (C.gr τ)⁻¹ * Pt τ = C.gr τ) (a : C.Arch) (x : Λ) (τ : Ψ) :
    (star (invApply a (vecAt (Pi.basisFun E (Fin (j + j'))) (C.e x)) (plc F τ)) ⬝ᵥ
      ((majOf C Pt hP hS).P (plc F τ) *ᵥ invApply a (vecAt (Pi.basisFun E (Fin (j + j'))) (C.e x)) (plc F τ))).re =
    (star (C.tm a⁻¹ τ *ᵥ C.vec x τ) ⬝ᵥ (Pt τ *ᵥ (C.tm a⁻¹ τ *ᵥ C.vec x τ))).re := by
  rw [majOf_P]
  by_cases h : (plc F τ).embedding = embOf (F.σ τ)
  · rw [atPlc_of_eq Pt h, tm_of_eq C _ h, ← vecAt_of_eq C x h]
    rfl
  · rw [atPlc_of_ne Pt h, tm_of_ne C _ h, ← re_term_cj, ← vecAt_of_ne C x h]
    rfl

theorem majOf_len (Pt : Ψ → Matrix (Fin (j + j')) (Fin (j + j')) ℂ) (hP : ∀ τ, (Pt τ).PosDef)
    (hS : ∀ τ, Pt τ * (C.gr τ)⁻¹ * Pt τ = C.gr τ) (a : C.Arch) (x : Λ) :
    (majOf C Pt hP hS).len (invApply a (vecAt (Pi.basisFun E (Fin (j + j'))) (C.e x))) ^ 2 =
      ∑ τ, (star (C.tm a⁻¹ τ *ᵥ C.vec x τ) ⬝ᵥ (Pt τ *ᵥ (C.tm a⁻¹ τ *ᵥ C.vec x τ))).re := by
  rw [Majorant.len, Real.sq_sqrt]
  · rw [← (Equiv.ofBijective _ (plc_bijective F)).sum_comp]
    exact Finset.sum_congr rfl fun τ _ => majOf_term C Pt hP hS a x τ
  · exact Finset.sum_nonneg fun w _ => ((majOf C Pt hP hS).posDef w).posSemidef.re_dotProduct_nonneg _

theorem majOf_stab (Pt : Ψ → Matrix (Fin (j + j')) (Fin (j + j')) ℂ) (hP : ∀ τ, (Pt τ).PosDef)
    (hS : ∀ τ, Pt τ * (C.gr τ)⁻¹ * Pt τ = C.gr τ) (c : C.Arch) :
    c ∈ (majOf C Pt hP hS).stab ↔ ∀ τ, (C.tm c τ)ᴴ * Pt τ * C.tm c τ = Pt τ := by
  have hloc : ∀ τ, ((((c : InfinitePlace E → GL (Fin (j + j')) ℂ) (plc F τ) : Matrix (Fin (j + j')) (Fin (j + j')) ℂ)).map
        (starRingEnd ℂ))ᵀ * (majOf C Pt hP hS).P (plc F τ) *
        ((c : InfinitePlace E → GL (Fin (j + j')) ℂ) (plc F τ) : Matrix (Fin (j + j')) (Fin (j + j')) ℂ) =
        (majOf C Pt hP hS).P (plc F τ) ↔ (C.tm c τ)ᴴ * Pt τ * C.tm c τ = Pt τ := by
    intro τ
    rw [majOf_P]
    by_cases h : (plc F τ).embedding = embOf (F.σ τ)
    · rw [atPlc_of_eq Pt h, tm_of_eq C _ h]
      rfl
    · rw [atPlc_of_ne Pt h, tm_of_ne C _ h]
      exact stab_iff_cj _ _
  rw [Majorant.stab, Subgroup.mem_subgroupOf, Subgroup.mem_pi]
  constructor
  · intro hc τ
    exact (hloc τ).1 (mem_unitaryGroupMatrix.1 (hc (plc F τ) (Set.mem_univ _)))
  · intro hc w _
    obtain ⟨τ, rfl⟩ := (plc_bijective F).2 w
    exact mem_unitaryGroupMatrix.2 ((hloc τ).2 (hc τ))

end Arch

theorem exists_majorant : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ] (j j' n g : ℕ) (Λ : Type)
    [AddCommGroup Λ] [Module (𝓞 E) Λ] (F : UnivFam E Ψ j j' n g Λ) (C : LatEmb F)
    (Pt : Ψ → Matrix (Fin (j + j')) (Fin (j + j')) ℂ), (∀ τ, (Pt τ).PosDef) →
    (∀ τ, Pt τ * (C.gr τ)⁻¹ * Pt τ = C.gr τ) →
    ∃ M : Majorant C.h (Pi.basisFun E (Fin (j + j'))),
      (∀ (a : C.Arch) (x : Λ), M.len (invApply a (vecAt (Pi.basisFun E (Fin (j + j'))) (C.e x))) ^ 2 =
        ∑ τ, (star (C.tm a⁻¹ τ *ᵥ C.vec x τ) ⬝ᵥ (Pt τ *ᵥ (C.tm a⁻¹ τ *ᵥ C.vec x τ))).re) ∧
      ∀ c : C.Arch, c ∈ M.stab ↔ ∀ τ, (C.tm c τ)ᴴ * Pt τ * C.tm c τ = Pt τ :=
  by
  intro E _ _ _ Ψ _ j j' n g Λ _ _ F C Pt hP hS
  exact ⟨majOf C Pt hP hS, majOf_len C Pt hP hS, majOf_stab C Pt hP hS⟩

end GlobalTheory.CompanionTheory.Ar.Cusp.Dict.TauMaj
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsNormalizedRiemannLattice
section
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder
open GlobalTheory.CompanionTheory.Ar.Cusp.Univ

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Univ.CoordLat

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ]

def ipLin (R : RiemLat E g Λ) (x : Fin g → ℂ) : (Fin g → ℂ) →ₗ[ℂ] ℂ where
  toFun := R.ip x
  map_add' y y' := by simp [RiemLat.ip, add_dotProduct]
  map_smul' c y := by simp [RiemLat.ip, smul_dotProduct]

theorem ip_eq_ipLin (R : RiemLat E g Λ) (x y : Fin g → ℂ) : R.ip x y = ipLin R x y := rfl

theorem conj_ip (R : RiemLat E g Λ) (x y : Fin g → ℂ) : starRingEnd ℂ (R.ip x y) = R.ip y x := by
  show star (y ⬝ᵥ R.Hm *ᵥ star x) = x ⬝ᵥ R.Hm *ᵥ star y
  rw [← star_dotProduct_star, star_mulVec, star_star, R.herm.eq, dotProduct_mulVec]

def diagAct (s : Fin g → (𝓞 E →+* ℂ)) : 𝓞 E →+* Module.End ℂ (Fin g → ℂ) where
  toFun a :=
    { toFun := fun x k => s k a * x k
      map_add' := fun x y => funext fun k => by simp [mul_add]
      map_smul' := fun r x => funext fun k => by simp [mul_left_comm] }
  map_one' := LinearMap.ext fun x => funext fun k => by simp
  map_mul' a b := LinearMap.ext fun x => funext fun k => by simp [mul_assoc]
  map_zero' := LinearMap.ext fun x => funext fun k => by simp
  map_add' a b := LinearMap.ext fun x => funext fun k => by simp [add_mul]

theorem diagAct_apply (s : Fin g → (𝓞 E →+* ℂ)) (a : 𝓞 E) (x : Fin g → ℂ) (k : Fin g) :
    diagAct s a x k = s k a * x k := rfl

section Frame

variable {ι : Type} [Fintype ι] [DecidableEq ι] (R : RiemLat E g Λ) (e : ι ≃ Fin g) (c : ι → Fin g → ℂ)

include e

theorem sum_ip_smul (hc : ∀ i i', R.ip (c i) (c i') = if i = i' then 1 else 0) (z : Fin g → ℂ) :
    ∑ i, R.ip (c i) z • c i = z := by
  have hli : LinearIndependent ℂ c := by
    rw [Fintype.linearIndependent_iff]
    intro a ha k
    have h := congrArg (ipLin R (c k)) ha
    rw [map_zero, map_sum] at h
    simp only [map_smul, ← ip_eq_ipLin, hc, smul_eq_mul] at h
    simpa using h
  have hspan : Submodule.span ℂ (Set.range c) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank' (by simp [Fintype.card_congr e])
  have hz : z ∈ Submodule.span ℂ (Set.range c) := hspan ▸ Submodule.mem_top
  obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hz
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  rw [ip_eq_ipLin, map_sum]
  simp only [map_smul, ← ip_eq_ipLin, hc, smul_eq_mul]
  simp

theorem sum_ip_mul_conj (hc : ∀ i i', R.ip (c i) (c i') = if i = i' then 1 else 0) (u v : Fin g → ℂ) :
    ∑ i, R.ip (c i) u * starRingEnd ℂ (R.ip (c i) v) = R.ip v u := by
  conv_rhs => rw [← sum_ip_smul R e c hc u]
  rw [ip_eq_ipLin, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, ← ip_eq_ipLin, conj_ip, smul_eq_mul]

theorem ip_act (hc : ∀ i i', R.ip (c i) (c i') = if i = i' then 1 else 0) (s : ι → (𝓞 E →+* ℂ))
    (hs : ∀ i, c i ∈ eigSp R.B (s i)) (a : 𝓞 E) (i : ι) (z : Fin g → ℂ) :
    R.ip (c i) (R.B a z) = s i a * R.ip (c i) z := by
  have hB : ∀ l, R.B a (c l) = s l a • c l := fun l => by
    have h := (Submodule.mem_iInf _).1 (hs l) a
    have h' := LinearMap.mem_ker.1 h
    simpa [sub_eq_zero] using h'
  conv_lhs => rw [← sum_ip_smul R e c hc z]
  rw [map_sum, ip_eq_ipLin, map_sum]
  simp only [map_smul, hB, ← ip_eq_ipLin, hc, smul_eq_mul]
  simp [mul_comm]

end Frame

variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {j j' : ℕ}

theorem exists_riemLat_coord (R₀ : RiemLat E g Λ) (σ : Ψ → (𝓞 E →+* ℂ)) (e : Ix Ψ j j' ≃ Fin g)
    (c : Ix Ψ j j' → Fin g → ℂ) (hs : ∀ i, c i ∈ eigSp R₀.B (emb σ i))
    (hc : ∀ i i', R₀.ip (c i) (c i') = if i = i' then 1 else 0) :
    ∃ R₁ : RiemLat E g Λ, R₁.form = R₀.form ∧ R₁.Hm = 1 ∧ ∀ a x k, R₁.B a x k = emb σ (e.symm k) a * x k := by
  let P : Λ →+ (Fin g → ℂ) :=
    { toFun := fun x k => R₀.ip (c (e.symm k)) (R₀.P x)
      map_zero' := funext fun k => by simp [ip_eq_ipLin]
      map_add' := fun x y => funext fun k => by simp [ip_eq_ipLin] }
  have hP : ∀ x k, P x k = R₀.ip (c (e.symm k)) (R₀.P x) := fun _ _ => rfl
  refine ⟨{ free := R₀.free, fin := R₀.fin, rank := R₀.rank, form := R₀.form, alt := R₀.alt, unimod := R₀.unimod,
            adj := R₀.adj, P := P, Hm := 1, herm := isHermitian_one, pos := ?_, im := ?_,
            B := diagAct fun k => emb σ (e.symm k), act := ?_ }, rfl, rfl, fun _ _ _ => rfl⟩
  · intro z hz
    obtain ⟨k, hk⟩ := Function.ne_iff.1 hz
    have hk' : z k ≠ 0 := hk
    have : (z ⬝ᵥ (1 : Matrix (Fin g) (Fin g) ℂ) *ᵥ star z).re = ∑ l, Complex.normSq (z l) := by
      simp [dotProduct, Complex.mul_conj]
    rw [this]
    exact Finset.sum_pos' (fun l _ => Complex.normSq_nonneg _) ⟨k, Finset.mem_univ _, Complex.normSq_pos.2 hk'⟩
  · intro x y
    have key : P x ⬝ᵥ (1 : Matrix (Fin g) (Fin g) ℂ) *ᵥ star (P y) = R₀.P x ⬝ᵥ R₀.Hm *ᵥ star (R₀.P y) := by
      have h := sum_ip_mul_conj R₀ e c hc (R₀.P x) (R₀.P y)
      rw [← e.symm.sum_comp] at h
      rw [one_mulVec]
      exact h
    rw [key]
    exact R₀.im x y
  · intro a x
    funext k
    rw [diagAct_apply, hP, hP, R₀.act]
    exact ip_act R₀ e c hc (emb σ) hs a (e.symm k) (R₀.P x)

theorem coord_lat : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {j j' g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ] (R₀ : RiemLat E g Λ) (σ : Ψ → (𝓞 E →+* ℂ)) (e : Ix Ψ j j' ≃ Fin g) (c : Ix Ψ j j' → Fin g → ℂ), (∀ i, c i ∈ eigSp R₀.B (emb σ i)) → (∀ i i', R₀.ip (c i) (c i') = if i = i' then 1 else 0) → ∃ R₁ : RiemLat E g Λ, R₁.form = R₀.form ∧ R₁.Hm = 1 ∧ ∀ a x k, R₁.B a x k = emb σ (e.symm k) a * x k :=
  fun R₀ σ e c hs hc => exists_riemLat_coord R₀ σ e c hs hc

end GlobalTheory.CompanionTheory.Ar.Cusp.Univ.CoordLat
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeCptFrameDivisorFormulaStatement
section
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodgeCpt_frame_divisor_formula : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K₀ : Type) [Fintype K₀] (J₀ : K₀ → Type) [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω) (𝔐 : HodgeCpt Y S x₀) (bW : WBases 𝔐) (bO : OmBases 𝔐) (n m : CMType H ⊕ CMType H → ℕ) (φ : ∀ s, Fin (n s) → Module.Dual Ω (EE 𝔐)) (d : ℕ), FormsOK 𝔐 bW bO m φ → 𝔐.IsCover d → ∀ (𝔐' : HodgeCpt Y S (yv (p := D.p) (q := D.q) (aOf 𝔐 bW bO φ) x₀)) (pr : 𝔐'.X ⟶ 𝔐.X) (j : 𝔐.Li →+ 𝔐'.Li), HodgeOver 𝔐' 𝔐 pr (algebraMap Ω (GenField Ω (rk (CMType H) D.p D.q))) j → Submodule.span (GenField Ω (rk (CMType H) D.p D.q)) (Set.range j) = ⊤ → (∀ s, 𝔐'.V s = (𝔐.V s).pull 𝔐'.ξ pr j) → ∃ Fl : 𝔐'.Flag, Fl.deg = d ∧ ColFlags 𝔐 bW bO j Fl := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FMX.GenFl.exists_colFlags | exact GlobalTheory.CompanionTheory.Ar.PB.FMX.GenFl.exists_colFlags | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FMX.GenFl.exists_colFlags <;> assumption)
end

