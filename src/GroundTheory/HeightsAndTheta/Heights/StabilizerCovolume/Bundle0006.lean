import Mathlib
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.Bundle0004
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.ShortIsotropic

-- bundled from GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.LinearIndependentReal
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NineStatements

open NumberField GroundTheory.Heights₂.Heights.LowerBoundFree

variable {Em : Type} [Field Em] [NumberField Em] [IsCMField Em] {Ψ : Type} [Fintype Ψ] {N j : ℕ}

theorem HermDatum.exists_emb_or_conj (A : HermDatum Em Ψ N j) (σ : Em →+* ℂ) :
    ∃ τ, A.emb τ = σ ∨ (starRingEnd ℂ).comp (A.emb τ) = σ := by
  by_cases h : ∃ τ, A.emb τ = σ
  · obtain ⟨τ, hτ⟩ := h
    exact ⟨τ, Or.inl hτ⟩
  · have h' : ∃ τ, A.emb τ = (starRingEnd ℂ).comp σ := by
      by_contra h''
      exact h ((A.cmType σ).2 h'')
    obtain ⟨τ, hτ⟩ := h'
    refine ⟨τ, Or.inr ?_⟩
    rw [hτ]
    ext x
    simp

theorem HermDatum.finrank_eq (A : HermDatum Em Ψ N j) : Module.finrank ℚ Em = 2 * Fintype.card Ψ := by
  classical
  let g : Ψ ⊕ Ψ → (Em →+* ℂ) := Sum.elim A.emb fun τ => (starRingEnd ℂ).comp (A.emb τ)
  have hconj : ∀ τ τ', A.emb τ ≠ (starRingEnd ℂ).comp (A.emb τ') := by
    intro τ τ' h
    have h1 := (A.cmType (A.emb τ')).1 ⟨τ', rfl⟩
    refine h1 ⟨τ, ?_⟩
    rw [h]
  have hg : Function.Bijective g := by
    constructor
    · rintro (a | a) (b | b) h
      · exact congrArg Sum.inl (A.emb_inj h)
      · exact absurd h (hconj a b)
      · exact absurd h.symm (hconj b a)
      · refine congrArg Sum.inr (A.emb_inj (RingHom.ext fun x => ?_))
        have := congrArg (fun φ : Em →+* ℂ => starRingEnd ℂ (φ x)) h
        simpa [g] using this
    · intro σ
      obtain ⟨τ, h | h⟩ := A.exists_emb_or_conj σ
      exacts [⟨Sum.inl τ, h⟩, ⟨Sum.inr τ, h⟩]
  rw [← NumberField.Embeddings.card Em ℂ, ← Fintype.card_of_bijective hg, Fintype.card_sum]
  ring

theorem HermDatum.linearIndependent_real (A : HermDatum Em Ψ N j) {m : ℕ} {x : Fin m → Fin N → Em}
    (hx : LinearIndependent ℚ x) :
    LinearIndependent ℝ fun k (p : Ψ × Fin N) => A.emb p.1 (x k p.2) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have h1 : ∀ τ a, ∑ k, (c k : ℂ) * A.emb τ (x k a) = 0 := by
    intro τ a
    have := congr_fun hc (τ, a)
    simpa [Finset.sum_apply, Complex.real_smul] using this
  have h2 : ∀ (σ : Em →+* ℂ) a, ∑ k, (c k : ℂ) * σ (x k a) = 0 := by
    intro σ a
    obtain ⟨τ, h | h⟩ := A.exists_emb_or_conj σ
    · rw [← h]
      exact h1 τ a
    · rw [← h]
      have := congrArg (starRingEnd ℂ) (h1 τ a)
      simpa [map_sum, Complex.conj_ofReal] using this
  set ω := NumberField.integralBasis Em
  have hxω : ∀ (σ : Em →+* ℂ) (y : Em), σ y = ∑ i, ((ω.repr y i : ℚ) : ℂ) * σ (ω i) := by
    intro σ y
    conv_lhs => rw [← ω.sum_repr y]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.smul_def, map_mul, eq_ratCast, map_ratCast]
  have h3 : ∀ a i, ∑ k, c k * (ω.repr (x k a) i : ℝ) = 0 := by
    intro a
    have key : ∀ (σ : Em →+* ℂ),
        ∑ i, ((∑ k, c k * (ω.repr (x k a) i : ℝ) : ℝ) : ℂ) * σ (ω i) = 0 := by
      intro σ
      rw [← h2 σ a]
      simp only [hxω σ (x _ a)]
      push_cast
      simp only [Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => by ring
    have hli := (NumberField.mixedEmbedding.latticeBasis Em).linearIndependent
    rw [Fintype.linearIndependent_iff] at hli
    refine hli _ (Prod.ext (funext fun w => ?_) (funext fun w => ?_))
    · simp only [Prod.fst_sum, Finset.sum_apply, Prod.smul_fst, Pi.smul_apply,
        NumberField.mixedEmbedding.latticeBasis_apply,
        NumberField.mixedEmbedding.mixedEmbedding_apply_isReal, smul_eq_mul, Prod.fst_zero,
        Pi.zero_apply]
      apply Complex.ofReal_injective
      push_cast
      simp only [InfinitePlace.embedding_of_isReal_apply]
      have hk := key w.1.embedding
      push_cast at hk
      exact hk
    · simp only [Prod.snd_sum, Finset.sum_apply, Prod.smul_snd, Pi.smul_apply,
        NumberField.mixedEmbedding.latticeBasis_apply,
        NumberField.mixedEmbedding.mixedEmbedding_apply_isComplex, Complex.real_smul,
        Prod.snd_zero, Pi.zero_apply]
      exact key _
  intro k
  rw [← Module.forall_dual_apply_eq_zero_iff ℚ (c k)]
  intro φ
  have h4 : ∑ k, φ (c k) • x k = 0 := by
    funext a
    apply ω.repr.injective
    ext i
    have := congrArg φ (h3 a i)
    rw [map_sum, map_zero] at this
    simp only [Finset.sum_apply, Pi.smul_apply, map_sum, map_smul, Finsupp.coe_finsetSum,
      Finsupp.smul_apply, smul_eq_mul, map_zero, Finsupp.coe_zero, Pi.zero_apply]
    rw [← this]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_comm (c k), ← Rat.smul_def, map_smul, smul_eq_mul, mul_comm]
  exact Fintype.linearIndependent_iff.1 hx _ h4 k

theorem HermDatum.exists_isZBasis (A : HermDatum Em Ψ N j) {I : Submodule (𝓞 Em) (Fin N → Em)}
    (hI : I ≤ A.L) : ∃ m, ∃ b : Fin m → Fin N → Em, IsZBasis I b := by
  classical
  have hL : IsNoetherian ℤ (A.L.restrictScalars ℤ) := isNoetherian_of_fg_of_noetherian _ A.fg
  have hJ : IsNoetherian ℤ (I.restrictScalars ℤ) :=
    isNoetherian_of_le (s := I.restrictScalars ℤ) (t := A.L.restrictScalars ℤ) hI
  have hfin : Module.Finite ℤ (I.restrictScalars ℤ) := inferInstance
  have htf : Module.IsTorsionFree ℤ (I.restrictScalars ℤ) := inferInstance
  have hfree : Module.Free ℤ (I.restrictScalars ℤ) := Module.free_of_finite_type_torsion_free'
  let B := Module.finBasis ℤ (I.restrictScalars ℤ)
  have hspan : Submodule.span ℤ (Set.range fun k => (B k : Fin N → Em)) = I.restrictScalars ℤ := by
    have e : (Set.range fun k => (B k : Fin N → Em)) = (I.restrictScalars ℤ).subtype '' Set.range B :=
      Set.range_comp _ _
    rw [e, Submodule.span_image, B.span_eq, Submodule.map_subtype_top]
  have hli : LinearIndependent ℤ ((I.restrictScalars ℤ).subtype ∘ B) :=
    B.linearIndependent.map' (I.restrictScalars ℤ).subtype (Submodule.ker_subtype _)
  refine ⟨_, fun k => (B k : Fin N → Em), hli, fun v => ?_⟩
  rw [hspan]
  rfl

omit [IsCMField Em] in

theorem card_eq_of_isZBasis {I : Submodule (𝓞 Em) (Fin N → Em)} {ρ : ℕ} {v : Fin ρ → Fin N → Em}
    (hv : IsNzFamily I ρ v) {m : ℕ} {b : Fin m → Fin N → Em} (hb : IsZBasis I b) :
    m = Module.finrank ℚ Em * ρ := by
  classical
  set ω := NumberField.integralBasis Em
  have hbQ : LinearIndependent ℚ b := (LinearIndependent.iff_fractionRing ℤ ℚ).1 hb.1
  have hvE : LinearIndependent Em v := (LinearIndependent.iff_fractionRing (𝓞 Em) Em).1 hv.2.2.1
  set w : _ × Fin ρ → Fin N → Em := fun p => ω p.1 • v p.2
  have hw : LinearIndependent ℚ w := linearIndependent_smul ω.linearIndependent hvE
  have hspan : Submodule.span ℚ (Set.range b) = Submodule.span ℚ (Set.range w) := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      have hbk : b k ∈ I := (hb.2 _).2 (Submodule.subset_span ⟨k, rfl⟩)
      set T := Submodule.span (𝓞 Em) (Set.range v)
      have hmem : T.toAddSubgroup.relIndex I.toAddSubgroup • b k ∈ T.toAddSubgroup :=
        AddSubgroup.nsmul_relIndex_mem _ hbk
      have hT : ∀ t ∈ T, t ∈ Submodule.span ℚ (Set.range w) := by
        intro t ht
        obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 Em)).1 ht
        refine Submodule.sum_mem _ fun k _ => ?_
        rw [← algebraMap_smul Em (a k) (v k), ← ω.sum_repr (algebraMap (𝓞 Em) Em (a k)),
          Finset.sum_smul]
        refine Submodule.sum_mem _ fun i _ => ?_
        rw [smul_assoc]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨(i, k), rfl⟩)
      have hn : (T.toAddSubgroup.relIndex I.toAddSubgroup : ℚ) ≠ 0 := by exact_mod_cast hv.2.2.2
      have := Submodule.smul_mem _ ((T.toAddSubgroup.relIndex I.toAddSubgroup : ℚ)⁻¹) (hT _ hmem)
      rwa [← Nat.cast_smul_eq_nsmul ℚ, smul_smul, inv_mul_cancel₀ hn, one_smul] at this
    · rw [Submodule.span_le]
      rintro _ ⟨p, rfl⟩
      have hpI : w p ∈ I := by
        show ω p.1 • v p.2 ∈ I
        rw [integralBasis_apply, algebraMap_smul]
        exact I.smul_mem _ (hv.2.1 p.2)
      exact Submodule.span_le_restrictScalars ℤ ℚ _ ((hb.2 _).1 hpI)
  have h1 := finrank_span_eq_card hbQ
  have h2 := finrank_span_eq_card hw
  rw [hspan, h2, Fintype.card_prod, Fintype.card_fin, ← Module.finrank_eq_card_basis ω] at h1
  simpa using h1.symm

end GroundTheory.Heights₂.Heights.NineStatements
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.PFirstMinPos
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NineStatements

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix

namespace FirstMinPos

section Lemmas

variable {Em : Type} [Field Em] [NumberField Em] [IsCMField Em] {Ψ : Type} [Fintype Ψ] {N j : ℕ}

theorem exists_cmType_one_le_norm (A : HermDatum Em Ψ N j) {x : Em} (hx : IsIntegral ℤ x) (hx0 : x ≠ 0) :
    ∃ τ, 1 ≤ ‖A.emb τ x‖ := by
  obtain ⟨σ, hσ⟩ := exists_conjugate_one_le_norm (K := Em) (α := ⟨x, hx⟩)
    (fun h => hx0 (congrArg (fun y : 𝓞 Em => (y : Em)) h))
  have hσ' : 1 ≤ ‖σ x‖ := hσ
  by_cases h : ∃ τ, A.emb τ = σ
  · obtain ⟨τ, rfl⟩ := h
    exact ⟨τ, hσ'⟩
  · obtain ⟨τ, hτ⟩ := not_not.mp (mt (A.cmType σ).mpr h)
    refine ⟨τ, ?_⟩
    rw [hτ, RingHom.comp_apply, Complex.norm_conj]
    exact hσ'

theorem exists_common_denom (A : HermDatum Em Ψ N j) :
    ∃ d : ℤ, d ≠ 0 ∧ ∀ v ∈ A.L, ∀ b, IsIntegral ℤ (d • v b) := by
  classical
  obtain ⟨S, hS⟩ := A.fg
  obtain ⟨d, hd0, hd⟩ := exists_integral_multiples ℤ ℚ (S.biUnion fun s => Finset.univ.image s)
  refine ⟨d, hd0, fun v hv => ?_⟩
  have key : ∀ w ∈ Submodule.span ℤ (S : Set (Fin N → Em)), ∀ b, IsIntegral ℤ (d • w b) := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
      intro b
      exact hd _ (Finset.mem_biUnion.mpr ⟨x, hx, Finset.mem_image_of_mem _ (Finset.mem_univ b)⟩)
    | zero =>
      intro b
      simpa using (isIntegral_zero : IsIntegral ℤ (0 : Em))
    | add x y _ _ hx hy =>
      intro b
      simp only [Pi.add_apply, smul_add]
      exact (hx b).add (hy b)
    | smul a x _ hx =>
      intro b
      simp only [Pi.smul_apply]
      rw [smul_comm, zsmul_eq_mul]
      have hi := (isIntegral_algebraMap (R := ℤ) (A := Em) (x := a)).mul (hx b)
      rwa [algebraMap_int_eq, eq_intCast] at hi
  exact key v (by rw [hS]; exact hv)

theorem isUnit_det_of_eq_signMat {P A : Matrix (Fin N) (Fin N) ℂ} (h : Pᴴ * A * P = signMat N j) :
    IsUnit P.det := by
  rw [isUnit_iff_ne_zero]
  intro h0
  have hs : (signMat N j).det ≠ 0 := by
    rw [signMat, Matrix.det_diagonal, Finset.prod_ne_zero_iff]
    intro a _
    split_ifs <;> norm_num
  apply hs
  rw [← h, Matrix.det_mul, h0, mul_zero]

theorem norm_sq_le_of_isUnit {P : Matrix (Fin N) (Fin N) ℂ} (hP : IsUnit P.det) (w : Fin N → ℂ) (b : Fin N) :
    ‖w b‖ ^ 2 ≤ (∑ a, ‖P b a‖ ^ 2) * ∑ a, ‖(P⁻¹ *ᵥ w) a‖ ^ 2 := by
  have hw : P *ᵥ (P⁻¹ *ᵥ w) = w := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hP, Matrix.one_mulVec]
  have h1 : ‖w b‖ ≤ ∑ a, ‖P b a‖ * ‖(P⁻¹ *ᵥ w) a‖ := by
    calc ‖w b‖ = ‖(P *ᵥ (P⁻¹ *ᵥ w)) b‖ := by rw [hw]
      _ = ‖∑ a, P b a * (P⁻¹ *ᵥ w) a‖ := by simp [Matrix.mulVec, dotProduct]
      _ ≤ ∑ a, ‖P b a * (P⁻¹ *ᵥ w) a‖ := norm_sum_le _ _
      _ = ∑ a, ‖P b a‖ * ‖(P⁻¹ *ᵥ w) a‖ := by simp
  calc ‖w b‖ ^ 2 ≤ (∑ a, ‖P b a‖ * ‖(P⁻¹ *ᵥ w) a‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ _ := Finset.sum_mul_sq_le_sq_mul_sq _ _ _

end Lemmas

variable {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] {K : Type} [Fintype K] {ι : K → Type}
  [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [Algebra ℚ Ω] {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)]
  [∀ τ, Module Ω (E τ)] {Em : Type} [Field Em] [NumberField Em] [IsCMField Em]

theorem proof (D : FullerData II Ψ K ι Ω E Em) : FirstMinPos.Statement D := by
  intro z hz
  classical
  obtain ⟨d, hd0, hd⟩ := exists_common_denom D.herm
  have hP : ∀ τ, IsUnit (D.per z τ).det := fun τ => isUnit_det_of_eq_signMat (D.per_witt z hz τ)
  have hdR : (0 : ℝ) < (d : ℝ) ^ 2 := by
    have : (d : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hd0
    positivity
  set g : Ψ → ℝ := fun τ => 2 * ‖D.herm.emb τ D.herm.ξ‖ /
    ((d : ℝ) ^ 2 * (∑ b, ∑ a, ‖D.per z τ b a‖ ^ 2 + 1)) with hg
  have hgpos : ∀ τ, 0 < g τ := by
    intro τ
    have : D.herm.emb τ D.herm.ξ ≠ 0 := (map_ne_zero _).mpr D.herm.ξ_ne
    have : 0 < ‖D.herm.emb τ D.herm.ξ‖ := norm_pos_iff.mpr this
    positivity
  have hbound : ∀ v ∈ D.herm.L, v ≠ 0 → ∃ τ, g τ ≤ D.hodgeNormSq z v := by
    intro v hv hv0
    obtain ⟨b, hb⟩ : ∃ b, v b ≠ 0 := by
      by_contra! h
      exact hv0 (funext h)
    obtain ⟨τ, hτ⟩ := exists_cmType_one_le_norm D.herm (hd v hv b) (smul_ne_zero hd0 hb)
    refine ⟨τ, ?_⟩
    set w : Fin D.N → ℂ := fun b => D.herm.emb τ (v b) with hwdef
    have hw : 1 ≤ (d : ℝ) ^ 2 * ‖w b‖ ^ 2 := by
      have he : ‖D.herm.emb τ (d • v b)‖ = |(d : ℝ)| * ‖w b‖ := by
        simp [w, zsmul_eq_mul]
      rw [he] at hτ
      have := pow_le_pow_left₀ zero_le_one hτ 2
      rw [mul_pow, sq_abs, one_pow] at this
      exact this
    set Kτ : ℝ := ∑ b, ∑ a, ‖D.per z τ b a‖ ^ 2 + 1 with hK
    have hrow : ∑ a, ‖D.per z τ b a‖ ^ 2 ≤ Kτ := by
      have h := Finset.single_le_sum (s := Finset.univ) (f := fun b' => ∑ a, ‖D.per z τ b' a‖ ^ 2)
        (fun b' _ => Finset.sum_nonneg fun a _ => sq_nonneg ‖D.per z τ b' a‖) (Finset.mem_univ b)
      exact le_add_of_le_of_nonneg h zero_le_one
    set s : ℝ := ∑ a, ‖((D.per z τ)⁻¹ *ᵥ w) a‖ ^ 2 with hs
    have hs0 : 0 ≤ s := by positivity
    have hc := norm_sq_le_of_isUnit (hP τ) w b
    have h1 : 1 ≤ (d : ℝ) ^ 2 * Kτ * s := by
      calc (1 : ℝ) ≤ (d : ℝ) ^ 2 * ‖w b‖ ^ 2 := hw
        _ ≤ (d : ℝ) ^ 2 * ((∑ a, ‖D.per z τ b a‖ ^ 2) * s) := by gcongr
        _ ≤ (d : ℝ) ^ 2 * (Kτ * s) := by gcongr
        _ = (d : ℝ) ^ 2 * Kτ * s := by ring
    have hterm : 2 * ‖D.herm.emb τ D.herm.ξ‖ * s ≤ D.hodgeNormSq z v := by
      unfold FullerData.hodgeNormSq
      exact Finset.single_le_sum (f := fun τ' => 2 * ‖D.herm.emb τ' D.herm.ξ‖ *
          ∑ a, ‖((D.per z τ')⁻¹ *ᵥ fun b => D.herm.emb τ' (v b)) a‖ ^ 2)
        (fun _ _ => by positivity) (Finset.mem_univ τ)
    have hKτ : 0 < Kτ := by
      have : 0 ≤ ∑ b', ∑ a, ‖D.per z τ b' a‖ ^ 2 :=
        Finset.sum_nonneg fun b' _ => Finset.sum_nonneg fun a _ => sq_nonneg ‖D.per z τ b' a‖
      linarith
    have hKpos : 0 < (d : ℝ) ^ 2 * Kτ := mul_pos hdR hKτ
    have hc0 : 0 ≤ 2 * ‖D.herm.emb τ D.herm.ξ‖ := mul_nonneg zero_le_two (norm_nonneg _)
    have hmul := mul_le_mul_of_nonneg_left h1 hc0
    calc g τ = 2 * ‖D.herm.emb τ D.herm.ξ‖ / ((d : ℝ) ^ 2 * Kτ) := rfl
      _ ≤ 2 * ‖D.herm.emb τ D.herm.ξ‖ * s := by
        rw [div_le_iff₀ hKpos]
        nlinarith
      _ ≤ _ := hterm
  obtain ⟨v0, hv0L, hv0⟩ : ∃ v ∈ D.herm.L, v ≠ 0 := by
    by_contra! h
    have h2 : 2 ≤ D.N := D.two_le_N
    have : Nonempty (Fin D.N) := ⟨⟨0, by omega⟩⟩
    have hbot : Submodule.span ℚ (D.herm.L : Set (Fin D.N → Em)) = ⊥ :=
      Submodule.span_eq_bot.mpr fun x hx => h x hx
    rw [D.herm.span] at hbot
    exact top_ne_bot hbot
  obtain ⟨τ0, -⟩ := hbound v0 hv0L hv0
  set δ : ℝ := Finset.univ.inf' ⟨τ0, Finset.mem_univ τ0⟩ g with hδ
  have hδpos : 0 < δ := (Finset.lt_inf'_iff _).mpr fun τ _ => hgpos τ
  have hlow : Real.sqrt δ ≤ D.lam1 z := by
    unfold FullerData.lam1
    refine le_csInf ⟨_, v0, hv0L, hv0, rfl⟩ ?_
    rintro x ⟨v, hv, hvne, rfl⟩
    obtain ⟨τ, hτ⟩ := hbound v hv hvne
    exact Real.sqrt_le_sqrt ((Finset.inf'_le _ (Finset.mem_univ τ)).trans hτ)
  exact (Real.sqrt_pos.mpr hδpos).trans_le hlow

end FirstMinPos

end GroundTheory.Heights₂.Heights.NineStatements
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.PIsotropicRank
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NineStatements

open NumberField
open scoped Matrix

namespace IsotropicRank

theorem hermForm_span_eq_zero {Em : Type} [Field Em] [NumberField Em] [IsCMField Em] {N : ℕ}
    (H : Matrix (Fin N) (Fin N) Em) (S : Set (Fin N → Em)) (hS : ∀ v ∈ S, ∀ w ∈ S, hermForm Em H v w = 0) :
    ∀ x ∈ Submodule.span Em S, ∀ y ∈ Submodule.span Em S, hermForm Em H x y = 0 := by
  have h1 : ∀ v ∈ S, ∀ y ∈ Submodule.span Em S, hermForm Em H v y = 0 := by
    intro v hv y hy
    induction hy using Submodule.span_induction with
    | mem w hw => exact hS v hv w hw
    | zero => exact ShortIsotropic.hermForm_zero_right H v
    | add y y' _ _ h h' => rw [ShortIsotropic.hermForm_add_right, h, h', add_zero]
    | smul c y _ h => rw [ShortIsotropic.hermForm_smul_right, h, mul_zero]
  intro x hx y hy
  induction hx using Submodule.span_induction with
  | mem v hv => exact h1 v hv y hy
  | zero => exact ShortIsotropic.hermForm_zero_left H y
  | add x x' _ _ h h' => rw [ShortIsotropic.hermForm_add_left, h, h', add_zero]
  | smul c x _ h => rw [ShortIsotropic.hermForm_smul_left, h, mul_zero]

theorem nonempty_cmType {Em : Type} [Field Em] [NumberField Em] [IsCMField Em] {Ψ : Type} [Fintype Ψ] {N j : ℕ}
    (A : HermDatum Em Ψ N j) : Nonempty Ψ := by
  obtain ⟨σ⟩ : Nonempty (Em →+* ℂ) := inferInstance
  by_cases h : ∃ τ, A.emb τ = σ
  · exact ⟨h.choose⟩
  · obtain ⟨τ, _⟩ := not_not.mp (mt (A.cmType σ).mpr h)
    exact ⟨τ⟩

theorem mulVec_map_injective {K L : Type*} [Field K] [Field L] {n r : ℕ} (σ : K →+* L)
    (M : Matrix (Fin n) (Fin r) K) (hM : Function.Injective M.mulVec) : Function.Injective (M.map σ).mulVec := by
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.mulVecLin M)
    (LinearMap.ker_eq_bot.mpr hM)
  have hL : LinearMap.toMatrix' g * M = 1 := by
    have hM' : LinearMap.toMatrix' (Matrix.mulVecLin M) = M := by
      rw [← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin']
    rw [← hM', ← LinearMap.toMatrix'_comp, hg, LinearMap.toMatrix'_id]
  have hLσ : (LinearMap.toMatrix' g).map σ * M.map σ = 1 := by
    rw [← Matrix.map_mul, hL, Matrix.map_one _ (map_zero σ) (map_one σ)]
  intro c d hcd
  have h := congrArg ((LinearMap.toMatrix' g).map σ).mulVec hcd
  simpa only [Matrix.mulVec_mulVec, hLσ, Matrix.one_mulVec] using h

theorem proof : IsotropicRank.Statement := by
  intro Em _ _ _ Ψ _ N j A S hS
  obtain ⟨τ⟩ := nonempty_cmType A
  obtain ⟨P, hPu, hP⟩ := A.signature τ
  set U := Submodule.span Em S
  set r := Module.finrank Em U
  let b := Module.finBasis Em U
  let M : Matrix (Fin N) (Fin r) Em := Matrix.of fun i a => (b a : Fin N → Em) i
  have hMv : ∀ c, M *ᵥ c = ∑ a, c a • (b a : Fin N → Em) := by
    intro c
    ext i
    simp [M, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  have hli : LinearIndependent Em fun a => (b a : Fin N → Em) :=
    b.linearIndependent.map' U.subtype (Submodule.ker_subtype U)
  have hM : Function.Injective M.mulVec := by
    intro c d hcd
    have h0 : ∑ a, (c - d) a • (b a : Fin N → Em) = 0 := by
      rw [← hMv, Matrix.mulVec_sub]
      exact sub_eq_zero.mpr hcd
    funext a
    exact sub_eq_zero.mp (Fintype.linearIndependent_iff.mp hli _ h0 a)
  have hz : ∀ a a', hermForm Em A.H (b a) (b a') = 0 := fun a a' =>
    hermForm_span_eq_zero A.H S hS _ (b a).2 _ (b a').2
  set Mτ := M.map (A.emb τ)
  set Hτ := A.H.map (A.emb τ)
  have hG : Mτᴴ * Hτ * Mτ = 0 := by
    ext a a'
    have h := ShortIsotropic.emb_hermForm (A.emb τ) A.H (b a) (b a')
    rw [hz a a', map_zero] at h
    rw [Matrix.zero_apply, h]
    simp only [Mτ, Hτ, M, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.map_apply, Matrix.of_apply,
      dotProduct, Matrix.mulVec, Pi.star_apply, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have hq : ∀ c, star (Mτ *ᵥ c) ⬝ᵥ (Hτ *ᵥ (Mτ *ᵥ c)) = 0 := by
    intro c
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
      hG, Matrix.zero_mulVec, dotProduct_zero]
  let g : Fin (N - j) → Fin N := fun k => ⟨j + k, by omega⟩
  let f : (Fin r → ℂ) →ₗ[ℂ] (Fin (N - j) → ℂ) := LinearMap.funLeft ℂ ℂ g ∘ₗ Matrix.mulVecLin (P⁻¹ * Mτ)
  have hinj : Function.Injective f := by
    refine (injective_iff_map_eq_zero f).mpr fun c hc => ?_
    set y := P⁻¹ *ᵥ (Mτ *ᵥ c)
    have hy0 : ∀ a : Fin N, j ≤ (a : ℕ) → y a = 0 := by
      intro a ha
      have h := congrFun hc ⟨a - j, by omega⟩
      simp only [f, LinearMap.coe_comp, Function.comp_apply, LinearMap.funLeft_apply, Matrix.mulVecLin_apply,
        ← Matrix.mulVec_mulVec, Pi.zero_apply] at h
      have hg : g ⟨a - j, by omega⟩ = a := Fin.ext (by simp only [g]; omega)
      rwa [hg] at h
    have hw := ShortIsotropic.form_witt hP (Mτ *ᵥ c) (Mτ *ᵥ c)
    rw [hq c] at hw
    have hsum : ∑ a, Complex.normSq (y a) = 0 := by
      have h := congrArg Complex.re hw.symm
      simp only [signMat, Matrix.mulVec_diagonal, dotProduct, Pi.star_apply, Complex.re_sum,
        Complex.zero_re] at h
      rw [← h]
      refine Finset.sum_congr rfl fun a _ => ?_
      by_cases ha : (a : ℕ) < j
      · simp only [ha, if_true, one_mul, Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im,
          Complex.normSq_apply]
        ring
      · have h0 : ((P⁻¹ * Mτ) *ᵥ c) a = 0 := by
          rw [← Matrix.mulVec_mulVec]
          exact hy0 a (by omega)
        have h1 : y a = 0 := hy0 a (by omega)
        simp [ha, h0, h1]
    have hy : y = 0 := by
      funext a
      have h := (Finset.sum_eq_zero_iff_of_nonneg fun a _ => Complex.normSq_nonneg (y a)).mp hsum a
        (Finset.mem_univ a)
      exact Complex.normSq_eq_zero.mp h
    have hMc : Mτ *ᵥ c = 0 := by
      have : Mτ *ᵥ c = P *ᵥ y := by
        rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hPu, Matrix.one_mulVec]
      rw [this, hy, Matrix.mulVec_zero]
    exact mulVec_map_injective (A.emb τ) M hM (hMc.trans (Matrix.mulVec_zero Mτ).symm)
  have := LinearMap.finrank_le_finrank_of_injective hinj
  simpa only [Module.finrank_fin_fun] using this

end IsotropicRank

end GroundTheory.Heights₂.Heights.NineStatements
end
end

