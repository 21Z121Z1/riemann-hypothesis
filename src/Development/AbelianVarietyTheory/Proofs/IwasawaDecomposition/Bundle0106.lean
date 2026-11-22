import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.Bundle0001
import Formalism.LocalToGlobal.UnitaryNorms.Bundle0006
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0104
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0097
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0004
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0101
import Formalism.LocalToGlobal.Divisibility.Tuples

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompletelySplitPrimeHostPlaceProperties
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr
open scoped Pointwise

namespace GlobalTheory.Mem.Chr

section General

variable {L : Type} [Field L] [NumberField L]

theorem liesOver_span_of_natCast_mem {p : ℕ} (hp : p.Prime) (P : Ideal (𝓞 L)) [P.IsPrime] (h : ((p : ℕ) : 𝓞 L) ∈ P) :
    P.LiesOver (Ideal.span {(p : ℤ)}) := by
  have : Fact p.Prime := ⟨hp⟩
  have hm : (Ideal.span {(p : ℤ)}).IsMaximal := Int.ideal_span_isMaximal_of_prime p
  refine ⟨hm.eq_of_le (Ideal.IsPrime.under ℤ P).ne_top ?_⟩
  rw [Ideal.span_le, Set.singleton_subset_iff]
  show algebraMap ℤ (𝓞 L) (p : ℤ) ∈ P
  simpa using h

theorem ncard_places_eq_primesOver {p : ℕ} (hp : p.Prime) :
    {v : HeightOneSpectrum (𝓞 L) | ((p : ℕ) : 𝓞 L) ∈ v.asIdeal}.ncard =
      ((Ideal.span {(p : ℤ)}).primesOver (𝓞 L)).ncard := by
  rw [← Set.ncard_image_of_injective _ (fun v w h => HeightOneSpectrum.ext h :
    Function.Injective (HeightOneSpectrum.asIdeal (R := 𝓞 L)))]
  congr 1
  ext P
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨v.isPrime, liesOver_span_of_natCast_mem hp _ hv⟩
  · rintro ⟨h1, h2⟩
    have hm : ((p : ℕ) : 𝓞 L) ∈ P := by
      have : (p : ℤ) ∈ P.under ℤ := by rw [← h2.over]; exact Ideal.mem_span_singleton_self _
      simpa using (show algebraMap ℤ (𝓞 L) (p : ℤ) ∈ P from this)
    refine ⟨⟨P, h1, ?_⟩, hm, rfl⟩
    rintro rfl
    exact hp.ne_zero (by exact_mod_cast (Ideal.mem_bot.1 hm))

theorem splitsC_place [IsGalois ℚ L] {p : ℕ} (hp : p.Prime) (hs : SplitsC L p) (v : HeightOneSpectrum (𝓞 L))
    (hv : ((p : ℕ) : 𝓞 L) ∈ v.asIdeal) :
    Ideal.absNorm v.asIdeal = p ∧ ((p : ℕ) : 𝓞 L) ∉ v.asIdeal ^ 2 ∧
      ∀ σ : L ≃ₐ[ℚ] L, σ • v.asIdeal = v.asIdeal → σ = 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have := v.isPrime
  have := liesOver_span_of_natCast_mem hp _ hv
  have hm : (Ideal.span {(p : ℤ)}).IsMaximal := Int.ideal_span_isMaximal_of_prime p
  have h0 : (Ideal.span {(p : ℤ)}) ≠ ⊥ := by simpa using hp.ne_zero
  have h1 := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn (Ideal.span {(p : ℤ)}) (𝓞 L) (L ≃ₐ[ℚ] L)
  unfold SplitsC at hs
  rw [← ncard_places_eq_primesOver hp, hs, IsGalois.card_aut_eq_finrank] at h1
  have h2 : (Ideal.span {(p : ℤ)}).ramificationIdxIn (𝓞 L) * (Ideal.span {(p : ℤ)}).inertiaDegIn (𝓞 L) = 1 :=
    (mul_eq_left₀ Module.finrank_pos.ne').1 h1
  have h3 := Ideal.card_stabilizer_eq (G := L ≃ₐ[ℚ] L) (Ideal.span {(p : ℤ)}) v.asIdeal
  rw [h2] at h3
  have he := Nat.eq_one_of_mul_eq_one_right h2
  have hf := Nat.eq_one_of_mul_eq_one_left h2
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx _ v.asIdeal (L ≃ₐ[ℚ] L),
    ← Ideal.ramificationIdx'_eq_ramificationIdx (Ideal.span {(p : ℤ)}) v.asIdeal h0] at he
  rw [Ideal.inertiaDegIn_eq_inertiaDeg _ v.asIdeal (L ≃ₐ[ℚ] L)] at hf
  refine ⟨?_, ?_, ?_⟩
  · rw [← Ideal.pow_inertiaDeg p v.asIdeal, hf, pow_one]
  · intro h
    refine (Ideal.ramificationIdx'_ne_one_iff ?_).2 ?_ he
    · simpa [Ideal.map_span] using hv
    · simpa [Ideal.map_span] using h
  · intro σ hσ
    have : (MulAction.stabilizer (L ≃ₐ[ℚ] L) v.asIdeal) = ⊥ := Subgroup.card_eq_one.1 h3
    exact Subgroup.mem_bot.1 (this ▸ hσ)

theorem conjPl_iff_smul (σ : L ≃ₐ[ℚ] L) (v v' : HeightOneSpectrum (𝓞 L)) :
    ConjPl σ.toRingEquiv v v' ↔ σ • v.asIdeal = v'.asIdeal := by
  rw [conjPl_iff_mem]
  constructor
  · intro h
    ext y
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem]
    exact h _ _ (σ.apply_symm_apply (y : L)).symm
  · intro h x y hxy
    have e : y = σ • x := RingOfIntegers.ext hxy
    rw [e, ← h, Ideal.smul_mem_pointwise_smul_iff]

theorem under_smul_of_fix (b : L) (σ : L ≃ₐ[ℚ] L) (h : σ b = b) (P : Ideal (𝓞 L)) :
    (σ • P).under (𝓞 (IntermediateField.adjoin ℚ {b})) = P.under (𝓞 (IntermediateField.adjoin ℚ {b})) := by
  have hfix : ∀ x ∈ IntermediateField.adjoin ℚ {b}, σ x = x := by
    intro x hx
    have : IntermediateField.adjoin ℚ {b} ≤ IntermediateField.fixedField (Subgroup.zpowers σ) := by
      rw [IntermediateField.adjoin_simple_le_iff, IntermediateField.mem_fixedField_iff]
      rintro _ hτ
      have : Subgroup.zpowers σ ≤ MulAction.stabilizer _ b := (Subgroup.zpowers_le).2 h
      exact this hτ
    exact (IntermediateField.mem_fixedField_iff _ _).1 (this hx) σ (Subgroup.mem_zpowers σ)
  ext a
  have e : σ • algebraMap _ (𝓞 L) a = algebraMap _ (𝓞 L) a := RingOfIntegers.ext (hfix _ (a : IntermediateField.adjoin ℚ {b}).2)
  rw [Ideal.mem_under, Ideal.mem_under]
  conv_lhs => rw [← e]
  rw [Ideal.smul_mem_pointwise_smul_iff]

theorem exists_smul_fix_of_under_eq [IsGalois ℚ L] (b : L) (P P' : Ideal (𝓞 L)) [P.IsPrime] [P'.IsPrime]
    (h : P.under (𝓞 (IntermediateField.adjoin ℚ {b})) = P'.under (𝓞 (IntermediateField.adjoin ℚ {b}))) :
    ∃ σ : L ≃ₐ[ℚ] L, σ b = b ∧ σ • P = P' := by
  set K := IntermediateField.adjoin ℚ {b} with hK
  have : P'.LiesOver (P.under (𝓞 K)) := ⟨h⟩
  obtain ⟨τ, hτ⟩ := Ideal.exists_smul_eq_of_isGaloisGroup (P.under (𝓞 K)) P P' (L ≃ₐ[K] L)
  refine ⟨τ.restrictScalars ℚ, τ.commutes (⟨b, IntermediateField.mem_adjoin_simple_self ℚ b⟩ : K), ?_⟩
  rw [← hτ]
  ext y
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem, Ideal.mem_pointwise_smul_iff_inv_smul_mem]
  rfl

theorem under_eq_iff_under_ne [IsGalois ℚ L] {p : ℕ} (hp : p.Prime) (hs : SplitsC L p) (b : L) (hb0 : b ≠ 0)
    (hb : ∀ σ : L ≃ₐ[ℚ] L, σ b = b ∨ σ b = -b) (c : L ≃ₐ[ℚ] L) (hc : c b = -b)
    (v v' : HeightOneSpectrum (𝓞 L)) (hv : ((p : ℕ) : 𝓞 L) ∈ v.asIdeal) (hvv : c • v.asIdeal = v'.asIdeal)
    (Q : HeightOneSpectrum (𝓞 (IntermediateField.adjoin ℚ {b})))
    (hQ : ((p : ℕ) : 𝓞 (IntermediateField.adjoin ℚ {b})) ∈ Q.asIdeal) :
    v.under (𝓞 (IntermediateField.adjoin ℚ {b})) = Q ↔ v'.under (𝓞 (IntermediateField.adjoin ℚ {b})) ≠ Q := by
  have := v.isPrime
  have := v'.isPrime
  constructor
  · rintro rfl h
    obtain ⟨σ, hσb, hσ⟩ := exists_smul_fix_of_under_eq b v.asIdeal v'.asIdeal
      (congrArg HeightOneSpectrum.asIdeal h).symm
    have h1 : σ⁻¹ * c = 1 := (splitsC_place hp hs v hv).2.2 _ (by rw [mul_smul, hvv, ← hσ, inv_smul_smul])
    rw [inv_mul_eq_one] at h1
    rw [h1, hc] at hσb
    exact hb0 (by linear_combination (-1 / 2 : L) * hσb)
  · intro h
    have := Q.isPrime
    obtain ⟨⟨W, hW, hWQ⟩⟩ := (inferInstance : Nonempty (Q.asIdeal.primesOver (𝓞 L)))
    have hpW : ((p : ℕ) : 𝓞 L) ∈ W := by
      rw [hWQ.over, Ideal.mem_under] at hQ
      simpa using hQ
    have := liesOver_span_of_natCast_mem hp _ hv
    have := liesOver_span_of_natCast_mem hp _ hpW
    obtain ⟨σ, hσ⟩ := Ideal.exists_smul_eq_of_isGaloisGroup (Ideal.span {(p : ℤ)}) v.asIdeal W (L ≃ₐ[ℚ] L)
    rcases hb σ with h1 | h1
    · apply HeightOneSpectrum.ext
      rw [hWQ.over, ← hσ, under_smul_of_fix b σ h1]
      rfl
    · exfalso
      apply h
      apply HeightOneSpectrum.ext
      have h2 : (σ * c⁻¹) b = b := by
        have : c⁻¹ b = -b := by
          have h3 : c⁻¹ (c b) = b := c.symm_apply_apply b
          rw [hc, map_neg] at h3
          exact neg_eq_iff_eq_neg.1 h3
        rw [AlgEquiv.mul_apply, this, map_neg, h1, neg_neg]
      have h4 : (σ * c⁻¹) • v'.asIdeal = W := by rw [← hvv, mul_smul, inv_smul_smul, hσ]
      rw [hWQ.over, ← h4, under_smul_of_fix b _ h2]
      rfl

end General

open Classical in

theorem splitsC_main : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (p : ℕ), p.Prime → SplitsC H.E p → ∀ v : HeightOneSpectrum (𝓞 H.E), OverP H p v → Ideal.absNorm v.asIdeal = p ∧ ((p : ℕ) : 𝓞 H.E) ∉ v.asIdeal ^ 2 ∧ IsSplitPl H v ∧ ∀ (Q : HeightOneSpectrum (𝓞 H.K)), ((p : ℕ) : 𝓞 H.K) ∈ Q.asIdeal → ∀ v', ConjPl H.conj.toRingEquiv v v' → OverP H p v' ∧ (v.under (𝓞 H.K) = Q ↔ v'.under (𝓞 H.K) ≠ Q) := by
  intro R H p hp hs v hv
  have hG : IsGalois ℚ H.E := H.hostE_isGalois
  have hsq := H.sqrtMinusD_sq
  have hc := H.conj_sqrtMinusD
  have hb0 : H.sqrtMinusD ≠ 0 := by
    intro h
    rw [h] at hsq
    have : (H.d : H.E) = 0 := by linear_combination hsq
    have h1 : H.d = 0 := by exact_mod_cast this
    have := H.qd_big.2
    omega
  have hb : ∀ σ : H.E ≃ₐ[ℚ] H.E, σ H.sqrtMinusD = H.sqrtMinusD ∨ σ H.sqrtMinusD = -H.sqrtMinusD := by
    intro σ
    apply sq_eq_sq_iff_eq_or_eq_neg.1
    rw [← map_pow, hsq, map_neg, map_natCast]
  obtain ⟨h1, h2, h3⟩ := splitsC_place hp hs v hv
  refine ⟨h1, h2, ?_, fun Q hQ v' hvv => ⟨?_, ?_⟩⟩
  · by_contra hn
    unfold IsSplitPl at hn
    push Not at hn
    have hle : H.conj • v.asIdeal ≤ v.asIdeal := by
      intro y hy
      rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem] at hy
      obtain ⟨z, hz, hzv⟩ := hn _ hy
      have e : z = y := RingOfIntegers.ext (hz.trans (H.conj.apply_symm_apply (y : H.E)))
      exact e ▸ hzv
    obtain ⟨w, hw, -⟩ := existsUnique_conjPl H.conj.toRingEquiv v
    have hw' := (conjPl_iff_smul H.conj v w).1 hw
    have heq : H.conj • v.asIdeal = v.asIdeal := by
      rw [hw'] at hle ⊢
      exact w.isMaximal.eq_of_le v.isPrime.ne_top hle
    rw [h3 _ heq] at hc
    have hc' : H.sqrtMinusD = -H.sqrtMinusD := hc
    exact hb0 (by linear_combination (1 / 2 : H.E) * hc')
  · exact ((conjPl_iff_mem _ v v').1 hvv _ _ (by simp)).1 hv
  · exact under_eq_iff_under_ne hp hs H.sqrtMinusD hb0 hb H.conj hc v v' hv ((conjPl_iff_smul H.conj v v').1 hvv) Q hQ

end GlobalTheory.Mem.Chr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOfTameLoc
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr

namespace GlobalTheory.ModelChar

def argU : ℂˣ →* ℂˣ where
  toFun z := Units.mk0 ((z : ℂ) / ((‖(z : ℂ)‖ : ℝ) : ℂ))
    (div_ne_zero z.ne_zero (by exact_mod_cast norm_ne_zero_iff.2 z.ne_zero))
  map_one' := by ext; simp
  map_mul' x y := by
    ext
    simp only [Units.val_mul, Units.val_mk0, norm_mul, Complex.ofReal_mul]
    rw [mul_div_mul_comm]

theorem argU_val (z : ℂˣ) : ((argU z : ℂˣ) : ℂ) = (z : ℂ) / ((‖(z : ℂ)‖ : ℝ) : ℂ) := rfl

theorem norm_argU (z : ℂˣ) : ‖((argU z : ℂˣ) : ℂ)‖ = 1 := by
  rw [argU_val, norm_div, Complex.norm_real, norm_norm, div_self (norm_ne_zero_iff.2 z.ne_zero)]

theorem continuous_argU : Continuous argU := by
  rw [Units.isEmbedding_val₀.continuous_iff]
  exact Units.continuous_val.div (Complex.continuous_ofReal.comp Units.continuous_val.norm)
    fun z => by exact_mod_cast norm_ne_zero_iff.2 z.ne_zero

variable {L : Type} [Field L] [NumberField L]

def finEv (v : HeightOneSpectrum (𝓞 L)) : AdeleRing (𝓞 L) L →* v.adicCompletion L where
  toFun a := a.2 v
  map_one' := rfl
  map_mul' _ _ := rfl

def infEv (w : InfinitePlace L) : AdeleRing (𝓞 L) L →* w.Completion where
  toFun a := a.1 w
  map_one' := rfl
  map_mul' _ _ := rfl

theorem continuous_finEv (v : HeightOneSpectrum (𝓞 L)) : Continuous (finEv v) :=
  (RestrictedProduct.continuous_eval v).comp continuous_snd

theorem continuous_infEv (w : InfinitePlace L) : Continuous (infEv w) :=
  (continuous_apply w).comp continuous_fst

theorem finEv_local_self (v : HeightOneSpectrum (𝓞 L)) (x : (v.adicCompletion L)ˣ) :
    Units.map (finEv v) (localIdele L v x) = x := by
  classical
  apply Units.ext
  exact Function.update_self v (x : v.adicCompletion L) (fun w : HeightOneSpectrum (𝓞 L) => (1 : w.adicCompletion L))

theorem finEv_local_ne {v w : HeightOneSpectrum (𝓞 L)} (h : w ≠ v) (x : (v.adicCompletion L)ˣ) :
    Units.map (finEv w) (localIdele L v x) = 1 := by
  classical
  apply Units.ext
  exact Function.update_of_ne h (x : v.adicCompletion L) (fun w : HeightOneSpectrum (𝓞 L) => (1 : w.adicCompletion L))

theorem infEv_local (w : InfinitePlace L) (v : HeightOneSpectrum (𝓞 L)) (x : (v.adicCompletion L)ˣ) :
    Units.map (infEv w) (localIdele L v x) = 1 := Units.ext rfl

theorem finEv_inf (v : HeightOneSpectrum (𝓞 L)) (w : InfinitePlace L) (x : (w.Completion)ˣ) :
    Units.map (finEv v) (infIdele L w x) = 1 := Units.ext rfl

theorem infEv_inf_self (w : InfinitePlace L) (x : (w.Completion)ˣ) :
    Units.map (infEv w) (infIdele L w x) = x := by
  classical
  apply Units.ext
  exact Pi.mulSingle_eq_same (M := fun w : InfinitePlace L => w.Completion) w (x : w.Completion)

theorem infEv_inf_ne {w u : InfinitePlace L} (h : u ≠ w) (x : (w.Completion)ˣ) :
    Units.map (infEv u) (infIdele L w x) = 1 := by
  classical
  apply Units.ext
  exact Pi.mulSingle_eq_of_ne (M := fun w : InfinitePlace L => w.Completion) h (x : w.Completion)

theorem infEv_infDiag (w : InfinitePlace L) (k : Lˣ) : Units.map (infEv w) (infDiag k) = atInf w k := by
  unfold infDiag
  rw [MonoidHom.finsetProd_apply, map_prod, Finset.prod_eq_single w]
  · exact infEv_inf_self w _
  · intro u _ hu
    exact infEv_inf_ne hu.symm _
  · simp

theorem finEv_infDiag (v : HeightOneSpectrum (𝓞 L)) (k : Lˣ) : Units.map (finEv v) (infDiag k) = 1 := by
  unfold infDiag
  rw [MonoidHom.finsetProd_apply, map_prod]
  exact Finset.prod_eq_one fun w _ => finEv_inf v w _

theorem infEv_diag (w : InfinitePlace L) (k : Lˣ) : Units.map (infEv w) (diagUnits L k) = atInf w k := Units.ext rfl

theorem finEv_diag (v : HeightOneSpectrum (𝓞 L)) (k : Lˣ) : Units.map (finEv v) (diagUnits L k) = atFin v k :=
  Units.ext rfl

theorem continuous_of_tameLoc {v : HeightOneSpectrum (𝓞 L)} {θ : (v.adicCompletion L)ˣ →* ℂˣ} (h : TameLoc v θ) :
    Continuous θ := by
  refine continuous_of_continuousAt_one θ ?_
  have hc : Continuous fun x : (v.adicCompletion L)ˣ => (x : v.adicCompletion L) - 1 :=
    Units.continuous_val.sub continuous_const
  have ho : IsOpen {y : v.adicCompletion L | Valued.v y < 1} := by
    have := Valued.isOpen_ball (v.adicCompletion L) 1
    simpa only [Valuation.restrict_lt_one_iff] using this
  have hn : {x : (v.adicCompletion L)ˣ | Valued.v ((x : v.adicCompletion L) - 1) < 1} ∈ nhds (1 : (v.adicCompletion L)ˣ) :=
    (ho.preimage hc).mem_nhds (by simp)
  refine (continuousAt_const (y := (1 : ℂˣ))).congr ?_
  filter_upwards [hn] with x hx
  refine (h.2 x ?_ ?_).symm
  · have := Valuation.map_one_add_of_lt (Valued.v : Valuation (v.adicCompletion L) _) hx
    rwa [add_sub_cancel] at this
  · have := (WithZero.lt_mul_exp_iff_le (x := Valued.v ((x : v.adicCompletion L) - 1)) (y := WithZero.exp (-1 : ℤ)) WithZero.exp_ne_zero).1
    apply this
    rw [← WithZero.exp_add]
    simpa using hx

open Classical in

theorem exists_modelChar : ∀ (L : Type) [Field L] [NumberField L] (I : Type) [Fintype I] (φ : I → L →+* ℂ), (Function.Bijective fun i => InfinitePlace.mk (φ i)) → ∀ (n : I → ℤ) (S : Finset (HeightOneSpectrum (𝓞 L))) (θ : ∀ v : HeightOneSpectrum (𝓞 L), (v.adicCompletion L)ˣ →* ℂˣ), (∀ v ∈ S, TameLoc v (θ v)) → ∃ ψ : Ideles L →* ℂˣ, Continuous ψ ∧ (∀ x, ‖((ψ x : ℂˣ) : ℂ)‖ = 1) ∧ (∀ i (k : Lˣ), ((ψ (infIdele L (InfinitePlace.mk (φ i)) (atInf _ k)) : ℂˣ) : ℂ) = (φ i (k : L) / ((‖φ i (k : L)‖ : ℝ) : ℂ)) ^ n i) ∧ (∀ v ∈ S, ∀ x, ψ (localIdele L v x) = θ v x) ∧ (∀ v ∉ S, ∀ x, ψ (localIdele L v x) = 1) ∧ ∀ k : Lˣ, ψ (diagUnits L k) = ψ (infDiag k) * ∏ v ∈ S, θ v (atFin v k) := by
  intro L _ _ I _ φ hφ n S θ hθ
  choose e hec he using fun i => GlobalTheory.InfTypeLocal.exists_ext (φ i)
  obtain ⟨ψ, hψ⟩ : ∃ ψ : Ideles L →* ℂˣ, ∀ a, ψ a =
      (∏ i, argU (Units.map (e i).toMonoidHom (Units.map (infEv (InfinitePlace.mk (φ i))) a)) ^ n i) *
        ∏ v ∈ S, θ v (Units.map (finEv v) a) :=
    ⟨{ toFun := fun a =>
        (∏ i, argU (Units.map (e i).toMonoidHom (Units.map (infEv (InfinitePlace.mk (φ i))) a)) ^ n i) *
          ∏ v ∈ S, θ v (Units.map (finEv v) a)
       map_one' := by simp only [map_one, one_zpow, Finset.prod_const_one, mul_one]
       map_mul' := fun a b => by
        simp only [map_mul, mul_zpow, Finset.prod_mul_distrib]
        rw [mul_mul_mul_comm] }, fun _ => rfl⟩
  refine ⟨ψ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show (ψ : Ideles L → ℂˣ) = _ from funext hψ]
    refine Continuous.mul (continuous_finsetProd _ fun i _ => ?_) (continuous_finsetProd _ fun v hv => ?_)
    · exact (continuous_argU.comp ((Continuous.units_map _ (hec i)).comp
        (Continuous.units_map _ (continuous_infEv _)))).zpow _
    · exact (continuous_of_tameLoc (hθ v hv)).comp (Continuous.units_map _ (continuous_finEv v))
  · intro x
    rw [hψ, Units.val_mul, Units.coe_prod, Units.coe_prod, norm_mul, norm_prod, norm_prod,
      Finset.prod_eq_one, Finset.prod_eq_one, one_mul]
    · exact fun v hv => (hθ v hv).1 _
    · intro i _
      rw [Units.val_zpow_eq_zpow_val, norm_zpow, norm_argU, one_zpow]
  · intro i k
    rw [hψ, Finset.prod_eq_one (s := S), mul_one, Finset.prod_eq_single i, infEv_inf_self,
      Units.val_zpow_eq_zpow_val, argU_val, ← he i k]
    · rfl
    · intro j _ hj
      rw [infEv_inf_ne (fun hh => hj (hφ.1 hh)), map_one, map_one, one_zpow]
    · simp
    · intro v _
      rw [finEv_inf, map_one]
  · intro v hv x
    rw [hψ, Finset.prod_eq_one, one_mul, Finset.prod_eq_single_of_mem v hv, finEv_local_self]
    · intro w _ hw
      rw [finEv_local_ne hw, map_one]
    · intro i _
      rw [infEv_local, map_one, map_one, one_zpow]
  · intro v hv x
    rw [hψ, Finset.prod_eq_one, one_mul, Finset.prod_eq_one]
    · intro w hw
      have hne : w ≠ v := fun hh => hv (hh ▸ hw)
      rw [finEv_local_ne hne, map_one]
    · intro i _
      rw [infEv_local, map_one, map_one, one_zpow]
  · intro k
    rw [hψ, hψ]
    simp only [infEv_diag, finEv_diag, infEv_infDiag, finEv_infDiag, map_one, Finset.prod_const_one, mul_one]

end GlobalTheory.ModelChar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsExponentThetaData
section
noncomputable section
namespace GlobalTheory.MemN
open Formalism.BasicNotions GlobalTheory.Mem NumberField IsDedekindDomain

section
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} [NumberField what₂.LL] [StarRing what₂.LL]
  {LL0 : IntermediateField ℚ what₂.LL} {nd : NData R H what₂} (tw : NTw R H what₂ LL0 nd)

def nexpOfEmpty [IsEmpty tw.Tw] (e : G0g nd → ↥LL0) : NExp R H what₂ LL0 nd tw where
  U := ⊥
  eLL0 := e
  Fm := fun i => isEmptyElim i
  acgFm := fun i => isEmptyElim i
  modFmK := fun i => isEmptyElim i
  modFmO := fun i => isEmptyElim i
  towFm := fun i => isEmptyElim i
  fdFm := fun i => isEmptyElim i
  actG := fun i => isEmptyElim i
  psiU := fun i => isEmptyElim i
  eAlg := fun i => isEmptyElim i
  eAlg_def := fun i => isEmptyElim i
  eAlg_idem := fun i => isEmptyElim i
  eAlg_central := fun i => isEmptyElim i
  Bsup := fun i => isEmptyElim i
  Dat := fun i => isEmptyElim i
  th := fun i => isEmptyElim i
  lev := fun i => isEmptyElim i
  thPsi := fun i => isEmptyElim i
  thPsi_one := fun i => isEmptyElim i
  thU := fun i => isEmptyElim i
  twPsi := fun i => isEmptyElim i
  twPsi_one := fun i => isEmptyElim i
  twDel := fun i => isEmptyElim i
  delU := fun i => isEmptyElim i
  delU_unr := fun i => isEmptyElim i
  delU_l := fun i => isEmptyElim i
  delU_anti := fun i => isEmptyElim i
  delU_open := fun i => isEmptyElim i
  delU_res := fun i => isEmptyElim i
  delU_conj := fun i => isEmptyElim i
  MtV := fun i => isEmptyElim i
  acgMt := fun i => isEmptyElim i
  modMtK := fun i => isEmptyElim i
  modMtO := fun i => isEmptyElim i
  towMt := fun i => isEmptyElim i
  fdMt := fun i => isEmptyElim i
  MtLat := fun i => isEmptyElim i
  MtLat_fg := fun i => isEmptyElim i
  MtLat_span := fun i => isEmptyElim i
  thP := fun i => isEmptyElim i
  hkF := fun i => isEmptyElim i
  embB := fun i => isEmptyElim i
  embB_inj := fun i => isEmptyElim i
  eH := fun i => isEmptyElim i
  eH_idem := fun i => isEmptyElim i

def nthOfEmpty [IsEmpty tw.Tw] (Y : NExp R H what₂ LL0 nd tw) : NTh R H what₂ LL0 nd tw Y where
  iC := fun i => isEmptyElim i
  iC_int := fun i => isEmptyElim i
  aL := fun i => isEmptyElim i
  aL_g := fun i => isEmptyElim i
  aL_off := fun i => isEmptyElim i
  Pt := fun i => isEmptyElim i
  ev := fun i => isEmptyElim i
  ev_smul := fun i => isEmptyElim i
  ev_inj := fun i => isEmptyElim i
  Lt := fun i => isEmptyElim i
  acgLt := fun i => isEmptyElim i
  modLt := fun i => isEmptyElim i
  freeLt := fun i => isEmptyElim i
  finLt := fun i => isEmptyElim i
  Let := fun i => isEmptyElim i
  finLet := fun i => isEmptyElim i
  Harm := fun i => isEmptyElim i
  Ctr := fun i => isEmptyElim i
  ctrC := fun i => isEmptyElim i
  Harm_def := fun i => isEmptyElim i
  thV := fun i => isEmptyElim i
  thV_add := fun i => isEmptyElim i
  thV_smul := fun i => isEmptyElim i
  thV_addP := fun i => isEmptyElim i
  thV_smulP := fun i => isEmptyElim i
  datPhi := fun i => isEmptyElim i
  datP := fun i => isEmptyElim i
  recDet := fun i => isEmptyElim i
  Kq := fun i => isEmptyElim i
  grpKq := fun i => isEmptyElim i
  actK := fun i => isEmptyElim i
  actK_one := fun i => isEmptyElim i
  actK_mul := fun i => isEmptyElim i
  recDetq := fun i => isEmptyElim i
  recDetq_mem := fun i => isEmptyElim i
  recDet_act := fun i => isEmptyElim i
  recDetq_act := fun i => isEmptyElim i
  hkIdx := fun i => isEmptyElim i
  finHk := fun i => isEmptyElim i
  hkMove := fun i => isEmptyElim i
  hkU := fun i => isEmptyElim i
  hk_ev := fun i => isEmptyElim i
  MaximalUnramifiedExtension := fun i => isEmptyElim i
  FmUr := fun i => isEmptyElim i
  FmUr_smul := fun i => isEmptyElim i
  FmUr_span := fun i => isEmptyElim i
  Bsup_def := fun i => isEmptyElim i

end

theorem exists_nexp_nth_of_isEmpty (B : Base) (C : Cols B) (W : RowsRest B C) (nd : NData B.R B.host W.what₂)
    (tw : NTw B.R B.host W.what₂ B.LL0 nd) (h : IsEmpty tw.Tw) (e : G0g nd → ↥B.LL0) :
    ∃ Y : NExp B.R B.host W.what₂ B.LL0 nd tw, Y.eLL0 = e ∧ Nonempty (NTh B.R B.host W.what₂ B.LL0 nd tw Y) :=
  ⟨nexpOfEmpty tw e, rfl, ⟨nthOfEmpty tw _⟩⟩

end GlobalTheory.MemN
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdeleCharacterTrivialOnLocalUnitsStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idele_character_trivial_on_local_units : ∀ (L : Type) [Field L] [NumberField L] (ψ : Ideles L →* ℂˣ), Continuous ψ → ∀ a : Ideles L, a ∈ unitIdl L → (∀ w, (a : AdeleRing (𝓞 L) L).1 w = 1) → (∀ v (x : (v.adicCompletion L)ˣ), (x : v.adicCompletion L) = (a : AdeleRing (𝓞 L) L).2 v → ψ (localIdele L v x) = 1) → ψ a = 1 := by
  first | exact @GlobalTheory.Mem.LocTriv.eq_one_of_local | exact GlobalTheory.Mem.LocTriv.eq_one_of_local | (intros; apply GlobalTheory.Mem.LocTriv.eq_one_of_local <;> assumption)
end

