import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0049
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0022
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0002
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0236
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.ValuationResidueLemmas
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HDiscAE
import Formalism.LocalToGlobal.ProjectiveLattices.CurveLoc

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.CaspowExpand
section
open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.TypeSum

open GlobalTheory.LowTypeDetermined

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Mx n → (H →L[ℂ] H)}

theorem Dw_comb (hσ : IsURepOn (UJset ε) σ) {l : List (Mx n)} (hl : ∀ X ∈ l, X ∈ lieSet ε) {v : H}
    (hv : Sm ε σ v) (L : List (ℂ × List (Mx n))) (hL : ∀ u ∈ L, ∀ Y ∈ u.2, Y ∈ lieSet ε) :
    Sm ε σ ((L.map fun u => u.1 • Dw σ u.2 v).sum) ∧
      Dw σ l ((L.map fun u => u.1 • Dw σ u.2 v).sum) = (L.map fun u => u.1 • Dw σ (l ++ u.2) v).sum := by
  induction L with
  | nil =>
    refine ⟨(smooth (Jm ε) σ).zero_mem, ?_⟩
    have h := Dw_smul hσ hl (0 : ℂ) hv
    simpa using h
  | cons u L ih =>
    have hu : Sm ε σ (Dw σ u.2 v) := hv.word hσ (hL u List.mem_cons_self)
    obtain ⟨ih1, ih2⟩ := ih fun w hw => hL w (List.mem_cons_of_mem _ hw)
    have hs : Sm ε σ (u.1 • Dw σ u.2 v) := (smooth (Jm ε) σ).smul_mem u.1 hu
    refine ⟨?_, ?_⟩
    · simp only [List.map_cons, List.sum_cons]
      exact (smooth (Jm ε) σ).add_mem hs ih1
    · simp only [List.map_cons, List.sum_cons]
      rw [Dw_add hσ hl hs ih1, Dw_smul hσ hl u.1 hu, ← Dw_append, ih2]

theorem sum_neg_comb (L : List (ℂ × List (Mx n))) (f : List (Mx n) → H) :
    (L.map fun u => (-u.1) • f u.2).sum = -(L.map fun u => u.1 • f u.2).sum := by
  induction L with
  | nil => simp
  | cons u L ih =>
    simp only [List.map_cons, List.sum_cons, neg_smul, neg_add] at *
    rw [ih]

theorem sum_norm_neg (L : List (ℂ × List (Mx n))) (f : List (Mx n) → List (Mx n)) :
    ((L.map fun u => ((-u.1, f u.2) : ℂ × List (Mx n))).map fun u => ‖u.1‖).sum = (L.map fun u => ‖u.1‖).sum := by
  simp [List.map_map, Function.comp_def]

theorem sum_flatMap' {α M : Type} [AddCommMonoid M] (l : List α) (f : α → List M) :
    (l.flatMap f).sum = (l.map fun i => (f i).sum).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.flatMap_cons, ih]

theorem caspow_expand : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Mx n → (H →L[ℂ] H)), IsURepOn (UJset ε) σ → ∀ (d : ℕ) (X : Fin d → Mx n), (∀ i, X i ∈ lieSet ε) →
    ∀ r : ℕ, ∃ L : List (ℂ × List (Mx n)), (∀ u ∈ L, u.2.length ≤ 2 * r ∧ ∀ Y ∈ u.2, ∃ i, X i = Y) ∧
      (L.map fun u => ‖u.1‖).sum ≤ (1 + (d : ℝ)) ^ r ∧
      ∀ v, Sm ε σ v → (onePlusCas σ X)^[r] v = (L.map fun u => u.1 • Dw σ u.2 v).sum := by
  intro n ε H _ _ σ hσ d X hX r
  induction r with
  | zero =>
    refine ⟨[(1, [])], ?_, ?_, ?_⟩
    · simp
    · simp
    · intro v _; simp
  | succ r ih =>
    obtain ⟨L, hL1, hL2, hL3⟩ := ih
    have hLie : ∀ u ∈ L, ∀ Y ∈ u.2, Y ∈ lieSet ε := fun u hu Y hY => by
      obtain ⟨i, rfl⟩ := (hL1 u hu).2 Y hY
      exact hX i
    let M : Fin d → List (ℂ × List (Mx n)) := fun i => L.map fun u => (-u.1, X i :: X i :: u.2)
    refine ⟨L ++ (List.finRange d).flatMap M, ?_, ?_, ?_⟩
    · intro u hu
      rcases List.mem_append.1 hu with hu | hu
      · exact ⟨(hL1 u hu).1.trans (by omega), (hL1 u hu).2⟩
      · obtain ⟨i, -, hu⟩ := List.mem_flatMap.1 hu
        obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hu
        refine ⟨?_, ?_⟩
        · simp only [List.length_cons]; have := (hL1 w hw).1; omega
        · intro Y hY
          simp only [List.mem_cons] at hY
          rcases hY with rfl | rfl | hY
          · exact ⟨i, rfl⟩
          · exact ⟨i, rfl⟩
          · exact (hL1 w hw).2 Y hY
    · have hM : ∀ i, ((M i).map fun u => ‖u.1‖).sum = (L.map fun u => ‖u.1‖).sum := fun i => sum_norm_neg L (fun l => X i :: X i :: l)
      rw [List.map_append, List.sum_append, List.map_flatMap, sum_flatMap']
      simp only [hM, List.map_const', List.sum_replicate, List.length_finRange, nsmul_eq_mul]
      have h0 : 0 ≤ (L.map fun u => ‖u.1‖).sum := List.sum_nonneg fun x hx => by
        obtain ⟨u, -, rfl⟩ := List.mem_map.1 hx; exact norm_nonneg _
      rw [pow_succ]
      nlinarith [pow_nonneg (by positivity : (0:ℝ) ≤ 1 + d) r]
    · intro v hv
      have hi : ∀ i, dRep σ (X i) (dRep σ (X i) (L.map fun u => u.1 • Dw σ u.2 v).sum) =
          (L.map fun u => u.1 • Dw σ (X i :: X i :: u.2) v).sum := fun i =>
        (Dw_comb hσ (l := [X i, X i]) (by simp [hX i]) hv L hLie).2
      have hMi : ∀ i, ((M i).map fun u => u.1 • Dw σ u.2 v).sum =
          -(L.map fun u => u.1 • Dw σ (X i :: X i :: u.2) v).sum := fun i => by
        rw [← sum_neg_comb L (fun l => Dw σ (X i :: X i :: l) v)]
        simp [M, List.map_map, Function.comp_def]
      rw [Function.iterate_succ_apply', hL3 v hv, onePlusCas]
      simp only [hi]
      rw [List.map_append, List.sum_append, List.map_flatMap, sum_flatMap', ← Fin.sum_univ_def]
      simp only [hMi, Finset.sum_neg_distrib, sub_eq_add_neg]

end GlobalTheory.TypeSum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.ContainsRayFieldComp
section
open NumberField IsDedekindDomain

namespace GlobalTheory.RayDescent

theorem dvd_intNorm_sub_one (K E : Type) [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E] (n : ℕ)
    (a : 𝓞 E) (h : (n : 𝓞 E) ∣ a - 1) : (n : 𝓞 K) ∣ Algebra.intNorm (𝓞 K) (𝓞 E) a - 1 := by
  classical
  obtain ⟨c, hc⟩ := h
  have ha : a = 1 + n * c := by rw [← hc]; ring
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [ha]
  let F := AlgebraicClosure E
  let r : (E →ₐ[K] F) → (𝓞 E →+* 𝓞 F) := fun σ => RingOfIntegers.mapRingHom (σ : E →+* F)
  have hd : (n : 𝓞 F) ∣ (∏ σ : E →ₐ[K] F, r σ a) - 1 := by
    have : ∀ s : Finset (E →ₐ[K] F), (n : 𝓞 F) ∣ (∏ σ ∈ s, r σ a) - 1 := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp
      | insert σ s hσ ih =>
        rw [Finset.prod_insert hσ]
        obtain ⟨d, hd⟩ := ih
        refine ⟨r σ a * d + r σ c, ?_⟩
        have h1 : r σ a = 1 + n * r σ c := by rw [ha]; simp
        have h2 : ∏ σ ∈ s, r σ a = 1 + n * d := by rw [← hd]; ring
        rw [h2, h1]; ring
    exact this _
  obtain ⟨d, hd⟩ := hd
  set N := Algebra.intNorm (𝓞 K) (𝓞 E) a with hN
  have hNK : (N : K) = Algebra.norm K (a : E) := Algebra.algebraMap_intNorm (L := E) a
  have hprod : algebraMap K F (N : K) = 1 + n * (d : F) := by
    rw [hNK, Algebra.norm_eq_prod_embeddings K F]
    have := congrArg (algebraMap (𝓞 F) F) hd
    rw [map_sub, map_prod, map_one, map_mul, map_natCast] at this
    rw [← this]
    simp [r]
  have hnK : (n : K) ≠ 0 := by exact_mod_cast hn.ne'
  have hnF : (n : F) ≠ 0 := by exact_mod_cast hn.ne'
  have hy : algebraMap K F (((N : K) - 1) / n) = d := by
    rw [map_div₀, map_sub, hprod, map_one, map_natCast]
    rw [add_sub_cancel_left, mul_div_cancel_left₀ _ hnF]
  have hint : IsIntegral ℤ (((N : K) - 1) / n) := by
    rw [← isIntegral_algebraMap_iff (algebraMap K F).injective, hy]
    exact d.isIntegral_coe
  obtain ⟨y, hy'⟩ : ∃ y : 𝓞 K, (y : K) = ((N : K) - 1) / n := ⟨⟨_, hint⟩, rfl⟩
  refine ⟨y, ?_⟩
  apply RingOfIntegers.ext
  change algebraMap (𝓞 K) K (N - 1) = algebraMap (𝓞 K) K (n * y)
  rw [map_sub, map_mul, map_one, map_natCast]
  change (N : K) - 1 = n * (y : K)
  rw [hy', mul_div_cancel₀ _ hnK]

theorem containsRayField_comp (K E L : Type) [Field K] [NumberField K] [Field E] [NumberField E] [Field L] [NumberField L]
    (φ : K →+* E) (ψ : E →+* L) (n : ℕ) (h : GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.ContainsRayField ψ n) :
    GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.ContainsRayField (ψ.comp φ) n := by
  intro P hP
  obtain ⟨f, α, h1, h2, h3⟩ := h P hP
  letI : Algebra K E := φ.toAlgebra
  letI : Algebra E L := ψ.toAlgebra
  have hq : P.asIdeal.comap (RingOfIntegers.mapRingHom ψ) = P.asIdeal.under (𝓞 E) := rfl
  have hp : P.asIdeal.comap (RingOfIntegers.mapRingHom (ψ.comp φ)) = (P.asIdeal.under (𝓞 E)).under (𝓞 K) := by
    ext x
    rfl
  rw [hq] at h1 h2
  rw [hp]
  haveI := P.isMaximal
  set q := P.asIdeal.under (𝓞 E)
  set p := q.under (𝓞 K)
  haveI : q.IsMaximal := inferInstance
  haveI : p.IsMaximal := inferInstance
  have hrel : Ideal.relNorm (𝓞 K) q = p ^ q.inertiaDeg (𝓞 K) := Ideal.relNorm_eq_pow_of_isMaximal q p
  refine ⟨q.inertiaDeg (𝓞 K) * f, Algebra.intNorm (𝓞 K) (𝓞 E) α, ?_, ?_, dvd_intNorm_sub_one K E n α h3⟩
  · rw [h1, pow_mul, ← map_pow Ideal.absNorm p, ← hrel, Ideal.absNorm_relNorm]
  · rw [pow_mul, ← hrel, ← map_pow, h2, Ideal.relNorm_singleton]

end GlobalTheory.RayDescent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.ContainsRayFieldOfRay
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FieldSize.RayNorm

open NumberField IsDedekindDomain GlobalTheory.NT
open scoped Pointwise

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

theorem heckeIdeal_prime_pow (χ : (L ≃ₐ[K] L) →* ℂˣ) (𝔮 : HeightOneSpectrum (𝓞 K)) (f : ℕ) :
    heckeIdeal L χ (𝔮.asIdeal ^ f) = heckeVal L χ 𝔮 ^ f := by
  unfold heckeIdeal
  rw [finprod_eq_single _ 𝔮]
  · rw [Associates.mk_pow, Associates.count_pow (Associates.mk_ne_zero.mpr 𝔮.ne_bot)
      (HeightOneSpectrum.associates_irreducible 𝔮), Associates.count_self
      (HeightOneSpectrum.associates_irreducible 𝔮), mul_one]
  · intro 𝔭 h𝔭
    have hne : Associates.mk 𝔭.asIdeal ≠ Associates.mk 𝔮.asIdeal := by
      intro h
      apply h𝔭
      rw [Associates.mk_eq_mk_iff_associated, associated_iff_eq] at h
      exact HeightOneSpectrum.ext h
    rw [Associates.mk_pow, Associates.count_pow (Associates.mk_ne_zero.mpr 𝔮.ne_bot)
      (HeightOneSpectrum.associates_irreducible 𝔭), Associates.count_eq_zero_of_ne
      (HeightOneSpectrum.associates_irreducible 𝔭) (HeightOneSpectrum.associates_irreducible 𝔮) hne,
      mul_zero, pow_zero]

omit [NumberField K] [NumberField L] in

theorem pow_smul_sub_mem (P : Ideal (𝓞 L)) {σ : L ≃ₐ[K] L} {q : ℕ} (h : ∀ x : 𝓞 L, σ • x - x ^ q ∈ P) (k : ℕ)
    (x : 𝓞 L) : σ ^ k • x - x ^ q ^ k ∈ P := by
  have h' : ∀ y : 𝓞 L, Ideal.Quotient.mk P (σ • y) = Ideal.Quotient.mk P y ^ q := fun y => by
    rw [← map_pow, Ideal.Quotient.eq]
    exact h y
  induction k with
  | zero => simp
  | succ k ih =>
    rw [← Ideal.Quotient.eq] at ih ⊢
    rw [pow_succ' σ k, mul_smul, h', ih, ← map_pow, ← pow_mul, ← pow_succ]

theorem exists_frob_pow_eq_one [IsGalois K L] (𝔭 : HeightOneSpectrum (𝓞 K)) (hu : UnramIn L 𝔭)
    (P : HeightOneSpectrum (𝓞 L)) [hPo : P.asIdeal.LiesOver 𝔭.asIdeal] {f : ℕ}
    (hf : Ideal.absNorm P.asIdeal = Ideal.absNorm 𝔭.asIdeal ^ f) :
    ∃ σ : L ≃ₐ[K] L, IsFrob L 𝔭 σ ∧ σ ^ f = 1 := by
  unfold UnramIn at hu
  have hq : Nat.card (𝓞 K ⧸ P.asIdeal.under (𝓞 K)) = Ideal.absNorm 𝔭.asIdeal := by
    rw [← hPo.over, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hfin : Finite (𝓞 L ⧸ P.asIdeal) :=
    (Ideal.absNorm_ne_zero_iff _).mp (fun h0 => P.ne_bot (Ideal.absNorm_eq_zero_iff.mp h0))
  obtain ⟨σ, hσ⟩ := IsArithFrobAt.exists_of_isInvariant (𝓞 K) (L ≃ₐ[K] L) P.asIdeal
  have hσ' : ∀ x : 𝓞 L, σ • x - x ^ Ideal.absNorm 𝔭.asIdeal ∈ P.asIdeal := fun x => by
    have h1 := hσ x
    rw [hq] at h1
    exact h1
  refine ⟨σ, ⟨P.asIdeal, P.isPrime, hPo, hσ'⟩, ?_⟩
  have hfix : ∀ x : 𝓞 L, σ ^ f • x - x ∈ P.asIdeal := fun x => by
    have h1 := pow_smul_sub_mem P.asIdeal hσ' f x
    have h2 : x ^ Ideal.absNorm 𝔭.asIdeal ^ f - x ∈ P.asIdeal := by
      let _ := Ideal.Quotient.field P.asIdeal
      have _ := Fintype.ofFinite (𝓞 L ⧸ P.asIdeal)
      rw [← hf, ← Ideal.Quotient.eq, map_pow, Ideal.absNorm_apply, Submodule.cardQuot_apply,
        Nat.card_eq_fintype_card, FiniteField.pow_card]
    have h3 := P.asIdeal.add_mem h1 h2
    rw [sub_add_sub_cancel] at h3
    exact h3
  apply hu
  exact ⟨P.asIdeal, P.isPrime, hPo, hfix⟩

theorem exists_gen_of_ray {𝔮 I : Ideal (𝓞 K)}
    (h : ∃ α β : 𝓞 K, RayPair 𝔮 α β ∧ I * Ideal.span {β} = Ideal.span {α}) :
    ∃ π : 𝓞 K, I = Ideal.span {π} ∧ π - 1 ∈ 𝔮 := by
  obtain ⟨α, β, hr, hI⟩ := h
  unfold RayPair at hr
  obtain ⟨-, hβ, -, hβc, hαβ, -⟩ := hr
  have hα : α ∈ I * Ideal.span {β} := by
    rw [hI]
    exact Ideal.mem_span_singleton_self α
  obtain ⟨π, -, hπ⟩ := Submodule.mem_mul_span_singleton.mp hα
  have hb0 : Ideal.span {β} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact hβ
  refine ⟨π, ?_, ?_⟩
  · apply mul_right_cancel₀ hb0
    rw [hI, Ideal.span_singleton_mul_span_singleton, hπ]
  · have hq : β * (π - 1) ∈ 𝔮 := by
      have e : β * (π - 1) = α - β := by
        rw [← hπ]
        ring
      rw [e]
      exact hαβ
    have h1 : (1 : 𝓞 K) ∈ Ideal.span {β} ⊔ 𝔮 := by
      rw [Ideal.isCoprime_iff_sup_eq.mp hβc]
      exact Submodule.mem_top
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp h1
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hy
    have e2 : π - 1 = c * (β * (π - 1)) + (π - 1) * z := by
      calc π - 1 = (π - 1) * (c * β + z) := by rw [hyz, mul_one]
        _ = c * (β * (π - 1)) + (π - 1) * z := by ring
    rw [e2]
    exact 𝔮.add_mem (𝔮.mul_mem_left c hq) (𝔮.mul_mem_left (π - 1) hz)

private theorem pow_residue_degree_eq_one_of_isFrobenius [IsGalois K L] (𝔭 : HeightOneSpectrum (𝓞 K)) (hu : UnramIn L 𝔭)
    (Q : Ideal (𝓞 L)) [hQ : Q.IsPrime] [hQo : Q.LiesOver 𝔭.asIdeal] {f : ℕ}
    (hQf : Ideal.absNorm Q = Ideal.absNorm 𝔭.asIdeal ^ f) (τ : L ≃ₐ[K] L)
    (hτ : ∀ x : 𝓞 L, τ • x - x ^ Ideal.absNorm 𝔭.asIdeal ∈ Q) : τ ^ f = 1 := by
  unfold UnramIn at hu
  have hN0 : Ideal.absNorm Q ≠ 0 := by
    rw [hQf]
    exact pow_ne_zero f (fun h0 => 𝔭.ne_bot (Ideal.absNorm_eq_zero_iff.mp h0))
  have hQ0 : Q ≠ ⊥ := fun h0 => hN0 (Ideal.absNorm_eq_zero_iff.mpr h0)
  have hfin : Finite (𝓞 L ⧸ Q) := (Ideal.absNorm_ne_zero_iff _).mp hN0
  haveI : Q.IsMaximal := hQ.isMaximal hQ0
  have hfix : ∀ x : 𝓞 L, τ ^ f • x - x ∈ Q := fun x => by
    have h1 := pow_smul_sub_mem Q hτ f x
    have h2 : x ^ Ideal.absNorm 𝔭.asIdeal ^ f - x ∈ Q := by
      let _ := Ideal.Quotient.field Q
      have _ := Fintype.ofFinite (𝓞 L ⧸ Q)
      rw [← hQf, ← Ideal.Quotient.eq, map_pow, Ideal.absNorm_apply, Submodule.cardQuot_apply,
        Nat.card_eq_fintype_card, FiniteField.pow_card]
    have h3 := Q.add_mem h1 h2
    rw [sub_add_sub_cancel] at h3
    exact h3
  exact hu _ ⟨Q, hQ, hQo, hfix⟩

theorem containsRayField_of_ray [IsGalois K L] (n : ℕ)
    (hun : ∀ 𝔭 : HeightOneSpectrum (𝓞 K), ¬ 𝔭.asIdeal ∣ Ideal.span {(n : 𝓞 K)} → UnramIn L 𝔭)
    (hart : ∀ I : Ideal (𝓞 K), I ≠ ⊥ → IsCoprime I (Ideal.span {(n : 𝓞 K)}) →
      (∀ χ : (L ≃ₐ[K] L) →* ℂˣ, heckeIdeal L χ I = 1) →
        ∃ α β : 𝓞 K, RayPair (Ideal.span {(n : 𝓞 K)}) α β ∧ I * Ideal.span {β} = Ideal.span {α}) :
    GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.ContainsRayField (algebraMap K L) n := by
  intro 𝔓 h𝔓
  haveI := 𝔓.isPrime
  have hN : ((Ideal.absNorm 𝔓.asIdeal : ℕ) : 𝓞 K) ∈
      𝔓.asIdeal.comap (RingOfIntegers.mapRingHom (algebraMap K L)) := by
    rw [Ideal.mem_comap, map_natCast]
    exact Ideal.absNorm_mem _
  have hne : 𝔓.asIdeal.comap (RingOfIntegers.mapRingHom (algebraMap K L)) ≠ ⊥ := by
    intro h0
    rw [h0, Ideal.mem_bot] at hN
    have h2 := congrArg (algebraMap (𝓞 K) K) hN
    rw [map_natCast, map_zero, Nat.cast_eq_zero, Ideal.absNorm_eq_zero_iff] at h2
    exact 𝔓.ne_bot h2
  let 𝔭 : HeightOneSpectrum (𝓞 K) := ⟨_, inferInstance, hne⟩
  haveI : 𝔓.asIdeal.LiesOver 𝔭.asIdeal := ⟨rfl⟩
  obtain ⟨f, hfdef⟩ : ∃ f, f = 𝔓.asIdeal.inertiaDeg (𝓞 K) := ⟨_, rfl⟩
  have hf : Ideal.absNorm 𝔓.asIdeal = Ideal.absNorm 𝔭.asIdeal ^ f := by
    rw [hfdef, Ideal.absNorm_pow_inertiaDeg]
  have hn𝔭 : ((n : ℕ) : 𝓞 K) ∉ 𝔭.asIdeal := by
    intro h
    apply h𝔓
    have h' : (RingOfIntegers.mapRingHom (algebraMap K L)) (n : 𝓞 K) ∈ 𝔓.asIdeal := h
    rwa [map_natCast] at h'
  have hu : UnramIn L 𝔭 := hun 𝔭 (fun h => hn𝔭 (Ideal.dvd_span_singleton.mp h))
  have hcop1 : IsCoprime 𝔭.asIdeal (Ideal.span {(n : 𝓞 K)}) := by
    rw [Ideal.isCoprime_iff_sup_eq]
    by_contra hne2
    have e := (𝔭.isMaximal).eq_of_le hne2 le_sup_left
    have h2 : (n : 𝓞 K) ∈ 𝔭.asIdeal ⊔ Ideal.span {(n : 𝓞 K)} :=
      Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)
    rw [← e] at h2
    exact hn𝔭 h2
  have hI0 : 𝔭.asIdeal ^ f ≠ ⊥ := pow_ne_zero f 𝔭.ne_bot
  have hχ : ∀ χ : (L ≃ₐ[K] L) →* ℂˣ, heckeIdeal L χ (𝔭.asIdeal ^ f) = 1 := by
    intro χ
    rw [heckeIdeal_prime_pow]
    obtain ⟨σ0, hσ0, -⟩ := exists_frob_pow_eq_one 𝔭 hu 𝔓 hf
    have hc : (∀ σ : L ≃ₐ[K] L, InInertia L 𝔭 σ → χ σ = 1) ∧ ∃ σ, IsFrob L 𝔭 σ :=
      ⟨fun σ hσ => by rw [hu σ hσ, map_one], ⟨σ0, hσ0⟩⟩
    unfold heckeVal
    rw [dif_pos hc]
    obtain ⟨Q, hQp, hQo, hQ⟩ := hc.2.choose_spec
    have hQf : Ideal.absNorm Q = Ideal.absNorm 𝔭.asIdeal ^ f := by
      rw [hfdef, Ideal.inertiaDeg_eq_of_isGaloisGroup 𝔭.asIdeal 𝔓.asIdeal Q (L ≃ₐ[K] L),
        Ideal.absNorm_pow_inertiaDeg]
    have hτ := pow_residue_degree_eq_one_of_isFrobenius 𝔭 hu Q hQf _ hQ
    have hχτ : χ hc.2.choose ^ f = 1 := by rw [← map_pow, hτ, map_one]
    rw [← Units.val_pow_eq_pow_val, hχτ, Units.val_one]
  obtain ⟨α, β, hr, hI⟩ := hart (𝔭.asIdeal ^ f) hI0 hcop1.pow_left hχ
  obtain ⟨π, hπ, hπ1⟩ := exists_gen_of_ray ⟨α, β, hr, hI⟩
  exact ⟨f, π, hf, hπ, Ideal.mem_span_singleton.mp hπ1⟩

end GlobalTheory.FieldSize.RayNorm

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsCompactFiniteApproxIdentity
section
open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped InnerProductSpace Topology

noncomputable section
namespace GlobalTheory.KFinApprox

theorem approx_identity : ∀ (n : ℕ) (ε : Fin n → Bool) (X : Type) [TopologicalSpace X] (F : X → KG ε → ℂ),
    (Continuous fun p : X × KG ε => F p.1 p.2) → ∀ C : Set X, IsCompact C → ∀ δ : ℝ, 0 < δ →
    ∃ e : KG ε → ℂ, KFinFun ε e ∧ ∀ x ∈ C, ‖F x 1 - ∫ k, e k * F x k ∂(muK ε)‖ < δ := by
  intro n ε X _ F hF C hC δ hδ

  have hFx : ∀ x, Continuous (F x) := fun x =>
    hF.comp (Continuous.prodMk continuous_const continuous_id)
  have hintC : ∀ g : KG ε → ℂ, Continuous g → Integrable g (muK ε) := fun g hg =>
    hg.integrable_of_hasCompactSupport (isClosed_tsupport g).isCompact
  have hintR : ∀ g : KG ε → ℝ, Continuous g → Integrable g (muK ε) := fun g hg =>
    hg.integrable_of_hasCompactSupport (isClosed_tsupport g).isCompact

  have hG : Continuous fun z : KG ε × X => ‖F z.2 z.1 - F z.2 1‖ :=
    ((hF.comp (Continuous.prodMk continuous_snd continuous_fst)).sub
      (hF.comp (Continuous.prodMk continuous_snd continuous_const))).norm
  have hev : ∀ᶠ k in 𝓝 (1 : KG ε), ∀ x ∈ C, ‖F x k - F x 1‖ < δ / 3 := by
    refine hC.eventually_forall_of_forall_eventually (fun y _ => ?_)
    have ht := hG.tendsto ((1 : KG ε), y)
    simp only [sub_self, norm_zero] at ht
    exact ht.eventually_lt_const (by positivity)
  obtain ⟨U, hUP, hUo, hU1⟩ := eventually_nhds_iff.1 hev

  obtain ⟨f, hf0, hf1, hf01⟩ := exists_continuous_zero_one_of_isClosed hUo.isClosed_compl
    (isClosed_singleton (x := (1 : KG ε))) (Set.disjoint_singleton_right.2 (fun h => h hU1))
  have hf1' : f 1 = 1 := by simpa using hf1 (Set.mem_singleton (1 : KG ε))
  have hfnn : ∀ k, 0 ≤ f k := fun k => (hf01 k).1
  have hfU : ∀ k, k ∉ U → f k = 0 := fun k hk => by simpa using hf0 hk
  have hIpos : 0 < ∫ k, f k ∂(muK ε) :=
    Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero f.continuous
      (isClosed_tsupport _).isCompact (fun k => hfnn k) (x := 1) (by rw [hf1']; norm_num)
  obtain ⟨I, hIdef⟩ : ∃ I, ∫ k, f k ∂(muK ε) = I := ⟨_, rfl⟩
  rw [hIdef] at hIpos

  let ψ : C(KG ε, ℂ) := ⟨fun k => ((f k / I : ℝ) : ℂ),
    Complex.continuous_ofReal.comp (f.continuous.div_const I)⟩
  have hψ : ∀ k, ψ k = ((f k / I : ℝ) : ℂ) := fun k => rfl
  have hψint : ∫ k, ψ k ∂(muK ε) = 1 := by
    simp only [hψ]
    rw [integral_complex_ofReal, integral_div, hIdef, div_self hIpos.ne']
    simp
  have hψnorm : ∀ k, ‖ψ k‖ = f k / I := fun k => by
    rw [hψ, Complex.norm_real, Real.norm_of_nonneg (div_nonneg (hfnn k) hIpos.le)]
  have h7 := GlobalTheory.KFinSep.finAlg_dense ε

  obtain ⟨M, hM⟩ := (hC.prod isCompact_univ).exists_bound_of_continuousOn hF.continuousOn
  obtain ⟨A, hA, hMA⟩ : ∃ A : ℝ, 0 < A ∧ M * (muK ε).real Set.univ ≤ A := by
    have hm : 0 ≤ (muK ε).real Set.univ := measureReal_nonneg
    refine ⟨(|M| + 1) * ((muK ε).real Set.univ + 1), by positivity, ?_⟩
    nlinarith [le_abs_self M, abs_nonneg M]
  have hη : 0 < δ / (3 * A) := div_pos hδ (by linarith)

  have hmem : ψ ∈ (GlobalTheory.KFinSep.finAlg ε).topologicalClosure := by
    rw [h7]; exact StarSubalgebra.mem_top
  have hmem' : ψ ∈ closure ((GlobalTheory.KFinSep.finAlg ε : Set C(KG ε, ℂ))) := hmem
  obtain ⟨p, hp, hpd⟩ := Metric.mem_closure_iff.1 hmem' (δ / (3 * A)) hη
  have hpK : KFinFun ε p := hp.1
  have hpk : ∀ k, ‖ψ k - p k‖ ≤ δ / (3 * A) := fun k => by
    have h := ContinuousMap.norm_coe_le_norm (ψ - p) k
    rw [← dist_eq_norm] at h
    simpa using h.trans hpd.le
  refine ⟨p, hpK, fun x hx => ?_⟩
  have i1 : Integrable (fun k => ψ k * F x 1) (muK ε) := hintC _ (ψ.continuous.mul continuous_const)
  have i2 : Integrable (fun k => ψ k * F x k) (muK ε) := hintC _ (ψ.continuous.mul (hFx x))
  have i3 : Integrable (fun k => p k * F x k) (muK ε) := hintC _ (p.continuous.mul (hFx x))
  have e1 : ∫ k, ψ k * (F x 1 - F x k) ∂(muK ε) = F x 1 - ∫ k, ψ k * F x k ∂(muK ε) := by
    simp_rw [mul_sub]
    rw [integral_sub i1 i2, integral_mul_const, hψint, one_mul]
  have e2 : ∫ k, (ψ k - p k) * F x k ∂(muK ε) =
      ∫ k, ψ k * F x k ∂(muK ε) - ∫ k, p k * F x k ∂(muK ε) := by
    simp_rw [sub_mul]
    exact integral_sub i2 i3
  have e3 : F x 1 - ∫ k, p k * F x k ∂(muK ε) =
      ∫ k, ψ k * (F x 1 - F x k) ∂(muK ε) + ∫ k, (ψ k - p k) * F x k ∂(muK ε) := by
    rw [e1, e2]; ring
  have b1 : ‖∫ k, ψ k * (F x 1 - F x k) ∂(muK ε)‖ ≤ δ / 3 := by
    have hg : Integrable (fun k => f k / I * (δ / 3)) (muK ε) :=
      hintR _ ((f.continuous.div_const I).mul continuous_const)
    refine (norm_integral_le_of_norm_le hg (Filter.Eventually.of_forall fun k => ?_)).trans_eq ?_
    · rw [norm_mul, hψnorm]
      by_cases hk : k ∈ U
      · have := hUP k hk x hx
        rw [norm_sub_rev] at this
        exact mul_le_mul_of_nonneg_left this.le (div_nonneg (hfnn k) hIpos.le)
      · rw [hfU k hk]; simp
    · rw [integral_mul_const, integral_div, hIdef, div_self hIpos.ne', one_mul]
  have b2 : ‖∫ k, (ψ k - p k) * F x k ∂(muK ε)‖ ≤ δ / 3 := by
    refine (norm_integral_le_of_norm_le_const (C := δ / (3 * A) * M)
      (Filter.Eventually.of_forall fun k => ?_)).trans ?_
    · rw [norm_mul]
      exact mul_le_mul (hpk k) (hM (x, k) ⟨hx, Set.mem_univ _⟩) (norm_nonneg _) hη.le
    · calc δ / (3 * A) * M * (muK ε).real Set.univ
          = δ / (3 * A) * (M * (muK ε).real Set.univ) := by ring
        _ ≤ δ / (3 * A) * A := mul_le_mul_of_nonneg_left hMA hη.le
        _ = δ / 3 := by field_simp
  rw [e3]
  calc ‖∫ k, ψ k * (F x 1 - F x k) ∂(muK ε) + ∫ k, (ψ k - p k) * F x k ∂(muK ε)‖
      ≤ δ / 3 + δ / 3 := (norm_add_le _ _).trans (add_le_add b1 b2)
    _ < δ := by linarith

end GlobalTheory.KFinApprox
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsGaussRingMapToCompletionStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_gaussRing_map_to_completion : ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO)) (N D' N' : ℕ) (σ : ReciprocityTheory.ChartRestriction.G.T0.TVar D' N' ≃ Idx D j N), ∃ (f : ReciprocityTheory.ChartRestriction.G.T0.Op D' N' la →+* Op X la N) (φ : ReciprocityTheory.ChartRestriction.G.T0.KTf B.KO D' N' →+* Kp X la N), f.Flat ∧ IsLocalHom f ∧ Ideal.map f (IsLocalRing.maximalIdeal (ReciprocityTheory.ChartRestriction.G.T0.Op D' N' la)) = IsLocalRing.maximalIdeal (Op X la N) ∧ (∀ x : Op X la N, ∃ a, x - f a ∈ IsLocalRing.maximalIdeal (Op X la N)) ∧ (∀ o, φ (ReciprocityTheory.ChartRestriction.G.T0.OpToKT D' N' la o) = algebraMap (Op X la N) (Kp X la N) (f o)) ∧ (∀ a : B.KO, φ (algebraMap B.KO (ReciprocityTheory.ChartRestriction.G.T0.KTf B.KO D' N') a) = algebraMap (X.Kl la) (Kp X la N) (algebraMap B.KO (X.Kl la) a)) ∧ ∀ q, φ (algebraMap (ReciprocityTheory.ChartRestriction.G.T0.KTp B.KO D' N') (ReciprocityTheory.ChartRestriction.G.T0.KTf B.KO D' N') (MvPolynomial.X q)) = algebraMap (Op X la N) (Kp X la N) (Tv X la N (σ q)) := by
  first | exact @GlobalTheory.GaussCompletion.exists_gaussRing_map | exact GlobalTheory.GaussCompletion.exists_gaussRing_map | (intros; apply GlobalTheory.GaussCompletion.exists_gaussRing_map <;> assumption)
end

