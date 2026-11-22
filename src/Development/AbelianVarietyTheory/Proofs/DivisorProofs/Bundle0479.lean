import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0262
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0374
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0472
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0463
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0014
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0464
import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingH1InvertingMorphisms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0456
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0436

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartRingLocalizationMembership
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin

theorem stdForm_incl_map_eq {F F' : Type} [Field F] [Field F'] [Algebra F F'] (n : ℕ) (t : F' ≃ₐ[F] F')
    (γ : GL (Fin n) F) :
    ((incl F F' n γ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F').map t =
      ((incl F F' n γ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') := by
  ext i j
  show t (algebraMap F F' ((γ : Matrix (Fin n) (Fin n) F) i j)) = algebraMap F F' ((γ : Matrix (Fin n) (Fin n) F) i j)
  exact t.commutes _

theorem stdForm_adjoin_map_mem {F F' : Type} [Field F] [Field F'] [Algebra F F'] (n : ℕ) (t : F' ≃ₐ[F] F')
    (γ : GL (Fin n) F) {M : Matrix (Fin n) (Fin n) F'}
    (hM : M ∈ Algebra.adjoin F' {((incl F F' n γ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F')}) :
    M.map t ∈ Algebra.adjoin F' {((incl F F' n γ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F')} := by
  let T : Matrix (Fin n) (Fin n) F' →+* Matrix (Fin n) (Fin n) F' := ((t : F' ≃+* F') : F' →+* F').mapMatrix
  have hT : ∀ N, T N = N.map t := fun N => rfl
  rw [← hT]
  induction hM using Algebra.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff] at hx
    subst hx
    rw [hT, stdForm_incl_map_eq]
    exact Algebra.subset_adjoin rfl
  | algebraMap r =>
    have : T (algebraMap F' (Matrix (Fin n) (Fin n) F') r) = algebraMap F' (Matrix (Fin n) (Fin n) F') (t r) := by
      rw [hT]
      ext i j
      by_cases h : i = j <;> simp [Matrix.algebraMap_matrix_apply, h]
    rw [this]
    exact Subalgebra.algebraMap_mem _ _
  | add x y _ _ hx hy => rw [map_add]; exact Subalgebra.add_mem _ hx hy
  | mul x y _ _ hx hy => rw [map_mul]; exact Subalgebra.mul_mem _ hx hy

theorem stdForm_commute_iff {F' : Type} [Field F'] {n : ℕ} (x y : GL (Fin n) F') :
    Commute x y ↔ Commute (x : Matrix (Fin n) (Fin n) F') (y : Matrix (Fin n) (Fin n) F') := by
  simp only [Commute, SemiconjBy, Units.ext_iff, Units.val_mul]

theorem isNorm_exists_twistedConj_adjoin :
    ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (s : F' ≃ₐ[F] F'),
      (∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s) → ∀ (n : ℕ) (δ : GL (Fin n) F') (γ : GL (Fin n) F),
      IsNorm s δ γ → ∃ y : GL (Fin n) F', ((y⁻¹ * δ * galAct F F' n s y : GL (Fin n) F') :
        Matrix (Fin n) (Fin n) F') ∈ Algebra.adjoin F' {((incl F F' n γ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F')} ∧
        nrm s (y⁻¹ * δ * galAct F F' n s y) = incl F F' n γ := by
  intro F F' _ _ _ _ s hs n δ γ hN
  obtain ⟨_, -, h3, h4, h5⟩ := GlobalTheory.T.galoisTwistedNormGL_basic_properties F F' s hs n

  have hgfix : ∀ t : F' ≃ₐ[F] F', galAct F F' n t (incl F F' n γ) = incl F F' n γ := fun t =>
    Units.ext (stdForm_incl_map_eq n t γ)

  have hC : ∀ z w : GL (Fin n) F',
      (z : Matrix (Fin n) (Fin n) F') ∈ Algebra.adjoin F' {((incl F F' n γ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F')} →
      Commute w (incl F F' n γ) → Commute z w := by
    intro z w hz hw
    rw [stdForm_commute_iff] at hw ⊢
    exact (Algebra.commute_of_mem_adjoin_singleton_of_commute hz hw).symm
  have hCt : ∀ (t : F' ≃ₐ[F] F') (w : GL (Fin n) F'), Commute w (incl F F' n γ) →
      Commute (galAct F F' n t w) (incl F F' n γ) := by
    intro t w hw
    have := hw.map (galAct F F' n t)
    rwa [hgfix t] at this

  obtain ⟨c, hc⟩ := isConj_iff.1 hN
  have hn1 : nrm s (c⁻¹ * δ * galAct F F' n s c) = incl F F' n γ := by
    rw [h3, ← hc]; group
  have hcomm1 : Commute (c⁻¹ * δ * galAct F F' n s c) (incl F F' n γ) := by
    have := h4 (c⁻¹ * δ * galAct F F' n s c)
    rw [hn1, hgfix s] at this
    exact this

  obtain ⟨δ₀, hδ₀A, hn0⟩ := GlobalTheory.T.norm_map_surjective_finite_field F F' s hs n γ
  have hδ₀g : Commute δ₀ (incl F F' n γ) := hC δ₀ _ hδ₀A (Commute.refl _)
  have hεg : Commute (δ₀⁻¹ * (c⁻¹ * δ * galAct F F' n s c)) (incl F F' n γ) :=
    (hδ₀g.inv_left).mul_left hcomm1
  have hεn : nrm s (δ₀⁻¹ * (c⁻¹ * δ * galAct F F' n s c)) = 1 := by
    have hp := h5 δ₀ (δ₀⁻¹ * (c⁻¹ * δ * galAct F F' n s c)) (fun t u =>
      hC _ _ (by rw [show ((galAct F F' n t δ₀ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') =
        (δ₀ : Matrix (Fin n) (Fin n) F').map t from rfl]; exact stdForm_adjoin_map_mem n t γ hδ₀A) (hCt u _ hεg))
    rw [mul_inv_cancel_left, hn1, hn0] at hp
    exact (mul_eq_left.1 hp.symm)

  have hBst : ∀ M ∈ Subalgebra.centralizer F' {((incl F F' n γ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F')},
      M.map s ∈ Subalgebra.centralizer F' {((incl F F' n γ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F')} := by
    intro M hM
    rw [Subalgebra.mem_centralizer_iff] at hM ⊢
    intro g' hg'
    rw [Set.mem_singleton_iff] at hg'
    subst hg'
    have e := congrArg (fun N => ((s : F' ≃+* F') : F' →+* F').mapMatrix N) (hM _ rfl)
    simp only [map_mul] at e
    rw [← stdForm_incl_map_eq n s γ]
    exact e
  have hεB : ((δ₀⁻¹ * (c⁻¹ * δ * galAct F F' n s c) : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') ∈
      Subalgebra.centralizer F' {((incl F F' n γ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F')} := by
    rw [Subalgebra.mem_centralizer_iff]
    intro g' hg'
    rw [Set.mem_singleton_iff] at hg'
    subst hg'
    exact ((stdForm_commute_iff _ _).1 hεg).eq.symm
  obtain ⟨x, hxB, hεx⟩ := GlobalTheory.T.exists_coboundary_of_norm_one_in_subalgebra F F' s hs n _ hBst _ hεB hεn
  have hxg : Commute x (incl F F' n γ) := by
    rw [stdForm_commute_iff]
    exact ((Subalgebra.mem_centralizer_iff F').1 hxB _ rfl).symm
  have hxδ₀ : Commute δ₀ x := hC δ₀ x hδ₀A hxg
  have e1 : c⁻¹ * δ * galAct F F' n s c = δ₀ * (x⁻¹ * galAct F F' n s x) := by
    rw [← hεx, mul_inv_cancel_left]
  have key : (c * x⁻¹)⁻¹ * δ * galAct F F' n s (c * x⁻¹) = δ₀ := by
    rw [map_mul, map_inv]
    calc (c * x⁻¹)⁻¹ * δ * (galAct F F' n s c * (galAct F F' n s x)⁻¹)
        = x * (c⁻¹ * δ * galAct F F' n s c) * (galAct F F' n s x)⁻¹ := by group
      _ = x * δ₀ * x⁻¹ := by rw [e1]; group
      _ = δ₀ := by rw [← hxδ₀.eq]; group
  exact ⟨c * x⁻¹, by rw [key]; exact hδ₀A, by rw [key]; exact hn0⟩

end GlobalTheory.Shin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClearsIdempotentConductorIff
section
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical

noncomputable section

namespace GlobalTheory.CondAway

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem isUnit_absNorm_of_not_mem (q : HeightOneSpectrum (OF E)) (l : ℕ) (hl : l.Prime)
    (hq : (l : OF E) ∉ q.asIdeal) (O : Type) [CommRing O] [IsLocalRing O]
    (hlO : (l : O) ∈ IsLocalRing.maximalIdeal O) : IsUnit ((Ideal.absNorm q.asIdeal : ℕ) : O) := by
  haveI : Finite (OF E ⧸ q.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ q.ne_bot
  haveI := q.isMaximal
  letI : Field (OF E ⧸ q.asIdeal) := Ideal.Quotient.field _
  letI : Fintype (OF E ⧸ q.asIdeal) := Fintype.ofFinite _
  obtain ⟨n, hp, hcard⟩ := FiniteField.card (OF E ⧸ q.asIdeal) (ringChar (OF E ⧸ q.asIdeal))
  set p := ringChar (OF E ⧸ q.asIdeal)
  have hN : Ideal.absNorm q.asIdeal = p ^ (n : ℕ) := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card, hcard]
  have hpl : p ≠ l := by
    intro h
    apply hq
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, ← h]
    exact ringChar.Nat.cast_ringChar
  by_contra hu
  have hmem : ((p : ℕ) : O) ∈ IsLocalRing.maximalIdeal O := by
    have : ((p : ℕ) : O) ^ (n : ℕ) ∈ IsLocalRing.maximalIdeal O := by
      rw [← Nat.cast_pow, ← hN]; exact (IsLocalRing.mem_maximalIdeal _).2 hu
    exact (IsLocalRing.maximalIdeal.isMaximal O).isPrime.mem_of_pow_mem _ this
  have hcop : IsCoprime (p : ℤ) (l : ℤ) := Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hp hl).2 hpl)
  obtain ⟨u, v, huv⟩ := hcop
  have h1 : (1 : O) ∈ IsLocalRing.maximalIdeal O := by
    have := congrArg (Int.cast : ℤ → O) huv
    push_cast at this
    rw [← this]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hmem) (Ideal.mul_mem_left _ _ hlO)
  exact (IsLocalRing.maximalIdeal.isMaximal O).ne_top ((Ideal.eq_top_iff_one _).2 h1)

theorem coordAt_rTensor (O : Type) [CommRing O] {K : Type} [Field K] [Algebra O K] {c c' : Ideal (OF E)} (s : E)
    (g : orderC c →ₗ[ℤ] orderC c') (hg : ∀ x, (g x : E) = s * x) (σ : E →+* K) (t : orderC c ⊗[ℤ] O) :
    coordAt O c' σ (g.rTensor O t) = σ s * coordAt O c σ t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    rw [LinearMap.rTensor_tmul]
    show σ (g a) * algebraMap O K x = σ s * (σ a * algebraMap O K x)
    rw [hg, map_mul, mul_assoc]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, mul_add]

theorem clearsIdem_condQ_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (𝔣 : Ideal (OF E))
    (Q : Finset (HeightOneSpectrum (OF E))) (l : ℕ), l.Prime → (∀ q ∈ Q, (l : OF E) ∉ q.asIdeal) →
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (K : Type) [Field K] [Algebra O K]
    [IsFractionRing O K], (l : O) ∈ IsLocalRing.maximalIdeal O → ∀ D : O,
    ClearsIdem K (condQ 𝔣 Q) D ↔ ClearsIdem K 𝔣 D := by
  intro E _ _ _ 𝔣 Q l hl hQ O _ _ _ _ K _ _ _ hlO D
  have hle : condQ 𝔣 Q ≤ 𝔣 := Ideal.mul_le_inf.trans inf_le_left
  constructor
  · intro h σ
    obtain ⟨t, ht⟩ := h σ
    let g : orderC (condQ 𝔣 Q) →ₗ[ℤ] orderC 𝔣 := AddMonoidHom.toIntLinearMap
      { toFun := fun x => ⟨(1 : E) * x, by rw [one_mul]; exact orderC_mono hle x.2⟩,
        map_zero' := Subtype.ext (by simp), map_add' := fun x y => Subtype.ext (by simp [mul_add]) }
    refine ⟨g.rTensor O t, fun σ' => ?_⟩
    rw [coordAt_rTensor O (1 : E) g (fun x => rfl), map_one, one_mul, ht]
  · intro h σ
    obtain ⟨t, ht⟩ := h σ
    set m : ℕ := ∏ q ∈ Q, Ideal.absNorm q.asIdeal with hm
    have hmI : (m : OF E) ∈ ∏ q ∈ Q, q.asIdeal := by
      rw [hm, Nat.cast_prod]
      exact Ideal.prod_mem_prod fun q _ => Ideal.absNorm_mem q.asIdeal
    have hmul : ∀ x ∈ orderC 𝔣, (m : E) * x ∈ orderC (condQ 𝔣 Q) := by
      intro x hx
      obtain ⟨a, b, hb, rfl⟩ := mem_orderC.1 hx
      refine mem_orderC.2 ⟨m * a, b * algebraMap (OF E) (𝓞 E) m, ?_, ?_⟩
      · rw [condQ, Ideal.map_mul]
        exact Ideal.mul_mem_mul hb (Ideal.mem_map_of_mem _ hmI)
      · simp only [map_mul, map_natCast]
        ring
    let g : orderC 𝔣 →ₗ[ℤ] orderC (condQ 𝔣 Q) := AddMonoidHom.toIntLinearMap
      { toFun := fun x => ⟨(m : E) * x, hmul x x.2⟩,
        map_zero' := Subtype.ext (by simp), map_add' := fun x y => Subtype.ext (by simp [mul_add]) }
    have hu : IsUnit (m : O) := by
      rw [hm, Nat.cast_prod]
      exact Finset.prod_induction _ IsUnit (fun a b ha hb => ha.mul hb) isUnit_one
        (fun q hq => isUnit_absNorm_of_not_mem q l hl (hQ q hq) O hlO)
    obtain ⟨u, hu'⟩ := hu.exists_left_inv
    refine ⟨g.rTensor O t * (1 ⊗ₜ u), fun σ' => ?_⟩
    rw [map_mul, coordAt_rTensor O (m : E) g (fun x => rfl), ht]
    have h1 : coordAt O (condQ 𝔣 Q) σ' (1 ⊗ₜ u) = algebraMap O K u := by
      show σ' ((1 : orderC (condQ 𝔣 Q)) : E) * algebraMap O K u = _
      simp
    have h2 : algebraMap O K u * (m : K) = 1 := by
      rw [← map_natCast (algebraMap O K), ← map_mul, hu', map_one]
    rw [h1, map_natCast]
    split_ifs
    · linear_combination (algebraMap O K D) * h2
    · simp

end GlobalTheory.CondAway
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClearsIdempotentOfExponentBound
section
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical

namespace GlobalTheory.Proof.clears_idempotent_of_exponent_bound

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem exists_not_mem_mul_pow_mem {𝔣 : Ideal (OF E)} (h𝔣 : 𝔣 ≠ ⊥) (v : HeightOneSpectrum (OF E)) {c : OF E}
    (hc : c ∈ v.asIdeal) {k : ℕ} (hk : expIn 𝔣 v ≤ k) : ∃ x : OF E, x ∉ v.asIdeal ∧ x * c ^ k ∈ 𝔣 := by
  set e := multiplicity v.asIdeal 𝔣 with he
  obtain ⟨𝔤, h𝔤⟩ := pow_multiplicity_dvd v.asIdeal 𝔣
  have hnu : ¬ IsUnit v.asIdeal := by
    rw [Ideal.isUnit_iff]; exact v.isPrime.ne_top
  have hfin : FiniteMultiplicity v.asIdeal 𝔣 := FiniteMultiplicity.of_not_isUnit hnu h𝔣
  have hndvd : ¬ v.asIdeal ∣ 𝔤 := by
    rintro ⟨𝔥, rfl⟩
    apply hfin.not_pow_dvd_of_multiplicity_lt (Nat.lt_succ_self e)
    exact ⟨𝔥, by rw [h𝔤, pow_succ, mul_assoc]⟩
  rw [Ideal.dvd_iff_le, SetLike.not_le_iff_exists] at hndvd
  obtain ⟨x, hx𝔤, hxv⟩ := hndvd
  refine ⟨x, hxv, ?_⟩
  rw [h𝔤, mul_comm x]
  refine Ideal.mul_mem_mul ?_ hx𝔤
  exact Ideal.pow_le_pow_right hk (Ideal.pow_mem_pow hc k)

theorem colon_sup_eq_top {𝔣 : Ideal (OF E)} (h𝔣 : 𝔣 ≠ ⊥) {l : ℕ} (hl : l ≠ 0) {k : ℕ}
    (hk : ∀ v : HeightOneSpectrum (OF E), (l : OF E) ∈ v.asIdeal → expIn 𝔣 v ≤ k) :
    𝔣.colon {((l : OF E) ^ k)} ⊔ Ideal.span {(l : OF E)} = ⊤ := by
  by_contra hne
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
  have hMb : M ≠ ⊥ := Ideal.IsMaximal.ne_bot_of_isIntegral_int M
  let v : HeightOneSpectrum (OF E) := ⟨M, hM.isPrime, hMb⟩
  have hlv : (l : OF E) ∈ v.asIdeal := hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
  obtain ⟨x, hxv, hx⟩ := exists_not_mem_mul_pow_mem h𝔣 v hlv (hk v hlv)
  apply hxv
  apply hle
  apply Ideal.mem_sup_left
  rw [Submodule.mem_colon_singleton, smul_eq_mul]
  exact hx

end GlobalTheory.Proof.clears_idempotent_of_exponent_bound

namespace GlobalTheory.Proof.clears_idempotent_of_exponent_bound

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem exists_coprime_mul_pow_mem {𝔣 : Ideal (OF E)} (h𝔣 : 𝔣 ≠ ⊥) {l : ℕ} (hl : l.Prime) {k : ℕ}
    (hk : ∀ v : HeightOneSpectrum (OF E), (l : OF E) ∈ v.asIdeal → expIn 𝔣 v ≤ k) :
    ∃ m : ℕ, m.Coprime l ∧ ((m : OF E) * (l : OF E) ^ k) ∈ 𝔣 := by
  set J := 𝔣.colon {((l : OF E) ^ k)} with hJ
  have hmemJ : ∀ r : OF E, r ∈ J ↔ r * (l : OF E) ^ k ∈ 𝔣 := fun r => by
    rw [hJ, Submodule.mem_colon_singleton, smul_eq_mul]
  have hfJ : 𝔣 ≤ J := fun r hr => (hmemJ r).2 (Ideal.mul_mem_right _ _ hr)
  have hJb : J ≠ ⊥ := fun h => h𝔣 (le_bot_iff.1 (h ▸ hfJ))
  have htop := colon_sup_eq_top h𝔣 hl.ne_zero hk
  rw [← hJ] at htop
  refine ⟨Ideal.absNorm J, ?_, (hmemJ _).1 (Ideal.absNorm_mem J)⟩
  rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hl]
  intro hdvd
  have hcard : Nat.card (OF E ⧸ J) = Ideal.absNorm J := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hne : Nat.card (OF E ⧸ J) ≠ 0 := by
    rw [hcard]; exact fun h => hJb (Ideal.absNorm_eq_zero_iff.1 h)
  haveI : Finite (OF E ⧸ J) := Nat.finite_of_card_ne_zero hne
  haveI : Fact l.Prime := ⟨hl⟩
  obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' (G := OF E ⧸ J) l (hcard ▸ hdvd)
  have h1 : (1 : OF E) ∈ J ⊔ Ideal.span {(l : OF E)} := htop ▸ Submodule.mem_top
  obtain ⟨j, hj, y, hy, hjy⟩ := Submodule.mem_sup.1 h1
  obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 hy
  have hu : (Ideal.Quotient.mk J a) * (l : OF E ⧸ J) = 1 := by
    have : Ideal.Quotient.mk J (j + a * l) = 1 := by rw [hjy, map_one]
    rw [map_add, Ideal.Quotient.eq_zero_iff_mem.2 hj, zero_add, map_mul, map_natCast] at this
    exact this
  have hlx : (l : OF E ⧸ J) * x = 0 := by
    rw [← nsmul_eq_mul, ← hx]; exact addOrderOf_nsmul_eq_zero x
  have hx0 : x = 0 := by
    calc x = (Ideal.Quotient.mk J a * (l : OF E ⧸ J)) * x := by rw [hu, one_mul]
      _ = 0 := by rw [mul_assoc, hlx, mul_zero]
  rw [hx0, addOrderOf_zero] at hx
  exact hl.one_lt.ne hx

theorem isUnit_natCast_of_coprime {O : Type} [CommRing O] [IsLocalRing O] {m l : ℕ} (h : m.Coprime l)
    (hl : (l : O) ∈ IsLocalRing.maximalIdeal O) : IsUnit (m : O) := by
  have hc : IsCoprime (m : O) (l : O) := by
    have := (Nat.isCoprime_iff_coprime.2 h).map (Int.castRingHom O)
    simpa using this
  by_contra hm
  obtain ⟨u, w, huw⟩ := hc
  have hm' : (m : O) ∈ IsLocalRing.maximalIdeal O := (IsLocalRing.mem_maximalIdeal _).2 hm
  have : (1 : O) ∈ IsLocalRing.maximalIdeal O := by
    rw [← huw]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hm') (Ideal.mul_mem_left _ _ hl)
  exact (IsLocalRing.maximalIdeal.isMaximal O).ne_top ((Ideal.eq_top_iff_one _).2 this)

end GlobalTheory.Proof.clears_idempotent_of_exponent_bound

namespace GlobalTheory.Proof.clears_idempotent_of_exponent_bound

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem mul_mem_orderC {𝔣 : Ideal (OF E)} {c : OF E} (hc : c ∈ 𝔣) {x : E} (hx : x ∈ orderC (⊤ : Ideal (OF E))) :
    algebraMap (OF E) E c * x ∈ orderC 𝔣 := by
  obtain ⟨a, b, -, rfl⟩ := mem_orderC.1 hx
  refine mem_orderC.2 ⟨c * a, algebraMap (OF E) (𝓞 E) c * b,
    Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hc), ?_⟩
  have hc' : ∀ a : OF E, algebraMap (OF E) E a = algebraMap (𝓞 E) E (algebraMap (OF E) (𝓞 E) a) := fun a => rfl
  rw [mul_add, map_mul, map_mul, ← hc' c]

def mulMap {𝔣 : Ideal (OF E)} {c : OF E} (hc : c ∈ 𝔣) : orderC (⊤ : Ideal (OF E)) →ₗ[ℤ] orderC 𝔣 where
  toFun x := ⟨algebraMap (OF E) E c * x, mul_mem_orderC hc x.2⟩
  map_add' x y := Subtype.ext (by simp [mul_add])
  map_smul' n x := Subtype.ext (by simp [mul_left_comm])

theorem coordAt_map {𝔣 : Ideal (OF E)} {c : OF E} (hc : c ∈ 𝔣) {O : Type} [CommRing O] {K : Type} [Field K]
    [Algebra O K] (w : O) (σ : E →+* K) (t : orderC (⊤ : Ideal (OF E)) ⊗[ℤ] O) :
    coordAt O 𝔣 σ (TensorProduct.map (mulMap hc) (LinearMap.mulLeft ℤ w) t) =
      σ (algebraMap (OF E) E c) * algebraMap O K w * coordAt O ⊤ σ t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
    simp only [TensorProduct.map_tmul, LinearMap.mulLeft_apply]
    change σ (algebraMap (OF E) E c * x) * algebraMap O K (w * y) = _ * (σ x * algebraMap O K y)
    rw [map_mul, map_mul]; ring
  | add s t hs ht => rw [map_add, map_add, hs, ht, map_add, mul_add]

end GlobalTheory.Proof.clears_idempotent_of_exponent_bound

open GlobalTheory.Proof.clears_idempotent_of_exponent_bound in
theorem GlobalTheory.Proof.clears_idempotent_of_exponent_bound.clearsIdem_condC :
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (𝔣 : Ideal (OF E)), 𝔣 ≠ ⊥ → ∀ (l : ℕ), l.Prime → ∀ k : ℕ, (∀ v : HeightOneSpectrum (OF E), (l : OF E) ∈ v.asIdeal → expIn 𝔣 v ≤ k) → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (K : Type) [Field K] [Algebra O K] [IsFractionRing O K], (l : O) ∈ IsLocalRing.maximalIdeal O → ∀ D : O, ClearsIdem K (⊤ : Ideal (OF E)) D → ClearsIdem K 𝔣 ((l : O) ^ k * D) := by
  intro E _ _ _ 𝔣 h𝔣 l hl k hk O _ _ _ _ K _ _ _ hlO D hD σ
  obtain ⟨m, hm, hmem⟩ := exists_coprime_mul_pow_mem h𝔣 hl hk
  obtain ⟨u, hu⟩ := isUnit_natCast_of_coprime (O := O) hm hlO
  obtain ⟨t, ht⟩ := hD σ
  refine ⟨TensorProduct.map (mulMap hmem) (LinearMap.mulLeft ℤ ((u⁻¹ : Oˣ) : O)) t, fun σ' => ?_⟩
  rw [coordAt_map, ht]
  have hw : algebraMap O K (m : O) * algebraMap O K ((u⁻¹ : Oˣ) : O) = 1 := by
    rw [← map_mul, ← hu, Units.mul_inv, map_one]
  simp only [map_mul, map_pow, map_natCast] at hw ⊢
  split_ifs
  · linear_combination ((l : K) ^ k * algebraMap O K D) * hw
  · simp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClearsIdempotentOfTraceDual
section
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical

noncomputable section

namespace GlobalTheory.DualCrit

theorem trace_eq_sum_ringHom {E : Type} [Field E] [NumberField E] {K : Type} [Field K] [CharZero K]
    [Fintype (E →+* K)] (hcard : Fintype.card (E →+* K) = Module.finrank ℚ E) (x : E) :
    algebraMap ℚ K (Algebra.trace ℚ E x) = ∑ σ : E →+* K, σ x := by
  let ι : K →+* AlgebraicClosure K := algebraMap K (AlgebraicClosure K)
  apply ι.injective
  rw [map_sum]
  have hq : ι.comp (algebraMap ℚ K) = algebraMap ℚ (AlgebraicClosure K) := RingHom.ext_rat _ _
  rw [← RingHom.comp_apply, hq, trace_eq_sum_embeddings (AlgebraicClosure K)]
  let f : (E →+* K) → (E →ₐ[ℚ] AlgebraicClosure K) := fun σ => (ι.comp σ).toRatAlgHom
  have hinj : Function.Injective f := by
    intro σ σ' h
    ext y
    apply ι.injective
    exact congrArg (fun g : E →ₐ[ℚ] AlgebraicClosure K => g y) h
  have hbij : Function.Bijective f := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨hinj, ?_⟩
    rw [hcard, AlgHom.card]
  exact (Fintype.sum_bijective f hbij (fun σ => ι (σ x)) (fun τ => τ x) (fun σ => rfl)).symm

theorem sum_basis_mul_dual {E : Type} [Field E] [NumberField E] {K : Type} [Field K] [CharZero K]
    [Fintype (E →+* K)] (hcard : Fintype.card (E →+* K) = Module.finrank ℚ E)
    {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℚ E) (σ σ' : E →+* K) :
    ∑ j, σ' (b j) * σ ((Algebra.traceForm ℚ E).dualBasis (traceForm_nondegenerate ℚ E) b j) =
      if σ' = σ then 1 else 0 := by
  set bd := (Algebra.traceForm ℚ E).dualBasis (traceForm_nondegenerate ℚ E) b
  let A : Matrix ι (E →+* K) K := fun j τ => τ (b j)
  let B : Matrix (E →+* K) ι K := fun τ k => τ (bd k)
  have hAB : A * B = 1 := by
    ext j k
    rw [Matrix.mul_apply, Matrix.one_apply]
    simp only [A, B]
    rw [show (∑ τ : E →+* K, τ (b j) * τ (bd k)) = ∑ τ : E →+* K, τ (bd k * b j) from
      Finset.sum_congr rfl fun τ _ => by rw [map_mul, mul_comm]]
    rw [← trace_eq_sum_ringHom hcard, ← Algebra.traceForm_apply,
      LinearMap.BilinForm.apply_dualBasis_left]
    split_ifs <;> simp
  have e : ι ≃ (E →+* K) := Fintype.equivOfCardEq (by rw [hcard, Module.finrank_eq_card_basis b])
  have hBA : B * A = 1 := (Matrix.mul_eq_one_comm_of_equiv e).1 hAB
  have h := congrFun (congrFun hBA σ) σ'
  rw [Matrix.mul_apply, Matrix.one_apply] at h
  simp only [A, B] at h
  calc _ = ∑ k, σ (bd k) * σ' (b k) := Finset.sum_congr rfl fun _ _ => mul_comm _ _
    _ = _ := by rw [h]; exact if_congr eq_comm rfl rfl

theorem clearsIdem_top_of_dual : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (K : Type) [Field K] [Algebra O K] [IsFractionRing O K], Nat.card (E →+* K) = Module.finrank ℚ E → ∀ D : O, (∀ (σ : E →+* K) (y : E), (∀ x : 𝓞 E, ∃ n : ℤ, Algebra.trace ℚ E (y * x) = n) → ∃ z : O, algebraMap O K z = algebraMap O K D * σ y) → ClearsIdem K (⊤ : Ideal (OF E)) D := by
  intro E _ _ _ O _ _ _ _ K _ _ _ hcard D hD σ
  haveI : CharZero K := charZero_of_injective_algebraMap (IsFractionRing.injective O K)
  haveI : Finite (E →+* K) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact Module.finrank_pos.ne')
  letI : Fintype (E →+* K) := Fintype.ofFinite _
  have hcard' : Fintype.card (E →+* K) = Module.finrank ℚ E := by
    rw [← Nat.card_eq_fintype_card, hcard]
  set b := RingOfIntegers.basis E
  set bQ := integralBasis E
  set bd := (Algebra.traceForm ℚ E).dualBasis (traceForm_nondegenerate ℚ E) bQ
  have hint : ∀ j (x : 𝓞 E), ∃ n : ℤ, Algebra.trace ℚ E (bd j * x) = n := by
    intro j x
    refine ⟨b.repr x j, ?_⟩
    have h1 : Algebra.trace ℚ E (bd j * x) = bQ.repr (x : E) j := by
      rw [← Algebra.traceForm_apply]
      conv_lhs => rw [← bQ.sum_repr (x : E)]
      rw [map_sum]
      simp only [bd, map_smul, LinearMap.BilinForm.apply_dualBasis_left, smul_eq_mul, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [h1]
    exact (integralBasis_repr_apply E x j).trans (eq_intCast _ _)
  choose z hz using fun j => hD σ (bd j) (hint j)
  have hmem : ∀ j, ((b j : 𝓞 E) : E) ∈ orderC (⊤ : Ideal (OF E)) := fun j =>
    mem_orderC.2 ⟨0, b j, by rw [Ideal.map_top]; exact Submodule.mem_top, by simp⟩
  refine ⟨∑ j, (⟨((b j : 𝓞 E) : E), hmem j⟩ : orderC (⊤ : Ideal (OF E))) ⊗ₜ[ℤ] z j, fun σ' => ?_⟩
  have hc : ∀ j, coordAt O (⊤ : Ideal (OF E)) σ'
      ((⟨((b j : 𝓞 E) : E), hmem j⟩ : orderC (⊤ : Ideal (OF E))) ⊗ₜ[ℤ] z j) =
        algebraMap O K D * (σ' (bQ j) * σ (bd j)) := by
    intro j
    show σ' ((b j : 𝓞 E) : E) * algebraMap O K (z j) = _
    rw [hz j, integralBasis_apply]
    simp only [b]
    rw [← RingOfIntegers.coe_eq_algebraMap]
    ring
  rw [map_sum, Finset.sum_congr rfl fun j _ => hc j, ← Finset.mul_sum, sum_basis_mul_dual hcard' bQ σ σ']
  split_ifs <;> simp

end GlobalTheory.DualCrit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTypeTraceImaginaryPartStatement
section
open NumberField GlobalTheory.CMVal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_type_trace_imaginary_part : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ),
    IsCMType φ → ∀ (h : I → ℝ) (mu : E), (∀ z : E, ((Algebra.trace ℚ E (mu * z) : ℚ) : ℝ) = ∑ i, h i * (φ i z).im) →
    ∀ i, 2 * Complex.I * φ i mu = (h i : ℂ) := by
  first | exact @GlobalTheory.cmType_trace_im_coeff | exact GlobalTheory.cmType_trace_im_coeff | (intros; apply GlobalTheory.cmType_trace_im_coeff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoalternatingExactOfFiniteTypeIsoFilteredColimitStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coalternatingExact_of_finiteType_iso_filteredColimits : ∀ (N M : CommRingCat.{0} ⥤ AddCommGrpCat.{1}) (ε : N ⟶ M), PreservesFilteredColimitsOfSize.{0, 0} N → (∀ A : CommRingCat.{0}, Algebra.FiniteType ℤ A → IsIso (ε.app A)) → (∀ (A B : CommRingCat.{0}) (g : A ⟶ B), EtFF g → WExact M (coAug g)) → ∀ (A B : CommRingCat.{0}) (g : A ⟶ B), EtFF g → WExact N (coAug g) := by
  first | (exact @GlobalTheory.EtC.wExact_of_finiteType_iso) | (exact GlobalTheory.EtC.wExact_of_finiteType_iso) | (intros; apply GlobalTheory.EtC.wExact_of_finiteType_iso  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommaDescentInjectiveStatement
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory.CatCoh GlobalTheory.CechDR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.comma_descent_injective : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), (∀ (T : C) (x : (F).obj T), (∀ t (u : T ⟶ G.obj t), mp (F) u x = 0) → x = 0) → (∀ (T : C) (s : ∀ t, (T ⟶ G.obj t) → (F).obj (G.obj t)), (∀ t t' (u : T ⟶ G.obj t) (a : t ⟶ t'), s t' (u ≫ G.map a) = mp (F) (G.map a) (s t u)) → ∃ x : (F).obj T, ∀ t u, mp (F) u x = s t u) → (∀ (T : C) (y : ∀ t t', (T ⟶ G.obj t) → (t ⟶ t') → (F).obj (G.obj t')), (∀ t t' t'' (u : T ⟶ G.obj t) (a : t ⟶ t') (b : t' ⟶ t''), y t t'' u (a ≫ b) = mp (F) (G.map b) (y t t' u a) + y t' t'' (u ≫ G.map a) b) → ∃ g : ∀ t, (T ⟶ G.obj t) → (F).obj (G.obj t), ∀ t t' (u : T ⟶ G.obj t) (a : t ⟶ t'), g t' (u ≫ G.map a) - mp (F) (G.map a) (g t u) = y t t' u a) → Function.Injective (CoefMap.restrict F G).pull2 := by
  first | exact @GlobalTheory.CatCoh.pull2_restrict_injective_of_comma | exact GlobalTheory.CatCoh.pull2_restrict_injective_of_comma | (intros; apply GlobalTheory.CatCoh.pull2_restrict_injective_of_comma <;> assumption)
end

