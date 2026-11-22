import Mathlib

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDerivationExtendingKernelFormOfLifting
section
namespace GlobalTheory.LiftDeriv

theorem krullDimLE_and_isLocalRing_quotient {P : Type} [CommRing P] (Q S : Ideal P) [hQ : Q.IsMaximal]
    (n : ℕ) (h1 : Q ^ (n + 1) ≤ S) (h2 : S ≤ Q) :
    Ring.KrullDimLE 0 (P ⧸ S) ∧ IsLocalRing (P ⧸ S) := by
  have hSt : S ≠ ⊤ := fun h => hQ.ne_top (top_le_iff.1 (h ▸ h2))
  have : Nontrivial (P ⧸ S) := Ideal.Quotient.nontrivial_iff.2 hSt
  have key : ∀ M : Ideal (P ⧸ S), M.IsPrime → M = Q.map (Ideal.Quotient.mk S) := by
    intro M hM
    have hc : (M.comap (Ideal.Quotient.mk S)).IsPrime := Ideal.comap_isPrime _ _
    have h3 : Q ≤ M.comap (Ideal.Quotient.mk S) := by
      refine Ideal.IsPrime.le_of_pow_le (n := n + 1) fun a ha => ?_
      rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.2 (h1 ha)]
      exact M.zero_mem
    exact (Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective M).symm.trans
      (congrArg _ (hQ.eq_of_le hc.ne_top h3).symm)
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (P ⧸ S)
  exact ((Ring.krullDimLE_zero_and_isLocalRing_tfae (P ⧸ S)).out 1 0 rfl rfl).mp
    ⟨M, hM.isPrime, fun M' hM' => (key M' hM').trans (key M hM.isPrime).symm⟩

theorem exists_derivation_extending : ∀ (A P R K : Type) [CommRing A] [CommRing P] [IsNoetherianRing P] [CommRing R] [Field K] [Algebra A P] [Algebra A R] [Algebra P R] [IsScalarTower A P R] [Algebra R K] [Algebra P K] [IsScalarTower P R K] [Algebra A K] [IsScalarTower A P K], Function.Surjective (algebraMap P R) → Function.Surjective (algebraMap R K) → (∀ (C C₀ : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → RingHom.ker π ^ 2 = ⊥ → ∀ (β : A →+* C) (φ₀ : R →+* C₀), φ₀.comp (algebraMap A R) = π.comp β → ∃ φ : R →+* C, π.comp φ = φ₀ ∧ φ.comp (algebraMap A R) = β) → ∀ ℓ : RingHom.ker (algebraMap P R) →ₗ[P] K, ∃ D : Derivation A P K, ∀ i : RingHom.ker (algebraMap P R), D i = ℓ i := by
  intro A P R K _ _ _ _ _ _ _ _ _ _ _ _ _ _ hf hg hlift ℓ
  have hPK : algebraMap P K = (algebraMap R K).comp (algebraMap P R) := IsScalarTower.algebraMap_eq P R K
  have hQm : (RingHom.ker (algebraMap P K)).IsMaximal :=
    RingHom.ker_isMaximal_of_surjective _ (by rw [hPK]; exact hg.comp hf)
  have hIQ : RingHom.ker (algebraMap P R) ≤ RingHom.ker (algebraMap P K) := fun x hx => by
    rw [RingHom.mem_ker] at hx ⊢
    rw [hPK, RingHom.comp_apply, hx, map_zero]
  generalize hI : RingHom.ker (algebraMap P R) = I at ℓ hIQ
  generalize hQ : RingHom.ker (algebraMap P K) = Q at hQm hIQ
  let J : Ideal P := Submodule.map I.subtype (LinearMap.ker ℓ)
  have hJI : J ≤ I := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hJ : ∀ (i i' : P) (hi : i ∈ I) (hi' : i' ∈ I), i' - i ∈ J → ℓ ⟨i, hi⟩ = ℓ ⟨i', hi'⟩ := by
    intro i i' hi hi' h
    obtain ⟨x, hx, hxe⟩ := Submodule.mem_map.1 h
    have e : x = ⟨i', hi'⟩ - ⟨i, hi⟩ := Subtype.ext (by simpa using hxe)
    rw [LinearMap.mem_ker, e, map_sub, sub_eq_zero] at hx
    exact hx.symm
  have hQIJ : Q * I ≤ J := by
    refine Ideal.mul_le.2 fun q hq i hi => ?_
    refine Submodule.mem_map.2 ⟨⟨q * i, I.mul_mem_left q hi⟩, ?_, rfl⟩
    rw [LinearMap.mem_ker]
    have e : (⟨q * i, I.mul_mem_left q hi⟩ : I) = q • ⟨i, hi⟩ := rfl
    rw [e, map_smul, Algebra.smul_def]
    have hq0 : algebraMap P K q = 0 := by rw [← RingHom.mem_ker, hQ]; exact hq
    rw [hq0, zero_mul]
  obtain ⟨k, hk⟩ := Ideal.exists_pow_inf_eq_pow_smul Q (I : Submodule P P)
  have hAR : Q ^ (k + 1) ⊓ I ≤ J := by
    have h := hk (k + 1) (Nat.le_succ k)
    rw [Nat.add_sub_cancel_left, pow_one] at h
    have e : (Q ^ (k + 1) • ⊤ : Submodule P P) = Q ^ (k + 1) := by rw [smul_eq_mul, Ideal.mul_top]
    rw [e] at h
    rw [h]
    exact le_trans (Submodule.smul_mono le_rfl inf_le_right) hQIJ

  let S : Ideal P := J ⊔ Q ^ (k + 1)
  let T : Ideal P := I ⊔ Q ^ (k + 1)
  have hST : S ≤ T := sup_le_sup_right hJI _
  have hSQ : S ≤ Q := sup_le (hJI.trans hIQ) (Ideal.pow_le_self (Nat.succ_ne_zero k))
  obtain ⟨hdim, hloc⟩ := krullDimLE_and_isLocalRing_quotient Q S k le_sup_right hSQ
  haveI : IsArtinianRing (P ⧸ S) := IsNoetherianRing.isArtinianRing_of_krullDimLE_zero
  let π : P ⧸ S →+* P ⧸ T := Ideal.Quotient.factor hST
  have hπmk : ∀ x, π (Ideal.Quotient.mk S x) = Ideal.Quotient.mk T x := fun x => rfl
  have hπs : Function.Surjective π := by
    intro y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨_, hπmk x⟩
  have hTT : ∀ x ∈ T, ∀ y ∈ T, x * y ∈ S := by
    intro x hx y hy
    obtain ⟨i, hi, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
    obtain ⟨i', hi', z', hz', rfl⟩ := Submodule.mem_sup.1 hy
    have e : (i + z) * (i' + z') = i * i' + (i * z' + z * (i' + z')) := by ring
    rw [e]
    refine S.add_mem (Ideal.mem_sup_left (hQIJ (Ideal.mul_mem_mul (hIQ hi) hi'))) (Ideal.mem_sup_right ?_)
    exact (Q ^ (k + 1)).add_mem (Ideal.mul_mem_left _ _ hz') (Ideal.mul_mem_right _ _ hz)
  have hsq : RingHom.ker π ^ 2 = ⊥ := by
    rw [pow_two, eq_bot_iff]
    refine Ideal.mul_le.2 fun c hc d hd => ?_
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective c
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective d
    rw [RingHom.mem_ker, hπmk, Ideal.Quotient.eq_zero_iff_mem] at hc hd
    rw [Ideal.mem_bot, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
    exact hTT x hc y hd
  let β : A →+* P ⧸ S := (Ideal.Quotient.mk S).comp (algebraMap A P)
  have hIT : RingHom.ker (algebraMap P R) ≤ T := hI ▸ le_sup_left
  let e := RingHom.quotientKerEquivOfSurjective hf
  let L : P ⧸ RingHom.ker (algebraMap P R) →+* P ⧸ T :=
    Ideal.Quotient.lift (RingHom.ker (algebraMap P R)) (Ideal.Quotient.mk T)
      (fun a ha => Ideal.Quotient.eq_zero_iff_mem.2 (hIT ha))
  let φ₀ : R →+* P ⧸ T := L.comp e.symm.toRingHom
  have hφ₀ : ∀ a, φ₀ (algebraMap P R a) = Ideal.Quotient.mk T a := by
    intro a
    have h1 : e.symm (algebraMap P R a) = Ideal.Quotient.mk _ a := by
      rw [RingEquiv.symm_apply_eq]; rfl
    change L (e.symm (algebraMap P R a)) = _
    rw [h1, Ideal.Quotient.lift_mk]
  have hcomp : φ₀.comp (algebraMap A R) = π.comp β := by
    ext r
    rw [RingHom.comp_apply, IsScalarTower.algebraMap_apply A P R r, hφ₀]
    rfl
  obtain ⟨φ, hφπ, hφA⟩ := hlift (P ⧸ S) (P ⧸ T) π hπs hsq β φ₀ hcomp

  let δ : P → P ⧸ S := fun a => Ideal.Quotient.mk S a - φ (algebraMap P R a)
  have hδ : ∀ a, δ a ∈ RingHom.ker π := by
    intro a
    rw [RingHom.mem_ker]
    show π (Ideal.Quotient.mk S a - φ (algebraMap P R a)) = 0
    rw [map_sub, hπmk, ← RingHom.comp_apply, hφπ, hφ₀, sub_self]
  have hδadd : ∀ a b, δ (a + b) = δ a + δ b := by
    intro a b
    show Ideal.Quotient.mk S (a + b) - φ (algebraMap P R (a + b)) = _
    rw [map_add, map_add, map_add]
    show _ = (Ideal.Quotient.mk S a - φ (algebraMap P R a)) + (Ideal.Quotient.mk S b - φ (algebraMap P R b))
    ring
  have hδmul : ∀ a b, δ (a * b) = Ideal.Quotient.mk S a * δ b + Ideal.Quotient.mk S b * δ a := by
    intro a b
    have h0 : δ a * δ b = 0 := by
      have : δ a * δ b ∈ RingHom.ker π ^ 2 := by rw [pow_two]; exact Ideal.mul_mem_mul (hδ a) (hδ b)
      rw [hsq] at this
      exact (Ideal.mem_bot.1 this)
    change (Ideal.Quotient.mk S a - φ (algebraMap P R a)) * (Ideal.Quotient.mk S b - φ (algebraMap P R b)) = 0 at h0
    show Ideal.Quotient.mk S (a * b) - φ (algebraMap P R (a * b)) =
      Ideal.Quotient.mk S a * (Ideal.Quotient.mk S b - φ (algebraMap P R b)) +
        Ideal.Quotient.mk S b * (Ideal.Quotient.mk S a - φ (algebraMap P R a))
    rw [map_mul, map_mul, map_mul]
    linear_combination -h0

  let Rl : P ⧸ S → K → Prop := fun c v => ∃ (i : P) (hi : i ∈ I), ∃ z ∈ Q ^ (k + 1),
    Ideal.Quotient.mk S (i + z) = c ∧ ℓ ⟨i, hi⟩ = v
  have huniq : ∀ c v v', Rl c v → Rl c v' → v = v' := by
    rintro c v v' ⟨i, hi, z, hz, rfl, rfl⟩ ⟨i', hi', z', hz', he, rfl⟩
    rw [Ideal.Quotient.eq] at he
    obtain ⟨j, hj, w, hw, hjw⟩ := Submodule.mem_sup.1 he
    have hmem : i' - i - j ∈ Q ^ (k + 1) ⊓ I := by
      refine ⟨?_, (I.sub_mem (I.sub_mem hi' hi) (hJI hj))⟩
      have e1 : i' - i - j = w + z - z' := by linear_combination -hjw
      rw [e1]
      exact (Q ^ (k + 1)).sub_mem ((Q ^ (k + 1)).add_mem hw hz) hz'
    have h2 : i' - i ∈ J := by
      have := J.add_mem (hAR hmem) hj
      rwa [sub_add_cancel] at this
    exact hJ i i' hi hi' h2
  have hex : ∀ c : P ⧸ S, π c = 0 → ∃ v, Rl c v := by
    intro c hc
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective c
    rw [hπmk, Ideal.Quotient.eq_zero_iff_mem] at hc
    obtain ⟨i, hi, z, hz, rfl⟩ := Submodule.mem_sup.1 hc
    exact ⟨_, i, hi, z, hz, rfl, rfl⟩
  have hRadd : ∀ c c' v v', Rl c v → Rl c' v' → Rl (c + c') (v + v') := by
    rintro c c' v v' ⟨i, hi, z, hz, rfl, rfl⟩ ⟨i', hi', z', hz', rfl, rfl⟩
    refine ⟨i + i', I.add_mem hi hi', z + z', (Q ^ (k + 1)).add_mem hz hz', ?_, ?_⟩
    · rw [← map_add]; congr 1; ring
    · rw [← map_add]; rfl
  have hRsmul : ∀ c v (p : P), Rl c v → Rl (Ideal.Quotient.mk S p * c) (p • v) := by
    rintro c v p ⟨i, hi, z, hz, rfl, rfl⟩
    refine ⟨p * i, I.mul_mem_left p hi, p * z, Ideal.mul_mem_left _ p hz, ?_, ?_⟩
    · rw [← map_mul]; congr 1; ring
    · rw [← map_smul]; rfl
  have hR0 : Rl 0 0 := ⟨0, I.zero_mem, 0, (Q ^ (k + 1)).zero_mem, by simp, map_zero ℓ⟩
  have hRI : ∀ i (hi : i ∈ I), Rl (Ideal.Quotient.mk S i) (ℓ ⟨i, hi⟩) :=
    fun i hi => ⟨i, hi, 0, (Q ^ (k + 1)).zero_mem, by rw [add_zero], rfl⟩
  let D0 : P → K := fun a => Classical.choose (hex (δ a) (hδ a))
  have hD0 : ∀ a v, Rl (δ a) v → D0 a = v := fun a v h =>
    huniq _ _ _ (Classical.choose_spec (hex (δ a) (hδ a))) h
  have hspec : ∀ a, Rl (δ a) (D0 a) := fun a => Classical.choose_spec (hex (δ a) (hδ a))
  have hDadd : ∀ a b, D0 (a + b) = D0 a + D0 b := fun a b =>
    hD0 _ _ (by rw [hδadd]; exact hRadd _ _ _ _ (hspec a) (hspec b))
  have hDmul : ∀ a b, D0 (a * b) = a • D0 b + b • D0 a := fun a b =>
    hD0 _ _ (by rw [hδmul]; exact hRadd _ _ _ _ (hRsmul _ _ a (hspec b)) (hRsmul _ _ b (hspec a)))
  have hDA : ∀ r : A, D0 (algebraMap A P r) = 0 := by
    intro r
    refine hD0 _ _ ?_
    have : δ (algebraMap A P r) = 0 := by
      show Ideal.Quotient.mk S (algebraMap A P r) - φ (algebraMap P R (algebraMap A P r)) = 0
      rw [← IsScalarTower.algebraMap_apply A P R r, ← RingHom.comp_apply φ, hφA, sub_eq_zero]
      rfl
    rw [this]; exact hR0
  let Dl : P →ₗ[A] K :=
    { toFun := D0
      map_add' := hDadd
      map_smul' := fun r a => by
        rw [Algebra.smul_def, hDmul, hDA, smul_zero, add_zero, RingHom.id_apply, algebraMap_smul] }
  refine ⟨Derivation.mk' Dl hDmul, fun ⟨i, hi⟩ => ?_⟩
  show D0 i = ℓ ⟨i, hi⟩
  refine hD0 _ _ ?_
  have : δ i = Ideal.Quotient.mk S i := by
    show Ideal.Quotient.mk S i - φ (algebraMap P R i) = _
    have hi0 : algebraMap P R i = 0 := by rw [← RingHom.mem_ker, hI]; exact hi
    rw [hi0, map_zero, sub_zero]
  rw [this]; exact hRI i hi

end GlobalTheory.LiftDeriv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDetOneMulStdBlock
section
namespace GlobalTheory

open Matrix

theorem exists_det_one_mul_stdBlock {K : Type} [Field K] {n r : ℕ} (hrn : r < n)
    (y : Matrix (Fin n) (Fin r) K) (hy : y.rank = r) :
    ∃ g : GL (Fin n) K, Matrix.GeneralLinearGroup.det g = 1 ∧
      g.val * (Matrix.of fun (a : Fin n) (b : Fin r) => if (a : ℕ) = (b : ℕ) then (1 : K) else 0) = y := by
  classical
  have hli : LinearIndependent K y.col := by
    rw [linearIndependent_iff_card_eq_finrank_span, Fintype.card_fin]
    rw [Matrix.rank_eq_finrank_span_cols] at hy
    exact hy.symm
  let b := Module.Basis.sumExtend hli
  have hfin : Finite (Fin r ⊕ Module.Basis.sumExtendIndex hli) := Module.Finite.finite_basis b
  have : Finite (Module.Basis.sumExtendIndex hli) := Finite.of_injective (Sum.inr : _ → Fin r ⊕ _) Sum.inr_injective
  have : Fintype (Module.Basis.sumExtendIndex hli) := Fintype.ofFinite _
  have hcard : Fintype.card (Fin r ⊕ Module.Basis.sumExtendIndex hli) = n := by
    rw [← Module.finrank_eq_card_basis b, Module.finrank_fin_fun]
  have hb : ∀ i, b (Sum.inl i) = y.col i := by
    intro i
    simp only [b, Module.Basis.sumExtend, Module.Basis.reindex_apply, Module.Basis.coe_extend,
      Equiv.symm_symm, Equiv.trans_apply, Equiv.sumCongr_apply]
    rfl
  have hS : Fintype.card (Module.Basis.sumExtendIndex hli) = n - r := by
    rw [Fintype.card_sum, Fintype.card_fin] at hcard; omega
  let e : Fin (n - r) ≃ Module.Basis.sumExtendIndex hli := (Fintype.equivFinOfCardEq hS).symm
  let τ : Fin n → Fin r ⊕ Module.Basis.sumExtendIndex hli := fun c =>
    if h : (c : ℕ) < r then Sum.inl ⟨c, h⟩ else Sum.inr (e ⟨c - r, by omega⟩)
  have hτ : Function.Injective τ := by
    intro c c' h
    simp only [τ] at h
    split_ifs at h
    all_goals first
      | (simp only [Sum.inl.injEq, Fin.mk.injEq] at h; ext; omega)
      | (simp only [Sum.inr.injEq, EmbeddingLike.apply_eq_iff_eq, Fin.mk.injEq] at h; ext; omega)
      | exact absurd h Sum.inl_ne_inr
      | exact absurd h.symm Sum.inl_ne_inr
  let s : Fin n → Fin n → K := b ∘ τ
  have hs : LinearIndependent K s := b.linearIndependent.comp τ hτ
  let g₀ : Matrix (Fin n) (Fin n) K := Matrix.of fun i a => s a i
  have hg₀col : g₀.col = s := by ext a i; rfl
  have hu : IsUnit g₀ := Matrix.linearIndependent_cols_iff_isUnit.mp (hg₀col ▸ hs)
  have hdet : g₀.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).mp hu).ne_zero
  let last : Fin n := ⟨n - 1, by omega⟩
  let D : Matrix (Fin n) (Fin n) K := Matrix.diagonal fun a => if a = last then g₀.det⁻¹ else 1
  let g := g₀ * D
  have hgdet : g.det = 1 := by
    simp only [g, D, Matrix.det_mul, Matrix.det_diagonal, Finset.prod_ite_eq', Finset.mem_univ, if_true]
    exact mul_inv_cancel₀ hdet
  have hU : IsUnit g := (Matrix.isUnit_iff_isUnit_det g).mpr (by rw [hgdet]; exact isUnit_one)
  refine ⟨hU.unit, ?_, ?_⟩
  · ext
    simp [Matrix.GeneralLinearGroup.val_det_apply, hgdet]
  · have hE : ∀ (a : Fin n) (c : Fin r), ((a : ℕ) = (c : ℕ)) ↔ a = Fin.castLE hrn.le c := by
      intro a c; rw [Fin.ext_iff, Fin.coe_castLE]
    have hτc : ∀ c : Fin r, τ (Fin.castLE hrn.le c) = Sum.inl c := by
      intro c
      simp only [τ, Fin.coe_castLE, dif_pos c.isLt]
    rw [IsUnit.unit_spec]
    ext i c
    simp only [g, D, Matrix.mul_assoc, Matrix.mul_apply, Matrix.diagonal_apply, Matrix.of_apply, hE]
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
    have hne : Fin.castLE hrn.le c ≠ last := by
      intro h
      have h2 := congrArg Fin.val h
      simp only [Fin.coe_castLE, last] at h2
      omega
    simp only [if_neg hne, mul_one]
    show b (τ (Fin.castLE hrn.le c)) i = y i c
    rw [hτc, hb]
    rfl

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDividedPowerEvalTwoVarsRingHom
section
open MvPolynomial

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.DPEval2

def bv (p : ℕ × ℕ) : MvPolynomial (Fin 2) ℚ :=
  ((p.1.factorial : ℚ)⁻¹ • (X 0 : MvPolynomial (Fin 2) ℚ) ^ p.1) * ((p.2.factorial : ℚ)⁻¹ • X 1 ^ p.2)

def ex (p : ℕ × ℕ) : Fin 2 →₀ ℕ := Finsupp.single 0 p.1 + Finsupp.single 1 p.2

theorem ex_injective : Function.Injective ex := by
  intro p q h
  have h0 := congrArg (fun f : Fin 2 →₀ ℕ ↦ f 0) h
  have h1 := congrArg (fun f : Fin 2 →₀ ℕ ↦ f 1) h
  simp [ex] at h0 h1
  exact Prod.ext h0 h1

theorem bv_eq (p : ℕ × ℕ) :
    bv p = ((p.1.factorial : ℚ)⁻¹ * (p.2.factorial : ℚ)⁻¹) • monomial (ex p) (1 : ℚ) := by
  rw [bv, ex, X_pow_eq_monomial, X_pow_eq_monomial, smul_monomial, smul_monomial, monomial_mul,
    smul_monomial]
  simp

theorem bv_li : LinearIndependent ℚ bv := by
  have h := ((basisMonomials (Fin 2) ℚ).linearIndependent.comp ex ex_injective).units_smul
    (fun p : ℕ × ℕ ↦ Units.mk0 ((p.1.factorial : ℚ)⁻¹ * (p.2.factorial : ℚ)⁻¹) (by positivity))
  have e : bv = (fun p : ℕ × ℕ ↦ Units.mk0 ((p.1.factorial : ℚ)⁻¹ * (p.2.factorial : ℚ)⁻¹) (by positivity)) •
      (⇑(basisMonomials (Fin 2) ℚ) ∘ ex) := by
    funext p
    simp [bv_eq, Units.smul_def, coe_basisMonomials]
  rw [e]; exact h

theorem ex_add (p q : ℕ × ℕ) : ex (p + q) = ex p + ex q := by
  simp only [ex, Prod.fst_add, Prod.snd_add, Finsupp.single_add]; abel

theorem bv_mul (p q : ℕ × ℕ) :
    bv p * bv q = ((p.1 + q.1).choose p.1 * (p.2 + q.2).choose p.2 : ℕ) • bv (p + q) := by
  rw [bv_eq, bv_eq, bv_eq, smul_mul_smul, monomial_mul, ← ex_add, ← Nat.cast_smul_eq_nsmul ℚ, smul_smul,
    mul_one]
  congr 1
  simp only [Prod.fst_add, Prod.snd_add, Nat.cast_mul, Nat.cast_add_choose]
  field_simp

def D : Submodule ℤ (MvPolynomial (Fin 2) ℚ) := Submodule.span ℤ (Set.range bv)

theorem bv_mem (p : ℕ × ℕ) : bv p ∈ D := Submodule.subset_span ⟨p, rfl⟩

def β : Module.Basis (ℕ × ℕ) ℤ D := Module.Basis.span (bv_li.restrict_scalars' ℤ)

theorem β_eq (p : ℕ × ℕ) : β p = ⟨bv p, bv_mem p⟩ :=
  Module.Basis.span_apply _ p

theorem mul_mem {x y : MvPolynomial (Fin 2) ℚ} (hx : x ∈ D) (hy : y ∈ D) : x * y ∈ D := by
  refine Submodule.span_induction₂ (p := fun x y _ _ ↦ x * y ∈ D) ?_ ?_ ?_ ?_ ?_ ?_ ?_ hx hy
  · rintro _ _ ⟨m, rfl⟩ ⟨n, rfl⟩
    rw [bv_mul]
    exact Submodule.smul_of_tower_mem _ _ (bv_mem _)
  · intro y _; simp
  · intro y _; simp
  · intro x y z _ _ _ h1 h2; rw [add_mul]; exact add_mem h1 h2
  · intro x y z _ _ _ h1 h2; rw [mul_add]; exact add_mem h1 h2
  · intro r x y _ _ h; rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ h
  · intro r x y _ _ h; rw [mul_smul_comm]; exact Submodule.smul_mem _ _ h

variable {B : Type} [CommRing B] (u v : ℕ → B)

def ψ : D →ₗ[ℤ] B := β.constr ℤ fun p ↦ u p.1 * v p.2

open Classical in

def φ (q : MvPolynomial (Fin 2) ℚ) : B := if h : q ∈ D then ψ u v ⟨q, h⟩ else 0

theorem φ_of_mem {q : MvPolynomial (Fin 2) ℚ} (h : q ∈ D) : φ u v q = ψ u v ⟨q, h⟩ := dif_pos h

theorem φ_bv (p : ℕ × ℕ) : φ u v (bv p) = u p.1 * v p.2 := by
  rw [φ_of_mem u v (bv_mem p), ← β_eq, ψ, Module.Basis.constr_basis]

theorem φ_add {x y : MvPolynomial (Fin 2) ℚ} (hx : x ∈ D) (hy : y ∈ D) :
    φ u v (x + y) = φ u v x + φ u v y := by
  rw [φ_of_mem u v hx, φ_of_mem u v hy, φ_of_mem u v (add_mem hx hy), ← map_add]; rfl

theorem φ_zsmul (z : ℤ) {x : MvPolynomial (Fin 2) ℚ} (hx : x ∈ D) : φ u v (z • x) = z • φ u v x := by
  rw [φ_of_mem u v hx, φ_of_mem u v (Submodule.smul_mem _ z hx), ← map_zsmul]; rfl

theorem φ_nsmul (n : ℕ) {x : MvPolynomial (Fin 2) ℚ} (hx : x ∈ D) : φ u v (n • x) = n • φ u v x := by
  rw [← Nat.cast_smul_eq_nsmul ℤ n x, φ_zsmul u v _ hx, Nat.cast_smul_eq_nsmul]

theorem φ_zero : φ u v 0 = 0 := by
  rw [φ_of_mem u v (zero_mem _)]; exact map_zero (ψ u v)

theorem φ_mul (hu : ∀ m n, u m * u n = ((m + n).choose m : B) * u (m + n))
    (hv : ∀ m n, v m * v n = ((m + n).choose m : B) * v (m + n))
    {x y : MvPolynomial (Fin 2) ℚ} (hx : x ∈ D) (hy : y ∈ D) :
    φ u v (x * y) = φ u v x * φ u v y := by
  refine Submodule.span_induction₂ (p := fun x y hx hy ↦ φ u v (x * y) = φ u v x * φ u v y)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ hx hy
  · rintro _ _ ⟨p, rfl⟩ ⟨q, rfl⟩
    rw [bv_mul, φ_nsmul u v _ (bv_mem _), φ_bv, φ_bv, φ_bv, nsmul_eq_mul]
    calc ((((p.1 + q.1).choose p.1 * (p.2 + q.2).choose p.2 : ℕ)) : B) * (u (p + q).1 * v (p + q).2)
        = (((p.1 + q.1).choose p.1 : B) * u (p.1 + q.1)) * (((p.2 + q.2).choose p.2 : B) * v (p.2 + q.2)) := by
          simp only [Prod.fst_add, Prod.snd_add, Nat.cast_mul]; ring
      _ = u p.1 * v p.2 * (u q.1 * v q.2) := by rw [← hu, ← hv]; ring
  · intro y _; simp [φ_zero]
  · intro y _; simp [φ_zero]
  · intro x y z hx hy hz h1 h2
    rw [add_mul, φ_add u v (mul_mem hx hz) (mul_mem hy hz), φ_add u v hx hy, h1, h2, add_mul]
  · intro x y z hx hy hz h1 h2
    rw [mul_add, φ_add u v (mul_mem hx hy) (mul_mem hx hz), φ_add u v hy hz, h1, h2, mul_add]
  · intro r x y hx hy h
    rw [smul_mul_assoc, φ_zsmul u v r (mul_mem hx hy), φ_zsmul u v r hx, h, smul_mul_assoc]
  · intro r x y hx hy h
    rw [mul_smul_comm, φ_zsmul u v r (mul_mem hx hy), φ_zsmul u v r hy, h, mul_smul_comm]

end GlobalTheory.DPEval2

namespace GlobalTheory

open DPEval2 in

theorem dpEval_two :
    ∀ (B : Type) [CommRing B] (u v : ℕ → B), u 0 = 1 → v 0 = 1 →
    (∀ m n, u m * u n = ((m + n).choose m : B) * u (m + n)) →
    (∀ m n, v m * v n = ((m + n).choose m : B) * v (m + n)) →
    ∃ φ : MvPolynomial (Fin 2) ℚ → B,
      (∀ a c : ℕ, φ (((a.factorial : ℚ)⁻¹ • MvPolynomial.X 0 ^ a) * ((c.factorial : ℚ)⁻¹ • MvPolynomial.X 1 ^ c)) = u a * v c) ∧
      (∀ d ∈ Submodule.span ℤ (Set.range fun p : ℕ × ℕ ↦ ((p.1.factorial : ℚ)⁻¹ • (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℚ) ^ p.1) * ((p.2.factorial : ℚ)⁻¹ • MvPolynomial.X 1 ^ p.2)),
        ∀ e ∈ Submodule.span ℤ (Set.range fun p : ℕ × ℕ ↦ ((p.1.factorial : ℚ)⁻¹ • (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℚ) ^ p.1) * ((p.2.factorial : ℚ)⁻¹ • MvPolynomial.X 1 ^ p.2)),
          φ (d + e) = φ d + φ e ∧
          d * e ∈ Submodule.span ℤ (Set.range fun p : ℕ × ℕ ↦ ((p.1.factorial : ℚ)⁻¹ • (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℚ) ^ p.1) * ((p.2.factorial : ℚ)⁻¹ • MvPolynomial.X 1 ^ p.2)) ∧
          φ (d * e) = φ d * φ e) ∧
      (∀ z : ℤ, ∀ d ∈ Submodule.span ℤ (Set.range fun p : ℕ × ℕ ↦ ((p.1.factorial : ℚ)⁻¹ • (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℚ) ^ p.1) * ((p.2.factorial : ℚ)⁻¹ • MvPolynomial.X 1 ^ p.2)),
        φ (z • d) = z • φ d) := by
  intro B _ u v _ _ hu hv
  refine ⟨φ u v, fun a c ↦ φ_bv u v (a, c), fun d hd e he ↦ ?_, fun z d hd ↦ φ_zsmul u v z hd⟩
  exact ⟨φ_add u v hd he, mul_mem hd he, φ_mul u v hu hv hd he⟩

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEquivEuclideanPiMulNormSqEqRe
section
open FourierTransform MeasureTheory Filter Topology

namespace GlobalTheory

theorem exists_equiv_euclidean_pi_mul_norm_sq_eq_re (V : Type) [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] (Q : V →L[ℝ] V →L[ℝ] ℂ) (c : ℝ)
    (hc : 0 < c) (hQ : ∀ x, c * ‖x‖ ^ 2 ≤ (Q x x).re) :
    ∃ A : V ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ V)),
      ∀ x, Real.pi * ‖A x‖ ^ 2 = (Q x x).re := by
  classical
  let B : LinearMap.BilinForm ℝ V := LinearMap.mk₂ ℝ (fun x y => (Q x y).re)
    (by intros; simp) (by intros; simp) (by intros; simp) (by intros; simp)
  let q : QuadraticForm ℝ V := B.toQuadraticMap
  have hq : ∀ x, q x = (Q x x).re := fun x => rfl
  obtain ⟨w, ⟨e⟩⟩ := QuadraticForm.equivalent_weightedSumSquares q
  have he : ∀ x, ∑ i, w i * (e x i * e x i) = (Q x x).re := by
    intro x
    have := e.map_app x
    rw [QuadraticMap.weightedSumSquares_apply] at this
    simpa [hq] using this
  have hw : ∀ i, 0 < w i := by
    intro i
    have h1 := he (e.symm (Pi.single i 1))
    have h2 : e (e.symm (Pi.single i 1)) = Pi.single i 1 := e.toLinearEquiv.apply_symm_apply _
    have hne : e.symm (Pi.single i 1) ≠ 0 := by
      intro h
      rw [h, map_zero] at h2
      have := congrFun h2 i
      simp at this
    rw [h2, Finset.sum_eq_single i (by intro j _ hj; simp [hj]) (by simp)] at h1
    have h3 := hQ (e.symm (Pi.single i 1))
    have h4 : 0 < c * ‖e.symm (Pi.single i 1)‖ ^ 2 := by
      have := norm_pos_iff.mpr hne
      positivity
    simp at h1
    linarith
  have hs : ∀ i, Real.sqrt (w i / Real.pi) ≠ 0 := fun i =>
    (Real.sqrt_pos.mpr (div_pos (hw i) Real.pi_pos)).ne'
  let D : (Fin (Module.finrank ℝ V) → ℝ) ≃ₗ[ℝ] (Fin (Module.finrank ℝ V) → ℝ) :=
    LinearEquiv.piCongrRight fun i =>
      LinearEquiv.smulOfNeZero ℝ ℝ (Real.sqrt (w i / Real.pi)) (hs i)
  let A : V ≃ₗ[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) :=
    (e.toLinearEquiv.trans D).trans (WithLp.linearEquiv 2 ℝ _).symm
  have hA : ∀ x i, A x i = Real.sqrt (w i / Real.pi) * e x i := fun x i => rfl
  refine ⟨A.toContinuousLinearEquiv, fun x => ?_⟩
  rw [← he, EuclideanSpace.norm_sq_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have : (A.toContinuousLinearEquiv x) i = Real.sqrt (w i / Real.pi) * e x i := hA x i
  rw [this, Real.norm_eq_abs, sq_abs, mul_pow, Real.sq_sqrt (div_pos (hw i) Real.pi_pos).le]
  have := Real.pi_pos.ne'
  field_simp

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntMatrixTransposeMulEqSmulOne
section
namespace GlobalTheory

theorem exists_int_matrix_transpose_mul_eq_smul_one (s : ℕ) :
    ∃ x : Matrix (Fin 4) (Fin 4) ℤ, x.transpose * x = (s : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) ∧
      x * x.transpose = (s : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) := by
  obtain ⟨a, b, c, d, h⟩ := Nat.sum_four_squares s
  have h' : ((a : ℤ) ^ 2 + (b : ℤ) ^ 2 + (c : ℤ) ^ 2 + (d : ℤ) ^ 2) = (s : ℤ) := by
    exact_mod_cast h
  refine ⟨!![(a:ℤ), -b, -c, -d; b, a, -d, c; c, d, a, -b; d, -c, b, a], ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply] <;>
      first | linear_combination h' | ring
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply] <;>
      first | linear_combination h' | ring

end GlobalTheory
end

