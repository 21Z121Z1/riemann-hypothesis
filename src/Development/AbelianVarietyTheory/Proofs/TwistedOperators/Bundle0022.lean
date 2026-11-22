import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RadfordShufflePolynomialHolds
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0013
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0016
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0012
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0014
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0015

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ShuffleCountLinearIndependentClasses
section
open GlobalTheory

namespace GlobalTheory.ShuffleCount

open MvPolynomial

private theorem aeval_killCompl {S B : Type*} [CommRing B] [Algebra ℚ B] (U : Set S)
    (φ : S → B) (h0 : ∀ Δ ∉ U, φ Δ = 0) (P : MvPolynomial S ℚ) :
    aeval (fun Δ : U => φ Δ) (killCompl (R := ℚ) (Subtype.val_injective : Function.Injective (Subtype.val : U → S)) P) = aeval φ P := by
  classical
  have key : (aeval (fun Δ : U => φ Δ)).comp (killCompl (R := ℚ) (Subtype.val_injective : Function.Injective (Subtype.val : U → S))) = aeval φ := by
    apply MvPolynomial.algHom_ext
    intro Δ
    by_cases hΔ : Δ ∈ U
    · have hX : (X Δ : MvPolynomial S ℚ) = rename Subtype.val (X (⟨Δ, hΔ⟩ : U)) := by rw [rename_X]
      rw [AlgHom.comp_apply]
      conv_lhs => rw [hX]
      rw [killCompl_rename_app, aeval_X, aeval_X]
    · rw [AlgHom.comp_apply, aeval_X, h0 Δ hΔ, X, killCompl_monomial_eq_zero_of_not_subset, map_zero]
      intro h
      obtain ⟨⟨_, hmem⟩, rfl⟩ := h (by simp : Δ ∈ (↑(Finsupp.single Δ 1).support : Set S))
      exact hΔ hmem
  exact AlgHom.congr_fun key P

private theorem coeff_killCompl_comapDomain {S : Type*} (U : Set S) (P : MvPolynomial S ℚ) (m : S →₀ ℕ)
    (hm : ↑m.support ⊆ Set.range (Subtype.val : U → S)) :
    coeff (m.comapDomain (Subtype.val : U → S) (Subtype.val_injective : Function.Injective (Subtype.val : U → S)).injOn)
      (killCompl (R := ℚ) (Subtype.val_injective : Function.Injective (Subtype.val : U → S)) P) = coeff m P := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial n r =>
    by_cases hn : ↑n.support ⊆ Set.range (Subtype.val : U → S)
    · rw [killCompl_monomial_eq_monomial_comapDomain_of_subset _ _ hn, coeff_monomial, coeff_monomial]
      have hiff : n.comapDomain (Subtype.val : U → S) (Subtype.val_injective : Function.Injective (Subtype.val : U → S)).injOn =
          m.comapDomain (Subtype.val : U → S) (Subtype.val_injective : Function.Injective (Subtype.val : U → S)).injOn ↔ n = m := by
        constructor
        · intro h
          rw [← Finsupp.mapDomain_comapDomain _ Subtype.val_injective n hn,
            ← Finsupp.mapDomain_comapDomain _ Subtype.val_injective m hm, h]
        · rintro rfl
          rfl
      simp only [hiff]
    · rw [killCompl_monomial_eq_zero_of_not_subset _ _ hn, coeff_zero, coeff_monomial, if_neg]
      rintro rfl
      exact hn hm
  | add P Q hP hQ => rw [map_add, coeff_add, coeff_add, hP, hQ]

theorem coeff_eq_zero_of_aeval_eq_zero {S B : Type*} [CommRing B] [Algebra ℚ B] (U : Set S)
    (φ : S → B) (hind : AlgebraicIndependent ℚ (fun Δ : U => φ Δ)) (h0 : ∀ Δ ∉ U, φ Δ = 0)
    (P : MvPolynomial S ℚ) (hP : aeval φ P = 0) (m : S →₀ ℕ) (hm : ∀ Δ ∈ m.support, Δ ∈ U) :
    coeff m P = 0 := by
  classical
  have hm' : ↑m.support ⊆ Set.range (Subtype.val : U → S) := fun Δ hΔ =>
    ⟨⟨Δ, hm Δ (Finset.mem_coe.1 hΔ)⟩, rfl⟩
  rw [← coeff_killCompl_comapDomain U P m hm']
  have hQ : killCompl (R := ℚ) (Subtype.val_injective : Function.Injective (Subtype.val : U → S)) P = 0 := by
    apply algebraicIndependent_iff_injective_aeval.1 hind
    rw [map_zero, aeval_killCompl U φ h0 P, hP]
  rw [hQ, coeff_zero]

theorem separates_of_shuffle_count : ∀ (I S : Type 1) (A : Type) [DecidableEq A] [LinearOrder A] (Ψ : (I →₀ ℤ) ≃+ MvPolynomial S ℤ) (M : I → List A → ℕ∞) (U : Set S) (ℓ : S → List A) (φ : S → ShuffleAlgebra ℚ A), Set.InjOn ℓ U → (∀ Δ ∈ U, IsLyndon (ℓ Δ) ∧ φ Δ = ShuffleAlgebra.word ℚ (ℓ Δ)) → (∀ Δ ∉ U, φ Δ = 0) → (∀ m : S →₀ ℕ, 0 ≤ Ψ.symm (MvPolynomial.monomial m 1) ∧ ∃ s : Multiset (List A), (∀ w, ((Ψ.symm (MvPolynomial.monomial m 1)).sum fun x a => (a.toNat : ℕ∞) * M x w) = (s.count w : ℕ∞)) ∧ (s.map (ShuffleAlgebra.word ℚ)).sum = m.prod fun Δ e => φ Δ ^ e) → ∀ (n : ℕ) (p : Fin n → I) (c : Fin n → ℂ), Function.Injective p → (∀ i, ∃ w, M (p i) w ≠ 0) → (∀ w, ∑ i, c i * ((M (p i) w).toNat : ℂ) = 0) → ∀ i, c i = 0 := by
  intro I S A _ _ Ψ M U ℓ φ hinj hU hφ0 hcnt n p c hp hne hc
  classical
  let Rh : List A → (I →₀ ℤ) →+ ℤ := fun w =>
    Finsupp.liftAddHom fun x => AddMonoidHom.mulRight ((M x w).toNat : ℤ)
  have hRs : ∀ w x a, Rh w (Finsupp.single x a) = a * ((M x w).toNat : ℤ) := fun w x a => by
    simp [Rh]
  have hRsum : ∀ w (y : I →₀ ℤ), Rh w y = y.sum fun x a => a * ((M x w).toNat : ℤ) := fun w y => by
    simp [Rh, Finsupp.liftAddHom_apply]
  have K0 : ∀ (y : I →₀ ℤ) (w : List A) (N : ℕ), 0 ≤ y →
      (y.sum fun x a => (a.toNat : ℕ∞) * M x w) = (N : ℕ∞) → Rh w y = N := by
    intro y w N hy hN
    rw [Finsupp.sum] at hN
    have hfin : ∀ x ∈ y.support, ((y x).toNat : ℕ∞) * M x w ≠ ⊤ := by
      intro x hx htop
      have hle : ((y x).toNat : ℕ∞) * M x w ≤ ∑ x ∈ y.support, ((y x).toNat : ℕ∞) * M x w :=
        Finset.single_le_sum (f := fun x => ((y x).toNat : ℕ∞) * M x w) (fun _ _ => zero_le) hx
      rw [hN, htop] at hle
      exact ENat.natCast_ne_top N (top_le_iff.1 hle)
    have h1 := congrArg ENat.toNat hN
    rw [ENat.toNat_sum hfin, ENat.toNat_natCast] at h1
    simp only [ENat.toNat_mul, ENat.toNat_natCast] at h1
    rw [hRsum, Finsupp.sum, ← h1, Nat.cast_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Nat.cast_mul, Int.toNat_of_nonneg (Finsupp.le_def.1 hy x)]
  have K1 : ∀ (w : List A) (P : MvPolynomial S ℤ),
      (ShuffleAlgebra.wordBasis ℚ A).repr (aeval φ (MvPolynomial.map (Int.castRingHom ℚ) P)) w =
        ((Rh w (Ψ.symm P) : ℤ) : ℚ) := by
    intro w P
    induction P using MvPolynomial.induction_on' with
    | monomial m r =>
      obtain ⟨hpos, s, hs1, hs2⟩ := hcnt m
      have hmr : (MvPolynomial.monomial m r : MvPolynomial S ℤ) = r • MvPolynomial.monomial m 1 := by
        rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
      rw [MvPolynomial.map_monomial, MvPolynomial.aeval_monomial, ← hs2, ← Algebra.smul_def, map_smul,
        Finsupp.smul_apply, Lyndon.repr_sum_word, hmr, map_zsmul, map_zsmul, K0 _ w _ hpos (hs1 w),
        smul_eq_mul, smul_eq_mul]
      simp only [eq_intCast, Int.cast_mul, Int.cast_natCast]
      congr
    | add P Q hP hQ =>
      simp only [map_add, Finsupp.add_apply, hP, hQ, Int.cast_add]
  have K2 : ∀ m : S →₀ ℕ, (∃ Δ ∈ m.support, Δ ∉ U) →
      ∀ x, Ψ.symm (MvPolynomial.monomial m 1) x ≠ 0 → ∀ w, M x w = 0 := by
    rintro m ⟨Δ, hΔ, hΔU⟩ x hx w
    obtain ⟨hpos, s, hs1, hs2⟩ := hcnt m
    have hprod : (m.prod fun Δ e => φ Δ ^ e) = 0 :=
      Finset.prod_eq_zero hΔ (by show φ Δ ^ m Δ = 0; rw [hφ0 Δ hΔU, zero_pow (Finsupp.mem_support_iff.1 hΔ)])
    have hcount : s.count w = 0 := by
      have h := Lyndon.repr_sum_word ℚ s w
      rw [hs2, hprod, map_zero, Finsupp.zero_apply] at h
      have h'' := Nat.cast_eq_zero.1 h.symm
      convert h''
    have h1 := hs1 w
    rw [hcount, Finsupp.sum, Nat.cast_zero, Finset.sum_eq_zero_iff] at h1
    have h2 := h1 x (Finsupp.mem_support_iff.2 hx)
    rcases mul_eq_zero.1 h2 with h | h
    · exfalso
      have hnn := Finsupp.le_def.1 hpos x
      have h0 : (Ψ.symm (MvPolynomial.monomial m 1) x).toNat = 0 := by exact_mod_cast h
      simp only [Finsupp.coe_zero, Pi.zero_apply] at hnn
      omega
    · exact h
  have hind : AlgebraicIndependent ℚ (fun Δ : U => φ Δ) := by
    have hR := Published.radfordShufflePolynomial_holds.algebraicIndependent ℚ A
    have he : Function.Injective
        (fun Δ : U => (⟨ℓ Δ, (hU Δ Δ.2).1⟩ : {w : List A // IsLyndon w})) := by
      intro a b hab
      exact Subtype.ext (hinj a.2 b.2 (congrArg Subtype.val hab))
    have hcomp := hR.comp _ he
    have heq : (fun Δ : U => φ Δ) =
        (fun l : {w : List A // IsLyndon w} => ShuffleAlgebra.word ℚ l.1) ∘
          (fun Δ : U => (⟨ℓ Δ, (hU Δ Δ.2).1⟩ : {w : List A // IsLyndon w})) := by
      funext Δ
      exact (hU Δ Δ.2).2
    rw [heq]
    exact hcomp
  have K3 : ∀ k : Fin n → ℤ, (∀ w, ∑ j, k j * ((M (p j) w).toNat : ℤ) = 0) → ∀ i, k i = 0 := by
    intro k hk i
    by_contra hki
    set y : I →₀ ℤ := ∑ j, Finsupp.single (p j) (k j) with hy
    have hRy : ∀ w, Rh w y = 0 := fun w => by
      rw [hy, map_sum]
      simp only [hRs]
      exact hk w
    set P := Ψ y with hPdef
    have hEv : aeval φ (MvPolynomial.map (Int.castRingHom ℚ) P) = 0 := by
      apply (ShuffleAlgebra.wordBasis ℚ A).repr.injective
      rw [map_zero]
      ext w
      rw [K1, hPdef, AddEquiv.symm_apply_apply, hRy, Int.cast_zero, Finsupp.zero_apply]
    have hcoef : ∀ m : S →₀ ℕ, (∀ Δ ∈ m.support, Δ ∈ U) → P.coeff m = 0 := by
      intro m hm
      have h := coeff_eq_zero_of_aeval_eq_zero U φ hind hφ0 _ hEv m hm
      rw [MvPolynomial.coeff_map, eq_intCast, Int.cast_eq_zero] at h
      exact h
    have hyP : y = ∑ m ∈ P.support, P.coeff m • Ψ.symm (MvPolynomial.monomial m 1) := by
      have h : y = Ψ.symm P := by rw [hPdef, AddEquiv.symm_apply_apply]
      conv_lhs => rw [h, P.as_sum]
      rw [map_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [← map_zsmul, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
    have hyi : y (p i) = k i := by
      rw [hy, Finsupp.finsetSum_apply, Finset.sum_eq_single i]
      · simp
      · intro j _ hji
        rw [Finsupp.single_apply, if_neg]
        exact fun h => hji (hp h)
      · intro h
        exact absurd (Finset.mem_univ i) h
    have hne0 : (∑ m ∈ P.support, P.coeff m • Ψ.symm (MvPolynomial.monomial m 1)) (p i) ≠ 0 := by
      rw [← hyP, hyi]
      exact hki
    rw [Finsupp.finsetSum_apply] at hne0
    obtain ⟨m, _, hm0⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne0
    rw [Finsupp.smul_apply, smul_eq_mul] at hm0
    have hc0 : P.coeff m ≠ 0 := left_ne_zero_of_mul hm0
    have hx0 : Ψ.symm (MvPolynomial.monomial m 1) (p i) ≠ 0 := right_ne_zero_of_mul hm0
    have hout : ∃ Δ ∈ m.support, Δ ∉ U := by
      by_contra h
      push_neg at h
      exact hc0 (hcoef m h)
    obtain ⟨w, hw⟩ := hne i
    exact hw (K2 m hout (p i) hx0 w)
  have KQ : ∀ q : Fin n → ℚ, (∀ w, ∑ j, q j * ((M (p j) w).toNat : ℚ) = 0) → ∀ i, q i = 0 := by
    intro q hq i
    obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors ℤ)
      (Finset.univ : Finset (Fin n)) q
    choose k hk using fun j => RingHom.mem_rangeS.1 (hb j (Finset.mem_univ j))
    have hk' : ∀ j, (k j : ℚ) = ((b : ℤ) : ℚ) * q j := fun j => by
      simpa [Algebra.smul_def] using hk j
    have hkrel : ∀ w, ∑ j, k j * ((M (p j) w).toNat : ℤ) = 0 := by
      intro w
      have h : ((∑ j, k j * ((M (p j) w).toNat : ℤ) : ℤ) : ℚ) = 0 := by
        push_cast
        simp only [hk', mul_assoc, ← Finset.mul_sum, hq w, mul_zero]
      exact_mod_cast h
    have hki := K3 k hkrel i
    have hb0 : ((b : ℤ) : ℚ) ≠ 0 := by exact_mod_cast nonZeroDivisors.coe_ne_zero b
    have h2 := hk' i
    rw [hki, Int.cast_zero] at h2
    exact (mul_eq_zero.1 h2.symm).resolve_left hb0
  intro i
  have hq : ∀ ψ : Module.Dual ℚ ℂ, ∀ j, ψ (c j) = 0 := by
    intro ψ
    apply KQ (fun j => ψ (c j))
    intro w
    have h := congrArg ψ (hc w)
    rw [map_sum, map_zero] at h
    rw [← h]
    refine Finset.sum_congr rfl fun j _ => ?_
    show ψ (c j) * _ = ψ (c j * _)
    rw [mul_comm (c j), ← nsmul_eq_mul, map_nsmul, nsmul_eq_mul, mul_comm]
  exact (Module.forall_dual_apply_eq_zero_iff ℚ (c i)).1 fun ψ => hq ψ i

end GlobalTheory.ShuffleCount
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SimpleTensorProductOperatorStableCountable
section
open scoped TensorProduct

namespace GlobalTheory.TensHead

theorem exists_adjoin_agree {V : Type} [AddCommGroup V] [Module ℂ V] [Nontrivial V]
    (A : Set (Module.End ℂ V)) (hrank : Module.rank ℂ V ≤ Cardinal.aleph0)
    (hA : ∀ U : Submodule ℂ V, Stab A U → U = ⊥ ∨ U = ⊤) (p : Module.End ℂ V) (s : Finset V) :
    ∃ r ∈ Algebra.adjoin ℂ A, ∀ m ∈ s, p m = r m := by
  set R := Algebra.adjoin ℂ A with hR
  haveI : IsSimpleModule R V := by
    rw [isSimpleModule_iff]
    refine { eq_bot_or_eq_top := fun N => ?_ }
    have h := hA (N.restrictScalars ℂ) (fun g hg x hx =>
      N.smul_mem (⟨g, Algebra.subset_adjoin hg⟩ : R) hx)
    rcases h with h | h
    · left; exact (Submodule.restrictScalars_eq_bot_iff ℂ R V).1 h
    · right; exact (Submodule.restrictScalars_eq_top_iff ℂ R V).1 h
  have hsc : ∀ φ : Module.End R V, ∃ c : ℂ, ∀ x, φ x = c • x := by
    intro φ
    obtain ⟨c, hc⟩ := GlobalTheory.dixmier_schur_of_rank_le_aleph0 V A (fun g => g.1)
      (LinearMap.restrictScalars ℂ φ) inferInstance hrank
      (fun N hN => hA N (fun g hg x hx => hN ⟨g, hg⟩ x hx))
      (fun g => LinearMap.ext fun x =>
        φ.map_smul (⟨g.1, Algebra.subset_adjoin g.2⟩ : R) x)
    exact ⟨c, fun x => LinearMap.congr_fun hc x⟩
  let f : Module.End (Module.End R V) V :=
    { toFun := p
      map_add' := p.map_add
      map_smul' := fun φ x => by
        obtain ⟨c, hc⟩ := hsc φ
        change p (φ x) = φ (p x)
        rw [hc, hc, map_smul] }
  obtain ⟨r, hr⟩ := jacobson_density f s
  exact ⟨r.1, r.2, hr⟩

theorem simple_tensor :
    ∀ {S₀ S₁ : Type} [AddCommGroup S₀] [Module ℂ S₀] [AddCommGroup S₁] [Module ℂ S₁]
    (A : Set (Module.End ℂ S₀)) (B : Set (Module.End ℂ S₁)),
    Module.rank ℂ S₀ ≤ Cardinal.aleph0 →
    (∀ U : Submodule ℂ S₀, GlobalTheory.TensHead.Stab A U → U = ⊥ ∨ U = ⊤) →
    (∀ U : Submodule ℂ S₁, GlobalTheory.TensHead.Stab B U → U = ⊥ ∨ U = ⊤) →
    ∀ U : Submodule ℂ (S₀ ⊗[ℂ] S₁), GlobalTheory.TensHead.Stab (GlobalTheory.TensHead.tensOps A B) U →
      U = ⊥ ∨ U = ⊤ := by
  classical
  intro S₀ S₁ _ _ _ _ A B hrank hA hB U hU
  rcases eq_or_ne U ⊥ with h0 | h0
  · exact Or.inl h0
  right
  obtain ⟨t, htU, ht0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h0
  have hadj : ∀ r ∈ Algebra.adjoin ℂ A, ∀ z ∈ U, TensorProduct.map r LinearMap.id z ∈ U := by
    intro r hr
    induction hr using Algebra.adjoin_induction with
    | mem g hg => exact hU _ (Or.inl ⟨g, hg, rfl⟩)
    | algebraMap c =>
      intro z hz
      rw [Algebra.algebraMap_eq_smul_one, TensorProduct.map_smul_left, LinearMap.smul_apply,
        Module.End.one_eq_id, TensorProduct.map_id]
      exact U.smul_mem c hz
    | add f g _ _ hf hg =>
      intro z hz
      rw [TensorProduct.map_add_left]
      exact U.add_mem (hf z hz) (hg z hz)
    | mul f g _ _ hf hg =>
      intro z hz
      have : TensorProduct.map (f * g) (LinearMap.id : S₁ →ₗ[ℂ] S₁) =
          (TensorProduct.map f LinearMap.id) ∘ₗ (TensorProduct.map g LinearMap.id) := by
        rw [← TensorProduct.map_comp]; rfl
      rw [this]
      exact hf _ (hg z hz)
  let b := Module.Basis.ofVectorSpace ℂ S₀
  set c := TensorProduct.equivFinsuppOfBasisLeft b t with hc
  have ht : t = c.sum fun i n => b i ⊗ₜ[ℂ] n := by
    rw [hc, ← TensorProduct.equivFinsuppOfBasisLeft_symm_apply, LinearEquiv.symm_apply_apply]
  have hc0 : c ≠ 0 := by
    intro h
    apply ht0
    rw [ht, h, Finsupp.sum_zero_index]
  obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.2 hc0
  have hbi : b i ≠ 0 := b.ne_zero i
  haveI : Nontrivial S₀ := ⟨⟨b i, 0, hbi⟩⟩
  obtain ⟨r, hr, hrp⟩ := exists_adjoin_agree A hrank hA ((b.coord i).smulRight (b i))
    (c.support.image b)
  have h1 : b i ⊗ₜ[ℂ] c i ∈ U := by
    have h2 := hadj r hr t htU
    have h3 : TensorProduct.map r LinearMap.id t = b i ⊗ₜ[ℂ] c i := by
      conv_lhs => rw [ht]
      rw [Finsupp.sum, map_sum, Finset.sum_eq_single i]
      · rw [TensorProduct.map_tmul, ← hrp _ (Finset.mem_image_of_mem b hi)]
        simp
      · intro j hj hji
        rw [TensorProduct.map_tmul, ← hrp _ (Finset.mem_image_of_mem b hj)]
        simp [Finsupp.single_apply, hji]
      · intro h; exact absurd hi h
    rwa [h3] at h2
  have h4 : U.comap (TensorProduct.mk ℂ S₀ S₁ (b i)) = ⊤ := by
    refine (hB _ ?_).resolve_left ?_
    · intro g hg y hy
      exact hU _ (Or.inr ⟨g, hg, rfl⟩) _ hy
    · intro h
      have : c i ∈ U.comap (TensorProduct.mk ℂ S₀ S₁ (b i)) := h1
      rw [h, Submodule.mem_bot] at this
      exact Finsupp.mem_support_iff.1 hi this
  have h5 : ∀ y, U.comap ((TensorProduct.mk ℂ S₀ S₁).flip y) = ⊤ := by
    intro y
    refine (hA _ ?_).resolve_left ?_
    · intro g hg x hx
      exact hU _ (Or.inl ⟨g, hg, rfl⟩) _ hx
    · intro h
      have h6 : y ∈ U.comap (TensorProduct.mk ℂ S₀ S₁ (b i)) := by rw [h4]; trivial
      have : b i ∈ U.comap ((TensorProduct.mk ℂ S₀ S₁).flip y) := h6
      rw [h, Submodule.mem_bot] at this
      exact hbi this
  rw [eq_top_iff]
  rintro z -
  induction z using TensorProduct.induction_on with
  | zero => exact U.zero_mem
  | tmul x y =>
    have : x ∈ U.comap ((TensorProduct.mk ℂ S₀ S₁).flip y) := by rw [h5]; trivial
    exact this
  | add x y hx hy => exact U.add_mem hx hy

end GlobalTheory.TensHead
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmulInvariantMeasureShearedProductPairGroup
section
open MeasureTheory Function
open scoped Pointwise

namespace GlobalTheory.UnfoldNormal

theorem smulInvariantMeasure_shear_map (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [LocallyCompactSpace H] [SecondCountableTopology H] [T2Space H] [MeasurableSpace H] [BorelSpace H]
    (ν : Measure H) [ν.IsHaarMeasure] (Γ N : Subgroup H) (hNc : IsClosed (N : Set H))
    (hN : ∀ γ ∈ Γ, ∀ n ∈ N, γ * n * γ⁻¹ ∈ N) (κ : Measure N) (hκ : κ.IsHaarMeasure)
    (hconj : ∀ (γ : H) (hγ : γ ∈ Γ), κ.map (fun n : N => (⟨γ * n * γ⁻¹, hN γ hγ n n.2⟩ : N)) = κ) :
    SMulInvariantMeasure (pairGroup Γ N hN) (H × H) ((κ.prod ν).map (shear N)) := by
  haveI : LocallyCompactSpace N := hNc.locallyCompactSpace
  haveI : SecondCountableTopology N := TopologicalSpace.Subtype.secondCountableTopology (N : Set H)
  haveI : SigmaFinite κ := inferInstance
  refine ⟨fun g s hs => ?_⟩
  obtain ⟨⟨u, v⟩, hu, hv, huv⟩ := g
  have hmeasg : Measurable (fun x : H × H => ((⟨(u, v), hu, hv, huv⟩ : pairGroup Γ N hN)) • x) := by
    change Measurable (fun x : H × H => (u * x.1, v * x.2))
    exact (measurable_fst.const_mul u).prodMk (measurable_snd.const_mul v)
  let δ : N := ⟨u * v⁻¹, huv⟩
  let c : N → N := fun n => ⟨v * n * v⁻¹, hN v hv n n.2⟩
  have hc : MeasurePreserving c κ κ :=
    ⟨(show Continuous c from ((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _).measurable,
      hconj v hv⟩
  have hf : MeasurePreserving (fun n : N => δ * c n) κ κ := (measurePreserving_mul_left κ δ).comp hc
  have hT : MeasurePreserving (Prod.map (fun n : N => δ * c n) (fun h : H => v * h)) (κ.prod ν) (κ.prod ν) :=
    hf.prod (measurePreserving_mul_left ν v)
  have hsh := (measurableEmbedding_shear (N := N) hNc)
  have key : (fun x : H × H => ((⟨(u, v), hu, hv, huv⟩ : pairGroup Γ N hN)) • x) ∘ shear N
      = shear N ∘ Prod.map (fun n : N => δ * c n) (fun h : H => v * h) := by
    funext p
    change (u * (p.1 * p.2), v * p.2) = (((u * v⁻¹) * (v * p.1 * v⁻¹)) * (v * p.2), v * p.2)
    congr 1
    group
  rw [← Measure.map_apply hmeasg hs, Measure.map_map hmeasg hsh.measurable, key,
    ← Measure.map_map hsh.measurable hT.measurable, hT.map_eq]

end GlobalTheory.UnfoldNormal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SubmodulePowSimpleEqSumEquivValuesStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_sum_intertwined_of_mem_invariant_submodule : ∀ {P : Type} [AddCommGroup P] [Module ℂ P] {ι : Type} (a : ι → Module.End ℂ P),
    (∀ B : Submodule ℂ P, (∀ i, ∀ p ∈ B, a i p ∈ B) → B ≠ ⊥ → B = ⊤) →
    ∀ (m : ℕ) (N : Submodule ℂ (Fin m → P)), (∀ i, ∀ y ∈ N, (fun j => a i (y j)) ∈ N) →
    ∀ y ∈ N, ∃ (n : ℕ) (Sm : Fin n → (P →ₗ[ℂ] (Fin m → P))) (q : Fin n → P),
      (∀ l i p, Sm l (a i p) = fun j => a i (Sm l p j)) ∧ (∀ l p, Sm l p ∈ N) ∧ y = ∑ l, Sm l (q l) := by
  first | exact @GlobalTheory.submodule_pow_simple_eq_sum_equiv_values | exact GlobalTheory.submodule_pow_simple_eq_sum_equiv_values | (intros; apply GlobalTheory.submodule_pow_simple_eq_sum_equiv_values <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SumProdUpdateRegroupStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_prod_update_regroup_of_update_eq : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] {X : ι → Type} {W : ι → Type}
    [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    {m : ι → ℕ} (k : ∀ i, Fin (m i) → X i) (ℓ : ∀ i, Fin (m i) → W i →ₗ[ℂ] ℂ) (i₀ : ι)
    (F F' : (∀ i, X i) → ℂ) (w w' : W i₀)
    (hone : ∀ J : (∀ i, Fin (m i)), ∑ j, ℓ i₀ j w' * F (Function.update (fun i => k i (J i)) i₀ (k i₀ j)) =
      ∑ j, ℓ i₀ j w * F' (Function.update (fun i => k i (J i)) i₀ (k i₀ j)))
    (v : ∀ i, W i), ∑ J : (∀ i, Fin (m i)), (∏ i, ℓ i (J i) (Function.update v i₀ w' i)) * F (fun i => k i (J i)) =
    ∑ J : (∀ i, Fin (m i)), (∏ i, ℓ i (J i) (Function.update v i₀ w i)) * F' (fun i => k i (J i)) := by
  first | exact @GlobalTheory.sum_prod_update_regroup | exact GlobalTheory.sum_prod_update_regroup | (intros; apply GlobalTheory.sum_prod_update_regroup <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SummableNormCosetOutStatement
section
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.summable_norm_coset_out' : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsMulLeftInvariant] (K : Subgroup G), IsOpen (K : Set G) → μ K = 1 → ∀ F : G → ℂ, (∀ g, ∀ k ∈ K, F (g * k) = F g) → Integrable F μ → Summable (fun x : G ⧸ K => ‖F x.out‖) := by
  first | exact @GlobalTheory.summable_norm_coset_out | exact GlobalTheory.summable_norm_coset_out | (intros; apply GlobalTheory.summable_norm_coset_out <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TraceMatrixPiOperatorStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trace_sum_single_comp_proj_eq : ∀ (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (m : ℕ)
    (h : Matrix (Fin m) (Fin m) ℂ) (A : W →ₗ[ℂ] W),
    LinearMap.trace ℂ (Fin m → W) (∑ k, ∑ j, h k j • (LinearMap.single ℂ (fun _ : Fin m => W) k ∘ₗ A ∘ₗ
      LinearMap.proj j)) = h.trace * LinearMap.trace ℂ W A := by
  first | exact @GlobalTheory.trace_matrix_pi_operator | exact GlobalTheory.trace_matrix_pi_operator | (intros; apply GlobalTheory.trace_matrix_pi_operator <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TsumSetIntegralFundamentalDomainEqZeroByOrbitsStatement
section
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tsum_setIntegral_fundamentalDomain_eq_zero_by_orbits : ∀ (H : Type) [Group H] [MeasurableSpace H] [MeasurableMul H] (ν : Measure H) [ν.IsMulLeftInvariant] (Γ : Subgroup H) [Countable Γ] (Y : Type) [Countable Y] [MulAction Γ Y] (𝓕 : Set H), IsFundamentalDomain Γ 𝓕 ν → ∀ Φ : Y → H → ℂ, (∀ y, Measurable (Φ y)) → (∀ (γ : Γ) y h, Φ (γ • y) ((γ : H) * h) = Φ y h) → ∑' y, ∫⁻ h in 𝓕, ‖Φ y h‖ₑ ∂ν ≠ ⊤ → (∀ y (𝓖 : Set H), IsFundamentalDomain ((MulAction.stabilizer Γ y).map Γ.subtype) 𝓖 ν → IntegrableOn (Φ y) 𝓖 ν → ∫ h in 𝓖, Φ y h ∂ν = 0) → ∑' y, ∫ h in 𝓕, Φ y h ∂ν = 0 := by
  first | exact @GlobalTheory.OrbitUnfold.tsum_setIntegral_eq_zero | exact GlobalTheory.OrbitUnfold.tsum_setIntegral_eq_zero | (intros; apply GlobalTheory.OrbitUnfold.tsum_setIntegral_eq_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnfoldIntegralFundamentalDomainStatement
section
open MeasureTheory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_eq_setIntegral_tsum_of_fundamentalDomain : ∀ (G : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (Γ : AddSubgroup G) [Countable Γ] (μ : Measure G), μ.IsAddLeftInvariant → ∀ 𝓕 : Set G, IsAddFundamentalDomain Γ 𝓕 μ → ∀ c g : G → ℂ, Integrable c μ → Continuous g → (∃ B : ℝ, ∀ w, ‖g w‖ ≤ B) → ∫ w, c w * g w ∂μ = ∫ w in 𝓕, ∑' γ : Γ, c ((γ : G) + w) * g ((γ : G) + w) ∂μ := by
  first | exact @GlobalTheory.unfold_integral_fundamentalDomain | exact GlobalTheory.unfold_integral_fundamentalDomain | (intros; apply GlobalTheory.unfold_integral_fundamentalDomain <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnfoldTsumAlongSubgroupStatement
section
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integrableOn_and_hasSum_tsum_subgroup : ∀ (G H : Type) [Group G] [Group H] [MeasurableSpace H] [MeasurableMul H] (ν : Measure H) [ν.IsMulLeftInvariant] (ι : H →* G), Function.Injective ι → ∀ (Γ : Subgroup G) [Countable Γ] (𝓕 : Set H), IsFundamentalDomain (Γ.comap ι) 𝓕 ν → ∀ (f : G → ℂ) (φ : H → ℂ), (∀ γ : G, Measurable fun h => f (γ * ι h)) → Measurable φ → (∀ γ ∈ Γ.comap ι, ∀ h, φ (γ * h) = φ h) → (∑' q : Γ ⧸ ι.range.subgroupOf Γ, ∫⁻ h, ‖f ((q.out : Γ) * ι h) * φ h‖ₑ ∂ν) ≠ ⊤ → IntegrableOn (fun h => (∑' γ : Γ, f (γ * ι h)) * φ h) 𝓕 ν ∧ HasSum (fun q : Γ ⧸ ι.range.subgroupOf Γ => ∫ h, f ((q.out : Γ) * ι h) * φ h ∂ν) (∫ h in 𝓕, (∑' γ : Γ, f (γ * ι h)) * φ h ∂ν) := by
  first | exact @GlobalTheory.unfold_tsum_along_subgroup | exact GlobalTheory.unfold_tsum_along_subgroup | (intros; apply GlobalTheory.unfold_tsum_along_subgroup <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryExistsSkewLogStatement
section
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_skewHermitian_log_of_unitary : ∀ (n : ℕ) (k : Matrix (Fin n) (Fin n) ℂ), kᴴ * k = 1 → ∃ (X : Matrix (Fin n) (Fin n) ℂ) (p : Polynomial ℂ), Xᴴ = -X ∧ NormedSpace.exp X = k ∧ X = Polynomial.aeval k p := by
  first | exact @GlobalTheory.unitary_exists_skew_log | exact GlobalTheory.unitary_exists_skew_log | (intros; apply GlobalTheory.unitary_exists_skew_log <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeylNumberOperatorCommutationStatement
section
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weyl_number_operator_commutation_alt : ∀ (V A κ : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Ring A] [Algebra ℂ A] [Fintype κ] (J : V ≃ₗᵢ[ℝ] V) (e : OrthonormalBasis κ ℝ V) (D a c : V → A) (N : A), (∀ x, J (J x) = -x) → (∀ u v, D (u + v) = D u + D v) → (∀ (r : ℝ) v, D (r • v) = (r : ℂ) • D v) → (∀ u v, D u * D v - D v * D u = (2 * Real.pi * Complex.I * (inner ℝ u (J v) : ℝ) : ℂ) • 1) → (∀ z, c z = D z - Complex.I • D (J z)) → (∀ z, a z = -(D z + Complex.I • D (J z))) → N = ∑ j, c (e j) * a (e j) → (∀ z, a z * c z - c z * a z = ((4 * Real.pi * ‖z‖ ^ 2 : ℝ) : ℂ) • 1) ∧ (∀ z, N * c z = c z * (N + ((8 * Real.pi : ℝ) : ℂ) • 1)) ∧ (∀ z, N * a z = a z * (N - ((8 * Real.pi : ℝ) : ℂ) • 1)) ∧ ∀ z, D z ∈ Submodule.span ℂ (Set.range (fun j => a (e j)) ∪ Set.range fun j => c (e j)) := by
  first | exact @GlobalTheory.weyl_number_operator_commutation | exact GlobalTheory.weyl_number_operator_commutation | (intros; apply GlobalTheory.weyl_number_operator_commutation <;> assumption)
end

