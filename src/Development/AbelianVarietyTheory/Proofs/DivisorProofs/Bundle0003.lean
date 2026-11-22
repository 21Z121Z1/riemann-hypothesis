import Mathlib

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraMapEqMk
section
open scoped TensorProduct

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.KummerAlg

open MvPolynomial

variable {B : Type} [CommRing B] {L : Type} [AddCommGroup L] [Module B L] {q : ℕ}

def rels (φ : MultilinearMap B (fun _ : Fin q => L) B) : Set (MvPolynomial L B) :=
  Set.range (fun p : L × L => X (p.1 + p.2) - X p.1 - X p.2) ∪
  Set.range (fun p : B × L => X (p.1 • p.2) - C p.1 * X p.2) ∪
  Set.range (fun ℓ : Fin q → L => ∏ i, X (ℓ i) - C (φ ℓ))

def ideal (φ : MultilinearMap B (fun _ : Fin q => L) B) : Ideal (MvPolynomial L B) :=
  Ideal.span (rels φ)

abbrev Alg (φ : MultilinearMap B (fun _ : Fin q => L) B) : Type :=
  MvPolynomial L B ⧸ ideal φ

variable (φ : MultilinearMap B (fun _ : Fin q => L) B)

theorem algebraMap_eq_mk (c : B) : algebraMap B (Alg φ) c = Ideal.Quotient.mk _ (C c) := rfl

theorem add_mem (a b : L) : X (a + b) - X a - X b ∈ ideal φ :=
  Ideal.subset_span (Or.inl (Or.inl ⟨(a, b), rfl⟩))

theorem smul_mem (c : B) (a : L) : X (c • a) - C c * X a ∈ ideal φ :=
  Ideal.subset_span (Or.inl (Or.inr ⟨(c, a), rfl⟩))

theorem prod_mem (ℓ : Fin q → L) : ∏ i, X (ℓ i) - C (φ ℓ) ∈ ideal φ :=
  Ideal.subset_span (Or.inr ⟨ℓ, rfl⟩)

def gen : L →ₗ[B] Alg φ where
  toFun ℓ := Ideal.Quotient.mk _ (X ℓ)
  map_add' a b := by
    rw [← sub_eq_zero, sub_add_eq_sub_sub, ← map_sub, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
    exact add_mem φ a b
  map_smul' c a := by
    rw [← sub_eq_zero, RingHom.id_apply, Algebra.smul_def, algebraMap_eq_mk,
      ← map_mul, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
    exact smul_mem φ c a

theorem gen_apply (ℓ : L) : gen φ ℓ = Ideal.Quotient.mk _ (X ℓ) := rfl

theorem prod_gen (ℓ : Fin q → L) : ∏ i, gen φ (ℓ i) = algebraMap B (Alg φ) (φ ℓ) := by
  rw [← sub_eq_zero]
  simp only [gen_apply, ← map_prod, algebraMap_eq_mk]
  rw [← map_sub, Ideal.Quotient.eq_zero_iff_mem]
  exact prod_mem φ ℓ

def scalePoly (t : B) : MvPolynomial L B →ₐ[B] MvPolynomial L B := aeval fun ℓ => C t * X ℓ

theorem scalePoly_X (t : B) (ℓ : L) : scalePoly t (X ℓ) = C t * X ℓ := by simp [scalePoly]

theorem scalePoly_C (t c : B) : scalePoly (L := L) t (C c) = C c := by
  simp [scalePoly, aeval_C, MvPolynomial.algebraMap_eq]

theorem le_comap_scale (t : B) (ht : t ^ q = 1) : ideal φ ≤ (ideal φ).comap (scalePoly t) := by
  rw [ideal, Ideal.span_le]
  rintro r ((⟨⟨a, b⟩, rfl⟩ | ⟨⟨c, a⟩, rfl⟩) | ⟨ℓ, rfl⟩)
  · change scalePoly t _ ∈ ideal φ
    have : scalePoly t (X (a + b) - X a - X b) = C t * (X (a + b) - X a - X b) := by
      simp only [map_sub, scalePoly_X]; ring
    rw [this]; exact Ideal.mul_mem_left _ _ (add_mem φ a b)
  · change scalePoly t _ ∈ ideal φ
    have : scalePoly t (X (c • a) - C c * X a) = C t * (X (c • a) - C c * X a) := by
      simp only [map_sub, map_mul, scalePoly_X, scalePoly_C]; ring
    rw [this]; exact Ideal.mul_mem_left _ _ (smul_mem φ c a)
  · change scalePoly t _ ∈ ideal φ
    have : scalePoly t (∏ i, X (ℓ i) - C (φ ℓ)) = ∏ i, X (ℓ i) - C (φ ℓ) := by
      simp only [map_sub, map_prod, scalePoly_X, scalePoly_C, Finset.prod_mul_distrib,
        Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← map_pow, ht, map_one, one_mul]
    rw [this]; exact prod_mem φ ℓ

def scale (t : B) (ht : t ^ q = 1) : Alg φ →ₐ[B] Alg φ :=
  Ideal.quotientMapₐ (ideal φ) (scalePoly t) (le_comap_scale φ t ht)

theorem scale_mk (t : B) (ht : t ^ q = 1) (p : MvPolynomial L B) :
    scale φ t ht (Ideal.Quotient.mk _ p) = Ideal.Quotient.mk _ (scalePoly t p) := rfl

theorem scale_gen (t : B) (ht : t ^ q = 1) (ℓ : L) : scale φ t ht (gen φ ℓ) = t • gen φ ℓ := by
  rw [gen_apply, scale_mk, scalePoly_X, map_mul, Algebra.smul_def, algebraMap_eq_mk]

theorem scale_ext {f g : Alg φ →ₐ[B] Alg φ} (h : ∀ ℓ, f (gen φ ℓ) = g (gen φ ℓ)) : f = g :=
  Ideal.Quotient.algHom_ext B (MvPolynomial.algHom_ext fun ℓ => h ℓ)

theorem scale_comp (s t : B) (hs : s ^ q = 1) (ht : t ^ q = 1) :
    (scale φ s hs).comp (scale φ t ht) = scale φ (s * t) (by rw [mul_pow, hs, ht, one_mul]) :=
  scale_ext φ fun ℓ => by
    rw [AlgHom.comp_apply, scale_gen, map_smul, scale_gen, scale_gen, smul_smul, mul_comm]

theorem scale_eq_id (t : B) (ht : t ^ q = 1) (h1 : t = 1) : scale φ t ht = AlgHom.id B (Alg φ) :=
  scale_ext φ fun ℓ => by rw [scale_gen, h1, one_smul, AlgHom.id_apply]

theorem scale_congr (s t : B) (hs : s ^ q = 1) (ht : t ^ q = 1) (h : s = t) :
    scale φ s hs = scale φ t ht := by subst h; rfl

def tw (ζ : B) (g : ZMod q) : B := ζ ^ g.val

theorem tw_add [NeZero q] {ζ : B} (hζ : ζ ^ q = 1) (g h : ZMod q) :
    tw ζ (g + h) = tw ζ g * tw ζ h := by
  rw [tw, tw, tw, ZMod.val_add, ← pow_add]
  conv_rhs => rw [← Nat.mod_add_div (g.val + h.val) q, pow_add, pow_mul, hζ, one_pow, mul_one]

theorem tw_pow {ζ : B} (hζ : ζ ^ q = 1) (g : ZMod q) : tw ζ g ^ q = 1 := by
  rw [tw, ← pow_mul, mul_comm, pow_mul, hζ, one_pow]

theorem tw_zero (ζ : B) : tw ζ (0 : ZMod q) = 1 := by simp [tw]

theorem tw_mul_tw_neg [NeZero q] {ζ : B} (hζ : ζ ^ q = 1) (g : ZMod q) :
    tw ζ g * tw ζ (-g) = 1 := by rw [← tw_add hζ, add_neg_cancel, tw_zero]

def act [NeZero q] (ζ : B) (hζ : ζ ^ q = 1) : Multiplicative (ZMod q) →* (Alg φ ≃ₐ[B] Alg φ) where
  toFun g := AlgEquiv.ofAlgHom (scale φ (tw ζ g.toAdd) (tw_pow hζ _))
    (scale φ (tw ζ (-g.toAdd)) (tw_pow hζ _))
    (by rw [scale_comp]; exact scale_eq_id φ _ _ (tw_mul_tw_neg hζ _))
    (by rw [scale_comp]; exact scale_eq_id φ _ _ (by rw [mul_comm]; exact tw_mul_tw_neg hζ _))
  map_one' := AlgEquiv.ext fun x => by
    change scale φ (tw ζ (0 : ZMod q)) (tw_pow hζ 0) x = x
    rw [scale_eq_id φ _ _ (tw_zero ζ)]; rfl
  map_mul' g h := AlgEquiv.ext fun x => by
    change scale φ (tw ζ (g.toAdd + h.toAdd)) (tw_pow hζ _) x =
      scale φ (tw ζ g.toAdd) (tw_pow hζ _) (scale φ (tw ζ h.toAdd) (tw_pow hζ _) x)
    rw [← AlgHom.comp_apply, scale_comp]
    exact DFunLike.congr_fun (scale_congr φ _ _ _ _ (tw_add hζ _ _)) x

theorem act_gen [NeZero q] (ζ : B) (hζ : ζ ^ q = 1) (g : ZMod q) (ℓ : L) :
    act φ ζ hζ (Multiplicative.ofAdd g) (gen φ ℓ) = ζ ^ g.val • gen φ ℓ :=
  scale_gen φ _ (tw_pow hζ _) ℓ

end GlobalTheory.KummerAlg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraMapNormMemSpan
section
open Polynomial

namespace GlobalTheory.PicDiv.SquarefreeFibre

theorem algebraMap_norm_mem_span {R S : Type} [CommRing R] [CommRing S] [Algebra R S]
    [Module.Free R S] [Module.Finite R S] (g : S) :
    algebraMap R S (Algebra.norm R g) ∈ Ideal.span {g} := by
  set p := LinearMap.charpoly (Algebra.lmul R S g) with hp
  have h1 : aeval g p = 0 := by
    have h2 := congrArg (fun φ : Module.End R S => φ 1) (LinearMap.aeval_self_charpoly (Algebra.lmul R S g))
    rw [← hp, Polynomial.aeval_algHom_apply (Algebra.lmul R S) g p] at h2
    simpa using h2
  have h3 : algebraMap R S (p.coeff 0) = -(g * aeval g p.divX) := by
    have h4 := X_mul_divX_add p
    rw [← h4] at h1
    simp only [map_add, map_mul, aeval_X, aeval_C] at h1
    linear_combination h1
  rw [Algebra.norm_apply, LinearMap.det_eq_sign_charpoly_coeff, map_mul, ← hp, h3]
  exact Ideal.mul_mem_left _ _ ((Ideal.span {g}).neg_mem
    (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self g)))

theorem main : ∀ (k A : Type) [Field k] [IsAlgClosed k] [CommRing A] [IsDedekindDomain A] [Algebra k A] [Algebra k[X] A] [IsScalarTower k k[X] A] [Module.Finite k[X] A] [Module.Free k[X] A], (∃ δ : k[X], δ ≠ 0 ∧ ∀ α : k, δ.eval α ≠ 0 → ∀ Q : Ideal A, Q.IsMaximal → algebraMap k[X] A (X - C α) ∉ Q ^ 2) → ∀ (g : A) (s : ℕ), g ≠ 0 → ∃ (q : k[X]) (r : ℕ) (Q : Fin r → Ideal A), q.Monic ∧ q.natDegree = s ∧ (∀ i, (Q i).IsMaximal) ∧ Function.Injective Q ∧ (∀ i, g ∉ Q i) ∧ Ideal.span {algebraMap k[X] A q} = ∏ i, Q i := by
  intro k A _ _ _ _ _ _ _ _ _ hred g s hg
  classical
  obtain ⟨δ, hδ0, hδ⟩ := hred
  set u := algebraMap k[X] A with hu
  set N := Algebra.norm k[X] g with hNdef
  have hN : N ≠ 0 := Algebra.norm_ne_zero_iff.mpr hg
  have hinj : Function.Injective u := FaithfulSMul.algebraMap_injective k[X] A
  have huC : ∀ c : k, u (C c) = algebraMap k A c := by
    intro c
    rw [IsScalarTower.algebraMap_apply k k[X] A c, Polynomial.algebraMap_eq]

  have hCnot : ∀ (P : Ideal A), P.IsPrime → ∀ c : k, c ≠ 0 → u (C c) ∉ P := by
    intro P hP c hc hmem
    rw [huC] at hmem
    exact hP.ne_top (Ideal.eq_top_of_isUnit_mem _ hmem ((Ne.isUnit hc).map (algebraMap k A)))

  have hgnot : ∀ (P : Ideal A), P.IsPrime → ∀ α : k, N.eval α ≠ 0 → u (X - C α) ∈ P → g ∉ P := by
    intro P hP α hα hX hgP
    have hNP : u N ∈ P := (Ideal.span_singleton_le_iff_mem P).mpr hgP (algebraMap_norm_mem_span g)
    have hdec := modByMonic_add_div N (X - C α)
    rw [modByMonic_X_sub_C_eq_C_eval] at hdec
    have h5 : C (N.eval α) = N - (X - C α) * (N /ₘ (X - C α)) := eq_sub_of_add_eq hdec
    have : u (C (N.eval α)) = u N - u (X - C α) * u (N /ₘ (X - C α)) := by
      rw [h5, map_sub, map_mul]
    exact hCnot P hP _ hα (this ▸ P.sub_mem hNP (P.mul_mem_right _ hX))

  have hδN : δ * N ≠ 0 := mul_ne_zero hδ0 hN
  have hfin : {a : k | (δ * N).eval a = 0}.Finite :=
    ((δ * N).roots.toFinset.finite_toSet).subset (fun a ha => by
      simp only [Set.mem_setOf_eq] at ha
      simp [Polynomial.mem_roots hδN, ha])
  have hinf : {a : k | (δ * N).eval a ≠ 0}.Infinite := by
    have := hfin.infinite_compl
    simpa [Set.compl_setOf] using this
  obtain ⟨F, hFS, hFcard⟩ := hinf.exists_subset_card_eq s
  have hF : ∀ a ∈ F, δ.eval a ≠ 0 ∧ N.eval a ≠ 0 := by
    intro a ha
    have := hFS ha
    simp only [Set.mem_setOf_eq, eval_mul] at this
    exact ⟨left_ne_zero_of_mul this, right_ne_zero_of_mul this⟩
  set q : k[X] := ∏ a ∈ F, (X - C a) with hq
  have hqm : q.Monic := monic_prod_of_monic _ _ (fun a _ => monic_X_sub_C a)
  have hqdeg : q.natDegree = s := by
    rw [hq, natDegree_prod_of_monic _ _ (fun a _ => monic_X_sub_C a)]
    simp [hFcard]

  have hone : ∀ (P : Ideal A), P.IsPrime → u q ∈ P → ∃ a ∈ F, u (X - C a) ∈ P := by
    intro P hP hqP
    rw [hq, map_prod] at hqP
    exact Ideal.IsPrime.prod_mem_iff.mp hqP
  have huniq : ∀ (P : Ideal A), P.IsPrime → ∀ a b : k, u (X - C a) ∈ P → u (X - C b) ∈ P → a = b := by
    intro P hP a b ha hb
    by_contra hab
    have : u (C (b - a)) = u (X - C a) - u (X - C b) := by
      rw [← map_sub]; congr 1; simp [C_sub]
    exact hCnot P hP (b - a) (sub_ne_zero.mpr (Ne.symm hab)) (this ▸ P.sub_mem ha hb)
  have hnotsq : ∀ (P : Ideal A), P.IsMaximal → u q ∉ P ^ 2 := by
    intro P hPm hq2
    have hP : P.IsPrime := hPm.isPrime
    obtain ⟨a, haF, haP⟩ := hone P hP (Ideal.pow_le_self two_ne_zero hq2)
    have hsplit : q = (∏ b ∈ F.erase a, (X - C b)) * (X - C a) := by
      rw [hq, mul_comm, Finset.mul_prod_erase F (fun b => X - C b) haF]
    rw [hsplit, map_mul] at hq2
    rcases Ideal.IsPrime.mul_mem_pow P hq2 with hrest | hX2
    · rw [map_prod] at hrest
      obtain ⟨b, hbF, hbP⟩ := Ideal.IsPrime.prod_mem_iff.mp hrest
      exact (Finset.ne_of_mem_erase hbF) (huniq P hP b a hbP haP)
    · exact hδ a (hF a haF).1 P hPm hX2

  set I : Ideal A := Ideal.span {u q} with hI
  have hI0 : I ≠ ⊥ := by
    rw [hI, Ne, Ideal.span_singleton_eq_bot]
    exact fun h => hqm.ne_zero (hinj (h.trans (map_zero u).symm))
  have hsq : Squarefree I := by
    intro J hJ
    by_contra hJu
    have hJtop : J ≠ ⊤ := fun h => hJu (Ideal.isUnit_iff.mpr h)
    obtain ⟨P, hPm, hJP⟩ := Ideal.exists_le_maximal J hJtop
    have hle : I ≤ P ^ 2 := (Ideal.le_of_dvd hJ).trans (by rw [pow_two]; exact Ideal.mul_mono hJP hJP)
    exact hnotsq P hPm (hle (Ideal.mem_span_singleton_self _))
  have hnodup := (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hI0).mp hsq
  set M := UniqueFactorizationMonoid.normalizedFactors I with hM
  have hmem : ∀ P ∈ M, P.IsMaximal ∧ g ∉ P := by
    intro P hPM
    have hPp : P.IsPrime := Ideal.isPrime_of_prime (UniqueFactorizationMonoid.prime_of_normalized_factor P hPM)
    have hPne : P ≠ ⊥ := UniqueFactorizationMonoid.ne_zero_of_mem_normalizedFactors hPM
    refine ⟨hPp.isMaximal hPne, ?_⟩
    have hqP : u q ∈ P := Ideal.le_of_dvd (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hPM)
      (Ideal.mem_span_singleton_self _)
    obtain ⟨a, haF, haP⟩ := hone P hPp hqP
    exact hgnot P hPp a (hF a haF).2 haP
  let e := M.toFinset.equivFin
  refine ⟨q, M.toFinset.card, fun i => (e.symm i : Ideal A), hqm, hqdeg, ?_, ?_, ?_, ?_⟩
  · intro i; exact (hmem _ (Multiset.mem_toFinset.mp (e.symm i).2)).1
  · intro i j h; exact e.symm.injective (Subtype.ext h)
  · intro i; exact (hmem _ (Multiset.mem_toFinset.mp (e.symm i).2)).2
  · rw [Fintype.prod_equiv e.symm (fun i => (e.symm i : Ideal A)) (fun x => (x : Ideal A)) (fun _ => rfl),
      Finset.prod_coe_sort M.toFinset (fun x => x), Finset.prod_eq_multiset_prod, Multiset.toFinset_val,
      hnodup.dedup, Multiset.map_id', hM, ← hI]
    exact (Ideal.prod_normalizedFactors_eq_self hI0).symm

end GlobalTheory.PicDiv.SquarefreeFibre
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlternatingFormLatticeIntegrality
section
open NumberField
open scoped nonZeroDivisors

namespace GlobalTheory

theorem alternating_pairing_expand {F V : Type} [Field F] [NumberField F] [AddCommGroup V]
    [Module F V] (L : Set V)
    (hadd : ∀ x ∈ L, ∀ x' ∈ L, x + x' ∈ L) (hsm : ∀ (a : 𝓞 F), ∀ x ∈ L, (a : F) • x ∈ L)
    (Q : V → V → F)
    (halt : ∀ x ∈ L, ∀ x' ∈ L, Q x x' = -Q x' x)
    (hQadd : ∀ x₁ ∈ L, ∀ x₂ ∈ L, ∀ x' ∈ L, Q (x₁ + x₂) x' = Q x₁ x' + Q x₂ x')
    (hQsmul : ∀ (a : 𝓞 F), ∀ x ∈ L, ∀ x' ∈ L, Q ((a : F) • x) x' = (a : F) * Q x x')
    {x x' : V} (hx : x ∈ L) (hx' : x' ∈ L) (r₀ r₁ s₀ s₁ : 𝓞 F) :
    Q ((r₀ : F) • x + (r₁ : F) • x') ((s₀ : F) • x + (s₁ : F) • x') =
      ((r₀ : F) * s₁ - (r₁ : F) * s₀) * Q x x' := by
  have hself : ∀ y ∈ L, Q y y = 0 := by
    intro y hy
    have h := halt y hy y hy
    have h2 : (2 : F) * Q y y = 0 := by linear_combination h
    rcases mul_eq_zero.mp h2 with h | h
    · exact absurd h two_ne_zero
    · exact h
  have hadd2 : ∀ y ∈ L, ∀ y₁ ∈ L, ∀ y₂ ∈ L, Q y (y₁ + y₂) = Q y y₁ + Q y y₂ := by
    intro y hy y₁ hy₁ y₂ hy₂
    have e1 := halt y hy _ (hadd _ hy₁ _ hy₂)
    have e2 := hQadd _ hy₁ _ hy₂ _ hy
    have e3 := halt y hy y₁ hy₁
    have e4 := halt y hy y₂ hy₂
    linear_combination e1 - e2 - e3 - e4
  have hsmul2 : ∀ y ∈ L, ∀ (a : 𝓞 F), ∀ y' ∈ L, Q y ((a : F) • y') = (a : F) * Q y y' := by
    intro y hy a y' hy'
    have e1 := halt y hy _ (hsm a y' hy')
    have e2 := hQsmul a y' hy' y hy
    have e3 := halt y hy y' hy'
    linear_combination e1 - e2 - (a : F) * e3
  have hu := hsm r₀ x hx
  have hv := hsm r₁ x' hx'
  have hp := hsm s₀ x hx
  have hq := hsm s₁ x' hx'
  rw [hQadd _ hu _ hv _ (hadd _ hp _ hq), hadd2 _ hu _ hp _ hq, hadd2 _ hv _ hp _ hq,
    hQsmul r₀ x hx _ hp, hQsmul r₀ x hx _ hq, hQsmul r₁ x' hx' _ hp, hQsmul r₁ x' hx' _ hq,
    hsmul2 x hx s₀ x hx, hsmul2 x hx s₁ x' hx', hsmul2 x' hx' s₀ x hx, hsmul2 x' hx' s₁ x' hx',
    hself x hx, hself x' hx', halt x' hx' x hx]
  ring

theorem exists_int_of_isInteger_smul {F : Type} [Field F] [NumberField F] (d : 𝓞 F) (y : F)
    (h : IsLocalization.IsInteger (𝓞 F) (d • y)) : ∃ n : 𝓞 F, (n : F) = (d : F) * y := by
  obtain ⟨n, hn⟩ := h
  refine ⟨n, ?_⟩
  rw [RingOfIntegers.coe_eq_algebraMap, hn, Algebra.smul_def, ← RingOfIntegers.coe_eq_algebraMap]

theorem exists_alternating_bilinForm_eq_pairing : ∀ {F V : Type} [Field F] [NumberField F]
    [AddCommGroup V] [Module F V], Module.finrank F V = 2 → ∀ (L : Set V),
    (∀ x ∈ L, ∀ x' ∈ L, x + x' ∈ L) → (∀ (a : 𝓞 F), ∀ x ∈ L, (a : F) • x ∈ L) → ∀ (P : V → V → F),
    (∀ x ∈ L, ∀ x' ∈ L, P x x' = -P x' x) →
    (∀ x₁ ∈ L, ∀ x₂ ∈ L, ∀ x' ∈ L, P (x₁ + x₂) x' = P x₁ x' + P x₂ x') →
    (∀ (a : 𝓞 F), ∀ x ∈ L, ∀ x' ∈ L, P ((a : F) • x) x' = (a : F) * P x x') →
    ∀ {x x' : V}, x ∈ L → x' ∈ L → P x x' ≠ 0 →
    ∃ B : LinearMap.BilinForm F V, (∀ z, B z z = 0) ∧ ∀ z ∈ L, ∀ w ∈ L, P z w = B z w := by
  intro F V _ _ _ _ hfin L hadd hsm P halt hPadd hPsmul x x' hx hx' hne
  have hP0 : ∀ y ∈ L, P 0 y = 0 := by
    intro y hy
    simpa using hPsmul 0 x hx y hy
  have hP0' : ∀ y ∈ L, P y 0 = 0 := by
    intro y hy
    have h0 : (0 : V) ∈ L := by simpa using hsm 0 x hx
    rw [halt y hy 0 h0, hP0 y hy, neg_zero]
  have hdne : ∀ d : (𝓞 F)⁰, ((d : 𝓞 F) : F) ≠ 0 := by
    intro d
    exact_mod_cast nonZeroDivisors.coe_ne_zero d
  have hli : LinearIndependent F ![x, x'] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (𝓞 F)⁰ ![s, t]
    obtain ⟨n₀, hn₀⟩ := exists_int_of_isInteger_smul (d : 𝓞 F) s (hd 0)
    obtain ⟨n₁, hn₁⟩ := exists_int_of_isInteger_smul (d : 𝓞 F) t (hd 1)
    have hrel : (n₀ : F) • x + (n₁ : F) • x' = 0 := by
      rw [hn₀, hn₁, ← smul_smul, ← smul_smul, ← smul_add, hst, smul_zero]
    have e₀ := alternating_pairing_expand L hadd hsm P halt hPadd hPsmul hx hx' n₀ n₁ 0 1
    have e₁ := alternating_pairing_expand L hadd hsm P halt hPadd hPsmul hx hx' 1 0 n₀ n₁
    rw [hrel, hP0 _ (hadd _ (hsm 0 x hx) _ (hsm 1 x' hx'))] at e₀
    rw [hrel, hP0' _ (hadd _ (hsm 1 x hx) _ (hsm 0 x' hx'))] at e₁
    push_cast at e₀ e₁
    simp only [mul_one, mul_zero, sub_zero, one_mul, zero_mul] at e₀ e₁
    have h0 : (n₀ : F) = 0 := by
      rcases mul_eq_zero.mp e₀.symm with h | h
      · exact h
      · exact absurd h hne
    have h1 : (n₁ : F) = 0 := by
      rcases mul_eq_zero.mp e₁.symm with h | h
      · exact h
      · exact absurd h hne
    rw [hn₀] at h0
    rw [hn₁] at h1
    exact ⟨(mul_eq_zero.mp h0).resolve_left (hdne d), (mul_eq_zero.mp h1).resolve_left (hdne d)⟩
  have hcard : Fintype.card (Fin 2) = Module.finrank F V := by simp [hfin]
  obtain ⟨b, hb⟩ : ∃ b : Module.Basis (Fin 2) F V, ⇑b = ![x, x'] :=
    ⟨_, coe_basisOfLinearIndependentOfCardEqFinrank hli hcard⟩
  have hb0 : b 0 = x := by rw [hb]; rfl
  have hb1 : b 1 = x' := by rw [hb]; rfl
  let B : LinearMap.BilinForm F V := LinearMap.mk₂ F
    (fun z w => P x x' * (b.repr z 0 * b.repr w 1 - b.repr z 1 * b.repr w 0))
    (by intros; simp; ring) (by intros; simp; ring) (by intros; simp; ring) (by intros; simp; ring)
  have hB : ∀ z w, B z w = P x x' * (b.repr z 0 * b.repr w 1 - b.repr z 1 * b.repr w 0) :=
    fun _ _ => rfl
  have hBxx' : B x x' = P x x' := by
    rw [hB, ← hb0, ← hb1, b.repr_self, b.repr_self]
    simp
  refine ⟨B, fun z => by rw [hB]; ring, ?_⟩
  intro z hz w hw
  have hsum : ∀ v : V, v = b.repr v 0 • x + b.repr v 1 • x' := by
    intro v
    conv_lhs => rw [← b.sum_repr v]
    rw [Fin.sum_univ_two, hb0, hb1]
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (𝓞 F)⁰
    ![b.repr z 0, b.repr z 1, b.repr w 0, b.repr w 1]
  obtain ⟨r₀, hr₀⟩ := exists_int_of_isInteger_smul (d : 𝓞 F) (b.repr z 0) (hd 0)
  obtain ⟨r₁, hr₁⟩ := exists_int_of_isInteger_smul (d : 𝓞 F) (b.repr z 1) (hd 1)
  obtain ⟨s₀, hs₀⟩ := exists_int_of_isInteger_smul (d : 𝓞 F) (b.repr w 0) (hd 2)
  obtain ⟨s₁, hs₁⟩ := exists_int_of_isInteger_smul (d : 𝓞 F) (b.repr w 1) (hd 3)
  set e : 𝓞 F := (d : 𝓞 F) with he
  have hez : (e : F) • z = (r₀ : F) • x + (r₁ : F) • x' := by
    calc (e : F) • z = (e : F) • (b.repr z 0 • x + b.repr z 1 • x') := congrArg _ (hsum z)
      _ = _ := by rw [smul_add, smul_smul, smul_smul, hr₀, hr₁]
  have hew : (e : F) • w = (s₀ : F) • x + (s₁ : F) • x' := by
    calc (e : F) • w = (e : F) • (b.repr w 0 • x + b.repr w 1 • x') := congrArg _ (hsum w)
      _ = _ := by rw [smul_add, smul_smul, smul_smul, hs₀, hs₁]
  have hPe : P ((e : F) • z) ((e : F) • w) = (e : F) * ((e : F) * P z w) := by
    have a1 := hPsmul e z hz _ (hsm e w hw)
    have a2 := halt z hz _ (hsm e w hw)
    have a3 := hPsmul e w hw z hz
    have a4 := halt w hw z hz
    linear_combination a1 + (e : F) * a2 - (e : F) * a3 - (e : F) * (e : F) * a4
  have hBe : B ((e : F) • z) ((e : F) • w) = (e : F) * ((e : F) * B z w) := by
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  have eP := alternating_pairing_expand L hadd hsm P halt hPadd hPsmul hx hx' r₀ r₁ s₀ s₁
  have eB := alternating_pairing_expand L hadd hsm (fun u v => B u v)
    (fun u _ v _ => by simp only [hB]; ring) (fun u₁ _ u₂ _ v _ => by rw [map_add, LinearMap.add_apply])
    (fun a u _ v _ => by rw [map_smul, LinearMap.smul_apply, smul_eq_mul]) hx hx' r₀ r₁ s₀ s₁
  rw [← hez, ← hew, hPe] at eP
  rw [← hez, ← hew, hBe, hBxx'] at eB
  have hee : (e : F) * (e : F) ≠ 0 := mul_ne_zero (hdne d) (hdne d)
  apply mul_left_cancel₀ hee
  linear_combination eP - eB

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnnihilatorAvoidsFibreMinimalPrimes
section
open AlgebraicGeometry CategoryTheory Limits

namespace GlobalTheory

theorem annihilator_avoids_fibre_minimalPrimes
    (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [Algebra.FiniteType A B] (b : B)
    (hd : ∀ q : PrimeSpectrum B, q ∈ closure ({P : PrimeSpectrum B | ∃ s ∉ P.asIdeal, s * b = 0} ∩
      PrimeSpectrum.comap (algebraMap A B) ⁻¹' {PrimeSpectrum.comap (algebraMap A B) q}))
    (u : PrimeSpectrum B) : ∃ g : B, g * b = 0 ∧ ∀ Q ∈ ((u.asIdeal.comap (algebraMap A B)).map (algebraMap A B)).minimalPrimes,
      Q ≤ u.asIdeal → g ∉ Q := by
  classical
  let p : PrimeSpectrum A := PrimeSpectrum.comap (algebraMap A B) u
  let I₀ : Ideal B := p.asIdeal.map (algebraMap A B)
  let T : Set (Ideal B) := {Q | Q ∈ I₀.minimalPrimes ∧ Q.comap (algebraMap A B) = p.asIdeal}
  have hTfin : T.Finite := by
    let e := PrimeSpectrum.preimageOrderIsoFiber A B p
    haveI : IsNoetherianRing (p.asIdeal.Fiber B) :=
      Algebra.FiniteType.isNoetherianRing p.asIdeal.ResidueField _
    have hM : {j : PrimeSpectrum (p.asIdeal.Fiber B) | j.asIdeal ∈ minimalPrimes (p.asIdeal.Fiber B)}.Finite :=
      (minimalPrimes.finite_of_isNoetherianRing _).preimage (fun x _ y _ h => PrimeSpectrum.ext h)
    refine (hM.image fun j => (e.symm j).1.asIdeal).subset ?_
    rintro Q ⟨hQmin, hQp⟩
    have hQprime : Q.IsPrime := hQmin.1.1
    let Q' : PrimeSpectrum B := ⟨Q, hQprime⟩
    have hQ'mem : Q' ∈ PrimeSpectrum.comap (algebraMap A B) ⁻¹' {p} := by
      show PrimeSpectrum.comap (algebraMap A B) Q' = p
      ext1; exact hQp
    obtain ⟨J, hJmin, hJle⟩ := Ideal.exists_minimalPrimes_le (bot_le : ⊥ ≤ (e ⟨Q', hQ'mem⟩).asIdeal)
    have hJprime : J.IsPrime := hJmin.1.1
    let j : PrimeSpectrum (p.asIdeal.Fiber B) := ⟨J, hJprime⟩
    refine ⟨j, hJmin, ?_⟩
    have hle : e.symm j ≤ ⟨Q', hQ'mem⟩ := by
      rw [← e.le_iff_le, e.apply_symm_apply]; exact hJle
    have hle' : (e.symm j).1.asIdeal ≤ Q := hle
    have hover : (e.symm j).1.asIdeal.comap (algebraMap A B) = p.asIdeal :=
      congrArg PrimeSpectrum.asIdeal (e.symm j).2
    have hge : I₀ ≤ (e.symm j).1.asIdeal := by
      rw [Ideal.map_le_iff_le_comap, hover]
    exact le_antisymm hle' (hQmin.2 ⟨(e.symm j).1.isPrime, hge⟩ hle')
  obtain ⟨s, hs⟩ := hTfin.exists_finset_coe
  have hsT : ∀ i, i ∈ s ↔ i ∈ T := fun i => by rw [← hs]; rfl
  let K : Ideal B := LinearMap.ker (LinearMap.toSpanSingleton B B b)
  have hK : ∀ x, x ∈ K ↔ x * b = 0 := fun x => by
    simp [K, LinearMap.toSpanSingleton_apply, smul_eq_mul]
  have key : ∀ Q ∈ T, ¬ K ≤ Q := by
    intro Q hQ hKQ
    have hQprime : Q.IsPrime := hQ.1.1.1
    have hnot : ¬ (∏ Q'' ∈ s.erase Q, Q'') ≤ Q := by
      rw [hQprime.prod_le]
      rintro ⟨i, hi, hiQ⟩
      have hiT : i ∈ T := (hsT i).1 (Finset.mem_of_mem_erase hi)
      exact Finset.ne_of_mem_erase hi (le_antisymm hiQ (hQ.1.2 hiT.1.1 hiQ))
    obtain ⟨f, hfprod, hfQ⟩ := SetLike.not_le_iff_exists.1 hnot
    have hfo : ∀ Q'' ∈ T, Q'' ≠ Q → f ∈ Q'' := fun Q'' hQ'' hne =>
      (Ideal.prod_le_inf.trans (Finset.inf_le (Finset.mem_erase.2 ⟨hne, (hsT Q'').2 hQ''⟩))) hfprod
    let Qp : PrimeSpectrum B := ⟨Q, hQprime⟩
    have hcl := hd Qp
    rw [mem_closure_iff] at hcl
    obtain ⟨P, hPf, ⟨t, htP, htb⟩, hPfib⟩ :=
      hcl (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum B)) (PrimeSpectrum.basicOpen f).isOpen hfQ
    have hPf' : f ∉ P.asIdeal := hPf
    have hPover : P.asIdeal.comap (algebraMap A B) = p.asIdeal :=
      (congrArg PrimeSpectrum.asIdeal hPfib).trans hQ.2
    have hI₀P : I₀ ≤ P.asIdeal := by rw [Ideal.map_le_iff_le_comap, hPover]
    obtain ⟨Q', hQ'min, hQ'P⟩ := Ideal.exists_minimalPrimes_le hI₀P
    have hQ'T : Q' ∈ T := ⟨hQ'min, le_antisymm ((Ideal.comap_mono hQ'P).trans hPover.le)
      (Ideal.map_le_iff_le_comap.1 hQ'min.1.2)⟩
    by_cases hQQ : Q' = Q
    · subst hQQ
      exact htP (hQ'P (hKQ ((hK t).2 htb)))
    · exact hPf' (hQ'P (hfo Q' hQ'T hQQ))
  have hprime : ∀ i ∈ s, i ≠ ⊥ → i ≠ ⊥ → (id i : Ideal B).IsPrime := fun i hi _ _ =>
    ((hsT i).1 hi).1.1.1
  have hnot := mt (Ideal.subset_union_prime (f := id) (I := K) ⊥ ⊥ hprime).1 (by
    rintro ⟨i, hi, hKi⟩; exact key i ((hsT i).1 hi) hKi)
  rw [Set.not_subset] at hnot
  obtain ⟨g, hgK, hgU⟩ := hnot
  refine ⟨g, (hK g).1 hgK, fun Q hQ hQu hgQ => hgU ?_⟩
  have hQT : Q ∈ T := ⟨hQ, le_antisymm (Ideal.comap_mono hQu) (Ideal.map_le_iff_le_comap.1 hQ.1.2)⟩
  exact Set.mem_biUnion (show Q ∈ (↑s : Set (Ideal B)) from (hsT Q).2 hQT) hgQ

end GlobalTheory
end

