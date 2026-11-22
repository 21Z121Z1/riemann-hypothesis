import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0002
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0036
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0009
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0032
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0001
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0022
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0037
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0038

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasseNormPrincipleOfCyclicTower
section
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

open NumberField IsDedekindDomain Polynomial in
open scoped WithZero TensorProduct in
private theorem prod_univ_eq_prod_range_orderOf_of_generator {G β : Type} [Group G] [Fintype G] [CommMonoid β]
    {g : G} (hg : ∀ x, x ∈ Subgroup.zpowers g) (f : G → β) :
    ∏ σ, f σ = ∏ i ∈ Finset.range (orderOf g), f (g ^ i) := by
  classical
  rw [← IsCyclic.image_range_orderOf hg, Finset.prod_image]
  intro i hi j hj hij
  exact pow_injOn_Iio_orderOf (by simpa using hi) (by simpa using hj) hij

open NumberField IsDedekindDomain Polynomial in
open scoped WithZero TensorProduct in
private theorem prod_range_pow_pow_prod_range_eq_prod_range_mul {F E : Type} [Field F] [Field E] [Algebra F E]
    (τ : E ≃ₐ[F] E) (y : E) (d n : ℕ) :
    ∏ j ∈ Finset.range n, ((τ ^ d) ^ j) (∏ i ∈ Finset.range d, (τ ^ i) y) =
      ∏ m ∈ Finset.range (d * n), (τ ^ m) y := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ, ih, Nat.mul_succ, Finset.prod_range_add, map_prod]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← AlgEquiv.mul_apply, ← pow_mul, ← pow_add]

open NumberField IsDedekindDomain Polynomial in
open scoped WithZero TensorProduct in
private theorem exists_eq_pow_finrank_mul_norm_of_norm_eq_cyclic (F M E : Type) [Field F] [Field M] [Field E]
    [Algebra F M] [Algebra M E] [Algebra F E] [IsScalarTower F M E] [FiniteDimensional F E]
    [IsGalois F E] (hcyc : IsCyclic (E ≃ₐ[F] E)) (x : F) (hx : x ≠ 0) (e₀ : E)
    (he₀ : Algebra.norm M e₀ = algebraMap F M x) :
    ∃ b : F, ∃ c : E, c ≠ 0 ∧ x = b ^ Module.finrank M E * Algebra.norm F c := by
  classical
  haveI : FiniteDimensional M E := FiniteDimensional.right F M E
  haveI : FiniteDimensional F M := FiniteDimensional.left F M E
  haveI : IsGalois M E := IsGalois.tower_top_of_isGalois F M E
  set n := Module.finrank M E with hn
  set d := Module.finrank F M with hd
  have hdn : d * n = Module.finrank F E := Module.finrank_mul_finrank F M E
  have hn0 : 0 < n := Module.finrank_pos
  have hd0 : 0 < d := Module.finrank_pos
  obtain ⟨τ, hτ⟩ := hcyc.exists_generator
  have hcomm : ∀ a b : E ≃ₐ[F] E, a * b = b * a := by
    intro a b
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hτ a)
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hτ b)
    exact ((Commute.refl τ).zpow_zpow i j).eq
  let ρ : (E ≃ₐ[M] E) →* (E ≃ₐ[F] E) :=
    { toFun := fun h => h.restrictScalars F, map_one' := rfl, map_mul' := fun _ _ => rfl }
  have hρ : Function.Injective ρ := AlgEquiv.restrictScalars_injective F
  have hρapp : ∀ (h : E ≃ₐ[M] E) (y : E), ρ h y = h y := fun _ _ => rfl
  let K := ρ.range
  haveI : K.Normal := ⟨fun a _ g => by rwa [hcomm g a, mul_inv_cancel_right]⟩
  have hcardK : Nat.card K = n := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hρ).toEquiv, IsGalois.card_aut_eq_finrank]
  have hcardG : Nat.card (E ≃ₐ[F] E) = d * n := by rw [IsGalois.card_aut_eq_finrank, hdn]
  have hindex : K.index = d := by
    have h := K.index_mul_card
    rw [hcardK, hcardG] at h
    exact Nat.eq_of_mul_eq_mul_right hn0 h
  have hτd : τ ^ d ∈ K := hindex ▸ K.pow_index_mem τ
  obtain ⟨g, hg⟩ := hτd
  have hordτ : orderOf τ = d * n := by rw [orderOf_eq_card_of_forall_mem_zpowers hτ, hcardG]
  have hordτd : orderOf (τ ^ d) = n := by
    rw [orderOf_pow' τ hd0.ne', hordτ, Nat.gcd_mul_right_left, Nat.mul_div_cancel_left _ hd0]
  have hKz : Subgroup.zpowers (τ ^ d) = K := by
    apply Subgroup.eq_of_le_of_card_ge
    · rw [Subgroup.zpowers_le, ← hg]
      exact ⟨g, rfl⟩
    · rw [hcardK, Nat.card_zpowers, hordτd]
  have hgen : ∀ h : E ≃ₐ[M] E, h ∈ Subgroup.zpowers g := by
    intro h
    have hmem : ρ h ∈ Subgroup.zpowers (τ ^ d) := hKz ▸ ⟨h, rfl⟩
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, hρ ?_⟩
    rw [map_zpow, hg, hk]
  haveI : IsCyclic (E ≃ₐ[M] E) := ⟨⟨g, hgen⟩⟩
  have hordg : orderOf g = n := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hgen, IsGalois.card_aut_eq_finrank]

  have hnormτ : ∀ y : E, algebraMap M E (Algebra.norm M (τ y)) =
      τ (algebraMap M E (Algebra.norm M y)) := by
    intro y
    rw [Algebra.norm_eq_prod_automorphisms, Algebra.norm_eq_prod_automorphisms, map_prod]
    refine Finset.prod_congr rfl fun σ _ => ?_
    rw [← hρapp σ, ← hρapp σ, ← AlgEquiv.mul_apply, ← AlgEquiv.mul_apply, hcomm]
  have he₀0 : e₀ ≠ 0 := by
    rintro rfl
    exact hx ((algebraMap F M).injective (by rw [← he₀, Algebra.norm_zero, map_zero]))
  have hxE : algebraMap M E (Algebra.norm M e₀) = algebraMap F E x := by
    rw [he₀, ← IsScalarTower.algebraMap_apply]
  have hN0 : Algebra.norm M e₀ ≠ 0 := by rw [he₀]; exact (_root_.map_ne_zero _).mpr hx
  have hu : Algebra.norm M (τ e₀ / e₀) = 1 := by
    have h1 : Algebra.norm M (τ e₀ / e₀) * Algebra.norm M e₀ = Algebra.norm M (τ e₀) := by
      rw [← map_mul, div_mul_cancel₀ _ he₀0]
    have h2 : algebraMap M E (Algebra.norm M (τ e₀)) = algebraMap M E (Algebra.norm M e₀) := by
      rw [hnormτ, hxE, AlgEquiv.commutes]
    rw [(algebraMap M E).injective h2] at h1
    exact mul_right_cancel₀ hN0 (h1.trans (one_mul _).symm)
  obtain ⟨c, hc⟩ := groupCohomology.exists_div_of_norm_eq_one hgen hu
  have hgc : g (c : E) = (τ ^ d) (c : E) := by rw [← hρapp, hg]
  have hc0 : (c : E) ≠ 0 := c.ne_zero
  have hτdc0 : (τ ^ d) (c : E) ≠ 0 := by
    rw [← hgc]; exact (_root_.map_ne_zero _).mpr hc0
  set P := ∏ i ∈ Finset.range d, (τ ^ i) (c : E) with hPdef
  have hτP : τ P * c = P * (τ ^ d) (c : E) := by
    have hs : τ P = ∏ i ∈ Finset.range d, (τ ^ (i + 1)) (c : E) := by
      rw [hPdef, map_prod]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [pow_succ', AlgEquiv.mul_apply]
    rw [hs]
    have h := Finset.prod_range_succ' (fun i => (τ ^ i) (c : E)) d
    rw [Finset.prod_range_succ] at h
    simp only [pow_zero, AlgEquiv.one_apply] at h
    exact h.symm
  have hτe₀ : τ e₀ * (τ ^ d) (c : E) = e₀ * c := by
    rw [← hgc]
    have h := hc
    rw [div_eq_div_iff ((_root_.map_ne_zero _).mpr hc0) he₀0] at h
    linear_combination -h
  have hfix : τ (e₀ * P) = e₀ * P := by
    rw [map_mul]
    apply mul_right_cancel₀ (mul_ne_zero hτdc0 hc0)
    linear_combination (τ P * c) * hτe₀ + (e₀ * c) * hτP
  obtain ⟨b, hb⟩ : ∃ b : F, algebraMap F E b = e₀ * P := by
    have hall : ∀ σ : E ≃ₐ[F] E, σ (e₀ * P) = e₀ * P := by
      intro σ
      have hst : τ ∈ MulAction.stabilizer (E ≃ₐ[F] E) (e₀ * P) := hfix
      exact (Subgroup.zpowers_le.mpr hst) (hτ σ)
    exact IntermediateField.mem_bot.mp ((IsGalois.mem_bot_iff_fixed _).mpr hall)
  have hnormP : algebraMap M E (Algebra.norm M P) =
      algebraMap M E (algebraMap F M (Algebra.norm F (c : E))) := by
    rw [Algebra.norm_eq_prod_automorphisms, prod_univ_eq_prod_range_orderOf_of_generator hgen, hordg,
      ← IsScalarTower.algebraMap_apply, Algebra.norm_eq_prod_automorphisms,
      prod_univ_eq_prod_range_orderOf_of_generator hτ, hordτ, ← prod_range_pow_pow_prod_range_eq_prod_range_mul]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [← hρapp, map_pow, hg]
  have hbn : algebraMap F M (b ^ n) = algebraMap F M (x * Algebra.norm F (c : E)) := by
    have h := congrArg (Algebra.norm M) hb
    rw [IsScalarTower.algebraMap_apply F M E, Algebra.norm_algebraMap, map_mul, he₀,
      (algebraMap M E).injective hnormP] at h
    rw [map_pow, map_mul, h]
  have hNc : Algebra.norm F (c : E) ≠ 0 := (c.isUnit.map (Algebra.norm F)).ne_zero
  refine ⟨b, ((c⁻¹ : Eˣ) : E), Units.ne_zero _, ?_⟩
  rw [map_units_inv (Algebra.norm F) c, (algebraMap F M).injective hbn, mul_inv_cancel_right₀ hNc]

open NumberField IsDedekindDomain Polynomial in
open scoped WithZero TensorProduct in

theorem _root_.GlobalTheory.CNorm.np_of_cyclic_tower : ∀ (F M E : Type) [Field F] [NumberField F] [Field M] [NumberField M]
    [Field E] [NumberField E] [Algebra F M] [Algebra M E] [Algebra F E] [IsScalarTower F M E]
    [IsGalois F E], IsCyclic (E ≃ₐ[F] E) → _root_.GlobalTheory.CNorm.NP M E → _root_.GlobalTheory.CNorm.NP F M → _root_.GlobalTheory.CNorm.NP F E := by
  intro F M E _ _ _ _ _ _ _ _ _ _ _ hcyc hME hMF x hx0 hloc
  haveI : FiniteDimensional F E := inferInstance
  haveI : FiniteDimensional F M := inferInstance
  haveI : FiniteDimensional M E := inferInstance
  haveI : IsGalois M E := IsGalois.tower_top_of_isGalois F M E
  have hprops := _root_.GlobalTheory.CNorm.tnorm_baseChange F E
  have hxM : algebraMap F M x ≠ 0 := (_root_.map_ne_zero _).mpr hx0
  have h1 : _root_.GlobalTheory.CNorm.LocNorm M E (algebraMap F M x) := by
    refine ⟨fun w => ?_, fun a => ?_⟩
    · obtain ⟨φ, hφ⟩ := _root_.GlobalTheory.QNorm.exists_ringHom_adicCompletion_under F M w
      letI : Algebra F (w.adicCompletion M) :=
        ((algebraMap M (w.adicCompletion M)).comp (algebraMap F M)).toAlgebra
      haveI : IsScalarTower F M (w.adicCompletion M) := IsScalarTower.of_algebraMap_eq fun _ => rfl
      let ψ : (HeightOneSpectrum.under (𝓞 F) w).adicCompletion F →ₐ[F] w.adicCompletion M :=
        { φ with commutes' := fun r => (hφ r).trans rfl }
      exact _root_.GlobalTheory.CNorm.TNorm.of_tower F M E _ x
        (hprops.1 _ _ ψ x (hloc.1 _))
    · letI : Algebra F ℝ := ((algebraMap M ℝ).comp (algebraMap F M)).toAlgebra
      haveI : IsScalarTower F M ℝ := IsScalarTower.of_algebraMap_eq fun _ => rfl
      exact _root_.GlobalTheory.CNorm.TNorm.of_tower F M E ℝ x (hloc.2 _)
  obtain ⟨e₀, he₀⟩ := hME _ hxM h1
  obtain ⟨b, c, hc0, hxb⟩ := exists_eq_pow_finrank_mul_norm_of_norm_eq_cyclic F M E hcyc x hx0 e₀ he₀
  have hNc : Algebra.norm F c ≠ 0 := by
    intro h
    exact hx0 (by rw [hxb, h, mul_zero])
  have hb0 : b ≠ 0 := by
    rintro rfl
    exact hx0 (by rw [hxb, zero_pow Module.finrank_pos.ne', zero_mul])
  have hpow : ∀ (K : Type) [Field K] [Algebra F K], _root_.GlobalTheory.CNorm.TNorm F E K x →
      _root_.GlobalTheory.CNorm.TNorm F M K b := by
    intro K _ _ hK
    refine _root_.GlobalTheory.CNorm.tnorm_of_tnorm_pow F M E K hcyc b hb0 ?_
    exact hprops.2.2 K _ _ hNc (hxb ▸ hK) (hprops.2.1 K c)
  obtain ⟨m, hm⟩ := hMF b hb0 ⟨fun v => hpow _ (hloc.1 v), fun a => hpow ℝ (hloc.2 a)⟩
  refine ⟨algebraMap M E m * c, ?_⟩
  rw [map_mul, hxb, ← Algebra.norm_norm (S := M), Algebra.norm_algebraMap, map_pow, hm]

end GlobalTheory.CNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.QuasiReflectionEqUnitaryTransvectionMul
section
open NumberField IsDedekindDomain Matrix GlobalTheory.UTrans GlobalTheory.AdLat
open scoped TensorProduct

namespace GlobalTheory.UTrans.Chain

theorem eventually_quad_ne {E : Type} [Field E] [CharZero E] (a b c : E) (ha : a ≠ 0) :
    ∀ᶠ t : ℚ in Filter.cofinite, a + (t : E) * b + (t : E) ^ 2 * c ≠ 0 := by
  classical
  set p : Polynomial E := Polynomial.C a + Polynomial.C b * Polynomial.X + Polynomial.C c * Polynomial.X ^ 2 with hp
  have hp0 : p ≠ 0 := by
    intro h
    have h0 := congrArg (fun q : Polynomial E => q.coeff 0) h
    simp [p] at h0
    exact ha h0
  rw [Filter.eventually_cofinite]
  refine (Set.Finite.preimage (fun _ _ _ _ h => Rat.cast_injective h)
    (Finset.finite_toSet p.roots.toFinset)).subset ?_
  intro t ht
  simp only [Set.mem_setOf_eq, not_not] at ht
  simp only [Set.mem_preimage, Finset.mem_coe, Multiset.mem_toFinset]
  rw [Polynomial.mem_roots hp0]
  show Polynomial.eval (t : E) p = 0
  simp only [p, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
    Polynomial.eval_pow]
  linear_combination ht

variable {E : Type} [Field E] [CharZero E] {n : ℕ}

theorem hf_line_left (σ : E →+* E) (G : Matrix (Fin n) (Fin n) E) (x w z : Fin n → E) (t : E) :
    hf σ G (x + t • w) z = hf σ G x z + t * hf σ G w z := by
  simp only [hf, Finset.mul_sum, Pi.add_apply, Pi.smul_apply, smul_eq_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem hf_line_right (σ : E →+* E) (G : Matrix (Fin n) (Fin n) E) (x w z : Fin n → E) (t : E) :
    hf σ G z (x + t • w) = hf σ G z x + σ t * hf σ G z w := by
  simp only [hf, Finset.mul_sum, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem eventually_aniso (σ : E →+* E) (G : Matrix (Fin n) (Fin n) E) (x w : Fin n → E)
    (hx : hf σ G x x ≠ 0) :
    ∀ᶠ t : ℚ in Filter.cofinite, hf σ G (x + (t : E) • w) (x + (t : E) • w) ≠ 0 := by
  filter_upwards [eventually_quad_ne (hf σ G x x) (hf σ G w x + hf σ G x w) (hf σ G w w) hx]
    with t ht
  have hσ : σ (t : E) = t := map_ratCast σ t
  rw [hf_line_left, hf_line_right, hf_line_right, hσ]
  intro h
  apply ht
  linear_combination h

theorem eventually_pair (σ : E →+* E) (G : Matrix (Fin n) (Fin n) E) (x w z : Fin n → E)
    (hx : hf σ G x z ≠ 0) :
    ∀ᶠ t : ℚ in Filter.cofinite, hf σ G (x + (t : E) • w) z ≠ 0 := by
  filter_upwards [eventually_quad_ne (hf σ G x z) (hf σ G w z) 0 hx] with t ht
  rw [hf_line_left]
  intro h
  apply ht
  linear_combination h

theorem eventually_chain (σ : E →+* E) (G : Matrix (Fin n) (Fin n) E) (hG : IsHerm σ G)
    {ι : Type} (z : ι → Fin n → E) (l : ι → E) (x : Fin n → E) (u : E) (hx : hf σ G x x ≠ 0)
    (hu : u * σ u = 1) (hz : ∀ i, hf σ G (z i) (z i) = 0) (hxz : ∀ i, hf σ G x (z i) ≠ 0)
    (S : Finset ι) :
    ∀ᶠ t : ℚ in Filter.cofinite, ∃ m ∈ TvGen σ G, tv σ G x ((u - 1) / hf σ G x x) =
      m * tv σ G (x + (t : E) • ∑ i ∈ S, l i • z i)
        ((u - 1) / hf σ G (x + (t : E) • ∑ i ∈ S, l i • z i) (x + (t : E) • ∑ i ∈ S, l i • z i)) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    refine Filter.Eventually.of_forall fun t => ⟨1, (TvGen σ G).one_mem, ?_⟩
    simp
  | @insert j S hj ih =>
    have hpair := eventually_pair σ G x (∑ i ∈ S, l i • z i) (z j) (hxz j)
    have ha1 := eventually_aniso σ G x (∑ i ∈ S, l i • z i) hx
    have ha2 := eventually_aniso σ G x (∑ i ∈ insert j S, l i • z i) hx
    filter_upwards [ih, hpair, ha1, ha2] with t hih h1 h2 h3
    obtain ⟨m, hm, hmeq⟩ := hih
    have hsplit : x + (t : E) • ∑ i ∈ insert j S, l i • z i =
        (x + (t : E) • ∑ i ∈ S, l i • z i) + ((t : E) * l j) • z j := by
      rw [Finset.sum_insert hj, smul_add, mul_smul]
      abel
    rw [hsplit] at h3 ⊢
    obtain ⟨m', hm', hm'eq⟩ :=
      GlobalTheory.T.quasiReflection_eq_mul_transvections_of_hyperbolicPlane E n σ G hG _ (z j) ((t : E) * l j) u (hz j) h1 h2 h3 hu
    exact ⟨m * m', (TvGen σ G).mul_mem hm hm', by rw [hmeq, hm'eq, mul_assoc]⟩

end GlobalTheory.UTrans.Chain

theorem GlobalTheory.UTrans.quasiReflection_eq_tvGen_mul : ∀ (E : Type) [Field E] [CharZero E] (n : ℕ) (σ : E →+* E) (G : Matrix (Fin n) (Fin n) E), IsHerm σ G → (∃ z : Fin n → E, z ≠ 0 ∧ hf σ G z z = 0) → ∀ (x y : Fin n → E) (u : E), hf σ G x x ≠ 0 → hf σ G y y ≠ 0 → u * σ u = 1 → ∃ m ∈ TvGen σ G, tv σ G x ((u - 1) / hf σ G x x) = m * tv σ G y ((u - 1) / hf σ G y y) := by
  intro E _ _ n σ G hG hiso x y u hx hy hu
  classical
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hx (by simp [hf])
  have hy0 : y ≠ 0 := by
    rintro rfl
    exact hy (by simp [hf])
  obtain ⟨z, hli, hzp⟩ := GlobalTheory.T.exists_isotropic_basis_nonorthogonal_two_vectors E n σ G hG hiso x y hx0 hy0
  have : Nonempty (Fin n) := by
    by_contra hne
    exact hx0 (funext fun i => (hne ⟨i⟩).elim)
  have hspan : Submodule.span E (Set.range z) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank (by simp)
  have hmem : y - x ∈ Submodule.span E (Set.range z) := by
    rw [hspan]
    exact Submodule.mem_top
  obtain ⟨l, hl⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 hmem
  have hz : ∀ i, hf σ G (z i) (z i) = 0 := fun i => (hzp i).1
  have hxz : ∀ i, hf σ G x (z i) ≠ 0 := fun i => (hzp i).2.1
  have hyz : ∀ i, hf σ G y (z i) ≠ 0 := fun i => (hzp i).2.2
  have h1 := GlobalTheory.UTrans.Chain.eventually_chain σ G hG z l x u hx hu hz hxz Finset.univ
  have h2 := GlobalTheory.UTrans.Chain.eventually_chain σ G hG z (fun i => -l i) y u hy hu hz hyz
    Finset.univ
  have hT : Filter.Tendsto (fun t : ℚ => 1 - t) Filter.cofinite Filter.cofinite :=
    (sub_right_injective : Function.Injective fun t : ℚ => 1 - t).tendsto_cofinite
  obtain ⟨t, ⟨m1, hm1, e1⟩, ⟨m2, hm2, e2⟩⟩ := (h1.and (hT.eventually h2)).exists
  have hv : y + (((1 - t : ℚ)) : E) • ∑ i ∈ Finset.univ, (-l i) • z i =
      x + (t : E) • ∑ i ∈ Finset.univ, l i • z i := by
    simp only [neg_smul, Finset.sum_neg_distrib, hl]
    push_cast
    module
  have e2' : tv σ G y ((u - 1) / hf σ G y y) =
      m2 * tv σ G (x + (t : E) • ∑ i ∈ Finset.univ, l i • z i)
        ((u - 1) / hf σ G (x + (t : E) • ∑ i ∈ Finset.univ, l i • z i)
          (x + (t : E) • ∑ i ∈ Finset.univ, l i • z i)) := by
    rw [← hv]
    exact e2
  obtain ⟨-, hdet, hinv, -⟩ := (GlobalTheory.T.unitaryTransvectionSubmonoid_normal_det_one E n σ G hG).2 m2 hm2
  have hunit : IsUnit m2.det := by
    rw [hdet]
    exact isUnit_one
  refine ⟨m1 * m2⁻¹, (TvGen σ G).mul_mem hm1 hinv, ?_⟩
  rw [e1, e2', mul_assoc m1, ← mul_assoc m2⁻¹, Matrix.nonsing_inv_mul _ hunit, one_mul]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SiegelCoverStatement
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_siegel_decomposition_mul_int_matrix_of_det_eq_one : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] [LinearOrder ι], ∃ C : ℝ, ∀ g : Matrix ι ι ℝ, g.det = 1 → ∃ γ : Matrix ι ι ℤ, γ.det = 1 ∧ ∃ k a n, IsSiegel C k a n ∧ g * γ.map (Int.cast : ℤ → ℝ) = k * diagonal a * n := by
  first | exact @GlobalTheory.ClassFin.siegel_cover | exact GlobalTheory.ClassFin.siegel_cover | (intros; apply GlobalTheory.ClassFin.siegel_cover <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SubgroupPowRelIndexUnitsOfIsAdicCompleteStatement
section
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.subgroupPowRelIndex_units_of_isAdicComplete : ∀ (p : ℕ) (O : Type) [CommRing O] [IsDomain O] [CharZero O] (π : O), 0 < p → π ≠ 0 → IsAdicComplete (Ideal.span {π}) O → Nat.card (O ⧸ Ideal.span {(p : O) * π}) ≠ 0 → pTor p (⊤ : Subgroup Oˣ) ≠ 0 ∧ pIdx p (⊤ : Subgroup Oˣ) = Nat.card (O ⧸ Ideal.span {(p : O)}) * pTor p (⊤ : Subgroup Oˣ) := by
  first | exact @GlobalTheory.CNorm.pIdx_units_of_isAdicComplete | exact GlobalTheory.CNorm.pIdx_units_of_isAdicComplete | (intros; apply GlobalTheory.CNorm.pIdx_units_of_isAdicComplete <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.TwoMulCardPlacesLeCardOverQuadraticStatement
section
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.two_mul_card_places_le_card_over_quadratic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (δ : F) (θ : E) (σ : E ≃ₐ[F] E), IsQuad δ θ σ → ∀ (S : Finset (HeightOneSpectrum (𝓞 F))) (SE : Finset (HeightOneSpectrum (𝓞 E))), (∀ w : HeightOneSpectrum (𝓞 E), w ∈ SE ↔ w.under (𝓞 F) ∈ S) → 2 * S.card ≤ SE.card + tFin F δ S := by
  first | exact @GlobalTheory.QNorm.two_mul_card_le_card_over | exact GlobalTheory.QNorm.two_mul_card_le_card_over | (intros; apply GlobalTheory.QNorm.two_mul_card_le_card_over <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.UnitaryMatrixEqProdQuasiReflectionsStatement
section
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryMatrix_eq_prod_quasiReflections : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E) (n : ℕ) (G : Matrix (Fin n) (Fin n) E), IsHermForm c G → ∀ γ, IsUnE c G γ → ∃ l : List ((Fin n → E) × E), (∀ p ∈ l, hermE c G p.1 p.1 ≠ 0 ∧ p.2 * c p.2 = 1) ∧ γ = (l.map fun p => refl c G p.1 p.2).prod := by
  first | exact @GlobalTheory.UnRep.isUnE_eq_prod_refl | exact GlobalTheory.UnRep.isUnE_eq_prod_refl | (intros; apply GlobalTheory.UnRep.isUnE_eq_prod_refl <;> assumption)
end

