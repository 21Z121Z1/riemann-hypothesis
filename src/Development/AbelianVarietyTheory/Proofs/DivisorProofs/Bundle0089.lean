import Mathlib

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitMassFormulaFiniteIndexSubgroup
section
open MulAction

namespace GlobalTheory.OrbitMass

variable {G H D : Type} [Group G] [Group H] [MulAction G D] [MulAction H D]

def toG (ι : H →* G) (hc : ∀ (h : H) (d : D), ι h • d = h • d) :
    orbitRel.Quotient H D → orbitRel.Quotient G D :=
  Quotient.map' id (fun a b hab => by
    change a ∈ orbit H b at hab
    change a ∈ orbit G b
    obtain ⟨h, rfl⟩ := hab
    exact ⟨ι h, hc h b⟩)

def toCoset (ι : H →* G) (hc : ∀ (h : H) (d : D), ι h • d = h • d) (x : D) :
    G ⧸ ι.range → orbitRel.Quotient H D :=
  fun ω => Quotient.liftOn' ω (fun g => (Quotient.mk'' (g⁻¹ • x) : orbitRel.Quotient H D)) (by
    intro g₁ g₂ hg
    rw [QuotientGroup.leftRel_apply, MonoidHom.mem_range] at hg
    obtain ⟨h, hh⟩ := hg
    apply Quotient.sound'
    change g₁⁻¹ • x ∈ orbit H (g₂⁻¹ • x)
    refine ⟨h, ?_⟩
    change h • g₂⁻¹ • x = g₁⁻¹ • x
    rw [← hc, smul_smul, hh, mul_inv_cancel_right])

theorem toCoset_mk (ι : H →* G) (hc : ∀ (h : H) (d : D), ι h • d = h • d) (x : D) (g : G) :
    toCoset ι hc x (g : G ⧸ ι.range) = Quotient.mk'' (g⁻¹ • x) := rfl

theorem toCoset_eq_iff (ι : H →* G) (hc : ∀ (h : H) (d : D), ι h • d = h • d) (x : D) (a g : G) :
    toCoset ι hc x (g : G ⧸ ι.range) = Quotient.mk'' (a⁻¹ • x) ↔
      (g : G ⧸ ι.range) ∈ orbit (stabilizer G x) (a : G ⧸ ι.range) := by
  rw [toCoset_mk, Quotient.eq'']
  change g⁻¹ • x ∈ orbit H (a⁻¹ • x) ↔ _
  rw [mem_orbit_iff, mem_orbit_iff]
  constructor
  · rintro ⟨h, hh⟩
    refine ⟨⟨g * ι h * a⁻¹, ?_⟩, ?_⟩
    · rw [mem_stabilizer_iff, mul_smul, mul_smul, hc, hh, smul_inv_smul]
    · change ((g * ι h * a⁻¹ : G) • (a : G ⧸ ι.range)) = g
      rw [MulAction.Quotient.smul_mk, QuotientGroup.eq]
      exact ⟨h⁻¹, by simp [mul_assoc]⟩
  · rintro ⟨⟨s, hs⟩, hsa⟩
    change ((s : G) • (a : G ⧸ ι.range)) = g at hsa
    rw [MulAction.Quotient.smul_mk, QuotientGroup.eq, MonoidHom.mem_range] at hsa
    obtain ⟨k, hk⟩ := hsa
    have hg : g = s * a * ι k := by rw [hk, smul_eq_mul, mul_inv_cancel_left]
    subst hg
    have hs' : s⁻¹ • x = x := by rw [inv_smul_eq_iff]; exact (mem_stabilizer_iff.mp hs).symm
    refine ⟨k⁻¹, ?_⟩
    rw [← hc, map_inv, mul_inv_rev, mul_inv_rev, mul_smul, mul_smul, hs']

theorem card_stab (ι : H →* G) (hinj : Function.Injective ι)
    (hc : ∀ (h : H) (d : D), ι h • d = h • d) (x : D) (a : G) :
    Nat.card (stabilizer (stabilizer G x) (a : G ⧸ ι.range)) =
      Nat.card (stabilizer H (a⁻¹ • x)) := by
  symm
  refine Nat.card_eq_of_bijective
    (fun h => ⟨⟨a * ι h.1 * a⁻¹, by
      rw [mem_stabilizer_iff, mul_smul, mul_smul, hc, mem_stabilizer_iff.mp h.2, smul_inv_smul]⟩,
      by
        rw [mem_stabilizer_iff]
        change ((a * ι h.1 * a⁻¹ : G) • (a : G ⧸ ι.range)) = a
        rw [MulAction.Quotient.smul_mk, QuotientGroup.eq]
        exact ⟨h.1⁻¹, by simp [mul_assoc]⟩⟩) ⟨?_, ?_⟩
  · intro h₁ h₂ he
    have e : a * ι h₁.1 * a⁻¹ = a * ι h₂.1 * a⁻¹ := congrArg (fun s => ((s.1 : stabilizer G x) : G)) he
    exact Subtype.ext (hinj (mul_left_cancel (mul_right_cancel e)))
  · rintro ⟨⟨s, hs⟩, hsa⟩
    rw [mem_stabilizer_iff] at hsa
    change ((s : G) • (a : G ⧸ ι.range)) = a at hsa
    rw [MulAction.Quotient.smul_mk, QuotientGroup.eq, MonoidHom.mem_range] at hsa
    obtain ⟨k, hk⟩ := hsa
    have e : ι k⁻¹ = a⁻¹ * s * a := by
      rw [map_inv, hk, smul_eq_mul]; group
    refine ⟨⟨k⁻¹, ?_⟩, ?_⟩
    · rw [mem_stabilizer_iff, ← hc, e, mul_smul, mul_smul, smul_inv_smul, mem_stabilizer_iff.mp hs]
    · apply Subtype.ext; apply Subtype.ext
      change a * ι k⁻¹ * a⁻¹ = s
      rw [e]; group

theorem toG_mk (ι : H →* G) (hc : ∀ (h : H) (d : D), ι h • d = h • d) (y : D) :
    toG ι hc (Quotient.mk'' y) = Quotient.mk'' y := rfl

theorem sum_fiber (ι : H →* G) (hinj : Function.Injective ι)
    (hc : ∀ (h : H) (d : D), ι h • d = h • d) [ι.range.FiniteIndex]
    (c' : orbitRel.Quotient G D) [Finite (stabilizer G (Quotient.out c'))]
    [Fintype (orbitRel.Quotient H D)] [DecidableEq (orbitRel.Quotient G D)] :
    ∑ c ∈ Finset.univ.filter (fun c => toG ι hc c = c'),
        ((Nat.card (stabilizer H (Quotient.out c)) : ℂ))⁻¹
      = (ι.range.index : ℂ) / Nat.card (stabilizer G (Quotient.out c')) := by
  classical
  set x := Quotient.out c' with hx
  haveI : Fintype (G ⧸ ι.range) := Fintype.ofFinite _
  have hS0 : 0 < Nat.card (stabilizer G x) := Nat.card_pos
  have hidx : (ι.range.index : ℂ) / Nat.card (stabilizer G x) =
      ∑ _ω : G ⧸ ι.range, ((Nat.card (stabilizer G x) : ℂ))⁻¹ := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Subgroup.index_eq_card,
      Nat.card_eq_fintype_card, div_eq_mul_inv]
  rw [hidx, ← Finset.sum_fiberwise Finset.univ (toCoset ι hc x), Finset.sum_filter]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [Finset.sum_const, nsmul_eq_mul]
  split_ifs with hcx
  · have hmem : Quotient.out c ∈ orbit G x := by
      have h1 : (Quotient.mk'' (Quotient.out c) : orbitRel.Quotient G D) = Quotient.mk'' x := by
        rw [← toG_mk ι hc, Quotient.out_eq', hcx, hx, Quotient.out_eq']
      exact Quotient.exact' h1
    obtain ⟨b, hb⟩ := hmem
    have hy : (b⁻¹)⁻¹ • x = Quotient.out c := by rw [inv_inv]; exact hb
    have hfib : (Finset.univ.filter (fun ω => toCoset ι hc x ω = c)) =
        (orbit (stabilizer G x) ((b⁻¹ : G) : G ⧸ ι.range)).toFinset := by
      ext ω
      induction ω using QuotientGroup.induction_on with
      | H g =>
        rw [Finset.mem_filter, Set.mem_toFinset, ← toCoset_eq_iff ι hc x b⁻¹ g, hy,
          Quotient.out_eq']
        simp
    have hcard := Subgroup.card_mul_index (stabilizer (stabilizer G x) ((b⁻¹ : G) : G ⧸ ι.range))
    rw [index_stabilizer, card_stab ι hinj hc x b⁻¹, hy] at hcard
    rw [hfib, ← Set.ncard_eq_toFinset_card']
    have hm0 : Nat.card (stabilizer H (Quotient.out c)) ≠ 0 := by
      intro h0; rw [h0, zero_mul] at hcard; omega
    have hn0 : (orbit (stabilizer G x) ((b⁻¹ : G) : G ⧸ ι.range)).ncard ≠ 0 := by
      intro h0; rw [h0, mul_zero] at hcard; omega
    rw [← hcard]
    push_cast
    field_simp
  · rw [Finset.card_eq_zero.mpr, Nat.cast_zero, zero_mul]
    rw [Finset.filter_eq_empty_iff]
    intro ω _ hω
    apply hcx
    rw [← hω]
    induction ω using QuotientGroup.induction_on with
    | H g =>
      rw [toCoset_mk, toG_mk, hx]
      conv_rhs => rw [← Quotient.out_eq' c']
      exact Quotient.sound' ⟨g⁻¹, rfl⟩

theorem mass_formula : ∀ {G H D : Type} [Group G] [Group H] [MulAction G D] [MulAction H D] (ι : H →* G), Function.Injective ι → (∀ (h : H) (d : D), ι h • d = h • d) → ι.range.FiniteIndex → (∀ d : D, Finite (MulAction.stabilizer G d)) → ∀ [Fintype (MulAction.orbitRel.Quotient G D)] [Fintype (MulAction.orbitRel.Quotient H D)] (f : D → ℂ), (∀ (g : G) (d : D), f (g • d) = f d) → ∑ c : MulAction.orbitRel.Quotient H D, ((Nat.card (MulAction.stabilizer H (Quotient.out c)) : ℂ))⁻¹ * f (Quotient.out c) = (ι.range.index : ℂ) * ∑ c : MulAction.orbitRel.Quotient G D, ((Nat.card (MulAction.stabilizer G (Quotient.out c)) : ℂ))⁻¹ * f (Quotient.out c) := by
  intro G H D _ _ _ _ ι hinj hc hfi hfin _ _ f hf
  classical
  rw [← Finset.sum_fiberwise Finset.univ (toG ι hc)
    (fun c => ((Nat.card (MulAction.stabilizer H (Quotient.out c)) : ℂ))⁻¹ * f (Quotient.out c)),
    Finset.mul_sum]
  refine Finset.sum_congr rfl (fun c' _ => ?_)
  have hconst : ∀ c ∈ Finset.univ.filter (fun c => toG ι hc c = c'),
      ((Nat.card (MulAction.stabilizer H (Quotient.out c)) : ℂ))⁻¹ * f (Quotient.out c) =
      ((Nat.card (MulAction.stabilizer H (Quotient.out c)) : ℂ))⁻¹ * f (Quotient.out c') := by
    intro c hc'
    rw [Finset.mem_filter] at hc'
    have h1 : (Quotient.mk'' (Quotient.out c) : orbitRel.Quotient G D) = Quotient.mk'' (Quotient.out c') := by
      rw [← toG_mk ι hc, Quotient.out_eq', hc'.2, Quotient.out_eq']
    obtain ⟨g, hg⟩ := (Quotient.exact' h1 : Quotient.out c ∈ orbit G (Quotient.out c'))
    rw [← hg]
    change _ * f (g • Quotient.out c') = _
    rw [hf]
  haveI := hfin (Quotient.out c')
  rw [Finset.sum_congr rfl hconst, ← Finset.sum_mul, sum_fiber ι hinj hc c', div_eq_mul_inv, mul_assoc]

end GlobalTheory.OrbitMass
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrderProdSubProd
section
namespace GlobalTheory.OrderProductDifference

open MvPowerSeries

theorem order_prod_sub_prod {R τ ι : Type} [CommRing R] (s : Finset ι)
    (a b : ι → MvPowerSeries τ R) (k : ι → ℕ)
    (ha : ∀ i ∈ s, ((k i : ℕ) : ℕ∞) ≤ MvPowerSeries.order (a i))
    (hb : ∀ i ∈ s, ((k i : ℕ) : ℕ∞) ≤ MvPowerSeries.order (b i))
    (hab : ∀ i ∈ s, ((k i : ℕ) : ℕ∞) + (1 : ℕ∞) ≤ MvPowerSeries.order (a i - b i)) :
    ∑ i ∈ s, ((k i : ℕ) : ℕ∞) + (1 : ℕ∞) ≤ MvPowerSeries.order (∏ i ∈ s, a i - ∏ i ∈ s, b i) := by
  classical
  revert ha hb hab
  induction s using Finset.induction_on with
  | empty => intro _ _ _; simp
  | @insert j s hj ih =>
    intro ha hb hab
    have ih' := ih (fun i hi => ha i (Finset.mem_insert_of_mem hi))
      (fun i hi => hb i (Finset.mem_insert_of_mem hi))
      (fun i hi => hab i (Finset.mem_insert_of_mem hi))
    have key : ∏ i ∈ insert j s, a i - ∏ i ∈ insert j s, b i
        = a j * (∏ i ∈ s, a i - ∏ i ∈ s, b i) + (a j - b j) * ∏ i ∈ s, b i := by
      rw [Finset.prod_insert hj, Finset.prod_insert hj]; ring
    have hbs : ∑ i ∈ s, ((k i : ℕ) : ℕ∞) ≤ MvPowerSeries.order (∏ i ∈ s, b i) :=
      le_trans (Finset.sum_le_sum fun i hi => hb i (Finset.mem_insert_of_mem hi))
        (MvPowerSeries.le_order_prod _ _)
    rw [key, Finset.sum_insert hj]
    refine le_trans ?_ MvPowerSeries.min_order_le_add
    refine le_min ?_ ?_
    · calc ((k j : ℕ) : ℕ∞) + ∑ i ∈ s, ((k i : ℕ) : ℕ∞) + 1
          = (k j : ℕ∞) + (∑ i ∈ s, ((k i : ℕ) : ℕ∞) + 1) := by rw [add_assoc]
        _ ≤ MvPowerSeries.order (a j) + MvPowerSeries.order (∏ i ∈ s, a i - ∏ i ∈ s, b i) :=
          add_le_add (ha j (Finset.mem_insert_self _ _)) ih'
        _ ≤ _ := MvPowerSeries.le_order_mul
    · calc ((k j : ℕ) : ℕ∞) + ∑ i ∈ s, ((k i : ℕ) : ℕ∞) + 1
          = ((k j : ℕ∞) + 1) + ∑ i ∈ s, ((k i : ℕ) : ℕ∞) := by rw [add_right_comm]
        _ ≤ MvPowerSeries.order (a j - b j) + MvPowerSeries.order (∏ i ∈ s, b i) :=
          add_le_add (hab j (Finset.mem_insert_self _ _)) hbs
        _ ≤ _ := MvPowerSeries.le_order_mul

theorem target : ∀ {R τ ι : Type} [inst : CommRing R] (s : Finset ι) (a b : ι → MvPowerSeries τ R) (k : ι → ℕ), (∀ i ∈ s, (↑(k i) : ℕ∞) ≤ MvPowerSeries.order (a i)) → (∀ i ∈ s, (↑(k i) : ℕ∞) ≤ MvPowerSeries.order (b i)) → (∀ i ∈ s, (↑(k i) : ℕ∞) + (1 : ℕ∞) ≤ MvPowerSeries.order (a i - b i)) → ∑ i ∈ s, (↑(k i) : ℕ∞) + (1 : ℕ∞) ≤ MvPowerSeries.order (∏ i ∈ s, a i - ∏ i ∈ s, b i) :=
  fun s a b k ha hb hab => order_prod_sub_prod s a b k ha hb hab

end GlobalTheory.OrderProductDifference
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OverSchemeGrpObjOfMonoFactor
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem grpObj_of_mono_factor {C : Type*} [Category C] [CartesianMonoidalCategory C]
    {A K : C} [GrpObj A] (i : K ⟶ A) [Mono i] (m : K ⊗ K ⟶ K) (hm : m ≫ i = (i ⊗ₘ i) ≫ μ[A])
    (e : 𝟙_ C ⟶ K) (he : e ≫ i = η[A]) (v : K ⟶ K) (hv : v ≫ i = i ≫ ι[A]) :
    ∃ _ : GrpObj K, IsMonHom i := by
  letI M : MonObj K :=
    { one := e, mul := m
      one_mul := by
        rw [← cancel_mono i, Category.assoc, hm]
        have h1 : e ▷ K ≫ (i ⊗ₘ i) = 𝟙_ C ◁ i ≫ η[A] ▷ A := by
          rw [← tensorHom_id, tensorHom_comp_tensorHom, Category.id_comp, he, tensorHom_def']
        rw [reassoc_of% h1, MonObj.one_mul, leftUnitor_naturality]
      mul_one := by
        rw [← cancel_mono i, Category.assoc, hm]
        have h1 : K ◁ e ≫ (i ⊗ₘ i) = i ▷ 𝟙_ C ≫ A ◁ η[A] := by
          rw [← id_tensorHom, tensorHom_comp_tensorHom, Category.id_comp, he, MonoidalCategory.tensorHom_def]
        rw [reassoc_of% h1, MonObj.mul_one, rightUnitor_naturality]
      mul_assoc := by
        rw [← cancel_mono i]
        have h1 : m ▷ K ≫ m ≫ i = ((i ⊗ₘ i) ⊗ₘ i) ≫ μ[A] ▷ A ≫ μ[A] := by
          simp only [← tensorHom_id, tensorHom_comp_tensorHom_assoc, hm, Category.id_comp,
            Category.comp_id]
        have h2 : K ◁ m ≫ m ≫ i = (i ⊗ₘ (i ⊗ₘ i)) ≫ A ◁ μ[A] ≫ μ[A] := by
          simp only [← id_tensorHom, tensorHom_comp_tensorHom_assoc, hm, Category.id_comp,
            Category.comp_id]
        simp only [Category.assoc]
        rw [h1, h2, MonObj.mul_assoc (X := A), associator_naturality_assoc] }
  letI G : GrpObj K :=
    { inv := v
      left_inv := by
        rw [← cancel_mono i]
        simp only [Category.assoc]
        change lift v (𝟙 K) ≫ m ≫ i = toUnit K ≫ e ≫ i
        have h3 : lift (i ≫ ι[A]) i = i ≫ lift ι[A] (𝟙 A) := by simp
        rw [hm, he, lift_map_assoc, hv, Category.id_comp, h3, Category.assoc, GrpObj.left_inv,
          ← Category.assoc, toUnit_unique (i ≫ toUnit A) (toUnit K)]
      right_inv := by
        rw [← cancel_mono i]
        simp only [Category.assoc]
        change lift (𝟙 K) v ≫ m ≫ i = toUnit K ≫ e ≫ i
        have h3 : lift i (i ≫ ι[A]) = i ≫ lift (𝟙 A) ι[A] := by simp
        rw [hm, he, lift_map_assoc, hv, Category.id_comp, h3, Category.assoc, GrpObj.right_inv,
          ← Category.assoc, toUnit_unique (i ≫ toUnit A) (toUnit K)] }
  exact ⟨G, { one_hom := he, mul_hom := hm }⟩

theorem overScheme_grpObj_of_mono_factor : ∀ (T : Scheme.{0}) (A K : Over T) [GrpObj A] (i : K ⟶ A),
    Mono i → (∃ m : K ⊗ K ⟶ K, m ≫ i = (i ⊗ₘ i) ≫ μ[A]) → (∃ e : 𝟙_ (Over T) ⟶ K, e ≫ i = η[A]) →
    (∃ v : K ⟶ K, v ≫ i = i ≫ ι[A]) → ∃ _ : GrpObj K, IsMonHom i := by
  intro T A K _ i hi ⟨m, hm⟩ ⟨e, he⟩ ⟨v, hv⟩
  exact grpObj_of_mono_factor i m hm e he v hv

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicIntExistsLevelNotDvdMulLift
section
namespace GlobalTheory

theorem padicInt_toZModPow_not_dvd_mul :
    ∀ (l : ℕ) [Fact l.Prime] (c : ℤ_[l]), c ≠ 0 → ∀ e : ℕ, 0 < e →
      ∃ N : ℕ, ∀ m : ℤ, PadicInt.toZModPow N c = (m : ZMod (l ^ N)) →
        ¬ ((l : ℤ) ^ N ∣ e * m) := by
  intro l _ c hc e he
  have hl : l.Prime := Fact.out
  refine ⟨c.valuation + e.factorization l + 1, ?_⟩
  intro m hm hdvd
  set v := c.valuation with hv
  set a := e.factorization l with ha
  have hm1 : (l : ℤ) ^ (v + 1) ∣ m := by
    have he' : (e : ℤ) = (l : ℤ) ^ a * ((e / l ^ a : ℕ) : ℤ) := by
      exact_mod_cast (Nat.ordProj_mul_ordCompl_eq_self e l).symm
    have hcop : IsCoprime ((l : ℤ) ^ (v + 1)) ((e / l ^ a : ℕ) : ℤ) := by
      have h := (Nat.coprime_ordCompl hl he.ne').pow_left (v + 1)
      have := Nat.isCoprime_iff_coprime.mpr h
      simpa [Nat.cast_pow] using this
    rw [he', show v + a + 1 = a + (v + 1) by ring, pow_add, mul_assoc] at hdvd
    have h2 := (mul_dvd_mul_iff_left (pow_ne_zero a (by exact_mod_cast hl.ne_zero : (l : ℤ) ≠ 0))).mp hdvd
    exact hcop.dvd_of_dvd_mul_left h2
  have h0 : PadicInt.toZModPow (v + 1) c = 0 := by
    rw [← PadicInt.cast_toZModPow (v + 1) (v + a + 1) (by omega) c, hm,
      ZMod.cast_intCast (pow_dvd_pow l (by omega))]
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact_mod_cast hm1
  have hmem : c ∈ (Ideal.span {(l : ℤ_[l]) ^ (v + 1)} : Ideal ℤ_[l]) := by
    rw [← PadicInt.ker_toZModPow]
    exact h0
  have := (PadicInt.mem_span_pow_iff_le_valuation c hc (v + 1)).mp hmem
  omega

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicMemRangeCompleteDvrPadicAlgCl
section
open IsLocalRing

namespace GlobalTheory.PadicUnitBall

variable {p : ℕ} [Fact p.Prime] {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  {κ : FractionRing V →+* PadicAlgCl p}

theorem norm_lt_one_of_mem_maximalIdeal
    (hV : ∀ x, ‖κ x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap V (FractionRing V)))
    {v : V} (hv : v ∈ maximalIdeal V) : ‖κ (algebraMap V (FractionRing V) v)‖ < 1 := by
  have hle : ‖κ (algebraMap V (FractionRing V) v)‖ ≤ 1 := (hV _).2 ⟨v, rfl⟩
  refine lt_of_le_of_ne hle fun h1 => ?_
  have hv0 : v ≠ 0 := by
    rintro rfl; simp at h1
  have hι : algebraMap V (FractionRing V) v ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective V (FractionRing V))).2 hv0
  have hinv : ‖κ (algebraMap V (FractionRing V) v)⁻¹‖ ≤ 1 := by
    rw [map_inv₀, norm_inv, h1, inv_one]
  obtain ⟨w, hw⟩ := (hV _).1 hinv
  have hvw : v * w = 1 := by
    apply IsFractionRing.injective V (FractionRing V)
    rw [map_mul, hw, map_one, mul_inv_cancel₀ hι]
  exact (mem_maximalIdeal _).1 hv ⟨⟨v, w, hvw, by rw [mul_comm]; exact hvw⟩, rfl⟩

theorem norm_natCast_p : ‖((p : ℕ) : PadicAlgCl p)‖ = (p : ℝ)⁻¹ := by
  have : ((p : ℕ) : PadicAlgCl p) = algebraMap ℚ_[p] (PadicAlgCl p) (p : ℚ_[p]) := by
    rw [map_natCast]
  rw [this, PadicAlgCl.norm_extends, Padic.norm_p]

theorem p_mem_maximalIdeal
    (hV : ∀ x, ‖κ x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap V (FractionRing V))) :
    ((p : ℕ) : V) ∈ maximalIdeal V := by
  rw [mem_maximalIdeal, mem_nonunits_iff]
  rintro ⟨u, hu⟩
  have h1 : ‖κ (algebraMap V (FractionRing V) (u⁻¹ : Vˣ))‖ ≤ 1 := (hV _).2 ⟨_, rfl⟩
  have h2 : κ (algebraMap V (FractionRing V) ((p : ℕ) : V)) *
      κ (algebraMap V (FractionRing V) (u⁻¹ : Vˣ)) = 1 := by
    rw [← map_mul, ← map_mul, ← hu, Units.mul_inv, map_one, map_one]
  have h3 := congrArg norm h2
  rw [norm_mul, norm_one, map_natCast, map_natCast, norm_natCast_p] at h3
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have : (p : ℝ)⁻¹ * ‖κ (algebraMap V (FractionRing V) (u⁻¹ : Vˣ))‖ < 1 :=
    lt_of_le_of_lt (mul_le_of_le_one_right (by positivity) h1) (inv_lt_one_of_one_lt₀ hp)
  linarith

end GlobalTheory.PadicUnitBall

namespace GlobalTheory.PadicUnitBall

variable {p : ℕ} [Fact p.Prime] {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  {κ : FractionRing V →+* PadicAlgCl p}

theorem exists_norm_le_pow
    (hV : ∀ x, ‖κ x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap V (FractionRing V))) :
    ∃ r : ℝ, 0 ≤ r ∧ r < 1 ∧ ∀ n : ℕ, ∀ x ∈ maximalIdeal V ^ n,
      ‖κ (algebraMap V (FractionRing V) x)‖ ≤ r ^ n := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  have hmax := hϖ.maximalIdeal_eq
  refine ⟨‖κ (algebraMap V (FractionRing V) ϖ)‖, norm_nonneg _,
    norm_lt_one_of_mem_maximalIdeal hV (by rw [hmax]; exact Ideal.mem_span_singleton_self ϖ),
    fun n x hx => ?_⟩
  rw [hmax, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hx
  obtain ⟨w, rfl⟩ := hx
  rw [map_mul, map_mul, norm_mul, map_pow, map_pow, norm_pow]
  have hw : ‖κ (algebraMap V (FractionRing V) w)‖ ≤ 1 := (hV _).2 ⟨w, rfl⟩
  exact mul_le_of_le_one_right (by positivity) hw

theorem smul_top_eq (I : Ideal V) : (I • ⊤ : Submodule V V) = I := by
  rw [smul_eq_mul, Ideal.mul_top]

theorem padicInt_mem_range
    (hc : IsAdicComplete (maximalIdeal V) V)
    (hV : ∀ x, ‖κ x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap V (FractionRing V))) (z : ℤ_[p]) :
    ∃ L : V, κ (algebraMap V (FractionRing V) L) = algebraMap ℚ_[p] (PadicAlgCl p) (z : ℚ_[p]) := by
  set f : ℕ → V := fun n => ((z.appr n : ℕ) : V) with hf
  have hpm := p_mem_maximalIdeal hV
  have hcauchy : ∀ {m n : ℕ}, m ≤ n → f m ≡ f n [SMOD (maximalIdeal V) ^ m • (⊤ : Submodule V V)] := by
    intro m n hmn
    rw [SModEq.sub_mem, smul_top_eq]
    obtain ⟨c, hc⟩ := PadicInt.dvd_appr_sub_appr z m n hmn
    have hmono : z.appr m ≤ z.appr n := PadicInt.appr_mono z hmn
    have heq : z.appr n = z.appr m + p ^ m * c := by
      generalize p ^ m * c = k at hc; omega
    have : f m - f n = ((p : ℕ) : V) ^ m * (-(c : V)) := by
      simp only [hf, heq]; push_cast; ring
    rw [this]
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hpm m)
  obtain ⟨L, hL⟩ := hc.toIsPrecomplete.prec hcauchy
  refine ⟨L, ?_⟩
  obtain ⟨r, hr0, hr1, hr⟩ := exists_norm_le_pow hV
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hbound : ∀ n : ℕ, ‖κ (algebraMap V (FractionRing V) L) - algebraMap ℚ_[p] (PadicAlgCl p) (z : ℚ_[p])‖
      ≤ r ^ n + ((p : ℝ)⁻¹) ^ n := by
    intro n
    have h1 : f n - L ∈ maximalIdeal V ^ n := by
      have := hL n
      rwa [SModEq.sub_mem, smul_top_eq] at this
    have h1' := hr n _ h1
    have hfn : κ (algebraMap V (FractionRing V) (f n)) =
        algebraMap ℚ_[p] (PadicAlgCl p) (((z.appr n : ℕ) : ℤ_[p]) : ℚ_[p]) := by
      simp only [hf, map_natCast, PadicInt.coe_natCast]
    have h2 : ‖z - ((z.appr n : ℕ) : ℤ_[p])‖ ≤ (p : ℝ) ^ (-(n : ℤ)) :=
      (PadicInt.norm_le_pow_iff_mem_span_pow _ n).2 (PadicInt.appr_spec n z)
    rw [zpow_neg, zpow_natCast, ← inv_pow] at h2
    have h2' : ‖algebraMap ℚ_[p] (PadicAlgCl p) (((z.appr n : ℕ) : ℤ_[p]) : ℚ_[p]) -
        algebraMap ℚ_[p] (PadicAlgCl p) (z : ℚ_[p])‖ ≤ ((p : ℝ)⁻¹) ^ n := by
      rw [← map_sub, PadicAlgCl.norm_extends, ← PadicInt.coe_sub, PadicInt.norm_def.symm, norm_sub_rev]
      exact h2
    calc _ = ‖(κ (algebraMap V (FractionRing V) L) - κ (algebraMap V (FractionRing V) (f n))) +
          (κ (algebraMap V (FractionRing V) (f n)) - algebraMap ℚ_[p] (PadicAlgCl p) (z : ℚ_[p]))‖ := by
            congr 1; ring
      _ ≤ _ := norm_add_le _ _
      _ ≤ r ^ n + ((p : ℝ)⁻¹) ^ n := by
        gcongr
        · rw [norm_sub_rev, ← map_sub, ← map_sub]; exact h1'
        · rw [hfn]; exact h2'
  have ht : Filter.Tendsto (fun n : ℕ => r ^ n + ((p : ℝ)⁻¹) ^ n) Filter.atTop (nhds 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).add
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (inv_lt_one_of_one_lt₀ hp))
    simpa using this
  have h0 := ge_of_tendsto' ht hbound
  exact sub_eq_zero.1 (norm_le_zero_iff.1 h0)

end GlobalTheory.PadicUnitBall

namespace GlobalTheory.PadicUnitBall

theorem padic_mem_range : ∀ (p : ℕ) [Fact p.Prime] (V : Type) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (maximalIdeal V) V →
    ∀ (κ : FractionRing V →+* PadicAlgCl p),
    (∀ x, ‖κ x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap V (FractionRing V))) →
    ∀ q : ℚ_[p], algebraMap ℚ_[p] (PadicAlgCl p) q ∈ κ.range := by
  intro p _ V _ _ _ _ hc κ hV q
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt ‖q‖ hp
  have hz : ‖q * (p : ℚ_[p]) ^ k‖ ≤ 1 := by
    rw [norm_mul, norm_pow, Padic.norm_p, inv_pow]
    rw [mul_inv_le_iff₀ (by positivity), one_mul]
    exact hk.le
  obtain ⟨L, hL⟩ := padicInt_mem_range hc hV (⟨q * (p : ℚ_[p]) ^ k, hz⟩ : ℤ_[p])
  have hpne : ((p : ℕ) : PadicAlgCl p) ≠ 0 := by
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  refine ⟨algebraMap V (FractionRing V) L * (((p : ℕ) : FractionRing V) ^ k)⁻¹, ?_⟩
  rw [map_mul, hL, map_inv₀, map_pow, map_natCast]
  show algebraMap ℚ_[p] (PadicAlgCl p) (q * (p : ℚ_[p]) ^ k) * _ = _
  simp only [map_mul, map_pow, map_natCast]
  field_simp

end GlobalTheory.PadicUnitBall
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PerfectionIsUnitOfCoeffZero
section
namespace GlobalTheory

open IsLocalRing

open IsLocalRing in
theorem _root_.GlobalTheory.preTilt_isLocalRing : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [IsLocalRing O]
    [Fact ¬IsUnit (p : O)], IsLocalRing (PreTilt O p) := by
  intro p _ O _ _ _
  haveI : IsLocalRing (ModP O p) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  haveI : IsLocalHom (Perfection.coeff (ModP O p) p 0) := by
    refine ⟨fun x hx => ?_⟩
    have hunit : ∀ n, IsUnit (Perfection.coeff (ModP O p) p n x) := by
      intro n
      induction n with
      | zero => exact hx
      | succ n ih =>
        rw [← Perfection.coeff_pow_p' x n] at ih
        exact (isUnit_pow_iff (Fact.out : p.Prime).ne_zero).mp ih
    let y : Perfection (ModP O p) p := ⟨fun n => ↑(hunit n).unit⁻¹, fun n => by
      have key : (hunit (n + 1)).unit ^ p = (hunit n).unit :=
        Units.ext (by simpa using Perfection.coeff_pow_p' x n)
      rw [← Units.val_pow_eq_pow_val, inv_pow, key]⟩
    have hxy : x * y = 1 := Perfection.ext fun n => by
      rw [map_mul, map_one]
      show Perfection.coeff (ModP O p) p n x * ↑(hunit n).unit⁻¹ = 1
      exact (hunit n).mul_val_inv
    exact ⟨⟨x, y, hxy, mul_comm y x ▸ hxy⟩, rfl⟩
  exact (Perfection.coeff (ModP O p) p 0).domain_isLocalRing

end GlobalTheory
end

