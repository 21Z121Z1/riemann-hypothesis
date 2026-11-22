import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0001
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0001
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.Bundle0001
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0002
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0005
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0004

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsIntegralCoeffInterpolationBivariateSeries
section
open GlobalTheory.ConvSer Polynomial

namespace GlobalTheory.ConvSer

theorem norm_coeff_prod_X_sub_C_le_pow {K : Type} [NormedField K] [IsUltrametricDist K]
    (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (S : Finset K) (hS : ∀ x ∈ S, ‖x‖ ≤ θ) (a : ℕ) :
    ‖(∏ x ∈ S, (X - C x) : K[X]).coeff a‖ ≤ θ ^ (S.card - a) := by
  first
  | exact @_root_.GlobalTheory.RootProductCoeffBound.main
  | exact _root_.GlobalTheory.RootProductCoeffBound.main
  | (apply _root_.GlobalTheory.RootProductCoeffBound.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.RootProductCoeffBound.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.RootProductCoeffBound.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.RootProductCoeffBound.main ..)

theorem exists_pow_eq_interpolation {K : Type} [NormedField K] [IsUltrametricDist K]
    (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (S : Finset K) (hS : ∀ x ∈ S, ‖x‖ ≤ θ)
    (hN : 0 < S.card) (k : ℕ) :
    ∃ Q : K[X], (∀ a, S.card ≤ a → Q.coeff a = 0) ∧ (∀ a, ‖Q.coeff a‖ ≤ θ ^ (k - a)) ∧
      ∀ x ∈ S, Q.eval x = x ^ k := by
  induction k with
  | zero =>
    refine ⟨1, fun a ha => ?_, fun a => ?_, by simp⟩
    · rw [coeff_one, if_neg (by omega)]
    · rw [coeff_one]; split_ifs <;> simp
  | succ k ih =>
    obtain ⟨Q, hQ0, hQ1, hQ2⟩ := ih
    obtain ⟨n, hn⟩ : ∃ n, S.card = n + 1 := ⟨S.card - 1, by omega⟩
    set P : K[X] := ∏ x ∈ S, (X - C x) with hP
    have hPm : P.Monic := monic_prod_of_monic _ _ (fun x _ => monic_X_sub_C x)
    have hPd : P.natDegree = n + 1 := by
      rw [hP, natDegree_prod_of_monic _ _ (fun x _ => monic_X_sub_C x)]
      simp [hn]
    refine ⟨X * Q - C (Q.coeff n) * P, fun a ha => ?_, fun a => ?_, fun x hx => ?_⟩
    · obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
      rw [coeff_sub, coeff_X_mul, coeff_C_mul]
      rcases (show n = b ∨ n < b by omega) with rfl | h
      · have : P.coeff (n + 1) = 1 := by rw [← hPd]; exact hPm.coeff_natDegree
        rw [this]; simp
      · rw [hQ0 b (by omega), coeff_eq_zero_of_natDegree_lt (p := P) (by omega)]; simp
    · by_cases ha : n + 1 < a
      · obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
        rw [coeff_sub, coeff_X_mul, coeff_C_mul, hQ0 b (by omega),
          coeff_eq_zero_of_natDegree_lt (p := P) (by omega)]
        simp; positivity
      rw [coeff_sub, coeff_C_mul, sub_eq_add_neg]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
      · cases a with
        | zero => simp; positivity
        | succ a =>
          rw [coeff_X_mul]
          simpa using hQ1 a
      · rw [norm_neg, norm_mul]
        calc _ ≤ θ ^ (k - n) * θ ^ (S.card - a) :=
              mul_le_mul (hQ1 n) (norm_coeff_prod_X_sub_C_le_pow θ h0 h1 S hS a) (norm_nonneg _)
                (by positivity)
          _ = θ ^ (k - n + (S.card - a)) := by ring
          _ ≤ _ := pow_le_pow_of_le_one h0 h1 (by omega)
    · have : P.eval x = 0 := by
        rw [hP, eval_prod]
        exact Finset.prod_eq_zero hx (by simp)
      simp [this, hQ2 x hx, pow_succ']

theorem exists_integral_interpolation_two :
    ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] (S : Finset K)
      (H : MvPowerSeries (Fin 2) K), (∀ x ∈ S, ‖x‖ < 1) → Intg H →
      ∃ c : Fin S.card → Fin S.card → K, (∀ a b, ‖c a b‖ ≤ 1) ∧ ∀ x ∈ S, ∀ y ∈ S,
        ev H ![x, y] = ∑ a, ∑ b, c a b * x ^ (a : ℕ) * y ^ (b : ℕ) := by
  intro K _ _ _ S H hS hH
  rcases S.eq_empty_or_nonempty with rfl | hne
  · exact ⟨fun _ _ => 0, by simp, by simp⟩
  obtain ⟨x0, hx0, hmax⟩ := S.exists_max_image (fun x => ‖x‖) hne
  set θ := ‖x0‖
  have h0 : 0 ≤ θ := norm_nonneg _
  have h1 : θ < 1 := hS x0 hx0
  choose Q hQ0 hQ1 hQ2 using
    exists_pow_eq_interpolation θ h0 h1.le S hmax hne.card_pos
  have hev : ∀ k, ∀ x ∈ S, x ^ k = ∑ a : Fin S.card, (Q k).coeff a * x ^ (a : ℕ) := by
    intro k x hx
    rw [← hQ2 k x hx, Fin.sum_univ_eq_sum_range (fun a => (Q k).coeff a * x ^ a)]
    apply eval_eq_sum_range'
    have := hne.card_pos
    have h : (Q k).natDegree ≤ S.card - 1 :=
      natDegree_le_iff_coeff_eq_zero.2 (fun a ha => hQ0 k a (by omega))
    omega
  have hg : ∀ a : ℕ, Summable (fun k : ℕ => θ ^ (k - a)) := by
    intro a
    rw [← summable_nat_add_iff a]
    simpa using summable_geometric_of_lt_one h0 h1
  let T : ℕ → ℕ → (Fin 2 →₀ ℕ) → K := fun a b ν =>
    MvPowerSeries.coeff ν H * (Q (ν 0)).coeff a * (Q (ν 1)).coeff b
  have hT : ∀ a b ν, ‖T a b ν‖ ≤ θ ^ (ν 0 - a) * θ ^ (ν 1 - b) := by
    intro a b ν
    simp only [T, norm_mul]
    refine mul_le_mul ?_ (hQ1 _ _) (norm_nonneg _) (by positivity)
    exact (mul_le_of_le_one_left (norm_nonneg _) (hH ν)).trans (hQ1 _ _)
  have hsum : ∀ a b, Summable (T a b) := by
    intro a b
    refine Summable.of_norm_bounded ?_ (hT a b)
    have h : Summable (fun p : ℕ × ℕ => θ ^ (p.1 - a) * θ ^ (p.2 - b)) :=
      Summable.mul_of_nonneg (f := fun k : ℕ => θ ^ (k - a)) (g := fun k : ℕ => θ ^ (k - b))
        (hg a) (hg b) (fun _ => pow_nonneg h0 _) (fun _ => pow_nonneg h0 _)
    have hinj : Function.Injective (fun ν : Fin 2 →₀ ℕ => (ν 0, ν 1)) := by
      intro ν μ h
      simp only [Prod.mk.injEq] at h
      ext i
      fin_cases i
      · exact h.1
      · exact h.2
    have h' := h.comp_injective hinj
    simpa only [Function.comp_def] using h'
  refine ⟨fun a b => ∑' ν, T a b ν, fun a b => ?_, fun x hx y hy => ?_⟩
  · refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg zero_le_one (fun ν => ?_)
    exact (hT a b ν).trans (mul_le_one₀ (pow_le_one₀ h0 h1.le) (by positivity)
      (pow_le_one₀ h0 h1.le))
  · have h : HasSum (fun ν => ∑ a : Fin S.card, ∑ b : Fin S.card,
        T a b ν * x ^ (a : ℕ) * y ^ (b : ℕ))
        (∑ a : Fin S.card, ∑ b : Fin S.card, (∑' ν, T a b ν) * x ^ (a : ℕ) * y ^ (b : ℕ)) :=
      hasSum_sum fun a _ => hasSum_sum fun b _ =>
        ((hsum a b).hasSum.mul_right _).mul_right _
    rw [← h.tsum_eq, ev]
    congr 1
    funext ν
    rw [Fin.prod_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [hev (ν 0) x hx, hev (ν 1) y hy, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [T]
    ring

end GlobalTheory.ConvSer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsPositiveAdd
section
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.LeastExponentCompare
open NumberField NumberField.IsCMField TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.BalancedHermitianSpace

set_option autoImplicit false in
open NumberField NumberField.IsCMField TensorProduct in

theorem _root_.GlobalTheory.LeastExponentCompare.isCMField_of_conj (E : Type) [Field E] [NumberField E] (cj : E → E)
    (h : ∀ (φ : E →+* ℂ) (z : E), φ (cj z) = star (φ z)) (hne : ∃ z : E, cj z ≠ z) :
    IsCMField E := by
  let φ₀ : E →+* ℂ := (Classical.arbitrary (InfinitePlace E)).embedding
  have inj := φ₀.injective
  have hadd : ∀ a b, cj (a + b) = cj a + cj b := fun a b =>
    inj (by rw [h, map_add, map_add, h, h, star_add])
  have hmul : ∀ a b, cj (a * b) = cj a * cj b := fun a b =>
    inj (by rw [h, map_mul, map_mul, h, h, star_mul'])
  have hinv : ∀ z, cj (cj z) = z := fun z => inj (by rw [h, h, star_star])
  let e : E ≃+* E :=
    { toFun := cj, invFun := cj, left_inv := hinv, right_inv := hinv,
      map_mul' := hmul, map_add' := hadd }
  let σ : E ≃ₐ[ℚ] E := e.toRatAlgEquiv
  have hσ : ∀ z, σ z = cj z := fun _ => rfl
  have hsq : σ ^ 2 = 1 := AlgEquiv.ext fun z => by
    rw [pow_two, AlgEquiv.mul_apply, hσ, hσ, hinv, AlgEquiv.one_apply]
  have hne1 : σ ≠ 1 := by
    obtain ⟨z, hz⟩ := hne
    intro h1
    exact hz (by rw [← hσ, h1, AlgEquiv.one_apply])
  have hord : orderOf σ = 2 := orderOf_eq_prime hsq hne1
  have hfix : ∀ x, x ∈ IntermediateField.fixedField (Subgroup.zpowers σ) ↔ cj x = x := by
    intro x
    rw [IntermediateField.mem_fixedField_iff]
    refine ⟨fun hx => hx σ (Subgroup.mem_zpowers σ), fun hx f hf => ?_⟩
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hf
    clear hf
    have hσx : σ x = x := hx
    have hσx' : σ⁻¹ x = x := by
      calc σ⁻¹ x = (σ⁻¹ * σ) x := by rw [AlgEquiv.mul_apply, hσx]
        _ = x := by rw [inv_mul_cancel, AlgEquiv.one_apply]
    induction n using Int.induction_on with
    | zero => simp
    | succ k ih => rw [zpow_add_one, AlgEquiv.mul_apply, hσx, ih]
    | pred k ih => rw [zpow_sub_one, AlgEquiv.mul_apply, hσx', ih]
  have hS : maximalRealSubfield E =
      (IntermediateField.fixedField (Subgroup.zpowers σ)).toSubfield := by
    ext x
    rw [mem_maximalRealSubfield_iff, IntermediateField.mem_toSubfield, hfix]
    exact ⟨fun hx => inj ((h φ₀ x).trans (hx φ₀)), fun hx φ => by rw [← h φ x, hx]⟩
  have hfin : Module.finrank (maximalRealSubfield E) E = 2 := by
    rw [hS]
    exact (IntermediateField.finrank_fixedField_eq_card (Subgroup.zpowers σ)).trans
      (by rw [Nat.card_zpowers, hord])
  haveI : IsTotallyComplex E := ⟨fun v => InfinitePlace.not_isReal_iff_isComplex.mp fun hv => by
    rw [InfinitePlace.isReal_iff, ComplexEmbedding.isReal_iff] at hv
    obtain ⟨z, hz⟩ := hne
    exact hz (v.embedding.injective ((h _ z).trans (RingHom.congr_fun hv z)))⟩
  haveI : Algebra.IsQuadraticExtension (maximalRealSubfield E) E := ⟨hfin⟩
  exact ⟨⟩

set_option autoImplicit false in
open NumberField NumberField.IsCMField TensorProduct in

theorem _root_.GlobalTheory.LeastExponentCompare.conj_iff (E : Type) [Field E] [NumberField E]
    (cj : E → E) :
    ((∀ (φ : E →+* ℂ) (z : E), φ (cj z) = star (φ z)) ∧ ∃ z : E, cj z ≠ z) ↔
      ∃ _ : IsCMField E, cj = fun z => complexConj E z := by
  constructor
  · rintro ⟨h, hne⟩
    haveI := _root_.GlobalTheory.LeastExponentCompare.isCMField_of_conj E cj h hne
    refine ⟨this, funext fun z => ?_⟩
    let φ₀ : E →+* ℂ := (Classical.arbitrary (InfinitePlace E)).embedding
    exact φ₀.injective (by rw [h, complexEmbedding_complexConj, RCLike.star_def])
  · rintro ⟨_, rfl⟩
    refine ⟨fun φ z => by rw [complexEmbedding_complexConj, RCLike.star_def], ?_⟩
    by_contra hall
    push_neg at hall
    exact complexConj_ne_one E (AlgEquiv.ext hall)

section Comparison₂
variable {Y : Type} [AddCommGroup Y] [Module.Free ℤ Y] [Module.Finite ℤ Y]

def IntegralAreSums (S : Submodule ℝ (Bil Y)) : Prop :=
  ∀ l : S →ₗ[ℝ] ℝ, (∀ β : S, (∀ a c, ∃ z : ℤ, (β : Bil Y) a c = z) → ∃ z : ℤ, l β = z) →
    ∃ (m : ℕ) (x x' : Fin m → Y), ∀ β : S, l β = ∑ i, (β : Bil Y) (x i) (x' i)

end Comparison₂

section AtLattice
variable (E : Type) [Field E] [NumberField E] {Y : Type} [AddCommGroup Y] [Module (𝓞 E) Y]

def SpanBound (S : Submodule ℝ (Bil Y)) (φ : S → ℝ) (w : 𝓞 E) : Prop :=
  ∀ (β : S), (∀ a, 0 ≤ (β : Bil Y) a a) → ∀ (k : ℕ) (x : Fin k → Y),
    (∀ y : Y, ∃ n : ℕ, 0 < n ∧ n • y ∈ Submodule.span (𝓞 E) (Set.range x)) →
    φ β ≤ ∑ b, (β : Bil Y) (w • x b) (x b)

def MinimaBound (S : Submodule ℝ (Bil Y)) (φ : S → ℝ) : Prop :=
  ∀ (β : S), (∃ (ι : Type) (_ : Fintype ι) (b : Module.Basis ι ℤ Y),
      (Matrix.of fun i j => (β : Bil Y) (b i) (b j)).PosDef) →
    ∃ v : Fin (Module.finrank ℤ Y) → Y, LinearIndependent ℤ v ∧
      ∀ i, (β : Bil Y) (v i) (v i) / 2 ≤
        (|(NumberField.discr E : ℝ)| ^ ((2 : ℝ) / Module.finrank ℚ E)) /
            (2 * Module.finrank ℚ E) * (Module.finrank ℤ Y : ℝ) ^ 2 * φ β

variable [IsCMField E]

end AtLattice

section Families

abbrev SpaceRule : Type 1 :=
  ∀ (E : Type) [Field E] [NumberField E] (_ : E → E) (Y : Type) [AddCommGroup Y] [Module (𝓞 E) Y],
    Submodule ℝ (Bil Y)

abbrev ValueRule (S : SpaceRule) : Type 1 :=
  ∀ (E : Type) [Field E] [NumberField E] (cj : E → E) (Y : Type) [AddCommGroup Y] [Module (𝓞 E) Y],
    S E cj Y → ℝ

def Matches (S : SpaceRule) (φ : ValueRule S) : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Y : Type) [AddCommGroup Y] [Module (𝓞 E) Y],
    IsBalancedSpace E (S E (fun z => complexConj E z) Y) ∧
      φ E (fun z => complexConj E z) Y = leastExponent (S E (fun z => complexConj E z) Y)

def ForAllLattices (P : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Y : Type) [AddCommGroup Y]
    [Module (𝓞 E) Y], Submodule ℝ (Bil Y) → Prop) : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], HasTraceOne E →
    ∀ (Y : Type) [AddCommGroup Y] [Module (𝓞 E) Y] [Module.Free ℤ Y] [Module.Finite ℤ Y]
      (S : Submodule ℝ (Bil Y)), IsBalancedSpace E S → P E Y S

def SpanAll (S : SpaceRule) (φ : ValueRule S) : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (cj : E → E),
    (∀ c : 𝓞 E, ∃ c' : 𝓞 E, (c' : E) = cj c) →
    ∀ (Y : Type) [AddCommGroup Y] [Module (𝓞 E) Y] (w : 𝓞 E), (w : E) + cj w = 1 →
      SpanBound E (S E cj Y) (φ E cj Y) w

def SpanCM (S : SpaceRule) (φ : ValueRule S) : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Y : Type) [AddCommGroup Y] [Module (𝓞 E) Y]
    [Module.Free ℤ Y] [Module.Finite ℤ Y] (w : 𝓞 E), (w : E) + complexConj E w = 1 →
      SpanBound E (S E (fun z => complexConj E z) Y) (φ E (fun z => complexConj E z) Y) w

def MinimaAll (S : SpaceRule) (φ : ValueRule S) : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (cj : E → E),
    (∀ (σ : E →+* ℂ) (z : E), σ (cj z) = star (σ z)) → (∃ z : E, cj z ≠ z) →
    ∀ (w : 𝓞 E), (w : E) + cj w = 1 →
    ∀ (Y : Type) [AddCommGroup Y] [Module (𝓞 E) Y] [Module.Free ℤ Y] [Module.Finite ℤ Y],
      MinimaBound E (S E cj Y) (φ E cj Y)

def SumsAll (S : SpaceRule) : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (cj : E → E) (Y : Type) [AddCommGroup Y]
    [Module (𝓞 E) Y] [Module.Free ℤ Y] [Module.Finite ℤ Y], IntegralAreSums (S E cj Y)

def SumsCM (S : SpaceRule) : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], HasTraceOne E → ∀ (Y : Type) [AddCommGroup Y]
    [Module (𝓞 E) Y] [Module.Free ℤ Y] [Module.Finite ℤ Y],
      IntegralAreSums (S E (fun z => complexConj E z) Y)

variable {S : SpaceRule} {φ : ValueRule S}

end Families

end GlobalTheory.LeastExponentCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsSeparatingModPrimePow
section
namespace GlobalTheory

private lemma ringHom_pow_sub_mem_span {A O : Type} [CommRing A] [CommRing O] (g : ℕ)
    (hA : ∀ x : A, x ^ g - x ∈ Ideal.span {(g : A)}) (σ : A →+* O) (x : A) :
    σ x ^ g - σ x ∈ Ideal.span {(g : O)} := by
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp (hA x)
  exact Ideal.mem_span_singleton'.mpr
    ⟨σ c, by rw [← map_natCast σ g, ← map_mul, hc, map_sub, map_pow]⟩

theorem _root_.GlobalTheory.exists_separating_mod_prime_pow : ∀ (A O : Type) [CommRing A] [Module.Finite ℤ A] [CommRing O] [IsLocalRing O] (g : ℕ), g.Prime → ¬ IsUnit (g : O) → (∀ x : A, x ^ g - x ∈ Ideal.span {(g : A)}) → ∀ (T : Type) [Fintype T] [DecidableEq T] (σ : T → A →+* O), Function.Injective σ → ∀ (K : ℕ) (t₀ : T), ∃ e : A, ∀ t, σ t e - (if t = t₀ then 1 else 0) ∈ Ideal.span {(g : O) ^ K} := by
  intro A O _ _ _ _ g hg hgO hA T _ _ σ hσ K t₀
  have h2 : 2 ≤ g := hg.two_le
  have hgm : (g : O) ∈ IsLocalRing.maximalIdeal O :=
    (IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hgO)
  have hspan : Ideal.span {(g : O)} ≤ IsLocalRing.maximalIdeal O :=
    (Ideal.span_singleton_le_iff_mem _).mpr hgm
  have hb : ∀ t, t ≠ t₀ → ∃ b : A, σ t b ∈ Ideal.span {(g : O)} ∧ IsUnit (σ t₀ b) := by
    intro t ht
    obtain ⟨a, ha⟩ := _root_.GlobalTheory.exists_isUnit_sub_of_ringHom_ne A O g hg hgO hA (σ t₀) (σ t)
      (fun h => ht (hσ h).symm)
    obtain ⟨⟨i, hi⟩, -⟩ := _root_.GlobalTheory.hom_value_congruent_int_mod_prime A O g hg hgO hA (σ t) a
    refine ⟨a - (i : A), by rwa [map_sub, map_intCast], ?_⟩
    rw [map_sub, map_intCast]
    by_contra hn
    have h1 : σ t₀ a - (i : O) ∈ IsLocalRing.maximalIdeal O :=
      (IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hn)
    have h3 : σ t₀ a - σ t a ∈ IsLocalRing.maximalIdeal O := by
      have := Ideal.sub_mem _ h1 (hspan hi)
      rwa [sub_sub_sub_cancel_right] at this
    exact (mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp h3)) ha
  choose! b hb1 hb2 using hb
  obtain ⟨c, hc0, hct⟩ : ∃ c : A, IsUnit (σ t₀ c) ∧ ∀ t, t ≠ t₀ → σ t c ∈ Ideal.span {(g : O)} := by
    refine ⟨∏ t ∈ Finset.univ.erase t₀, b t, ?_, fun t ht => ?_⟩
    · rw [map_prod]
      exact Finset.prod_induction _ IsUnit (fun _ _ => IsUnit.mul) isUnit_one
        (fun t ht => hb2 t (Finset.ne_of_mem_erase ht))
    · rw [map_prod, ← Finset.mul_prod_erase _ _ (Finset.mem_erase.mpr ⟨ht, Finset.mem_univ t⟩)]
      exact Ideal.mul_mem_right _ _ (hb1 t ht)
  obtain ⟨f, hf0, hft⟩ : ∃ f : A, σ t₀ f - 1 ∈ Ideal.span {(g : O)} ∧
      ∀ t, t ≠ t₀ → σ t f ∈ Ideal.span {(g : O)} := by
    refine ⟨c ^ (g - 1), ?_, fun t ht => ?_⟩
    · rw [map_pow]
      have hz : σ t₀ c * (σ t₀ c ^ (g - 1) - 1) = σ t₀ c ^ g - σ t₀ c := by
        rw [mul_sub, mul_one, ← pow_succ']
        congr 2
        omega
      have : σ t₀ c ^ (g - 1) - 1 = (σ t₀ c ^ g - σ t₀ c) * ↑hc0.unit⁻¹ := by
        rw [← hz, mul_comm (σ t₀ c), mul_assoc, IsUnit.mul_val_inv, mul_one]
      rw [this]
      exact Ideal.mul_mem_right _ _ (ringHom_pow_sub_mem_span g hA (σ t₀) c)
    · rw [map_pow]
      exact Ideal.pow_mem_of_mem _ (hct t ht) _ (by omega)
  refine ⟨1 - (1 - f ^ K) ^ K, fun t => ?_⟩
  rw [← Ideal.span_singleton_pow]
  split_ifs with ht
  · subst ht
    simp only [map_sub, map_one, map_pow]
    have h1 : 1 - σ t f ^ K ∈ Ideal.span {(g : O)} := by
      rw [← Ideal.Quotient.eq_zero_iff_mem] at hf0 ⊢
      rw [map_sub, map_one, map_pow]
      rw [map_sub, map_one, sub_eq_zero] at hf0
      rw [hf0, one_pow, sub_self]
    have : 1 - (1 - σ t f ^ K) ^ K - 1 = -((1 - σ t f ^ K) ^ K) := by ring
    rw [this]
    exact neg_mem (Ideal.pow_mem_pow h1 K)
  · simp only [map_sub, map_one, map_pow]
    have hw : σ t f ^ K ∈ Ideal.span {(g : O)} ^ K := Ideal.pow_mem_pow (hft t ht) K
    have hgs := geom_sum_mul (1 - σ t f ^ K) K
    have : 1 - (1 - σ t f ^ K) ^ K - 0 =
        (∑ i ∈ Finset.range K, (1 - σ t f ^ K) ^ i) * σ t f ^ K := by
      linear_combination hgs
    rw [this]
    exact Ideal.mul_mem_left _ _ hw

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.InterlacedShiftedDistanceBracketBound
section
open Finset

namespace GlobalTheory.BracketBound

theorem main : ∀ (k r l : ℕ) (b c Y e : ℝ) (lam v : ℕ → ℝ), 1 ≤ k → 1 ≤ c → c + 2 ≤ b → (k : ℝ) ≤ b → |Y| ≤ b → 0 ≤ e → e ≤ 1 → (∀ s ∈ Finset.Icc 1 (k + 2 * r + 1), |lam s| ≤ b) → (∀ s : ℕ, 1 ≤ s → s + 1 ≤ k - 1 → lam (s + 1) + 2 * c ≤ lam s) → (∀ s : ℕ, 1 ≤ s → s + 1 ≤ k → (s ≠ l → lam s + 1 / 2 ≤ v s) ∧ (s + 1 ≠ l → v (s + 1) + 1 / 2 ≤ lam s)) → (∀ i ∈ Finset.Icc 1 k, 1 ≤ |Y + 1 / 2 + v i|) → ∏ s ∈ Finset.Icc 1 (k + 2 * r + 1), (|Y + e + lam s| + c) ≤ b ^ (4 * r + 10) * ∏ i ∈ Finset.Icc 1 k, |Y + 1 / 2 + v i| := by
  intro k r l b c Y e lam v hk hc hcb hkb hY he0 he1 hlam hgap hint hW
  have hb3 : 3 ≤ b := by linarith
  have hb0 : 0 ≤ b := by linarith
  have h3b : 3 * b ≤ b ^ 2 := by nlinarith
  have ha0 : ∀ s, 0 ≤ |Y + e + lam s| + c := fun s => by positivity
  have ha1 : ∀ s, |Y + e + lam s| + c ≤ |lam s + Y| + 1 + c := fun s => by
    have h1 : |Y + e + lam s| ≤ |lam s + Y| + |e| := by
      have : Y + e + lam s = (lam s + Y) + e := by ring
      rw [this]; exact abs_add_le _ _
    rw [abs_of_nonneg he0] at h1
    linarith
  have ha2 : ∀ s ∈ Finset.Icc 1 (k + 2 * r + 1), |Y + e + lam s| + c ≤ 3 * b := fun s hs => by
    have h1 := ha1 s
    have h2 := abs_add_le (lam s) Y
    have h3 := hlam s hs
    linarith
  have hsplit : Finset.Icc 1 (k + 2 * r + 1) = Finset.Icc 1 (k - 1) ∪ Finset.Icc k (k + 2 * r + 1) := by
    ext x; simp only [Finset.mem_union, Finset.mem_Icc]; omega
  have hdisj : Disjoint (Finset.Icc 1 (k - 1)) (Finset.Icc k (k + 2 * r + 1)) := by
    rw [Finset.disjoint_left]; intro x; simp only [Finset.mem_Icc]; omega
  have hWp : 0 ≤ ∏ i ∈ Finset.Icc 1 k, |Y + 1 / 2 + v i| :=
    Finset.prod_nonneg fun i _ => abs_nonneg _
  have hpair := GlobalTheory.prod_le_of_interlacing_pairing k l c (3 * b) Y lam v (fun s => |Y + e + lam s| + c)
    (by linarith) (by linarith) (fun s h1 h2 => by have := hgap s h1 h2; linarith) hint hW
    (fun s hs => ⟨ha0 s, ha1 s, ha2 s (by rw [hsplit]; exact Finset.mem_union_left _ hs)⟩)
  have hcloud := GlobalTheory.CloudProd.main k c (-Y) lam hk hc hgap
  simp only [sub_neg_eq_add] at hcloud
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have h4 : ((2 + c) * (k : ℝ)) ^ 2 ≤ b ^ 4 := by
    have h1 : (2 + c) * (k : ℝ) ≤ b * b := mul_le_mul (by linarith) hkb hk0 hb0
    calc ((2 + c) * (k : ℝ)) ^ 2 ≤ (b * b) ^ 2 :=
          pow_le_pow_left₀ (by positivity) h1 2
      _ = b ^ 4 := by ring
  have hR0 : 0 ≤ ∏ s ∈ Finset.Icc 1 (k - 1), (1 + (1 + c) / max |lam s + Y| 1) :=
    Finset.prod_nonneg fun s _ => by positivity
  have hC : ∏ s ∈ Finset.Icc 1 (k - 1), (|Y + e + lam s| + c) ≤
      b ^ 2 * b ^ 4 * ∏ i ∈ Finset.Icc 1 k, |Y + 1 / 2 + v i| := by
    refine hpair.trans (mul_le_mul_of_nonneg_right ?_ hWp)
    exact mul_le_mul h3b (hcloud.trans h4) hR0 (by positivity)
  have hN : ∏ s ∈ Finset.Icc k (k + 2 * r + 1), (|Y + e + lam s| + c) ≤ (b ^ 2) ^ (2 * r + 2) := by
    calc ∏ s ∈ Finset.Icc k (k + 2 * r + 1), (|Y + e + lam s| + c)
        ≤ ∏ _s ∈ Finset.Icc k (k + 2 * r + 1), b ^ 2 :=
          Finset.prod_le_prod (fun s _ => ha0 s) (fun s hs =>
            (ha2 s (by rw [hsplit]; exact Finset.mem_union_right _ hs)).trans h3b)
      _ = (b ^ 2) ^ (2 * r + 2) := by
          rw [Finset.prod_const, Nat.card_Icc]
          congr 1; omega
  rw [hsplit, Finset.prod_union hdisj]
  calc _ ≤ (b ^ 2 * b ^ 4 * ∏ i ∈ Finset.Icc 1 k, |Y + 1 / 2 + v i|) * (b ^ 2) ^ (2 * r + 2) :=
        mul_le_mul hC hN (Finset.prod_nonneg fun s _ => ha0 s) (by positivity)
    _ = b ^ (4 * r + 10) * ∏ i ∈ Finset.Icc 1 k, |Y + 1 / 2 + v i| := by ring

end GlobalTheory.BracketBound
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.WignerExtremeNeZero
section
open Finset

namespace GlobalTheory.WigSh

theorem wigner_den_ne_zero {n : ℕ} (L : Fin (n+1) → ℤ) (l : Fin (n+1)) (hL : StrictAnti L) :
    (∏ j ∈ univ.erase l, ((L j : ℝ) - (L l : ℝ))) ≠ 0 := by
  rw [Finset.prod_ne_zero_iff]
  intro j hj
  have h1 : j ≠ l := (Finset.mem_erase.mp hj).1
  have h2 : L j ≠ L l := fun h => h1 (hL.injective h)
  exact sub_ne_zero.mpr (by exact_mod_cast h2)

theorem wigner_extreme_ne_zero : ∀ (n : ℕ) (L : Fin (n+1) → ℤ) (l : Fin (n+1)), StrictAnti L → ((∀ j, L j ≠ L l + 1) → GlobalTheory.WigSh.wP L (fun j : Fin n => L j.castSucc) l ≠ 0) ∧ ((∀ j, L j ≠ L l - 1) → GlobalTheory.WigSh.wM L (fun j : Fin n => L j.succ + 1) l ≠ 0) := by
  intro n L l hL
  refine ⟨fun h => ?_, fun h => ?_⟩
  · unfold wP
    refine div_ne_zero ?_ (wigner_den_ne_zero L l hL)
    rw [Finset.prod_ne_zero_iff]
    intro j _
    have h1 : L j.castSucc - 1 - L l ≠ 0 := by
      have := h j.castSucc
      omega
    exact_mod_cast h1
  · unfold wM
    refine div_ne_zero ?_ (wigner_den_ne_zero L l hL)
    rw [Finset.prod_ne_zero_iff]
    intro j _
    have h1 : L j.succ + 1 - L l ≠ 0 := by
      have := h j.succ
      omega
    exact_mod_cast h1

end GlobalTheory.WigSh
end

