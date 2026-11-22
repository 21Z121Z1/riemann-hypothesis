import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIndexOfGammaLe
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0011

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerExtensionPrimeNotMapComapLeSq
section
open GlobalTheory.NeedB Polynomial

namespace GlobalTheory

theorem kummer_aeval_mem_integralClosure {A₀ F E : Type} [CommRing A₀] [Field F] [Field E] [Algebra A₀ F]
    [Algebra F E] [Algebra A₀ E] [IsScalarTower A₀ F E] {x : E} (hx : IsIntegral A₀ x)
    (p : (integralClosure A₀ F)[X]) : IsIntegral A₀ (aeval x p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add]; exact hp.add hq
  | monomial n c =>
    rw [aeval_monomial]
    refine IsIntegral.mul ?_ (hx.pow n)
    have : algebraMap (integralClosure A₀ F) E c = algebraMap F E (c : F) := rfl
    rw [this]
    exact c.2.map (IsScalarTower.toAlgHom A₀ F E)

theorem kummer_dual_step (A₀ K₀ F E : Type) [CommRing A₀] [IsDomain A₀] [Field K₀] [Algebra A₀ K₀]
    [IsFractionRing A₀ K₀] [Field F] [Field E] [Algebra K₀ F] [Algebra F E] [Algebra K₀ E]
    [IsScalarTower K₀ F E] [Algebra A₀ F] [Algebra A₀ E] [IsScalarTower A₀ K₀ F] [IsScalarTower A₀ K₀ E]
    [IsScalarTower A₀ F E] [FiniteDimensional K₀ F] [FiniteDimensional F E] [CharZero K₀]
    (N : ℕ) (hN : IsUnit (N : A₀)) (x : E) (u : A₀ˣ) (hx : x ^ N = algebraMap A₀ E u)
    (hgen : Algebra.adjoin F {x} = ⊤)
    (hF : ∀ y : F, (∀ z : F, IsIntegral A₀ z → Algebra.trace K₀ F (y * z) ∈ (algebraMap A₀ K₀).range) →
      IsIntegral A₀ y) :
    ∀ y : E, (∀ z : E, IsIntegral A₀ z → Algebra.trace K₀ E (y * z) ∈ (algebraMap A₀ K₀).range) →
      IsIntegral A₀ y := by
  intro y hy
  haveI : CharZero F := charZero_of_injective_algebraMap (algebraMap K₀ F).injective
  haveI : CharZero E := charZero_of_injective_algebraMap (algebraMap F E).injective
  haveI : Algebra.IsSeparable F E := inferInstance
  let C := integralClosure A₀ F
  haveI : IsFractionRing C F := IsIntegralClosure.isFractionRing_of_finite_extension A₀ K₀ F C
  haveI : IsIntegrallyClosed C := integralClosure.isIntegrallyClosedOfFiniteExtension K₀
  have hN0 : N ≠ 0 := by
    rintro rfl
    simp at hN
  have hxA : IsIntegral A₀ x := by
    refine ⟨X ^ N - Polynomial.C (u : A₀), monic_X_pow_sub_C _ hN0, ?_⟩
    simp [eval₂_sub, hx]
  have hxC : IsIntegral C x := hxA.tower_top
  have key := traceForm_dualSubmodule_adjoin C F hgen hxC

  have hymem : y ∈ (Algebra.traceForm F E).dualSubmodule (Subalgebra.toSubmodule (Algebra.adjoin C {x})) := by
    rw [LinearMap.BilinForm.mem_dualSubmodule]
    intro z hz
    rw [Subalgebra.mem_toSubmodule, Algebra.adjoin_singleton_eq_range_aeval] at hz
    obtain ⟨p, rfl⟩ := hz
    have hzA : IsIntegral A₀ (aeval x p) := kummer_aeval_mem_integralClosure hxA p
    rw [Algebra.traceForm_apply]
    have hw : IsIntegral A₀ (Algebra.trace F E (y * aeval x p)) := by
      apply hF
      intro c hc
      have : Algebra.trace F E (y * aeval x p) * c =
          Algebra.trace F E (y * (aeval x p * algebraMap F E c)) := by
        rw [mul_comm _ c, ← smul_eq_mul, ← LinearMap.map_smul, Algebra.smul_def]
        ring_nf
      rw [this, Algebra.trace_trace]
      exact hy _ (hzA.mul (hc.map (IsScalarTower.toAlgHom A₀ F E)))
    exact Submodule.mem_one.mpr ⟨⟨_, hw⟩, rfl⟩
  rw [key, Submodule.mem_smul_pointwise_iff_exists] at hymem
  obtain ⟨z, hz, rfl⟩ := hymem
  rw [Subalgebra.mem_toSubmodule, Algebra.adjoin_singleton_eq_range_aeval] at hz
  obtain ⟨q, rfl⟩ := hz
  have hmin : minpoly F x = map (algebraMap C F) (minpoly C x) :=
    minpoly.isIntegrallyClosed_eq_field_fractions' F hxC
  have hdvd : minpoly C x ∣ X ^ N - Polynomial.C (algebraMap A₀ C u) := by
    apply minpoly.isIntegrallyClosed_dvd hxC
    simp [hx, ← IsScalarTower.algebraMap_apply]
  obtain ⟨g, hg⟩ := hdvd
  have hder := congrArg (fun p => aeval x (derivative p)) hg
  simp only [derivative_sub, derivative_X_pow, derivative_C, sub_zero, derivative_mul, map_add, map_mul,
    minpoly.aeval, zero_mul, add_zero] at hder
  set d := aeval x (derivative (minpoly C x))
  let v : A₀ˣ := hN.unit * u
  have hinv : (aeval x (derivative (minpoly F x)))⁻¹ = aeval x g * x * algebraMap A₀ E (↑v⁻¹ : A₀) := by
    rw [hmin, derivative_map, aeval_map_algebraMap]
    apply inv_eq_of_mul_eq_one_right
    change d * _ = 1
    have h1 : d * aeval x g = (N : E) * x ^ (N - 1) := by rw [← hder]; simp
    have hv : ((v : A₀)) = (N : A₀) * u := by simp [v]
    calc d * (aeval x g * x * algebraMap A₀ E ↑v⁻¹)
        = (N : E) * (x ^ (N - 1) * x) * algebraMap A₀ E ↑v⁻¹ := by
          rw [← mul_assoc, ← mul_assoc, h1]; ring
      _ = algebraMap A₀ E ((v : A₀) * ↑v⁻¹) := by
        rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hN0), hx, map_mul, hv, map_mul,
          map_natCast]
      _ = 1 := by simp
  rw [smul_eq_mul, hinv]
  refine IsIntegral.mul (IsIntegral.mul (kummer_aeval_mem_integralClosure hxA g) hxA) isIntegral_algebraMap
    |>.mul (kummer_aeval_mem_integralClosure hxA q)

end GlobalTheory

namespace GlobalTheory

theorem kummer_dual_induction (A₀ K₀ : Type) [CommRing A₀] [IsDomain A₀] [Field K₀] [Algebra A₀ K₀]
    [IsFractionRing A₀ K₀] [CharZero K₀] (N : ℕ) (hN : IsUnit (N : A₀)) :
    ∀ (n : ℕ) (E : Type) [Field E] [Algebra K₀ E] [FiniteDimensional K₀ E] [Algebra A₀ E]
      [IsScalarTower A₀ K₀ E] (s : Finset E), s.card = n → IntermediateField.adjoin K₀ (s : Set E) = ⊤ →
      (∀ x ∈ s, ∃ u : A₀ˣ, x ^ N = algebraMap A₀ E u) →
      ∀ y : E, (∀ z : E, IsIntegral A₀ z → Algebra.trace K₀ E (y * z) ∈ (algebraMap A₀ K₀).range) →
        IsIntegral A₀ y := by
  intro n
  induction n with
  | zero =>
    intro E _ _ _ _ _ s hs hadj _ y hy
    rw [Finset.card_eq_zero] at hs
    subst hs
    rw [Finset.coe_empty, IntermediateField.adjoin_empty] at hadj
    have hr : Module.finrank K₀ E = 1 := IntermediateField.bot_eq_top_iff_finrank_eq_one.mp hadj
    have hyb : y ∈ (⊥ : IntermediateField K₀ E) := hadj ▸ IntermediateField.mem_top
    obtain ⟨k, rfl⟩ := IntermediateField.mem_bot.mp hyb
    obtain ⟨a, ha⟩ := hy 1 isIntegral_one
    rw [mul_one, Algebra.trace_algebraMap, hr, one_smul] at ha
    rw [← ha, ← IsScalarTower.algebraMap_apply]
    exact isIntegral_algebraMap
  | succ n ih =>
    intro E _ _ _ _ _ s hs hadj hu y hy
    classical
    obtain ⟨x, hxs⟩ : s.Nonempty := Finset.card_pos.mp (by omega)
    let t := s.erase x
    let F := IntermediateField.adjoin K₀ (t : Set E)
    let s' : Finset F := t.subtype (· ∈ F)
    have hs' : s'.card = n := by
      rw [Finset.card_subtype, Finset.filter_true_of_mem (s := t) (p := (· ∈ F))
        (fun y hy => IntermediateField.subset_adjoin K₀ (t : Set E) hy),
        Finset.card_erase_of_mem hxs, hs]
      rfl
    have hadj' : IntermediateField.adjoin K₀ (s' : Set F) = ⊤ := by
      apply IntermediateField.lift_injective
      rw [IntermediateField.lift_adjoin, IntermediateField.lift_top]
      change _ = IntermediateField.adjoin K₀ (t : Set E)
      congr 1
      ext w
      constructor
      · rintro ⟨w, hw, rfl⟩
        exact Finset.mem_subtype.mp hw
      · intro hw
        exact ⟨⟨w, IntermediateField.subset_adjoin K₀ _ hw⟩, Finset.mem_subtype.mpr hw, rfl⟩
    have hu' : ∀ y ∈ s', ∃ u : A₀ˣ, y ^ N = algebraMap A₀ F u := by
      intro y hy
      obtain ⟨u, hu⟩ := hu y (Finset.mem_of_mem_erase (Finset.mem_subtype.mp hy))
      exact ⟨u, Subtype.ext hu⟩
    have hF := ih F s' hs' hadj' hu'
    obtain ⟨u, hux⟩ := hu x hxs
    have hgen : Algebra.adjoin F {x} = ⊤ := by
      have h1 : IntermediateField.adjoin F ({x} : Set E) = ⊤ := by
        apply IntermediateField.restrictScalars_injective K₀
        rw [IntermediateField.adjoin_adjoin_left, IntermediateField.restrictScalars_top, ← hadj]
        congr 1
        rw [Set.union_singleton, ← Finset.coe_insert, Finset.insert_erase hxs]
      rw [← IntermediateField.adjoin_toSubalgebra_of_isAlgebraic
        (fun z _ => Algebra.IsAlgebraic.isAlgebraic z), h1]
      rfl
    haveI : IsScalarTower A₀ F E := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    exact kummer_dual_step A₀ K₀ F E N hN x u hux hgen hF y hy

end GlobalTheory

namespace GlobalTheory

theorem kummer_not_map_comap_le_sq :
    ∀ (A₀ K₀ E : Type) [CommRing A₀] [IsDedekindDomain A₀] [Field K₀] [CharZero K₀] [Algebra A₀ K₀]
      [IsFractionRing A₀ K₀] [Field E] [Algebra K₀ E] [FiniteDimensional K₀ E] [Algebra A₀ E]
      [IsScalarTower A₀ K₀ E] (N : ℕ), IsUnit (N : A₀) →
      ∀ s : Finset E, IntermediateField.adjoin K₀ (s : Set E) = ⊤ →
      (∀ x ∈ s, ∃ u : A₀ˣ, x ^ N = algebraMap A₀ E u) →
      ∀ P : Ideal (integralClosure A₀ E), P.IsPrime → P ≠ ⊥ →
        ¬ Ideal.map (algebraMap A₀ (integralClosure A₀ E))
          (P.comap (algebraMap A₀ (integralClosure A₀ E))) ≤ P ^ 2 := by
  intro A₀ K₀ E _ _ _ _ _ _ _ _ _ _ _ N hN s hadj hu P hP hP0 hle
  have hdual := kummer_dual_induction A₀ K₀ N hN _ E s rfl hadj hu
  haveI : IsFractionRing (integralClosure A₀ E) E :=
    IsIntegralClosure.isFractionRing_of_finite_extension A₀ K₀ E _
  haveI : IsDedekindDomain (integralClosure A₀ E) := integralClosure.isDedekindDomain A₀ K₀ E
  haveI : Module.Finite A₀ (integralClosure A₀ E) := IsIntegralClosure.finite A₀ K₀ E _
  have hinj : Function.Injective (algebraMap A₀ E) := by
    rw [IsScalarTower.algebraMap_eq A₀ K₀ E]
    exact (algebraMap K₀ E).injective.comp (IsFractionRing.injective A₀ K₀)
  haveI : FaithfulSMul A₀ (integralClosure A₀ E) := by
    rw [faithfulSMul_iff_algebraMap_injective]
    intro a b hab
    exact hinj (congrArg Subtype.val hab)
  haveI : Module.IsTorsionFree A₀ (integralClosure A₀ E) := inferInstance
  have hone : Submodule.traceDual A₀ K₀ (1 : Submodule (integralClosure A₀ E) E) = 1 := by
    refine le_antisymm ?_ Submodule.one_le_traceDual_one
    intro y hy
    rw [Submodule.mem_traceDual] at hy
    refine Submodule.mem_one.mpr ⟨⟨y, hdual y fun z hz => ?_⟩, rfl⟩
    exact hy z (Submodule.mem_one.mpr ⟨⟨z, hz⟩, rfl⟩)
  have hdiff : differentIdeal A₀ (integralClosure A₀ E) = 1 := by
    rw [← FractionalIdeal.coeIdeal_eq_one (K := E), coeIdeal_differentIdeal A₀ K₀ E]
    have : FractionalIdeal.dual A₀ K₀
        (1 : FractionalIdeal (nonZeroDivisors (integralClosure A₀ E)) E) = 1 := by
      apply FractionalIdeal.coeToSubmodule_injective
      simp only [FractionalIdeal.coe_dual_one, FractionalIdeal.coe_one, hone]
    rw [this, inv_one]
  obtain ⟨b, hbP, hb0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP0
  have hp0 : P.comap (algebraMap A₀ (integralClosure A₀ E)) ≠ ⊥ :=
    Ideal.comap_ne_bot_of_integral_mem hb0 hbP (Algebra.IsIntegral.isIntegral b)
  haveI : (P.comap (algebraMap A₀ (integralClosure A₀ E))).IsMaximal :=
    Ideal.IsPrime.isMaximal inferInstance hp0
  have h := pow_sub_one_dvd_differentIdeal_aux A₀ K₀ E P two_ne_zero hp0 (Ideal.dvd_iff_le.mpr hle)
  rw [hdiff, Ideal.dvd_iff_le] at h
  apply hP.ne_top
  simpa using h

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerTowerQqPowLevelEqQ
section
noncomputable section

namespace GlobalTheory.KumDlog

open GlobalTheory.K5

variable {p : ℕ} [Fact p.Prime] {Ω : Type*} [Field Ω] [Algebra (O0 p) Ω]

def IsDer (S : Subalgebra (O0 p) Ω) (D : Ω → Ω) : Prop :=
  (∀ x ∈ S, ∀ y ∈ S, IsInt p (D (x + y) - D x - D y)) ∧
  (∀ x ∈ S, ∀ y ∈ S, IsInt p (D (x * y) - x * D y - y * D x)) ∧
  ∀ c : O0 p, IsInt p (D (algebraMap (O0 p) Ω c))

def FixI (G : Subgroup (Gal p Ω)) : Subalgebra (O0 p) Ω where
  carrier := {x | IsInt p x ∧ ∀ g ∈ G, g x = x}
  mul_mem' := fun {a b} ha hb =>
    ⟨IsIntegral.mul ha.1 hb.1, fun g hg => by rw [map_mul, ha.2 g hg, hb.2 g hg]⟩
  add_mem' := fun {a b} ha hb =>
    ⟨IsIntegral.add ha.1 hb.1, fun g hg => by rw [map_add, ha.2 g hg, hb.2 g hg]⟩
  algebraMap_mem' := fun c => ⟨isIntegral_algebraMap, fun g _ => g.commutes c⟩

def Hinf (T : Tower p Ω) : Subgroup (Gal p Ω) := ⨅ n, Gn T n

def Hfix (T : Tower p Ω) (r : Ω) : Subgroup (Gal p Ω) :=
  Hinf T ⊓ MulAction.stabilizer (Gal p Ω) r

def Lev (T : Tower p Ω) (m : ℕ) : Subalgebra (O0 p) Ω :=
  Algebra.adjoin (O0 p) {T.ζ m, T.qq m}

def Vals (T : Tower p Ω) (m : ℕ) (dz dq : Ω → Ω) : Prop :=
  IsInt p (dz (T.ζ m) - p * T.ζ m / (p : Ω) ^ m) ∧ IsInt p (dz (T.qq m)) ∧
  IsInt p (dq (T.ζ m)) ∧ IsInt p (dq (T.qq m) - p * T.qq m / (p : Ω) ^ m)

def DualData (B C : Subalgebra (O0 p) Ω) {ι : Type} [Fintype ι] (u v : ι → Ω) (tr : Ω → Ω) : Prop :=
  B ≤ C ∧ (∀ x ∈ C, IsInt p x) ∧ (∀ k, u k ∈ C) ∧ (∀ k, v k ∈ C) ∧ (∀ x ∈ C, tr x ∈ B) ∧
  (∀ x ∈ C, ∀ y ∈ C, tr (x + y) = tr x + tr y) ∧ (∀ b ∈ B, ∀ x ∈ C, tr (b * x) = b * tr x) ∧
  (∀ y ∈ C, ∑ k, u k * tr (v k * y) = p * y) ∧ (∀ y ∈ C, ∑ k, v k * tr (u k * y) = p * y) ∧
  ∑ k, u k * v k = p

theorem mem_FixI {G : Subgroup (Gal p Ω)} {x : Ω} :
    x ∈ FixI G ↔ IsInt p x ∧ ∀ g ∈ G, g x = x := Iff.rfl

theorem mem_Gn {T : Tower p Ω} {n : ℕ} {g : Gal p Ω} :
    g ∈ Gn T n ↔ g (T.ζ n) = T.ζ n ∧ g (T.qq n) = T.qq n := Iff.rfl

theorem mem_Hinf {T : Tower p Ω} {g : Gal p Ω} :
    g ∈ Hinf T ↔ ∀ n, g (T.ζ n) = T.ζ n ∧ g (T.qq n) = T.qq n := by
  simp only [Hinf, Subgroup.mem_iInf, mem_Gn]

theorem mem_Hfix {T : Tower p Ω} {r : Ω} {g : Gal p Ω} :
    g ∈ Hfix T r ↔ g ∈ Hinf T ∧ g r = r := Iff.rfl

theorem int_add {x y : Ω} (hx : IsInt p x) (hy : IsInt p y) : IsInt p (x + y) := IsIntegral.add hx hy
theorem int_sub {x y : Ω} (hx : IsInt p x) (hy : IsInt p y) : IsInt p (x - y) := IsIntegral.sub hx hy
theorem int_mul {x y : Ω} (hx : IsInt p x) (hy : IsInt p y) : IsInt p (x * y) := IsIntegral.mul hx hy
theorem int_neg {x : Ω} (hx : IsInt p x) : IsInt p (-x) := IsIntegral.neg hx
theorem int_pow {x : Ω} (hx : IsInt p x) (k : ℕ) : IsInt p (x ^ k) := IsIntegral.pow hx k
theorem int_alg (c : O0 p) : IsInt p (algebraMap (O0 p) Ω c) := isIntegral_algebraMap
theorem int_zero : IsInt p (0 : Ω) := isIntegral_zero
theorem int_one : IsInt p (1 : Ω) := isIntegral_one
theorem int_nat (k : ℕ) : IsInt p (k : Ω) := by
  simpa using (int_alg (k : O0 p) : IsInt p (algebraMap (O0 p) Ω _))
theorem int_int (k : ℤ) : IsInt p (k : Ω) := by
  simpa using (int_alg (k : O0 p) : IsInt p (algebraMap (O0 p) Ω _))
theorem int_sum {ι : Type*} (s : Finset ι) (f : ι → Ω) (h : ∀ i ∈ s, IsInt p (f i)) :
    IsInt p (∑ i ∈ s, f i) := IsIntegral.sum f h
theorem int_congr {x y : Ω} (hx : IsInt p x) (h : y = x) : IsInt p y := h ▸ hx
theorem int_gal (g : Gal p Ω) {x : Ω} (hx : IsInt p x) : IsInt p (g x) :=
  IsIntegral.map (g : Ω →ₐ[O0 p] Ω) hx
theorem int_of_pow {x : Ω} {k : ℕ} (hk : 0 < k) (hx : IsInt p (x ^ k)) : IsInt p x :=
  IsIntegral.of_pow hk hx

theorem zeta_pow (T : Tower p Ω) (n j : ℕ) : T.ζ (n + j) ^ (p ^ j) = T.ζ n := by
  induction j with
  | zero => simp
  | succ j ih => rw [pow_succ', pow_mul, ← add_assoc, T.ζpow, ih]

theorem qq_pow (T : Tower p Ω) (n j : ℕ) : T.qq (n + j) ^ (p ^ j) = T.qq n := by
  induction j with
  | zero => simp
  | succ j ih => rw [pow_succ', pow_mul, ← add_assoc, T.qpow, ih]

theorem ppow_pos (n : ℕ) : 0 < p ^ n := pow_pos (Fact.out : p.Prime).pos n

theorem int_zeta (T : Tower p Ω) (n : ℕ) : IsInt p (T.ζ n) :=
  int_of_pow (ppow_pos n) (by rw [(T.prim n).pow_eq_one]; exact int_one)

theorem zeta_ne (T : Tower p Ω) (n : ℕ) : T.ζ n ≠ 0 := (T.prim n).ne_zero (ppow_pos n).ne'

theorem int_zeta_inv (T : Tower p Ω) (n : ℕ) : IsInt p (T.ζ n)⁻¹ :=
  int_of_pow (ppow_pos n) (by rw [inv_pow, (T.prim n).pow_eq_one, inv_one]; exact int_one)

theorem kummerTower_qq_pow_level_eq_q (T : Tower p Ω) (n : ℕ) : T.qq n ^ (p ^ n) = algebraMap (O0 p) Ω (qO p) := by
  have := qq_pow T 0 n
  rwa [zero_add, T.q0] at this

theorem isUnit_qO : IsUnit (qO p) := by
  refine IsUnit.map _ (IsUnit.of_mul_eq_one (HahnSeries.single (-1 : ℤ) (1 : ℤ_[p])) ?_)
  rw [HahnSeries.single_mul_single]; simp

theorem int_qq (T : Tower p Ω) (n : ℕ) : IsInt p (T.qq n) :=
  int_of_pow (ppow_pos n) (by rw [kummerTower_qq_pow_level_eq_q]; exact int_alg _)

theorem qq_ne (T : Tower p Ω) (n : ℕ) : T.qq n ≠ 0 := by
  intro h
  have h1 := kummerTower_qq_pow_level_eq_q T n
  rw [h, zero_pow (ppow_pos (p := p) n).ne'] at h1
  exact ((isUnit_qO (p := p)).map (algebraMap (O0 p) Ω)).ne_zero h1.symm

theorem int_qq_inv (T : Tower p Ω) (n : ℕ) : IsInt p (T.qq n)⁻¹ := by
  refine int_of_pow (ppow_pos (p := p) n) ?_
  obtain ⟨w, hw⟩ := (isUnit_qO (p := p))
  rw [inv_pow, kummerTower_qq_pow_level_eq_q, ← hw]
  refine int_congr (int_alg (↑w⁻¹ : O0 p)) ?_
  exact inv_eq_of_mul_eq_one_right (by rw [← map_mul]; simp)

theorem Lev_int (T : Tower p Ω) (m : ℕ) : ∀ x ∈ Lev T m, IsInt p x := by
  have : Lev T m ≤ integralClosure (O0 p) Ω := by
    refine Algebra.adjoin_le ?_
    rintro x (rfl | rfl)
    · exact int_zeta T m
    · exact int_qq T m
  exact fun x hx => this hx

theorem zeta_mem_Lev (T : Tower p Ω) (m : ℕ) : T.ζ m ∈ Lev T m :=
  Algebra.subset_adjoin (by simp)

theorem qq_mem_Lev (T : Tower p Ω) (m : ℕ) : T.qq m ∈ Lev T m :=
  Algebra.subset_adjoin (by simp)

theorem Lev_mono (T : Tower p Ω) {m m' : ℕ} (h : m ≤ m') : Lev T m ≤ Lev T m' := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
  refine Algebra.adjoin_le ?_
  rintro x (rfl | rfl)
  · rw [← zeta_pow T m j]; exact pow_mem (zeta_mem_Lev T _) _
  · rw [← qq_pow T m j]; exact pow_mem (qq_mem_Lev T _) _

theorem Lev_le_FixI (T : Tower p Ω) (m : ℕ) {G : Subgroup (Gal p Ω)} (hG : G ≤ Gn T m) :
    Lev T m ≤ FixI G := by
  refine Algebra.adjoin_le ?_
  rintro x (rfl | rfl)
  · exact ⟨int_zeta T m, fun g hg => (hG hg).1⟩
  · exact ⟨int_qq T m, fun g hg => (hG hg).2⟩

theorem Hinf_le (T : Tower p Ω) (m : ℕ) : Hinf T ≤ Gn T m := iInf_le _ m

theorem IsDer.mono {S S' : Subalgebra (O0 p) Ω} {D : Ω → Ω} (h : IsDer S D) (hS : S' ≤ S) :
    IsDer S' D :=
  ⟨fun x hx y hy => h.1 x (hS hx) y (hS hy), fun x hx y hy => h.2.1 x (hS hx) y (hS hy), h.2.2⟩

theorem IsDer.zero {S : Subalgebra (O0 p) Ω} {D : Ω → Ω} (h : IsDer S D) : IsInt p (D 0) := by
  simpa using h.2.2 0

theorem IsDer.one {S : Subalgebra (O0 p) Ω} {D : Ω → Ω} (h : IsDer S D) : IsInt p (D 1) := by
  simpa using h.2.2 1

theorem IsDer.sum {S : Subalgebra (O0 p) Ω} {D : Ω → Ω} (h : IsDer S D) {ι : Type*}
    (s : Finset ι) (f : ι → Ω) (hf : ∀ i ∈ s, f i ∈ S) :
    IsInt p (D (∑ i ∈ s, f i) - ∑ i ∈ s, D (f i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using h.zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have h1 := h.1 (f a) (hf a (by simp)) (∑ i ∈ s, f i)
      (sum_mem fun i hi => hf i (by simp [hi]))
    exact int_congr (int_add h1 (ih fun i hi => hf i (by simp [hi]))) (by ring)

theorem IsDer.pow {S : Subalgebra (O0 p) Ω} {D : Ω → Ω} (h : IsDer S D)
    (hS : ∀ x ∈ S, IsInt p x) {x : Ω} (hx : x ∈ S) (k : ℕ) :
    IsInt p (D (x ^ (k + 1)) - (k + 1 : ℕ) * x ^ k * D x) := by
  induction k with
  | zero => simpa using int_zero
  | succ k ih =>
    have h1 := h.2.1 x hx (x ^ (k + 1)) (pow_mem hx _)
    refine int_congr (int_add h1 (int_mul (hS x hx) ih)) ?_
    rw [← pow_succ']; push_cast; ring

theorem IsDer.pow' {S : Subalgebra (O0 p) Ω} {D : Ω → Ω} (h : IsDer S D)
    (hS : ∀ x ∈ S, IsInt p x) {x : Ω} (hx : x ∈ S) (k : ℕ) :
    IsInt p (x * D (x ^ k) - k * x ^ k * D x) := by
  rcases k with _ | k
  · simpa using int_mul (hS x hx) h.one
  · exact int_congr (int_mul (hS x hx) (h.pow hS hx k)) (by ring)

theorem IsDer.alg_mul {S : Subalgebra (O0 p) Ω} {D : Ω → Ω} (h : IsDer S D)
    (hS : ∀ x ∈ S, IsInt p x) (c : O0 p) {x : Ω} (hx : x ∈ S) :
    IsInt p (D (algebraMap (O0 p) Ω c * x) - algebraMap (O0 p) Ω c * D x) :=
  int_congr (int_add (h.2.1 _ (S.algebraMap_mem c) x hx) (int_mul (hS x hx) (h.2.2 c))) (by ring)

theorem IsDer.sub {S : Subalgebra (O0 p) Ω} {D D' : Ω → Ω} (h : IsDer S D) (h' : IsDer S D') :
    IsDer S (fun x => D x - D' x) :=
  ⟨fun x hx y hy => int_congr (int_sub (h.1 x hx y hy) (h'.1 x hx y hy)) (by ring),
   fun x hx y hy => int_congr (int_sub (h.2.1 x hx y hy) (h'.2.1 x hx y hy)) (by ring),
   fun c => int_sub (h.2.2 c) (h'.2.2 c)⟩

theorem IsDer.smul {S : Subalgebra (O0 p) Ω} {D : Ω → Ω} (h : IsDer S D) {c : Ω}
    (hc : IsInt p c) : IsDer S (fun x => c * D x) :=
  ⟨fun x hx y hy => int_congr (int_mul hc (h.1 x hx y hy)) (by ring),
   fun x hx y hy => int_congr (int_mul hc (h.2.1 x hx y hy)) (by ring),
   fun a => int_mul hc (h.2.2 a)⟩

theorem IsDer.conj {S : Subalgebra (O0 p) Ω} {D : Ω → Ω} (h : IsDer S D) (g : Gal p Ω)
    (hg : ∀ x ∈ S, g x ∈ S) : IsDer S (fun x => g.symm (D (g x))) := by
  refine ⟨fun x hx y hy => ?_, fun x hx y hy => ?_, fun c => ?_⟩
  · refine int_congr (int_gal g.symm (h.1 _ (hg x hx) _ (hg y hy))) ?_
    simp
  · refine int_congr (int_gal g.symm (h.2.1 _ (hg x hx) _ (hg y hy))) ?_
    simp
  · refine int_gal g.symm ?_
    rw [g.commutes]; exact h.2.2 c

theorem IsDer.adjoin {S : Subalgebra (O0 p) Ω} {D : Ω → Ω} (h : IsDer S D)
    (hS : ∀ x ∈ S, IsInt p x) {t : Set Ω} (ht : t ⊆ S) (h0 : ∀ x ∈ t, IsInt p (D x)) :
    ∀ x ∈ Algebra.adjoin (O0 p) t, IsInt p (D x) := by
  have hle : Algebra.adjoin (O0 p) t ≤ S := Algebra.adjoin_le ht
  intro x hx
  induction hx using Algebra.adjoin_induction with
  | mem x hx => exact h0 x hx
  | algebraMap c => exact h.2.2 c
  | add x y hx hy ihx ihy =>
    exact int_congr (int_add (h.1 x (hle hx) y (hle hy)) (int_add ihx ihy)) (by ring)
  | mul x y hx hy ihx ihy =>
    exact int_congr (int_add (h.2.1 x (hle hx) y (hle hy))
      (int_add (int_mul (hS x (hle hx)) ihy) (int_mul (hS y (hle hy)) ihx))) (by ring)

end GlobalTheory.KumDlog
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LevelOneTwelveMulFinrankModularFormLowerBound
section
open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology

namespace GlobalTheory.OddFrame

theorem levelOne_twelve_mul_finrank_lower_bound :
    ∀ n : ℤ, Even n → n + 5 + 3 * (if n % 4 = 0 then 1 else -1) +
      4 * (if n % 6 = 0 then 1 else if n % 6 = 2 then -1 else 0) ≤
        12 * (Module.finrank ℂ (ModularForm 𝒮ℒ n) : ℤ) := by
  intro n hn
  rcases lt_or_ge n 0 with hneg | hpos
  · have h0 : (0 : ℤ) ≤ (Module.finrank ℂ (ModularForm 𝒮ℒ n) : ℤ) := Int.natCast_nonneg _
    obtain ⟨m, hm⟩ := hn
    generalize (Module.finrank ℂ (ModularForm 𝒮ℒ n) : ℤ) = d at h0 ⊢
    split_ifs <;> omega
  · lift n to ℕ using hpos
    have hke : Even n := by exact_mod_cast hn
    have hrank := ModularForm.dimension_level_one n hke
    have hfin : Module.finrank ℂ (ModularForm 𝒮ℒ (n : ℤ)) =
        if n % 12 = 2 then n / 12 else n / 12 + 1 := by
      exact Module.finrank_eq_of_rank_eq hrank
    obtain ⟨m, hm⟩ := hke
    generalize Module.finrank ℂ (ModularForm 𝒮ℒ (n : ℤ)) = d at hfin ⊢
    split_ifs at hfin ⊢ <;> omega

end GlobalTheory.OddFrame
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LseriesShiftTwistStatement
section
open Complex Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lSeries_twist_natPow_eq_shift : ∀ (e : ℕ) (ψ g : ℕ → ℂ) (s : ℝ), 1 ≤ e → LSeries (fun n : ℕ => ψ n * (n : ℂ) ^ (e - 1) * g n) (((2 * (e : ℝ) + s : ℝ)) : ℂ) = LSeries (fun n => ψ n * g n) ((e + 1 : ℝ) + s : ℝ) := by
  first | exact @GlobalTheory.lseries_shift_twist | exact GlobalTheory.lseries_shift_twist | (intros; apply GlobalTheory.lseries_shift_twist <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LseriesSquaresEqStatement
section
open Complex Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lSeries_squares_eq_shift : ∀ (e : ℕ) (χ ψ θ : ℕ → ℂ) (s : ℝ), 1 ≤ e → 0 < s → (∀ n, ‖χ n‖ ≤ 1 ∧ ‖ψ n‖ ≤ 1 ∧ ‖θ n‖ ≤ 1) → LSeriesSummable (fun n : ℕ => if Nat.sqrt n * Nat.sqrt n = n then χ (Nat.sqrt n) * ψ (Nat.sqrt n) * θ (Nat.sqrt n) * (Nat.sqrt n : ℂ) ^ (3 * e - 1) else 0) (((2 * (e : ℝ) + s : ℝ)) : ℂ) ∧ LSeries (fun n : ℕ => if Nat.sqrt n * Nat.sqrt n = n then χ (Nat.sqrt n) * ψ (Nat.sqrt n) * θ (Nat.sqrt n) * (Nat.sqrt n : ℂ) ^ (3 * e - 1) else 0) (((2 * (e : ℝ) + s : ℝ)) : ℂ) = LSeries (fun n => χ n * ψ n * θ n) ((e + 1 : ℕ) + 2 * s) := by
  first | exact @GlobalTheory.lseriesSquares_eq | exact GlobalTheory.lseriesSquares_eq | (intros; apply GlobalTheory.lseriesSquares_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LseriesSummableTwistPowOfSqSummableStatement
section
open Complex Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lSeriesSummable_twist_pow_of_summable_sq_div : ∀ (e : ℕ) (ψ g : ℕ → ℂ) (s : ℝ), 1 ≤ e → 0 < s → (∀ n, ‖ψ n‖ ≤ 1) → (∀ t : ℝ, 0 < t → Summable fun n : ℕ => ‖g n‖ ^ 2 / (n : ℝ) ^ (((2 * e + 1 : ℕ) : ℝ) + t)) → LSeriesSummable (fun n : ℕ => ψ n * (n : ℂ) ^ (e - 1) * g n) (((2 * (e : ℝ) + s : ℝ)) : ℂ) := by
  first | exact @GlobalTheory.lseriesSummable_twist_pow_of_sq_summable | exact GlobalTheory.lseriesSummable_twist_pow_of_sq_summable | (intros; apply GlobalTheory.lseriesSummable_twist_pow_of_sq_summable <;> assumption)
end

