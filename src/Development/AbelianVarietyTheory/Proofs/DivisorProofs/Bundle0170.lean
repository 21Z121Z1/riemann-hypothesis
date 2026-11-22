import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0074
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
import Formalism.SatakeDualWeyl.Statement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0073
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0075

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LengthCokerLsmulEqLengthKerAddSum
section
namespace GlobalTheory.HerbrandLength

open IsLocalRing

variable {A : Type} [CommRing A]

def Concl (b : A) (P : Finset (PrimeSpectrum A)) (M : Type) [AddCommGroup M] [Module A M] : Prop :=
  Module.length A (LinearMap.ker (LinearMap.lsmul A M b)) ≠ ⊤ ∧
  Module.length A (M ⧸ LinearMap.range (LinearMap.lsmul A M b)) =
    Module.length A (LinearMap.ker (LinearMap.lsmul A M b)) +
      ∑ p ∈ P, Module.length (Localization.AtPrime p.asIdeal)
        (LocalizedModule p.asIdeal.primeCompl M) * Module.length A (A ⧸ (p.asIdeal ⊔ Ideal.span {b}))

theorem loc_exact (p : Ideal A) [p.IsPrime] {N M Q : Type} [AddCommGroup N] [Module A N]
    [AddCommGroup M] [Module A M] [AddCommGroup Q] [Module A Q] (f : N →ₗ[A] M) (g : M →ₗ[A] Q)
    (hf : Function.Injective f) (hg : Function.Surjective g) (H : Function.Exact f g) :
    Module.length (Localization.AtPrime p) (LocalizedModule p.primeCompl M) =
      Module.length (Localization.AtPrime p) (LocalizedModule p.primeCompl N) +
      Module.length (Localization.AtPrime p) (LocalizedModule p.primeCompl Q) :=
  Module.length_eq_add_of_exact (LocalizedModule.map p.primeCompl f)
    (LocalizedModule.map p.primeCompl g) (LocalizedModule.map_injective _ f hf)
    (LocalizedModule.map_surjective _ g hg) (LocalizedModule.map_exact _ f g H)

theorem loc_zero_of_ann (p : Ideal A) [p.IsPrime] (M : Type) [AddCommGroup M] [Module A M]
    (s : A) (hs : s ∉ p) (hsM : ∀ x : M, s • x = 0) :
    Module.length (Localization.AtPrime p) (LocalizedModule p.primeCompl M) = 0 :=
  Module.length_eq_zero_iff.2 ((IsLocalizedModule.subsingleton_iff p.primeCompl
    (LocalizedModule.mkLinearMap p.primeCompl M)).2 fun x => ⟨s, hs, hsM x⟩)

theorem loc_quot_self (p : Ideal A) [hp : p.IsPrime] :
    Module.length (Localization.AtPrime p) (LocalizedModule p.primeCompl (A ⧸ p)) = 1 := by
  refine Module.length_eq_one_iff.2 (isSimpleModule_iff_toSpanSingleton_surjective.2 ⟨?_, ?_⟩)
  · rw [← not_subsingleton_iff_nontrivial, IsLocalizedModule.subsingleton_iff p.primeCompl
      (LocalizedModule.mkLinearMap p.primeCompl (A ⧸ p))]
    intro h
    obtain ⟨r, hr, hr0⟩ := h 1
    rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, mul_one,
      Ideal.Quotient.eq_zero_iff_mem] at hr0
    exact hr hr0
  · intro x hx y
    induction x using LocalizedModule.induction_on with
    | h a s =>
    induction y using LocalizedModule.induction_on with
    | h c t =>
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨r', rfl⟩ := Ideal.Quotient.mk_surjective c
    have hr : r ∈ p.primeCompl := by
      intro hrm
      apply hx
      rw [Ideal.Quotient.eq_zero_iff_mem.2 hrm, LocalizedModule.zero_mk]
    refine ⟨Localization.mk (r' * s) (⟨r, hr⟩ * t), ?_⟩
    rw [LinearMap.toSpanSingleton_apply, LocalizedModule.mk_smul_mk, LocalizedModule.mk_eq]
    refine ⟨1, ?_⟩
    simp only [Submonoid.smul_def, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul,
      Submonoid.coe_mul, Submonoid.coe_one]
    congr 1
    ring

theorem ker_eq_coker {M : Type} [AddCommGroup M] [Module A M] (φ : M →ₗ[A] M)
    (h : Module.length A M ≠ ⊤) :
    Module.length A (M ⧸ LinearMap.range φ) = Module.length A (LinearMap.ker φ) := by
  have h1 := Module.length_eq_add_of_exact (LinearMap.ker φ).subtype (LinearMap.ker φ).mkQ
    (Submodule.injective_subtype _) (Submodule.mkQ_surjective _) (LinearMap.exact_subtype_mkQ _)
  have h2 := Module.length_eq_add_of_exact (LinearMap.range φ).subtype (LinearMap.range φ).mkQ
    (Submodule.injective_subtype _) (Submodule.mkQ_surjective _) (LinearMap.exact_subtype_mkQ _)
  rw [φ.quotKerEquivRange.length_eq] at h1
  have hR : Module.length A (LinearMap.range φ) ≠ ⊤ :=
    ne_top_of_le_ne_top h (le_self_add.trans_eq h2.symm)
  exact WithTop.add_left_cancel hR (h2.symm.trans (h1.trans (add_comm _ _)))

theorem enat_cancel {c₂ k₁ k₂ k₃ s₁ s₃ : ℕ∞} (h₁ : k₁ ≠ ⊤) (h₃ : k₃ ≠ ⊤)
    (e : c₂ + k₁ + k₃ = k₂ + (k₁ + s₁) + (k₃ + s₃)) : c₂ = k₂ + (s₁ + s₃) := by
  have hne : k₁ + k₃ ≠ ⊤ := WithTop.add_ne_top.2 ⟨h₁, h₃⟩
  have h : c₂ + (k₁ + k₃) = k₂ + (s₁ + s₃) + (k₁ + k₃) := by
    rw [← add_assoc, e]
    ring
  exact WithTop.add_right_cancel hne h

theorem concl_ext {M₁ M₂ M₃ : Type} [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup M₃]
    [Module A M₁] [Module A M₂] [Module A M₃] (b : A) (P : Finset (PrimeSpectrum A))
    (f : M₁ →ₗ[A] M₂) (g : M₂ →ₗ[A] M₃) (hf : Function.Injective f)
    (hg : Function.Surjective g) (hfg : Function.Exact f g)
    (h₁ : Concl b P M₁) (h₃ : Concl b P M₃) : Concl b P M₂ := by
  obtain ⟨e, hle⟩ := GlobalTheory.scalar_snake_length A M₁ M₂ M₃ f g hf hg hfg b
  obtain ⟨k1, s1⟩ := h₁
  obtain ⟨k3, s3⟩ := h₃
  have hne := WithTop.add_ne_top.2 ⟨k1, k3⟩
  refine ⟨ne_top_of_le_ne_top hne hle, ?_⟩
  have hsum : ∑ p ∈ P, Module.length (Localization.AtPrime p.asIdeal)
        (LocalizedModule p.asIdeal.primeCompl M₂) * Module.length A (A ⧸ (p.asIdeal ⊔ Ideal.span {b})) =
      (∑ p ∈ P, Module.length (Localization.AtPrime p.asIdeal)
        (LocalizedModule p.asIdeal.primeCompl M₁) * Module.length A (A ⧸ (p.asIdeal ⊔ Ideal.span {b}))) +
      ∑ p ∈ P, Module.length (Localization.AtPrime p.asIdeal)
        (LocalizedModule p.asIdeal.primeCompl M₃) * Module.length A (A ⧸ (p.asIdeal ⊔ Ideal.span {b})) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [loc_exact p.asIdeal f g hf hg hfg, add_mul]
  rw [hsum]
  rw [s1, s3] at e
  exact enat_cancel k1 k3 e

theorem concl_subsingleton (b : A) (P : Finset (PrimeSpectrum A)) (M : Type) [AddCommGroup M]
    [Module A M] [Subsingleton M] : Concl b P M := by
  have hk : Module.length A (LinearMap.ker (LinearMap.lsmul A M b)) = 0 :=
    Module.length_eq_zero_iff.2 ⟨fun x y => Subtype.ext (Subsingleton.elim _ _)⟩
  have hc : Module.length A (M ⧸ LinearMap.range (LinearMap.lsmul A M b)) = 0 :=
    Module.length_eq_zero_iff.2 ((Submodule.mkQ_surjective _).subsingleton)
  refine ⟨by rw [hk]; exact ENat.zero_ne_top, ?_⟩
  rw [hk, hc, zero_add, eq_comm]
  refine Finset.sum_eq_zero fun p _ => ?_
  rw [loc_zero_of_ann p.asIdeal M 1 (Ideal.IsPrime.ne_top' ∘ (Ideal.eq_top_of_isUnit_mem _ · isUnit_one))
    (fun x => Subsingleton.elim _ _), zero_mul]

theorem concl_equiv {M N : Type} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    (b : A) (P : Finset (PrimeSpectrum A)) (e : M ≃ₗ[A] N) (h : Concl b P M) : Concl b P N :=
  concl_ext (M₃ := PUnit) b P e.toLinearMap 0 e.injective (Function.surjective_to_subsingleton _)
    ((e.exact_zero_iff_surjective _).2 e.surjective) h (concl_subsingleton b P PUnit)

theorem ne_max [IsLocalRing A] (p : PrimeSpectrum A) (h : ringKrullDim (A ⧸ p.asIdeal) = 1) :
    p.asIdeal ≠ maximalIdeal A := by
  intro hpm
  letI := Ideal.Quotient.field (maximalIdeal A)
  have h0 : ringKrullDim (A ⧸ maximalIdeal A) = 0 := ringKrullDim_eq_zero_of_field (A ⧸ maximalIdeal A)
  rw [← hpm, h] at h0
  exact one_ne_zero h0

theorem eq_of_le [IsLocalRing A] (p q : PrimeSpectrum A) (hp : ringKrullDim (A ⧸ p.asIdeal) = 1)
    (hq : ringKrullDim (A ⧸ q.asIdeal) = 1) (hle : p.asIdeal ≤ q.asIdeal) : p = q := by
  by_contra hne
  have hlt : p.asIdeal < q.asIdeal := lt_of_le_of_ne hle (fun h => hne (PrimeSpectrum.ext h))
  have hqm : q.asIdeal < maximalIdeal A :=
    lt_of_le_of_ne (IsLocalRing.le_maximalIdeal q.isPrime.ne_top) (ne_max q hq)
  let a : PrimeSpectrum.zeroLocus (R := A) p.asIdeal := ⟨p, fun _ h => h⟩
  let c : PrimeSpectrum.zeroLocus (R := A) p.asIdeal := ⟨q, fun _ h => hle h⟩
  let d : PrimeSpectrum.zeroLocus (R := A) p.asIdeal :=
    ⟨⟨maximalIdeal A, inferInstance⟩, fun _ h => (hle.trans hqm.le) h⟩
  have hac : a < c := Subtype.mk_lt_mk.2 ((PrimeSpectrum.asIdeal_lt_asIdeal _ _).1 hlt)
  have hcd : c < d := Subtype.mk_lt_mk.2 ((PrimeSpectrum.asIdeal_lt_asIdeal _ _).1 hqm)
  let s : LTSeries (PrimeSpectrum.zeroLocus (R := A) p.asIdeal) :=
    ⟨2, ![a, c, d], fun i => by fin_cases i <;> first | exact hac | exact hcd | simp [hac, hcd]⟩
  have hs := Order.LTSeries.length_le_krullDim s
  rw [← ringKrullDim_quotient, hp] at hs
  have h2 : s.length = 2 := rfl
  rw [h2] at hs
  exact absurd hs (by decide)

theorem concl_prime [IsLocalRing A] (b : A) (P : Finset (PrimeSpectrum A))
    (hP : ∀ p ∈ P, ringKrullDim (A ⧸ p.asIdeal) = 1 ∧ b ∉ p.asIdeal) (p : PrimeSpectrum A)
    (hpP : p ∈ P) : Concl b P (A ⧸ p.asIdeal) := by
  have hb : b ∉ p.asIdeal := (hP p hpP).2
  have hker : LinearMap.ker (LinearMap.lsmul A (A ⧸ p.asIdeal) b) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro x hx
    rw [LinearMap.lsmul_apply, Algebra.smul_def, Ideal.Quotient.algebraMap_eq] at hx
    exact (mul_eq_zero.1 hx).resolve_left (fun h => hb (Ideal.Quotient.eq_zero_iff_mem.1 h))
  have hrange : LinearMap.range (LinearMap.lsmul A (A ⧸ p.asIdeal) b) =
      Submodule.map p.asIdeal.mkQ (Ideal.span {b}) := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective _ y
      exact ⟨b * a, Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self b),
        by rw [LinearMap.lsmul_apply, ← LinearMap.map_smul, smul_eq_mul]⟩
    · rintro ⟨a, ha, rfl⟩
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ha
      exact ⟨p.asIdeal.mkQ c, by rw [LinearMap.lsmul_apply, ← LinearMap.map_smul, smul_eq_mul, mul_comm]⟩
  have hcok : Module.length A ((A ⧸ p.asIdeal) ⧸ LinearMap.range (LinearMap.lsmul A (A ⧸ p.asIdeal) b)) =
      Module.length A (A ⧸ (p.asIdeal ⊔ Ideal.span {b})) :=
    ((Submodule.quotEquivOfEq _ _ hrange).trans
      (Submodule.quotientQuotientEquivQuotientSup p.asIdeal (Ideal.span {b}))).length_eq
  have hk0 : Module.length A (LinearMap.ker (LinearMap.lsmul A (A ⧸ p.asIdeal) b)) = 0 := by
    rw [hker]; exact Module.length_eq_zero_iff.2 inferInstance
  refine ⟨by rw [hk0]; exact ENat.zero_ne_top, ?_⟩
  rw [hcok, hk0, zero_add, Finset.sum_eq_single p, loc_quot_self, one_mul]
  · intro q hq hqp
    have hnle : ¬ p.asIdeal ≤ q.asIdeal := fun h => hqp (eq_of_le p q (hP p hpP).1 (hP q hq).1 h).symm
    obtain ⟨s, hsp, hsq⟩ := SetLike.not_le_iff_exists.1 hnle
    rw [loc_zero_of_ann q.asIdeal _ s hsq (fun x => ?_), zero_mul]
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mul_mem_right _ _ hsp
  · intro h; exact absurd hpP h

theorem concl_max [IsLocalRing A] (b : A) (P : Finset (PrimeSpectrum A))
    (hP : ∀ p ∈ P, ringKrullDim (A ⧸ p.asIdeal) = 1 ∧ b ∉ p.asIdeal) :
    Concl b P (A ⧸ maximalIdeal A) := by
  have hlen : Module.length A (A ⧸ maximalIdeal A) = 1 :=
    Module.length_eq_one_iff.2
      (isSimpleModule_iff_isCoatom.2 (inferInstance : (maximalIdeal A).IsMaximal).out)
  have hfin : Module.length A (A ⧸ maximalIdeal A) ≠ ⊤ := by rw [hlen]; exact ENat.one_ne_top
  refine ⟨ne_top_of_le_ne_top hfin
    (Module.length_le_of_injective (LinearMap.ker _).subtype (Submodule.injective_subtype _)), ?_⟩
  rw [ker_eq_coker _ hfin, Finset.sum_eq_zero, add_zero]
  intro p hp
  have hnle : ¬ maximalIdeal A ≤ p.asIdeal := fun h =>
    ne_max p (hP p hp).1 (le_antisymm (IsLocalRing.le_maximalIdeal p.isPrime.ne_top) h)
  obtain ⟨s, hsm, hsp⟩ := SetLike.not_le_iff_exists.1 hnle
  rw [loc_zero_of_ann p.asIdeal _ s hsp (fun x => ?_), zero_mul]
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mul_mem_right _ _ hsm

end GlobalTheory.HerbrandLength

open GlobalTheory.HerbrandLength in

theorem GlobalTheory.length_coker_lsmul_eq_length_ker_add_sum : ∀ (A : Type) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] (b : A) (P : Finset (PrimeSpectrum A)), (∀ p ∈ P, ringKrullDim (A ⧸ p.asIdeal) = 1 ∧ b ∉ p.asIdeal) → ∀ (M : Type) [AddCommGroup M] [Module A M] [Module.Finite A M], (∀ p ∈ Module.support A M, p ∈ P ∨ p.asIdeal = IsLocalRing.maximalIdeal A) → Module.length A (LinearMap.ker (LinearMap.lsmul A M b)) ≠ ⊤ ∧ Module.length A (M ⧸ LinearMap.range (LinearMap.lsmul A M b)) = Module.length A (LinearMap.ker (LinearMap.lsmul A M b)) + ∑ p ∈ P, Module.length (Localization.AtPrime p.asIdeal) (LocalizedModule p.asIdeal.primeCompl M) * Module.length A (A ⧸ (p.asIdeal ⊔ Ideal.span {b})) := by
  intro A _ _ _ b P hP M _ _ hfin hM
  revert hM
  induction hfin using IsNoetherianRing.induction_on_isQuotientEquivQuotientPrime A with
  | subsingleton N => intro _; exact concl_subsingleton b P N
  | quotient N p e =>
    intro hN
    have hpN : p ∈ Module.support A N := by
      rw [e.support_eq, Module.mem_support_iff_of_finite]
      intro r hr
      have h1 := Module.mem_annihilator.1 hr 1
      rwa [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, mul_one,
        Ideal.Quotient.eq_zero_iff_mem] at h1
    rcases hN p hpN with hpP | hpm
    · exact concl_equiv b P e.symm (concl_prime b P hP p hpP)
    · exact concl_equiv b P ((Submodule.quotEquivOfEq _ _ hpm).symm.trans e.symm) (concl_max b P hP)
  | exact N₁ N₂ N₃ f g hf hg hfg h₁ h₃ =>
    intro hN
    exact concl_ext b P f g hf hg hfg
      (h₁ fun q hq => hN q (Module.support_subset_of_injective f hf hq))
      (h₃ fun q hq => hN q (Module.support_subset_of_surjective g hg hq))
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LengthKerCokerLsmulQuotientSpanSwapStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.length_ker_coker_lsmul_quotient_span_swap : ∀ (A : Type) [CommRing A] [IsDomain A] (a b : A), a ≠ 0 → b ≠ 0 → Module.length A (LinearMap.ker (LinearMap.lsmul A (A ⧸ Ideal.span {a}) b)) = Module.length A (LinearMap.ker (LinearMap.lsmul A (A ⧸ Ideal.span {b}) a)) ∧ Module.length A ((A ⧸ Ideal.span {a}) ⧸ LinearMap.range (LinearMap.lsmul A (A ⧸ Ideal.span {a}) b)) = Module.length A ((A ⧸ Ideal.span {b}) ⧸ LinearMap.range (LinearMap.lsmul A (A ⧸ Ideal.span {b}) a)) := by
  first | exact @GlobalTheory.kernel_cokernel_length_swap | exact GlobalTheory.kernel_cokernel_length_swap | (intros; apply GlobalTheory.kernel_cokernel_length_swap <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftAt
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.SecLift

def LiftAt {R R₀ : Type} [CommRing R] [CommRing R₀] (π : R →+* R₀) (X : Over (Sp R))
    (g₀ : Sp R₀ ⟶ X.left) (f : R) : Prop :=
  ∃ e : Sp (Localization.Away f) ⟶ X.left,
    e ≫ X.hom = spMap (algebraMap R (Localization.Away f)) ∧
    spMap (Localization.awayMap π f) ≫ e = spMap (algebraMap R₀ (Localization.Away (π f))) ≫ g₀

def LiftIn {R R₀ : Type} [CommRing R] [CommRing R₀] (π : R →+* R₀) (X : Over (Sp R))
    (g₀ : Sp R₀ ⟶ X.left) (f : R) (V : X.left.Opens) : Prop :=
  ∃ e : Sp (Localization.Away f) ⟶ X.left,
    e ≫ X.hom = spMap (algebraMap R (Localization.Away f)) ∧
    spMap (Localization.awayMap π f) ≫ e = spMap (algebraMap R₀ (Localization.Away (π f))) ≫ g₀ ∧
    e ⁻¹ᵁ V = ⊤

end GlobalTheory.SecLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftFormsToLatticeOfFiniteInvertibleStabilisers
section
namespace GlobalTheory

theorem lift_forms_of_card_isUnit : ∀ (O : Type) [CommRing O] (G : Type) [Group G] (Γ K : Subgroup G)
    (B Q : Type) [AddCommGroup B] [Module O B] [AddCommGroup Q] [Module O Q]
    (ρ : Representation O K B) (π : B →ₗ[O] Q), Function.Surjective π →
    (∀ κ x, π x = 0 → π (ρ κ x) = 0) →
    (∀ g : G, Finite {γ : Γ // g⁻¹ * (γ : G) * g ∈ K} ∧
      IsUnit ((Nat.card {γ : Γ // g⁻¹ * (γ : G) * g ∈ K} : ℕ) : O)) →
    ∀ f : G → Q, (∀ (γ : Γ) (g : G) (κ : K) (y : B), f g = π y → f ((γ : G) * g * κ) = π (ρ κ⁻¹ y)) →
    ∃ F ∈ Formalism.UG.AMFK O Γ K ρ, ∀ g, π (F g) = f g := by
  intro O _ G _ Γ K B Q _ _ _ _ ρ π hπ _hker hfin f hf
  classical

  have hlift : ∀ s : G, ∃ y : B, π y = f s ∧
      ∀ (h : Γ) (hk : s⁻¹ * (h : G) * s ∈ K), ρ ⟨_, hk⟩ y = y := by
    intro s
    obtain ⟨hF, hu⟩ := hfin s
    haveI : Fintype {γ : Γ // s⁻¹ * (γ : G) * s ∈ K} := Fintype.ofFinite _
    obtain ⟨y0, hy0⟩ := hπ (f s)
    obtain ⟨u, hu'⟩ := hu
    let kk : {γ : Γ // s⁻¹ * (γ : G) * s ∈ K} → K := fun h => ⟨_, h.2⟩
    refine ⟨(↑u⁻¹ : O) • ∑ h, ρ (kk h) y0, ?_, ?_⟩
    · rw [map_smul, map_sum]
      have hval : ∀ h, π (ρ (kk h) y0) = f s := by
        intro h
        have e := hf h.1 s (kk h)⁻¹ y0 hy0.symm
        rw [inv_inv] at e
        rw [← e]
        congr 1
        simp only [kk, Subgroup.coe_inv]
        group
      simp_rw [hval, Finset.sum_const, Finset.card_univ]
      rw [← Nat.cast_smul_eq_nsmul O, smul_smul, ← Nat.card_eq_fintype_card, ← hu', Units.inv_mul,
        one_smul]
    · intro h hk
      rw [map_smul, map_sum]
      congr 1
      have hmul : ∀ x : {γ : Γ // s⁻¹ * (γ : G) * s ∈ K},
          s⁻¹ * ((h * x.1 : Γ) : G) * s ∈ K := by
        intro x
        have : s⁻¹ * ((h * x.1 : Γ) : G) * s = (s⁻¹ * (h : G) * s) * (s⁻¹ * (x.1 : G) * s) := by
          push_cast; group
        rw [this]; exact K.mul_mem hk x.2
      have hinvm : ∀ x : {γ : Γ // s⁻¹ * (γ : G) * s ∈ K},
          s⁻¹ * ((h⁻¹ * x.1 : Γ) : G) * s ∈ K := by
        intro x
        have : s⁻¹ * ((h⁻¹ * x.1 : Γ) : G) * s = (s⁻¹ * (h : G) * s)⁻¹ * (s⁻¹ * (x.1 : G) * s) := by
          push_cast; group
        rw [this]; exact K.mul_mem (K.inv_mem hk) x.2
      let e : {γ : Γ // s⁻¹ * (γ : G) * s ∈ K} ≃ {γ : Γ // s⁻¹ * (γ : G) * s ∈ K} :=
        { toFun := fun x => ⟨h * x.1, hmul x⟩
          invFun := fun x => ⟨h⁻¹ * x.1, hinvm x⟩
          left_inv := fun x => Subtype.ext (by simp)
          right_inv := fun x => Subtype.ext (by simp) }
      refine Fintype.sum_equiv e _ _ (fun x => ?_)
      rw [← Module.End.mul_apply, ← map_mul]
      congr 2
      apply Subtype.ext
      simp only [kk, e, Equiv.coe_fn_mk, Subgroup.coe_mul]
      push_cast
      group
  choose y hy hinv using hlift

  have hwd : ∀ (s : G) (γ γ' : Γ) (κ κ' : K), (γ : G) * s * κ = γ' * s * κ' →
      ρ κ⁻¹ (y s) = ρ κ'⁻¹ (y s) := by
    intro s γ γ' κ κ' e
    have hk : s⁻¹ * ((γ'⁻¹ * γ : Γ) : G) * s = ((κ' * κ⁻¹ : K) : G) := by
      have h1 : (γ : G) * s = γ' * s * κ' * κ⁻¹ := by
        calc (γ : G) * s = (γ : G) * s * κ * (κ : G)⁻¹ := by group
          _ = γ' * s * κ' * (κ : G)⁻¹ := by rw [e]
      calc s⁻¹ * ((γ'⁻¹ * γ : Γ) : G) * s = s⁻¹ * ((γ' : G)⁻¹ * ((γ : G) * s)) := by
            push_cast; group
        _ = ((κ' * κ⁻¹ : K) : G) := by rw [h1]; push_cast; group
    have hmem : s⁻¹ * ((γ'⁻¹ * γ : Γ) : G) * s ∈ K := hk ▸ (κ' * κ⁻¹).2
    have hfix := hinv s (γ'⁻¹ * γ) hmem
    have heq : (⟨_, hmem⟩ : K) = κ' * κ⁻¹ := Subtype.ext hk
    rw [heq] at hfix
    calc ρ κ⁻¹ (y s) = ρ κ'⁻¹ (ρ (κ' * κ⁻¹) (y s)) := by
          rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel_left]
      _ = ρ κ'⁻¹ (y s) := by rw [hfix]

  have hrep : ∃ rep : G → G, (∀ (γ : Γ) (g : G) (κ : K), rep ((γ : G) * g * κ) = rep g) ∧
      ∀ g : G, ∃ (γ : Γ) (κ : K), g = (γ : G) * rep g * κ := by
    refine ⟨fun g => (DoubleCoset.mk Γ K g).out, ?_, ?_⟩
    · intro γ g κ
      have : DoubleCoset.mk Γ K ((γ : G) * g * κ) = DoubleCoset.mk Γ K g :=
        (DoubleCoset.eq Γ K _ _).2 ⟨(γ : G)⁻¹, Γ.inv_mem γ.2, (κ : G)⁻¹, K.inv_mem κ.2, by group⟩
      simp only [this]
    · intro g
      obtain ⟨h, k, hh, hk, e⟩ := DoubleCoset.mk_out_eq_mul Γ K g
      refine ⟨⟨h, hh⟩⁻¹, ⟨k, hk⟩⁻¹, ?_⟩
      simp only [e, Subgroup.coe_inv]
      group
  obtain ⟨rep, hrep1, hrep2⟩ := hrep
  choose γg κg hg using hrep2
  refine ⟨fun g => ρ (κg g)⁻¹ (y (rep g)), ?_, ?_⟩
  · intro γ g κ
    show ρ (κg ((γ : G) * g * κ))⁻¹ (y (rep ((γ : G) * g * κ))) = ρ κ⁻¹ (ρ (κg g)⁻¹ (y (rep g)))
    have e1 := hg ((γ : G) * g * κ)
    rw [hrep1] at e1 ⊢
    have e2 := hg g
    have key : ((γ * γg g : Γ) : G) * rep g * ((κg g * κ : K) : G) =
        (γg ((γ : G) * g * κ) : G) * rep g * (κg ((γ : G) * g * κ) : G) := by
      rw [← e1]
      conv_rhs => rw [e2]
      push_cast; group
    rw [← hwd (rep g) _ _ _ _ key, ← Module.End.mul_apply, ← map_mul, mul_inv_rev]
  · intro g
    calc π (ρ (κg g)⁻¹ (y (rep g))) = f ((γg g : G) * rep g * κg g) :=
          (hf (γg g) (rep g) (κg g) (y (rep g)) (hy (rep g)).symm).symm
      _ = f g := by rw [← hg g]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftModMaximalSkewStatement
section
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_skew_lift_mod_maximalIdeal : ∀ (O : Type) [CommRing O] [IsLocalRing O] (c : O →+* O), (∀ x, c (c x) = x) → IsUnit (2 : O) →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) O), (∀ i j, c (J j i) = J i j) → IsUnit J.det →
    ∀ Z₀ : Matrix (Fin n) (Fin n) O, (∀ i j, (Z₀ᵀ * J + J * Z₀.map c) i j ∈ IsLocalRing.maximalIdeal O) →
      ∃ Z : Matrix (Fin n) (Fin n) O, Zᵀ * J + J * Z.map c = 0 ∧ ∀ i j, Z i j - Z₀ i j ∈ IsLocalRing.maximalIdeal O := by
  first | exact @GlobalTheory.lift_mod_maximal_skew | exact GlobalTheory.lift_mod_maximal_skew | (intros; apply GlobalTheory.lift_mod_maximal_skew <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftRingHomAffineOpenOfArtinianSchemeLift
section
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem lift_ringHom_of_scheme_lift : ∀ (B : Type) [CommRing B] (X : Scheme.{0}) (s : X ⟶ Sp B), (∀ (C C₀ : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → RingHom.ker π ^ 2 = ⊥ → ∀ (t : Sp C ⟶ Sp B) (x₀ : Sp C₀ ⟶ X), x₀ ≫ s = spMap π ≫ t → ∃ x : Sp C ⟶ X, spMap π ≫ x = x₀ ∧ x ≫ s = t) → ∀ (U : (Sp B).Opens), IsAffineOpen U → ∀ (V : X.Opens), IsAffineOpen V → ∀ (e : V ≤ s ⁻¹ᵁ U), (∀ (C C₀ : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → RingHom.ker π ^ 2 = ⊥ → ∀ (β : Γ(Sp B, U) →+* C) (φ₀ : Γ(X, V) →+* C₀), φ₀.comp ((s.appLE U V e).hom) = π.comp β → ∃ φ : Γ(X, V) →+* C, π.comp φ = φ₀ ∧ φ.comp ((s.appLE U V e).hom) = β) := by
  intro B _ X s hlift U hU V hV e C C₀ _ _ _ _ π hπ hk β φ₀ hcomp

  haveI : Nontrivial C₀ := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    have h1 : (1 : C) ∈ RingHom.ker π := by
      rw [RingHom.mem_ker]; exact Subsingleton.elim _ _
    have h2 : (1 : C) ∈ RingHom.ker π ^ 2 := by
      have := Ideal.mul_mem_mul h1 h1
      simpa [pow_two] using this
    rw [hk, Ideal.mem_bot] at h2
    exact one_ne_zero h2
  have hsub : ∀ a b : PrimeSpectrum C, a = b := by
    intro a b
    ext1
    rw [IsLocalRing.eq_maximalIdeal (IsArtinianRing.isMaximal_of_isPrime a.asIdeal),
      IsLocalRing.eq_maximalIdeal (IsArtinianRing.isMaximal_of_isPrime b.asIdeal)]
  have hA := IsAffineOpen.SpecMap_appLE_fromSpec s hU hV e
  have hx₀ : (Spec.map (CommRingCat.ofHom φ₀) ≫ hV.fromSpec) ≫ s =
      spMap π ≫ (Spec.map (CommRingCat.ofHom β) ≫ hU.fromSpec) := by
    rw [Category.assoc, ← hA, ← Category.assoc, ← Spec.map_comp, ← Category.assoc, spMap,
      ← Spec.map_comp]
    congr 2
    ext1
    exact hcomp
  obtain ⟨x, hx1, hx2⟩ := hlift C C₀ π hπ hk _ _ hx₀
  have hrange : Set.range x ⊆ Set.range hV.fromSpec := by
    rintro _ ⟨p, rfl⟩
    obtain ⟨q⟩ := (inferInstance : Nonempty (PrimeSpectrum C₀))
    have hp : p = (spMap π) q := hsub _ _
    refine ⟨(Spec.map (CommRingCat.ofHom φ₀)) q, ?_⟩
    rw [hp]
    have := congrArg (fun f : Sp C₀ ⟶ X => f q) hx1
    first
      | exact this.symm
      | (rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at this; exact this.symm)
      | (simp only [Scheme.Hom.comp_base, TopCat.comp_app] at this; exact this.symm)
  have hyx : IsOpenImmersion.lift hV.fromSpec x hrange ≫ hV.fromSpec = x :=
    IsOpenImmersion.lift_fac _ _ _
  obtain ⟨φ, hφ⟩ : ∃ φ, Spec.map φ = IsOpenImmersion.lift hV.fromSpec x hrange :=
    ⟨_, Spec.map_preimage _⟩
  rw [← hφ] at hyx
  refine ⟨φ.hom, ?_, ?_⟩
  · have h3 : Spec.map (CommRingCat.ofHom (π.comp φ.hom)) ≫ hV.fromSpec =
        Spec.map (CommRingCat.ofHom φ₀) ≫ hV.fromSpec := by
      rw [← hx1, ← hyx, spMap, ← Category.assoc, ← Spec.map_comp]
      rfl
    have h4 := Spec.map_injective ((cancel_mono hV.fromSpec).1 h3)
    exact congrArg CommRingCat.Hom.hom h4
  · have h3 : Spec.map (CommRingCat.ofHom (φ.hom.comp (s.appLE U V e).hom)) ≫
        hU.fromSpec = Spec.map (CommRingCat.ofHom β) ≫ hU.fromSpec := by
      rw [← hx2, ← hyx, Category.assoc, ← hA, ← Category.assoc,
        ← Spec.map_comp]
      rfl
    have h4 := Spec.map_injective ((cancel_mono hU.fromSpec).1 h3)
    exact congrArg CommRingCat.Hom.hom h4

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinIndepIntBilinFormCharZeroCombinationEqZeroStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linIndep_intBilinForm_charZero_combination_eq_zero : ∀ {X : Type} [AddCommGroup X] {m : ℕ} (gam : Fin m → LinearMap.BilinForm ℤ X) (k : Type) [Field k] [CharZero k] (a : Fin m → k), LinearIndependent ℤ gam → (∀ y z, ∑ i, a i * (gam i y z : k) = 0) → a = 0 := by
  first | exact @GlobalTheory.linIndep_intBilinForm_charZero_comb_eq_zero | exact GlobalTheory.linIndep_intBilinForm_charZero_comb_eq_zero | (intros; apply GlobalTheory.linIndep_intBilinForm_charZero_comb_eq_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearIndepOnPowOfIsDomainTensorPurelyInseparablStatement
section
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linearIndepOn_frob_pow_of_isDomain_tensor_insep : ∀ (k B : Type) [Field k] [CommRing B] [IsDomain B] [Algebra k B] (p : ℕ), p.Prime → CharP k p → (∀ (K : Type) [Field K] [Algebra k K], FiniteDimensional k K → IsPurelyInseparable k K → IsDomain (K ⊗[k] B)) → ∀ s : Finset (FractionRing B), LinearIndepOn k _root_.id (s : Set (FractionRing B)) → LinearIndepOn k (· ^ p) (s : Set (FractionRing B)) := by
  first | exact @GlobalTheory.linearIndepOn_pow_of_isDomain_tensor_purelyInseparable | exact GlobalTheory.linearIndepOn_pow_of_isDomain_tensor_purelyInseparable | (intros; apply GlobalTheory.linearIndepOn_pow_of_isDomain_tensor_purelyInseparable <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearIndependentComplexMapStatement
section
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linear_independent_complex_map : ∀ {E : Type} [Field E] {r n : ℕ} (τ : E →+* ℂ) (e : Fin n → Matrix (Fin r) (Fin r) E), LinearIndependent E e → LinearIndependent ℝ (fun i => (e i).map τ) := by
  first | exact @GlobalTheory.linearIndependent_real_map_of_fieldEmb | exact GlobalTheory.linearIndependent_real_map_of_fieldEmb | (intros; apply GlobalTheory.linearIndependent_real_map_of_fieldEmb <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearIndependentKaehlerDOfAlgebraicIndependentStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linearIndependent_kaehlerD_of_algebraicIndependent : ∀ (k κ : Type) [Field k] [CharZero k] [Field κ] [Algebra k κ] [Algebra.EssFiniteType k κ] {σ : Type} (t : σ → κ), AlgebraicIndependent k t → LinearIndependent κ (fun s => KaehlerDifferential.D k κ (t s)) := by
  first | exact @GlobalTheory.BertiniAlg.linearIndependent_D_of_algebraicIndependent | exact GlobalTheory.BertiniAlg.linearIndependent_D_of_algebraicIndependent | (intros; apply GlobalTheory.BertiniAlg.linearIndependent_D_of_algebraicIndependent <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearIndependentOfDistinctValuationLikeStatement
section
open Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linearIndependent_of_injective_valuationLike : ∀ (C V Γ ι : Type) [Field C] [AddCommGroup V] [Module C V] [LinearOrder Γ] (ν : V → Γ), (∀ (c : C) (u : V), c ≠ 0 → ν (c • u) = ν u) → (∀ u v : V, u ≠ 0 → v ≠ 0 → ν u < ν v → u + v ≠ 0 ∧ ν (u + v) = ν u) → ∀ f : ι → V, (∀ i, f i ≠ 0) → Function.Injective (fun i => ν (f i)) → LinearIndependent C f := by
  first | exact @GlobalTheory.linearIndependent_of_distinct_valuationLike | exact GlobalTheory.linearIndependent_of_distinct_valuationLike | (intros; apply GlobalTheory.linearIndependent_of_distinct_valuationLike <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralNormPowMulLeSqrtWeightedSqStatement
section
open MeasureTheory Filter Topology Set Module
open scoped ENNReal

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lintegral_norm_pow_mul_le_sqrt_weighted_sq : ∀ {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] [NormedAddCommGroup F], ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ (H : E → F), Continuous H → ∀ k : ℕ, ∫⁻ z, ENNReal.ofReal (‖z‖ ^ k * ‖H z‖) ∂μ ≤ C * (∫⁻ z, ENNReal.ofReal ((‖z‖ ^ k * ‖H z‖) ^ 2) ∂μ + ∫⁻ z, ENNReal.ofReal ((‖z‖ ^ (k + finrank ℝ E + 1) * ‖H z‖) ^ 2) ∂μ) ^ (1 / 2 : ℝ) := by
  first | exact @GlobalTheory.lintegral_norm_pow_mul_le_sqrt_weighted_sq | exact GlobalTheory.lintegral_norm_pow_mul_le_sqrt_weighted_sq | (intros; apply GlobalTheory.lintegral_norm_pow_mul_le_sqrt_weighted_sq <;> assumption)
end

