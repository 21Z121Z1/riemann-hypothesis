import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.QuadraticClassFieldTheory
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0114
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0155
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0156
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0091
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0157

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierSumsCosetsSemidirectCyclic
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin.CosetFourier

theorem star_eq_inv_of_pow_eq_one {w : ℂ} {n : ℕ} (hn : n ≠ 0) (hw : w ^ n = 1) :
    star w = w⁻¹ := by
  have h1 : ‖w‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hw hn
  have h2 : Complex.normSq w = 1 := by
    rw [Complex.normSq_eq_norm_sq, h1]; norm_num
  rw [Complex.inv_def, h2]; simp [Complex.star_def]

theorem geom_sum_root_of_unity {w : ℂ} {n : ℕ} (hw : w ^ n = 1) :
    ∑ a ∈ Finset.range n, w ^ a = if w = 1 then (n : ℂ) else 0 := by
  split_ifs with h
  · simp [h]
  · rw [geom_sum_eq h, hw]; simp

theorem fourier_coset_sums : ∀ (G Γ : Type) [Group G] [Finite G] [Group Γ] [Fintype Γ] (φ : Γ →* MulAut G) (s : Γ), (∀ t : Γ, t ∈ Subgroup.zpowers s) → ∀ ζ : ℂ, IsPrimitiveRoot ζ (Nat.card Γ) → ∃ η : G ⋊[φ] Γ →* ℂˣ, (∀ g, η (inl g) = 1) ∧ (η (inr s) : ℂ) = ζ ∧ ∀ X Y : G ⋊[φ] Γ → ℂ, ((Nat.card Γ : ℂ) * ∑ᶠ g, X (inl g) * star (Y (inl g)) = ∑ a ∈ Finset.range (Nat.card Γ), ∑ᶠ x, X x * star (Y x * (η x : ℂ) ^ a)) ∧ (Nat.card Γ : ℂ) * ∑ᶠ g, X (inl g * inr s) * star (Y (inl g * inr s)) = ∑ a ∈ Finset.range (Nat.card Γ), ζ ^ a * ∑ᶠ x, X x * star (Y x * (η x : ℂ) ^ a) := by
  intro G Γ _ _ _ _ φ s hs ζ hζ
  have hn0 : Nat.card Γ ≠ 0 := Nat.card_pos.ne'
  have hord : orderOf s = Nat.card Γ := orderOf_eq_card_of_forall_mem_zpowers hs
  let u : ℂˣ := Units.mk0 ζ (hζ.ne_zero hn0)
  have hu : orderOf u ∣ orderOf s := by
    apply orderOf_dvd_of_pow_eq_one
    rw [hord]; ext
    simp only [Units.val_pow_eq_pow_val, Units.val_one, u, Units.val_mk0]
    exact hζ.pow_eq_one
  let η₀ : Γ →* ℂˣ := monoidHomOfForallMemZpowers hs hu
  have hη₀s : η₀ s = u := monoidHomOfForallMemZpowers_apply_gen hs hu
  have hinj : Function.Injective η₀ := by
    rw [injective_iff_map_eq_one]
    intro t ht
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hs t)
    rw [map_zpow, hη₀s] at ht
    have hk : ζ ^ k = 1 := by
      have := congrArg Units.val ht
      simpa [u, Units.val_zpow_eq_zpow_val] using this
    rw [hζ.zpow_eq_one_iff_dvd] at hk
    rw [← orderOf_dvd_iff_zpow_eq_one, hord]; exact hk
  let η : G ⋊[φ] Γ →* ℂˣ := η₀.comp rightHom
  have hηx : ∀ x, η x = η₀ x.right := fun x => rfl
  have hpow : ∀ x, (η x : ℂ) ^ Nat.card Γ = 1 := by
    intro x
    rw [hηx, ← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one']; simp
  have hstar : ∀ x, star (η x : ℂ) = (η x : ℂ)⁻¹ := fun x => star_eq_inv_of_pow_eq_one hn0 (hpow x)
  have hone : ∀ x : G ⋊[φ] Γ, (η x : ℂ)⁻¹ = 1 ↔ x.right = 1 := by
    intro x
    rw [inv_eq_one, Units.val_eq_one, hηx, ← map_one η₀, hinj.eq_iff]
  have hzeta : ∀ x : G ⋊[φ] Γ, ζ * (η x : ℂ)⁻¹ = 1 ↔ x.right = s := by
    intro x
    have hne : (η x : ℂ) ≠ 0 := (η x).ne_zero
    rw [mul_inv_eq_one₀ hne, eq_comm, hηx]
    have : ζ = ((η₀ s : ℂˣ) : ℂ) := by rw [hη₀s]; rfl
    rw [this, Units.val_inj, hinj.eq_iff]
  refine ⟨η, fun g => by simp [η], by rw [show η (inr s) = η₀ s from by simp [η], hη₀s]; rfl, ?_⟩
  intro X Y
  haveI : Fintype G := Fintype.ofFinite G
  let e : G ⋊[φ] Γ ≃ G × Γ :=
    ⟨fun x => (x.left, x.right), fun p => ⟨p.1, p.2⟩, fun _ => rfl, fun _ => rfl⟩
  haveI : Fintype (G ⋊[φ] Γ) := Fintype.ofEquiv (G × Γ) e.symm

  have key : ∀ (c : ℂ) (t : Γ), (∀ x : G ⋊[φ] Γ, c * (η x : ℂ)⁻¹ = 1 ↔ x.right = t) →
      c ^ Nat.card Γ = 1 →
      ∑ a ∈ Finset.range (Nat.card Γ), c ^ a * ∑ᶠ x, X x * star (Y x * (η x : ℂ) ^ a) =
        (Nat.card Γ : ℂ) * ∑ g : G, X ⟨g, t⟩ * star (Y ⟨g, t⟩) := by
    intro c t hct hc
    simp_rw [finsum_eq_sum_of_fintype, Finset.mul_sum]
    rw [Finset.sum_comm]
    have hterm : ∀ x : G ⋊[φ] Γ, ∑ a ∈ Finset.range (Nat.card Γ), c ^ a * (X x * star (Y x * (η x : ℂ) ^ a))
        = X x * star (Y x) * (if x.right = t then (Nat.card Γ : ℂ) else 0) := by
      intro x
      have : ∀ a, c ^ a * (X x * star (Y x * (η x : ℂ) ^ a)) = X x * star (Y x) * (c * (η x : ℂ)⁻¹) ^ a := by
        intro a
        rw [star_mul', star_pow, hstar, mul_pow]; ring
      simp_rw [this]
      rw [← Finset.mul_sum, geom_sum_root_of_unity (by rw [mul_pow, inv_pow, hc, hpow, inv_one, one_mul])]
      simp only [hct]
    simp_rw [hterm]
    rw [← e.symm.sum_comp, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun g _ => ?_
    simp [e, mul_comm]
  refine ⟨?_, ?_⟩
  · have := key 1 1 (fun x => by rw [one_mul]; exact hone x) (one_pow _)
    simp only [one_pow, one_mul] at this
    rw [this, finsum_eq_sum_of_fintype]
    rfl
  · rw [key ζ s hzeta hζ.pow_eq_one, finsum_eq_sum_of_fintype]
    congr 1
    refine Finset.sum_congr rfl fun g _ => ?_
    have : (inl g * inr s : G ⋊[φ] Γ) = ⟨g, s⟩ := by ext <;> simp
    rw [this]

end GlobalTheory.Shin.CosetFourier
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameDual
section
open ReciprocityTheory.PGsh GlobalTheory.FGDepth

namespace GlobalTheory.FrameDual

open Matrix Finset

variable {C : Type} [Field C]

def intSubring (v : AddValuation C (WithTop ℝ)) : Subring C where
  carrier := {x | IsIntV v x}
  zero_mem' := by simp [IsIntV]
  one_mem' := by simp [IsIntV]
  add_mem' := by
    intro x y hx hy
    exact le_trans (le_min hx hy) (v.map_add x y)
  mul_mem' := by
    intro x y hx hy
    show 0 ≤ v (x * y)
    rw [v.map_mul]; exact add_nonneg hx hy
  neg_mem' := by
    intro x hx
    show 0 ≤ v (-x)
    rw [v.map_neg]; exact hx

theorem adjugate_int (v : AddValuation C (WithTop ℝ)) {n : ℕ} (M : Matrix (Fin n) (Fin n) C)
    (hM : ∀ a b, IsIntV v (M a b)) (a b : Fin n) : IsIntV v (M.adjugate a b) := by
  let M' : Matrix (Fin n) (Fin n) (intSubring v) := Matrix.of fun a b => ⟨M a b, hM a b⟩
  have hMM : (intSubring v).subtype.mapMatrix M' = M := by
    ext a b; rfl
  have := RingHom.map_adjugate (intSubring v).subtype M'
  rw [hMM] at this
  rw [← this]
  exact (M'.adjugate a b).2

theorem frameDual (C : Type) [Field C] (v : AddValuation C (WithTop ℝ)) (i d : ℕ)
    (u : Fin i → Fin d → C) (hu : IsSatFrame v u) :
    ∃ l : Fin i → Fin d → C, (∀ a e, IsIntV v (l a e)) ∧
      ∀ a a', ∑ e, l a e * u a' e = if a = a' then 1 else 0 := by
  obtain ⟨hint, r, hr⟩ := hu
  set M : Matrix (Fin i) (Fin i) C := Matrix.of fun a b => u a (r b) with hMdef
  have hdet0 : M.det ≠ 0 := by
    intro h; rw [h, v.map_zero] at hr; exact WithTop.top_ne_coe hr
  have hdetU : IsUnit M.det := isUnit_iff_ne_zero.mpr hdet0
  have hinvdet : IsIntV v (M.det)⁻¹ := by
    show 0 ≤ v (M.det)⁻¹
    rw [v.map_inv, hr, neg_zero]
  have hNint : ∀ a b, IsIntV v (M⁻¹ a b) := by
    intro a b
    rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
    exact (intSubring v).mul_mem hinvdet (adjugate_int v M (fun a b => hint _ _) a b)
  refine ⟨fun a e => ∑ b, if r b = e then M⁻¹ b a else 0, ?_, ?_⟩
  · intro a e
    exact (intSubring v).sum_mem fun b _ => by
      split_ifs
      · exact hNint b a
      · exact (intSubring v).zero_mem
  · intro a a'
    have hMN := Matrix.mul_nonsing_inv M hdetU
    have h1 := congrFun (congrFun hMN a') a
    rw [Matrix.mul_apply, Matrix.one_apply] at h1
    calc ∑ e, (∑ b, if r b = e then M⁻¹ b a else 0) * u a' e
        = ∑ e, ∑ b, if r b = e then u a' (r b) * M⁻¹ b a else 0 := by
          refine Finset.sum_congr rfl fun e _ => ?_
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun b _ => ?_
          split_ifs with h
          · rw [h, mul_comm]
          · rw [zero_mul]
      _ = ∑ b, ∑ e, if r b = e then u a' (r b) * M⁻¹ b a else 0 := Finset.sum_comm
      _ = ∑ b, M a' b * M⁻¹ b a := by
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [Finset.sum_ite_eq]; simp [hMdef]
      _ = if a = a' then 1 else 0 := by
          rw [h1]; exact if_congr eq_comm rfl rfl

end GlobalTheory.FrameDual
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobLiftLocalization
section
open GlobalTheory GlobalTheory.DI

namespace GlobalTheory.DI

theorem frobLift_localization :
    ∀ (p : ℕ) [Fact p.Prime] {B Kt : Type} [CommRing B] [CommRing Kt] [Algebra B Kt]
      (S : Submonoid B) [IsLocalization S Kt] (F : B →+* B), (p : B) ^ 2 = 0 →
      (∀ z, ∃ w, F z = z ^ p + p * w) →
      ∃ F' : Kt →+* Kt, (∀ b, F' (algebraMap B Kt b) = algebraMap B Kt (F b)) ∧
        ∀ z, ∃ w, F' z = z ^ p + p * w := by
  intro p _ B Kt _ _ _ S _ F hp2 hF
  have hunit : ∀ s : S, IsUnit ((algebraMap B Kt).comp F s) := by
    intro s
    obtain ⟨w, hw⟩ := hF (s : B)
    have hu : IsUnit (algebraMap B Kt (s : B) ^ p) :=
      (IsLocalization.map_units Kt s).pow p
    have hn : IsNilpotent ((p : Kt) * algebraMap B Kt w) := by
      refine ⟨2, ?_⟩
      have : (p : Kt) ^ 2 = 0 := by
        have := congrArg (algebraMap B Kt) hp2
        simpa using this
      rw [mul_pow, this, zero_mul]
    have := hn.isUnit_add_right_of_commute hu (Commute.all _ _)
    rw [add_comm] at this
    simpa [RingHom.comp_apply, hw, map_add, map_mul, map_pow, map_natCast] using this
  refine ⟨IsLocalization.lift hunit, fun b => by simp [IsLocalization.lift_eq], ?_⟩
  intro z
  obtain ⟨⟨b, s⟩, rfl⟩ := IsLocalization.mk'_surjective S z
  set z := IsLocalization.mk' Kt b s with hz
  set F' : Kt →+* Kt := IsLocalization.lift hunit
  have hF' : ∀ c, F' (algebraMap B Kt c) = algebraMap B Kt (F c) := fun c => by
    simp [F', IsLocalization.lift_eq]
  have hspec : z * algebraMap B Kt (s : B) = algebraMap B Kt b := IsLocalization.mk'_spec Kt b s
  obtain ⟨v, hv⟩ := hF b
  obtain ⟨u, hu⟩ := hF (s : B)
  have key : F' z * (algebraMap B Kt (s : B) ^ p + p * algebraMap B Kt u) =
      algebraMap B Kt b ^ p + p * algebraMap B Kt v := by
    have := congrArg F' hspec
    rw [map_mul, hF', hF', hu, hv] at this
    simpa [map_add, map_mul, map_pow, map_natCast] using this
  obtain ⟨t, ht⟩ := (IsLocalization.map_units Kt s).pow p
  refine ⟨(algebraMap B Kt v - F' z * algebraMap B Kt u) * ↑t⁻¹, ?_⟩
  have hzs : z ^ p * algebraMap B Kt (s : B) ^ p = algebraMap B Kt b ^ p := by
    rw [← mul_pow, hspec]
  have h1 : (F' z - z ^ p) * (t : Kt) = p * (algebraMap B Kt v - F' z * algebraMap B Kt u) := by
    rw [ht]; linear_combination key - hzs
  calc F' z = z ^ p + (F' z - z ^ p) * (t : Kt) * ↑t⁻¹ := by
        rw [mul_assoc, Units.mul_inv, mul_one]; ring
    _ = _ := by rw [h1]; ring

end GlobalTheory.DI
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FromKSurjective
section
noncomputable section
open NumberField

namespace GlobalTheory.LKTorus.KerOne

variable {K L : Type} [Field K] [Field L] [CharZero K] [CharZero L] [Algebra K L]

def cK (c : L →ₐ[ℚ] L) (hcK : ∀ x : K, c (algebraMap K L x) = algebraMap K L x) : L →ₐ[K] L :=
  { c.toRingHom with commutes' := hcK }

@[simp] theorem cK_apply (c : L →ₐ[ℚ] L) (hcK : ∀ x : K, c (algebraMap K L x) = algebraMap K L x) (x : L) :
    cK c hcK x = c x := rfl

def fixOfK (c : L →ₐ[ℚ] L) (hcK : ∀ x : K, c (algebraMap K L x) = algebraMap K L x) : Kˣ →* fixU ℚ c where
  toFun a := ⟨Units.map (algebraMap K L : K →* L) a, hcK a⟩
  map_one' := by ext; simp
  map_mul' a b := by ext; simp

@[simp] theorem fixOfK_apply (c : L →ₐ[ℚ] L) (hcK : ∀ x : K, c (algebraMap K L x) = algebraMap K L x) (a : Kˣ) :
    (((fixOfK c hcK a : fixU ℚ c) : Lˣ) : L) = algebraMap K L a := rfl

def fromK (c : L →ₐ[ℚ] L) (hcK : ∀ x : K, c (algebraMap K L x) = algebraMap K L x) : Kˣ →* H1 ℚ c :=
  (QuotientGroup.mk' (normSub ℚ c)).comp (fixOfK c hcK)

variable (K L) in

def ratNormSub : Subgroup Kˣ :=
  (Units.map (algebraMap ℚ K : ℚ →* K)).range ⊔ GlobalTheory.QuadSymbol.globalNorms K L

section Quad

variable [Algebra.IsQuadraticExtension K L]

def cE (c : L →ₐ[ℚ] L) (hcK : ∀ x : K, c (algebraMap K L x) = algebraMap K L x) : L ≃ₐ[K] L :=
  AlgEquiv.ofBijective (cK c hcK) (Algebra.IsAlgebraic.algHom_bijective _)

@[simp] theorem cE_apply (c : L →ₐ[ℚ] L) (hcK : ∀ x : K, c (algebraMap K L x) = algebraMap K L x) (x : L) :
    cE c hcK x = c x := rfl

end Quad

end GlobalTheory.LKTorus.KerOne
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisComparisonMapInjectiveOfFlat
section
open scoped TensorProduct

theorem GlobalTheory.GoodEtale.galMap_injective_of_flat : ∀ (A R C O : Type) [CommRing A] [CommRing R] [Algebra A R] [CommRing C] [Algebra R C]
    [CommRing O] [Algebra R O] [Module.Flat R O]
    (G : Type) [Group G] [Fintype G] [DecidableEq G] (act : G →* (C ≃ₐ[R] C)) (T : C →ₗ[R] R),
    (∀ c, algebraMap R C (T c) = ∑ g, act g c) →
    ∀ (a : A), a ≠ 0 → ∀ (n : ℕ) (x y : Fin n → C),
      (∀ g, ∑ i, x i * act g (y i) = if g = 1 then algebraMap R C (algebraMap A R a) else 0) →
    GlobalTheory.GoodEtale.TorsionFreeOver A R C → ∀ σ : C →ₐ[R] O, Function.Injective (GlobalTheory.GoodEtale.galMap act σ) := by
  intro A R C O _ _ _ _ _ _ _ _ G _ _ _ act T hT a ha n x y hxy htf σ
  set b := algebraMap R C (algebraMap A R a) with hb
  have key : ∀ c : C, ∑ i, T (y i * c) • x i = b * c := by
    intro c
    have h1 : ∀ i, T (y i * c) • x i = ∑ g, x i * act g (y i) * act g c := by
      intro i; rw [Algebra.smul_def, hT, mul_comm, Finset.mul_sum]
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [map_mul, mul_assoc]
    simp_rw [h1]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, hxy]
    simp
  let L := LinearMap.lTensor O (LinearMap.mulLeft R b)
  have hL : Function.Injective L := by
    apply Module.Flat.lTensor_preserves_injective_linearMap
    rw [injective_iff_map_eq_zero]
    intro c hc
    exact htf a ha c (by rw [Algebra.smul_def]; simpa using hc)
  let Φ : (G → O) → O ⊗[R] C := fun f => ∑ i, (∑ g, σ (act g (y i)) * f g) ⊗ₜ x i
  have hΦ : ∀ m, Φ (GlobalTheory.GoodEtale.galMap act σ m) = L m := by
    intro m
    induction m using TensorProduct.induction_on with
    | zero => simp [Φ]
    | tmul o c =>
      simp only [Φ, GlobalTheory.GoodEtale.galMap_tmul, L, LinearMap.lTensor_tmul, LinearMap.mulLeft_apply]
      have h2 : ∀ i, (∑ g, σ (act g (y i)) * (o * σ (act g c))) = T (y i * c) • o := by
        intro i
        rw [Algebra.smul_def, ← σ.commutes, hT, map_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun g _ => ?_
        rw [map_mul, map_mul]; ring
      simp_rw [h2, ← key, TensorProduct.tmul_sum, TensorProduct.smul_tmul]
    | add m m' hm hm' =>
      rw [map_add, map_add, ← hm, ← hm']
      simp only [Φ, Pi.add_apply, mul_add, Finset.sum_add_distrib, TensorProduct.add_tmul]
  rw [injective_iff_map_eq_zero]
  intro m hm
  apply hL
  rw [← hΦ, hm, map_zero]
  simp [Φ]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisDescentSemilinearBijective
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin

theorem semilinear_pow_smul {F F' V : Type} [Field F] [Field F'] [Algebra F F'] [AddCommGroup V]
    [Module F' V] [Module F V] (s : F' ≃ₐ[F] F') (T : Module.End F V)
    (hT : ∀ (c : F') (v : V), T (c • v) = s c • T v) (m : ℕ) (c : F') (v : V) :
    (T ^ m) (c • v) = (s ^ m) c • (T ^ m) v := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', pow_succ', Module.End.mul_apply, ih, hT, AlgEquiv.mul_apply, Module.End.mul_apply]

theorem pow_apply_of_mem_ker_sub_one {F V : Type} [Field F] [AddCommGroup V] [Module F V]
    (T : Module.End F V) (u : V) (hu : u ∈ LinearMap.ker (T - 1)) (m : ℕ) : (T ^ m) u = u := by
  have h1 : T u = u := by
    have h := LinearMap.mem_ker.mp hu
    rwa [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at h
  induction m with
  | zero => simp
  | succ m ih => rw [pow_succ, Module.End.mul_apply, h1, ih]

theorem algebraMap_trace_eq_sum_pow {F F' : Type} [Field F] [Field F'] [Algebra F F'] [Finite F']
    (s : F' ≃ₐ[F] F') (hs : ∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s) (x : F') :
    algebraMap F F' (Algebra.trace F F' x) = ∑ j : Fin (Module.finrank F F'), (s ^ (j : ℕ)) x := by
  classical
  have : Finite F := Finite.of_injective _ (algebraMap F F').injective
  have : FiniteDimensional F F' := Module.Finite.of_finite
  rw [trace_eq_sum_automorphisms]
  have hord : orderOf s = Module.finrank F F' := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hs, IsGalois.card_aut_eq_finrank]
  have hinj : Function.Injective (fun j : Fin (Module.finrank F F') => s ^ (j : ℕ)) := by
    intro i j hij
    simp only at hij
    rw [pow_inj_mod, hord, Nat.mod_eq_of_lt i.2, Nat.mod_eq_of_lt j.2] at hij
    exact Fin.ext hij
  have hbij : Function.Bijective (fun j : Fin (Module.finrank F F') => s ^ (j : ℕ)) :=
    (Fintype.bijective_iff_injective_and_card _).mpr
      ⟨hinj, by rw [Fintype.card_fin, ← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank]⟩
  exact (Fintype.sum_bijective _ hbij _ _ (fun j => rfl)).symm

end GlobalTheory.Shin

namespace GlobalTheory.Shin

theorem galoisDescent_semilinear_bijective : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (s : F' ≃ₐ[F] F'), (∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s) → ∀ (V : Type) [AddCommGroup V] [Module F' V] [Module F V] [IsScalarTower F F' V] (T : Module.End F V), (∀ (c : F') (v : V), T (c • v) = s c • T v) → T ^ Module.finrank F F' = 1 → ∀ (ι : Type) [Fintype ι] (b : Module.Basis ι F F'), Function.Bijective (fun v : ι → LinearMap.ker (T - 1) => ∑ i, b i • (v i : V)) := by
  intro F F' _ _ _ _ s hs V _ _ _ _ T hT hTn ι _ b
  classical
  have : Finite F := Finite.of_injective _ (algebraMap F F').injective
  have : FiniteDimensional F F' := Module.Finite.of_finite
  set n := Module.finrank F F' with hn
  have hnd := traceForm_nondegenerate F F'
  set d := (Algebra.traceForm F F').dualBasis hnd b with hd
  have hdb : ∀ i j, Algebra.trace F F' (d i * b j) = if j = i then 1 else 0 := fun i j => by
    have h := LinearMap.BilinForm.apply_dualBasis_left hnd b i j
    simpa [Algebra.traceForm_apply] using h
  have key1 : ∀ i j, ∑ k : Fin n, (s ^ (k : ℕ)) (d i) * (s ^ (k : ℕ)) (b j) =
      if i = j then 1 else 0 := by
    intro i j
    have h := algebraMap_trace_eq_sum_pow s hs (d i * b j)
    simp only [map_mul] at h
    rw [← h, hdb]
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij, Ne.symm hij]
  have hTk : ∀ (k : ℕ) (c : F') (v : V), (T ^ k) (c • v) = (s ^ k) c • (T ^ k) v :=
    semilinear_pow_smul s T hT
  have hfix : ∀ (u : LinearMap.ker (T - 1)) (k : ℕ), (T ^ k) (u : V) = u :=
    fun u k => pow_apply_of_mem_ker_sub_one T u u.2 k
  have hn0 : 0 < n := Module.finrank_pos
  have hcard : Fintype.card ι = n := (Module.finrank_eq_card_basis b).symm
  let e : ι ≃ Fin n := Fintype.equivFinOfCardEq hcard
  let A : Matrix (Fin n) ι F' := fun k j => (s ^ (k : ℕ)) (b j)
  let B : Matrix ι (Fin n) F' := fun i k => (s ^ (k : ℕ)) (d i)
  have hBA : B * A = 1 := by
    ext i j
    rw [Matrix.mul_apply, Matrix.one_apply]
    exact key1 i j
  have hAB : A * B = 1 := (Matrix.mul_eq_one_comm_of_equiv e.symm).mpr hBA
  let k0 : Fin n := ⟨0, hn0⟩
  have key2 : ∀ l : Fin n, ∑ i, b i * (s ^ (l : ℕ)) (d i) = if k0 = l then 1 else 0 := by
    intro l
    have h := congrFun (congrFun hAB k0) l
    rw [Matrix.mul_apply, Matrix.one_apply] at h
    simpa [A, B, k0] using h
  constructor
  · intro v w hvw
    simp only at hvw
    have hk : ∀ k : ℕ, ∑ i, (s ^ k) (b i) • (v i : V) = ∑ i, (s ^ k) (b i) • (w i : V) := by
      intro k
      have h := congrArg (T ^ k) hvw
      simpa only [map_sum, hTk, hfix] using h
    have expand : ∀ (u : ι → LinearMap.ker (T - 1)) (j : ι), (u j : V) =
        ∑ k : Fin n, (s ^ (k : ℕ)) (d j) • ∑ i, (s ^ (k : ℕ)) (b i) • (u i : V) := by
      intro u j
      simp_rw [Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      simp_rw [← Finset.sum_smul, key1]
      simp [ite_smul]
    funext j
    apply Subtype.ext
    rw [expand v j, expand w j]
    simp_rw [hk]
  · intro w
    let Q : V → V := fun u => ∑ k : Fin n, (T ^ (k : ℕ)) u
    have hQ : ∀ u, Q u ∈ LinearMap.ker (T - 1) := by
      intro u
      simp only [Q]
      rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero, map_sum]
      rw [Fin.sum_univ_eq_sum_range (fun k => T ((T ^ k) u)),
        Fin.sum_univ_eq_sum_range (fun k => (T ^ k) u)]
      have hs1 : ∀ k : ℕ, T ((T ^ k) u) = (T ^ (k + 1)) u := fun k => by
        rw [pow_succ', Module.End.mul_apply]
      simp_rw [hs1]
      have h1 := Finset.sum_range_succ' (fun k => (T ^ k) u) n
      have h2 := Finset.sum_range_succ (fun k => (T ^ k) u) n
      rw [h2, hTn, pow_zero] at h1
      exact (add_right_cancel h1).symm
    refine ⟨fun i => ⟨Q (d i • w), hQ _⟩, ?_⟩
    simp only [Q, hTk, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_smul, key2]
    simp [ite_smul, k0]

end GlobalTheory.Shin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussianIteratedFDerivWeightedExpBoundedStatement
section
open MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gaussian_iteratedFDeriv_weighted_exp_bounded : ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] (c α : ℝ), 0 < c → α < 1 → ∀ (k m : ℕ),
    ∃ K : ℝ, ∀ y : E, ‖y‖ ^ k * ‖iteratedFDeriv ℝ m (fun y : E => Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ))) y‖ *
      Real.exp (c * α * ‖y‖ ^ 2) ≤ K := by
  first | exact @GlobalTheory.GaussDerivBound.weighted_bound | exact GlobalTheory.GaussDerivBound.weighted_bound | (intros; apply GlobalTheory.GaussDerivBound.weighted_bound <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeomRegFibOfIsRegularRingTensorEssFiniteType
section
open IsLocalRing TensorProduct ReciprocityTheory.AnForm.R

namespace GlobalTheory

theorem geomRegFib_of_isRegularRing_essFiniteType :
    ∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B],
      (∀ (K : Type) [Field K] [Algebra R K] [Algebra.EssFiniteType R K], IsRegularRing (B ⊗[R] K)) →
        FinalTheorems.GeomRegFib R B := by
  intro R B _ _ _ h P _ K _ _ _ _ hfg
  haveI : Algebra.EssFiniteType P.ResidueField K := IntermediateField.fg_top_iff.mp hfg
  haveI : Algebra.EssFiniteType R K := Algebra.EssFiniteType.comp R P.ResidueField K
  haveI hr : IsRegularRing (B ⊗[R] K) := h K
  exact ⟨inferInstance, fun Q _ => hr.isRegularLocalRing_localization Q⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HartTensorOfFlatStatement
section
open IsLocalRing Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hart_baseChange_of_flat : ∀ (A R M O : Type) [CommRing A] [IsNoetherianRing A] [CommRing R] [Algebra A R]
    [AddCommGroup M] [Module R M] [CommRing O] [Algebra R O] [Algebra A O] [IsScalarTower A R O]
    [Module.Flat R O], GlobalTheory.GoodEtale.Hart A R M → GlobalTheory.GoodEtale.Hart A O (O ⊗[R] M) := by
  first | (exact @GlobalTheory.GoodEtale.hart_tensor_of_flat) | (exact GlobalTheory.GoodEtale.hart_tensor_of_flat) | (intros; apply GlobalTheory.GoodEtale.hart_tensor_of_flat  <;> assumption)
end

