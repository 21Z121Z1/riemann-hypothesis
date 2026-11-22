import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EtaleLocalizationAtPrimeTensorOfLowHeight
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0006

-- bundled from Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EigLat
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

variable {X : Scheme.{0}} {Ω : Type} [Field Ω]

variable {G : Over X} [GrpObj G] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {E : Type} [AddCommGroup E] [Module Ω E]

namespace LieModel

def Extends (M : LieModel G ξ E) (p : Cpt ξ) (e : E)
    (v : epsAt (R := X.presheaf.stalk p.1) (X.fromSpecStalk p.1) ⟶ G) : Prop :=
  IsTanAt G _ v ∧ (M.pt e).left = Spec.map (CommRingCat.ofHom (dualMap (genMap ξ p))) ≫ v.left

def lat (M : LieModel G ξ E) : Lat ξ E := fun p =>
  Submodule.span (regAt ξ p) {e | ∃ v, M.Extends p e v}

def omLat (M : LieModel G ξ E) : Lat ξ (Module.Dual Ω E) := M.lat.dual

def eigLat (M : LieModel G ξ E) {O : Type} [CommRing O] (ρ : O →+* Module.End Ω E) (σ : O →+* Ω) : Lat ξ E :=
  M.lat.inter (eigSp ρ σ)

variable {R : Type} [CommRing R] [IsLocalRing R]

def ValAt (M : LieModel G ξ E) (z : Spec (CommRingCat.of R) ⟶ X) (e : E) (w : epsAt z ⟶ G) : Prop :=
  ∃ (h : genPt ξ ⤳ centre z) (v : epsAt (R := X.presheaf.stalk (centre z)) (X.fromSpecStalk (centre z)) ⟶ G),
    M.Extends ⟨centre z, h⟩ e v ∧
      w.left = Spec.map (CommRingCat.ofHom (dualMap (Scheme.stalkClosedPointTo z).hom)) ≫ v.left

def fibAt (M : LieModel G ξ E) (L : Lat ξ E) (z : Spec (CommRingCat.of R) ⟶ X) {C : Type} [Field C] [Algebra R C]
    {EC : Type} [AddCommGroup EC] [Module C EC] [Module R EC]
    (MC : LieModel G (Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ z) EC) : Submodule R EC :=
  Submodule.span R {w | ∃ (h : genPt ξ ⤳ centre z) (e : E), e ∈ L ⟨centre z, h⟩ ∧
    M.ValAt (Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ z) e (MC.pt w)}

end LieModel

end GlobalTheory.CompanionTheory.Ar
end
end

-- bundled from Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsGenOfIsVBOne
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {E : Type} [AddCommGroup E] [Module Ω E]

def NormalCpt (ξ : Spec (CommRingCat.of Ω) ⟶ X) : Prop :=
  ∀ (p : Cpt ξ) (a : Ω), IsIntegral (regAt ξ p) a → a ∈ regAt ξ p

def zeroSet (ξ : Spec (CommRingCat.of Ω) ⟶ X) (ϖ : Ω) : Set X :=
  {q | ∃ h : genPt ξ ⤳ q, ¬ unitAt ξ ⟨q, h⟩ ϖ}

def TrivMod (L : Lat ξ E) (ϖ : Ω) : Prop :=
  ∃ t : Cpt ξ → E, ∀ p : Cpt ξ, ¬ unitAt ξ p ϖ → ∃ U : X.Opens, p.1 ∈ U ∧
    ∀ q : Cpt ξ, q.1 ∈ U → ¬ unitAt ξ q ϖ →
      t p ≠ 0 ∧ L q = Submodule.span (regAt ξ q) {t p} ∧ ∃ y ∈ L q, t p - t q = ϖ • y

def TrivRed (L : Lat ξ E) (ϖ : Ω) : Prop :=
  ∃ t : Cpt ξ → E, ∀ p : Cpt ξ, ¬ unitAt ξ p ϖ → ∃ U : X.Opens, p.1 ∈ U ∧
    ∀ q : Cpt ξ, q.1 ∈ U → ¬ unitAt ξ q ϖ →
      t p ≠ 0 ∧ L q = Submodule.span (regAt ξ q) {t p} ∧
        ∃ c ∈ regAt ξ q, ¬ unitAt ξ q c ∧ t p - t q = c • t p

def OrderAt (L : Lat ξ E) (σ : E) (ϖ : Ω) (M : ℕ) (a : ℤ) (p : Cpt ξ) : Prop :=
  ∃ (e : E) (c : Ω), e ≠ 0 ∧ L p = Submodule.span (regAt ξ p) {e} ∧ σ = c • e ∧ unitAt ξ p (c ^ M / ϖ ^ a)

namespace ZUnit

variable {p : Cpt ξ} {a b : Ω}

theorem one : unitAt ξ p 1 := ⟨one_ne_zero, one_mem _, by simp⟩

theorem mul (ha : unitAt ξ p a) (hb : unitAt ξ p b) : unitAt ξ p (a * b) :=
  ⟨mul_ne_zero ha.1 hb.1, mul_mem ha.2.1 hb.2.1, by rw [mul_inv]; exact mul_mem ha.2.2 hb.2.2⟩

theorem inv (ha : unitAt ξ p a) : unitAt ξ p a⁻¹ :=
  ⟨inv_ne_zero ha.1, ha.2.2, by rw [inv_inv]; exact ha.2.1⟩

theorem pow (ha : unitAt ξ p a) (n : ℕ) : unitAt ξ p (a ^ n) :=
  ⟨pow_ne_zero n ha.1, pow_mem ha.2.1 n, by rw [← inv_pow]; exact pow_mem ha.2.2 n⟩

theorem of_mul (ha : a ∈ regAt ξ p) (hb : b ∈ regAt ξ p) (h : unitAt ξ p (a * b)) : unitAt ξ p a := by
  have ha0 := left_ne_zero_of_mul h.1
  have hb0 := right_ne_zero_of_mul h.1
  refine ⟨ha0, ha, ?_⟩
  have : a⁻¹ = b * (a * b)⁻¹ := by field_simp
  rw [this]
  exact mul_mem hb h.2.2

theorem of_pow (ha : a ∈ regAt ξ p) {n : ℕ} (hn : n ≠ 0) (h : unitAt ξ p (a ^ n)) : unitAt ξ p a := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  exact of_mul ha (pow_mem ha m) (by rwa [← pow_succ'])

theorem mem_of_pow_mem (hN : NormalCpt ξ) {n : ℕ} (hn : n ≠ 0) (h : a ^ n ∈ regAt ξ p) : a ∈ regAt ξ p :=
  hN p a (IsIntegral.of_pow (Nat.pos_of_ne_zero hn) (isIntegral_algebraMap (x := (⟨a ^ n, h⟩ : regAt ξ p))))

theorem of_pow_of_normal (hN : NormalCpt ξ) {n : ℕ} (hn : n ≠ 0) (h : unitAt ξ p (a ^ n)) : unitAt ξ p a :=
  of_pow (mem_of_pow_mem hN hn h.2.1) hn h

theorem exists_of_span_eq {e e' : E} (he : e ≠ 0)
    (h : Submodule.span (regAt ξ p) {e} = Submodule.span (regAt ξ p) {e'}) :
    ∃ u : Ω, unitAt ξ p u ∧ e = u • e' := by
  have h1 : e ∈ Submodule.span (regAt ξ p) {e'} := by
    rw [← h]; exact Submodule.mem_span_singleton_self _
  have h2 : e' ∈ Submodule.span (regAt ξ p) {e} := by
    rw [h]; exact Submodule.mem_span_singleton_self _
  obtain ⟨u, hu⟩ := Submodule.mem_span_singleton.1 h1
  obtain ⟨v, hv⟩ := Submodule.mem_span_singleton.1 h2
  replace hu : (u : Ω) • e' = e := hu
  replace hv : (v : Ω) • e = e' := hv
  have huv : (u : Ω) * v = 1 := by
    apply smul_left_injective Ω he
    simp only [mul_smul, hv, hu, one_smul]
  exact ⟨u, of_mul u.2 v.2 (by rw [huv]; exact one), hu.symm⟩

end ZUnit

theorem coe_mem_zeroSet {ϖ : Ω} (p : Cpt ξ) : p.1 ∈ zeroSet ξ ϖ ↔ ¬ unitAt ξ p ϖ :=
  ⟨fun ⟨_, h⟩ => h, fun h => ⟨p.2, h⟩⟩

theorem TrivMod.of_mul {L : Lat ξ E} {ϖ a : Ω} (hϖ : ∀ p, ϖ ∈ regAt ξ p) (ha : ∀ p, a ∈ regAt ξ p)
    (h : TrivMod L (ϖ * a)) : TrivMod L ϖ := by
  have key : ∀ p, ¬ unitAt ξ p ϖ → ¬ unitAt ξ p (ϖ * a) := fun p hp hu => hp (ZUnit.of_mul (hϖ p) (ha p) hu)
  obtain ⟨t, ht⟩ := h
  refine ⟨t, fun p hp => ?_⟩
  obtain ⟨U, hU, h⟩ := ht p (key p hp)
  refine ⟨U, hU, fun q hq hq' => ?_⟩
  obtain ⟨h0, h1, y, hy, e⟩ := h q hq (key q hq')
  exact ⟨h0, h1, a • y, (L q).smul_mem (⟨a, ha q⟩ : regAt ξ q) hy, by rw [e, mul_smul]⟩

theorem TrivRed.mono {L : Lat ξ E} {ϖ ϖ' : Ω} (h : TrivRed L ϖ) (hs : zeroSet ξ ϖ' ⊆ zeroSet ξ ϖ) :
    TrivRed L ϖ' := by
  have key : ∀ p, ¬ unitAt ξ p ϖ' → ¬ unitAt ξ p ϖ := fun p hp =>
    (coe_mem_zeroSet p).1 (hs ((coe_mem_zeroSet p).2 hp))
  obtain ⟨t, ht⟩ := h
  refine ⟨t, fun p hp => ?_⟩
  obtain ⟨U, hU, H⟩ := ht p (key p hp)
  exact ⟨U, hU, fun q hq hq' => H q hq (key q hq')⟩

section Order

variable {L : Lat ξ E} {σ : E} {ϖ : Ω} {M M' : ℕ} {a a' : ℤ} {p : Cpt ξ}

theorem OrderAt.unitAt (h : OrderAt L σ ϖ M a p) {e : E} {c : Ω} (hL : L p = Submodule.span (regAt ξ p) {e})
    (hσ : σ = c • e) : unitAt ξ p (c ^ M / ϖ ^ a) := by
  obtain ⟨e₀, c₀, he₀, hL₀, hσ₀, h⟩ := h
  obtain ⟨u, hu, e'⟩ := ZUnit.exists_of_span_eq he₀ (hL₀.symm.trans hL)
  have he : e ≠ 0 := by rintro rfl; exact he₀ (by rw [e', smul_zero])
  have hc : c = c₀ * u := by
    apply smul_left_injective Ω he
    simp only [mul_smul, ← e', ← hσ, ← hσ₀]
  have : c ^ M / ϖ ^ a = c₀ ^ M / ϖ ^ a * u ^ M := by rw [hc, mul_pow]; ring
  rw [this]
  exact ZUnit.mul h (ZUnit.pow hu M)

theorem orderAt_iff_of_gen {e : E} {c : Ω} (he : e ≠ 0) (hL : L p = Submodule.span (regAt ξ p) {e})
    (hσ : σ = c • e) : OrderAt L σ ϖ M a p ↔ unitAt ξ p (c ^ M / ϖ ^ a) :=
  ⟨fun h => h.unitAt hL hσ, fun h => ⟨e, c, he, hL, hσ, h⟩⟩

theorem orderAt_iff_div {Λ : Lat ξ Ω} {s e : Ω} (he : e ≠ 0) (hΛ : Λ p = Submodule.span (regAt ξ p) {e}) :
    OrderAt Λ s ϖ M a p ↔ unitAt ξ p ((s / e) ^ M / ϖ ^ a) :=
  orderAt_iff_of_gen he hΛ (by rw [smul_eq_mul, div_mul_cancel₀ _ he])

theorem exists_gen_of_isVB_one {V : Submodule Ω E} (hL : L.IsVB 1 V) (p : Cpt ξ) :
    ∃ e : E, e ≠ 0 ∧ L p = Submodule.span (regAt ξ p) {e} ∧ V = Submodule.span Ω {e} := by
  obtain ⟨U, hU, b, hb, h⟩ := hL p trivial
  obtain ⟨h1, h2⟩ := h p trivial hU
  have hr : Set.range b = {b 0} := by
    ext x
    simp [Fin.exists_fin_one, eq_comm]
  exact ⟨b 0, h1.ne_zero 0, by rw [h2, hr], by rw [← hb, hr]⟩

theorem OrderAt.ne_zero (h : OrderAt L σ ϖ M a p) (hM : M ≠ 0) : σ ≠ 0 := by
  obtain ⟨e, c, he, -, rfl, h⟩ := h
  refine smul_ne_zero ?_ he
  rintro rfl
  exact h.1 (by rw [zero_pow hM, zero_div])

theorem orderAt_one_zero : OrderAt L σ ϖ 1 0 p ↔ σ ≠ 0 ∧ L p = Submodule.span (regAt ξ p) {σ} := by
  refine ⟨fun h => ⟨h.ne_zero one_ne_zero, ?_⟩, fun ⟨h0, h⟩ => ⟨σ, 1, h0, h, (one_smul _ _).symm, by
    simpa using ZUnit.one⟩⟩
  obtain ⟨e, c, -, hL, rfl, h⟩ := h
  rw [pow_one, zpow_zero, div_one] at h
  rw [hL]
  refine le_antisymm ?_ ?_ <;> rw [Submodule.span_singleton_le_iff_mem, Submodule.mem_span_singleton]
  · exact ⟨⟨c⁻¹, h.2.2⟩, by
      change c⁻¹ • c • e = e
      rw [inv_smul_smul₀ h.1]⟩
  · exact ⟨⟨c, h.2.1⟩, rfl⟩

theorem OrderAt.mul_nat (h : OrderAt L σ ϖ M a p) (k : ℕ) : OrderAt L σ ϖ (M * k) (a * k) p := by
  obtain ⟨e, c, he, hL, hσ, h⟩ := h
  refine ⟨e, c, he, hL, hσ, ?_⟩
  rw [pow_mul, zpow_mul, zpow_natCast, ← div_pow]
  exact ZUnit.pow h k

theorem OrderAt.unique (h0 : ϖ ≠ 0) (hϖ : ϖ ∈ regAt ξ p) (hp : ¬ Ar.unitAt ξ p ϖ) (ha : OrderAt L σ ϖ M a p)
    (ha' : OrderAt L σ ϖ M a' p) : a = a' := by
  obtain ⟨e, c, he, hL, hσ, ha⟩ := ha
  replace ha' := ha'.unitAt hL hσ
  have key : ∀ a b : ℤ, Ar.unitAt ξ p (c ^ M / ϖ ^ a) → Ar.unitAt ξ p (c ^ M / ϖ ^ b) → ¬ a < b := by
    intro a b ha hb hlt
    obtain ⟨n, rfl⟩ : ∃ n : ℕ, b = a + ((n + 1 : ℕ) : ℤ) := ⟨(b - a - 1).toNat, by omega⟩
    have hc : c ^ M ≠ 0 := fun h => ha.1 (by rw [h, zero_div])
    have hu := ZUnit.mul ha (ZUnit.inv hb)
    have : c ^ M / ϖ ^ a * (c ^ M / ϖ ^ (a + ((n + 1 : ℕ) : ℤ)))⁻¹ = ϖ ^ (n + 1) := by
      have : ϖ ^ a ≠ 0 := zpow_ne_zero a h0
      rw [zpow_add₀ h0, zpow_natCast]
      field_simp
    rw [this] at hu
    exact hp (ZUnit.of_pow hϖ n.succ_ne_zero hu)
  exact le_antisymm (not_lt.1 (key a' a ha' ha)) (not_lt.1 (key a a' ha ha'))

theorem OrderAt.ratio_unique (h0 : ϖ ≠ 0) (hϖ : ϖ ∈ regAt ξ p) (hp : ¬ Ar.unitAt ξ p ϖ)
    (ha : OrderAt L σ ϖ M a p) (ha' : OrderAt L σ ϖ M' a' p) : a * M' = a' * M :=
  OrderAt.unique h0 hϖ hp (ha.mul_nat M') (by rw [mul_comm M M']; exact ha'.mul_nat M)

end Order

example {e : E} (he : e ≠ 0) {ϖ : Ω} (h0 : ϖ ≠ 0) (n : ℤ) (p : Cpt ξ) :
    OrderAt (fun p => Submodule.span (regAt ξ p) {e} : Lat ξ E) (ϖ ^ n • e) ϖ 1 n p :=
  ⟨e, ϖ ^ n, he, rfl, rfl, by rw [pow_one, div_self (zpow_ne_zero n h0)]; exact ZUnit.one⟩

example {e : E} (he : e ≠ 0) {ϖ : Ω} (h0 : ϖ ≠ 0) (p : Cpt ξ) :
    OrderAt (fun p => Submodule.span (regAt ξ p) {e} : Lat ξ E) (ϖ ^ 3 • e) (ϖ ^ 2) 2 3 p :=
  ⟨e, ϖ ^ 3, he, rfl, rfl, by
    rw [show (ϖ ^ 3) ^ 2 / (ϖ ^ 2) ^ (3 : ℤ) = 1 by rw [zpow_ofNat]; field_simp]; exact ZUnit.one⟩

example (σ : E) (ϖ : Ω) (M : ℕ) (a : ℤ) (p : Cpt ξ) : ¬ OrderAt (fun _ => ⊥ : Lat ξ E) σ ϖ M a p :=
  fun ⟨_, _, he, h, _⟩ => he (Submodule.span_singleton_eq_bot.1 h.symm)

example (ϖ : Ω) (M : ℕ) (a : ℤ) (p : Cpt ξ) :
    ¬ OrderAt (fun p => Submodule.span (regAt ξ p) {((1 : Ω), (0 : Ω))} : Lat ξ (Ω × Ω)) (0, 1) ϖ M a p := by
  rintro ⟨e, c, he, h, hσ, -⟩
  obtain ⟨u, -, rfl⟩ := ZUnit.exists_of_span_eq he h.symm
  simpa using congrArg Prod.snd hσ

example {ϖ : Ω} {p : Cpt ξ} (hp : ¬ unitAt ξ p ϖ) : ¬ TrivRed (fun _ => ⊥ : Lat ξ E) ϖ := by
  rintro ⟨t, ht⟩
  obtain ⟨U, hU, h⟩ := ht p hp
  obtain ⟨h0, h1, -⟩ := h p hU hp
  exact h0 (Submodule.span_singleton_eq_bot.1 h1.symm)

example : zeroSet ξ 1 = ∅ ∧ zeroSet ξ 0 = {q | genPt ξ ⤳ q} :=
  ⟨Set.eq_empty_of_forall_notMem fun _ ⟨_, h⟩ => h ZUnit.one,
    Set.ext fun _ => ⟨fun ⟨h, _⟩ => h, fun h => ⟨h, fun hu => hu.1 rfl⟩⟩⟩

end GlobalTheory.CompanionTheory.Ar.Flat
end
end

-- bundled from Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsPowSubMemSpanOfIsUnitModOfIsAlgClosed
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
  {F : Type} [Field F] [NumberField F]

abbrev evC (z : (Σ k, ι k) → ℂ) (g : MRing ι) : ℂ := eval z (map (Int.castRingHom ℂ) g)

def OverInt (y : (Σ k, ι k) → Ω) (φ : F →+* Ω) : Prop :=
  (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) ∧
    ∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) → ∀ a : 𝓞 F, φ (a : F) ∈ chartRingZ y c

def PtOver (y : (Σ k, ι k) → Ω) (φ : F →+* Ω) (σ : F →+* ℂ) (z : (Σ k, ι k) → ℂ) : Prop :=
  z ∈ mcPts (mCoordIdeal y) ∧ ∀ (a : F) (d : K → ℕ) (g h : MRing ι), IsMultiHomog g d → IsMultiHomog h d →
    aeval y g = φ a * aeval y h → evC z g = σ a * evC z h

def IsUnitSec (P : Ideal (MRing ι)) (f g : MRing ι) : Prop :=
  ∀ W : Ideal (MRing ι), W.IsPrime → P ≤ W → IsRelevant W → ∃ u v : MRing ι, u ∉ W ∧ v ∉ W ∧ u * f - v * g ∈ P

structure IsPlaceWeight (y : (Σ k, ι k) → Ω) (φ : F →+* Ω) (t : (F →+* ℂ) → ℝ) (u : ((Σ k, ι k) → ℂ) → ℝ) : Prop where
  inv : ∀ (c : K → ℂ) z, (∀ k, c k ≠ 0) → u (fun p => c p.1 * z p) = u z
  smooth : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0}
  near : ∀ σ z, PtOver y φ σ z → ∀ᶠ z' in nhds z, u z' = t σ

def IsPlaceWeight.shift {y : (Σ k, ι k) → Ω} {φ : F →+* Ω} {s : (F →+* ℂ) → ℝ} {u : ((Σ k, ι k) → ℂ) → ℝ}
    (hu : IsPlaceWeight y φ s u) (A : HermLine ι) : HermLine ι :=
  A.tensor (HermLine.ofWeight u hu.inv)

def meanEmb (t : (F →+* ℂ) → ℝ) : ℝ := (∑ σ : F →+* ℂ, t σ) / (Module.finrank ℚ F : ℝ)

structure FlatHerm (y : (Σ k, ι k) → Ω) (φ : F →+* Ω) (A : HermLine ι) where
  M : ℕ
  M_pos : 0 < M
  f : MRing ι
  g : MRing ι
  df : K → ℕ
  dg : K → ℕ
  hf : IsMultiHomog f df
  hg : IsMultiHomog g dg
  deg : ∀ k, (df k : ℤ) - dg k = M * A.a k
  f_ne : f ∉ mCoordIdeal y
  g_ne : g ∉ mCoordIdeal y
  unit : IsUnitSec (mCoordIdeal y) f g
  κ : (F →+* ℂ) → ℝ
  κ_pos : ∀ σ, 0 < κ σ
  κ_conj : ∀ σ, κ (ComplexEmbedding.conjugate σ) = κ σ
  norm : ∀ σ z, PtOver y φ σ z → ‖evC z f‖ = (κ σ * A.h z) ^ M * ‖evC z g‖

def FlatHerm.ht {y : (Σ k, ι k) → Ω} {φ : F →+* Ω} {A : HermLine ι} (S : FlatHerm y φ A) : ℝ :=
  -meanEmb fun σ => Real.log (S.κ σ)

end GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat.Inh

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Flat

variable (F : Type) [Field F] [NumberField F]

abbrev Idx : Unit → Type := fun _ => Option (Module.Free.ChooseBasisIndex ℤ (𝓞 F))

def intPt (i : Option (Module.Free.ChooseBasisIndex ℤ (𝓞 F))) : 𝓞 F :=
  i.elim 1 (RingOfIntegers.basis F)

def pt (p : Σ k, Idx F k) : F := (intPt F p.2 : F)

theorem pt_none : pt F ⟨(), none⟩ = 1 := by simp [pt, intPt]

theorem mem_of_inv_mem {S : Subalgebra ℤ F} {x : F} (hx : x ≠ 0) (hi : IsIntegral ℤ x) (h : x⁻¹ ∈ S) :
    x ∈ S := by
  obtain ⟨q, hq, h0⟩ := hi
  rcases Nat.eq_zero_or_pos q.natDegree with hd | hd
  · rw [hq.natDegree_eq_zero.mp hd] at h0; simp at h0
  obtain ⟨m, hm⟩ : ∃ m, q.natDegree = m + 1 := ⟨q.natDegree - 1, by omega⟩
  rw [Polynomial.eval₂_eq_sum_range, hm, Finset.sum_range_succ] at h0
  have hc : q.coeff (m + 1) = 1 := by rw [← hm]; exact hq.coeff_natDegree
  rw [hc, map_one, one_mul] at h0
  have : x = -∑ i ∈ Finset.range (m + 1), algebraMap ℤ F (q.coeff i) * x⁻¹ ^ (m - i) := by
    have hxm : x ^ m ≠ 0 := pow_ne_zero _ hx
    apply mul_left_cancel₀ hxm
    rw [mul_neg, Finset.mul_sum, ← pow_succ, eq_neg_iff_add_eq_zero, add_comm, ← h0]
    congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hi'
    simp only [Nat.add_sub_cancel_left, pow_add, inv_pow]
    field_simp
  rw [this]
  exact neg_mem (Subalgebra.sum_mem _ fun i _ => mul_mem (S.algebraMap_mem _) (pow_mem h _))

theorem overInt_pt : OverInt (pt F) (RingHom.id F) := by
  refine ⟨fun k => ⟨none, by rw [pt_none]; exact one_ne_zero⟩, fun c hc a => ?_⟩
  have hg : ∀ p, pt F p / pt F ⟨(), c ()⟩ ∈ chartRingZ (pt F) c := fun p =>
    Algebra.subset_adjoin ⟨p, rfl⟩
  have h1 : pt F ⟨(), c ()⟩ ∈ chartRingZ (pt F) c := by
    refine mem_of_inv_mem F (hc ()) (intPt F (c ())).isIntegral_coe ?_
    have := hg ⟨(), none⟩
    rwa [pt_none, one_div] at this
  have h2 : ∀ p, pt F p ∈ chartRingZ (pt F) c := fun p => by
    have := mul_mem (hg p) h1
    rwa [div_mul_cancel₀ _ (hc ())] at this
  rw [← (RingOfIntegers.basis F).sum_repr a]
  simp only [RingHom.id_apply, map_sum, map_zsmul, RingOfIntegers.coe_eq_algebraMap]
  exact Subalgebra.sum_mem _ fun i _ => zsmul_mem (h2 ⟨(), some i⟩) _

theorem X_none_notMem (W : Ideal (MRing (Idx F))) (hW : W.IsPrime) (hP : mCoordIdeal (pt F) ≤ W)
    (hr : IsRelevant W) : (X ⟨(), none⟩ : MRing (Idx F)) ∉ W := by
  intro h0
  obtain ⟨j, hj⟩ := hr ()
  obtain ⟨q, hq, hz⟩ := (intPt F j).isIntegral_coe
  have hG : (∑ i ∈ Finset.range (q.natDegree + 1), C (q.coeff i) * X ⟨(), j⟩ ^ i *
      X ⟨(), none⟩ ^ (q.natDegree - i) : MRing (Idx F)) ∈ mCoordIdeal (pt F) := by
    rw [mCoordIdeal, RingHom.mem_ker, map_sum]
    have : ∀ i ∈ Finset.range (q.natDegree + 1), mConeMap (pt F) (C (q.coeff i) * X ⟨(), j⟩ ^ i *
        X ⟨(), none⟩ ^ (q.natDegree - i) : MRing (Idx F)) =
        C (algebraMap ℤ F (q.coeff i) * pt F ⟨(), j⟩ ^ i) * X () ^ q.natDegree := by
      intro i hi
      have hi' : i ≤ q.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      obtain ⟨e, he⟩ := Nat.exists_eq_add_of_le hi'
      simp only [mConeMap, map_mul, map_pow, aeval_X, pt_none, map_one, one_mul, he,
        Nat.add_sub_cancel_left, eq_intCast, map_intCast]
      ring
    rw [Finset.sum_congr rfl this, ← Finset.sum_mul, ← map_sum]
    rw [Polynomial.eval₂_eq_sum_range] at hz
    have hz' : ∑ i ∈ Finset.range (q.natDegree + 1), algebraMap ℤ F (q.coeff i) * pt F ⟨(), j⟩ ^ i = 0 := hz
    rw [hz', map_zero, zero_mul]
  have hG' := hP hG
  rw [Finset.sum_range_succ, hq.coeff_natDegree, Nat.sub_self, pow_zero, map_one, one_mul, mul_one] at hG'
  have hs : (∑ i ∈ Finset.range q.natDegree, C (q.coeff i) * X ⟨(), j⟩ ^ i *
      X ⟨(), none⟩ ^ (q.natDegree - i) : MRing (Idx F)) ∈ W :=
    W.sum_mem fun i hi => W.mul_mem_left _ (W.pow_mem_of_mem h0 _ (by
      have := Finset.mem_range.mp hi; omega))
  exact hj (hW.mem_of_pow_mem _ ((W.add_mem_iff_right hs).mp hG'))

def fs : HermLine (Idx F) where
  a := 1
  h z := √(∑ p, ‖z p‖ ^ 2)
  pos z hz := by
    obtain ⟨i, hi⟩ := hz ()
    exact Real.sqrt_pos.mpr (Finset.sum_pos' (fun _ _ => by positivity)
      ⟨⟨(), i⟩, Finset.mem_univ _, by positivity⟩)
  smul c z _ := by
    simp only [norm_mul, mul_pow, Pi.one_apply, zpow_one, Fintype.prod_unique]
    have : ∑ p : Σ k, Idx F k, ‖c p.1‖ ^ 2 * ‖z p‖ ^ 2 = ‖c default‖ ^ 2 * ∑ p, ‖z p‖ ^ 2 := by
      rw [Finset.mul_sum]
    rw [this, Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg _)]

theorem homog_X (i : Idx F ()) : IsMultiHomog (X ⟨(), i⟩ : MRing (Idx F)) (fun _ => 1) := by
  classical
  intro m hm k
  rw [support_X, Finset.mem_singleton] at hm
  subst hm
  rw [Finset.sum_eq_single i] <;> simp +contextual [Finsupp.single_apply, eq_comm]

theorem sum_pos (σ : F →+* ℂ) : 0 < ∑ p, ‖σ (pt F p)‖ ^ 2 :=
  Finset.sum_pos' (fun _ _ => by positivity) ⟨⟨(), none⟩, Finset.mem_univ _, by simp [pt_none]⟩

def flatFs : FlatHerm (pt F) (RingHom.id F) (fs F) where
  M := 1
  M_pos := one_pos
  f := X ⟨(), none⟩
  g := 1
  df := fun _ => 1
  dg := fun _ => 0
  hf := homog_X F none
  hg := by
    intro m hm k
    rw [← C_1, C_apply] at hm
    have := Finset.mem_singleton.mp (support_monomial_subset hm)
    simp [this]
  deg k := by simp [fs]
  f_ne := by simp [mCoordIdeal, RingHom.mem_ker, mConeMap, pt_none]
  g_ne := by simp [mCoordIdeal, RingHom.mem_ker]
  unit W hW hP hr := ⟨1, X ⟨(), none⟩, (Ideal.ne_top_iff_one W).mp hW.ne_top, X_none_notMem F W hW hP hr, by simp⟩
  κ σ := (√(∑ p, ‖σ (pt F p)‖ ^ 2))⁻¹
  κ_pos σ := inv_pos.mpr (Real.sqrt_pos.mpr (sum_pos F σ))
  κ_conj σ := by simp [ComplexEmbedding.conjugate_coe_eq]
  norm σ z hz := by
    have h : ∀ p, z p = σ (pt F p) * z ⟨(), none⟩ := fun p => by
      have := hz.2 (pt F p) _ _ _ (homog_X F p.2) (homog_X F none) (by simp [pt_none])
      simpa [evC] using this
    have h2 : ∑ p, ‖z p‖ ^ 2 = (∑ p, ‖σ (pt F p)‖ ^ 2) * ‖z ⟨(), none⟩‖ ^ 2 := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun p _ => by rw [h p, norm_mul, mul_pow]
    have h3 := Real.sqrt_pos.mpr (sum_pos F σ)
    simp only [evC, map_X, eval_X, map_one, norm_one, mul_one, pow_one, fs]
    rw [h2, Real.sqrt_mul (sum_pos F σ).le, Real.sqrt_sq (norm_nonneg _)]
    field_simp

theorem ptOver_pt (σ : F →+* ℂ) : PtOver (pt F) (RingHom.id F) σ (fun p => σ (pt F p)) := by
  have e : ∀ g : MRing (Idx F), evC (fun p => σ (pt F p)) g = σ (aeval (pt F) g) := fun g => by
    induction g using MvPolynomial.induction_on with
    | C a => simp [evC]
    | add p q hp hq => simp only [evC, map_add] at *; rw [hp, hq]
    | mul_X p i hp => simp only [evC, map_mul, map_X, eval_X, aeval_X] at *; rw [hp]
  refine ⟨⟨fun k => ⟨none, by cases k; simp [pt_none]⟩, fun f hf => ?_⟩, fun a d g h _ _ H => by
    rw [e, e, H, map_mul]; rfl⟩
  have hf' : mConeMap (pt F) f = 0 := hf
  have e2 : ∀ g : MRing (Idx F), eval (fun _ : Unit => (1 : F)) (mConeMap (pt F) g) = aeval (pt F) g := fun g => by
    induction g using MvPolynomial.induction_on with
    | C a => simp
    | add p q hp hq => simp only [map_add, hp, hq]
    | mul_X p i hp => rw [map_mul, map_mul, hp, map_mul]; simp [mConeMap]
  have := e f
  rw [← e2, hf'] at this
  simpa using this

theorem ht_pos : 0 < (flatFs F).ht := by
  have h : ∀ σ : F →+* ℂ, Real.log ((flatFs F).κ σ) < 0 := fun σ => by
    refine Real.log_neg ((flatFs F).κ_pos σ) (inv_lt_one_of_one_lt₀ ?_)
    rw [Real.lt_sqrt zero_le_one, one_pow]
    obtain ⟨i⟩ := (RingOfIntegers.basis F).index_nonempty
    have hi : pt F ⟨(), some i⟩ ≠ 0 := by
      simpa [pt, intPt] using (RingOfIntegers.basis F).ne_zero i
    have := Finset.single_lt_sum (s := Finset.univ) (f := fun p => ‖σ (pt F p)‖ ^ 2) (i := ⟨(), none⟩)
      (j := ⟨(), some i⟩) (by simp) (Finset.mem_univ _) (Finset.mem_univ _)
      (by have : σ (pt F ⟨(), some i⟩) ≠ 0 := by simpa using hi
          positivity) (fun _ _ _ => by positivity)
    simpa [pt_none] using this
  unfold FlatHerm.ht meanEmb
  rw [neg_pos]
  exact div_neg_of_neg_of_pos (Finset.sum_neg (fun σ _ => h σ) Finset.univ_nonempty)
    (Nat.cast_pos.mpr Module.finrank_pos)

theorem isPlaceWeight_const (c : ℝ) : IsPlaceWeight (pt F) (RingHom.id F) (fun _ => c) (fun _ => c) :=
  ⟨fun _ _ _ => rfl, contDiffOn_const, fun _ _ _ => Filter.Eventually.of_forall fun _ => rfl⟩

example (c : ℝ) : meanEmb (fun _ : F →+* ℂ => c) = c := by
  have : (Module.finrank ℚ F : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
  simp only [meanEmb, Finset.sum_const, Finset.card_univ, Embeddings.card, nsmul_eq_mul]
  field_simp

end GlobalTheory.CompanionTheory.Ar.Flat.Inh
end
end

