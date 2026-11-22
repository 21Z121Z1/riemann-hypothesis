import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.HStable
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0004
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.InstFintypeSumElim

-- bundled from Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.CoeffSyGauge
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Conj

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing

variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
variable (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k]

theorem coeff_sy_gauge (B : FB R d O) (h : PS k 2 d) (hc : B.IsCanonGauge k h) (i j : Fin d) :
    algebraMap R k (coeff (Finsupp.single ((0 : Fin 2), i) 1 + Finsupp.single ((1 : Fin 2), j) 1) B.sy) = sg1 k h j i - sg1 k h i j := by
  have e₁ := congrArg (coeff (Finsupp.single ((0 : Fin 2), i) 1 + Finsupp.single ((1 : Fin 2), j) 1)) hc.sy
  rw [coeff_expS_two _ (coeff_swap_sub_low h hc.ax0 hc.ax1) _ (by simp)] at e₁
  rw [map_sub, coeff_ev_swap', Finsupp.embDomain_add, Finsupp.embDomain_single, Finsupp.embDomain_single] at e₁
  have s₁ : (swE d) ((0 : Fin 2), i) = ((1 : Fin 2), i) := rfl
  have s₂ : (swE d) ((1 : Fin 2), j) = ((0 : Fin 2), j) := rfl
  rw [s₁, s₂, add_comm (Finsupp.single ((1 : Fin 2), i) 1)] at e₁
  rw [gaugeBilinearTerm_eq_neg_double_sum, gaugeBilinearTerm_eq_neg_double_sum, ← coeff_map, e₁]
  ring

theorem coeff_ad_gauge (B : FB R d O) (h : PS k 2 d) (hc : B.IsCanonGauge k h) (a : O) (i j : Fin d) :
    algebraMap R k (coeff (Finsupp.single ((0 : Fin 2), j) 1 + Finsupp.single ((1 : Fin 2), i) 1) (B.ad a)) =
      ((dAct k B (star a)).transpose * sg1 k h - sg1 k h * dAct k B a) i j := by
  have k0 : ∀ i', constantCoeff (comp1 (B.actK k a) (pt k d 0 : Pt k 2 d) i') = 0 := fun i' => by
    have : comp1 (B.actK k a) (pt k d 0 : Pt k 2 d) i' = rename (eXv d) (B.actK k a i') := eval_first_point_rename _
    rw [this, constantCoeff_rename, const_actK]
  have k1 : ∀ i', constantCoeff (comp1 (B.actK k (star a)) (pt k d 1 : Pt k 2 d) i') = 0 := fun i' => by
    have : comp1 (B.actK k (star a)) (pt k d 1 : Pt k 2 d) i' = rename (eZ d) (B.actK k (star a) i') :=
      eval_second_point_rename _
    rw [this, constantCoeff_rename, const_actK]
  have kX : ∀ (j' : Fin 2) (i' : Fin d), constantCoeff (pt k d j' i' : PS k 2 d) = 0 :=
    fun j' i' => constantCoeff_X _
  have c1 : ∀ j' i',
      constantCoeff ((![comp1 (B.actK k a) (pt k d 0), pt k d 1] : Fin 2 → Pt k 2 d) j' i') = 0 := by
    intro j' i'
    fin_cases j'
    exacts [k0 i', kX 1 i']
  have c2 : ∀ j' i',
      constantCoeff ((![pt k d 0, comp1 (B.actK k (star a)) (pt k d 1)] : Fin 2 → Pt k 2 d) j' i') = 0 := by
    intro j' i'
    fin_cases j'
    exacts [kX 0 i', k1 i']
  have hord : ∀ e : Fin 2 × Fin d →₀ ℕ, e.degree < 2 →
      coeff e (ev (n := 2) ![comp1 (B.actK k a) (pt k d 0), pt k d 1] h -
        ev (n := 2) ![pt k d 0, comp1 (B.actK k (star a)) (pt k d 1)] h) = 0 := fun e he => by
    rw [map_sub, coeff_ev_low B h hc _ c1 e he, coeff_ev_low B h hc _ c2 e he, sub_zero]
  have e := congrArg (coeff (Finsupp.single ((0 : Fin 2), j) 1 + Finsupp.single ((1 : Fin 2), i) 1)) (hc.ad a)
  rw [coeff_expS_two _ hord _ (degree_xz j i), map_sub, coeff_ad_side1 B h hc a i j, coeff_ad_side2 B h hc a i j,
    coeff_map] at e
  rw [e]
  simp only [Matrix.sub_apply, Matrix.mul_apply, Matrix.transpose_apply, gaugeBilinearTerm_eq_neg_double_sum, neg_mul, mul_neg,
    Finset.sum_neg_distrib, mul_comm (dAct k B (star a) _ i)]
  ring

end GlobalTheory.CompanionTheory.Ar.Conj
end
end

-- bundled from Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsCompactUnitaryPointsAtPlaceFstMemCompact
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HT

open Module NumberField

structure HTChart (A K : Type) [CommRing A] [Field K] [Algebra A K] {E : Type} [Field E] [NumberField E]
    (c : E ≃+* E) (p R N : ℕ)
    (Ω : Type) [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω] where

  om : Submodule A Ω
  om_lat : om.IsLattice K
  om_proj : Module.Projective A om

  ρΩ : 𝓞 E →+* Module.End K Ω
  om_stable : ∀ (a : 𝓞 E), ∀ x ∈ om, ρΩ a x ∈ om

  e : (Fin N → 𝓞 E) →+ (Fin N → 𝓞 E) →+ ZMod (p ^ R)
  alt : ∀ x, e x x = 0
  adj : ∀ (a : 𝓞 E) (x y : Fin N → 𝓞 E), e (a • x) y = e x (RingOfIntegers.mapRingEquiv c a • y)
  e_surj : ∀ φ : (Fin N → 𝓞 E) →+ ZMod (p ^ R), ∃ x, e x = φ
  e_inj : ∀ x, e x = 0 → ∃ x', x = (p ^ R) • x'

  h : (Fin N → 𝓞 E) →+ Ω
  h_mem : ∀ x, h x ∈ om
  h_lin : ∀ (a : 𝓞 E) (x : Fin N → 𝓞 E), ∃ y ∈ om, h (a • x) = ρΩ a (h x) + (p ^ R) • y

namespace HTChart

variable {A K : Type} [CommRing A] [Field K] [Algebra A K] {E : Type} [Field E] [NumberField E]
  {c : E ≃+* E} {p R N : ℕ}
  {Ω : Type} [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω]
  (D : HTChart A K c p R N Ω)

def om' : Submodule A Ω :=
  Submodule.span A (Set.range D.h) ⊔ D.om.map (((p : A) ^ R) • LinearMap.id)

def omHT (σ : E →+* K) : Submodule A Ω := eigQuot D.ρΩ σ D.om'

def q (σ : E →+* K) (x : Fin N → A) : Ω := ∑ i, x i • eigProj D.ρΩ σ (D.h (Pi.single i 1))

def gram (σ : E →+* K) (d : A) (i j : Fin N) : K :=
  ∑ k, algebraMap A K d * σ (dualInt E k) *
    ((D.e (Pi.single i (RingOfIntegers.basis E k)) (Pi.single j 1)).val : K)

def IsDualMap (σ : E →+* K) (d : A) (m : ℕ)
    (i : Module.Dual A (D.omHT (σ.comp c.toRingHom)) →ₗ[A] (Fin N → A)) : Prop :=
  ∀ (w : Module.Dual A (D.omHT (σ.comp c.toRingHom))) (j : Fin N)
    (y : D.omHT (σ.comp c.toRingHom)),
    (y : Ω) = eigProj D.ρΩ (σ.comp c.toRingHom) (D.h (Pi.single j 1)) →
      ∃ z : A, ∑ l, algebraMap A K (i w l) * D.gram σ d l j = algebraMap A K (w y + (p : A) ^ m * z)

def ExactMod (σ : E →+* K) (m : ℕ)
    (i : Module.Dual A (D.omHT (σ.comp c.toRingHom)) →ₗ[A] (Fin N → A)) : Prop :=
  (∃ r : (Fin N → A) →ₗ[A] Module.Dual A (D.omHT (σ.comp c.toRingHom)),
    ∀ w, ∃ w', r (i w) = w + ((p : A) ^ m) • w') ∧
  (∀ x : Fin N → A, (∃ y ∈ D.omHT σ, D.q σ x = ((p : A) ^ m) • y) ↔
    ∃ w, ∃ x' : Fin N → A, x = i w + ((p : A) ^ m) • x') ∧
  ∀ y ∈ D.omHT σ, ∃ x : Fin N → A, ∃ y' ∈ D.omHT σ, y = D.q σ x + ((p : A) ^ m) • y'

structure ReducesTo {C O : Type} [Field C] [CommRing O] [Algebra O C] {κ : O}
    {V Ω' : Type} [AddCommGroup V] [Module C V] [Module O V] [IsScalarTower O C V]
    [AddCommGroup Ω'] [Module C Ω'] [Module O Ω'] [IsScalarTower O C Ω']
    (φ : A →+* O) (P : HTPoint C O c κ N V Ω') (ι : D.om →ₛₗ[φ] Ω') : Prop where
  span_eq : Submodule.span O (Set.range ι) = P.om
  rank_eq : Module.finrank K Ω = Module.finrank C Ω'
  lin : ∀ (a : 𝓞 E) (x : D.om), ι ⟨D.ρΩ a x, D.om_stable a x x.2⟩ = P.ρΩ a (ι x)
  ht_eq : ∀ x, ∃ y ∈ P.om, ι ⟨D.h x, D.h_mem x⟩ = P.ht (P.tate x) + (p ^ R) • y
  e_eq : ∀ x y, ∃ z : O, P.e (P.tate x) (P.tate y) =
    algebraMap O C (((D.e x y).val : O) + (p : O) ^ R * z)

def HasTestPoints (κ : A) : Prop :=
  ∀ 𝔮 : Ideal A, 𝔮.IsPrime → 𝔮.height = 1 → (p : A) ∈ 𝔮 →
    ∃ (C O : Type) (_ : Field C) (_ : IsAlgClosed C) (_ : CharZero C) (_ : CommRing O) (_ : Algebra O C)
      (v : Valuation C NNReal) (φ : A →+* O)
      (V Ω' : Type) (_ : AddCommGroup V) (_ : Module C V) (_ : Module O V) (_ : IsScalarTower O C V)
      (_ : AddCommGroup Ω') (_ : Module C Ω') (_ : Module O Ω') (_ : IsScalarTower O C Ω')
      (P : HTPoint C O c (φ κ) N V Ω') (ι : D.om →ₛₗ[φ] Ω'),
      v.Integers O ∧ Function.Injective φ ∧ (∀ a, a ∈ 𝔮 ↔ v (algebraMap O C (φ a)) < 1) ∧
        D.ReducesTo φ P ι

end HTChart

def GeneratesDiff {A K : Type} [CommRing A] [Field K] [Algebra A K] {E : Type} [Field E]
    [NumberField E] (σ : E →+* K) (d : A) : Prop :=
  Submodule.span A {algebraMap A K d} =
    Submodule.span A {y : K | ∃ x ∈ differentIdeal ℤ (𝓞 E), y = σ (x : E)}

end GlobalTheory.CompanionTheory.Ar.HT
end
end

-- bundled from Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TrivFlagMod
section
namespace GlobalTheory.CompanionTheory.Ar.Num

open ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles

variable (o : Type*) [CommRing o] {Ω : Type*} [Field Ω] [Algebra o Ω]
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {V V₁ V₂ : Type*} [AddCommGroup V] [Module Ω V] [AddCommGroup V₁] [Module Ω V₁]
  [AddCommGroup V₂] [Module Ω V₂]

def IsLatFamily (x : (Σ k, ι k) → Ω) (Γ : (∀ k, ι k) → AddSubgroup V) : Prop :=
  (∀ s, mseg x s ≠ 0 → ∀ a ∈ chartRing o (mseg x) s, ∀ v ∈ Γ s, a • v ∈ Γ s) ∧
  ∀ s t, mseg x s ≠ 0 → mseg x t ≠ 0 → ∀ v ∈ Γ s, ∃ m : ℕ, (mseg x s / mseg x t) ^ m • v ∈ Γ t

def IsQuotHom (x : (Σ k, ι k) → Ω) (A A' : (∀ k, ι k) → AddSubgroup V)
    (B B' : (∀ k, ι k) → AddSubgroup V₁) (Γ : (∀ k, ι k) → AddSubgroup (V × V₁)) : Prop :=
  IsLatFamily o x Γ ∧ ∀ s, mseg x s ≠ 0 →
    (∀ v w, (v, w) ∈ Γ s → v ∈ A s ∧ w ∈ B s) ∧ (∀ v ∈ A s, ∃ w, (v, w) ∈ Γ s) ∧
    (∀ w, (0, w) ∈ Γ s ↔ w ∈ B' s) ∧ (∀ v ∈ A' s, (v, 0) ∈ Γ s)

def QuotEquiv (x : (Σ k, ι k) → Ω) (A A' : (∀ k, ι k) → AddSubgroup V)
    (B B' : (∀ k, ι k) → AddSubgroup V₁) : Prop :=
  ∃ Γ, IsQuotHom o x A A' B B' Γ ∧ ∀ s, mseg x s ≠ 0 →
    (∀ v, (v, 0) ∈ Γ s → v ∈ A' s) ∧ (∀ w ∈ B s, ∃ v, (v, w) ∈ Γ s)

def QuotExact (x : (Σ k, ι k) → Ω) (A A' : (∀ k, ι k) → AddSubgroup V)
    (B B' : (∀ k, ι k) → AddSubgroup V₁) (C C' : (∀ k, ι k) → AddSubgroup V₂) : Prop :=
  ∃ Γ Δ, IsQuotHom o x A A' B B' Γ ∧ IsQuotHom o x B B' C C' Δ ∧ ∀ s, mseg x s ≠ 0 →
    (∀ v, (v, 0) ∈ Γ s → v ∈ A' s) ∧ (∀ c ∈ C s, ∃ b, (b, c) ∈ Δ s) ∧
    (∀ b, (b, 0) ∈ Δ s ↔ ∃ a, (a, b) ∈ Γ s)

def IsScaled (x : (Σ k, ι k) → Ω) (c : Ω) (A A' : (∀ k, ι k) → AddSubgroup V) : Prop :=
  ∀ s, mseg x s ≠ 0 → ∀ v, v ∈ A' s ↔ ∃ e ∈ A s, v = c • e

def IsLine (x : (Σ k, ι k) → Ω) (u : Ω) (a : K → ℤ) (A : (∀ k, ι k) → AddSubgroup Ω) : Prop :=
  ∀ s, mseg x s ≠ 0 → ∀ v, v ∈ A s ↔ ∃ r ∈ chartRing o (mseg x) s, v = r * (u * chartMon x s a)

def IsDualLat (x : (Σ k, ι k) → Ω) (β : V →ₗ[Ω] V₁ →ₗ[Ω] Ω) (A : (∀ k, ι k) → AddSubgroup V)
    (B : (∀ k, ι k) → AddSubgroup V₁) : Prop :=
  Function.Bijective β.flip ∧
    ∀ s, mseg x s ≠ 0 → ∀ w, w ∈ B s ↔ ∀ v ∈ A s, β v w ∈ chartRing o (mseg x) s

def TrivFlagMod (ϖ : o) (x : (Σ k, ι k) → Ω) (N : ℕ) (b : Fin N → K → ℤ) : Prop :=
  ∃ g : (∀ k, ι k) → Matrix (Fin N) (Fin N) Ω,
    (∀ s, mseg x s ≠ 0 → (∀ i j, g s i j ∈ chartRing o (mseg x) s) ∧
      ∃ h ∈ chartRing o (mseg x) s, ∃ r ∈ chartRing o (mseg x) s,
        (g s).det * h = 1 + algebraMap o Ω ϖ * r) ∧
    ∀ s t, mseg x s ≠ 0 → mseg x t ≠ 0 → ∃ (m : ℕ) (U Z : Matrix (Fin N) (Fin N) Ω),
      (∀ i j, U i j ∈ chartRing o (mseg x) t) ∧ (∀ i j, Z i j ∈ chartRing o (mseg x) t) ∧
      (∀ i j, j < i → U i j = 0) ∧
      (∀ i, U i i = (mseg x s / mseg x t) ^ m * (chartMon x s (b i) / chartMon x t (b i))) ∧
      (∀ i j, (mseg x s / mseg x t) ^ m * g s i j ∈ chartRing o (mseg x) t) ∧
      (mseg x s / mseg x t) ^ m • g s = g t * U + algebraMap o Ω ϖ • Z

end GlobalTheory.CompanionTheory.Ar.Num
end

