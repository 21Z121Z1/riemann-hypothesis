import Mathlib

-- bundled from Formalism.PeriodIntegrals.TransferenceCoverRad
section
open scoped InnerProductSpace

noncomputable section

namespace PI

def TransferenceCoverDiv : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (M : Submodule ℤ V), DiscreteTopology M → Submodule.span ℝ (M : Set V) = ⊤ →
    ∀ κ : ℝ, 0 < κ → (∀ y : V, (∀ x ∈ M, ∃ z : ℤ, inner ℝ x y = (z : ℝ)) → y ≠ 0 → κ ≤ ‖y‖) →
    ∀ x : V, ∃ y ∈ M, ‖x - y‖ ≤ (Module.finrank ℝ V : ℝ) / (2 * κ)

def covRad {N : ℕ} (L : Set (EuclideanSpace ℝ (Fin N))) : ℝ := ⨆ x, Metric.infDist x L

def dualLat {N : ℕ} (L : Submodule ℤ (EuclideanSpace ℝ (Fin N))) : Set (EuclideanSpace ℝ (Fin N)) :=
  {y | ∀ x ∈ L, ∃ z : ℤ, inner ℝ x y = (z : ℝ)}

def firstMin {N : ℕ} (S : Set (EuclideanSpace ℝ (Fin N))) : ℝ :=
  sInf {r | ∃ y ∈ S, y ≠ 0 ∧ r = ‖y‖}

def TransferenceCoverRad : Prop :=
  ∀ (N : ℕ) (L : Submodule ℤ (EuclideanSpace ℝ (Fin N))) [DiscreteTopology L], IsZLattice ℝ L →
    covRad (L : Set (EuclideanSpace ℝ (Fin N))) * firstMin (dualLat L) ≤ (N : ℝ) / 2

end PI
end
end

-- bundled from Formalism.PeriodIntegrals.TwChrOne
section
open NumberField IsDedekindDomain Module

noncomputable section

namespace PI.TwChrOne

section LocS

variable {R : Type*} [CommRing R]

def locS {W : Type*} [AddCommGroup W] [Module R W] (S : Submonoid R) (L : Submodule R W) :
    Submodule R W where
  carrier := {x | ∃ s ∈ S, s • x ∈ L}
  zero_mem' := ⟨1, S.one_mem, by simp⟩
  add_mem' := by
    rintro x y ⟨s, hs, hx⟩ ⟨t, ht, hy⟩
    refine ⟨s * t, S.mul_mem hs ht, ?_⟩
    have e : (s * t) • (x + y) = t • (s • x) + s • (t • y) := by
      rw [smul_add, mul_smul, smul_comm s t x, mul_smul]
    rw [e]
    exact L.add_mem (L.smul_mem t hx) (L.smul_mem s hy)
  smul_mem' := by
    rintro r x ⟨s, hs, hx⟩
    refine ⟨s, hs, ?_⟩
    rw [smul_comm]
    exact L.smul_mem r hx

def localization₂ {W : Type*} [AddCommGroup W] [Module R W] (p : Ideal R) [p.IsPrime] (L : Submodule R W) :
    Submodule R W :=
  locS p.primeCompl L

end LocS

abbrev Sp (E : Type) (n : ℕ) : Type := Fin n → E

section Red

variable {E : Type} [Field E] [NumberField E]

def redP (P : HeightOneSpectrum (𝓞 E)) (a : E) : 𝓞 E ⧸ P.asIdeal :=
  open Classical in
  if h : ∃ c : 𝓞 E ⧸ P.asIdeal, ∃ r s : 𝓞 E, s ∉ P.asIdeal ∧ algebraMap (𝓞 E) E s * a = algebraMap (𝓞 E) E r ∧
      Ideal.Quotient.mk P.asIdeal s * c = Ideal.Quotient.mk P.asIdeal r
  then h.choose else 0

def IntAt (P : HeightOneSpectrum (𝓞 E)) (a : E) : Prop :=
  ∃ r s : 𝓞 E, s ∉ P.asIdeal ∧ algebraMap (𝓞 E) E s * a = algebraMap (𝓞 E) E r

end Red

section Deco

variable (E : Type) [Field E] [NumberField E] [StarRing E] (n : ℕ)

def stdLat : Submodule (𝓞 E) (Sp E n) := Submodule.pi Set.univ fun _ => (1 : Submodule (𝓞 E) E)

end Deco

section Frames

variable (E : Type) [Field E] [NumberField E] [StarRing E] (n : ℕ)

def stabL (M : Submodule (𝓞 E) (Sp E n)) : Subgroup (Sp E n ≃ₗ[E] Sp E n) where
  carrier := {c | ∀ x, c x ∈ M ↔ x ∈ M}
  one_mem' := fun _ => Iff.rfl
  mul_mem' := fun {a b} ha hb x => (ha (b x)).trans (hb x)
  inv_mem' := fun {a} ha x => by
    have h := ha (a⁻¹ x)
    rw [show a (a⁻¹ x) = x from LinearEquiv.apply_symm_apply a x] at h
    exact h.symm

def stdAt (P : HeightOneSpectrum (𝓞 E)) : Submodule (𝓞 E) (Sp E n) := localization₂ P.asIdeal (stdLat E n)

def GLint (P : HeightOneSpectrum (𝓞 E)) : Subgroup (Sp E n ≃ₗ[E] Sp E n) := stabL E n (stdAt E n P)

end Frames

namespace Loc

section Groups

variable (k : Type) [CommRing k] (n c : ℕ)

def atN {k : Type} [CommRing k] {N : ℕ} (v : Fin N → k) (i : ℕ) : k := if h : i < N then v ⟨i, h⟩ else 0

def eN (N i : ℕ) : Fin N → k := fun l => if l.1 = i then 1 else 0

def supp (N : ℕ) (s : Set ℕ) : Submodule k (Fin N → k) where
  carrier := {v | ∀ l : Fin N, l.1 ∉ s → v l = 0}
  add_mem' := fun {a b} ha hb l hl => by simp [ha l hl, hb l hl]
  zero_mem' := fun _ _ => rfl
  smul_mem' := fun r a ha l hl => by simp [ha l hl]

def Ufl (i : ℕ) : Submodule k (Fin (n + c) → k) := supp k (n + c) {l | l < n + i}

def inX : (Fin n → k) →ₗ[k] (Fin (n + c) → k) :=
  LinearMap.pi fun l => if h : l.1 < n then LinearMap.proj ⟨l.1, h⟩ else 0

def R1cond (r : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)) : Prop :=
  (∀ i, ∀ v ∈ Ufl k n c i, r v ∈ Ufl k n c i) ∧ r (eN k (n + c) n) = eN k (n + c) n ∧
    ∀ i, r (eN k (n + c) (n + i)) - eN k (n + c) (n + i) ∈ Ufl k n c i

variable {k n c} in
theorem R1cond.mul {r s : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)} (hr : R1cond k n c r) (hs : R1cond k n c s) :
    R1cond k n c (r * s) := by
  refine ⟨fun i v hv => hr.1 i _ (hs.1 i v hv), ?_, fun i => ?_⟩
  · show r (s _) = _
    rw [hs.2.1, hr.2.1]
  · have h1 : (r * s) (eN k (n + c) (n + i)) - eN k (n + c) (n + i) =
        r (s (eN k (n + c) (n + i)) - eN k (n + c) (n + i)) + (r (eN k (n + c) (n + i)) - eN k (n + c) (n + i)) := by
      rw [map_sub]
      show r (s _) - _ = _
      abel
    rw [h1]
    exact add_mem (hr.1 i _ (hs.2.2 i)) (hr.2.2 i)

theorem R1cond_one : R1cond k n c 1 :=
  ⟨fun _ _ hv => hv, rfl, fun i => by
    show eN k (n + c) (n + i) - eN k (n + c) (n + i) ∈ _
    rw [sub_self]
    exact zero_mem _⟩

def R1 : Subgroup ((Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)) where
  carrier := {r | R1cond k n c r ∧ R1cond k n c r⁻¹}
  one_mem' := ⟨R1cond_one k n c, by rw [inv_one]; exact R1cond_one k n c⟩
  mul_mem' := fun {a b} ha hb => ⟨ha.1.mul hb.1, by rw [mul_inv_rev]; exact hb.2.mul ha.2⟩
  inv_mem' := fun {a} ha => ⟨ha.2, by rw [inv_inv]; exact ha.1⟩

def fixX : Subgroup ((Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)) where
  carrier := {r | ∀ x, r (inX k n c x) = inX k n c x}
  one_mem' := fun _ => rfl
  mul_mem' := fun {a b} ha hb x => by
    show a (b _) = _
    rw [hb, ha]
  inv_mem' := fun {a} ha x => by
    have h := ha x
    show a.symm _ = _
    rw [LinearEquiv.symm_apply_eq, h]

def N1 : Subgroup ((Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)) := R1 k n c ⊓ fixX k n c

variable {k n c}

def n1Arg (r : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)) : k :=
  ∑ i ∈ Finset.range (c - 1), atN (r (eN k (n + c) (n + i + 1))) (n + i)

def Cbe (J : Subgroup ((Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k))) (h : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)) :
    Subgroup ((Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)) :=
  R1 k n c ⊓ J.comap (MulAut.conj h⁻¹).toMonoidHom

def prX (C : Subgroup ((Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k))) : Subgroup ((Fin n → k) ≃ₗ[k] (Fin n → k)) where
  carrier := {g | ∃ r ∈ C, ∀ x, r (inX k n c x) = inX k n c (g x)}
  one_mem' := ⟨1, C.one_mem, fun _ => rfl⟩
  mul_mem' := by
    rintro a b ⟨r, hr, h1⟩ ⟨s, hs, h2⟩
    refine ⟨r * s, C.mul_mem hr hs, fun x => ?_⟩
    show r (s _) = _
    rw [h2, h1]
    rfl
  inv_mem' := by
    rintro a ⟨r, hr, h1⟩
    refine ⟨r⁻¹, C.inv_mem hr, fun x => ?_⟩
    show r.symm _ = _
    rw [LinearEquiv.symm_apply_eq, h1]
    show _ = inX k n c (a (a.symm x))
    rw [LinearEquiv.apply_symm_apply]

def volN (K : Type) [Field K] (C N1O : Subgroup ((Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k))) : K :=
  ((N1O.relIndex (C ⊓ N1 k n c) : ℕ) : K) / (((C ⊓ N1 k n c).relIndex N1O : ℕ) : K)

end Groups

end Loc

abbrev HomE (E : Type) [Field E] (a b : ℕ) : Type := Sp E a →ₗ[E] Sp E b

namespace LocE

open Loc

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] (P : HeightOneSpectrum (𝓞 E)) (q : ℕ)

def vP (a : E) : ℤ := Classical.epsilon fun z : ℤ => IsUnit (redP P (a / (q : E) ^ z))

variable {P} in
open Classical in

def unitV (χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (a : E) : K := if h : IsUnit (redP P a) then ((χ h.unit : Kˣ) : K) else 0

variable {P} in

def locChar (cq : K) (χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (a : E) : K := cq ^ vP P q a * unitV χ (a / (q : E) ^ vP P q a)

def sclLat (N : ℕ) (e : ℕ → ℤ) : Submodule (𝓞 E) (Sp E N) :=
  (stdAt E N P).comap
    ((LinearMap.pi fun l : Fin N => ((q : E) ^ e l.1)⁻¹ • (LinearMap.proj l : Sp E N →ₗ[E] E)).restrictScalars (𝓞 E))

def fIdx (k₀ c n s : ℕ) : ℕ := if s < k₀ then s else if s < k₀ + c then n + (s - k₀) else s - c

def fPos (k₀ c n l : ℕ) : ℕ := if l < k₀ then l else if l < n then l + c else k₀ + (l - n)

def scE (n : ℕ) (ex : ℕ → ℕ) (l : ℕ) : ℤ := if l < n then 0 else (ex (l - n) : ℤ)

def lamY (n c : ℕ) (ex : ℕ → ℕ) : Submodule (𝓞 E) (Sp E (n + c)) := sclLat P q (n + c) (scE n ex)

section AtQ

variable (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ)

def parL (kj n c : ℕ) : Submodule (𝓞 E) (Sp E (n + c)) := sclLat P q (n + c) fun l => if kj ≤ l ∧ l < n then 1 else 0

def JQ (kj n c : ℕ) : Subgroup (Sp E (n + c) ≃ₗ[E] Sp E (n + c)) :=
  stabL E (n + c) (stdAt E (n + c) P) ⊓ stabL E (n + c) (parL P q kj n c)

variable {P}

def lamQB (kj n : ℕ) {N : ℕ} (h : HomE E N N) : K :=
  (unitV ξ (Matrix.det (Matrix.of fun s t : Fin (n - kj) => atN (h (eN E N (kj + t.1))) (kj + s.1))))⁻¹

end AtQ

end LocE

section Target

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K]

def ChiL (P : HeightOneSpectrum (𝓞 E)) (psi : E → K) (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (kj N c : ℕ)
    (h r : Sp E (N + c) ≃ₗ[E] Sp E (N + c)) : K :=
  (psi (Loc.n1Arg r))⁻¹ * LocE.lamQB ξ kj N ((h⁻¹ * r * h : Sp E (N + c) ≃ₗ[E] Sp E (N + c))).toLinearMap

def ChrOkL (P : HeightOneSpectrum (𝓞 E)) (psi : E → K) (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (kj N c : ℕ)
    (h : Sp E (N + c) ≃ₗ[E] Sp E (N + c)) : Prop :=
  (∀ r ∈ Loc.Cbe (LocE.JQ P (Ideal.absNorm P.asIdeal) kj N c) h, ChiL P psi ξ kj N c h r ≠ 0) ∧
  ∀ r ∈ Loc.Cbe (LocE.JQ P (Ideal.absNorm P.asIdeal) kj N c) h, ∀ r' ∈ Loc.Cbe (LocE.JQ P (Ideal.absNorm P.asIdeal) kj N c) h,
    ∀ r'' ∈ Loc.Cbe (LocE.JQ P (Ideal.absNorm P.asIdeal) kj N c) h,
    (∀ x, r'' (Loc.inX E N c x) = r (r' (Loc.inX E N c x))) →
      ChiL P psi ξ kj N c h r'' = ChiL P psi ξ kj N c h r * ChiL P psi ξ kj N c h r'

end Target

def TwChrOne : Prop :=
  ∀ (E K : Type) [Field E] [NumberField E] [StarRing E] [Field K] (P : HeightOneSpectrum (𝓞 E)) (psi : E → K)
    (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (kj N c : ℕ), (∀ x, IntAt P x → psi x = 1) → ChrOkL P psi ξ kj N c 1

end PI.TwChrOne
end
end

-- bundled from Formalism.PeriodIntegrals.UMultOne
section
noncomputable section

namespace PI.UMultOne

open MeasureTheory Matrix ComplexConjugate Finset

def MultOne : Prop :=
  ∀ (n N M : ℕ) (ι : Matrix.unitaryGroup (Fin n) ℂ →* Matrix.unitaryGroup (Fin (n + 1)) ℂ),
    (∀ g, ((ι g : Matrix.unitaryGroup (Fin (n + 1)) ℂ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) =
      Matrix.reindex finSumFinEquiv finSumFinEquiv
        (Matrix.fromBlocks (g : Matrix (Fin n) (Fin n) ℂ) 0 0 (1 : Matrix (Fin 1) (Fin 1) ℂ))) →
    ∀ (ρ : Matrix.unitaryGroup (Fin (n + 1)) ℂ →* GL (Fin N) ℂ)
      (σ : Matrix.unitaryGroup (Fin n) ℂ →* GL (Fin M) ℂ),
    Continuous (fun g => ((ρ g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ)) →
    Continuous (fun g => ((σ g : GL (Fin M) ℂ) : Matrix (Fin M) (Fin M) ℂ)) →
    0 < N → 0 < M →
    (∀ S : Submodule ℂ (Fin N → ℂ),
      (∀ g, ∀ v ∈ S, ((ρ g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ).mulVec v ∈ S) →
      S = ⊥ ∨ S = ⊤) →
    (∀ S : Submodule ℂ (Fin M → ℂ),
      (∀ g, ∀ v ∈ S, ((σ g : GL (Fin M) ℂ) : Matrix (Fin M) (Fin M) ℂ).mulVec v ∈ S) →
      S = ⊥ ∨ S = ⊤) →
    ∀ Hm : Submodule ℂ (Matrix (Fin N) (Fin M) ℂ),
      (∀ T, T ∈ Hm ↔ ∀ g, ((ρ (ι g) : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) * T =
        T * ((σ g : GL (Fin M) ℂ) : Matrix (Fin M) (Fin M) ℂ)) →
      Module.finrank ℂ Hm ≤ 1

def blk (n : ℕ) (h : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv
    (Matrix.fromBlocks h 0 0 (1 : Matrix (Fin 1) (Fin 1) ℂ))

def ConjTranspose : Prop :=
  ∀ (n : ℕ) (g : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ), g ∈ Matrix.unitaryGroup (Fin (n + 1)) ℂ →
    ∃ h ∈ Matrix.unitaryGroup (Fin n) ℂ, blk n h * g * (blk n h)ᴴ = gᵀ

def Irr {G : Type} [Group G] {N : ℕ} (ρ : G →* GL (Fin N) ℂ) : Prop :=
  ∀ S : Submodule ℂ (Fin N → ℂ),
    (∀ g, ∀ v ∈ S, ((ρ g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ).mulVec v ∈ S) → S = ⊥ ∨ S = ⊤

def Cont {G : Type} [Group G] [TopologicalSpace G] {N : ℕ} (ρ : G →* GL (Fin N) ℂ) : Prop :=
  Continuous (fun g => ((ρ g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ))

def GelfandCompact : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [SecondCountableTopology G] (H : Subgroup G) (τ : G → G), IsClosed (H : Set G) → Continuous τ →
    (∀ x y, τ (x * y) = τ y * τ x) → (∀ x, τ (τ x) = x) → (∀ g, ∃ h ∈ H, τ g = h * g * h⁻¹) →
    ∀ (N : ℕ) (ρ : G →* GL (Fin N) ℂ), Cont ρ → Irr ρ →
    ∀ A B : Matrix (Fin N) (Fin N) ℂ,
      (∀ h ∈ H, ((ρ h : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) * A = A * ((ρ h : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ)) →
      (∀ h ∈ H, ((ρ h : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) * B = B * ((ρ h : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ)) → A * B = B * A

def IntSpan : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
    (N : ℕ) (ρ : G →* GL (Fin N) ℂ), Cont ρ → Irr ρ →
    ∀ T : Matrix (Fin N) (Fin N) ℂ, ∃ f : G → ℂ, Continuous f ∧
      ∀ i j, T i j = ∫ g, f g * ((ρ g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) i j ∂μ

def ConvComm : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
    (H : Subgroup G) (τ : G → G), Continuous τ →
    (∀ x y, τ (x * y) = τ y * τ x) → (∀ x, τ (τ x) = x) → (∀ g, ∃ h ∈ H, τ g = h * g * h⁻¹) →
    ∀ f₁ f₂ : G → ℂ, Continuous f₁ → Continuous f₂ →
      (∀ h ∈ H, ∀ x, f₁ (h * x * h⁻¹) = f₁ x) → (∀ h ∈ H, ∀ x, f₂ (h * x * h⁻¹) = f₂ x) →
      ∀ z, ∫ x, f₁ x * f₂ (x⁻¹ * z) ∂μ = ∫ x, f₂ x * f₁ (x⁻¹ * z) ∂μ

def CommutantMult : Prop :=
  ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H] [T2Space H]
    [SecondCountableTopology H] (N M : ℕ) (π : H →* GL (Fin N) ℂ) (σ : H →* GL (Fin M) ℂ),
    Cont π → Cont σ → Irr σ →
    (∀ A B : Matrix (Fin N) (Fin N) ℂ,
      (∀ h, ((π h : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) * A = A * ((π h : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ)) →
      (∀ h, ((π h : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) * B = B * ((π h : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ)) → A * B = B * A) →
    ∀ Hm : Submodule ℂ (Matrix (Fin N) (Fin M) ℂ),
      (∀ T, T ∈ Hm ↔ ∀ g, ((π g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) * T = T * ((σ g : GL (Fin M) ℂ) : Matrix (Fin M) (Fin M) ℂ)) →
      Module.finrank ℂ Hm ≤ 1

end PI.UMultOne
end
end

-- bundled from Formalism.PeriodIntegrals.UnimodGenus
section
open NumberField

noncomputable section

namespace PI.UG

section Defs

variable {R K V : Type*} [CommRing R] [Field K] [StarRing K] [Algebra R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]

def isom (h : V →ₗ⋆[K] V →ₗ[K] K) : Subgroup (V ≃ₗ[K] V) where
  carrier := {g | ∀ x y, h (g x) (g y) = h x y}
  one_mem' := fun _ _ => rfl
  mul_mem' := by
    intro a b ha hb x y
    change h (a (b x)) (a (b y)) = h x y
    rw [ha, hb]
  inv_mem' := by
    intro a ha x y
    have := ha (a.symm x) (a.symm y)
    change h (a.symm x) (a.symm y) = h x y
    simpa using this.symm

def gmap (g : V ≃ₗ[K] V) (L : Submodule R V) : Submodule R V :=
  L.map ((g : V →ₗ[K] V).restrictScalars R)

def dual (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule R V) : Submodule R V :=
  ⨅ y ∈ L, (1 : Submodule R K).comap ((h y).restrictScalars R)

def IsUnimodular (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule R V) : Prop :=
  dual h L = L

def locS {W : Type*} [AddCommGroup W] [Module R W] (S : Submonoid R) (L : Submodule R W) :
    Submodule R W where
  carrier := {x | ∃ s ∈ S, s • x ∈ L}
  zero_mem' := ⟨1, S.one_mem, by simp⟩
  add_mem' := by
    rintro x y ⟨s, hs, hx⟩ ⟨t, ht, hy⟩
    refine ⟨s * t, S.mul_mem hs ht, ?_⟩
    have e : (s * t) • (x + y) = t • (s • x) + s • (t • y) := by
      rw [smul_add, mul_smul, smul_comm s t x, mul_smul]
    rw [e]
    exact L.add_mem (L.smul_mem t hx) (L.smul_mem s hy)
  smul_mem' := by
    rintro r x ⟨s, hs, hx⟩
    refine ⟨s, hs, ?_⟩
    rw [smul_comm]
    exact L.smul_mem r hx

def hcompl (p : Ideal R) : Submonoid R :=
  Submonoid.closure {s | s ∉ p ∧ ∀ t : R, algebraMap R K t = star (algebraMap R K s) → t ∉ p}

def loc {W : Type*} [AddCommGroup W] [Module R W] (p : Ideal R) (L : Submodule R W) :
    Submodule R W :=
  locS (hcompl (K := K) p) L

def SameGenus (h : V →ₗ⋆[K] V →ₗ[K] K) (L M : Submodule R V) : Prop :=
  ∀ p : Ideal R, p.IsMaximal → ∃ g ∈ isom h, gmap g (loc (K := K) p L) = loc (K := K) p M

end Defs

abbrev Sp (E : Type) (n : ℕ) : Type := Fin n → E

def hStd (E : Type) [Field E] [StarRing E] (n : ℕ) : Sp E n →ₗ⋆[E] Sp E n →ₗ[E] E :=
  LinearMap.mk₂'ₛₗ (starRingEnd E) (RingHom.id E) (fun x y => ∑ i, star (x i) * y i)
    (by intro x y z; simp [add_mul, Finset.sum_add_distrib])
    (by intro c x y; simp [Finset.mul_sum, mul_assoc, starRingEnd_apply])
    (by intro x y z; simp [mul_add, Finset.sum_add_distrib])
    (by intro c x y; simp [Finset.mul_sum, mul_left_comm])

def stdLat (E : Type) [Field E] [NumberField E] (n : ℕ) : Submodule (𝓞 E) (Sp E n) :=
  Submodule.pi Set.univ fun _ => (1 : Submodule (𝓞 E) E)

def IsCMUnram (K : Type*) [Field K] [NumberField K] [StarRing K] : Prop :=
  IsTotallyComplex K ∧ (∀ (φ : K →+* ℂ) (a : K), φ (star a) = starRingEnd ℂ (φ a)) ∧
    ∀ P : Ideal (RingOfIntegers K), P.IsMaximal →
      ∃ θ t : RingOfIntegers K, algebraMap (RingOfIntegers K) K t =
        star (algebraMap (RingOfIntegers K) K θ) ∧ θ - t ∉ P

end PI.UG

namespace PI

open PI.UG

def UnimodGenus : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (n : ℕ), IsCMUnram E →
    ∀ N : Submodule (𝓞 E) (Sp E n), Submodule.IsLattice E N → IsUnimodular (hStd E n) N →
      SameGenus (hStd E n) (stdLat E n) N

end PI
end
end

-- bundled from Formalism.PeriodIntegrals.UnimodIdx
section
open MeasureTheory Topology

noncomputable section

namespace PI

def UnimodIdx : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [SigmaFinite μ], μ.IsHaarMeasure →
    ∀ (U : ℕ → Subgroup G), (∀ n, IsOpen (U n : Set G)) → (∀ V ∈ 𝓝 (1 : G), ∃ n, (U n : Set G) ⊆ V) →
    ∀ K : Subgroup G, IsOpen (K : Set G) → IsCompact (K : Set G) →
    (∀ x : G, (K.map (MulAut.conj x).toMonoidHom).relIndex K = (K.map (MulAut.conj x⁻¹).toMonoidHom).relIndex K) →
    μ.IsMulRightInvariant

end PI

end
end

-- bundled from Formalism.PeriodIntegrals.UnitKron
section
namespace PI

open Matrix ComplexOrder

def UnitKron : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (c : E →+* E), (∀ (φ : E →+* ℂ) (x : E), φ (c x) = (starRingEnd ℂ) (φ x)) →
  ∀ (k : ℕ) (J γ : Matrix (Fin k) (Fin k) E),
    (∀ φ : E →+* ℂ, (J.map φ).PosDef ∨ (-(J.map φ)).PosDef) →
    (γ.map c)ᵀ * J * γ = J → (∀ i, IsIntegral ℤ (γ.charpoly.coeff i)) →
    ∃ n : ℕ, 0 < n ∧ γ ^ n = 1

end PI
end

-- bundled from Formalism.PeriodIntegrals.WedgeDetNz
section
namespace PI

def WedgeDetNz : Prop :=
  ∀ (K V : Type) [Field K] [AddCommGroup V] [Module K V] (ρ : ℕ) (z : Fin ρ → V),
    LinearIndependent K z → ∃ φ : Fin ρ → (V →ₗ[K] K), (Matrix.of fun i k => φ i (z k)).det ≠ 0

end PI
end

