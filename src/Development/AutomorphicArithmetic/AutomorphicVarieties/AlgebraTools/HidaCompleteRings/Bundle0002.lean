import Mathlib
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0022
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0002

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.Component
section
open IsLocalRing

theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.component :
    ∀ (Λ T : Type) [CommRing Λ] [IsDomain Λ] [CommRing T] [Algebra Λ T] [Algebra.IsIntegral Λ T], (∀ a : Λ, a ≠ 0 → algebraMap Λ T a ∈ nonZeroDivisors T) → ∀ P ∈ minimalPrimes T, P.comap (algebraMap Λ T) = ⊥ ∧ (∀ p : Ideal Λ, p.IsPrime → ∃ Q : Ideal T, P ≤ Q ∧ Q.IsPrime ∧ Q.comap (algebraMap Λ T) = p) ∧ ringKrullDim (T ⧸ P) = ringKrullDim Λ := by
  intro Λ T _ _ _ _ _ hreg P hP
  have hP' : P.IsPrime := hP.1.1
  have hbot : P.comap (algebraMap Λ T) = ⊥ := by
    refine (Submodule.eq_bot_iff _).2 fun a ha => ?_
    by_contra hne
    exact Set.disjoint_left.1 (Ideal.disjoint_nonZeroDivisors_of_mem_minimalPrimes hP) ha (hreg a hne)
  refine ⟨hbot, fun p hp => ?_, ?_⟩
  · obtain ⟨Q, hQ, hQp, hQc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral p P (by rw [hbot]; exact bot_le)
    exact ⟨Q, hQ, hQp, hQc⟩
  · haveI : FaithfulSMul Λ (T ⧸ P) := by
      rw [faithfulSMul_iff_algebraMap_injective]
      intro a b hab
      rw [IsScalarTower.algebraMap_apply Λ T (T ⧸ P), IsScalarTower.algebraMap_apply Λ T (T ⧸ P)] at hab
      have hm : Ideal.Quotient.mk P (algebraMap Λ T a) = Ideal.Quotient.mk P (algebraMap Λ T b) := hab
      have h1 : algebraMap Λ T a - algebraMap Λ T b ∈ P := Ideal.Quotient.eq.1 hm
      have h2 : a - b ∈ P.comap (algebraMap Λ T) := by
        rw [Ideal.mem_comap, map_sub]
        exact h1
      rw [hbot, Submodule.mem_bot, sub_eq_zero] at h2
      exact h2
    exact GlobalTheory.ringKrullDim_eq_of_isIntegral Λ (T ⧸ P)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.ExtendPt
section
open IsLocalRing

theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.extendPt :
    ∀ (O Λ T K : Type) [CommRing O] [CommRing Λ] [CommRing T] [Field K] [IsAlgClosed K] [Algebra O Λ] [Algebra O T] [Algebra Λ T] [IsScalarTower O Λ T] [Algebra O K] [Algebra.IsIntegral Λ T] (P : Ideal T) (y : Λ →ₐ[O] K), P.comap (algebraMap Λ T) ≤ RingHom.ker y → ∃ x : T →ₐ[O] K, P ≤ RingHom.ker x ∧ ∀ a, x (algebraMap Λ T a) = y a :=
  _root_.UpperTheory.Reformulated.B.Qi4.extendPt
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.MaxIdem
section
open IsLocalRing

theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.maxIdem :
    ∀ (Λ T : Type) [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ] [CommRing T] [Algebra Λ T] [Module.Finite Λ T] (m : Ideal T), m.IsMaximal → ∃ e : T, IsIdempotentElem e ∧ e ∉ m ∧ ∀ m' : Ideal T, m'.IsMaximal → m' ≠ m → e ∈ m' := by
  intro Λ T _ _ _ _ _ _ _ m hm
  classical
  obtain ⟨hfin, -, n, h1, h2⟩ := UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.finMax Λ T
  set I' := Ideal.map (algebraMap Λ T) (maximalIdeal Λ) with hI'
  have key : ∀ (k : ℕ) (y : T), y ∈ ((maximalIdeal Λ) ^ k • (⊤ : Submodule Λ T)) ↔
      y ∈ (I' ^ k • (⊤ : Submodule T T)) := by
    intro k y
    rw [Ideal.smul_top_eq_map, Submodule.restrictScalars_mem, Ideal.map_pow, Ideal.smul_eq_mul,
      Ideal.mul_top]
  haveI hΛ : IsAdicComplete (maximalIdeal Λ) T := UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.finCompl Λ T (maximalIdeal Λ)
  have hT : IsAdicComplete I' T :=
    { haus' := fun y hy => IsHausdorff.haus' (I := maximalIdeal Λ) y fun k =>
        SModEq.sub_mem.mpr ((key k _).mpr (SModEq.sub_mem.mp (hy k)))
      prec' := fun f hf => by
        obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := maximalIdeal Λ) f fun hmn =>
          SModEq.sub_mem.mpr ((key _ _).mpr (SModEq.sub_mem.mp (hf hmn)))
        exact ⟨L, fun k => SModEq.sub_mem.mpr ((key k _).mp (SModEq.sub_mem.mp (hL k)))⟩ }
  haveI hJ : IsAdicComplete (⊥ : Ideal T).jacobson T :=
    UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.cofinalCompl T T I' _ n h1 h2 hT
  haveI := hfin
  haveI := Fintype.ofFinite (MaximalSpectrum T)
  set s := Finset.univ.filter (fun p : MaximalSpectrum T => p.asIdeal ≠ m) with hs
  set m'' := s.inf (fun p => p.asIdeal) with hm''
  have hnot : ¬ m'' ≤ m := by
    intro h
    obtain ⟨p, hp, hpm⟩ := (Ideal.IsPrime.inf_le' hm.isPrime).mp h
    exact (Finset.mem_filter.mp hp).2 (p.isMaximal.eq_of_le hm.ne_top hpm)
  have htop : m ⊔ m'' = ⊤ :=
    hm.out.2 _ (lt_of_le_of_ne le_sup_left fun h => hnot (h ▸ le_sup_right))
  have h1mem : (1 : T) ∈ m ⊔ m'' := htop ▸ Submodule.mem_top
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp h1mem
  have hbp : ∀ p : Ideal T, p.IsMaximal → p ≠ m → b ∈ p := by
    intro p hp hpm
    have hle : m'' ≤ p :=
      Finset.inf_le (f := fun p : MaximalSpectrum T => p.asIdeal) (b := ⟨p, hp⟩) (by simp [s, hpm])
    exact hle hb
  have memJ : ∀ y : T, (∀ p : Ideal T, p.IsMaximal → y ∈ p) → y ∈ (⊥ : Ideal T).jacobson :=
    fun y hy => Ideal.mem_sInf.mpr fun p hp => hy p hp.2
  have hJm : ∀ y : T, y ∈ (⊥ : Ideal T).jacobson → ∀ p : Ideal T, p.IsMaximal → y ∈ p :=
    fun y hy p hp => Ideal.mem_sInf.mp hy ⟨bot_le, hp⟩
  have hxx : b * b - b ∈ (⊥ : Ideal T).jacobson := by
    have e1 : b * b - b = -(b * a) := by
      have ha' : a = 1 - b := by rw [← hab]; ring
      rw [ha']
      ring
    rw [e1]
    refine memJ _ fun p hp => p.neg_mem ?_
    by_cases hpm : p = m
    · rw [hpm]
      exact m.mul_mem_left _ ha
    · exact p.mul_mem_right _ (hbp p hp hpm)
  obtain ⟨e, he, hex⟩ := UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.idemLift T _ b hxx
  refine ⟨e, he, fun hem => ?_, fun p hp hpm => ?_⟩
  · apply hm.ne_top
    rw [Ideal.eq_top_iff_one]
    have h3 : e - b ∈ m := hJm _ hex m hm
    have h4 : (1 : T) = e - (e - b) + a := by rw [← hab]; ring
    rw [h4]
    exact m.add_mem (m.sub_mem hem h3) ha
  · have h3 : e - b ∈ p := hJm _ hex p hp
    have h4 : e = (e - b) + b := by ring
    rw [h4]
    exact p.add_mem h3 (hbp p hp hpm)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.TopLeCopiesSelf
section
noncomputable section

namespace UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite

section Alg

variable {k G V N : Type} [Field k] [Group G] [AddCommGroup V] [Module k V] [AddCommGroup N] [Module k N]

def Stab (ρ : Representation k G V) (W : Submodule k V) : Prop := ∀ g, ∀ v ∈ W, ρ g v ∈ W

structure IrrSub (ρ : Representation k G V) (W : Submodule k V) : Prop where
  stab : Stab ρ W
  ne : W ≠ ⊥
  irr : ∀ W' ≤ W, Stab ρ W' → W' = ⊥ ∨ W' = W

abbrev Into (ρ : Representation k G V) (Y : Submodule k V) (σ : Representation k G N) : Type :=
  {f : N →ₗ[k] V // (∀ g v, f (σ g v) = ρ g (f v)) ∧ LinearMap.range f ≤ Y}

def copies (ρ : Representation k G V) (Y : Submodule k V) (σ : Representation k G N) : Submodule k V :=
  ⨆ f : Into ρ Y σ, LinearMap.range f.1

theorem Stab.comp {ρ : Representation k G V} {W : Submodule k V} (h : Stab ρ W) {H : Type} [Group H] (j : H →* G) :
    Stab (ρ.comp j) W := fun x => h (j x)

def piRep (ρ : Representation k G V) (ι : Type) : Representation k G (ι → V) where
  toFun g := LinearMap.compLeft (ρ g) ι
  map_one' := by ext1 F; simp; rfl
  map_mul' a b := by ext1 F; simp; rfl

@[simp] theorem piRep_apply (ρ : Representation k G V) (ι : Type) (g : G) (F : ι → V) (i : ι) :
    piRep ρ ι g F i = ρ g (F i) := rfl

def IsTypeVec (σ : Representation k G N) (K : Subgroup G) {μ : Type} [Fintype μ] (τ : K → Matrix μ μ k) (e : μ → N) : Prop :=
  ∀ (x : K) a, ∑ b, τ x a b • σ x (e b) = e a

end Alg

structure LocFac {G H : Type} [Group G] [Group H] (j : H →* G) (p : G →* H) : Prop where
  left : ∀ h, p (j h) = h
  comm : ∀ g, p g = 1 → ∀ h, Commute (j h) g

theorem LocFac.dec {G H : Type} [Group G] [Group H] {j : H →* G} {p : G →* H} (h : LocFac j p) (g : G) :
    p ((j (p g))⁻¹ * g) = 1 := by rw [map_mul, map_inv, h.left, inv_mul_cancel]

structure PosForm {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    (B : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) : Prop where
  herm : ∀ u v, star (B u v) = B v u
  nonneg : ∀ v, 0 ≤ (B v v).re
  defn : ∀ v, B v v = 0 → v = 0
  inv : ∀ g u v, B (ρ g u) (ρ g v) = B u v

section Mass

variable {G : Type} [Group G]

def stabGrp (Γ K : Subgroup G) (x : G) : Subgroup G := Γ ⊓ K.map (MulAut.conj x).toMonoidHom

def massSum (Γ K : Subgroup G) (φ : G → ℂ) : ℂ :=
  ∑ᶠ q : DoubleCoset.Quotient (Γ : Set G) K, φ q.out / (Nat.card (stabGrp Γ K q.out) : ℂ)

structure FinMass (Γ K : Subgroup G) : Prop where
  fin : Finite (DoubleCoset.Quotient (Γ : Set G) K)
  stab : ∀ x, Finite (stabGrp Γ K x)

end Mass

end UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite
end
end

