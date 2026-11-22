import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1308
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1299
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0052
import ReciprocityTheory.SemistableReduction.Bundle0025
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1294
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import GroundTheory.AutomorphicForms.MultiplicityOne.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1261
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1295
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1241
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0016
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0183
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsConstAlongSingleton

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EnvelopingAlgebraLineWords
section
open Matrix GlobalTheory.TorFin
open scoped ContDiff

namespace GlobalTheory.TorFin.WordSpan

variable {n : ℕ} {G : Type} [Group G]

theorem map_one_of_isMulOn {J : Matrix (Fin n) (Fin n) ℂ} {s : Matrix (Fin n) (Fin n) ℂ → G}
    (hs : IsMulOn J s) : s 1 = 1 := by
  have h1 : IsUni J (1 : Matrix (Fin n) (Fin n) ℂ) := by simp [IsUni]
  have h := hs 1 1 h1 h1
  rw [mul_one] at h
  exact mul_left_cancel (a := s 1) (by rw [mul_one]; exact h.symm)

theorem lineOf_zero {J : Matrix (Fin n) (Fin n) ℂ} {s : Matrix (Fin n) (Fin n) ℂ → G}
    (hs : IsMulOn J s) (Z : Matrix (Fin n) (Fin n) ℂ) : lineOf s Z 0 = 1 := by
  simp [lineOf, map_one_of_isMulOn hs]

theorem rho_skew_apply {J : Matrix (Fin n) (Fin n) ℂ} {s : Matrix (Fin n) (Fin n) ℂ → G}
    (hs : IsMulOn J s) {ρ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ (smLoc J s)}
    (hρ : IsRightDer J s ρ) {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : IsSkew J Z) (f : smLoc J s) :
    (ρ Z f).1 = rder (lineOf s Z) f.1 := by
  funext g
  have h := hρ Z hZ f g 0
  rw [lineOf_zero hs, mul_one] at h
  exact h.deriv.symm

theorem prod_apply {J : Matrix (Fin n) (Fin n) ℂ} {s : Matrix (Fin n) (Fin n) ℂ → G}
    (hs : IsMulOn J s) {ρ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ (smLoc J s)}
    (hρ : IsRightDer J s ρ) (L : List (Matrix (Fin n) (Fin n) ℂ)) (hL : ∀ Z ∈ L, IsSkew J Z)
    (f : smLoc J s) : ((L.map ρ).prod f).1 = (L.map (lineOf s)).foldr rder f.1 := by
  induction L with
  | nil => simp
  | cons Z L ih =>
    simp only [List.map_cons, List.prod_cons, List.foldr_cons, Module.End.mul_apply]
    rw [rho_skew_apply hs hρ (hL Z (by simp)), ih (fun Y hY => hL Y (by simp [hY]))]

theorem skew_decomp {J : Matrix (Fin n) (Fin n) ℂ} (hJ : Jᴴ = J) (hdet : IsUnit J.det)
    (Y : Matrix (Fin n) (Fin n) ℂ) :
    ∃ Z₁ Z₂, IsSkew J Z₁ ∧ IsSkew J Z₂ ∧ Y = Z₁ + Complex.I • Z₂ := by
  have hJJ : J * J⁻¹ = 1 := Matrix.mul_nonsing_inv J hdet
  have hJiJ : J⁻¹ * J = 1 := Matrix.nonsing_inv_mul J hdet
  set Ys := J⁻¹ * Yᴴ * J with hYs
  have hYsH : Ysᴴ * J = J * Y := by
    rw [hYs, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hJ,
      conjTranspose_nonsing_inv, hJ, Matrix.mul_assoc, Matrix.mul_assoc, hJiJ, Matrix.mul_one]
  have hJYs : J * Ys = Yᴴ * J := by
    rw [hYs, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hJJ, Matrix.one_mul]
  refine ⟨(1 / 2 : ℂ) • (Y - Ys), (1 / (2 * Complex.I)) • (Y + Ys), ?_, ?_, ?_⟩
  · simp only [IsSkew, conjTranspose_smul, conjTranspose_sub, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.sub_mul, Matrix.mul_sub, hYsH, hJYs]
    have : star (1 / 2 : ℂ) = 1 / 2 := by simp
    rw [this, ← smul_add]; simp
  · simp only [IsSkew, conjTranspose_smul, conjTranspose_add, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.add_mul, Matrix.mul_add, hYsH, hJYs]
    have : star (1 / (2 * Complex.I)) = -(1 / (2 * Complex.I)) := by
      simp [Complex.ext_iff]
    rw [this, neg_smul, add_comm (J * Y), neg_add_cancel]
  · rw [smul_smul, show Complex.I * (1 / (2 * Complex.I)) = 1 / 2 by field_simp]
    module

end GlobalTheory.TorFin.WordSpan

namespace GlobalTheory.TorFin.WordSpan

variable {n : ℕ} {G : Type} [Group G]

theorem wop_single (l : List (ℝ → G)) (f : G → ℂ) : wop (Finsupp.single l 1) f = l.foldr rder f := by
  funext g; simp [wop, Finsupp.sum_single_index]

theorem wop_zero (f : G → ℂ) : wop (0 : List (ℝ → G) →₀ ℂ) f = 0 := by
  funext g; simp [wop]

theorem wop_add (z z' : List (ℝ → G) →₀ ℂ) (f : G → ℂ) : wop (z + z') f = wop z f + wop z' f := by
  funext g
  simp only [wop, Pi.add_apply]
  rw [Finsupp.sum_add_index' (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)]

theorem wop_smul (c : ℂ) (z : List (ℝ → G) →₀ ℂ) (f : G → ℂ) : wop (c • z) f = c • wop z f := by
  funext g
  simp only [wop, Pi.smul_apply, smul_eq_mul]
  rw [Finsupp.sum_smul_index' (fun _ => zero_mul _), Finsupp.mul_sum]
  simp [smul_eq_mul, mul_assoc]

def words (J : Matrix (Fin n) (Fin n) ℂ) (s : Matrix (Fin n) (Fin n) ℂ → G)
    (ρ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ (smLoc J s)) : Set (Module.End ℂ (smLoc J s)) :=
  {T | ∃ L : List (Matrix (Fin n) (Fin n) ℂ), (∀ Z ∈ L, IsSkew J Z) ∧ T = (L.map ρ).prod}

theorem adjoin_le_span {J : Matrix (Fin n) (Fin n) ℂ} (hJ : Jᴴ = J) (hdet : IsUnit J.det)
    {s : Matrix (Fin n) (Fin n) ℂ → G} (ρ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ (smLoc J s)) :
    ∀ T ∈ Algebra.adjoin ℂ (Set.range ρ), T ∈ Submodule.span ℂ (words J s ρ) := by
  have hone : (1 : Module.End ℂ (smLoc J s)) ∈ Submodule.span ℂ (words J s ρ) :=
    Submodule.subset_span ⟨[], by simp, by simp⟩
  have hmul : ∀ x y, x ∈ Submodule.span ℂ (words J s ρ) → y ∈ Submodule.span ℂ (words J s ρ) →
      x * y ∈ Submodule.span ℂ (words J s ρ) := by
    intro x y hx hy
    have hxy := Submodule.mul_mem_mul hx hy
    rw [Submodule.span_mul_span] at hxy
    refine Submodule.span_le.mpr ?_ hxy
    rintro _ ⟨a, ⟨L, hL, rfl⟩, b, ⟨L', hL', rfl⟩, rfl⟩
    refine Submodule.subset_span ⟨L ++ L', ?_, by simp [List.prod_append]⟩
    intro Z hZ
    rcases List.mem_append.mp hZ with h | h
    · exact hL Z h
    · exact hL' Z h
  let S : Subalgebra ℂ (Module.End ℂ (smLoc J s)) :=
    (Submodule.span ℂ (words J s ρ)).toSubalgebra hone hmul
  have hle : Algebra.adjoin ℂ (Set.range ρ) ≤ S := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨Y, rfl⟩
    obtain ⟨Z₁, Z₂, h₁, h₂, rfl⟩ := skew_decomp hJ hdet Y
    show ρ (Z₁ + Complex.I • Z₂) ∈ Submodule.span ℂ (words J s ρ)
    rw [map_add, map_smul]
    refine Submodule.add_mem _ (Submodule.subset_span ⟨[Z₁], by simpa using h₁, by simp⟩)
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨[Z₂], by simpa using h₂, by simp⟩))
  intro T hT
  exact hle hT

theorem exists_wop_of_mem_adjoin : ∀ (n : ℕ) (G : Type) [Group G] (J : Matrix (Fin n) (Fin n) ℂ) (s : Matrix (Fin n) (Fin n) ℂ → G), Jᴴ = J → IsUnit J.det → IsMulOn J s → ∀ ρ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ (smLoc J s), IsRightDer J s ρ → ∀ T ∈ Algebra.adjoin ℂ (Set.range ρ), ∃ z : List (ℝ → G) →₀ ℂ, (∀ l ∈ z.support, ∀ γ ∈ l, ∃ Z, IsSkew J Z ∧ γ = lineOf s Z) ∧ ∀ f : smLoc J s, (T f).1 = wop z f.1 := by
  intro n G _ J s hJ hdet hs ρ hρ T hT
  classical
  have hS := adjoin_le_span hJ hdet ρ T hT
  clear hT
  induction hS using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨L, hL, rfl⟩ := hx
    refine ⟨Finsupp.single (L.map (lineOf s)) 1, ?_, ?_⟩
    · intro l hl γ hγ
      have hl' : l = L.map (lineOf s) := by
        by_contra hne
        simp [Finsupp.single_apply, Ne.symm hne] at hl
        exact hne hl
      subst hl'
      obtain ⟨Z, hZ, rfl⟩ := List.mem_map.mp hγ
      exact ⟨Z, hL Z hZ, rfl⟩
    · intro f
      rw [prod_apply hs hρ L hL f, wop_single]
  | zero =>
    exact ⟨0, by simp, fun f => by rw [wop_zero]; rfl⟩
  | add x y _ _ hx hy =>
    obtain ⟨z, hz, hzf⟩ := hx
    obtain ⟨z', hz', hzf'⟩ := hy
    refine ⟨z + z', ?_, ?_⟩
    · intro l hl
      rcases Finset.mem_union.mp (Finsupp.support_add hl) with h | h
      · exact hz l h
      · exact hz' l h
    · intro f
      rw [wop_add, ← hzf, ← hzf']
      rfl
  | smul c x _ hx =>
    obtain ⟨z, hz, hzf⟩ := hx
    refine ⟨c • z, fun l hl => hz l (Finsupp.support_smul hl), ?_⟩
    intro f
    rw [wop_smul, ← hzf]
    rfl

end GlobalTheory.TorFin.WordSpan
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EquivariantDoubleCosetSectionMemEquivariant
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.TraceBlocks
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.TraceBlocks

def secMemLeftMul {H V : Type} [Group H] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ H V) (g : H) : Module.End ℂ V ≃+ Module.End ℂ V where
  toFun f := ρ g * f
  invFun f := ρ g⁻¹ * f
  left_inv f := by
    simp only [← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]
  right_inv f := by
    simp only [← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
  map_add' a b := mul_add _ a b

theorem secM_mem_eqvM : ∀ (G H V : Type) [Group G] [Group H] [AddCommGroup V] [Module ℂ V]
    (ι : H →* G) (ρ : Representation ℂ H V) (K' : Subgroup G) (x : G) (v : V),
    secM ι ρ K' x v ∈ eqvM ι ρ K' := by
  intro G H V _ _ _ _ ι ρ K' x v
  refine ⟨fun g y => ?_, fun k hk y => ?_⟩
  · change ((stabCard ι K' x : ℂ))⁻¹ • (∑ᶠ h : H, if (ι h * x)⁻¹ * (ι g * y) ∈ K' then ρ h else 0) v
      = ρ g (((stabCard ι K' x : ℂ))⁻¹ • (∑ᶠ h : H, if (ι h * x)⁻¹ * y ∈ K' then ρ h else 0) v)
    have hsum : (∑ᶠ h : H, if (ι h * x)⁻¹ * (ι g * y) ∈ K' then ρ h else 0)
        = ρ g * (∑ᶠ h : H, if (ι h * x)⁻¹ * y ∈ K' then ρ h else 0) := by
      rw [← finsum_comp_equiv (Equiv.mulLeft g)]
      have hpt : ∀ h' : H, (fun h : H => if (ι h * x)⁻¹ * (ι g * y) ∈ K' then ρ h else 0)
          ((Equiv.mulLeft g) h') = secMemLeftMul ρ g (if (ι h' * x)⁻¹ * y ∈ K' then ρ h' else 0) := by
        intro h'
        have he : (ι (g * h') * x)⁻¹ * (ι g * y) = (ι h' * x)⁻¹ * y := by
          rw [map_mul]; group
        simp only [Equiv.coe_mulLeft, he]
        change _ = ρ g * _
        split_ifs
        · exact map_mul ρ g h'
        · exact (mul_zero _).symm
      simp_rw [hpt]
      exact (AddEquiv.map_finsum (secMemLeftMul ρ g) _).symm
    rw [hsum, map_smul]
    rfl
  · change ((stabCard ι K' x : ℂ))⁻¹ • (∑ᶠ h : H, if (ι h * x)⁻¹ * (y * k) ∈ K' then ρ h else 0) v
      = ((stabCard ι K' x : ℂ))⁻¹ • (∑ᶠ h : H, if (ι h * x)⁻¹ * y ∈ K' then ρ h else 0) v
    have hc : ∀ h : H, ((ι h * x)⁻¹ * (y * k) ∈ K' ↔ (ι h * x)⁻¹ * y ∈ K') := by
      intro h
      rw [← mul_assoc]
      exact Subgroup.mul_mem_cancel_right K' hk
    simp_rw [hc]

end GlobalTheory.BCT.TraceBlocks
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EquivariantFunctionEqFinsumDoubleCosetSections
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.TraceBlocks
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT.TraceBlocks.Decomp

variable {G H V : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V]

theorem secM_apply' (ι : H →* G) (ρ : Representation ℂ H V) (K : Subgroup G) (x : G) (v : V) (y : G) :
    secM ι ρ K x v y =
      ((stabCard ι K x : ℂ))⁻¹ • (∑ᶠ h : H, if (ι h * x)⁻¹ * y ∈ K then ρ h else 0) v := rfl

theorem finsum_apply_eq (ι : H →* G) (ρ : Representation ℂ H V) (K : Subgroup G) {φ : G → V}
    (hφ : φ ∈ eqvM ι ρ K) (x y : G) (hs : Set.Finite {h : H | (ι h * x)⁻¹ * y ∈ K}) :
    (∑ᶠ h : H, if (ι h * x)⁻¹ * y ∈ K then ρ h else 0) (φ x) =
      Nat.card {h : H | (ι h * x)⁻¹ * y ∈ K} • φ y := by
  rw [finsum_eq_sum_of_support_subset _ (s := hs.toFinset) ?_]
  · rw [LinearMap.sum_apply,
      Finset.sum_congr rfl (g := fun _ => φ y) ?_, Finset.sum_const, ← Nat.card_eq_card_finite_toFinset]
    intro h hh
    rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hh
    rw [if_pos hh, ← hφ.1 h x, ← hφ.2 _ hh (ι h * x), mul_inv_cancel_left]
  · intro h hh
    rw [Function.mem_support] at hh
    rw [Set.Finite.coe_toFinset, Set.mem_setOf_eq]
    by_contra hc
    exact hh (if_neg hc)

theorem card_eq (ι : H →* G) (hι : Function.Injective ι) (K : Subgroup G) (x : G) (h₀ : H) {k₀ : G}
    (hk₀ : k₀ ∈ K) :
    ∃ e : {h : H | (ι h * x)⁻¹ * (ι h₀ * x * k₀) ∈ K} → ↥(ι.range ⊓ K.map (MulAut.conj x).toMonoidHom),
      Function.Bijective e := by
  have key : ∀ h : H, (ι h * x)⁻¹ * (ι h₀ * x * k₀) ∈ K ↔ x⁻¹ * ι (h⁻¹ * h₀) * x ∈ K := by
    intro h
    have : (ι h * x)⁻¹ * (ι h₀ * x * k₀) = x⁻¹ * ι (h⁻¹ * h₀) * x * k₀ := by
      simp only [map_mul, map_inv, _root_.mul_inv_rev, mul_assoc]
    rw [this, Subgroup.mul_mem_cancel_right K hk₀]
  refine ⟨fun h => ⟨ι (h.1⁻¹ * h₀), Subgroup.mem_inf.mpr ⟨⟨_, rfl⟩,
    Subgroup.mem_map.mpr ⟨x⁻¹ * ι (h.1⁻¹ * h₀) * x, (key h.1).mp h.2, ?_⟩⟩⟩, ?_, ?_⟩
  · simp [MulAut.conj_apply, mul_assoc]
  · intro a b hab
    have := hι (congrArg Subtype.val hab)
    exact Subtype.ext (by simpa using this)
  · rintro ⟨g, hg⟩
    obtain ⟨⟨s, rfl⟩, hm⟩ := Subgroup.mem_inf.mp hg
    obtain ⟨k, hk, hks⟩ := Subgroup.mem_map.mp hm
    refine ⟨⟨h₀ * s⁻¹, ?_⟩, ?_⟩
    · show (ι (h₀ * s⁻¹) * x)⁻¹ * (ι h₀ * x * k₀) ∈ K
      rw [key]
      have : x⁻¹ * ι ((h₀ * s⁻¹)⁻¹ * h₀) * x = k := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hks
        simp [← hks, mul_assoc]
      rw [this]; exact hk
    · apply Subtype.ext
      simp

end GlobalTheory.BCT.TraceBlocks.Decomp

namespace GlobalTheory.BCT.TraceBlocks.Decomp

variable {G H V : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V]

theorem secM_self (ι : H →* G) (hι : Function.Injective ι) (ρ : Representation ℂ H V) (K : Subgroup G)
    {φ : G → V} (hφ : φ ∈ eqvM ι ρ K) (x : G) [Finite ↥(ι.range ⊓ K.map (MulAut.conj x).toMonoidHom)]
    (h₀ : H) {k₀ : G} (hk₀ : k₀ ∈ K) :
    secM ι ρ K x (φ x) (ι h₀ * x * k₀) = φ (ι h₀ * x * k₀) := by
  obtain ⟨e, he⟩ := card_eq ι hι K x h₀ hk₀
  have hfin : Set.Finite {h : H | (ι h * x)⁻¹ * (ι h₀ * x * k₀) ∈ K} :=
    Set.finite_coe_iff.mp (Finite.of_injective e he.1)
  rw [secM_apply', finsum_apply_eq ι ρ K hφ x _ hfin, Nat.card_congr (Equiv.ofBijective e he),
    ← Nat.cast_smul_eq_nsmul ℂ]
  have hpos : (0 : ℕ) < Nat.card ↥(ι.range ⊓ K.map (MulAut.conj x).toMonoidHom) := Nat.card_pos
  exact inv_smul_smul₀ (Nat.cast_ne_zero.mpr hpos.ne') _

theorem secM_off (ι : H →* G) (ρ : Representation ℂ H V) (K : Subgroup G) (x y : G) (v : V)
    (hy : ∀ h : H, (ι h * x)⁻¹ * y ∉ K) : secM ι ρ K x v y = 0 := by
  rw [secM_apply']
  simp only [hy, if_false, finsum_zero, LinearMap.zero_apply, smul_zero]

end GlobalTheory.BCT.TraceBlocks.Decomp

open GlobalTheory.BCT.TraceBlocks.Decomp in

theorem GlobalTheory.BCT.TraceBlocks.eqvM_eq_finsum_secM : ∀ (G H V : Type) [Group G] [Group H] [AddCommGroup V] [Module ℂ V] (ι : H →* G), Function.Injective ι → ∀ (ρ : Representation ℂ H V) (K' : Subgroup G), Finite (DoubleCoset.Quotient (ι.range : Set G) (K' : Set G)) → (∀ x : G, Finite (ι.range ⊓ K'.map (MulAut.conj x).toMonoidHom : Subgroup G)) → ∀ φ ∈ eqvM ι ρ K', ∑ᶠ q : DoubleCoset.Quotient (ι.range : Set G) (K' : Set G), secM ι ρ K' (Quotient.out q) (φ (Quotient.out q)) = φ := by
  intro G H V _ _ _ _ ι hι ρ K' hQ hS φ hφ
  haveI := Fintype.ofFinite (DoubleCoset.Quotient (ι.range : Set G) (K' : Set G))
  funext y
  rw [finsum_eq_sum_of_fintype, Finset.sum_apply, Finset.sum_eq_single (DoubleCoset.mk ι.range K' y)]
  · obtain ⟨g, hg, k₀, hk₀, hy⟩ := (DoubleCoset.eq ι.range K'
      (Quotient.out (DoubleCoset.mk ι.range K' y)) y).mp (DoubleCoset.out_eq' _ _ _)
    obtain ⟨h₀, rfl⟩ := hg
    haveI := hS (Quotient.out (DoubleCoset.mk ι.range K' y))
    have key := secM_self ι hι ρ K' hφ (Quotient.out (DoubleCoset.mk ι.range K' y)) h₀ hk₀
    rw [← hy] at key
    exact key
  · intro q _ hq
    refine secM_off ι ρ K' _ y _ fun h hh => hq ?_
    refine (DoubleCoset.out_eq' _ _ q).symm.trans ((DoubleCoset.eq _ _ _ _).mpr
      ⟨ι h, ⟨h, rfl⟩, _, hh, (mul_inv_cancel_left _ _).symm⟩)
  · intro h
    exact absurd (Finset.mem_univ _) h
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleOfFinrankLeCardAlgHomAlgebraicClosure
section
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open scoped TensorProduct

namespace GlobalTheory

theorem etale_of_finrank_le_card_algHom_algebraicClosure : ∀ (E R : Type) [Field E] [CommRing R] [Algebra E R] [Module.Finite E R], Finite (R →ₐ[E] AlgebraicClosure E) ∧ Nat.card (R →ₐ[E] AlgebraicClosure E) ≤ Module.finrank E R ∧ (Module.finrank E R ≤ Nat.card (R →ₐ[E] AlgebraicClosure E) → Algebra.Etale E R) := by
  intro E R _ _ _ _
  refine ⟨inferInstance, card_algHom_le_finrank E R (AlgebraicClosure E), fun hle => ?_⟩
  classical
  set Ω := AlgebraicClosure E
  set S := Ω ⊗[E] R
  set ι := S →ₐ[Ω] Ω
  have : Fintype ι := Fintype.ofFinite ι
  have hcard : Nat.card ι = Nat.card (R →ₐ[E] Ω) :=
    (Nat.card_congr (AlgHom.liftEquiv E Ω R Ω)).symm
  have hrank : Module.finrank Ω S = Module.finrank E R := Module.finrank_baseChange
  let φ : S →ₐ[Ω] (ι → Ω) := AlgHom.pi fun f => f
  have hsurj : Function.Surjective φ.toLinearMap := by
    rw [← LinearMap.dualMap_injective_iff, injective_iff_map_eq_zero]
    intro g hg
    have hs : ∀ i : ι, (fun j => if i = j then (1 : Ω) else 0) = Pi.single i 1 := fun i => by
      ext j; simp [Pi.single_apply, eq_comm]
    have hli := Fintype.linearIndependent_iff.mp (linearIndependent_algHom_toLinearMap Ω S Ω)
      (fun f => g (Pi.single f 1))
    have hc : ∀ f, g (Pi.single f 1) = 0 := by
      apply hli
      refine LinearMap.ext fun s => ?_
      have := LinearMap.congr_fun hg s
      simp only [LinearMap.dualMap_apply, LinearMap.zero_apply] at this
      rw [LinearMap.zero_apply, ← this, LinearMap.pi_apply_eq_sum_univ g]
      simp only [hs, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [φ, mul_comm]
    refine LinearMap.ext fun x => ?_
    rw [LinearMap.pi_apply_eq_sum_univ g]
    simp [hs, hc]
  have hinj : Function.Injective φ.toLinearMap := by
    have hle' : Module.finrank Ω S ≤ Module.finrank Ω (ι → Ω) := by
      rw [Module.finrank_fintype_fun_eq_card, ← Nat.card_eq_fintype_card, hcard, hrank]
      exact hle
    have hge : Module.finrank Ω (ι → Ω) ≤ Module.finrank Ω S := by
      have h := LinearMap.finrank_range_le φ.toLinearMap
      rwa [LinearMap.range_eq_top.mpr hsurj, finrank_top] at h
    exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (le_antisymm hle' hge)).mpr hsurj
  have : IsReduced S := isReduced_of_injective φ.toRingHom hinj
  have : IsArtinianRing S := .of_finite Ω S
  have hE : Algebra.Etale Ω S := by
    have (I : MaximalSpectrum S) : Algebra.FormallyEtale Ω (S ⧸ I.asIdeal) := by
      let := Ideal.Quotient.field I.asIdeal
      exact Algebra.FormallyEtale.of_isSeparable Ω (S ⧸ I.asIdeal)
    exact ⟨.of_equiv ((IsArtinianRing.equivPi S).restrictScalars Ω).symm,
      Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩
  exact Algebra.Etale.of_etale_tensorProduct_of_faithfullyFlat Ω

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdelicWhittakerEquivariantBumpMirabolicStatement
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_adelic_whittaker_equivariant_bump_mirabolic : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))), ∃ b : GA E (m + 1) → ℂ, b 1 = 1 ∧ (∀ u ∈ GlobalTheory.JSW.NA E (m + 1), ∀ g, b (u * g) = GlobalTheory.JSW.psiN u * b g) ∧ (∃ C : Set (GA E (m + 1)), IsCompact C ∧ ∀ p ∈ GlobalTheory.JSW.mirS E S m, b p ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA E (m + 1), u⁻¹ * p ∈ C) ∧ (∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧ ∀ u ∈ U, ∀ g, b (g * finGL E (m + 1) u) = b g) ∧ ∀ g, ContDiffOn ℝ ∞ (chart b g) (invSet E (m + 1)) := by
  first | exact @GlobalTheory.WhitBump.exists_bump | exact GlobalTheory.WhitBump.exists_bump | (intros; apply GlobalTheory.WhitBump.exists_bump <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBaseElementNegativeAtTwoEmbeddingsStatement
section
open NumberField IsDedekindDomain
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_base_element_negative_at_two_embeddings : ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L], Module.finrank K L = 2 → ∀ σ : L →+* L, σ ≠ RingHom.id L → (∀ x : K, σ (algebraMap K L x) = algebraMap K L x) → (∀ (φ : L →+* ℂ) (x : L), φ (σ x) = (starRingEnd ℂ) (φ x)) → ∀ ε ε' : L →+* ℂ, ε ≠ ε' → ε ≠ ComplexEmbedding.conjugate ε' → ∃ h : K, h ≠ 0 ∧ (ε (algebraMap K L h)).re < 0 ∧ (ε' (algebraMap K L h)).re < 0 ∧ (∀ φ : L →+* ℂ, φ ≠ ε → φ ≠ ComplexEmbedding.conjugate ε → φ ≠ ε' → φ ≠ ComplexEmbedding.conjugate ε' → 0 < (φ (algebraMap K L h)).re) ∧ ∀ v : HeightOneSpectrum (𝓞 K), ∃ z : v.adicCompletion K ⊗[K] L, Algebra.norm (v.adicCompletion K) z = algebraMap K (v.adicCompletion K) h := by
  first | (exact @GlobalTheory.QuadSigns.exists_signs) | (exact GlobalTheory.QuadSigns.exists_signs) | (intros; apply GlobalTheory.QuadSigns.exists_signs  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBlockUpperParabolicLeviProjectionUnipotentStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_blockUpperParabolic_levi_projection_unipotent : ∀ (E : Type) [Field E] [NumberField E] (n a b : ℕ) (h : a + b = n) (w : Pl E), ∃ (s : GLw a w × GLw b w →* GlobalTheory.LeviDesc.parP a n w) (π : GlobalTheory.LeviDesc.parP a n w →* GLw a w × GLw b w) (u : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)) →* GlobalTheory.LeviDesc.parP a n w), (∀ m, (s m : GLw n w) = blk h w m 0) ∧ (∀ X, (u X : GLw n w) = blk h w 1 (Multiplicative.toAdd X)) ∧ (∀ m, π (s m) = m) ∧ Function.Injective u ∧ (∀ p, π p = 1 ↔ ∃ X, u X = p) ∧ (∀ k ∈ (GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b), s k ∈ (GlobalTheory.LFun.KGL w n).subgroupOf (GlobalTheory.LeviDesc.parP a n w)) ∧ (∀ k ∈ (GlobalTheory.LFun.KGL w n).subgroupOf (GlobalTheory.LeviDesc.parP a n w), π k ∈ (GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b)) ∧ (∀ X, u X ∈ (GlobalTheory.LFun.KGL w n).subgroupOf (GlobalTheory.LeviDesc.parP a n w) ↔ X ∈ intMat a b w) := by
  first | exact @GlobalTheory.LeviDesc.LeviHoms.levi_homs | exact GlobalTheory.LeviDesc.LeviHoms.levi_homs | (intros; apply GlobalTheory.LeviDesc.LeviHoms.levi_homs <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBundleIsoZpowLocalUnitsPow
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

noncomputable section

namespace GlobalTheory.FormalAlg

open ReciprocityTheory.ChartRestriction.G.Semi

theorem commGroup_mul_inv_zpow {G : Type} [CommGroup G] (x y : G) (a : ℤ) : (x * y⁻¹) ^ a = x ^ a * (y ^ a)⁻¹ := by
  rw [mul_zpow, inv_zpow]

theorem div_pull_pw_g {X Y : Scheme.{0}} (A : LB X) (H : LB Y) (φ : Y ⟶ X) (a : ℤ) (p q : (PUnit → A.ι) × H.ι) :
    (LB.div ((GlobalTheory.AbLaw.pw A a).pull φ) (GlobalTheory.AbLaw.pw H a)).g p q =
      (((LB.div (A.pull φ) H).g p q) ^ a : Γ(Y, (LB.div (A.pull φ) H).U p ⊓ (LB.div (A.pull φ) H).U q)ˣ) := by
  show res _ (∏ _k : PUnit, res _ (pullU φ _ (A.g _ _ ^ a)) ^ (1 : ℤ)) * (res _ (H.g p.2 q.2 ^ a))⁻¹ =
    (res _ (∏ _k : PUnit, res _ (pullU φ _ (A.g _ _)) ^ (1 : ℤ)) * (res _ (H.g p.2 q.2))⁻¹) ^ a
  simp only [Fintype.prod_unique, zpow_one, map_zpow]
  exact (commGroup_mul_inv_zpow _ _ a).symm

theorem lbIso_pw_pull_gw : ∀ (X Y : Scheme.{0}) (φ : Y ⟶ X) (A : LB X) (H : LB Y) (w : LB.Iso H (A.pull φ)), w.IsGen → ∀ a : ℤ, ∃ wa : LB.Iso (GlobalTheory.AbLaw.pw H a) ((GlobalTheory.AbLaw.pw A a).pull φ), wa.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (k : A.ι) (k' : H.ι), φ (r z) ∈ A.U k → r z ∈ H.U k' → Geo.Tor.gw wa r z k k' = Geo.Tor.gw w r z k k' ^ a := by
  intro X Y φ A H w hw a
  refine ⟨⟨fun p => w.s p ^ a⟩, ?_, ?_⟩
  · intro p q
    have e := congrArg (· ^ a) (hw p q)
    simp only [mul_zpow, ← map_zpow] at e
    exact e.trans (congrArg (· * res _ (w.s q ^ a)) (div_pull_pw_g A H φ a p q).symm)
  · intro Z r z k k' _ _
    exact map_zpow _ _ a

end GlobalTheory.FormalAlg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoeffBoundOfLinearIndependentSectionsStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_coeff_bound_of_linearIndependent_sections : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p) (a b : ℤ) (r : ℕ) (f : Fin r → X.functionField), (∀ j, f j ∈ P.H a b) → LinearIndependent ℤ f → ∃ C : ℝ, 0 ≤ C ∧ ∀ (c : Fin r → ℤ) (R : ℝ), (∑ j, c j • f j) ∈ P.Bl a b R → ∀ j, |(c j : ℝ)| ≤ C * R := by
  first | exact @GlobalTheory.HSNef.exists_coeff_le_of_linearIndependent | exact GlobalTheory.HSNef.exists_coeff_le_of_linearIndependent | (intros; apply GlobalTheory.HSNef.exists_coeff_le_of_linearIndependent <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoeffOfMemColSpan
section
open Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SiegelSet GlobalTheory.StdPar
open scoped TensorProduct

namespace GlobalTheory.ColumnSpanCoefficients

theorem exists_coeff_of_mem_colSpan {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {n r s : ℕ} (hs : s ≤ r) (X : Matrix (Fin n) (Fin r) E) (I : Set (Fin r)) (P : Fin s → Prop)
    (hI : ∀ i ∈ I, ∃ j : Fin s, Fin.castLE hs j = i ∧ P j) {y : Fin n → AF F ⊗[F] E} (hy : y ∈ colSpan F X I) :
    ∃ a : Fin s → AF F ⊗[F] E, (∀ j, ¬ P j → a j = 0) ∧ adMat F (X.submatrix id (Fin.castLE hs)) *ᵥ a = y := by
  classical
  rw [colSpan] at hy
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, hi, rfl⟩ := hx
    obtain ⟨j, rfl, hj⟩ := hI i hi
    refine ⟨Pi.single j 1, fun j' hj' => ?_, ?_⟩
    · rw [Pi.single_apply, if_neg]
      rintro rfl
      exact hj' hj
    · rw [Matrix.mulVec_single_one]
      ext r
      rfl
  | zero => exact ⟨0, fun _ _ => rfl, Matrix.mulVec_zero _⟩
  | add x z _ _ hx hz =>
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hz
    exact ⟨a + b, fun j hj => by simp [ha j hj, hb j hj], Matrix.mulVec_add _ _ _⟩
  | smul c x _ hx =>
    obtain ⟨a, ha, rfl⟩ := hx
    exact ⟨c • a, fun j hj => by simp [ha j hj], Matrix.mulVec_smul _ _ _⟩

end GlobalTheory.ColumnSpanCoefficients
end

