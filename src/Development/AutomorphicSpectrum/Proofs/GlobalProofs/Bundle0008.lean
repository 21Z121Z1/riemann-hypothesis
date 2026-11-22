import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.InstBorelGL
import GroundTheory.AutomorphicForms.Cartan
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0003
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0006
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0004
import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0007
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0035
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.MetaplecticRepresentation
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IteratedLineDerivMemWeylAlg
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.CartanDecompositionGeneralLinear
section
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ComplexConjugate ValuativeRel

namespace GlobalTheory.CompanionTheory.QL.KAK

variable {F : Type} [Field F]

def dg {n : ℕ} (a : Fin n → Fˣ) : GL (Fin n) F where
  val := Matrix.diagonal fun i => (a i : F)
  inv := Matrix.diagonal fun i => (((a i)⁻¹ : Fˣ) : F)
  val_inv := by simp [Matrix.diagonal_mul_diagonal]
  inv_val := by simp [Matrix.diagonal_mul_diagonal]

theorem dg_mem (O : Subring F) {n : ℕ} (a : Fin n → Fˣ) (h₁ : ∀ i, (a i : F) ∈ O)
    (h₂ : ∀ i, (((a i)⁻¹ : Fˣ) : F) ∈ O) : dg a ∈ GLint O n := by
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · change (Matrix.diagonal fun i => (a i : F)) i j ∈ O
    by_cases hij : i = j
    · subst hij; simpa using h₁ i
    · simp [Matrix.diagonal_apply_ne _ hij, O.zero_mem]
  · change (Matrix.diagonal fun i => (((a i)⁻¹ : Fˣ) : F)) i j ∈ O
    by_cases hij : i = j
    · subst hij; simpa using h₂ i
    · simp [Matrix.diagonal_apply_ne _ hij, O.zero_mem]

variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem integralGL_le (n : ℕ) :
    GroundTheory.Automorphic.GLnLocal.integralGL F n ≤ GLint 𝒪[F] n := fun _ hg =>
  (GroundTheory.Automorphic.GLnLocal.mem_integralGL_iff F n).1 hg

theorem irreducible_pi {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ} (h : LF 𝒪[F] ϖ nrm q)
    (hϖ : ϖ ∈ 𝒪[F]) : Irreducible (⟨ϖ, hϖ⟩ : 𝒪[F]) := by
  rw [IsDiscreteValuationRing.irreducible_iff_uniformizer]
  ext x
  have hu : IsUnit x ↔ ValuativeRel.valuation F (x : F) = 1 :=
    (Valuation.integer.integers (ValuativeRel.valuation F)).isUnit_iff_valuation_eq_one
  have hle : ValuativeRel.valuation F (x : F) ≤ 1 := x.2
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, hu, Ideal.mem_span_singleton']
  constructor
  · intro hx
    obtain ⟨o, ho, e⟩ := (h.lt_one (x : F)).1 (lt_of_le_of_ne hle hx)
    exact ⟨⟨o, ho⟩, Subtype.ext (by simp [e, mul_comm])⟩
  · rintro ⟨a, rfl⟩
    exact ((h.lt_one _).2 ⟨a, a.2, by simp [mul_comm]⟩).ne

theorem cartan {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ} (h : LF O ϖ nrm q)
    (n : ℕ) (g : GL (Fin n) F) :
    ∃ k₁ ∈ GLint O n, ∃ k₂ ∈ GLint O n, ∃ (e : Fin n → ℤ) (d : GL (Fin n) F),
      (d : Matrix (Fin n) (Fin n) F) = Matrix.diagonal (fun i => ϖ ^ e i) ∧ g = k₁ * d * k₂ := by
  obtain rfl := h.O_eq
  have hv : ValuativeRel.valuation F ϖ < 1 := (h.lt_one ϖ).2 ⟨1, Subring.one_mem _, by simp⟩
  have hϖ : ϖ ∈ 𝒪[F] := (Valuation.mem_integer_iff _ _).2 hv.le
  obtain ⟨c, hc⟩ := IsDiscreteValuationRing.associated_of_irreducible 𝒪[F]
    (GroundTheory.Automorphic.GLnLocal.irreducible_uniformizer F) (irreducible_pi h hϖ)

  have hcF : (GroundTheory.Automorphic.GLnLocal.uniformizer F : F) * ((c : 𝒪[F]) : F) = ϖ :=
    congrArg Subtype.val hc
  let cF : Fˣ := Units.map (𝒪[F]).subtype.toMonoidHom c
  have hcF' : (cF : F) = ((c : 𝒪[F]) : F) := rfl
  have hc₁ : ∀ z : ℤ, ((cF ^ z : Fˣ) : F) ∈ 𝒪[F] := fun z => by
    have : cF ^ z = Units.map (𝒪[F]).subtype.toMonoidHom (c ^ z) := by simp [cF]
    rw [this]; exact ((c ^ z : (𝒪[F])ˣ) : 𝒪[F]).2
  have hϖ0 : ϖ ≠ 0 := h.ne
  obtain ⟨μ, -, k₁, hk₁, k₂, hk₂, rfl⟩ := GroundTheory.Automorphic.Cartan.exists_eq_mul_diagPow_mul F n g
  let wu : Fˣ := Units.mk0 ϖ hϖ0
  refine ⟨k₁, integralGL_le n hk₁, dg (fun i => (cF ^ (-μ i) : Fˣ)) * k₂,
    (GLint 𝒪[F] n).mul_mem (dg_mem _ _ (fun i => hc₁ _) (fun i => ?_)) (integralGL_le n hk₂),
    μ, dg (fun i => wu ^ μ i), ?_, ?_⟩
  · rw [← _root_.zpow_neg]; exact hc₁ _
  · change (Matrix.diagonal fun i => ((wu ^ μ i : Fˣ) : F)) = _
    congr 1; funext i; simp [wu]
  · have hd : GroundTheory.Automorphic.Cartan.diagPow F n μ =
        dg (fun i => wu ^ μ i) * dg (fun i => (cF ^ (-μ i) : Fˣ)) := by
      apply Units.ext
      rw [Units.val_mul]
      change (Matrix.diagonal fun i => (GroundTheory.Automorphic.GLnLocal.uniformizer F : F) ^ μ i) =
        (Matrix.diagonal fun i => ((wu ^ μ i : Fˣ) : F)) *
          (Matrix.diagonal fun i => ((cF ^ (-μ i) : Fˣ) : F))
      rw [Matrix.diagonal_mul_diagonal]
      congr 1; funext i
      have hcu : ((c : 𝒪[F]) : F) ≠ 0 := by rw [← hcF']; exact cF.ne_zero
      have : ((c : 𝒪[F]) : F) ^ μ i ≠ 0 := zpow_ne_zero _ hcu
      simp only [_root_.zpow_neg, Units.val_inv_eq_inv_val, Units.val_zpow_eq_zpow_val, wu,
        Units.val_mk0, hcF', ← hcF, mul_zpow]
      field_simp
    rw [hd]; simp only [mul_assoc]

end GlobalTheory.CompanionTheory.QL.KAK
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.DiagonalConjugateCongruenceBox
section
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL GlobalTheory.CompanionTheory.QL.QIndex
open scoped ComplexConjugate ValuativeRel

namespace GlobalTheory.CompanionTheory.QL.QIndex.ConjLe

section Field

variable {F : Type} [Field F]

theorem det_eq_one_add (O : Subring F) {c : F} (hc : c ∈ O) {n : ℕ}
    {g : Matrix (Fin n) (Fin n) F} (h : Lvl O c (g - 1)) : ∃ o ∈ O, g.det = 1 + c * o := by
  classical
  have hint : IsInt O g := fun i j => by
    obtain ⟨o, ho, e⟩ := h i j
    have e' : g i j = (1 : Matrix (Fin n) (Fin n) F) i j + c * o := by
      rw [← e]; simp
    rw [e']
    refine O.add_mem ?_ (O.mul_mem hc ho)
    by_cases hij : i = j
    · subst hij; rw [Matrix.one_apply_eq]; exact O.one_mem
    · rw [Matrix.one_apply_ne hij]; exact O.zero_mem
  let M : Matrix (Fin n) (Fin n) O := fun i j => ⟨g i j, hint i j⟩
  have hM : O.subtype.mapMatrix M = g := by
    ext i j; rfl
  let c' : O := ⟨c, hc⟩
  let π := Ideal.Quotient.mk (Ideal.span {c'})
  have hc0 : π c' = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self c')
  have hπ : π.mapMatrix M = 1 := by
    ext i j
    obtain ⟨o, ho, e⟩ := h i j
    have e' : M i j = (1 : Matrix (Fin n) (Fin n) O) i j + c' * ⟨o, ho⟩ := by
      apply Subtype.ext
      have e2 : g i j = (1 : Matrix (Fin n) (Fin n) F) i j + c * o := by
        rw [← e]; simp
      by_cases hij : i = j
      · subst hij; rw [Matrix.one_apply_eq] at e2 ⊢; simpa [M, c'] using e2
      · simpa [M, c', hij] using e2
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, e', map_add, map_mul, hc0, zero_mul, add_zero]
    by_cases hij : i = j
    · subst hij; rw [Matrix.one_apply_eq, Matrix.one_apply_eq, map_one]
    · simp [hij]
  have hdet : π (M.det - 1) = 0 := by
    rw [map_sub, RingHom.map_det, hπ, Matrix.det_one, map_one, sub_self]
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq_zero_iff_mem.1 hdet)
  refine ⟨a, a.2, ?_⟩
  have h1 : (O.subtype M.det) = g.det := by
    rw [RingHom.map_det, hM]
  have h2 : (a : F) * c = (M.det : F) - 1 := by
    simpa [c'] using congrArg Subtype.val ha
  have h3 : (M.det : F) = g.det := h1
  rw [← h3]
  linear_combination -h2

theorem diag_inv {n : ℕ} (g : GL (Fin n) F) {dd : Fin n → F}
    (hD : (g : Matrix (Fin n) (Fin n) F) = diagonal dd) :
    (∀ a, dd a ≠ 0) ∧
      ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = diagonal fun a => (dd a)⁻¹ := by
  have hmul : (g : Matrix (Fin n) (Fin n) F) * ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = 1 := by
    rw [← Units.val_mul]; simp
  have hne : ∀ a, dd a ≠ 0 := fun a => by
    have h1 := congrFun (congrFun hmul a) a
    rw [hD, diagonal_mul, one_apply_eq] at h1
    exact left_ne_zero_of_mul_eq_one h1
  refine ⟨hne, ?_⟩
  have h2 : (diagonal fun a => (dd a)⁻¹) * (g : Matrix (Fin n) (Fin n) F) = 1 := by
    rw [hD, diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext a
    exact inv_mul_cancel₀ (hne a)
  calc ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)
      = ((diagonal fun a => (dd a)⁻¹) * (g : Matrix (Fin n) (Fin n) F)) *
          ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by rw [h2, Matrix.one_mul]
    _ = diagonal fun a => (dd a)⁻¹ := by rw [Matrix.mul_assoc, hmul, Matrix.mul_one]

theorem conj_entry {n : ℕ} (g p : GL (Fin n) F) {dd : Fin n → F}
    (hD : (g : Matrix (Fin n) (Fin n) F) = diagonal dd) (a b : Fin n) :
    (((g * p * g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) - 1) a b =
      dd a * ((p : Matrix (Fin n) (Fin n) F) - 1) a b * (dd b)⁻¹ := by
  obtain ⟨-, hE⟩ := diag_inv g hD
  have hmul : (g : Matrix (Fin n) (Fin n) F) * ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = 1 := by
    rw [← Units.val_mul]; simp
  have h1 : ((g * p * g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) - 1 =
      (g : Matrix (Fin n) (Fin n) F) * ((p : Matrix (Fin n) (Fin n) F) - 1) *
        ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by
    rw [Units.val_mul, Units.val_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hmul]
  rw [h1, hE, Matrix.mul_diagonal, hD, diagonal_mul]

end Field

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}

theorem mem_congGL_of_lvl (hLF : LF O ϖ nrm q) {n T : ℕ} (hT : 1 ≤ T) (g : GL (Fin n) F)
    (h : Lvl O (ϖ ^ T) ((g : Matrix (Fin n) (Fin n) F) - 1)) : g ∈ congGL O (ϖ ^ T) n := by
  obtain ⟨-, hpi, hle, hlt, -, hult, -⟩ := GlobalTheory.T.localField_uniformizer_norm_properties hLF
  have hc : ϖ ^ T ∈ O := O.pow_mem hpi T
  refine ⟨(GlobalTheory.CompanionTheory.QLDet.mem_GLint_iff hLF n g).2 ⟨fun i j => ?_, ?_⟩, h⟩
  · obtain ⟨o, ho, e⟩ := h i j
    have e' : (g : Matrix (Fin n) (Fin n) F) i j = (1 : Matrix (Fin n) (Fin n) F) i j + ϖ ^ T * o := by
      rw [← e]; simp
    rw [e']
    refine O.add_mem ?_ (O.mul_mem hc ho)
    by_cases hij : i = j
    · subst hij; rw [Matrix.one_apply_eq]; exact O.one_mem
    · rw [Matrix.one_apply_ne hij]; exact O.zero_mem
  · obtain ⟨o, ho, e⟩ := det_eq_one_add O hc h
    rw [e]
    have hy : nrm (ϖ ^ T * o) < 1 := by
      refine (hlt _).2 ⟨ϖ ^ (T - 1) * o, O.mul_mem (O.pow_mem hpi _) ho, ?_⟩
      obtain ⟨k, rfl⟩ : ∃ k, T = k + 1 := ⟨T - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      ring
    apply le_antisymm
    · refine (hult _ _).trans (max_le ?_ hy.le)
      simp
    · by_contra hcon
      have hcon' : nrm (1 + ϖ ^ T * o) < 1 := not_le.1 hcon
      have h1 := hult (1 + ϖ ^ T * o) (-(ϖ ^ T * o))
      rw [add_neg_cancel_right, map_one, map_neg_eq_map] at h1
      exact absurd h1 (not_le.2 (max_lt hcon' hy))

theorem main : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}, LF O ϖ nrm q → ∀ (n : ℕ) (β : Fin n → ℕ) (Q : Subgroup (GL (Fin n) F)), (∀ g, g ∈ Q ↔ (g : Matrix (Fin n) (Fin n) F).BlockTriangular β) → ∀ T : ℕ, 1 ≤ T → ∀ d : Q, ((d : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).IsDiag → (∀ a b, ϖ ^ T * (((d : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) a a * (((d : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) b b)⁻¹) ∈ O) → conjSub ((congGL O (ϖ ^ (2 * T)) n).subgroupOf Q) d ≤ (congGL O (ϖ ^ T) n).subgroupOf Q ∧ ∀ p ∈ (congGL O (ϖ ^ T) n).subgroupOf Q, (p ∈ conjSub ((congGL O (ϖ ^ (2 * T)) n).subgroupOf Q) d ↔ ((p : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) - 1 ∈ boxAdd O β (lev ϖ T fun a => ((d : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) a a)) := by
  intro F _ _ _ _ O ϖ nrm q hLF n β Q hQ T hT d hdiag hd
  have hD : ((d : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      diagonal fun a => ((d : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) a a :=
    hdiag.diagonal_diag.symm
  obtain ⟨hne, -⟩ := diag_inv (d : GL (Fin n) F) hD
  have hent := fun (p : GL (Fin n) F) => conj_entry (d : GL (Fin n) F) p hD
  have hconj : ∀ p : Q, ((d * p * d⁻¹ : Q) : GL (Fin n) F) =
      (d : GL (Fin n) F) * (p : GL (Fin n) F) * (d : GL (Fin n) F)⁻¹ := fun p => rfl
  have h2T : 1 ≤ 2 * T := by omega
  refine ⟨fun p hp => ?_, fun p _ => ?_⟩
  · rw [mem_conjSub, Subgroup.mem_subgroupOf, hconj] at hp
    rw [Subgroup.mem_subgroupOf]
    refine mem_congGL_of_lvl hLF hT _ fun a b => ?_
    obtain ⟨o, ho, e⟩ := hp.2 a b
    rw [hent] at e
    refine ⟨o * (ϖ ^ T * (((d : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) b b *
      (((d : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) a a)⁻¹)), O.mul_mem ho (hd b a), ?_⟩
    have hna := hne a
    have hnb := hne b
    field_simp at e ⊢
    linear_combination e
  · rw [mem_conjSub, Subgroup.mem_subgroupOf, hconj]
    constructor
    · intro hp
      refine ⟨((hQ _).1 p.2).sub (blockTriangular_one), fun a b => ?_⟩
      obtain ⟨o, ho, e⟩ := hp.2 a b
      rw [hent] at e
      refine ⟨o, ho, ?_⟩
      have hna := hne a
      have hnb := hne b
      simp only [lev]
      field_simp at e ⊢
      linear_combination e
    · rintro ⟨-, hx⟩
      refine mem_congGL_of_lvl hLF h2T _ fun a b => ?_
      obtain ⟨o, ho, e⟩ := hx a b
      refine ⟨o, ho, ?_⟩
      rw [hent, e]
      have hna := hne a
      have hnb := hne b
      simp only [lev]
      field_simp

end GlobalTheory.CompanionTheory.QL.QIndex.ConjLe
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.DifferentDvdRamifiedPrimePower
section
open NumberField IsDedekindDomain

namespace GlobalTheory.CompanionTheory.Glob

theorem exists_prime_mem_of_natCast_mem {R : Type*} [CommRing R] (P : Ideal R) [hP : P.IsPrime]
    (t : ℕ) (ht : t ≠ 0) (htP : (t : R) ∈ P) : ∃ p : ℕ, p.Prime ∧ p ∣ t ∧ (p : R) ∈ P :=
  _root_.UpperTheory.Reformulated.B.DYdc5.main P t ht htP

theorem prime_pow_dvd_span_of_dvd_differentIdeal (E : Type) [Field E] [NumberField E] (t : ℕ)
    (ht : t ≠ 0)
    (h : ∀ P : Ideal (𝓞 E), P.IsPrime → P ≠ ⊥ → P ∣ differentIdeal ℤ (𝓞 E) → (t : 𝓞 E) ∈ P)
    (P : Ideal (𝓞 E)) (hPp : Prime P) (i : ℕ) (hi : P ^ i ∣ differentIdeal ℤ (𝓞 E)) :
    P ^ i ∣ Ideal.span {((t : 𝓞 E)) ^ (Module.finrank ℚ E)} := by
  rcases Nat.eq_zero_or_pos i with rfl | hipos
  · simp
  have hPD : P ∣ differentIdeal ℤ (𝓞 E) := (dvd_pow_self P hipos.ne').trans hi
  have hP0 : P ≠ ⊥ := hPp.ne_zero
  haveI hPprime : P.IsPrime := Ideal.isPrime_of_prime hPp
  obtain ⟨p, hp, hpt, hpP⟩ := exists_prime_mem_of_natCast_mem P t ht (h P hPprime hP0 hPD)
  have hp0 : ((p : 𝓞 E)) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have hS0 : Ideal.span {((p : 𝓞 E)) ^ (Module.finrank ℚ E)} ≠ 0 := by
    intro h0
    have := Ideal.span_singleton_eq_bot.1 h0
    exact pow_ne_zero _ hp0 this
  obtain ⟨J, hJ, hnd⟩ :=
    (FiniteMultiplicity.of_not_isUnit hPp.not_unit hS0).exists_eq_pow_mul_and_not_dvd
  have hnot := GlobalTheory.T.prime_power_not_dvd_different E P J p _ hp hpP hnd hJ
  have hlt : i < multiplicity P (Ideal.span {((p : 𝓞 E)) ^ (Module.finrank ℚ E)}) := by
    by_contra hle
    exact hnot ((pow_dvd_pow P (not_lt.1 hle)).trans hi)
  have h1 : P ^ i ∣ Ideal.span {((p : 𝓞 E)) ^ (Module.finrank ℚ E)} := by
    exact ((pow_dvd_pow P hlt.le).mul_right J).trans (dvd_of_eq hJ.symm)
  refine h1.trans ?_
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_span_singleton]
  exact pow_dvd_pow_of_dvd (Nat.cast_dvd_cast hpt) _

theorem differentIdeal_dvd_span_pow : ∀ (E : Type) [Field E] [NumberField E] (t : ℕ), t ≠ 0 →
    (∀ P : Ideal (𝓞 E), P.IsPrime → P ≠ ⊥ → P ∣ differentIdeal ℤ (𝓞 E) → (t : 𝓞 E) ∈ P) →
    differentIdeal ℤ (𝓞 E) ∣ Ideal.span {((t : 𝓞 E)) ^ (Module.finrank ℚ E)} := by
  intro E _ _ t ht h
  have hD : differentIdeal ℤ (𝓞 E) ≠ 0 := differentIdeal_ne_bot
  have key : ∀ I : Ideal (𝓞 E), I ≠ 0 → I ∣ differentIdeal ℤ (𝓞 E) →
      I ∣ Ideal.span {((t : 𝓞 E)) ^ (Module.finrank ℚ E)} := by
    intro I
    induction I using UniqueFactorizationMonoid.induction_on_coprime with
    | h0 => exact fun h0 => absurd rfl h0
    | h1 hu => exact fun _ _ => hu.dvd
    | hpr i hq =>
      exact fun _ hd => prime_pow_dvd_span_of_dvd_differentIdeal E t ht h _ hq i hd
    | hcp hxy hx hy =>
      intro h0 hd
      exact hxy.mul_dvd (hx (left_ne_zero_of_mul h0) ((dvd_mul_right _ _).trans hd))
        (hy (right_ne_zero_of_mul h0) ((dvd_mul_left _ _).trans hd))
  exact key _ hD dvd_rfl

end GlobalTheory.CompanionTheory.Glob
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.DigammaLogBoundLeftRegionStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.digamma_log_bound_left_region : ∃ C : ℝ, 0 < C ∧ ∀ w : ℂ, w.re ≤ 1 / 4 → (1 / 2 ≤ |w.im| ∨ ∃ k : ℤ, w.re = (k : ℝ) / 2 + 1 / 4) → ‖Complex.digamma w‖ ≤ C * Real.log (‖w‖ + 2) := by
  first | exact @GlobalTheory.CompanionTheory.DigammaLeft.norm_digamma_le_left | exact GlobalTheory.CompanionTheory.DigammaLeft.norm_digamma_le_left | (intros; apply GlobalTheory.CompanionTheory.DigammaLeft.norm_digamma_le_left <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.HasDerivAtLpOfDominated
section
noncomputable section

open MeasureTheory Complex Matrix GlobalTheory.RealWeil GlobalTheory.CompanionTheory.Hypotheses₂ Filter Topology
open scoped Real SchwartzMap ComplexConjugate

namespace GlobalTheory.CompanionTheory.Hypotheses₂.GaussCurve

theorem lp_two_norm_sq {E : Type*} [MeasurableSpace E] {μ : Measure E} (f : Lp ℂ 2 μ) :
    ‖f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  rw [@norm_sq_eq_re_inner ℂ, MeasureTheory.L2.inner_def,
    ← integral_re (MeasureTheory.L2.integrable_inner (𝕜 := ℂ) f f)]
  simp_rw [inner_self_eq_norm_sq]

theorem hasDerivAt_Lp_of_dominated {E : Type*} [MeasurableSpace E] {μ : Measure E}
    (F : ℝ → Lp ℂ 2 μ) (G : Lp ℂ 2 μ) (f f' : ℝ → E → ℂ) (b : E → ℝ) (t₀ δ : ℝ) (hδ : 0 < δ)
    (hF : ∀ t, F t =ᵐ[μ] f t) (hG : G =ᵐ[μ] f' t₀) (hb : MemLp b 2 μ)
    (hd : ∀ x, ∀ t ∈ Metric.ball t₀ δ, HasDerivAt (fun s => f s x) (f' t x) t)
    (hbd : ∀ x, ∀ t ∈ Metric.ball t₀ δ, ‖f' t x‖ ≤ b x) :
    HasDerivAt F G t₀ := by
  rw [hasDerivAt_iff_tendsto_slope_zero]
  set d : ℝ → E → ℂ := fun s x => (s⁻¹ : ℝ) • (f (t₀ + s) x - f t₀ x) - f' t₀ x with hd_def
  have hD : ∀ s : ℝ, ((s⁻¹ • (F (t₀ + s) - F t₀) - G : Lp ℂ 2 μ) : E → ℂ) =ᵐ[μ] d s := by
    intro s
    filter_upwards [Lp.coeFn_sub (s⁻¹ • (F (t₀ + s) - F t₀)) G,
      Lp.coeFn_smul s⁻¹ (F (t₀ + s) - F t₀), Lp.coeFn_sub (F (t₀ + s)) (F t₀),
      hF (t₀ + s), hF t₀, hG] with x h1 h2 h3 h4 h5 h6
    simp only [hd_def, h1, Pi.sub_apply, h2, Pi.smul_apply, h3, h4, h5, h6]
  have hsq : ∀ s : ℝ, ‖s⁻¹ • (F (t₀ + s) - F t₀) - G‖ ^ 2 = ∫ x, ‖d s x‖ ^ 2 ∂μ := by
    intro s
    rw [lp_two_norm_sq]
    exact integral_congr_ae ((hD s).mono fun x hx => by simp only [hx])
  have hlim : Tendsto (fun s : ℝ => ∫ x, ‖d s x‖ ^ 2 ∂μ) (𝓝[≠] 0) (𝓝 (∫ _x, (0 : ℝ) ∂μ)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun x => (2 * b x) ^ 2) ?_ ?_ ?_ ?_
    · exact Eventually.of_forall fun s =>
        (((Lp.aestronglyMeasurable _).congr (hD s)).norm.pow 2)
    · have hs : ∀ᶠ s : ℝ in 𝓝[≠] 0, s ≠ 0 ∧ |s| < δ := by
        have h1 : ∀ᶠ s : ℝ in 𝓝[≠] 0, s ≠ 0 := eventually_mem_nhdsWithin
        have h2 : ∀ᶠ s : ℝ in 𝓝[≠] 0, |s| < δ := by
          refine nhdsWithin_le_nhds ?_
          have : ∀ᶠ s : ℝ in 𝓝 0, s ∈ Metric.ball (0 : ℝ) δ := Metric.ball_mem_nhds _ hδ
          exact this.mono fun s hs => by simpa using hs
        exact h1.and h2
      refine hs.mono fun s hs => Eventually.of_forall fun x => ?_
      obtain ⟨hs0, hsδ⟩ := hs
      have hmem : t₀ + s ∈ Metric.ball t₀ δ := by simpa [Metric.mem_ball, dist_eq_norm] using hsδ
      have h0 : t₀ ∈ Metric.ball t₀ δ := Metric.mem_ball_self hδ
      have hmv : ‖f (t₀ + s) x - f t₀ x‖ ≤ b x * ‖(t₀ + s) - t₀‖ :=
        (convex_ball t₀ δ).norm_image_sub_le_of_norm_hasDerivWithin_le
          (f := fun r => f r x) (f' := fun r => f' r x)
          (fun r hr => (hd x r hr).hasDerivWithinAt) (fun r hr => hbd x r hr) h0 hmem
      have hb0 : 0 ≤ b x := (norm_nonneg _).trans (hbd x t₀ h0)
      have hq : ‖(s⁻¹ : ℝ) • (f (t₀ + s) x - f t₀ x)‖ ≤ b x := by
        rw [norm_smul, norm_inv]
        have hn : 0 < ‖s‖ := norm_pos_iff.2 hs0
        rw [add_sub_cancel_left] at hmv
        rw [inv_mul_le_iff₀ hn]
        linarith [mul_comm (b x) ‖s‖]
      have hdn : ‖d s x‖ ≤ 2 * b x := by
        calc ‖d s x‖ ≤ ‖(s⁻¹ : ℝ) • (f (t₀ + s) x - f t₀ x)‖ + ‖f' t₀ x‖ := norm_sub_le _ _
          _ ≤ 2 * b x := by linarith [hbd x t₀ h0]
      rw [Real.norm_of_nonneg (by positivity)]
      exact pow_le_pow_left₀ (norm_nonneg _) hdn 2
    · have := (memLp_two_iff_integrable_sq hb.1).1 hb
      simpa [mul_pow] using this.const_mul (2 ^ 2)
    · refine Eventually.of_forall fun x => ?_
      have h1 := hasDerivAt_iff_tendsto_slope_zero.1 (hd x t₀ (Metric.mem_ball_self hδ))
      have h2 : Tendsto (fun s : ℝ => d s x) (𝓝[≠] 0) (𝓝 (f' t₀ x - f' t₀ x)) :=
        h1.sub tendsto_const_nhds
      have h3 := (h2.norm).pow 2
      simpa using h3
  have hlim0 : Tendsto (fun s : ℝ => ‖s⁻¹ • (F (t₀ + s) - F t₀) - G‖ ^ 2) (𝓝[≠] 0) (𝓝 0) := by
    simp only [hsq]
    simpa using hlim
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h4 := (Real.continuous_sqrt.tendsto 0).comp hlim0
  simpa [Function.comp_def, Real.sqrt_sq (norm_nonneg _)] using h4

variable {l : Type} [Fintype l]

def qf (Z : Matrix l l ℂ) (x : EuclideanSpace ℝ l) : ℂ :=
  ∑ j, ∑ k, Z j k * (x j : ℂ) * (x k : ℂ)

end GlobalTheory.CompanionTheory.Hypotheses₂.GaussCurve

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.KaehlerBasisOnLocalizationAwayStatement
section
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R ReciprocityTheory.ChartRestriction.G.Geo.ResK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kaehler_basis_on_localization_away : ∀ (K : Type) [Field K] (Y : Scheme.{0}) (g : Y ⟶ Sp K) (U : Y.affineOpens) (s : Γ(Y, U.1)) {n : ℕ} (x : Fin n → Γ(Y, U.1)), (letI := secAlgebra g U.1; ∀ (B : Type) [CommRing B] [Algebra Γ(Y, U.1) B] [Algebra K B] [IsScalarTower K Γ(Y, U.1) B] [IsLocalization.Away s B], LinearIndependent B (fun i => KaehlerDifferential.D K B (algebraMap Γ(Y, U.1) B (x i))) ∧ Submodule.span B (Set.range fun i => KaehlerDifferential.D K B (algebraMap Γ(Y, U.1) B (x i))) = ⊤) → IsCoords g (Y.basicOpen s) (fun i => Y.presheaf.map (homOfLE (Y.basicOpen_le s)).op (x i)) := by
  first | exact @GlobalTheory.CompanionTheory.Glob.ResKCoords.isCoords_basicOpen_of_away | exact GlobalTheory.CompanionTheory.Glob.ResKCoords.isCoords_basicOpen_of_away | (intros; apply GlobalTheory.CompanionTheory.Glob.ResKCoords.isCoords_basicOpen_of_away <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.KaehlerBasisSpreadsToNeighbourhoodStatement
section
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R ReciprocityTheory.ChartRestriction.G.Geo.ResK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kaehler_basis_spreads_to_neighbourhood : ∀ (K A : Type) [Field K] [CommRing A] [Algebra K A] [Algebra.FinitePresentation K A] (P : Ideal A) [P.IsPrime] {n : ℕ} (x : Fin n → A), (LinearIndependent (Localization.AtPrime P) (fun i => KaehlerDifferential.D K (Localization.AtPrime P) (algebraMap A _ (x i))) ∧ Submodule.span (Localization.AtPrime P) (Set.range fun i => KaehlerDifferential.D K (Localization.AtPrime P) (algebraMap A _ (x i))) = ⊤) → ∃ s ∉ P, ∀ (B : Type) [CommRing B] [Algebra A B] [Algebra K B] [IsScalarTower K A B] [IsLocalization.Away s B], LinearIndependent B (fun i => KaehlerDifferential.D K B (algebraMap A B (x i))) ∧ Submodule.span B (Set.range fun i => KaehlerDifferential.D K B (algebraMap A B (x i))) = ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.KaehlerSpread.spread | exact GlobalTheory.CompanionTheory.KaehlerSpread.spread | (intros; apply GlobalTheory.CompanionTheory.KaehlerSpread.spread <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.MemIntegralGLIffIntegralUnitDetStatement
section
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ComplexConjugate ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_integralGL_iff_integral_unit_det : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}, LF O ϖ nrm q → ∀ (n : ℕ) (g : GL (Fin n) F), g ∈ GLint O n ↔ (IsInt O (g : Matrix (Fin n) (Fin n) F) ∧ nrm (g : Matrix (Fin n) (Fin n) F).det = 1) := by
  first | exact @GlobalTheory.CompanionTheory.QLDet.mem_GLint_iff | exact GlobalTheory.CompanionTheory.QLDet.mem_GLint_iff | (intros; apply GlobalTheory.CompanionTheory.QLDet.mem_GLint_iff <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.RegularSequenceGermsRegularLocalStatement
section
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R ReciprocityTheory.ChartRestriction.G.Geo.ResK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regular_sequence_germs_regular_local : ∀ (Y : Scheme.{0}) (U : Y.affineOpens) (y : Y) (hy : y ∈ U.1), IsRegularLocalRing (Y.presheaf.stalk y) → ∀ (m : ℕ) (f : Fin m → Γ(Y, U.1)), FinalTheorems.Rsp (Y.presheaf.stalk y) m (fun i => Y.presheaf.germ U.1 y hy (f i)) → IsRegularLocalRing (Localization.AtPrime (U.2.primeIdealOf ⟨y, hy⟩).asIdeal) ∧ FinalTheorems.Rsp (Localization.AtPrime (U.2.primeIdealOf ⟨y, hy⟩).asIdeal) m (fun i => algebraMap Γ(Y, U.1) _ (f i)) ∧ ∀ s : Γ(Y, U.1), y ∈ Y.basicOpen s ↔ s ∉ (U.2.primeIdealOf ⟨y, hy⟩).asIdeal := by
  first | exact @GlobalTheory.CompanionTheory.ResKCoords.stalk_to_localization | exact GlobalTheory.CompanionTheory.ResKCoords.stalk_to_localization | (intros; apply GlobalTheory.CompanionTheory.ResKCoords.stalk_to_localization <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.SmoothLocalRingFreeDifferentialsStatement
section
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R ReciprocityTheory.ChartRestriction.G.Geo.ResK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_local_ring_free_differentials : ∀ (K : Type) [Field K] (D : ℕ) (Y : Scheme.{0}) (g : Y ⟶ Sp K), SmoothOfRelativeDimension D g → ∀ (U : Y.affineOpens) (P : Ideal Γ(Y, U.1)) [P.IsPrime], letI := secAlgebra g U.1; Algebra.FinitePresentation K Γ(Y, U.1) ∧ Module.Free (Localization.AtPrime P) Ω[Localization.AtPrime P⁄K] ∧ Module.Finite (Localization.AtPrime P) Ω[Localization.AtPrime P⁄K] ∧ Module.finrank (Localization.AtPrime P) Ω[Localization.AtPrime P⁄K] = D := by
  first | exact @GlobalTheory.CompanionTheory.ResKCoords.finitePresentation_and_kaehler_atPrime | exact GlobalTheory.CompanionTheory.ResKCoords.finitePresentation_and_kaehler_atPrime | (intros; apply GlobalTheory.CompanionTheory.ResKCoords.finitePresentation_and_kaehler_atPrime <;> assumption)
end

