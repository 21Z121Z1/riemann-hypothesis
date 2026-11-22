import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0008
import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
import Formalism.SatakeDualWeyl.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0326
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0066
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0284
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0327
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0331
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.MetaplecticRepresentation
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IteratedLineDerivMemWeylAlg
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsEqTransposeMulDiagonalMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0325
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0192
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0235
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0249
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0304

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwZ
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex

namespace GlobalTheory.EtC.KumPic

abbrev twZ (q : ℕ) : Shv ℤ := (restr (Int.castRingHom (ZMod q))).obj (tw q 1)

def dv (q : ℕ) (φ : Gm ⟶ (res ℤ (twZ q)).X 0) (U : Scheme.{0}) (v : (Γ(U, ⊤))ˣ) : Sec ((res ℤ (twZ q)).X 0) U :=
  Sec.map φ (unitSec v) - (restrMap (Int.castRingHom (ZMod q)) (tw q 1)).app U 0 (kumT q U v)

end GlobalTheory.EtC.KumPic

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistAtOfNe
section
set_option autoImplicit false

noncomputable section

open Polynomial

namespace GlobalTheory.Nef

def symMat {R : Type} [CommRing R] (m : ℕ) (A : Matrix (Fin 2) (Fin 2) R) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) R :=
  Matrix.of fun a i => ((C (A 0 1) + C (A 1 1) * X) ^ (i : ℕ) * C (A 0 0) ^ (m - i)).coeff a

theorem symMat_mulVec {R : Type} [CommRing R] (m : ℕ) (A : Matrix (Fin 2) (Fin 2) R)
    (p : Fin (m + 1) → R) :
    (symMat m A).mulVec p = fun a =>
      (∑ i : Fin (m + 1), C (p i) * (C (A 0 1) + C (A 1 1) * X) ^ (i : ℕ) * C (A 0 0) ^ (m - i)).coeff a := by
  funext a
  simp only [Matrix.mulVec, dotProduct, symMat, Matrix.of_apply, finset_sum_coeff]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_assoc, coeff_C_mul, mul_comm]

theorem symMat_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (m : ℕ)
    (A : Matrix (Fin 2) (Fin 2) R) : (symMat m A).map f = symMat m (A.map f) := by
  ext a i
  simp only [symMat, Matrix.map_apply, Matrix.of_apply]
  rw [← Polynomial.coeff_map]
  simp [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_add]

def twistAt {k F : Type} [Field k] [Field F] [Algebra k F] {n : ℕ} (v₀ : Place k F) (c : F)
    (h : Place k F → Matrix (Fin n) (Fin n) F) : Place k F → Matrix (Fin n) (Fin n) F := by
  classical
  exact fun v => if v = v₀ then c • h v else h v

theorem twistAt_self {k F : Type} [Field k] [Field F] [Algebra k F] {n : ℕ} (v₀ : Place k F) (c : F)
    (h : Place k F → Matrix (Fin n) (Fin n) F) : twistAt v₀ c h v₀ = c • h v₀ := by
  simp [twistAt]

theorem twistAt_of_ne {k F : Type} [Field k] [Field F] [Algebra k F] {n : ℕ} (v₀ : Place k F) (c : F)
    (h : Place k F → Matrix (Fin n) (Fin n) F) (v : Place k F) (hv : v ≠ v₀) :
    twistAt v₀ c h v = h v := by
  simp [twistAt, hv]

end GlobalTheory.Nef
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipLatIsOpenIsCompact
section
open GlobalTheory.LGrp GlobalTheory.BorelUMod Formalism.UG

namespace GlobalTheory.BorelUMod

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem ball_eq_image {ϖ : L} (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) (k : ℤ) :
    {x : L | Valued.v x ≤ WithZero.exp (-k)} = (fun x => ϖ ^ k * x) '' {x : L | Valued.v x ≤ 1} := by
  have h0 : ϖ ≠ 0 := fun e => by simp [e] at hϖ; exact WithZero.exp_ne_zero hϖ.symm
  have hk : Valued.v (ϖ ^ k) = WithZero.exp (-k) := by
    rw [map_zpow₀, hϖ, ← WithZero.exp_zsmul]; simp
  ext x
  constructor
  · intro hx
    refine ⟨(ϖ ^ k)⁻¹ * x, ?_, by field_simp⟩
    show Valued.v ((ϖ ^ k)⁻¹ * x) ≤ 1
    rw [map_mul, map_inv₀, hk]
    exact (inv_mul_le_one₀ (zero_lt_iff.2 WithZero.exp_ne_zero)).2 hx
  · rintro ⟨y, hy, rfl⟩
    show Valued.v (ϖ ^ k * y) ≤ WithZero.exp (-k)
    rw [map_mul, hk]
    exact (mul_le_mul' le_rfl hy).trans (by rw [mul_one])

theorem isOpen_vball {ϖ : L} (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) (k : ℤ) :
    IsOpen {x : L | Valued.v x ≤ WithZero.exp (-k)} := by
  have h0 : ϖ ≠ 0 := fun e => by simp [e] at hϖ; exact WithZero.exp_ne_zero hϖ.symm
  rw [ball_eq_image hϖ]
  exact (Homeomorph.mulLeft₀ (ϖ ^ k) (zpow_ne_zero k h0)).isOpenMap _ (Valued.isOpen_integer L)

theorem isCompact_vball [CompleteSpace L] {ϖ : L} {σ : L →+* L} {q : ℕ} (h : IsUnramInv ϖ σ q) (k : ℤ) :
    IsCompact {x : L | Valued.v x ≤ WithZero.exp (-k)} := by
  obtain ⟨-, hv, -, hϖ, -, hq, hcard⟩ := h
  haveI : (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).IsNontrivial :=
    ⟨ϖ, by rw [hϖ]; exact WithZero.coe_ne_zero, by rw [hϖ, ← WithZero.coe_one, ne_eq, WithZero.coe_inj]; decide⟩
  letI : (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).RankOne :=
    Valuation.IsRankOneDiscrete.rankOne _ (e := 2) (by norm_num)
  have hp := (Valued.integer.compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField
    (K := L)).2 ⟨(Valued.isClosed_integer L).completeSpace_coe,
      (Valued.v : Valuation L _).valuationSubring_isDiscreteValuationRing,
      Nat.finite_of_card_ne_zero (by
        refine ne_of_eq_of_ne hcard (pow_ne_zero _ (by omega)))⟩
  rw [ball_eq_image hϖ]
  exact (isCompact_iff_compactSpace.2 hp).image (continuous_const.mul continuous_id)

theorem continuous_adjJ {σ : L →+* L} (hσ : Continuous σ) (n : ℕ) :
    Continuous (adjJ σ : Matrix (Fin n) (Fin n) L → Matrix (Fin n) (Fin n) L) :=
  continuous_matrix fun i j => hσ.comp (continuous_id.matrix_elem j.rev i.rev)

theorem isInducing_GU_val {σ : L →+* L} (hσ : Continuous σ) (n : ℕ) :
    Topology.IsInducing fun g : GU σ n => (g.1.val : Matrix (Fin n) (Fin n) L) := by
  have h1 : Topology.IsInducing fun g : GU σ n => Units.embedProduct _ g.1 :=
    Units.isEmbedding_embedProduct.isInducing.comp Topology.IsInducing.subtypeVal
  refine Topology.IsInducing.of_comp (g := fun A : Matrix (Fin n) (Fin n) L => (A, MulOpposite.op (adjJ σ A)))
    (Units.continuous_val.comp continuous_subtype_val)
    (continuous_id.prodMk (MulOpposite.continuous_op.comp (continuous_adjJ hσ n))) ?_
  convert h1 using 1
  funext g
  simp only [Function.comp_apply, Units.embedProduct_apply, (mem_GU_iff_adjJ σ _).1 g.2]

end GlobalTheory.BorelUMod
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitsLocalizationDescendAway
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory

theorem units_localization_descend_away (A : Type) [CommRing A] (M : Submonoid A)
    (u : (Localization M)ˣ) :
    ∃ m ∈ M, ∃ v : (Localization.Away m)ˣ, ∀ φ : Localization.Away m →+* Localization M,
      φ.comp (algebraMap A _) = algebraMap A _ → Units.map φ.toMonoidHom v = u := by
  obtain ⟨⟨a, m₁⟩, ha⟩ := IsLocalization.mk'_surjective M (u : Localization M)
  obtain ⟨⟨b, m₂⟩, hb⟩ := IsLocalization.mk'_surjective M ((u⁻¹ : (Localization M)ˣ) : Localization M)
  simp only at ha hb
  have hprod : IsLocalization.mk' (Localization M) (a * b) (m₁ * m₂) = 1 := by
    rw [IsLocalization.mk'_mul, ha, hb]; simp
  have h1 : algebraMap A (Localization M) (a * b) = algebraMap A (Localization M) ((m₁ * m₂ : M) : A) := by
    have := IsLocalization.mk'_spec (Localization M) (a * b) (m₁ * m₂)
    rw [hprod, one_mul] at this
    exact this.symm
  obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists M (Localization M)).1 h1
  set m : A := (m₁ : A) * m₂ * c with hm
  have hmM : m ∈ M := M.mul_mem (M.mul_mem m₁.2 m₂.2) c.2
  have hc' : (c : A) * (a * b) = (c : A) * ((m₁ : A) * m₂) := by
    simpa [Submonoid.coe_mul] using hc
  let s := IsLocalization.Away.invSelf (S := Localization.Away m) m
  have hs : algebraMap A (Localization.Away m) m * s = 1 := IsLocalization.Away.mul_invSelf m
  let x : Localization.Away m := algebraMap A _ (a * (m₂ * c)) * s
  let y : Localization.Away m := algebraMap A _ (b * (m₁ * c)) * s
  have hxy : x * y = 1 := by
    have e : a * (m₂ * c) * (b * (m₁ * c)) = m * m := by
      rw [hm]; linear_combination ((m₁ : A) * m₂ * c) * hc'
    calc x * y = algebraMap A _ (a * (m₂ * c) * (b * (m₁ * c))) * s * s := by
          simp only [x, y, map_mul]; ring
      _ = (algebraMap A (Localization.Away m) m * s) * (algebraMap A (Localization.Away m) m * s) := by
          rw [e, map_mul]; ring
      _ = 1 := by rw [hs, one_mul]
  refine ⟨m, hmM, ⟨x, y, hxy, by rw [mul_comm]; exact hxy⟩, ?_⟩
  intro φ hφ
  have hφa : ∀ r : A, φ (algebraMap A _ r) = algebraMap A (Localization M) r := fun r =>
    congrArg (fun f : A →+* Localization M => f r) hφ
  apply Units.ext
  show φ x = (u : Localization M)
  have hu : (u : Localization M) * algebraMap A _ (m₁ : A) = algebraMap A _ a := by
    rw [← ha]; exact IsLocalization.mk'_spec _ _ _
  have hφs : algebraMap A (Localization M) m * φ s = 1 := by
    rw [← hφa, ← map_mul, hs, map_one]
  have hx : φ x * algebraMap A (Localization M) (m₁ : A) = algebraMap A _ a := by
    have : φ x * algebraMap A (Localization M) (m₁ : A)
        = algebraMap A (Localization M) a * (algebraMap A (Localization M) m * φ s) := by
      simp only [x, map_mul, hφa, hm]; ring
    rw [this, hφs, mul_one]
  have hunit : IsUnit (algebraMap A (Localization M) (m₁ : A)) := IsLocalization.map_units _ m₁
  exact hunit.mul_left_inj.1 (hx.trans hu.symm)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedPrincipalSeriesNoInvariant
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PrinTwo

namespace GlobalTheory.PrinTwo.NoFix

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

variable (k) in

theorem exists_unif : ∃ ϖ : kˣ, valuation k (ϖ : k) = uniformizer k := by
  obtain ⟨x, hx⟩ := valuation_surjective (uniformizer k)
  exact ⟨Units.mk0 x (by rintro rfl; exact uniformizer_ne_zero (R := k) (by simpa using hx.symm)), hx⟩

theorem isUnram_mul {χ ψ : kˣ →* ℂˣ} (h : IsUnram χ) (h' : IsUnram ψ) : IsUnram (χ * ψ) := fun x hx => by
  rw [MonoidHom.mul_apply, h x hx, h' x hx, one_mul]

theorem bchar_shift (μ₁ μ₂ : kˣ →* ℂˣ) (a d t : kˣ) :
    bchar μ₁ μ₂ (a * t) (d * t⁻¹) = bchar μ₁ μ₂ a d * ((μ₁ t * absPow k 1 t / μ₂ t : ℂˣ) : ℂ) := by
  have h1 : absPow k 1 = absPow k (1 / 2) * absPow k (1 / 2) := by rw [← absPow_add]; norm_num
  have h2 : absPow k (-1 / 2) = (absPow k (1 / 2))⁻¹ := by rw [neg_div, absPow_neg]
  simp only [bchar, h1, h2, MonoidHom.mul_apply, MonoidHom.inv_apply, map_mul, map_inv, Units.val_mul,
    Units.val_inv_eq_inv_val, Units.val_div_eq_div_val]
  have e1 : ((μ₂ t : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  have e2 : ((absPow k (1 / 2) d : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  have e3 : ((absPow k (1 / 2) t : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  field_simp

theorem val_lt_val_mul_inv {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k) (y : kˣ) :
    valuation k (y : k) < valuation k ((y * ϖ⁻¹ : kˣ) : k) := by
  rw [Units.val_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀]
  have hy0 : 0 < valuation k (y : k) := zero_lt_iff.2 (by simp)
  have hϖ0 : 0 < valuation k (ϖ : k) := zero_lt_iff.2 (by simp)
  have hu : valuation k (ϖ : k) < 1 := hϖ ▸ uniformizer_lt_one
  exact lt_mul_of_one_lt_right hy0 ((one_lt_inv₀ hϖ0).2 hu)

end GlobalTheory.PrinTwo.NoFix

namespace GlobalTheory.PrinTwo.NoFix

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem eq_zero_of_fixed_of
    (hinj : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (μ₁ μ₂ : kˣ →* ℂˣ) (f : GlobalTheory.PrinTwo.PSp μ₁ μ₂), GlobalTheory.PrinTwo.ev f 1 = 0 → (∀ x : k, GlobalTheory.PrinTwo.coord f x = 0) → f = 0)
    (hasy : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (μ₁ μ₂ : kˣ →* ℂˣ) (f : GlobalTheory.PrinTwo.PSp μ₁ μ₂), ∃ R : kˣ, ∀ x : kˣ, ValuativeRel.valuation k (R : k) < ValuativeRel.valuation k (x : k) → GlobalTheory.PrinTwo.coord f x = GlobalTheory.PrinTwo.bchar μ₁ μ₂ (-x⁻¹) x * GlobalTheory.PrinTwo.ev f 1)
    {μ₁ μ₂ : kˣ →* ℂˣ} (h₁ : IsUnram μ₁) (h₂ : IsUnram μ₂) (hne : μ₂ ≠ μ₁ * absPow k 1)
    (f : PSp μ₁ μ₂) (hf : ∀ x : k, psRep μ₁ μ₂ (nU x) f = f) : f = 0 := by
  have hc : ∀ x : k, coord f x = ev f wE := fun x => by
    rw [coord, ← ev_act, hf x]
  obtain ⟨R, hR⟩ := hasy k μ₁ μ₂ f
  obtain ⟨ϖ, hϖ⟩ := exists_unif k
  obtain ⟨x, hx⟩ : ∃ x : kˣ, x = R * ϖ⁻¹ := ⟨_, rfl⟩
  have hxR : valuation k (R : k) < valuation k (x : k) := hx ▸ val_lt_val_mul_inv hϖ R
  have hx'R : valuation k (R : k) < valuation k ((x * ϖ⁻¹ : kˣ) : k) :=
    hxR.trans (val_lt_val_mul_inv hϖ x)
  have h1 : ev f 1 = 0 := by
    by_contra h0
    apply hne
    have e := (hR x hxR).symm.trans ((hc x).trans ((hc _).symm.trans (hR _ hx'R)))
    have e2 : bchar μ₁ μ₂ (-(x * ϖ⁻¹)⁻¹) (x * ϖ⁻¹) =
        bchar μ₁ μ₂ (-x⁻¹) x * ((μ₁ ϖ * absPow k 1 ϖ / μ₂ ϖ : ℂˣ) : ℂ) := by
      rw [← bchar_shift]
      congr 1
      rw [mul_inv_rev, inv_inv, neg_mul, mul_comm]
    rw [e2, mul_assoc] at e
    have e3 := mul_left_cancel₀ (bchar_ne_zero μ₁ μ₂ _ _) e
    have e4 : ((μ₁ ϖ * absPow k 1 ϖ / μ₂ ϖ : ℂˣ) : ℂ) = 1 := by
      have := mul_right_cancel₀ h0 (e3.symm.trans (one_mul _).symm)
      exact this
    have e5 : μ₂ ϖ = (μ₁ * absPow k 1) ϖ := by
      rw [MonoidHom.mul_apply]
      exact (div_eq_one.1 (Units.ext e4)).symm
    rw [eq_unrChar h₂ hϖ, eq_unrChar (isUnram_mul h₁ (isUnram_absPow k 1)) hϖ, e5]
  refine hinj k μ₁ μ₂ f h1 fun y => ?_
  rw [hc y, ← hc x, hR x hxR, h1, mul_zero]

end GlobalTheory.PrinTwo.NoFix

theorem GlobalTheory.PrinTwo.NoFix.eq_zero_of_nU_fixed : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (μ₁ μ₂ : kˣ →* ℂˣ), GlobalTheory.SplitWeil.IsUnram μ₁ → GlobalTheory.SplitWeil.IsUnram μ₂ → μ₂ ≠ μ₁ * GlobalTheory.SmGL.absPow k 1 → ∀ f : GlobalTheory.PrinTwo.PSp μ₁ μ₂, (∀ x : k, GlobalTheory.PrinTwo.psRep μ₁ μ₂ (GlobalTheory.PrinTwo.nU x) f = f) → f = 0 :=
  fun _ _ _ _ _ _ _ h₁ h₂ hne f hf =>
    GlobalTheory.PrinTwo.NoFix.eq_zero_of_fixed_of GlobalTheory.T.principal_series_zero_of_coordinate_zero GlobalTheory.T.principal_series_coordinate_near_infinity h₁ h₂ hne f hf
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VacuumMatrixCoefficientSqStatement
section
open MeasureTheory Matrix Complex GlobalTheory.RealWeil
open scoped Real SchwartzMap ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vacuum_matrix_coefficient_sq : ∀ (l : Type) [Fintype l] [DecidableEq l] (s : Matrix (l ⊕ l) (l ⊕ l) ℝ) (P Q : Matrix l l ℂ), (∀ a b, P a b = (s (.inl a) (.inl b) : ℂ) - I * (s (.inl a) (.inr b) : ℂ)) → (∀ a b, Q a b = (s (.inr a) (.inl b) : ℂ) - I * (s (.inr a) (.inr b) : ℂ)) → P.det ≠ 0 → GlobalTheory.IsSiegel (-(Q * P⁻¹)) → ∀ c : ℂ, c ^ 2 * P.det = 1 → (∫ x : l → ℝ, c * cexp (π * I * ((fun i => (x i : ℂ)) ⬝ᵥ (-(Q * P⁻¹)) *ᵥ fun i => (x i : ℂ))) * conj (cexp (-π * ((x ⬝ᵥ x : ℝ) : ℂ)))) ^ 2 * (GlobalTheory.Published.Metaplectic.holPart s).det = (∫ x : l → ℝ, cexp (-π * ((x ⬝ᵥ x : ℝ) : ℂ)) * conj (cexp (-π * ((x ⬝ᵥ x : ℝ) : ℂ)))) ^ 2 := by
  first | exact @GlobalTheory.vacuum_coef_sq | exact GlobalTheory.vacuum_coef_sq | (intros; apply GlobalTheory.vacuum_coef_sq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VariablesUniformizerPowerLatticeBasisOpenVolume
section
open MeasureTheory ValuativeRel GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.UnfoldLoss

namespace GlobalTheory.UnfoldLoss.LatVol

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem varLat_eq_pi (G : Grid k) (ϖ : kˣ) (n : ℕ) :
    (varLat G ϖ n : Set (Vars G)) = Set.univ.pi fun _ => Set.univ.pi fun _ => cball (ϖ ^ n) := by
  ext e
  exact ⟨fun h j _ r _ => h j r, fun h j r => h j trivial r trivial⟩

theorem eventually_cball_subset {ϖ : kˣ} (hϖ : IsUnif ϖ) {U : Set k} (hU : U ∈ nhds (0 : k)) :
    ∀ᶠ n : ℕ in Filter.atTop, cball (ϖ ^ n) ⊆ U := by
  obtain ⟨γ, hγ⟩ := (IsValuativeTopology.mem_nhds_zero_iff U).mp hU
  have h1 : valuation k (ϖ : k) < 1 := hϖ ▸ uniformizer_lt_one
  haveI : MulArchimedean (ValueGroupWithZero k) := ValuativeRel.isRankLeOne_iff_mulArchimedean.mp inferInstance
  obtain ⟨N, hN⟩ := exists_pow_lt₀ h1 γ
  refine Filter.eventually_atTop.2 ⟨N, fun n hn z hz => hγ ?_⟩
  have hz' : valuation k z ≤ valuation k ((ϖ ^ n : kˣ) : k) := hz
  rw [Units.val_pow_eq_pow_val, map_pow] at hz'
  exact (hz'.trans (pow_le_pow_of_le_one zero_le h1.le hn)).trans_lt hN

theorem varLat_basis_open_vol : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
    (G : Grid k) (ν : Measure k), IsUnitVol ν → ∀ ϖ : kˣ, IsUnif ϖ →
    (∀ s ∈ nhds (0 : Vars G), ∃ n : ℕ, (varLat G ϖ n : Set (Vars G)) ⊆ s) ∧
    ∀ n : ℕ, IsOpen (varLat G ϖ n : Set (Vars G)) ∧ varsVol G ν (varLat G ϖ n : Set (Vars G)) ≠ ⊤ ∧
      (varsVol G ν).real (varLat G ϖ n : Set (Vars G)) = ((resCard k : ℝ)⁻¹) ^ (n * varCount G) := by
  intro k _ _ _ _ _ _ G ν hν ϖ hϖ
  classical
  refine ⟨fun s hs => ?_, fun n => ?_⟩
  · rw [nhds_pi, Filter.mem_pi'] at hs
    obtain ⟨I, t, ht, hts⟩ := hs
    have key : ∀ j, ∀ᶠ n : ℕ in Filter.atTop, (Set.univ.pi fun _ => cball (ϖ ^ n)) ⊆ t j := fun j => by
      have hj := ht j
      rw [nhds_pi, Filter.mem_pi'] at hj
      obtain ⟨J, u, hu, hut⟩ := hj
      filter_upwards [Filter.eventually_all.2 fun r => eventually_cball_subset hϖ (hu r)] with n hn e he
      exact hut fun r _ => hn r (he r trivial)
    obtain ⟨n, hn⟩ := (Filter.eventually_all.2 key).exists
    refine ⟨n, fun e he => hts fun j _ => hn j fun r _ => he j r⟩
  · haveI := hν.1
    haveI := secondCountable k
    have h1 : ((distribHaarChar k ϖ : NNReal) : ℝ) = (resCard k : ℝ)⁻¹ :=
      nabs_uniformiser hϖ.irreducible rfl
    have hv : varsVol G ν (varLat G ϖ n : Set (Vars G)) =
        ((distribHaarChar k ϖ ^ (n * varCount G) : NNReal) : ENNReal) := by
      rw [varLat_eq_pi, varsVol, Measure.pi_pi]
      simp only [Measure.pi_pi, measure_cball, hν.2, mul_one, Finset.prod_const, Finset.card_univ, map_pow,
        varCount, ← Nat.card_eq_fintype_card, ENNReal.coe_pow, ← pow_mul, Finset.prod_pow_eq_pow_sum, Finset.mul_sum]
    refine ⟨?_, ?_, ?_⟩
    · rw [varLat_eq_pi]
      exact isOpen_set_pi Set.finite_univ fun _ _ => isOpen_set_pi Set.finite_univ fun _ _ => isOpen_cball _
    · rw [hv]; exact ENNReal.coe_ne_top
    · rw [Measure.real, hv, ENNReal.coe_toReal, NNReal.coe_pow, h1]

end GlobalTheory.UnfoldLoss.LatVol
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WExactColimit
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC.WExactColim

abbrev altC {T : Type 1} [Category.{0} T] (X : CosimplicialObject T) (F : T ⥤ AddCommGrpCat.{1}) :
    CochainComplex AddCommGrpCat.{1} ℕ :=
  (AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{1}).obj (X ⋙ F)

abbrev altM {T : Type 1} [Category.{0} T] {X Y : CosimplicialObject T} (g : X ⟶ Y) (F : T ⥤ AddCommGrpCat.{1}) :
    altC X F ⟶ altC Y F :=
  (AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{1}).map (Functor.whiskerRight g F)

theorem altM_d {T : Type 1} [Category.{0} T] {X Y : CosimplicialObject T} (g : X ⟶ Y) (F : T ⥤ AddCommGrpCat.{1})
    (n m : ℕ) (w : (altC X F).X n) :
    (altC Y F).d n m ((altM g F).f n w) = (altM g F).f m ((altC X F).d n m w) := by
  have h := ConcreteCategory.congr_hom ((altM g F).comm n m) w
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h
  exact h

theorem altM_comp {T : Type 1} [Category.{0} T] {X Y Z : CosimplicialObject T} (g : X ⟶ Y) (h : Y ⟶ Z)
    (F : T ⥤ AddCommGrpCat.{1}) (n : ℕ) (w : (altC X F).X n) :
    (altM h F).f n ((altM g F).f n w) = (altM (g ≫ h) F).f n w := by
  show F.map (h.app _) (F.map (g.app _) w) = F.map (g.app _ ≫ h.app _) w
  rw [F.map_comp]
  rfl

theorem altM_comp' {T : Type 1} [Category.{0} T] {X Y Z : CosimplicialObject T} (g : X ⟶ Y) (h : Y ⟶ Z)
    (g' : X ⟶ Z) (e : g ≫ h = g') (F : T ⥤ AddCommGrpCat.{1}) (n : ℕ) (w : (altC X F).X n) :
    (altM h F).f n ((altM g F).f n w) = (altM g' F).f n w := by
  subst e
  exact altM_comp g h F n w

theorem exact_elt {T : Type 1} [Category.{0} T] (X : CosimplicialObject T) (F : T ⥤ AddCommGrpCat.{1}) (n : ℕ)
    (h : (altC X F).ExactAt (n + 1)) (w : (altC X F).X (n + 1)) (hw : (altC X F).d (n + 1) (n + 2) w = 0) :
    ∃ v : (altC X F).X n, (altC X F).d n (n + 1) v = w := by
  rw [HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp) (by simp), ShortComplex.ab_exact_iff] at h
  exact h w hw

theorem wExact_colimit : ∀ (T : Type 1) [Category.{0} T] (N : T ⥤ AddCommGrpCat.{1}), PreservesFilteredColimitsOfSize.{0, 0} N → ∀ (J : Type) [SmallCategory J] [IsFiltered J] (U : J ⥤ T) (X : J ⥤ CosimplicialObject T) (a : U ⋙ CosimplicialObject.const T ⟶ X) (cU : Cocone U) (cX : Cocone X) (b : (CosimplicialObject.const T).obj cU.pt ⟶ cX.pt), IsColimit cU → (∀ k : SimplexCategory, Nonempty (IsColimit (((evaluation SimplexCategory T).obj k).mapCocone cX))) → (∀ j, a.app j ≫ cX.ι.app j = (CosimplicialObject.const T).map (cU.ι.app j) ≫ b) → (∀ j, WExact N (a.app j)) → WExact N b := by
  intro T _ N hN J _ _ U X a cU cX b hU hX hab hW
  have fe := (GlobalTheory.T.preservesFilteredColimits_addCommGrp_iff_elements T N).1 hN
  have hNc : ∀ {A B C : T} (f : A ⟶ B) (g : B ⟶ C) (x : N.obj A), N.map (f ≫ g) x = N.map g (N.map f x) := by
    intros; simp
  have hab' : ∀ j (k : SimplexCategory), (a.app j).app k ≫ (cX.ι.app j).app k = cU.ι.app j ≫ b.app k := by
    intro j k
    exact NatTrans.congr_app (hab j) k
  have hnat : ∀ {j j' : J} (f : j ⟶ j') (k : SimplexCategory), (a.app j).app k ≫ (X.map f).app k = U.map f ≫ (a.app j').app k := by
    intro j j' f k
    exact (NatTrans.congr_app (a.naturality f) k).symm
  have hXι : ∀ {j j' : J} (f : j ⟶ j') (k : SimplexCategory), (X.map f).app k ≫ (cX.ι.app j').app k = (cX.ι.app j).app k := by
    intro j j' f k
    exact NatTrans.congr_app (cX.w f) k
  have feX : ∀ k : SimplexCategory, (∀ x : N.obj (cX.pt.obj k), ∃ j y, N.map ((cX.ι.app j).app k) y = x) ∧
      ∀ j (y : N.obj ((X.obj j).obj k)), N.map ((cX.ι.app j).app k) y = 0 → ∃ (j' : J) (f : j ⟶ j'), N.map ((X.map f).app k) y = 0 := by
    intro k
    exact fe J (X ⋙ (evaluation SimplexCategory T).obj k) _ (hX k).some
  have feU := fe J U cU hU
  refine ⟨?_, ?_, ?_⟩
  ·
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨j, y, rfl⟩ := feU.1 x
    have h0 : N.map ((cX.ι.app j).app (SimplexCategory.mk 0)) (N.map ((a.app j).app (SimplexCategory.mk 0)) y) = 0 := by
      rw [← hNc, hab', hNc]; simpa using hx
    obtain ⟨k, f, hf⟩ := (feX _).2 j _ h0
    rw [← hNc, hnat, hNc] at hf
    have hk := (hW k).1 (hf.trans (map_zero _).symm)
    rw [← cU.w f, hNc]
    simp only [Functor.comp_obj] at hk
    rw [hk, map_zero]
  ·
    intro y hy
    obtain ⟨j, y', rfl⟩ := (feX _).1 y
    have hδ : ∀ {Y Z : CosimplicialObject T} (g : Y ⟶ Z) (i : Fin 2),
        Y.δ (n := 0) i ≫ g.app (SimplexCategory.mk 1) = g.app (SimplexCategory.mk 0) ≫ Z.δ (n := 0) i :=
      fun g i => g.naturality _
    set d' := N.map ((X.obj j).δ (n := 0) 0) y' - N.map ((X.obj j).δ (n := 0) 1) y' with hd'
    have h1 : N.map ((cX.ι.app j).app (SimplexCategory.mk 1)) d' = 0 := by
      rw [hd', map_sub, ← hNc, ← hNc, hδ, hδ, hNc, hNc]
      exact sub_eq_zero.mpr hy
    obtain ⟨k, f, hf⟩ := (feX _).2 j _ h1
    have h2 : N.map ((X.obj k).δ (n := 0) 0) (N.map ((X.map f).app (SimplexCategory.mk 0)) y') =
        N.map ((X.obj k).δ (n := 0) 1) (N.map ((X.map f).app (SimplexCategory.mk 0)) y') := by
      rw [← sub_eq_zero, ← hNc, ← hNc, ← hδ, ← hδ, hNc, hNc, ← map_sub]
      exact hf
    obtain ⟨x, hx⟩ := (hW k).2.1 _ h2
    refine ⟨N.map (cU.ι.app k) x, ?_⟩
    rw [← hNc, ← hab', hNc]
    simp only [Functor.comp_obj] at hx
    rw [hx, ← hNc, hXι]
  · intro n
    rw [HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp) (by simp), ShortComplex.ab_exact_iff]
    intro z hz
    obtain ⟨j, z', rfl⟩ := (feX _).1 z
    have h1 : (altM (cX.ι.app j) N).f (n + 2) ((altC (X.obj j) N).d (n + 1) (n + 2) z') = 0 := by
      exact (altM_d (cX.ι.app j) N (n + 1) (n + 2) z').symm.trans hz
    obtain ⟨k, f, hf⟩ := (feX _).2 j _ h1
    have h2 : (altC (X.obj k) N).d (n + 1) (n + 2) ((altM (X.map f) N).f (n + 1) z') = 0 := by
      exact (altM_d (X.map f) N (n + 1) (n + 2) z').trans hf
    obtain ⟨v, hv⟩ := exact_elt _ N n ((hW k).2.2 n) _ h2
    refine ⟨(altM (cX.ι.app k) N).f n v, ?_⟩
    show (altC cX.pt N).d n (n + 1) ((altM (cX.ι.app k) N).f n v) = (altM (cX.ι.app j) N).f (n + 1) z'
    rw [altM_d, hv]
    exact altM_comp' (X.map f) (cX.ι.app k) (cX.ι.app j) (cX.w f) N (n + 1) z'

end GlobalTheory.EtC.WExactColim
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZmodTorsorBaseChangeTransportPointStatement
section
open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zmodTorsor_baseChange_transport_point : ∀ (A A₁ R R₁ : Type) [CommRing A] [CommRing A₁] [IsDomain A₁] [CommRing R] [Algebra A R]
    [CommRing R₁] [Algebra A₁ R₁] (j : A →+* A₁) (γ : R →+* R₁) (ρ : R →+* A) (ρ₁ : R₁ →+* A₁)
    (β : GlobalTheory.LocAcyc.GenFib A R →+* GlobalTheory.LocAcyc.GenFib A₁ R₁),
    β.comp (algebraMap R (GlobalTheory.LocAcyc.GenFib A R)) = (algebraMap R₁ (GlobalTheory.LocAcyc.GenFib A₁ R₁)).comp γ →
    ρ₁.comp (algebraMap A₁ R₁) = RingHom.id A₁ →
    ρ₁.comp γ = j.comp ρ →
    ∀ (q : ℕ), 0 < q → ∀ (DA : Type) [CommRing DA] [Algebra (GlobalTheory.LocAcyc.GenFib A R) DA]
      (actA : Multiplicative (ZMod q) →* (DA ≃ₐ[GlobalTheory.LocAcyc.GenFib A R] DA)),
    GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib A R) DA q actA →
    ∃ (DA₁ : Type) (_ : CommRing DA₁) (_ : Algebra (GlobalTheory.LocAcyc.GenFib A₁ R₁) DA₁)
      (actA₁ : Multiplicative (ZMod q) →* (DA₁ ≃ₐ[GlobalTheory.LocAcyc.GenFib A₁ R₁] DA₁)) (h : DA →+* DA₁),
      GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib A₁ R₁) DA₁ q actA₁ ∧
      h.comp (algebraMap (GlobalTheory.LocAcyc.GenFib A R) DA) = (algebraMap (GlobalTheory.LocAcyc.GenFib A₁ R₁) DA₁).comp β ∧
      ∀ σ : DA →+* FractionRing A₁,
        (σ.comp (algebraMap (GlobalTheory.LocAcyc.GenFib A R) DA)).comp (algebraMap R (GlobalTheory.LocAcyc.GenFib A R)) =
          (algebraMap A₁ (FractionRing A₁)).comp (j.comp ρ) →
        ∃ σ₁ : DA₁ →+* FractionRing A₁,
          (σ₁.comp (algebraMap (GlobalTheory.LocAcyc.GenFib A₁ R₁) DA₁)).comp (algebraMap R₁ (GlobalTheory.LocAcyc.GenFib A₁ R₁)) =
            (algebraMap A₁ (FractionRing A₁)).comp ρ₁ := by
  first | (exact @GlobalTheory.KeyOriginCut.torsor_baseChange_point) | (exact GlobalTheory.KeyOriginCut.torsor_baseChange_point) | (intros; apply GlobalTheory.KeyOriginCut.torsor_baseChange_point  <;> assumption)
end

