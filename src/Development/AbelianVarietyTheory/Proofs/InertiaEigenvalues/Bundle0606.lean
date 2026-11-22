import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0341
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0358
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0592
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0595
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0430
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0476
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0471
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LineOfSingleJump
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0591
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0483
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWildInertiaCyclotomicElement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0588
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0451
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0396
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0015
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0458
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0457
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0565
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0596
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeEqFiltrationSumAtLevel
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0003

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RamificationJumpSumPowGrowth
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem jumpSum_pow_growth :
    ∀ (K L : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L] [IsGalois K L] (p E : ℕ) (A B C : Subgroup (L ≃ₐ[K] L)), A ≤ lowerRamificationGroup K L 0 → OrdIs L p E → (∀ σ ∈ A, ∀ τ ∈ A, σ * τ * σ⁻¹ * τ⁻¹ ∈ C) → (∀ σ ∈ A, σ ^ p ∈ C → σ ∈ B) → min (2 * jumpSum (wild K L) A B) (jumpSum (wild K L) A B + E) ≤ jumpSum (wild K L) A C := by
  intro K L _ _ _ _ _ _ _ _ _ _ _ _ p E A B C hA hE hC hB
  obtain ⟨j, hj, hr, -, hG⟩ := GlobalTheory.T.galoisGroup_fixedField_baseChange_localField K L A
  have hmem : ∀ σ, j σ ∈ A := fun σ => hr.le ⟨σ, rfl⟩
  have hw : wild ↥(IntermediateField.fixedField A) L = fun t => (wild K L t).comap j := by
    funext t
    exact hG _
  have h0 : lowerRamificationGroup ↥(IntermediateField.fixedField A) L 0 = ⊤ := by
    rw [hG, eq_top_iff]
    intro σ _
    exact hA (hmem σ)
  have key := GlobalTheory.T.min_jumpSum_le_jumpSum_of_totally_ramified ↥(IntermediateField.fixedField A) L p E (B.comap j) (C.comap j) h0 hE
    (fun σ τ => by
      have := hC _ (hmem σ) _ (hmem τ)
      simpa [Subgroup.mem_comap, map_mul, map_inv] using this)
    (fun σ h => by
      have h' : j σ ^ p ∈ C := by simpa [Subgroup.mem_comap, map_pow] using h
      exact hB _ (hmem σ) h')
  rw [hw, jumpSum_comap_injective _ _ j _ B hj, jumpSum_comap_injective _ _ j _ C hj, hr] at key
  exact key

end GlobalTheory.PMon.Ram
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RatioIntegral
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon.RatioTransport

open GlobalTheory.PMon.Gauss

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI)

theorem lift_phi {b : P.R.B} {y : Formalism.Per.Acris l}
    (h : T.eB b = algebraMap (Formalism.Per.Acris l) (Formalism.Per.Bcris l) y) :
    T.eB (P.φB b) = algebraMap (Formalism.Per.Acris l) (Formalism.Per.Bcris l) (φc l y) := by
  rw [T.frob, h, (GlobalTheory.PMon.Trans.acris_bcris l).2.1]

theorem lift_iter {b : P.R.B} {y : Formalism.Per.Acris l}
    (h : T.eB b = algebraMap (Formalism.Per.Acris l) (Formalism.Per.Bcris l) y) (j : ℕ) :
    T.eB (P.φB^[j] b) = algebraMap (Formalism.Per.Acris l) (Formalism.Per.Bcris l) ((φc l)^[j] y) := by
  induction j with
  | zero => exact h
  | succ j ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply']; exact lift_phi T ih

theorem iter_lpow (m j : ℕ) (x : P.R.B) :
    P.φB^[m] ((l : P.R.B) ^ j * x) = (l : P.R.B) ^ j * P.φB^[m] x := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, map_mul, map_pow, map_natCast]

theorem isUnit_lpow (m : ℕ) : IsUnit ((l : P.R.B) ^ m) := by
  have h : IsUnit (l : ℚ_[l]) := (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero : (l : ℚ_[l]) ≠ 0).isUnit
  have h2 := h.map (algebraMap ℚ_[l] P.R.B)
  rw [map_natCast] at h2
  exact h2.pow m

theorem ratio_integral {h s : ℕ} (hs : s < h) {b b' : P.R.B} {y y' : Formalism.Per.Acris l}
    (hb : T.eB b = algebraMap (Formalism.Per.Acris l) (Formalism.Per.Bcris l) y)
    (hb' : T.eB b' = algebraMap (Formalism.Per.Acris l) (Formalism.Per.Bcris l) y')
    (he : P.φB^[h] b = (l : P.R.B) ^ s * b) (he' : P.φB^[h] b' = (l : P.R.B) ^ s * b')
    (h0 : b' ≠ 0) (hr : P.φB b * b' = b * P.φB b') : ∃ c : ℚ_[l], b = c • b' := by
  obtain ⟨hinj, -, hz⟩ := GlobalTheory.PMon.Trans.acris_bcris l
  have e1 : (φc l)^[h] y = (l : Formalism.Per.Acris l) ^ s * y := by
    apply hinj
    rw [← lift_iter T hb, he, map_mul, map_pow, map_natCast, hb, map_mul, map_pow, map_natCast]
  have e2 : (φc l)^[h] y' = (l : Formalism.Per.Acris l) ^ s * y' := by
    apply hinj
    rw [← lift_iter T hb', he', map_mul, map_pow, map_natCast, hb', map_mul, map_pow, map_natCast]
  have e3 : y' ≠ 0 := by
    rintro rfl
    apply h0
    apply T.eB.injective
    rw [hb', map_zero, map_zero]
  have e4 : φc l y * y' = y * φc l y' := by
    apply hinj
    rw [map_mul, map_mul, ← lift_phi T hb, ← lift_phi T hb', ← hb, ← hb', ← map_mul, ← map_mul, hr]
  obtain ⟨c, d, hc, hcd⟩ := ratio_proportional_target l h s hs y y' e1 e2 e3 e4
  have e5 : algebraMap ℚ_[l] P.R.B (c : ℚ_[l]) * b = algebraMap ℚ_[l] P.R.B (d : ℚ_[l]) * b' := by
    apply T.eB.injective
    rw [map_mul, map_mul, T.zB, T.zB, hb, hb', ← hz, ← hz, ← map_mul, ← map_mul, hcd]
  have hc' : (c : ℚ_[l]) ≠ 0 := fun e => hc (Subtype.ext e)
  refine ⟨(c : ℚ_[l])⁻¹ * d, ?_⟩
  rw [Algebra.smul_def, map_mul, mul_assoc, ← e5, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hc', map_one, one_mul]

theorem ratio_of_acris : Ratio := by
  intro l _ P AI T h s hs ω ω' hω hω' he he' h0 hr
  obtain ⟨N, x, hx⟩ := hω
  obtain ⟨M, x', hx'⟩ := hω'
  have hb : T.eB ((l : P.R.B) ^ (N + M) * ω) =
      algebraMap (Formalism.Per.Acris l) (Formalism.Per.Bcris l) ((l : Formalism.Per.Acris l) ^ M * x) := by
    have e : (l : P.R.B) ^ (N + M) * ω = (l : P.R.B) ^ M * ((l : P.R.B) ^ N * ω) := by ring
    rw [e, map_mul T.eB ((l : P.R.B) ^ M), hx]
    simp only [map_mul, map_pow, map_natCast]
  have hb' : T.eB ((l : P.R.B) ^ (N + M) * ω') =
      algebraMap (Formalism.Per.Acris l) (Formalism.Per.Bcris l) ((l : Formalism.Per.Acris l) ^ N * x') := by
    have e : (l : P.R.B) ^ (N + M) * ω' = (l : P.R.B) ^ N * ((l : P.R.B) ^ M * ω') := by ring
    rw [e, map_mul T.eB ((l : P.R.B) ^ N), hx']
    simp only [map_mul, map_pow, map_natCast]
  have hu := isUnit_lpow (P := P) (N + M)
  obtain ⟨c, hc⟩ := ratio_integral T hs hb hb'
    (by rw [iter_lpow, he]; ring) (by rw [iter_lpow, he']; ring)
    (fun e => h0 ((hu.mul_right_eq_zero).1 e))
    (by
      simp only [map_mul, map_pow, map_natCast]
      linear_combination ((l : P.R.B) ^ (N + M)) ^ 2 * hr)
  refine ⟨c, hu.mul_left_cancel ?_⟩
  rw [hc, Algebra.smul_def, Algebra.smul_def]
  ring

end GlobalTheory.PMon.RatioTransport
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RepERankOne
section
noncomputable section

open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial Neutral.B1 Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.Pst

namespace GlobalTheory.TwistAbove

def twGL {Γ K : Type} [Group Γ] [CommRing K] {a : ℕ} (χ : Γ →* Kˣ) (r : Γ →* GL (Fin a) K) :
    Γ →* GL (Fin a) K where
  toFun g := ⟨((χ g : Kˣ) : K) • ((r g : GL (Fin a) K) : Matrix (Fin a) (Fin a) K),
    (((χ g)⁻¹ : Kˣ) : K) • (((r g)⁻¹ : GL (Fin a) K) : Matrix (Fin a) (Fin a) K),
    by rw [smul_mul_smul_comm, Units.mul_inv, Units.mul_inv, one_smul],
    by rw [smul_mul_smul_comm, Units.inv_mul, Units.inv_mul, one_smul]⟩
  map_one' := Units.ext (by simp)
  map_mul' g h := Units.ext (by
    change ((χ (g * h) : Kˣ) : K) • ((r (g * h) : GL (Fin a) K) : Matrix (Fin a) (Fin a) K) =
      (((χ g : Kˣ) : K) • ((r g : GL (Fin a) K) : Matrix (Fin a) (Fin a) K)) *
      (((χ h : Kˣ) : K) • ((r h : GL (Fin a) K) : Matrix (Fin a) (Fin a) K))
    rw [smul_mul_smul_comm, map_mul, map_mul, Units.val_mul, Units.val_mul])

@[simp] theorem twGL_val {Γ K : Type} [Group Γ] [CommRing K] {a : ℕ} (χ : Γ →* Kˣ) (r : Γ →* GL (Fin a) K)
    (g : Γ) : ((twGL χ r g : GL (Fin a) K) : Matrix (Fin a) (Fin a) K) =
      ((χ g : Kˣ) : K) • ((r g : GL (Fin a) K) : Matrix (Fin a) (Fin a) K) := rfl

variable {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
  {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
  (Bw : LocBridge l E Ω Gw O) {a : ℕ}

abbrev chr {L : FinExt l} (m : ↥Gw →* GL (Fin 1) ↥L.1) : ↥Gw →* (↥L.1)ˣ :=
  Matrix.GeneralLinearGroup.det.comp m

theorem isModel_twGL {L : FinExt l} {r r' : ↥Gw →* GL (Fin a) (Om l)} {μ : ↥Gw →* (Om l)ˣ}
    (hr' : ∀ g, ((r' g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) =
      ((μ g : (Om l)ˣ) : Om l) • ((r g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)))
    {r₁ : ↥Gw →* GL (Fin a) ↥L.1} {m : ↥Gw →* GL (Fin 1) ↥L.1}
    (h₁ : IsModel Bw r L r₁) (h₂ : IsModel Bw (rk1 μ) L m) :
    IsModel Bw r' L (twGL (chr m) r₁) := by
  refine ⟨h₁.1, ?_⟩
  ext g i j
  have e1 := congrArg (fun f : ↥Gw →* GL (Fin a) (Om l) =>
    ((f g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) i j) h₁.2
  have e2 := congrArg (fun f : ↥Gw →* GL (Fin 1) (Om l) =>
    ((f g : GL (Fin 1) (Om l)) : Matrix (Fin 1) (Fin 1) (Om l)) 0 0) h₂.2
  simp only [mapRep, rk1] at e1 e2 ⊢
  simp at e1 e2 ⊢
  rw [hr']
  simp [← e1, ← e2]

section Common

variable {L : FinExt l} (r₁ : ↥Gw →* GL (Fin a) ↥L.1) (m : ↥Gw →* GL (Fin 1) ↥L.1)

theorem repE_twGL (g : ↥(GK Bw.Kw)) (x : Fin a → ↥L.1) :
    Bw.repE L (twGL (chr m) r₁) g x = ((chr m (Bw.e.symm g) : (↥L.1)ˣ) : ↥L.1) • Bw.repE L r₁ g x := by
  change Matrix.toLin' ((twGL (chr m) r₁ (Bw.e.symm g) : GL (Fin a) ↥L.1) : Matrix (Fin a) (Fin a) ↥L.1) x =
    ((chr m (Bw.e.symm g) : (↥L.1)ˣ) : ↥L.1) •
      Matrix.toLin' ((r₁ (Bw.e.symm g) : GL (Fin a) ↥L.1) : Matrix (Fin a) (Fin a) ↥L.1) x
  rw [twGL_val, Matrix.toLin'_apply, Matrix.toLin'_apply]
  exact Matrix.smul_mulVec _ _ _

theorem repE_rank_one (g : ↥(GK Bw.Kw)) (x : Fin 1 → ↥L.1) :
    Bw.repE L m g x = ((chr m (Bw.e.symm g) : (↥L.1)ˣ) : ↥L.1) • x := by
  funext i
  fin_cases i
  simp [LocBridge.repE, Matrix.mulVec, dotProduct, Matrix.det_unique]

theorem isDR_iff (P : LocPrime l) {n : ℕ} (s : ↥Gw →* GL (Fin n) ↥L.1) :
    IsDR (P.PD Bw.Kw) (Bw.repE L s) ↔ Bw.IsdRE P L s := by
  rw [IsDR, LocBridge.IsdRE, Module.finrank_fin_fun]

theorem twist_common {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI) :
    (Bw.IsdRE P L r₁ → Bw.IsdRE P L m → Bw.IsdRE P L (twGL (chr m) r₁)) ∧
    (Bw.IsCrysE P L r₁ → Bw.IsCrysE P L m → Bw.IsCrysE P L (twGL (chr m) r₁)) ∧
    (Bw.IsPotCrysE P L r₁ → Bw.IsPotCrysE P L m → Bw.IsPotCrysE P L (twGL (chr m) r₁)) ∧
    ∀ (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥L.1) (b : ℤ), Bw.IsdRE P L m →
      (∀ n, Bw.multE P L m τ' n = if n = b then 1 else 0) →
      ∀ n, Bw.multE P L (twGL (chr m) r₁) τ' (n + b) = Bw.multE P L r₁ τ' n := by
  have hν := repE_rank_one Bw m
  have hρ := repE_twGL Bw r₁ m
  refine ⟨fun h1 h2 => ?_, fun h1 h2 => ?_, ?_, ?_⟩
  · rw [← isDR_iff] at h1 h2 ⊢
    exact (GlobalTheory.TwistDR.isDR_twist_iff l P AI T Bw.Kw L (Fin a → ↥L.1) _ _ _ _ hν hρ h2).1 h1
  · exact (GlobalTheory.TwistCrys.isCrys_iff_of_twist GlobalTheory.MemLoc.fontaineBcris l P AI T Bw.Kw L (Fin a → ↥L.1)
      _ _ _ _ hν hρ h2).1 h1
  · rintro ⟨K₁, k₁, c₁⟩ ⟨K₂, k₂, c₂⟩
    have l₁ : K₁.1 ≤ (supExt K₁ K₂).1 := le_sup_left
    have l₂ : K₂.1 ≤ (supExt K₁ K₂).1 := le_sup_right
    have k₃ : Bw.Kw.1 ≤ (supExt K₁ K₂).1 := k₁.trans l₁
    have d₁ := GlobalTheory.Per.TiedRestrict.isCrys_restrict l₁ _ T c₁
    have d₂ := GlobalTheory.Per.TiedRestrict.isCrys_restrict l₂ _ T c₂
    have e₁ : ((Bw.repE L r₁).comp (Subgroup.inclusion (GK_le k₁))).comp (Subgroup.inclusion (GK_le l₁)) =
        (Bw.repE L r₁).comp (Subgroup.inclusion (GK_le k₃)) := MonoidHom.ext fun _ => rfl
    have e₂ : ((Bw.repE L m).comp (Subgroup.inclusion (GK_le k₂))).comp (Subgroup.inclusion (GK_le l₂)) =
        (Bw.repE L m).comp (Subgroup.inclusion (GK_le k₃)) := MonoidHom.ext fun _ => rfl
    rw [e₁] at d₁
    rw [e₂] at d₂
    exact ⟨supExt K₁ K₂, k₃, (GlobalTheory.TwistCrys.isCrys_iff_of_twist GlobalTheory.MemLoc.fontaineBcris l P AI T
      (supExt K₁ K₂) L (Fin a → ↥L.1) ((Bw.repE L r₁).comp (Subgroup.inclusion (GK_le k₃))) _
      ((Bw.repE L m).comp (Subgroup.inclusion (GK_le k₃))) _ (fun g x => hν _ x) (fun g x => hρ _ x) d₂).1 d₁⟩
  · intro τ' b hm hmult n
    exact GlobalTheory.TwistJump.multV_twist_char l P AI T Bw.Kw L (Fin a → ↥L.1) _ _ _ _ hν hρ
      ((isDR_iff Bw P m).2 hm) τ' b hmult n

end Common

theorem twist_above : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] (Gw : Subgroup (Ω ≃ₐ[E] Ω)) (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω Gw O) (a : ℕ), ∀ (r r' : ↥Gw →* GL (Fin a) (Loc.Om l)) (μ : ↥Gw →* (Loc.Om l)ˣ), (∀ g, ((r' g : GL (Fin a) (Loc.Om l)) : Matrix (Fin a) (Fin a) (Loc.Om l)) = ((μ g : (Loc.Om l)ˣ) : Loc.Om l) • ((r g : GL (Fin a) (Loc.Om l)) : Matrix (Fin a) (Fin a) (Loc.Om l))) → (IsdRAt P Bw r → IsdRAt P Bw (rk1 μ) → IsdRAt P Bw r') ∧ (IsCrysAt P Bw r → IsCrysAt P Bw (rk1 μ) → IsCrysAt P Bw r') ∧ (IsPotCrysAt P Bw r → IsPotCrysAt P Bw (rk1 μ) → IsPotCrysAt P Bw r') ∧ ∀ (τ : E →+* Loc.Om l) (J : Multiset ℤ) (c : ℤ), IsJumpsAt P Bw r τ J → IsJumpsAt P Bw (rk1 μ) τ {c} → IsJumpsAt P Bw r' τ (J.map (· + c)) := by
  intro l _ P AI hT E Ω _ _ _ _ Gw O _ _ _ Bw a r r' μ hr'
  obtain ⟨T⟩ := hT
  refine ⟨fun h1 h2 => ?_, fun h1 h2 => ?_, fun h1 h2 => ?_, fun τ J c h1 h2 => ?_⟩
  · obtain ⟨L₁, r₁, m₁, d₁⟩ := h1
    obtain ⟨L₂, r₂, m₂, d₂⟩ := h2
    have l₁ : L₁.1 ≤ (supExt L₁ L₂).1 := le_sup_left
    have l₂ : L₂.1 ≤ (supExt L₁ L₂).1 := le_sup_right
    exact ⟨_, _, isModel_twGL Bw hr' (m₁.enlarge l₁) (m₂.enlarge l₂),
      (twist_common Bw _ _ T).1 ((local_ext P Bw l₁ r₁).2.1.2 d₁) ((local_ext P Bw l₂ r₂).2.1.2 d₂)⟩
  · obtain ⟨L₁, r₁, m₁, d₁⟩ := h1
    obtain ⟨L₂, r₂, m₂, d₂⟩ := h2
    have l₁ : L₁.1 ≤ (supExt L₁ L₂).1 := le_sup_left
    have l₂ : L₂.1 ≤ (supExt L₁ L₂).1 := le_sup_right
    exact ⟨_, _, isModel_twGL Bw hr' (m₁.enlarge l₁) (m₂.enlarge l₂),
      (twist_common Bw _ _ T).2.1 ((local_ext P Bw l₁ r₁).1.2 d₁) ((local_ext P Bw l₂ r₂).1.2 d₂)⟩
  · obtain ⟨L₁, r₁, m₁, d₁⟩ := h1
    obtain ⟨L₂, r₂, m₂, d₂⟩ := h2
    have l₁ : L₁.1 ≤ (supExt L₁ L₂).1 := le_sup_left
    have l₂ : L₂.1 ≤ (supExt L₁ L₂).1 := le_sup_right
    exact ⟨_, _, isModel_twGL Bw hr' (m₁.enlarge l₁) (m₂.enlarge l₂),
      (twist_common Bw _ _ T).2.2.1 ((local_ext P Bw l₁ r₁).2.2.1.2 d₁) ((local_ext P Bw l₂ r₂).2.2.1.2 d₂)⟩
  · obtain ⟨L₁, r₁, m₁, d₁, τ₁, i₁, c₁⟩ := h1
    obtain ⟨L₂, r₂, m₂, d₂, τ₂, i₂, c₂⟩ := h2
    have l₁ : L₁.1 ≤ (supExt L₁ L₂).1 := le_sup_left
    have l₂ : L₂.1 ≤ (supExt L₁ L₂).1 := le_sup_right
    have j₁ : IsInduced Bw τ ((IntermediateField.inclusion l₁).comp τ₁) := fun x => i₁ x
    have j₂ : IsInduced Bw τ ((IntermediateField.inclusion l₂).comp τ₂) := fun x => i₂ x
    have eτ := IsInduced.unique j₁ j₂
    have hd₂ := (local_ext P Bw l₂ r₂).2.1.2 d₂
    have hc := twist_common Bw (mapRep (IntermediateField.inclusion l₁).toRingHom r₁)
      (mapRep (IntermediateField.inclusion l₂).toRingHom r₂) T
    have hm : ∀ n, Bw.multE P (supExt L₁ L₂) (mapRep (IntermediateField.inclusion l₂).toRingHom r₂)
        ((IntermediateField.inclusion l₁).comp τ₁) n = if n = c then 1 else 0 := by
      intro n
      rw [eτ, (local_ext P Bw l₂ r₂).2.2.2 τ₂ n, ← c₂ n, Multiset.count_singleton]
      split_ifs <;> simp
    refine ⟨_, _, isModel_twGL Bw hr' (m₁.enlarge l₁) (m₂.enlarge l₂),
      hc.1 ((local_ext P Bw l₁ r₁).2.1.2 d₁) hd₂, _, j₁, fun n => ?_⟩
    have e1 := Multiset.count_map_eq_count' (fun x : ℤ => x + c) J (add_left_injective c) (n - c)
    simp only [sub_add_cancel] at e1
    have e2 := hc.2.2.2 _ c hd₂ hm (n - c)
    rw [sub_add_cancel] at e2
    rw [e1, e2, (local_ext P Bw l₁ r₁).2.2.2 τ₁ (n - c), c₁]

end GlobalTheory.TwistAbove
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RowFiveOneTypePrimeOfCoefRingTakenAtLive
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

namespace GlobalTheory.OrthogonalDesignFromSize

theorem main : GlobalTheory.TwSys.Cheb → ∀ D : D7, AutomorphicSideWildInertia.ResidualIrreducibleGood D → TakenAll D → TypePrimeCongruences.TypePrimeWildIdempotentChoice D := by
  intro hC D hN9 hT i k hk hHG r ρ hr π hπ hd _
  have hdec : ∃ e, GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.IsDecomp (t := D.R.t) (r π) (ρ π) (D.nd.chi i) e := hd
  have hcont : Continuous (fun g => ((ρ π g : GL (Fin D.R.r) (D.nd.O i)) :
      Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i))) :=
    GlobalTheory.BlockJumpsCompare.continuous_rho D.nd i r ρ π (hr π) hd
  have hrb : IsRhoBar D.nd i (redRep D.nd i (ρ π)) := by
    refine ⟨isOpen_ker_redRep D i (ρ π) hcont, ?_⟩
    intro x w hw B σ hB hσ
    have e2 := congrArg (Polynomial.map (IsLocalRing.residue (D.nd.O i)))
      (charpoly_of_decomp D i r ρ π hd σ)
    rw [Polynomial.map_mul, Polynomial.map_prod, ← Matrix.charpoly_map, ← Matrix.charpoly_map] at e2
    rw [heckePol_res D i x π w, ← (hr π).2.2 w hw B σ hB hσ, ← Matrix.charpoly_map]
    refine (e2.trans ?_).symm
    congr 1
    refine Finset.prod_congr rfl fun c _ => ?_
    simp
  have hirr := (hN9 i hHG _ hrb).1
  have hpos : 0 < D.R.r := by
    have := D.R.two_le_m
    unfold Ranks.r
    omega
  have habs : AbsIrrSub (mapRep (IsLocalRing.residue (D.nd.O i)) (ρ π)) ⊤ :=
    GlobalTheory.ResAbsIrrGood.absIrrSub_top_of_irred (D.naut.kFbar i) hpos _
      fun W hW => hirr W fun g _ x hx => hW g x hx
  have hlive : Live D.nd i := ⟨π, hπ, r π, ρ π, hr π, hdec, habs⟩
  obtain ⟨r₀, ρ₀, hr₀, hw⟩ := hT i hlive
  obtain ⟨S, hS, hg⟩ := GlobalTheory.T.exists_globalObjects_every_family_wild hC D.nd i r₀ ρ₀ hr₀ hw r ρ hr π hπ hdec
  exact ⟨S, hS, hg.2 ⟨k, hk⟩⟩

end GlobalTheory.OrthogonalDesignFromSize
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemistableDiscCoefficientRecurrence
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section
namespace GlobalTheory.BSP

variable {l : ℕ} [hl : Fact l.Prime] {K : FinExt l}

theorem wseedRec_ρ₀_pos (bk : BK K) : 0 < bk.ρ₀ := by
  unfold BK.ρ₀
  exact NNReal.rpow_pos (by exact_mod_cast hl.out.pos)

theorem wseedRec_ρ₀_lt_one (bk : BK K) : bk.ρ₀ < 1 := by
  unfold BK.ρ₀
  apply NNReal.rpow_lt_one_of_one_lt_of_neg
  · exact_mod_cast hl.out.one_lt
  · have : (0:ℝ) < bk.Ep.natDegree := by exact_mod_cast bk.deg_pos
    have : 0 < 1 / (bk.Ep.natDegree : ℝ) := by positivity
    linarith

theorem wseedRec_frobS_norm (bk : BK K) :
    ‖toDisc l (X : bk.S) bk.ρ₀ (frobS l bk.a X)‖ ≤ bk.ρ₀ := by
  rw [frobS_X]
  refine (norm_toDisc_pow_le (l := l) (u := (X : bk.S)) l (wseedRec_ρ₀_pos bk)).trans ?_
  exact pow_le_of_le_one bk.ρ₀.coe_nonneg (by exact_mod_cast (wseedRec_ρ₀_lt_one bk).le) hl.out.ne_zero

theorem wseedRec_comm (bk : BK K) (j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀) (hj : IsDiscMap bk.ev j)
    (Φ : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀) (hΦ : IsDiscMap WittVector.frobenius Φ)
    (ΦS : bk.DS bk.ρ₀ →+* bk.DS bk.ρ₀) (hΦS : IsDiscMap (frobS l bk.a) ΦS) (x : bk.DS bk.ρ₀) :
    Φ (j x) = j (ΦS x) := by
  have h1 : IsDiscMap (bk.ev.comp (frobS l bk.a)) (Φ.comp j) :=
    ⟨fun a => by simp [hj.ext, hΦ.ext, bk.ev_frob], fun x => (hΦ.norm_le _).trans (hj.norm_le x)⟩
  have h2 : IsDiscMap (bk.ev.comp (frobS l bk.a)) (j.comp ΦS) :=
    ⟨fun a => by simp [hj.ext, hΦS.ext], fun x => (hj.norm_le _).trans (hΦS.norm_le x)⟩
  exact RingHom.congr_fun (h1.unique h2) x

theorem wseedRec_frobS_E_ne_zero (bk : BK K) : frobS l bk.a bk.E ≠ 0 := by
  intro h
  have := congrArg (PowerSeries.coeff (l * bk.Ep.natDegree)) h
  simp [frobS, BK.E, Polynomial.coeff_coe, bk.monic.coeff_natDegree] at this

theorem wseedRec_ev_injective (bk : BK K) {ι : Type} (TB : TopBasis bk.ev bk.J ι) : Function.Injective bk.ev := by
  have hb : TB.c TB.i₀ 1 = 1 := by rw [← TB.b_i₀]; exact TB.c_self _
  have hev : ∀ x, TB.c TB.i₀ (bk.ev x) = x := fun x => by simpa [hb] using TB.c_mul TB.i₀ x 1
  intro x y h
  rw [← hev x, h, hev]

theorem wseed_coeff_recurrence : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l) (hτ : bk.IsPer τ) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (hρ : ∀ g, IsUnit (ρ g)) (s : WSeed bk d ρ τ), ∀ (ι : Type) (TB : TopBasis bk.ev bk.J ι) (j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀), IsDiscMap bk.ev j → ∀ (cD : ι → (bk.DA bk.ρ₀ →+ bk.DS bk.ρ₀)), (∀ i a, cD i (bk.iA a) = toDisc l (X : bk.S) bk.ρ₀ (TB.c i a)) → (∀ i x y, cD i (j x * y) = x * cD i y) → (∀ y, HasSum (fun i => j (cD i y) * bk.iA (TB.b i)) y) → (∀ i y, ‖cD i y‖ ≤ ‖y‖) → ∀ Φ : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap WittVector.frobenius Φ → ∀ (i₁ : ι) (a b : Fin d), HasSum (fun i => Φ ((s.W * (s.W'.map (cD i)).map j) a b) * bk.iS (TB.c i₁ (WittVector.frobenius (TB.b i)))) (bk.iS bk.E ^ (2 * s.N) * (s.W * (s.W'.map (cD i₁)).map j) a b) := by
  intro l _ K bk τ hτ d ρ hρ s ι TB j hj cD hc hcm hsum hnorm Φ hΦ i₁ a b
  have h0 := wseedRec_ρ₀_pos bk
  have h1 := wseedRec_ρ₀_lt_one bk
  obtain ⟨hdom, -, -⟩ := GlobalTheory.BSP.discAinf_isDomain l K bk bk.ρ₀ h0 h1
  let ΦS := Disc.map (l := l) (u := (X : bk.S)) (ρ := bk.ρ₀) (u' := (X : bk.S)) (ρ' := bk.ρ₀)
    (frobS l bk.a) (wseedRec_frobS_norm bk)
  have hΦS : IsDiscMap (frobS l bk.a) ΦS := isDiscMap_map _ _
  have hcomm : ∀ x, Φ (j x) = j (ΦS x) := wseedRec_comm bk j hj Φ hΦ ΦS hΦS
  have hjS : ∀ t, j (toDisc l (X : bk.S) bk.ρ₀ t) = bk.iS t := fun t => hj.ext t
  have hΦA : ∀ x, Φ (bk.iA x) = bk.iA (WittVector.frobenius x) := fun x => hΦ.ext x
  have hcont : ∀ i, Continuous (cD i) := fun i =>
    AddMonoidHomClass.continuous_of_bound (cD i) 1 (fun y => by rw [one_mul]; exact hnorm i y)
  have hΦc : Continuous Φ :=
    AddMonoidHomClass.continuous_of_bound Φ 1 (fun y => by rw [one_mul]; exact hΦ.norm_le y)
  have hjc : Continuous j :=
    AddMonoidHomClass.continuous_of_bound j 1 (fun y => by rw [one_mul]; exact hj.norm_le y)
  let c : ι → bk.DA bk.ρ₀ := fun i => bk.iS (TB.c i₁ (WittVector.frobenius (TB.b i)))
  let L : bk.DA bk.ρ₀ →+ bk.DA bk.ρ₀ := (j : bk.DS bk.ρ₀ →+ bk.DA bk.ρ₀).comp (cD i₁)
  have hLa : ∀ y, L y = j (cD i₁ y) := fun y => rfl
  have hLc : Continuous L := hjc.comp (hcont i₁)
  have hL : ∀ t y, L (bk.iS t * y) = bk.iS t * L y := by
    intro t y
    rw [hLa, hLa, ← hjS, hcm, map_mul]
  have key : ∀ y, HasSum (fun i => Φ (j (cD i y)) * c i) (L (Φ y)) := by
    intro y
    have h := ((hsum y).map (Φ : bk.DA bk.ρ₀ →+ bk.DA bk.ρ₀) hΦc).map L hLc
    convert h using 1
    · funext i
      simp only [Function.comp_apply, AddMonoidHom.coe_coe]
      rw [map_mul Φ, hΦA, hcomm, hLa, hcm, hc, map_mul, hjS]
    · rfl
  have stepA : HasSum (fun i => Φ ((s.W * (s.W'.map (cD i)).map j) a b) * c i)
      ((s.W.map Φ * (s.W'.map Φ).map L) a b) := by
    simp only [Matrix.mul_apply, Matrix.map_apply, map_sum, map_mul, Finset.sum_mul]
    refine hasSum_sum fun k _ => ?_
    simp_rw [mul_assoc]
    exact (key (s.W' k b)).mul_left (Φ (s.W a k))
  haveI := hdom
  have hphi := GlobalTheory.T.frobenius_matrix_relation_discrete l K bk τ hτ d ρ hρ s Φ hΦ
  have hwp := GlobalTheory.T.semistablePeriod_frobenius_of_scaled_inverse l K bk τ hτ d ρ hρ s Φ hΦ
  have hmapL : ∀ (M : Matrix (Fin d) (Fin d) bk.S) (Y : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀)),
      (M.map bk.iS * Y).map L = M.map bk.iS * Y.map L := by
    intro M Y
    ext k m
    simp only [Matrix.map_apply, Matrix.mul_apply, map_sum, hL]
  have hμ : (l : bk.DA bk.ρ₀) ^ (s.c₁ + s.c₂) * bk.iS (frobS l bk.a bk.E) ^ s.N * bk.iS bk.E ^ (2 * s.N) =
      bk.iS ((l : bk.S) ^ (s.c₁ + s.c₂) * frobS l bk.a bk.E ^ s.N * bk.E ^ (2 * s.N)) := by
    simp only [map_mul, map_pow, map_natCast]
  have hBL : (s.X' * s.F.map (C : Wq l bk.a →+* bk.S) * s.X.map (frobS l bk.a)).map bk.iS *
      (s.W'.map Φ).map L = ((l : bk.DA bk.ρ₀) ^ (s.c₁ + s.c₂) * bk.iS (frobS l bk.a bk.E) ^ s.N *
        bk.iS bk.E ^ (2 * s.N)) • s.W'.map L := by
    rw [← hmapL, hwp]
    ext k m
    rw [Matrix.map_apply, Matrix.smul_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, smul_eq_mul, hμ, hL]
  have hWJ : s.W'.map L = (s.W'.map (cD i₁)).map j := by ext; rfl
  have heq : ((l : bk.DA bk.ρ₀) ^ (s.c₁ + s.c₂) * bk.iS (frobS l bk.a bk.E) ^ s.N) •
      (s.W.map Φ * (s.W'.map Φ).map L) = ((l : bk.DA bk.ρ₀) ^ (s.c₁ + s.c₂) * bk.iS (frobS l bk.a bk.E) ^ s.N) •
      (bk.iS bk.E ^ (2 * s.N) • (s.W * (s.W'.map (cD i₁)).map j)) := by
    conv_lhs => rw [← Matrix.smul_mul, hphi, Matrix.mul_assoc, hBL, Matrix.mul_smul]
    rw [smul_smul, hWJ]
  have hE0 : bk.iS (frobS l bk.a bk.E) ≠ 0 := by
    intro h
    apply wseedRec_frobS_E_ne_zero bk
    apply wseedRec_ev_injective bk TB
    rw [map_zero]
    apply (toDisc_injective_of_topBasis l K bk (Ainf l) bk.ev ι TB bk.ρ₀ h0 h1).1
    rw [map_zero]
    exact h
  have hlam : (l : bk.DA bk.ρ₀) ^ (s.c₁ + s.c₂) * bk.iS (frobS l bk.a bk.E) ^ s.N ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (isUnit_l_disc l (bk.ev X) bk.ρ₀).ne_zero) (pow_ne_zero _ hE0)
  have hab := congrFun (congrFun heq a) b
  rw [Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul] at hab
  have h2 := mul_left_cancel₀ hlam hab
  rw [Matrix.smul_apply, smul_eq_mul] at h2
  rw [← h2]
  exact stepA

end GlobalTheory.BSP
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TopBasisDiscRegularStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.toDisc_injective_and_nonZeroDivisors_of_topBasis : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (A : Type) [CommRing A] (s : bk.S →+* A) (ι : Type), TopBasis s bk.J ι → Function.Injective (toDisc l (s X) bk.ρ₀) ∧ toDisc l (s X) bk.ρ₀ (s bk.E) ∈ nonZeroDivisors (Disc l (s X) bk.ρ₀) ∧ (l : A) ∈ nonZeroDivisors A ∧ ∀ F : bk.DS bk.ρ₀ →+* Disc l (s X) bk.ρ₀, IsDiscMap s F → Function.Injective F := by
  first | exact @GlobalTheory.BSP.topBasis_disc_regular | exact GlobalTheory.BSP.topBasis_disc_regular | (intros; apply GlobalTheory.BSP.topBasis_disc_regular <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitLemmaUnitaryGroupOddResidueOfLieStatement
section
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitLemma_unitary_group_odd_residue_of_lie : UnitLemmaLie → UnitLemmaGroup := by
  first | exact @GlobalTheory.UnitLemma.Orbit.unitLemmaGroup_of_lie | exact GlobalTheory.UnitLemma.Orbit.unitLemmaGroup_of_lie | (intros; apply GlobalTheory.UnitLemma.Orbit.unitLemmaGroup_of_lie <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeEqFiltrationSumAtLevelStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wach_lattice_eq_filtration_sum_at_level : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let E := ((F l).E K s LL h).tie; let C := Cm l; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ (i : Let K) (ζ : ↥LL.1) τ, Pt (HW l) h i ζ τ → ∀ f : ℤ → T.V ⊗[ℚ_[l]] (D.loc l).R.B, f ∈ Lat C h T i ζ ↔ (∃ m : ℤ, ∀ k < m, f k = 0) ∧ ∀ k : ℤ, f k ∈ Di (HW l) h T i ∧ ιV ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V) (f k) ∈ FilAt ((D.loc l).PD K) T τ (-k) := by
  first | exact @GlobalTheory.NL.LatFil.lat_eq_fil | exact GlobalTheory.NL.LatFil.lat_eq_fil | (intros; apply GlobalTheory.NL.LatFil.lat_eq_fil <;> assumption)
end

