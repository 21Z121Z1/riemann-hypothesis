import Formalism.LocalToGlobal.IndefiniteReal.Bundle0024
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0603
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0604
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0580
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0545
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValApplySubLtOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertialOrderFifteenCharAuxiliaryPrimeSpec
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import GroundTheory.GlobalFields.TateThesis.AdelicChar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0434
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0602

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsDoubleCosetOfSmallerLevelSameLocal
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem isDC_of_smaller_level_same_local {G : Type} [Group G] (J J' Lc : Subgroup G) (x : G) (A : Finset G)
    (hJJ : J' ≤ J) (hLc : J ⊓ Lc ≤ J')
    (hdec : ∀ k ∈ J, ∃ k₁ ∈ J, ∃ k₂ ∈ J, k₁ ∈ Lc ∧ k = k₁ * k₂ ∧ ∀ y ∈ Lc, Commute k₂ y)
    (hx : x ∈ Lc) (hA : ∀ a ∈ A, a ∈ Lc) (hDC : Bridge.IsDC J x A) : Bridge.IsDC J' x A := by
  obtain ⟨h1, h2⟩ := hDC
  refine ⟨fun a ha => ?_, fun g hg => ?_⟩
  · obtain ⟨⟨k, hk⟩, ⟨k', hk'⟩, rfl⟩ := h1 a ha
    obtain ⟨k₁, hk₁J, k₂, hk₂J, hk₁L, rfl, hk₂c⟩ := hdec k hk
    obtain ⟨k₁', hk₁'J, k₂', hk₂'J, hk₁'L, rfl, -⟩ := hdec k' hk'
    have e : k₁ * k₂ * x * (k₁' * k₂') = k₁ * x * k₁' * (k₂ * k₂') := by
      have c1 : k₂ * x = x * k₂ := (hk₂c x hx).eq
      have c2 : k₂ * k₁' = k₁' * k₂ := (hk₂c k₁' hk₁'L).eq
      calc k₁ * k₂ * x * (k₁' * k₂') = k₁ * (k₂ * x) * k₁' * k₂' := by group
        _ = k₁ * x * (k₂ * k₁') * k₂' := by rw [c1]; group
        _ = k₁ * x * (k₁' * k₂) * k₂' := by rw [c2]
        _ = k₁ * x * k₁' * (k₂ * k₂') := by group
    have haL := hA _ ha
    have hprodL : k₂ * k₂' ∈ Lc := by
      have : k₂ * k₂' = (k₁ * x * k₁')⁻¹ * (k₁ * k₂ * x * (k₁' * k₂')) := by rw [e]; group
      rw [this]
      exact Lc.mul_mem (Lc.inv_mem (Lc.mul_mem (Lc.mul_mem hk₁L hx) hk₁'L)) haL
    have hprod : k₂ * k₂' ∈ J' := hLc ⟨J.mul_mem hk₂J hk₂'J, hprodL⟩
    have hk₁ : k₁ ∈ J' := hLc ⟨hk₁J, hk₁L⟩
    have hk₁' : k₁' ∈ J' := hLc ⟨hk₁'J, hk₁'L⟩
    refine ⟨⟨k₁, hk₁⟩, ⟨k₁' * (k₂ * k₂'), J'.mul_mem hk₁' hprod⟩, ?_⟩
    simp only
    rw [e]; group
  · obtain ⟨⟨k, hk⟩, ⟨k', hk'⟩, rfl⟩ := hg
    obtain ⟨k₁, hk₁J, k₂, hk₂J, hk₁L, rfl, hk₂c⟩ := hdec k (hJJ hk)
    have hk₁ : k₁ ∈ J' := hLc ⟨hk₁J, hk₁L⟩
    have hk₂ : k₂ ∈ J' := by
      have : k₂ = k₁⁻¹ * (k₁ * k₂) := by group
      rw [this]; exact J'.mul_mem (J'.inv_mem hk₁) hk
    obtain ⟨a, ⟨haA, haJ⟩, -⟩ := h2 (k₁ * x) ⟨⟨k₁, hk₁J⟩, 1, by simp⟩
    have haL : a⁻¹ * (k₁ * x) ∈ Lc := Lc.mul_mem (Lc.inv_mem (hA a haA)) (Lc.mul_mem hk₁L hx)
    have haJ' : a⁻¹ * (k₁ * x) ∈ J' := hLc ⟨haJ, haL⟩
    have c1 : k₂ * x = x * k₂ := (hk₂c x hx).eq
    refine ⟨a, ⟨haA, ?_⟩, ?_⟩
    · have : a⁻¹ * (k₁ * k₂ * x * k') = a⁻¹ * (k₁ * x) * (k₂ * k') := by
        calc a⁻¹ * (k₁ * k₂ * x * k') = a⁻¹ * k₁ * (k₂ * x) * k' := by group
          _ = a⁻¹ * (k₁ * x) * (k₂ * k') := by rw [c1]; group
      rw [this]
      exact J'.mul_mem haJ' (J'.mul_mem hk₂ hk')
    · rintro b ⟨hbA, hbJ'⟩
      have hgJ : ∃ m₁ m₂ : J, k₁ * k₂ * x * k' = (m₁ : G) * x * m₂ :=
        ⟨⟨k₁ * k₂, hJJ hk⟩, ⟨k', hJJ hk'⟩, rfl⟩
      obtain ⟨c, -, hc⟩ := h2 _ hgJ
      have haJg : a⁻¹ * (k₁ * k₂ * x * k') ∈ J := by
        have : a⁻¹ * (k₁ * k₂ * x * k') = a⁻¹ * (k₁ * x) * (k₂ * k') := by
          calc a⁻¹ * (k₁ * k₂ * x * k') = a⁻¹ * k₁ * (k₂ * x) * k' := by group
            _ = a⁻¹ * (k₁ * x) * (k₂ * k') := by rw [c1]; group
        rw [this]; exact J.mul_mem haJ (J.mul_mem hk₂J (hJJ hk'))
      rw [hc b ⟨hbA, hJJ hbJ'⟩, hc a ⟨haA, haJg⟩]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsExactTripleBreuilKisinOfShortExactLatticesStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isExactTriple_breuilKisin_of_shortExactLattices : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (ι : Type) [Fintype ι] [DecidableEq ι] (κ : Type) [Fintype κ] [DecidableEq κ] (μ : Type) [Fintype μ] [DecidableEq μ] (P₀ : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (P₁ : PhiMod ↥(OL LL) ↥LL.1 l e a κ) (P₂ : PhiMod ↥(OL LL) ↥LL.1 l e a μ) (T₀ T₁ T₂ : QLat LL) (I₀ : Ident (thetaW a LL) ϖ P₀ T₀) (I₁ : Ident (thetaW a LL) ϖ P₁ T₁) (I₂ : Ident (thetaW a LL) ϖ P₂ T₂) (f : LatHom T₀.L T₁.L) (g : LatHom T₁.L T₂.L) (F : GlobalTheory.BK.Hom P₀ P₁) (G : GlobalTheory.BK.Hom P₁ P₂), IsSESLat (Qp := ℚ_[l]) f g → IsMapOf I₀ I₁ f F → IsMapOf I₁ I₂ g G → IsExactTriple F G := by
  first | exact @GlobalTheory.BKExact.isExactTriple_of_isSESLat | exact GlobalTheory.BKExact.isExactTriple_of_isSESLat | (intros; apply GlobalTheory.BKExact.isExactTriple_of_isSESLat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsStablePrismHomOfLocalizationAwayStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isStablePrismHom_of_localizationAway : ∀ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] (B C : Obj l R) (s : B.A) (h : Hom B C), (∃ t ∈ B.I, ∀ x ∈ B.I, ∃ k : ℕ, s ^ k * x ∈ Ideal.span {t}) → IsLoc s h → Stable h := by
  first | exact @GlobalTheory.BSP.stable_of_isLoc | exact GlobalTheory.BSP.stable_of_isLoc | (intros; apply GlobalTheory.BSP.stable_of_isLoc <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitDiscBasisCrystallineLatticeStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isUnit_discBasis_crystallineLattice : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l) (hτ : bk.IsPer τ) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (hρ : ∀ g, IsUnit (ρ g)) (s : Seed bk d ρ τ) (Y : Matrix (Fin d) (Fin d) (Ainf l)) (Z : Matrix (Fin d) (Fin d) (bk.DS bk.ρ₀)) (k : ℕ) (S' : Matrix (Fin d) (Fin d) (Ainf l)), Y * S' = ((l : Ainf l) ^ k * τ ^ (2 * s.N)) • (1 : Matrix (Fin d) (Fin d) (Ainf l)) → (∀ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap bk.ev j → s.W * Z.map j = Y.map bk.iA) → IsUnit Z := by
  first | exact @GlobalTheory.BSP.height_Z_isUnit | exact GlobalTheory.BSP.height_Z_isUnit | (intros; apply GlobalTheory.BSP.height_Z_isUnit <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitSaturatedBasisEtaleLattice
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

noncomputable section

namespace GlobalTheory.EtaleLattice

theorem exists_frob_matrix {R : Type} [CommRing R] [IsDomain R] (O : Subring R) (φ : R →+* R) (p : R) (hp : p ≠ 0)
    (hφp : φ p = p) (hφO : ∀ w ∈ O, φ w ∈ O) {d : ℕ} (Y A P Y' : Matrix (Fin d) (Fin d) R) (k m : ℕ) (u u' : R)
    (hu' : u' ∈ O) (huu : u * u' = 1) (hA : ∀ i j, A i j ∈ O) (hP : ∀ i j, P i j ∈ O)
    (hφ : (p ^ k * u) • Y.map φ = Y * A) (hY' : p ^ m • Y' = Y * P)
    (hlat : ∀ v : Fin d → R, (∀ i, v i ∈ O) → ∀ n : ℕ, (∀ i, p ^ n ∣ (Y *ᵥ v) i) →
      ∃ w : Fin d → R, (∀ i, w i ∈ O) ∧ p ^ m • v = p ^ n • (P *ᵥ w)) :
    ∃ B : Matrix (Fin d) (Fin d) R, (∀ i j, B i j ∈ O) ∧ Y'.map φ = Y' * B := by
  have cancel : ∀ (n : ℕ) (M N : Matrix (Fin d) (Fin d) R), p ^ n • M = p ^ n • N → M = N := by
    intro n M N h
    refine Matrix.ext fun i j => ?_
    exact mul_left_cancel₀ (pow_ne_zero n hp) (congrFun (congrFun h i) j)
  have h1 : p ^ m • Y'.map φ = Y.map φ * P.map φ := by
    rw [← Matrix.map_mul, ← hY']
    refine Matrix.ext fun i j => ?_
    simp [hφp]
  set V : Matrix (Fin d) (Fin d) R := u' • (A * P.map φ) with hV
  have hVO : ∀ i j, V i j ∈ O := by
    intro i j
    rw [hV, Matrix.smul_apply, Matrix.mul_apply]
    exact O.mul_mem hu' (O.sum_mem fun c _ => O.mul_mem (hA i c) (hφO _ (hP c j)))
  have h2 : Y * V = p ^ (k + m) • Y'.map φ := by
    rw [hV, Matrix.mul_smul, ← Matrix.mul_assoc, ← hφ, Matrix.smul_mul, ← h1, smul_smul, smul_smul]
    congr 1
    linear_combination (p ^ k * p ^ m) * huu
  have h3 : ∀ j, ∃ w : Fin d → R, (∀ i, w i ∈ O) ∧ p ^ m • (fun i => V i j) = p ^ (k + m) • (P *ᵥ w) := by
    intro j
    refine hlat _ (fun i => hVO i j) _ fun i => ⟨φ (Y' i j), ?_⟩
    exact congrFun (congrFun h2 i) j
  choose w hwO hw using h3
  refine ⟨Matrix.of fun i j => w j i, fun i j => hwO j i, ?_⟩
  have h4 : p ^ m • V = p ^ (k + m) • (P * Matrix.of fun i j => w j i) := by
    refine Matrix.ext fun i j => ?_
    exact congrFun (hw j) i
  apply cancel (k + m)
  apply cancel m
  rw [← h2, ← Matrix.mul_smul, h4, Matrix.mul_smul, ← Matrix.mul_assoc, ← hY', Matrix.smul_mul, smul_comm]

theorem isUnit_saturated_basis : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d N : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]), (∀ g, IsUnit (ρ g)) → ∀ (Y1 : Matrix (Fin d) (Fin d) (Ainf l)) (δ : bk.S) (A1 : Matrix (Fin d) (Fin d) (bk.S)), (Y1.map (inclW l)).det ≠ 0 → δ ≠ 0 → bk.ev δ • Y1.map WittVector.frobenius = Y1 * A1.map bk.ev → (∀ g : ↥(GK K), bk.FixFlat g → τ ^ N • ((ρ g).map (algebraMap ℤ_[l] (Ainf l)) * Y1.map (Per.σA (g : GQ l))) = Per.σA (g : GQ l) τ ^ N • Y1) → ∀ (m : ℕ) (P Y' : Matrix (Fin d) (Fin d) (WCb l)), (∀ i j, P i j ∈ bk.OE) → P.det ≠ 0 → (l : WCb l) ^ m • Y' = Y1.map (inclW l) * P → (∀ v : Fin d → WCb l, (∀ i, v i ∈ bk.OE) → ∀ n : ℕ, (∀ i, (l : WCb l) ^ n ∣ (Y1.map (inclW l) *ᵥ v) i) → ∃ w : Fin d → WCb l, (∀ i, w i ∈ bk.OE) ∧ (l : WCb l) ^ m • v = (l : WCb l) ^ n • (P *ᵥ w)) → (∀ w : Fin d → WCb l, (∀ i, w i ∈ bk.OE) → (∀ i, (l : WCb l) ∣ (Y' *ᵥ w) i) → ∀ i, (l : WCb l) ∣ w i) → IsUnit Y' := by
  intro l hl K bk τ hτ d N ρ hρ Y1 δ A1 hdet hδ hφ hg m P Y' hP hPdet hY' hlat hsat
  obtain ⟨-, -, h3, -, -, h6, h7⟩ := GlobalTheory.T.integral_elements_unit_factorization l K bk
  obtain ⟨ht1, -, -, ht4⟩ := GlobalTheory.T.breuilKisin_period_isUnit_wittTilt_and_ne_zero l K bk τ hτ
  haveI : PerfectRing (Cb l) l := by
    refine PerfectRing.ofSurjective _ l fun x => ?_
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := OCb l) x
    obtain ⟨a', rfl⟩ := surjective_frobenius (OCb l) l a
    obtain ⟨b', rfl⟩ := surjective_frobenius (OCb l) l b
    exact ⟨algebraMap (OCb l) (Cb l) a' / algebraMap (OCb l) (Cb l) b', by
      simp [frobenius_def, div_pow, map_pow]⟩
  have hl0 : (l : WCb l) ≠ 0 := WittVector.p_nonzero l (Cb l)
  have hlu : ¬ IsUnit (l : bk.S) := fun h => by
    have := h.map bk.evW
    rw [map_natCast] at this
    exact (WittVector.irreducible l (k := Cb l)).not_isUnit this
  have hev : ∀ s, bk.evW s ∈ bk.OE := fun s n => ⟨0, s, 0, by simp⟩
  obtain ⟨k, δ', hnd, rfl⟩ := WfDvdMonoid.max_power_factor' hδ hlu
  obtain ⟨u', hu', huu⟩ := h3 δ' hnd
  have hφW : ((l : WCb l) ^ k * bk.evW δ') • (Y1.map (inclW l)).map (frobW l).toRingHom =
      Y1.map (inclW l) * A1.map bk.evW := by
    have := congrArg (fun M => Matrix.map M (inclW l)) hφ
    simp only [Matrix.map_mul] at this
    rw [show A1.map bk.evW = (A1.map bk.ev).map (inclW l) from rfl, ← this]
    refine Matrix.ext fun i j => ?_
    simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, map_mul, map_pow, map_natCast]
    rw [BK.evW, RingHom.comp_apply, ← GlobalTheory.Prism.frobW_inclW]
    rfl
  obtain ⟨B, hB, hBφ⟩ := exists_frob_matrix bk.OE (frobW l).toRingHom (l : WCb l) hl0 (map_natCast _ _) h7
    (Y1.map (inclW l)) (A1.map bk.evW) P Y' k m (bk.evW δ') u' hu' huu (fun i j => hev _) hP hφW hY' hlat
  refine GlobalTheory.T.isUnit_of_saturated' l K bk d Y' B ?_ hB hBφ ?_ hsat
  · intro h0
    have := congrArg Matrix.det hY'
    rw [Matrix.det_smul, h0, mul_zero, Matrix.det_mul] at this
    exact mul_ne_zero hdet hPdet this.symm
  · intro g hfix
    obtain ⟨t, ht⟩ := ht1
    obtain ⟨s, hs⟩ := ht4 (g : GQ l)
    set Z : Matrix (Fin d) (Fin d) (WCb l) := ((ρ g).map (algebraMap ℤ_[l] (Ainf l))).map (inclW l) with hZ
    have hZu : IsUnit Z := ((hρ g).map (algebraMap ℤ_[l] (Ainf l)).mapMatrix).map (inclW l).mapMatrix
    have e1 : (t : WCb l) ^ N • (Z * (Y1.map (inclW l)).map (galW l (g : GQ l))) =
        (s : WCb l) ^ N • Y1.map (inclW l) := by
      have := congrArg (fun M => Matrix.map M (inclW l)) (hg g hfix)
      have e : (Y1.map (inclW l)).map (galW l (g : GQ l)) = (Y1.map (Per.σA (g : GQ l))).map (inclW l) := by
        refine Matrix.ext fun i j => ?_
        exact GlobalTheory.Prism.galW_inclW _ _
      rw [e, hZ, ← Matrix.map_mul, ht, hs]
      refine Matrix.ext fun i j => ?_
      have := congrFun (congrFun this i) j
      simpa only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, map_mul, map_pow] using this
    have e2 : (l : WCb l) ^ m • Y'.map (galW l (g : GQ l)) = (Y1.map (inclW l)).map (galW l (g : GQ l)) * P := by
      have eP : P.map (galW l (g : GQ l)) = P := by
        refine Matrix.ext fun i j => ?_
        exact h6 g hfix _ (hP i j)
      rw [← eP, ← Matrix.map_mul, ← hY']
      refine Matrix.ext fun i j => ?_
      simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, map_mul, map_pow, map_natCast]
    refine ⟨((s⁻¹ * t) ^ N : (WCb l)ˣ) • Z, ?_, ?_⟩
    · exact hZu.smul _
    · have e3 : (l : WCb l) ^ m • ((((s⁻¹ * t) ^ N : (WCb l)ˣ) • Z) * Y'.map (galW l (g : GQ l))) =
          (l : WCb l) ^ m • Y' := by
        rw [← Matrix.mul_smul, e2, hY', ← Matrix.mul_assoc, Units.smul_def, Matrix.smul_mul, Units.val_pow_eq_pow_val,
          Units.val_mul, mul_pow, mul_smul, e1, smul_smul, ← mul_pow, Units.inv_mul, one_pow, one_smul]
      refine Matrix.ext fun i j => ?_
      exact mul_left_cancel₀ (pow_ne_zero m hl0) (congrFun (congrFun e3 i) j)

end GlobalTheory.EtaleLattice
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsValueTiedOfIsToricElt
section
noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions GlobalTheory.CMVal GlobalTheory.HeckeGal GlobalTheory.ToricDenom
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (lamF upIdele)

namespace GlobalTheory.ToricRational

attribute [local instance 10000] GlobalTheory.GalChar.isTorsionFree_field

def RatioConj : Prop :=
  ∀ (R : Ranks) (H : Host R) (I : Type) [Fintype I] (φ : I → H.E →+* ℂ) (s : ℕ) (κ : I → ℕ) (𝔣 : Ideal (OF H.E)) (χ : HChar H.E),
    IsHostDatum H φ s κ 𝔣 χ →
    ∀ (Ω : Type) [Field Ω] [Algebra H.K Ω] [IsAlgClosure H.K Ω] (j : Ω →+* ℂ) (τ₀ : I),
    (∀ x : H.K, j (algebraMap H.K Ω x) = φ τ₀ x) →
    ∀ art : Ideles H.K →* Gab H.K Ω, IsGlobalArtin art →
    ∀ T₀ : ℂ, IsToricSum φ s κ (condQ 𝔣 ∅) χ T₀ → T₀ ≠ 0 →
    ∀ Q : Finset (HeightOneSpectrum (OF H.E)), IsFinSetSplitPlacesCoprimeConductor 𝔣 Q → Finite (PicO (condQ 𝔣 Q)) →
    ∀ T : PicO (condQ 𝔣 Q) → ℂ, (∀ q, IsClassTerm φ s κ (condQ 𝔣 Q) χ q.out (T q)) →
    ∃ ρ : (PicO (condQ 𝔣 Q) →* Ωˣ) → Ω,
      (∀ ψ, j (ρ ψ) = (∑ᶠ q, (j (ψ q))⁻¹ * T q) / T₀) ∧
      ∀ g : G H.K Ω, (∀ (x : Ω) (τ : I) (y : H.E), j x = φ τ y → g x = x) → (∀ (x : Ω) (y : (Af H.E)ˣ), j x = lamF s χ y → g x = x) →
        ∀ t : (Af H.K)ˣ, art (finIdele H.K t) = toAb H.K Ω g⁻¹ → ∀ ψ : PicO (condQ 𝔣 Q) →* Ωˣ,
          g (ρ ψ) = (g (ψ (QuotientGroup.mk (upIdele H.K H.E t))))⁻¹ * ρ ((Units.map g.toRingEquiv.toMonoidHom).comp ψ)

variable {D : D7} {N : NData D.R D.host D.what₂} (X : NTw D.R D.host D.what₂ D.LL0 N)

def setTh (th : ∀ i Q, X.abelian₂ i → X.RCG i Q → FractionRing (X.O i)) : NTw D.R D.host D.what₂ D.LL0 N :=
  { X with th := th }

def IsValueCharAt (i : X.Tw) (ι : ℂ →+* Kbar X i) (lam : X.abelian₂ i) (s : ℕ) : Prop :=
  ∃ (I : Type) (_ : Fintype I) (φ : I → D.host.E →+* ℂ) (κ : I → ℕ) (𝔣 : Ideal (OF D.host.E)) (χ : HChar D.host.E),
    IsHostDatum D.host φ s κ 𝔣 χ ∧ (∀ P, (below P).asIdeal ∣ 𝔣 → P ∈ X.S0 i) ∧
    ∀ P, P ∉ X.S0 i → algebraMap (X.O i) (Kbar X i) (X.Xv i lam P) * ι (val χ P : ℂ) = 1

def IsValueTied : Prop :=
  ∀ i, X.NonzeroIndexPlace i → ∃ ι : ℂ →+* Kbar X i, (∀ x : D.LL0, ι (D.what₂.embLL (x : D.what₂.LL)) = toBar X i (X.emb0 i x)) ∧
    ∀ (lam : X.abelian₂ i) (s : ℕ), BlochKatoReduction.Gen.SOk X i lam s → IsValueCharAt X i (atSide X (X.sideL i lam) ι) lam s

def IsGalTied : Prop :=
  ∀ i, X.NonzeroIndexPlace i → ∃ (e : FractionRing (X.O0 i) →+* Qbar (X.l i)) (ι : Qbar (X.l i) ≃+* ℂ)
    (art : Ideles D.host.E →* Gab D.host.E N.Om), IsGlobalArtin art ∧
    (∀ z : ℤ_[X.l i], e (algebraMap (X.O0 i) _ (algebraMap ℤ_[X.l i] (X.O0 i) z)) =
      algebraMap ℚ_[X.l i] (Qbar (X.l i)) (z : ℚ_[X.l i])) ∧
    (∀ x : D.LL0, ι (e (X.emb0 i x)) = D.what₂.embLL (x : D.what₂.LL)) ∧
    ∀ (lam : X.abelian₂ i) (s : ℕ), BlochKatoReduction.Gen.SOk X i lam s →
      ∃ (I : Type) (_ : Fintype I) (φ : I → D.host.E →+* ℂ) (κ : I → ℕ) (𝔣 : Ideal (OF D.host.E)) (χ : HChar D.host.E)
        (n : (D.host.E →+* ℂ) → ℤ) (r : G D.host.E N.Om →* (X.O0 i)ˣ),
        IsHostDatum D.host φ s κ 𝔣 χ ∧ (∀ P, (below P).asIdeal ∣ 𝔣 → P ∈ X.S0 i) ∧
        GlobalTheory.GalChar.IsGal art e (GlobalTheory.GalChar.sideIso ι (X.sideL i lam)) χ n r ∧
        X.lamG i lam = (Units.map (algebraMap (X.O0 i) (X.O i)).toMonoidHom).comp r

variable {X}

theorem isValueTied_of_isToricElt (h : IsToricElt X) : IsValueTied X := fun i hi =>
  let ⟨ι, h1, h2⟩ := h i hi
  ⟨ι, h1, fun lam s hs =>
    let ⟨I, j, φ, κ, 𝔣, χ, _, a, b, c, _⟩ := h2 lam s hs
    ⟨I, j, φ, κ, 𝔣, χ, a, b, c⟩⟩

theorem toBar_algebraMap (i : X.Tw) (a : X.O0 i) :
    toBar X i (algebraMap (X.O0 i) _ a) = algebraMap (X.O i) (Kbar X i) (algebraMap (X.O0 i) (X.O i) a) := by
  rw [toBar, RingHom.comp_apply, IsFractionRing.lift_algebraMap]
  rfl

theorem IsGalTied.isValueTied (h : IsGalTied X) : IsValueTied X := by
  intro i hi
  obtain ⟨e, ι, art, ha, he, hι, hl⟩ := h i hi
  let _ : Algebra (FractionRing (X.O0 i)) (Qbar (X.l i)) := e.toAlgebra
  let _ : Algebra (FractionRing (X.O0 i)) (Kbar X i) := (toBar X i).toAlgebra
  have : Algebra.IsAlgebraic (FractionRing (X.O0 i)) (Qbar (X.l i)) := ⟨fun x => by
    have h1 : IsAlgebraic ℤ_[X.l i] x :=
      (IsFractionRing.isAlgebraic_iff ℤ_[X.l i] ℚ_[X.l i] _).2 (Algebra.IsAlgebraic.isAlgebraic x)
    refine h1.ringHom_of_comp_eq ((algebraMap (X.O0 i) _).comp (algebraMap ℤ_[X.l i] (X.O0 i))) (RingHom.id _)
      (fun a b hab => ?_) (RingHom.ext he)
    have := congrArg e hab
    rw [RingHom.comp_apply, RingHom.comp_apply, he, he] at this
    exact Subtype.ext ((algebraMap ℚ_[X.l i] (Qbar (X.l i))).injective this)⟩
  let J : Qbar (X.l i) →ₐ[FractionRing (X.O0 i)] Kbar X i := IsAlgClosed.lift
  have hJ : ∀ x, J (e x) = toBar X i x := J.commutes
  refine ⟨J.toRingHom.comp ι.symm.toRingHom, fun x => ?_, fun lam s hs => ?_⟩
  · rw [← hι, ← hJ]
    exact congrArg J (ι.symm_apply_apply _)
  obtain ⟨I, _, φ, κ, 𝔣, χ, n, r, hD, h𝔣, hr, hG⟩ := hl lam s hs
  refine ⟨I, inferInstance, φ, κ, 𝔣, χ, hD, h𝔣, fun P hP => ?_⟩
  obtain ⟨σ, hσ⟩ := exists_isFrob (N.plOm.2 P)
  have hu : χ.UnrAt P := by
    have e := (hD.2.2.2.2.2.2.2.2 _ P (over_below P)).2 (Finset.notMem_empty _)
    rwa [expIn, multiplicity_eq_zero.2 fun h => hP (h𝔣 P h), expAt_zero_iff] at e
  have h1 := hr.frob ha (Or.inl fun h => hP (X.twistExcludedPlaces_contains_residueChar i h)) hu (N.plOm.2 P) hσ
  have h2 : ∀ b x, atSide X b (J.toRingHom.comp ι.symm.toRingHom) (GlobalTheory.GalChar.sideIso ι b x) = J x := fun b x => by
    cases b
    · show J (ι.symm (starRingEnd ℂ (starRingEnd ℂ (ι x)))) = _
      rw [Complex.conj_conj, ι.symm_apply_apply]
    · exact congrArg J (ι.symm_apply_apply x)
  have h3 := congrArg (atSide X (X.sideL i lam) (J.toRingHom.comp ι.symm.toRingHom)) h1
  rw [h2, map_inv₀, GlobalTheory.GalChar.toQ, RingHom.comp_apply, hJ, toBar_algebraMap] at h3
  rw [X.Xv_def i lam P hP σ hσ, hG]
  exact (congrArg (· * _) h3).trans (inv_mul_cancel₀ ((map_ne_zero _).2 (Units.ne_zero _)))

end GlobalTheory.ToricRational
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IteratedColumnTransformEqGlobalWhittakerStatement
section
open NumberField Matrix GlobalTheory.CuspRep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iteratedColumnTransform_eq_globalWhittaker : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (F : GA E a → ℂ), 0 < a → Continuous F → (∀ (γ : GL (Fin a) E) (g : GA E a), F (ratGL E a γ * g) = F g) → GlobalTheory.CuspGeneric.whit (Circle.coeHom.compAddChar (GroundTheory.Global.adelicChar E)) (a - 1) F = GlobalTheory.JSW.whit F := by
  first | exact @GlobalTheory.CuspGeneric.WhitEq.whit_eq_whittaker | exact GlobalTheory.CuspGeneric.WhitEq.whit_eq_whittaker | (intros; apply GlobalTheory.CuspGeneric.WhitEq.whit_eq_whittaker <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeHomLiftsBreuilKisinDescentHom
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.BKGal.PackMap

section General

variable {l : ℕ} [hl : Fact l.Prime] {a : ℕ} [NeZero a] {e : ℕ} [NeZero e]
  {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
  [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K]
  {t : Wq l a →ₐ[ℤ_[l]] O} {ϖ : PiSys l e}
  {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  {G : Type} [Group G] [TopologicalSpace G]

theorem latW_TWact {T T' : LocLat G ℚ_[l] K O} (f : LatHom T.L T'.L) (s : GQ l) (g : G)
    (y : TW (OW l O) T) :
    latW f (TWact (galOW O s) T g y) = TWact (galOW O s) T' g (latW f y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul w x =>
    simp only [latW, TWact, TensorProduct.map_tmul]
    congr 1
    exact Subtype.ext (f.equiv g x)
  | add x y hx hy => simp only [map_add, hx, hy]

theorem homW_act {P : PhiMod O K l e a ι} {Q : PhiMod O K l e a κ} {T T' : LocLat G ℚ_[l] K O}
    {I : Ident t ϖ P T} {I' : Ident t ϖ Q T'} {f : LatHom T.L T'.L} {F : BK.Hom P Q}
    (h : IsMapOf I I' f F) (s : GQ l) (g : G) (v : ι → OW l O) :
    homW t ϖ F (I.act s g v) = I'.act s g (homW t ϖ F v) :=
  I'.j.injective (by rw [h, I.j_act, latW_TWact, I'.j_act, h])

variable [TameDescentExponentData K l e a]

theorem app_act_of_cover {s : G →* GQ l} {η H η' H' : ℕ} {D₁ : BKDat O K l e a ι η H}
    {D₂ : BKDat O K l e a κ η' H'} {T₁ T₂ : LocLat G ℚ_[l] K O} (R₁ : GalDat t ϖ s D₁ T₁)
    (R₂ : GalDat t ϖ s D₂ T₂) {f : LatHom T₁.L T₂.L} {F : BK.Hom D₁.toPhiMod D₂.toPhiMod}
    (hF : IsMapOf R₁.I R₂.I f F) (hcov : ∀ γ : TameGal K l e a, ∃ g : G, Covers K t ϖ (s g) γ)
    (γ : TameGal K l e a) (v : Vec K a ι) :
    F.app (D₁.desc.act γ v) = D₂.desc.act γ (F.app v) := by
  have hb : ∀ i : ι, F.app (D₁.desc.act γ (bas i)) = D₂.desc.act γ (F.app (bas i)) := by
    intro i
    obtain ⟨g, hg⟩ := hcov γ
    have m0 : (bas i : Vec K a ι) ∈ D₁.M := PhiMod.bas_mem_M _ i
    have m1 : D₁.desc.act γ (bas i) ∈ D₁.M := D₁.desc.act_mem_M γ _ m0
    have m2 : F.app (bas i) ∈ D₂.M := F.app_mem_M m0
    have m3 : D₂.desc.act γ (F.app (bas i)) ∈ D₂.M := D₂.desc.act_mem_M γ _ m2
    have m4 : F.app (D₁.desc.act γ (bas i)) ∈ D₂.M := F.app_mem_M m1
    have e1 := R₁.desc g γ hg ⟨_, mem_ME_of_mem_M m0⟩ ⟨_, mem_ME_of_mem_M m1⟩ rfl
    have e2 := R₂.desc g γ hg ⟨_, mem_ME_of_mem_M m2⟩ ⟨_, mem_ME_of_mem_M m3⟩ rfl
    have h1 := homW_toW t ϖ F ⟨_, mem_ME_of_mem_M m1⟩
    have h2 := homW_toW t ϖ F ⟨_, mem_ME_of_mem_M m0⟩
    have key : toW t ϖ D₂.toPhiMod ⟨_, mem_ME_of_mem_M m4⟩ =
        toW t ϖ D₂.toPhiMod ⟨_, mem_ME_of_mem_M m3⟩ :=
      calc toW t ϖ D₂.toPhiMod ⟨_, mem_ME_of_mem_M m4⟩
          = homW t ϖ F (toW t ϖ D₁.toPhiMod ⟨_, mem_ME_of_mem_M m1⟩) := h1.symm
        _ = homW t ϖ F (R₁.I.act (s g) g (toW t ϖ D₁.toPhiMod ⟨_, mem_ME_of_mem_M m0⟩)) := by rw [e1]
        _ = R₂.I.act (s g) g (homW t ϖ F (toW t ϖ D₁.toPhiMod ⟨_, mem_ME_of_mem_M m0⟩)) :=
          homW_act hF _ _ _
        _ = R₂.I.act (s g) g (toW t ϖ D₂.toPhiMod ⟨_, mem_ME_of_mem_M m2⟩) := by rw [h2]
        _ = toW t ϖ D₂.toPhiMod ⟨_, mem_ME_of_mem_M m3⟩ := e2
    exact congrArg Subtype.val (toW_injective t ϖ _ key)
  rw [eq_sum_bas v, map_sum, map_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [D₁.desc.act_smul_tot, F.app_smul_tot, F.app_smul_tot, D₂.desc.act_smul_tot, hb]

end General

theorem main : GlobalTheory.Published.BhattScholzeCrystallineLattices → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e]
    (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (η H : ℕ) (T₁ T₂ : QLat LL)
    (P₁ : Pack a ϖ η H T₁) (P₂ : Pack a ϖ η H T₂) (f : LatHom T₁.L T₂.L),
    ∃ F : BKHom P₁.D P₂.D, IsMapOf P₁.R.I P₂.R.I f F.toHom := by
  intro BS l _ a e _ _ ϖ LL _ _ η H T₁ T₂ P₁ P₂ f
  let f' : LatHom (resF T₁ (ϖ.field a)).L (resF T₂ (ϖ.field a)).L :=
    ⟨f.f, fun _ x => f.equiv _ x, f.cont, f.T_le⟩
  obtain ⟨F, hF⟩ := GlobalTheory.BKReal.Full.main BS l a e _ _ (thetaW a LL) ϖ _ _ P₁.D.toPhiMod P₂.D.toPhiMod
    (resF T₁ (ϖ.field a)) (resF T₂ (ϖ.field a))
    (P₁.R.I.res (inclG (ϖ.field a)) (continuous_subtype_val.subtype_mk _))
    (P₂.R.I.res (inclG (ϖ.field a)) (continuous_subtype_val.subtype_mk _)) P₁.isBK P₂.isBK f'
  have hF' : IsMapOf P₁.R.I P₂.R.I f F := hF
  have hcov : ∀ γ : TameGal ↥LL.1 l e a, ∃ g : Gl l, Covers ↥LL.1 (thetaW a LL) ϖ (sQ l g) γ := fun γ => by
    obtain ⟨k, -, hc⟩ := (GlobalTheory.T.galois_eq_mul_kisinInf_tameSemidirect l a e ϖ LL).2.2.1 γ
    refine ⟨⟨k, ?_⟩, hc⟩
    show k ∈ (⊥ : IntermediateField ℚ_[l] (Om l)).fixingSubgroup
    rw [IntermediateField.fixingSubgroup_bot]
    trivial
  exact ⟨⟨F, app_act_of_cover P₁.R P₂.R hF' hcov⟩, hF'⟩

end GlobalTheory.BKGal.PackMap
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalRankinSelbergFactorConjTendstoOneNeZero
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.JSW Filter Topology Formalism.UG GlobalTheory.RSNonvan

namespace GlobalTheory.JSW

theorem locL_conj_tendsto_one_and_ne_zero : ∀ (q : ℕ) (A B : Multiset ℂˣ), 1 < q → (∀ α ∈ A, ‖(α : ℂ)‖ ^ 2 < (q : ℝ)) →
    (∀ β ∈ B, ‖(β : ℂ)‖ ^ 2 < (q : ℝ)) →
    Tendsto (fun x : ℝ => locL q A (B.map (Units.map (starRingEnd ℂ).toMonoidHom)) (x : ℂ)) (𝓝[>] 1)
      (𝓝 (locL q A (B.map (Units.map (starRingEnd ℂ).toMonoidHom)) 1)) ∧
    locL q A (B.map (Units.map (starRingEnd ℂ).toMonoidHom)) 1 ≠ 0 := by
  intro q A B hq hA hB
  set B' := B.map (Units.map (starRingEnd ℂ).toMonoidHom) with hB'
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  have hqr : (1 : ℝ) < q := by exact_mod_cast hq

  have key : ∀ p ∈ A ×ˢ B', (1 - (p.1 : ℂ) * p.2 * (q : ℂ) ^ (-(1 : ℂ))) ≠ 0 := by
    intro p hp
    rw [Multiset.mem_product] at hp
    obtain ⟨h1, h2⟩ := hp
    rw [hB', Multiset.mem_map] at h2
    obtain ⟨β, hβ, hpe⟩ := h2
    rw [← hpe]
    have ha := hA _ h1
    have hb := hB _ hβ
    have hnb : ‖((Units.map (starRingEnd ℂ).toMonoidHom β : ℂˣ) : ℂ)‖ = ‖(β : ℂ)‖ := by
      simp [Units.coe_map]
    have hprod : ‖(p.1 : ℂ)‖ * ‖(β : ℂ)‖ < q := by
      have h0 : 0 ≤ ‖(p.1 : ℂ)‖ * ‖(β : ℂ)‖ := by positivity
      by_contra hc
      push_neg at hc
      have : (q : ℝ) * q ≤ (‖(p.1 : ℂ)‖ * ‖(β : ℂ)‖) * (‖(p.1 : ℂ)‖ * ‖(β : ℂ)‖) :=
        mul_le_mul hc hc (by positivity) h0
      have h3 : (‖(p.1 : ℂ)‖ * ‖(β : ℂ)‖) * (‖(p.1 : ℂ)‖ * ‖(β : ℂ)‖) = ‖(p.1 : ℂ)‖ ^ 2 * ‖(β : ℂ)‖ ^ 2 := by ring
      have h4 : ‖(p.1 : ℂ)‖ ^ 2 * ‖(β : ℂ)‖ ^ 2 < (q : ℝ) * q :=
        mul_lt_mul'' ha hb (by positivity) (by positivity)
      linarith
    intro h0
    have hz : (p.1 : ℂ) * ((Units.map (starRingEnd ℂ).toMonoidHom β : ℂˣ) : ℂ) * (q : ℂ) ^ (-(1 : ℂ)) = 1 := by
      linear_combination -h0
    have hn := congrArg norm hz
    rw [Complex.cpow_neg_one, norm_mul, norm_mul, hnb, norm_inv, Complex.norm_natCast, norm_one] at hn
    have hqpos : (0 : ℝ) < q := by linarith
    rw [mul_inv_eq_one₀ hqpos.ne'] at hn
    linarith
  constructor
  · have hc : ∀ p ∈ A ×ˢ B', Tendsto (fun x : ℝ => (1 - (p.1 : ℂ) * p.2 * (q : ℂ) ^ (-(x : ℂ)))⁻¹) (𝓝[>] 1)
        (𝓝 ((1 - (p.1 : ℂ) * p.2 * (q : ℂ) ^ (-((1 : ℝ) : ℂ)))⁻¹)) := by
      intro p hp
      apply Tendsto.mono_left _ nhdsWithin_le_nhds
      apply ContinuousAt.tendsto
      apply ContinuousAt.inv₀
      · apply ContinuousAt.sub continuousAt_const
        apply ContinuousAt.mul continuousAt_const
        apply ContinuousAt.const_cpow
        · exact (Complex.continuous_ofReal.neg).continuousAt
        · exact Or.inl hq0
      · simpa using key p hp
    have := tendsto_multiset_prod (A ×ˢ B') hc
    simpa [locL] using this
  · unfold locL
    apply Multiset.prod_ne_zero
    rw [Multiset.mem_map]
    rintro ⟨p, hp, h⟩
    exact inv_ne_zero (key p hp) h
end GlobalTheory.JSW
end

