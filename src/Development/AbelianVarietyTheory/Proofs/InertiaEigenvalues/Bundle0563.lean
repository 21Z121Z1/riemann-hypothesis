import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0352
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0422
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0489
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0492
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0545
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0548
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0432
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0476
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0003
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RestrictJumps
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalWdSpace
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0549
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0478
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0261
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0447
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0238
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0015
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KummerNotCoboundary
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsLogAExtends
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaBdRPlusSurjectiveKerUnitsEquivariant
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0500
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinBetaUniqueModEPow
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0434
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0555
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0375
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineLatticeFrobeniusRationalColumns
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

namespace GlobalTheory.BSP.FrobRational

theorem core {S A D D' : Type} [CommRing S] [IsDomain S] [CommRing A] [IsDomain A] [CommRing D] [CommRing D']
    (ev : S →+* A) (t : S →+* D) (i : A →+* D') (j : D →+* D') (hi : Function.Injective i)
    (hj : ∀ a, j (t a) = i (ev a)) (φ : A →+* A) (Φ : D' →+* D') (Ψ : D →+* D)
    (hΦ : ∀ a, Φ (i a) = i (φ a)) (hΨ : ∀ x, Φ (j x) = j (Ψ x))
    (disj : ∀ (x y : A) (f g : D), g ≠ 0 → y ≠ 0 → i x * j g = i y * j f →
      ∃ δ a : S, δ ≠ 0 ∧ ev δ * x = ev a * y)
    {d : ℕ} (lam : S) (hlam : lam ≠ 0) (W : Matrix (Fin d) (Fin d) D') (B : Matrix (Fin d) (Fin d) S)
    (hW : i (ev lam) • W.map Φ = W * B.map (i.comp ev))
    (Y : Matrix (Fin d) (Fin d) A) (Z : Matrix (Fin d) (Fin d) D) (hY : Y.det ≠ 0)
    (hYZ : W * Z.map j = Y.map i) :
    ∃ (δ : S) (A1 : Matrix (Fin d) (Fin d) S), δ ≠ 0 ∧ ev δ • Y.map φ = Y * A1.map ev := by
  classical
  set x : Matrix (Fin d) (Fin d) D := B.map t * Z.map Ψ with hx
  set P : Matrix (Fin d) (Fin d) A := ev lam • Y.map φ with hP
  have hPx : P.map i = W * x.map j := by
    have h1 : (Y.map φ).map i = (Y.map i).map Φ := by ext a b; simp [hΦ]
    have h2 : (Z.map j).map Φ = (Z.map Ψ).map j := by ext a b; simp [hΨ]
    have h3 : (B.map t).map j = B.map (i.comp ev) := by ext a b; simp [hj]
    have h4 : P.map i = i (ev lam) • (Y.map φ).map i := by ext a b; simp [hP]
    rw [h4, h1, ← hYZ, Matrix.map_mul, ← Matrix.smul_mul, hW, h2, hx, Matrix.map_mul, h3, Matrix.mul_assoc]
  have hdet : W.det * j Z.det = i Y.det := by
    rw [RingHom.map_det, RingHom.map_det, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, ← hYZ, Matrix.det_mul]
  have hZ : Z.det ≠ 0 := fun h => hY (hi (by rw [← hdet, h, map_zero, mul_zero, map_zero]))
  have hadjY : (Y.adjugate).map i = (Y.map i).adjugate := RingHom.map_adjugate i Y
  have hadjZ : (Z.adjugate).map j = (Z.map j).adjugate := RingHom.map_adjugate j Z
  have key : (Y.adjugate * P).map i = W.det • (Z.adjugate * x).map j := by
    rw [Matrix.map_mul, Matrix.map_mul, hadjY, hadjZ, hPx, ← hYZ, Matrix.adjugate_mul_distrib, Matrix.mul_assoc,
      ← Matrix.mul_assoc W.adjugate, Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul]
  have hent : ∀ p : Fin d × Fin d, ∃ δ a : S, δ ≠ 0 ∧ ev δ * (Y.adjugate * P) p.1 p.2 = ev a * Y.det := by
    intro p
    refine disj _ _ ((Z.adjugate * x) p.1 p.2) Z.det hZ hY ?_
    have h := congrFun (congrFun key p.1) p.2
    rw [Matrix.map_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul] at h
    rw [h, ← hdet]; ring
  choose δ a hδ ha using hent
  refine ⟨(∏ p, δ p) * lam, Matrix.of fun r c => (∏ p ∈ Finset.univ.erase (r, c), δ p) * a (r, c),
    mul_ne_zero (Finset.prod_ne_zero_iff.2 fun p _ => hδ p) hlam, ?_⟩
  have h5 : ev (∏ p, δ p) • (Y.adjugate * P) =
      Y.det • (Matrix.of fun r c => (∏ p ∈ Finset.univ.erase (r, c), δ p) * a (r, c)).map ev := by
    ext r c
    rw [Matrix.smul_apply, Matrix.smul_apply, Matrix.map_apply, Matrix.of_apply, smul_eq_mul, smul_eq_mul,
      ← Finset.prod_erase_mul _ _ (Finset.mem_univ (r, c)), map_mul, map_mul, mul_assoc, ha (r, c)]
    ring
  have h6 := congrArg (fun M => Y * M) h5
  simp only [Matrix.mul_smul] at h6
  rw [← Matrix.mul_assoc, Matrix.mul_adjugate, Matrix.smul_mul, Matrix.one_mul, smul_comm] at h6
  ext r c
  have h7 := congrFun (congrFun h6 r) c
  rw [Matrix.smul_apply, Matrix.smul_apply Y.det, smul_eq_mul, smul_eq_mul] at h7
  rw [← mul_left_cancel₀ hY h7, hP, smul_smul, map_mul]

theorem isDiscMap_comp {l : ℕ} {A A' A'' : Type} [CommRing A] [CommRing A'] [CommRing A''] {u : A} {u' : A'}
    {u'' : A''} {ρ ρ' ρ'' : ℝ≥0} {f : A →+* A'} {g : A' →+* A''} {F : Disc l u ρ →+* Disc l u' ρ'}
    {G : Disc l u' ρ' →+* Disc l u'' ρ''} (hF : IsDiscMap f F) (hG : IsDiscMap g G) :
    IsDiscMap (g.comp f) (G.comp F) :=
  ⟨fun a => by rw [RingHom.comp_apply, hF.ext, hG.ext, RingHom.comp_apply],
    fun x => (hG.norm_le _).trans (hF.norm_le x)⟩

theorem main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l) (hτ : bk.IsPer τ) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (hρ : ∀ g, IsUnit (ρ g)) (s : Seed bk d ρ τ) (Y1 : Matrix (Fin d) (Fin d) (Ainf l)) (Z1 : Matrix (Fin d) (Fin d) (bk.DS bk.ρ₀)), Y1.det ≠ 0 → (∀ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap bk.ev j → s.W * Z1.map j = Y1.map bk.iA) → ∃ (δ : bk.S) (A1 : Matrix (Fin d) (Fin d) (bk.S)), δ ≠ 0 ∧ bk.ev δ • Y1.map WittVector.frobenius = Y1 * A1.map bk.ev := by
  intro l hl K bk τ hτ d ρ hρ s Y1 Z1 hY hYZ
  have hl1 : (1 : ℝ≥0) < l := by exact_mod_cast hl.out.one_lt
  have h0 : 0 < bk.ρ₀ := NNReal.rpow_pos (zero_lt_one.trans hl1)
  have h1 : bk.ρ₀ < 1 := NNReal.rpow_lt_one_of_one_lt_of_neg hl1
    (neg_lt_zero.2 (one_div_pos.2 (Nat.cast_pos.2 bk.deg_pos)))
  have hpow : bk.ρ₀ ^ l ≤ bk.ρ₀ := pow_le_of_le_one h0.le h1.le hl.out.ne_zero
  obtain ⟨ι, ⟨TB⟩⟩ := GlobalTheory.T.ainf_adicTopologicalBasis_over_breuilKisin l K bk
  haveI : IsDomain (bk.DA bk.ρ₀) := (GlobalTheory.T.breuilKisin_ainfDisc_isDomain_norm_bounds l K bk bk.ρ₀ h0 h1).1
  have hi : Function.Injective bk.iA := (GlobalTheory.T.closedDisc_toDisc_injective_of_adicBasis l K bk _ bk.ev ι TB bk.ρ₀ h0 h1).1
  haveI : IsDomain (Ainf l) := hi.isDomain _
  obtain ⟨j, hj⟩ := exists_discMap_of_pow_dvd l _ _ bk.ev (X : bk.S) (bk.ev X) bk.ρ₀ bk.ρ₀ 1 h0
    (by rw [pow_one]) (by rw [pow_one])
  obtain ⟨Ψ, hΨ⟩ := exists_discMap_of_pow_dvd l _ _ (frobS l bk.a) (X : bk.S) (X : bk.S) bk.ρ₀ bk.ρ₀ l h0
    (by rw [frobS_X]) hpow
  obtain ⟨Φ, hΦ⟩ := exists_discMap_of_pow_dvd l _ _ (WittVector.frobenius : Ainf l →+* Ainf l) (bk.ev X) (bk.ev X)
    bk.ρ₀ bk.ρ₀ l h0 (by rw [← bk.ev_frob, frobS_X, map_pow]) hpow
  have hcomm : Φ.comp j = j.comp Ψ := by
    have e : (WittVector.frobenius : Ainf l →+* Ainf l).comp bk.ev = bk.ev.comp (frobS l bk.a) :=
      RingHom.ext fun x => (bk.ev_frob x).symm
    exact (isDiscMap_comp hj hΦ).unique (e ▸ isDiscMap_comp hΨ hj)
  have hlam : bk.iA (bk.ev ((l : bk.S) ^ (s.c₁ + s.c₂) * frobS l bk.a bk.E ^ s.N)) =
      (l : bk.DA bk.ρ₀) ^ (s.c₁ + s.c₂) * bk.iS (frobS l bk.a bk.E) ^ s.N := by
    simp only [map_mul, map_pow, map_natCast, RingHom.comp_apply]
  have hu : IsUnit (bk.iS (frobS l bk.a bk.E)) := by
    have h := (isUnit_toDisc_frobS_E l K bk).map j
    rwa [hj.ext] at h
  have hne : (l : bk.S) ^ (s.c₁ + s.c₂) * frobS l bk.a bk.E ^ s.N ≠ 0 := fun h => by
    rw [h, map_zero, map_zero] at hlam
    exact (((isUnit_l_disc l _ _).pow _).mul (hu.pow _)).ne_zero hlam.symm
  exact core bk.ev (toDisc l (X : bk.S) bk.ρ₀) bk.iA j hi hj.ext WittVector.frobenius Φ Ψ hΦ.ext
    (fun x => RingHom.congr_fun hcomm x) (GlobalTheory.T.ainf_closedDisc_linearDisjoint_over_powerSeries l K bk _ bk.ev ι TB j hj) _ hne s.W _
    (by rw [hlam]; exact GlobalTheory.T.discPeriods_map_frobenius_eq_mul l K bk τ hτ d ρ hρ s Φ hΦ) Y1 Z1 hY (hYZ j hj)

end GlobalTheory.BSP.FrobRational
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineLatticeRationalInColumns
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

namespace GlobalTheory.BSP

private theorem map_mulVec_fun {R S : Type} [CommRing R] [CommRing S] {d : ℕ} (f : R →+* S)
    (M : Matrix (Fin d) (Fin d) R) (v : Fin d → R) :
    (fun a => f ((M *ᵥ v) a)) = M.map f *ᵥ fun a => f (v a) := funext fun a => RingHom.map_mulVec f M v a

private theorem det_map_ringHom {R S : Type} [CommRing R] [CommRing S] {d : ℕ} (f : R →+* S)
    (M : Matrix (Fin d) (Fin d) R) : (M.map f).det = f M.det := (RingHom.map_det f M).symm

private theorem adjugate_map_ringHom {R S : Type} [CommRing R] [CommRing S] {d : ℕ} (f : R →+* S)
    (M : Matrix (Fin d) (Fin d) R) : (M.map f).adjugate = M.adjugate.map f := (RingHom.map_adjugate f M).symm

theorem rational_in_columns : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l) (hτ : bk.IsPer τ) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (hρ : ∀ g, IsUnit (ρ g)) (s : Seed bk d ρ τ) (Y1 : Matrix (Fin d) (Fin d) (Ainf l)) (Z1 : Matrix (Fin d) (Fin d) (bk.DS bk.ρ₀)), (Y1.map (inclW l)).det ≠ 0 → (∀ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap bk.ev j → s.W * Z1.map j = Y1.map bk.iA) → ∀ y, (fun y : Fin d → Ainf l => ∃ x : Fin d → bk.DS bk.ρ₀, ∀ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap bk.ev j → s.W *ᵥ (fun a => j (x a)) = fun a => bk.iA (y a)) y → ∃ (δ : bk.S) (c : Fin d → bk.S), δ ≠ 0 ∧ (fun a => bk.ev δ * y a) = Y1 *ᵥ fun a => bk.ev (c a) := by
  intro l _ K bk τ hτ d ρ hρ s Y1 Z1 hdet hWZ y hy
  obtain ⟨x, hx⟩ := hy
  have hl : (1 : ℝ≥0) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have he : (0 : ℝ) < bk.Ep.natDegree := by exact_mod_cast bk.deg_pos
  have hρ0 : 0 < bk.ρ₀ := NNReal.rpow_pos (zero_lt_one.trans hl)
  have hρ1 : bk.ρ₀ < 1 := NNReal.rpow_lt_one_of_one_lt_of_neg hl (by simp only [Left.neg_neg_iff]; positivity)
  obtain ⟨ι, ⟨TB⟩⟩ := GlobalTheory.T.ainf_adicTopologicalBasis_over_breuilKisin l K bk
  have hinj : Function.Injective bk.iA := (GlobalTheory.T.closedDisc_toDisc_injective_of_adicBasis l K bk (Ainf l) bk.ev ι TB bk.ρ₀ hρ0 hρ1).1
  have hXn : ‖toDisc l (bk.ev X) bk.ρ₀ (bk.ev X)‖ ≤ bk.ρ₀ := by
    simpa using norm_toDisc_pow_le (l := l) (u := bk.ev X) (ρ := bk.ρ₀) 1 hρ0
  let j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀ := Disc.map (l := l) (u := (X : bk.S)) (ρ := bk.ρ₀) bk.ev hXn
  have hj : IsDiscMap bk.ev j := isDiscMap_map _ _
  have hWZj := hWZ j hj
  have hxj := hx j hj
  have hD : Y1.det ≠ 0 := by
    intro h; apply hdet; rw [det_map_ringHom, h, map_zero]
  have hdetA : bk.iA Y1.det = (s.W).det * j Z1.det := by
    rw [← det_map_ringHom, ← hWZj, det_mul, det_map_ringHom]
  have hΔ : Z1.det ≠ 0 := by
    intro h; apply hD; apply hinj; rw [hdetA, h, map_zero, mul_zero, map_zero]
  have h1 : Y1.map bk.iA *ᵥ (fun a => j ((Z1.adjugate *ᵥ x) a)) = j Z1.det • fun a => bk.iA (y a) := by
    rw [map_mulVec_fun j, ← hWZj, ← adjugate_map_ringHom, mulVec_mulVec, Matrix.mul_assoc, mul_adjugate,
      det_map_ringHom, Matrix.mul_smul, Matrix.mul_one, smul_mulVec, hxj]
  have h2 : bk.iA Y1.det • (fun a => j ((Z1.adjugate *ᵥ x) a)) =
      j Z1.det • fun a => bk.iA ((Y1.adjugate *ᵥ y) a) := by
    have h3 : (Y1.map bk.iA).adjugate *ᵥ (Y1.map bk.iA *ᵥ (fun a => j ((Z1.adjugate *ᵥ x) a))) =
        (Y1.map bk.iA).adjugate *ᵥ (j Z1.det • fun a => bk.iA (y a)) := by rw [h1]
    rw [mulVec_mulVec, adjugate_mul, det_map_ringHom, smul_mulVec, one_mulVec, mulVec_smul,
      adjugate_map_ringHom, ← map_mulVec_fun] at h3
    exact h3
  have key : ∀ a, ∃ δ c : bk.S, δ ≠ 0 ∧ bk.ev δ * (Y1.adjugate *ᵥ y) a = bk.ev c * Y1.det := fun a =>
    GlobalTheory.T.ainf_closedDisc_linearDisjoint_over_powerSeries l K bk (Ainf l) bk.ev ι TB j hj ((Y1.adjugate *ᵥ y) a) Y1.det ((Z1.adjugate *ᵥ x) a) Z1.det
      hΔ hD (by
        have h4 := congrFun h2 a
        simp only [Pi.smul_apply, smul_eq_mul] at h4
        calc _ = j Z1.det * bk.iA ((Y1.adjugate *ᵥ y) a) := mul_comm _ _
          _ = _ := h4.symm)
  choose δs cs hδ hc using key
  refine ⟨∏ a, δs a, fun a => cs a * ∏ b ∈ Finset.univ.erase a, δs b,
    Finset.prod_ne_zero_iff.2 fun a _ => hδ a, ?_⟩
  have hw : ∀ a, bk.ev (∏ b, δs b) * (Y1.adjugate *ᵥ y) a =
      Y1.det * bk.ev (cs a * ∏ b ∈ Finset.univ.erase a, δs b) := by
    intro a
    rw [← Finset.mul_prod_erase Finset.univ δs (Finset.mem_univ a), map_mul, map_mul, mul_comm (bk.ev (δs a)),
      mul_assoc, hc a]
    ring
  have hYw : Y1 *ᵥ (Y1.adjugate *ᵥ y) = Y1.det • y := by
    rw [mulVec_mulVec, mul_adjugate, smul_mulVec, one_mulVec]
  have hcancel : Y1.det • (fun a => bk.ev (∏ b, δs b) * y a) =
      Y1.det • (Y1 *ᵥ fun a => bk.ev (cs a * ∏ b ∈ Finset.univ.erase a, δs b)) := by
    calc Y1.det • (fun a => bk.ev (∏ b, δs b) * y a) = bk.ev (∏ b, δs b) • (Y1 *ᵥ (Y1.adjugate *ᵥ y)) := by
          rw [hYw]; funext a; simp only [Pi.smul_apply, smul_eq_mul]; ring
      _ = Y1 *ᵥ (bk.ev (∏ b, δs b) • (Y1.adjugate *ᵥ y)) := by rw [mulVec_smul]
      _ = Y1 *ᵥ (Y1.det • fun a => bk.ev (cs a * ∏ b ∈ Finset.univ.erase a, δs b)) := by
          congr 1; funext a; simp only [Pi.smul_apply, smul_eq_mul]; exact hw a
      _ = _ := by rw [mulVec_smul]
  exact smul_right_injective _ hD hcancel

end GlobalTheory.BSP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallinePotentialFamilyStatement
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition GlobalTheory.Pass.LocDual
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystalline_potential_family : ∀ (D : D7), FontaineAtPlacesOverL (D := D) → PotDRL D.loc → admBK (D := D) → ∀ (i : D.nd.Loc)
    (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))), GoodR D.nd i r →
    ∀ (Xs : Set (D.nd.X i)) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)),
      finrank ℚ_[D.nd.l i] (Br.Kw D.nbr i w hw) = 1 → ∀ n : ℕ,
      PotFam i w hw (fun x : ↥Xs => rTwO D.nd i r x) n →
    ∀ (k : ℕ) (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (hSub : SubTw i r Xs M),
      IsDR (Br.PD D.loc D.nbr i w hw) (locU i w hw M hSub.1).ρ ∧
      ∃ (U' : GRep (Br.G D.nbr i w hw) ℚ_[D.nd.l i] (Br.LL D.nbr i w hw) (Br.OLL D.nbr i w hw))
        (PU : (locU i w hw M hSub.1).V →ₗ[Br.LL D.nbr i w hw] U'.V →ₗ[Br.LL D.nbr i w hw] Br.LL D.nbr i w hw),
        IsSubFam (fun x : ↥Xs => Br.loc D.nbr i w hw (rDuO D.nd i r x)) U' ∧
        DualLatLe (Br.PD D.loc D.nbr i w hw) (locU i w hw M hSub.1) U' (Br.locLat D.nbr i w hw M) PU (2 * k) := by
  first | exact @GlobalTheory.Pass.LocDualU.main | exact GlobalTheory.Pass.LocDualU.main | (intros; apply GlobalTheory.Pass.LocDualU.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicCocycleMemImageOfCrystallineStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices GlobalTheory.NL.CrystallineBase
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cyclotomicCocycle_mem_image_of_crystalline : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (T : Lt K LL), IsCrys ((D.loc l).PD K) T.ρ → ∀ (c : ↥(latticeCocycles (resLat T ((HW l).W K s LL h).GKs))) (b : TW (RW LL) T) (lam : ↥((HW l).W K s LL h).GKs →* Multiplicative ℤ_[l]), Continuous lam → (∀ g, lam g = 1 → ((HW l).W K s LL h).resΓ (g : ↥(GK K)) = 1) → (∀ g : ↥((HW l).W K s LL h).GKs, ((HW l).W K s LL h).resΓ (g : ↥(GK K)) = 1 → Zf (D.locA l) T ((HW l).W K s LL h).GKs c b g = 0) → ∀ g₁ : ↥((HW l).W K s LL h).GKs, lam g₁ = Multiplicative.ofAdd 1 → ∀ z₁ ∈ aN ((HW l).W K s LL h) T ((HW l).W K s LL h).X, Zf (D.locA l) T ((HW l).W K s LL h).GKs c b g₁ = ((F l).E K s LL h).tie.jD T z₁ → ∀ g : ↥((HW l).W K s LL h).GKs, ∃ z ∈ aN ((HW l).W K s LL h) T ((HW l).W K s LL h).X, Zf (D.locA l) T ((HW l).W K s LL h).GKs c b g = ((F l).E K s LL h).tie.jD T z := by
  first | exact @GlobalTheory.NL.ZVal.zval | exact GlobalTheory.NL.ZVal.zval | (intros; apply GlobalTheory.NL.ZVal.zval <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamExistsHodgeTateEigenbasisStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.deRham_exists_hodgeTate_eigenbasis : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (m : ℕ) (r' : ↥(GK K) →* Matrix.GeneralLinearGroup (Fin m) ↥LL.1), let ρ : Representation ↥LL.1 ↥(GK K) (Fin m → ↥LL.1) := ((Matrix.toLinAlgEquiv' : Matrix (Fin m) (Fin m) ↥LL.1 ≃ₐ[↥LL.1] _) : _ →* _).comp ((Units.coeHom _).comp r'); Module.finrank ↥LL.1 ↥(DdR (P.PD K) ρ) = Module.finrank ℚ_[l] ↥K.1 * m → (∀ (σ : ↥K.1 →ₐ[ℚ_[l]] Om l) (x : ↥K.1), σ x ∈ LL.1) → ∀ τ' : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1, (∀ x : ↥K.1, ((τ' x : ↥LL.1) : Om l) = (x : Om l)) → ∀ (K' : FinExt l), K.1 ≤ K'.1 → LL.1 ≤ K'.1 → ∃ (Pm : Matrix.GeneralLinearGroup (Fin m) ℂ_[l]) (k : Fin m → ℤ), (∀ a : ℤ, ((Multiset.map k Finset.univ.val).count a : ℤ) = multV (P.PD K) ρ τ' a) ∧ ∀ g : ↥(GK K), (g : GQ l) ∈ GK K' → (r' g : Matrix (Fin m) (Fin m) ↥LL.1).map (fun x => (((x : ↥LL.1) : Om l) : ℂ_[l])) * (Pm : Matrix (Fin m) (Fin m) ℂ_[l]).map (Per.σC (g : GQ l)) = (Pm : Matrix (Fin m) (Fin m) ℂ_[l]) * Matrix.diagonal (fun i => ((((P.χQ (g : GQ l)) ^ (-k i) : ℚ_[l]ˣ) : ℚ_[l]) : ℂ_[l])) := by
  first | (exact @GlobalTheory.HTBasis.htc_basis) | (exact GlobalTheory.HTBasis.htc_basis) | (intros; apply GlobalTheory.HTBasis.htc_basis  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DualExponentialImageContainsLatticeStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dualExponential_image_contains_lattice : ∀ (D : Formalism.BasicNotions.D7) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ), Lev l s → ∀ e : ℕ, ∀ α : Om l, α ∈ Ks K s → ‖α‖ ≤ 1 → ∃ z : GQ l → ℚ_[l], (∀ σ ∈ Gj K s, ‖z σ‖ ≤ 1) ∧ ExpStar D.loc (Gj K s) e z ((l : Om l) ^ (betaE l s e) * α) := by
  first | exact @GlobalTheory.ExpImage.expStar_image | exact GlobalTheory.ExpImage.expStar_image | (intros; apply GlobalTheory.ExpImage.expStar_image <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DualLatticeRankBoundStatement
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystalline_over_extension : ∀ (D : D7), FontaineAtPlacesOverL (D := D) → admBK (D := D) → PotDRL D.loc → ∀ (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)), finrank ℚ_[D.nd.l i] (Br.Kw D.nbr i w hw) = 1 → ∀ {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (hM : Continuous fun g => M g) (K' : FinExt (D.nd.l i)) (h : (D.nbr i w hw).Kw.1 ≤ K'.1), IsCrys ((D.loc (D.nd.l i)).PD K') ((GlobalTheory.Pass.LocDirect.ModuleGaloisRepresentation i w hw M hM).ρ.comp (Subgroup.inclusion (GK_le h))) → ∃ (U' : GRep (Br.G D.nbr i w hw) ℚ_[D.nd.l i] (Br.LL D.nbr i w hw) (Br.OLL D.nbr i w hw)), letI := U'.modO; letI := U'.towO; ∃ (LT' : Lattice (O := Br.OLL D.nbr i w hw) U'.ρ) (PU : (GlobalTheory.Pass.LocDirect.ModuleGaloisRepresentation i w hw M hM).V →ₗ[Br.LL D.nbr i w hw] U'.V →ₗ[Br.LL D.nbr i w hw] Br.LL D.nbr i w hw), IsDualLat1 (Br.PD D.loc D.nbr i w hw) (Br.locLat D.nbr i w hw M) LT' PU ∧ finrank (Br.OLL D.nbr i w hw) ↥(latticeFiniteCohomology (Br.PD D.loc D.nbr i w hw) LT') ≤ k := by
  first | exact @GlobalTheory.Pass.LocDirect.dualLat_rank | exact GlobalTheory.Pass.LocDirect.dualLat_rank | (intros; apply GlobalTheory.Pass.LocDirect.dualLat_rank <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EisensteinApproxRootGaloisSubMemBdRFil
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP.RootGal

theorem sub_mem_of_eval_mem {R : Type*} [CommRing R] (J : Ideal R) (P : Polynomial R) (x y : R)
    (hx : P.eval x ∈ J) (hy : P.eval y ∈ J)
    (hu : ∀ k : R, IsUnit ((Polynomial.derivative P).eval x + k * (y - x))) : y - x ∈ J := by
  obtain ⟨k, hk⟩ := Polynomial.binomExpansion P x (y - x)
  have hxy : x + (y - x) = y := by ring
  rw [hxy] at hk
  have hmem : (y - x) * ((Polynomial.derivative P).eval x + k * (y - x)) ∈ J := by
    have e : (y - x) * ((Polynomial.derivative P).eval x + k * (y - x)) = P.eval y - P.eval x := by
      rw [hk]; ring
    rw [e]; exact J.sub_mem hy hx
  obtain ⟨v, hv⟩ := (hu k).exists_right_inv
  have e : y - x = (y - x) * ((Polynomial.derivative P).eval x + k * (y - x)) * v := by
    rw [mul_assoc, hv, mul_one]
  rw [e]; exact J.mul_mem_right _ hmem

variable {l : ℕ} [Fact l.Prime]

theorem ev_algebraMap (n : ℕ) (a : Per.AinfP l) :
    Per.ev l n (algebraMap (Per.AinfP l) (Per.BdRp l) a) = Ideal.Quotient.mk _ a :=
  GlobalTheory.RingIface.ev_alg l n a

theorem mem_filtration_of_dvd (n : ℕ) (a : Per.Ainf l) (ha : Per.θ l a = 0) (z : Per.BdRp l)
    (hz : aDp l a ^ n ∣ z) : z ∈ Per.FilP l n := by
  obtain ⟨w, rfl⟩ := hz
  have h2 : algebraMap (Per.Ainf l) (Per.AinfP l) a ∈ Per.kerP l := GlobalTheory.RingIface.alg_mem_kerP l ha
  rw [GlobalTheory.RingIface.mem_filtration_iff_mem_kerTheta_pow, map_mul, map_pow, aDp, RingHom.comp_apply, ev_algebraMap, ← map_pow,
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.pow_mem_pow h2 n), zero_mul]

end GlobalTheory.BSP.RootGal

open GlobalTheory.BSP.RootGal in

theorem GlobalTheory.BSP.approxRoot_gal_sub_mem_fil : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (n M : ℕ) (q : bk.S),
    bk.E ∣ q - (l : bk.S) ^ M * X →
    bk.E ^ n ∣ Polynomial.eval₂ PowerSeries.C q (bk.Ep.scaleRoots ((l : Wq l bk.a) ^ M)) →
    ∀ g : ↥(GK K), aDp l (Per.σA (g : GQ l) (bk.ev q) - bk.ev q) ∈ Per.FilP l n := by
  intro l _ K bk n M q hq hroot g
  have hP := GlobalTheory.MemLoc.thetaD_props l
  set h : bk.S →+* Per.BdRp l := (aDp l).comp bk.ev with hh
  set h' : bk.S →+* Per.BdRp l := (aDp l).comp ((Per.σA (g : GQ l)).comp bk.ev) with hh'
  set f : Wq l bk.a →+* Per.BdRp l := h.comp PowerSeries.C with hf
  have hf' : h'.comp PowerSeries.C = f := by
    refine RingHom.ext fun w => ?_
    simp only [hh', hf, hh, RingHom.comp_apply, bk.ev_C, bk.gal_w]
  have hE : Per.θ l (bk.ev bk.E) = 0 := by
    rw [← RingHom.mem_ker, ← bk.span_ev]; exact Ideal.mem_span_singleton_self _
  have hE' : Per.θ l (Per.σA (g : GQ l) (bk.ev bk.E)) = 0 := by rw [GlobalTheory.RingBasics.θ_σA, hE, map_zero]
  have hY : Polynomial.eval₂ f (h q) (bk.Ep.scaleRoots ((l : Wq l bk.a) ^ M)) ∈ Per.FilP l n := by
    refine mem_filtration_of_dvd n (bk.ev bk.E) hE _ ?_
    have h1 := map_dvd h hroot
    rw [Polynomial.hom_eval₂, map_pow] at h1
    exact h1
  have hY' : Polynomial.eval₂ f (h' q) (bk.Ep.scaleRoots ((l : Wq l bk.a) ^ M)) ∈ Per.FilP l n := by
    refine mem_filtration_of_dvd n (Per.σA (g : GQ l) (bk.ev bk.E)) hE' _ ?_
    have h1 := map_dvd h' hroot
    rw [Polynomial.hom_eval₂, map_pow, hf'] at h1
    exact h1
  set s : Per.BdRp l := f ((l : Wq l bk.a) ^ M) with hs
  have hs' : s = (l : Per.BdRp l) ^ M := by rw [hs, map_pow, map_natCast]
  have hsu : IsUnit s := hs' ▸ (isUnit_l_BdRp l).pow M
  obtain ⟨r, hr⟩ := hsu.exists_left_inv
  have hsy : ∀ z : Per.BdRp l, z = s * (r * z) := fun z => by rw [← mul_assoc, mul_comm s r, hr, one_mul]

  have hroot' : ∀ z : Per.BdRp l, Polynomial.eval₂ f z (bk.Ep.scaleRoots ((l : Wq l bk.a) ^ M)) ∈ Per.FilP l n →
      (bk.Ep.map f).eval (r * z) ∈ Per.FilP l n := by
    intro z hz
    rw [hsy z, hs, Polynomial.scaleRoots_eval₂_mul, ← hs] at hz
    have h1 := (Per.FilP l n).mul_mem_left (r ^ bk.Ep.natDegree) hz
    rwa [← mul_assoc, ← mul_pow, hr, one_pow, one_mul, ← Polynomial.eval_map] at h1

  have hθh : ∀ x : bk.S, Per.θD l (h x) = ((Per.θ l (bk.ev x) : OC l) : ℂ_[l]) := fun x => hP.2.2.2.1 _
  have hθdiff : Per.θD l (h' q - h q) = 0 := by
    rw [map_sub, hθh, show h' q = aDp l (Per.σA (g : GQ l) (bk.ev q)) from rfl, hP.2.2.2.1,
      GlobalTheory.BKLim.BetaUniq.theta_gal_ev bk g q, sub_self]
  have hθs : Per.θD l s ≠ 0 := (hsu.map (Per.θD l)).ne_zero
  have hθq : Per.θD l (h q) = Per.θD l s * Per.θD l (h X) := by
    obtain ⟨c, hc⟩ := hq
    have h1 : q = (l : bk.S) ^ M * X + bk.E * c := by rw [← hc]; ring
    rw [h1, map_add, map_mul, map_mul, map_add, map_mul, map_mul, hθh bk.E, hE, hs', map_pow, map_pow,
      map_natCast, map_natCast]
    simp
  have hθy : Per.θD l (r * h q) = Per.θD l (h X) := by
    have h1 : Per.θD l s * Per.θD l (r * h q) = Per.θD l s * Per.θD l (h X) := by
      rw [← map_mul, ← mul_assoc, mul_comm s r, hr, one_mul, hθq]
    exact mul_left_cancel₀ hθs h1
  have hder : Per.θD l ((Polynomial.derivative (bk.Ep.map f)).eval (r * h q)) ≠ 0 := by
    rw [Polynomial.derivative_map, Polynomial.eval_map, Polynomial.hom_eval₂, hθy, hf, ← RingHom.comp_assoc,
      show Per.θD l (h X) = ((Per.θD l).comp h) X from rfl, ← Polynomial.hom_eval₂, Polynomial.eval₂_C_X_eq_coe,
      RingHom.comp_apply, hθh]
    intro h0
    apply GlobalTheory.BKLim.ZNotRoot.theta_deriv_ne bk
    exact Subtype.ext h0
  have key := sub_mem_of_eval_mem (Per.FilP l n) (bk.Ep.map f) (r * h q) (r * h' q) (hroot' _ hY) (hroot' _ hY')
    (fun k => hP.2.2.1 _ (by
      rw [map_add, map_mul, ← mul_sub, map_mul, hθdiff, mul_zero, mul_zero, add_zero]; exact hder))
  rw [map_sub, show aDp l (Per.σA (g : GQ l) (bk.ev q)) = h' q from rfl, show aDp l (bk.ev q) = h q from rfl,
    hsy (h' q), hsy (h q), ← mul_sub]
  exact (Per.FilP l n).mul_mem_left s key
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EisensteinDivClosedDiscOfTopBasis
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem exists_discMap_of_map_eq (l : ℕ) [Fact l.Prime] {A A' : Type} [CommRing A] [CommRing A'] (f : A →+* A')
    (u : A) (u' : A') (ρ ρ' : ℝ≥0) (h0 : 0 < ρ') (hu : f u = u') (h : ρ' ≤ ρ) :
    ∃ F : Disc l u ρ →+* Disc l u' ρ', IsDiscMap f F := by
  have h1 : ‖toDisc l u' ρ' (f u)‖ ≤ ρ := by
    have := norm_toDisc_pow_le (l := l) (u := u') 1 h0
    rw [pow_one, pow_one] at this
    rw [hu]
    exact this.trans (by exact_mod_cast h)
  exact ⟨_, isDiscMap_map f h1⟩

theorem BK.rho_zero_pos {l : ℕ} [hl : Fact l.Prime] {K : FinExt l} (bk : BK K) : 0 < bk.ρ₀ :=
  NNReal.rpow_pos (Nat.cast_pos.2 hl.out.pos)

theorem norm_E_mul_of_topBasis (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (A : Type) [CommRing A]
    (s : bk.S →+* A) (ι : Type) (TB : TopBasis s bk.J ι) (ρ : ℝ≥0) (h0 : bk.ρ₀ ≤ ρ) (h1 : ρ < 1)
    (y : Disc l (s X) ρ) :
    ‖toDisc l (s X) ρ (s bk.E) * y‖ = (ρ : ℝ) ^ bk.Ep.natDegree * ‖y‖ := by
  have hρ : 0 < ρ := bk.rho_zero_pos.trans_le h0
  have hρ' : (0 : ℝ) < (ρ : ℝ) ^ bk.Ep.natDegree := pow_pos (by exact_mod_cast hρ) _
  obtain ⟨j, hj⟩ := exists_discMap_of_map_eq l s X (s X) ρ ρ hρ rfl le_rfl
  obtain ⟨cD, -, hmul, hle, -, -, hsup, -, -⟩ := GlobalTheory.T.closedDisc_coefficients_topologicallyFree l K bk A s ι TB ρ hρ h1 j hj
  have key : ∀ i, ‖cD i (toDisc l (s X) ρ (s bk.E) * y)‖ = (ρ : ℝ) ^ bk.Ep.natDegree * ‖cD i y‖ := fun i => by
    rw [← hj.ext, hmul, GlobalTheory.T.norm_eisenstein_mul_closedDisc_eq_rpow l K bk ρ h0 h1]
  refine le_antisymm (hsup _ _ (by positivity) fun i => ?_) ?_
  · rw [key]
    exact mul_le_mul_of_nonneg_left (hle i y) hρ'.le
  · rw [← le_div_iff₀' hρ']
    refine hsup _ _ (by positivity) fun i => ?_
    rw [le_div_iff₀' hρ', ← key]
    exact hle _ _

theorem E_dvd_of_topBasis (l : ℕ) [hl : Fact l.Prime] (K : FinExt l) (bk : BK K) (A : Type) [CommRing A]
    (s : bk.S →+* A) (ι : Type) (TB : TopBasis s bk.J ι) (ρ : ℝ≥0) (h0 : bk.ρ₀ ≤ ρ) (h1 : ρ < 1)
    (R : Disc l (s X) ρ →+* Disc l (s X) bk.ρ₀) (hR : IsDiscMap (RingHom.id A) R) (y : Disc l (s X) ρ)
    (hy : toDisc l (s X) bk.ρ₀ (s bk.E) ∣ R y) : toDisc l (s X) ρ (s bk.E) ∣ y := by
  have hρ₀ := bk.rho_zero_pos
  have hρ : 0 < ρ := hρ₀.trans_le h0
  have hρ' : (0 : ℝ) < (ρ : ℝ) ^ bk.Ep.natDegree := pow_pos (by exact_mod_cast hρ) _
  obtain ⟨j, hj⟩ := exists_discMap_of_map_eq l s X (s X) ρ ρ hρ rfl le_rfl
  obtain ⟨j₀, hj₀⟩ := exists_discMap_of_map_eq l s X (s X) bk.ρ₀ bk.ρ₀ hρ₀ rfl le_rfl
  obtain ⟨RS, hRS⟩ := exists_discMap_of_map_eq l (RingHom.id bk.S) X X ρ bk.ρ₀ hρ₀ rfl h0
  obtain ⟨cD, hc, hmul, hle, hnull, -, hsup, hex, -⟩ := GlobalTheory.T.closedDisc_coefficients_topologicallyFree l K bk A s ι TB ρ hρ h1 j hj
  obtain ⟨cD₀, hc₀, hmul₀, hle₀, -, -, -, -, -⟩ :=
    GlobalTheory.T.closedDisc_coefficients_topologicallyFree l K bk A s ι TB bk.ρ₀ hρ₀ (h0.trans_lt h1) j₀ hj₀
  have comm : ∀ i x, cD₀ i (R x) = RS (cD i x) := fun i => by
    have h := (GlobalTheory.T.closedDiscGaugeCompletion_basic_properties l A (s X) ρ).2.2.1 (bk.DS bk.ρ₀) (fun z hz => by
        rw [nsmul_eq_mul] at hz
        exact (isUnit_l_disc l (X : bk.S) bk.ρ₀).mul_right_eq_zero.1 hz)
      ((cD₀ i).comp R.toAddMonoidHom) (RS.toAddMonoidHom.comp (cD i))
      (AddMonoidHomClass.continuous_of_bound _ 1 fun x =>
        ((hle₀ i (R x)).trans (hR.norm_le x)).trans (one_mul _).ge)
      (AddMonoidHomClass.continuous_of_bound _ 1 fun x =>
        ((hRS.norm_le (cD i x)).trans (hle i x)).trans (one_mul _).ge)
      (fun a => by
        change cD₀ i (R (toDisc l (s X) ρ a)) = RS (cD i (toDisc l (s X) ρ a))
        rw [hR.ext, hc, hRS.ext, RingHom.id_apply, RingHom.id_apply, hc₀])
    exact fun x => DFunLike.congr_fun h x
  obtain ⟨w, hw⟩ := hy
  have hd : ∀ i, ∃ z, cD i y = toDisc l (X : bk.S) ρ bk.E * z := fun i =>
    GlobalTheory.T.eisenstein_dvd_of_dvd_restrict_closedDisc l K bk ρ h0 h1 RS hRS _ ⟨cD₀ i w, by rw [← comm, hw, ← hj₀.ext, hmul₀]⟩
  choose z hz using hd
  have hzn : Filter.Tendsto z Filter.cofinite (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have h := (tendsto_zero_iff_norm_tendsto_zero.1 (hnull y)).div_const ((ρ : ℝ) ^ bk.Ep.natDegree)
    rw [zero_div] at h
    refine h.congr fun i => ?_
    rw [hz, GlobalTheory.T.norm_eisenstein_mul_closedDisc_eq_rpow l K bk ρ h0 h1, mul_div_cancel_left₀ _ hρ'.ne']
  obtain ⟨y', hy'⟩ := hex z hzn
  refine ⟨y', ?_⟩
  rw [← sub_eq_zero, ← norm_le_zero_iff]
  refine hsup _ 0 le_rfl fun i => ?_
  rw [map_sub, ← hj.ext, hmul, hy', hz, sub_self, norm_zero]

theorem div_E_of_topBasis : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (A : Type) [CommRing A]
    (s : bk.S →+* A) (ι : Type), TopBasis s bk.J ι → ∀ ρ : ℝ≥0, bk.ρ₀ ≤ ρ → ρ < 1 →
    (∀ y : Disc l (s X) ρ, ‖toDisc l (s X) ρ (s bk.E) * y‖ = (ρ : ℝ) ^ bk.Ep.natDegree * ‖y‖) ∧
    ∀ R : Disc l (s X) ρ →+* Disc l (s X) bk.ρ₀, IsDiscMap (RingHom.id A) R → ∀ (h : ℕ) (y : Disc l (s X) ρ),
      toDisc l (s X) bk.ρ₀ (s bk.E) ^ h ∣ R y → toDisc l (s X) ρ (s bk.E) ^ h ∣ y := by
  intro l _ K bk A _ s ι TB ρ h0 h1
  refine ⟨norm_E_mul_of_topBasis l K bk A s ι TB ρ h0 h1, fun R hR h => ?_⟩
  have hρ' : (0 : ℝ) < (bk.ρ₀ : ℝ) ^ bk.Ep.natDegree := pow_pos (by exact_mod_cast bk.rho_zero_pos) _
  induction h with
  | zero => intro y _; rw [pow_zero]; exact one_dvd _
  | succ h ih =>
    intro y hy
    obtain ⟨y', rfl⟩ := E_dvd_of_topBasis l K bk A s ι TB ρ h0 h1 R hR y
      ((dvd_pow_self _ (Nat.succ_ne_zero h)).trans hy)
    obtain ⟨w, hw⟩ := hy
    rw [pow_succ']
    refine mul_dvd_mul_left _ (ih y' ⟨w, ?_⟩)
    rw [map_mul, hR.ext, RingHom.id_apply, pow_succ', mul_assoc, ← sub_eq_zero, ← mul_sub] at hw
    have h2 := norm_E_mul_of_topBasis l K bk A s ι TB bk.ρ₀ le_rfl (h0.trans_lt h1)
      (R y' - toDisc l (s X) bk.ρ₀ (s bk.E) ^ h * w)
    rw [hw, norm_zero] at h2
    exact sub_eq_zero.1 (norm_eq_zero.1 ((mul_eq_zero.1 h2.symm).resolve_left hρ'.ne'))

end GlobalTheory.BSP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EnvRingExistsStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_envRing : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] (D : Delta l A) (J : Ideal A) (d p : A), J.FG → (l : A) ∈ J → d ∈ J → IsUnit (D.δ d) → IsAdicComplete J A → Nonempty (EnvRing D J d p) := by
  first | exact @GlobalTheory.BSP.envRing_exists | exact GlobalTheory.BSP.envRing_exists | (intros; apply GlobalTheory.BSP.envRing_exists <;> assumption)
end

