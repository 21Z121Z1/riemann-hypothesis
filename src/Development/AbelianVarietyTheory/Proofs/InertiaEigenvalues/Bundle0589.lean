import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0015
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0550
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0563
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0489
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0498
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0408
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0578
import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWildInertiaCyclotomicElement
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0102
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0425
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0437
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0451
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0579
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0404

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBetaOfDiscCocycle
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BKLim.BetaDR

variable {l : ℕ} [Fact l.Prime] {K : FinExt l}

theorem map_mk_eq_iff {R : Type} [CommRing R] {d : ℕ} (e : R) (P P' : Matrix (Fin d) (Fin d) R) :
    P.map (Ideal.Quotient.mk (Ideal.span {e})) = P'.map (Ideal.Quotient.mk (Ideal.span {e})) ↔
      ∀ a b, e ∣ P a b - P' a b := by
  constructor
  · intro h a b
    have h1 := congrFun (congrFun h a) b
    simp only [Matrix.map_apply] at h1
    exact Ideal.mem_span_singleton.1 (Ideal.Quotient.eq.1 h1)
  · intro h
    ext a b
    simp only [Matrix.map_apply]
    exact Ideal.Quotient.eq.2 (Ideal.mem_span_singleton.2 (h a b))

theorem map_smul_mat {R R' : Type} [CommRing R] [CommRing R'] {d : ℕ} (f : R →+* R') (c : R)
    (P : Matrix (Fin d) (Fin d) R) : (c • P).map f = f c • P.map f := by
  ext a b; simp

theorem map_sub_mat {R R' : Type} [CommRing R] [CommRing R'] {d : ℕ} (f : R →+* R')
    (P P' : Matrix (Fin d) (Fin d) R) : (P - P').map f = P.map f - P'.map f := by
  ext a b; simp

theorem map_mul_three {R R' : Type} [CommRing R] [CommRing R'] {d : ℕ} (f : R →+* R')
    (P₁ P₂ P₃ : Matrix (Fin d) (Fin d) R) : (P₁ * P₂ * P₃).map f = P₁.map f * P₂.map f * P₃.map f := by
  simp only [Matrix.map_mul]

theorem map_entry_sub_smul_one {R R' : Type} [CommRing R] [CommRing R'] {d : ℕ} (f : R →+* R') (c : R)
    (P : Matrix (Fin d) (Fin d) R) (a b : Fin d) :
    f ((P - c • (1 : Matrix (Fin d) (Fin d) R)) a b) = (P.map f) a b - (f c • (1 : Matrix (Fin d) (Fin d) R')) a b := by
  rcases eq_or_ne a b with rfl | hab
  · simp
  · simp [Matrix.one_apply_ne hab]

theorem mat_approx (bk : BK K) (m : ℕ) {d : ℕ} (x : Matrix (Fin d) (Fin d) (bk.DS bk.ρ₀)) :
    ∃ (k : ℕ) (s : Matrix (Fin d) (Fin d) bk.S), ∀ a b,
      toDisc l (X : bk.S) bk.ρ₀ bk.E ^ m ∣ (l : bk.DS bk.ρ₀) ^ k * x a b - toDisc l (X : bk.S) bk.ρ₀ (s a b) := by
  choose k s hs using fun p : Fin d × Fin d => GlobalTheory.BKLim.WApprox.exists_congr_pow_E l K bk m (x p.1 p.2)
  refine ⟨∑ p, k p, fun a b => (l : bk.S) ^ (∑ p, k p - k (a, b)) * s (a, b), fun a b => ?_⟩
  have hle : k (a, b) ≤ ∑ p, k p := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ (a, b))
  obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_le hle
  have hc' : ∑ p, k p - k (a, b) = c := by omega
  show toDisc l (X : bk.S) bk.ρ₀ bk.E ^ m ∣ (l : bk.DS bk.ρ₀) ^ (∑ p, k p) * x a b -
    toDisc l (X : bk.S) bk.ρ₀ ((l : bk.S) ^ (∑ p, k p - k (a, b)) * s (a, b))
  rw [hc', hc, pow_add, map_mul, map_pow, map_natCast]
  have h := dvd_mul_of_dvd_right (hs (a, b)) ((l : bk.DS bk.ρ₀) ^ c)
  convert h using 1
  ring

theorem mat_lift (bk : BK K) (m : ℕ) {d : ℕ} (x : Matrix (Fin d) (Fin d) (bk.DS bk.ρ₀)) :
    ∃ (k : ℕ) (γ : Matrix (Fin d) (Fin d) bk.S), (∀ a b, toDisc l (X : bk.S) bk.ρ₀ bk.E ∣
      toDisc l (X : bk.S) bk.ρ₀ (γ a b) - (l : bk.DS bk.ρ₀) ^ k * x a b) ∧
      ∀ (g : ↥(GK K)) a b, bk.ev bk.E ^ m ∣ Per.σA (g : GQ l) (bk.ev (γ a b)) - bk.ev (γ a b) := by
  obtain ⟨k₀, s, hs⟩ := mat_approx bk 1 x
  obtain ⟨k₁, hk₁⟩ := GlobalTheory.T.exists_invariant_lift_mod_E l K bk m
  choose γ hγ1 hγ2 using fun p : Fin d × Fin d => hk₁ (s p.1 p.2)
  refine ⟨k₁ + k₀, fun a b => γ (a, b), fun a b => ?_, fun g a b => hγ2 (a, b) g⟩
  have h1 := map_dvd (toDisc l (X : bk.S) bk.ρ₀) (hγ1 (a, b))
  have hs1 := hs a b
  rw [pow_one] at hs1
  have h2 := dvd_mul_of_dvd_right hs1 ((l : bk.DS bk.ρ₀) ^ k₁)
  have h3 := dvd_sub h1 h2
  convert h3 using 1
  simp only [map_sub, map_mul, map_pow, map_natCast]
  ring

theorem dvd_gal_E (bk : BK K) (g : GQ l) : bk.ev bk.E ∣ Per.σA g (bk.ev bk.E) := by
  rw [← Ideal.mem_span_singleton, bk.span_ev, RingHom.mem_ker, GlobalTheory.RingBasics.θ_σA]
  have h : Per.θ l (bk.ev bk.E) = 0 := by
    rw [← RingHom.mem_ker, ← bk.span_ev]; exact Ideal.mem_span_singleton_self _
  rw [h, map_zero]

theorem dvd_of_iS_dvd (bk : BK K) (s : bk.S) (h : bk.iS bk.E ∣ bk.iS s) : bk.E ∣ s := by
  have h2 : bk.ev bk.E ^ 1 ∣ bk.ev s :=
    (GlobalTheory.BSP.ainf_dvd_of_disc_dvd l K bk (bk.ev s)).1 1 (by rw [pow_one]; exact h)
  have h3 := (GlobalTheory.T.eisensteinImage_pow_ideal_ainf_properties l K bk 1).2.1 s h2
  rwa [pow_one] at h3

end GlobalTheory.BKLim.BetaDR

open GlobalTheory.BKLim.BetaDR in

theorem GlobalTheory.BKLim.exists_beta_of_disc_cocycle : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d N : ℕ) (κ : ↥(GK K) → Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀)) (φε : ↥(GK K) → Matrix (Fin d) (Fin d) (Ainf l)) (H : Matrix (Fin d) (Fin d) (bk.DS bk.ρ₀)) (i : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀), IsDiscMap bk.ev i → IsUnit H → (∀ m : ℕ, ∃ (k : ℕ) (Λ : Matrix (Fin d) (Fin d) bk.S), (∀ a b, bk.E ∣ (Λ - (l : bk.S) ^ k • (1 : Matrix (Fin d) (Fin d) bk.S)) a b) ∧ ∀ (g : ↥(GK K)) (G : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀), IsDiscMap (Per.σA (g : GQ l)) G → ∀ a b, bk.iS bk.E ^ m ∣ (κ g * (Λ.map bk.iS).map G - Λ.map bk.iS) a b) → (∀ (g : ↥(GK K)) (G : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀), IsDiscMap (Per.σA (g : GQ l)) G → G (bk.iS (frobS l bk.a bk.E)) ^ N • (H.map i * (φε g).map bk.iA) = bk.iS (frobS l bk.a bk.E) ^ N • (κ g * (H.map i).map G)) → ∀ m : ℕ, ∃ (k : ℕ) (β : Matrix (Fin d) (Fin d) bk.S), (∀ a b, bk.E ∣ (β - (l : bk.S) ^ k • (1 : Matrix (Fin d) (Fin d) bk.S)) a b) ∧ ∀ (g : ↥(GK K)) a b, bk.ev bk.E ^ m ∣ (φε g * (β.map bk.ev).map (Per.σA (g : GQ l)) - β.map bk.ev) a b := by
  intro l _ K bk d N κ φε H i hi hH hΛ hmain m₀
  obtain ⟨hmap, hgal, -, hρ0, -, -⟩ := GlobalTheory.BSP.exists_discMaps l K bk
  set m := m₀ + 1 with hm

  obtain ⟨u, hu⟩ := isUnit_toDisc_frobS_E l K bk
  obtain ⟨U, hU⟩ := hH
  set v : bk.DS bk.ρ₀ := ((u⁻¹ : (bk.DS bk.ρ₀)ˣ) : bk.DS bk.ρ₀) with hv
  set H₁ : Matrix (Fin d) (Fin d) (bk.DS bk.ρ₀) := v ^ N • H with hH₁
  set H₁' : Matrix (Fin d) (Fin d) (bk.DS bk.ρ₀) := (u : bk.DS bk.ρ₀) ^ N • ((U⁻¹ : (Matrix (Fin d) (Fin d) (bk.DS bk.ρ₀))ˣ) : Matrix (Fin d) (Fin d) (bk.DS bk.ρ₀)) with hH₁'
  have hvu : v * (u : bk.DS bk.ρ₀) = 1 := Units.inv_mul u
  have hH11 : H₁ * H₁' = 1 := by
    rw [hH₁, hH₁', Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← mul_pow, hvu, one_pow, one_smul, ← hU, Units.mul_inv]
  have hH12 : H₁' * H₁ = 1 := by
    rw [hH₁, hH₁', Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← mul_pow, mul_comm, hvu, one_pow, one_smul, ← hU,
      Units.inv_mul]

  have hmapt : ∀ P : Matrix (Fin d) (Fin d) bk.S, (P.map (toDisc l (X : bk.S) bk.ρ₀)).map i = P.map bk.iS := by
    intro P; ext a b; exact hi.ext _
  set A := H₁.map i with hA
  set A' := H₁'.map i with hA'
  have hAA' : A * A' = 1 := by rw [hA, hA', ← Matrix.map_mul, hH11, Matrix.map_one _ (map_zero i) (map_one i)]
  have hA'A : A' * A = 1 := by rw [hA, hA', ← Matrix.map_mul, hH12, Matrix.map_one _ (map_zero i) (map_one i)]
  have hiv : i v * bk.iS (frobS l bk.a bk.E) = 1 := by
    have e : bk.iS (frobS l bk.a bk.E) = i (toDisc l (X : bk.S) bk.ρ₀ (frobS l bk.a bk.E)) := (hi.ext _).symm
    rw [e, ← hu, ← map_mul, hvu, map_one]
  have key : ∀ (g : ↥(GK K)) (G : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀), IsDiscMap (Per.σA (g : GQ l)) G →
      A * (φε g).map bk.iA = κ g * A.map G := by
    intro g G hG
    have hGiv : G (i v) * G (bk.iS (frobS l bk.a bk.E)) = 1 := by rw [← map_mul, hiv, map_one]
    have e1 : A = i v ^ N • H.map i := by rw [hA, hH₁, map_smul_mat, map_pow]
    have e2 : A.map G = G (i v) ^ N • (H.map i).map G := by rw [e1, map_smul_mat, map_pow]
    calc A * (φε g).map bk.iA = i v ^ N • (H.map i * (φε g).map bk.iA) := by rw [e1, Matrix.smul_mul]
      _ = (i v ^ N * G (i v) ^ N) • (G (bk.iS (frobS l bk.a bk.E)) ^ N • (H.map i * (φε g).map bk.iA)) := by
          rw [smul_smul, mul_assoc, ← mul_pow, hGiv, one_pow, mul_one]
      _ = (i v ^ N * G (i v) ^ N) • (bk.iS (frobS l bk.a bk.E) ^ N • (κ g * (H.map i).map G)) := by
          rw [hmain g G hG]
      _ = G (i v) ^ N • (κ g * (H.map i).map G) := by
          rw [smul_smul, mul_comm (i v ^ N), mul_assoc, ← mul_pow, hiv, one_pow, mul_one]
      _ = κ g * A.map G := by rw [e2, Matrix.mul_smul]
  obtain ⟨k₁, Λ, hΛE, hΛinv⟩ := hΛ m
  obtain ⟨k₂, Hs, hHsE, hHsinv⟩ := mat_lift bk m H₁
  obtain ⟨k₃, β, hβ⟩ := mat_approx bk m (H₁' * Λ.map (toDisc l (X : bk.S) bk.ρ₀) * Hs.map (toDisc l (X : bk.S) bk.ρ₀))
  have hM : (H₁' * Λ.map (toDisc l (X : bk.S) bk.ρ₀) * Hs.map (toDisc l (X : bk.S) bk.ρ₀)).map i =
      A' * Λ.map bk.iS * Hs.map bk.iS := by
    rw [Matrix.map_mul, Matrix.map_mul, hmapt, hmapt]
  set L := Λ.map bk.iS with hL
  set Hm := Hs.map bk.iS with hHm
  set B := β.map bk.iS with hB
  have hβD : ∀ a b, bk.iS bk.E ^ m ∣ ((l : bk.DA bk.ρ₀) ^ k₃ • (A' * L * Hm)) a b - B a b := by
    intro a b
    have h := map_dvd i (hβ a b)
    rw [map_pow, hi.ext, map_sub, map_mul, map_pow, map_natCast, hi.ext] at h
    rw [← hM]
    exact h
  refine ⟨k₁ + k₂ + k₃, β, fun a b => ?_, fun g a b => ?_⟩
  · apply dvd_of_iS_dvd bk
    rw [map_entry_sub_smul_one]
    set q := Ideal.Quotient.mk (Ideal.span {bk.iS bk.E}) with hq
    have hE1 : bk.iS bk.E ∣ bk.iS bk.E ^ m := dvd_pow_self _ (by omega)
    have eL : L.map q = (q (l : bk.DA bk.ρ₀) ^ k₁) • 1 := by
      have h : L.map q = ((bk.iS ((l : bk.S) ^ k₁)) • (1 : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀))).map q :=
        (map_mk_eq_iff _ _ _).2 fun a b => by rw [← map_entry_sub_smul_one]; exact map_dvd bk.iS (hΛE a b)
      rw [h, map_smul_mat, Matrix.map_one _ (map_zero q) (map_one q)]
      simp only [map_pow, map_natCast]
    have eH : Hm.map q = (q (l : bk.DA bk.ρ₀) ^ k₂) • A.map q := by
      have h : Hm.map q = ((l : bk.DA bk.ρ₀) ^ k₂ • A).map q :=
        (map_mk_eq_iff _ _ _).2 fun a b => by
          have h1 := map_dvd i (hHsE a b)
          rw [hi.ext, map_sub, map_mul, map_pow, map_natCast, hi.ext] at h1
          exact h1
      rw [h, map_smul_mat, map_pow]
    have eB : B.map q = ((l : bk.DA bk.ρ₀) ^ k₃ • (A' * L * Hm)).map q :=
      ((map_mk_eq_iff _ _ _).2 fun a b => dvd_trans hE1 (hβD a b)).symm
    have hq0 : (bk.iS ((l : bk.S) ^ (k₁ + k₂ + k₃)) • (1 : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀))).map q = B.map q := by
      rw [eB, map_smul_mat q, map_smul_mat q, map_mul_three, eL, eH, Matrix.map_one _ (map_zero q) (map_one q)]
      simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, smul_smul]
      rw [← Matrix.map_mul, hA'A, Matrix.map_one _ (map_zero q) (map_one q)]
      congr 1
      simp only [map_pow, map_natCast]
      ring
    exact (map_mk_eq_iff _ _ _).1 hq0.symm a b
  · obtain ⟨G, hG⟩ := hgal bk.ρ₀ hρ0 (g : GQ l)
    set q := Ideal.Quotient.mk (Ideal.span {bk.iS bk.E ^ m}) with hq
    have hGE : bk.iS bk.E ∣ G (bk.iS bk.E) := by
      obtain ⟨w, hw⟩ := dvd_gal_E bk (g : GQ l)
      show bk.iS bk.E ∣ G (toDisc l (bk.ev X) bk.ρ₀ (bk.ev bk.E))
      rw [hG.ext, hw, map_mul]
      exact dvd_mul_right _ _
    have hGd : ∀ x, bk.iS bk.E ^ m ∣ x → bk.iS bk.E ^ m ∣ G x := by
      rintro x ⟨y, rfl⟩
      rw [map_mul, map_pow]
      exact Dvd.dvd.mul_right (pow_dvd_pow_of_dvd hGE m) _
    have hGm : ∀ P P' : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀), (∀ a b, bk.iS bk.E ^ m ∣ P a b - P' a b) →
        ∀ a b, bk.iS bk.E ^ m ∣ (P.map G) a b - (P'.map G) a b := by
      intro P P' h a b
      simp only [Matrix.map_apply]
      rw [← map_sub]
      exact hGd _ (h a b)
    have hφA : (φε g).map bk.iA * A'.map G = A' * κ g := by
      have hAG : A.map G * A'.map G = 1 := by
        rw [← Matrix.map_mul, hAA', Matrix.map_one _ (map_zero G) (map_one G)]
      calc (φε g).map bk.iA * A'.map G = A' * (A * (φε g).map bk.iA) * A'.map G := by
            rw [← Matrix.mul_assoc A', hA'A, Matrix.one_mul]
        _ = A' * κ g * (A.map G * A'.map G) := by rw [key g G hG]; simp only [Matrix.mul_assoc]
        _ = A' * κ g := by rw [hAG, Matrix.mul_one]
    have eΛ : (κ g * L.map G).map q = L.map q := (map_mk_eq_iff _ _ _).2 (hΛinv g G hG)
    have eH : (Hm.map G).map q = Hm.map q := (map_mk_eq_iff _ _ _).2 fun a b => by
      have h := map_dvd bk.iA (hHsinv g a b)
      rw [map_pow, map_sub] at h
      have e : G (bk.iS (Hs a b)) = bk.iA (Per.σA (g : GQ l) (bk.ev (Hs a b))) := hG.ext _
      show bk.iS bk.E ^ m ∣ G (bk.iS (Hs a b)) - bk.iS (Hs a b)
      rw [e]
      exact h
    have eB : B.map q = ((l : bk.DA bk.ρ₀) ^ k₃ • (A' * L * Hm)).map q := ((map_mk_eq_iff _ _ _).2 hβD).symm
    have eBG : (B.map G).map q = (((l : bk.DA bk.ρ₀) ^ k₃ • (A' * L * Hm)).map G).map q :=
      ((map_mk_eq_iff _ _ _).2 (hGm _ _ hβD)).symm
    have hid : (φε g).map bk.iA * ((l : bk.DA bk.ρ₀) ^ k₃ • (A' * L * Hm)).map G =
        (l : bk.DA bk.ρ₀) ^ k₃ • (A' * (κ g * L.map G) * Hm.map G) := by
      rw [map_smul_mat, map_pow, map_natCast, map_mul_three, Matrix.mul_smul]
      congr 1
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hφA]
      simp only [Matrix.mul_assoc]
    have hfin : ((φε g).map bk.iA * B.map G).map q = B.map q := by
      rw [Matrix.map_mul, eBG, ← Matrix.map_mul, hid, eB, map_smul_mat q _ (A' * (κ g * L.map G) * Hm.map G),
        map_smul_mat q _ (A' * L * Hm), map_mul_three q A' (κ g * L.map G) (Hm.map G), eΛ, eH, map_mul_three q A' L Hm]
    have hdiv := (map_mk_eq_iff _ _ _).1 hfin a b
    have hσ : ((β.map bk.ev).map (Per.σA (g : GQ l))).map bk.iA = B.map G := by
      ext a b
      exact (hG.ext _).symm
    have hmat : (φε g * (β.map bk.ev).map (Per.σA (g : GQ l)) - β.map bk.ev).map bk.iA =
        (φε g).map bk.iA * B.map G - B := by
      rw [map_sub_mat, Matrix.map_mul, hσ]
      rfl
    have h2 : bk.iS bk.E ^ m ∣ bk.iA ((φε g * (β.map bk.ev).map (Per.σA (g : GQ l)) - β.map bk.ev) a b) := by
      have h := congrFun (congrFun hmat a) b
      rw [Matrix.map_apply] at h
      rw [h]
      exact hdiv
    have h3 := (GlobalTheory.BSP.ainf_dvd_of_disc_dvd l K bk _).1 m h2
    exact dvd_trans (pow_dvd_pow _ (by omega)) h3
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDecompositionSetting
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

noncomputable section

namespace GlobalTheory.AbsoluteIrreducibilityOfTraceSpan

open GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices

theorem mat_mul {Γ k : Type} [Group Γ] [CommRing k] {r : ℕ} (σ : Γ →* GL (Fin r) k) (g h : Γ) :
    mat σ g * mat σ h = mat σ (g * h) := by
  simp [mat]

theorem span_eq_top_of_trace_eq {Γ k : Type} [Group Γ] [Field k] {r : ℕ}
    (σ ρ : Γ →* GL (Fin r) k) (ht : ∀ g, (mat σ g).trace = (mat ρ g).trace)
    (h : Submodule.span k (Set.range (mat ρ)) = ⊤) :
    Submodule.span k (Set.range (mat σ)) = ⊤ := by
  classical
  let L := Finsupp.linearCombination k (mat σ)
  let L0 := Finsupp.linearCombination k (mat ρ)
  have hker : LinearMap.ker L ≤ LinearMap.ker L0 := by
    intro c hc
    rw [LinearMap.mem_ker] at hc ⊢
    have h1 : ∀ y : Γ, (L0 c * mat ρ y).trace = 0 := by
      intro y
      have e1 : (L c * mat σ y).trace = 0 := by rw [hc]; simp
      rw [← e1]
      simp only [L, L0, Finsupp.linearCombination_apply, Finsupp.sum, Finset.sum_mul, Matrix.smul_mul,
        Matrix.trace_sum, Matrix.trace_smul, mat_mul, ht]
    have h2 : ∀ Y : Matrix (Fin r) (Fin r) k, (L0 c * Y).trace = 0 := by
      intro Y
      have hY : Y ∈ Submodule.span k (Set.range (mat ρ)) := h ▸ Submodule.mem_top
      induction hY using Submodule.span_induction with
      | mem Y hY => obtain ⟨y, rfl⟩ := hY; exact h1 y
      | zero => simp
      | add Y Z _ _ hY hZ => rw [Matrix.mul_add, Matrix.trace_add, hY, hZ, add_zero]
      | smul a Y _ hY => rw [Matrix.mul_smul, Matrix.trace_smul, hY, smul_zero]
    ext p q
    have := h2 (Matrix.single q p 1)
    simpa [Matrix.trace_mul_single] using this
  have hL0 : LinearMap.range L0 = ⊤ := by
    rw [Finsupp.range_linearCombination]; exact h
  let f : LinearMap.range L →ₗ[k] Matrix (Fin r) (Fin r) k :=
    ((LinearMap.ker L).liftQ L0 hker).comp (L.quotKerEquivRange.symm : LinearMap.range L →ₗ[k] _)
  have hf : LinearMap.range f = ⊤ := by
    rw [LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range _), Submodule.range_liftQ, hL0]
  have h3 := LinearMap.finrank_range_le f
  rw [hf, finrank_top] at h3
  have h4 : LinearMap.range L = ⊤ :=
    Submodule.eq_top_of_finrank_eq (le_antisymm (Submodule.finrank_le _) h3)
  rw [← Finsupp.range_linearCombination]; exact h4

theorem absIrrSub_of_span_eq_top {Γ k : Type} [Group Γ] [Field k] {r : ℕ} (hr : 0 < r)
    (σ : Γ →* GL (Fin r) k) (h : Submodule.span k (Set.range (mat σ)) = ⊤) : AbsIrrSub σ ⊤ := by
  refine GlobalTheory.ResAbsIrrGood.absIrrSub_top_of_irred (algebraMap k (AlgebraicClosure k)) hr σ fun W hW => ?_
  refine GlobalTheory.BurnsideIff.eq_bot_or_top_of_span_eq_top (mat σ) h W fun g x hx => ?_
  have e : (mat σ g).map (algebraMap k (AlgebraicClosure k)) =
      ((mapRep (algebraMap k (AlgebraicClosure k)) σ g : GL (Fin r) (AlgebraicClosure k)) :
        Matrix (Fin r) (Fin r) (AlgebraicClosure k)) := by
    ext p q; simp [mat, mapRep]
  rw [e]; exact hW g x hx

theorem pos_of_absIrrSub {Γ k : Type} [Group Γ] [Field k] {r : ℕ} (σ : Γ →* GL (Fin r) k)
    (h : AbsIrrSub σ ⊤) : 0 < r := by
  rcases Nat.eq_zero_or_pos r with h0 | h0
  · subst h0
    exact absurd (Subsingleton.elim _ _) h.1
  · exact h0

end GlobalTheory.AbsoluteIrreducibilityOfTraceSpan

namespace GlobalTheory.AbsoluteIrreducibilityOfTraceSpan

open GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices

theorem mat_mapRep {Γ A B : Type} [Group Γ] [CommRing A] [CommRing B] {k : ℕ} (f : A →+* B)
    (σ : Γ →* GL (Fin k) A) (g : Γ) : mat (mapRep f σ) g = (mat σ g).map f := by
  ext p q; simp [mat, mapRep]

theorem charpoly_eq_of_isHeckeGalois (hC : GlobalTheory.TwSys.Cheb) (D : D7) (i : D.nd.Loc)
    (rep : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (hr : GoodR D.nd i rep) (π : D.nd.X i)
    (r0 : GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)) (hr0 : IsHeckeGalois D.nd i π r0) (g : GE D.nd) :
    (mat (rep π) g).charpoly = (mat r0 g).charpoly := by
  classical
  let rep' := Function.update rep π r0
  have hr' : GoodR D.nd i rep' := by
    intro y
    by_cases hy : y = π
    · subst hy; simpa [rep'] using hr0
    · simpa [rep', Function.update_of_ne hy] using hr y
  obtain ⟨Pm, hPm⟩ := GlobalTheory.PointRepConj.main hC D.nd i rep rep' hr hr' π
  have h1 := hPm g
  have h2 : (rO D.nd i rep' π g) = mat r0 g := by simp [rep', rO, mat]
  rw [h2] at h1
  apply Polynomial.map_injective (toK D.nd i) (IsFractionRing.injective (D.nd.O i) (KK D.nd i))
  rw [← Matrix.charpoly_map, ← Matrix.charpoly_map]
  have h1' : (Pm : Matrix (Fin D.R.nV) (Fin D.R.nV) (KK D.nd i)) * (mat (rep π) g).map (toK D.nd i) =
      (mat r0 g).map (toK D.nd i) * (Pm : Matrix (Fin D.R.nV) (Fin D.R.nV) (KK D.nd i)) := h1
  have h3 : (mat (rep π) g).map (toK D.nd i) =
      ((Pm⁻¹ : GL (Fin D.R.nV) (KK D.nd i)) : Matrix _ _ _) * (mat r0 g).map (toK D.nd i) *
        (Pm : Matrix _ _ _) := by
    rw [Matrix.mul_assoc, ← h1', ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel,
      Units.val_one, Matrix.one_mul]
  rw [h3]
  have := Matrix.charpoly_units_conj (Pm⁻¹) ((mat r0 g).map (toK D.nd i))
  rwa [← Matrix.coe_units_inv, inv_inv] at this

theorem residual_charpoly_eq (hC : GlobalTheory.TwSys.Cheb) (D : D7) (h32 : SumRepresentations.Conclusion41 D) (i : D.nd.Loc)
    (rep : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (hr : GoodR D.nd i rep)
    (x π : D.nd.X i) (ρx ρ0 : GE D.nd →* GL (Fin D.R.r) (D.nd.O i))
    (hx : ∃ e, IsDecomp (t := D.R.t) (rep x) ρx (D.nd.chi i) e)
    (r0 : GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)) (hr0 : IsHeckeGalois D.nd i π r0)
    (h0 : ∃ e, IsDecomp (t := D.R.t) r0 ρ0 (D.nd.chi i) e) (g : GE D.nd) :
    ((mat ρx g).map (IsLocalRing.residue (D.nd.O i))).charpoly =
      ((mat ρ0 g).map (IsLocalRing.residue (D.nd.O i))).charpoly := by
  classical
  have hG3 := (((h32 i).2.2 rep hr).2.2.1).2 x π g
  obtain ⟨ex, hex⟩ := hx
  obtain ⟨e0, he0⟩ := h0
  have dx := charpoly_of_decomp D i rep (fun _ => ρx) x ⟨ex, hex⟩ g
  have d0 := charpoly_of_decomp D i (fun _ => r0) (fun _ => ρ0) π ⟨e0, he0⟩ g
  have hc := charpoly_eq_of_isHeckeGalois hC D i rep hr π r0 hr0 g
  set res := IsLocalRing.residue (D.nd.O i)
  set P : (D.nd.O i)[X] := ∏ c ∈ Finset.Icc 1 D.R.t, (X - C ((chiU D.nd i c g : (D.nd.O i)ˣ) : D.nd.O i))
  have hP : (P.map res) ≠ 0 := by
    apply Polynomial.Monic.ne_zero
    apply Polynomial.Monic.map
    exact Polynomial.monic_prod_of_monic _ _ fun c _ => Polynomial.monic_X_sub_C _
  have e1 : ((mat ρx g).map res).charpoly * P.map res = ((mat ρ0 g).map res).charpoly * P.map res := by
    rw [Matrix.charpoly_map, Matrix.charpoly_map, ← Polynomial.map_mul, ← Polynomial.map_mul]
    have ex' : (rO D.nd i rep x g).charpoly = (mat ρx g).charpoly * P := dx
    have e0' : (mat r0 g).charpoly = (mat ρ0 g).charpoly * P := d0
    rw [← ex', ← e0', ← hc, ← Matrix.charpoly_map, ← Matrix.charpoly_map]
    exact hG3
  exact mul_right_cancel₀ hP e1

theorem setting_of_live : GlobalTheory.TwSys.Cheb → ∀ (D : D7), SumRepresentations.Conclusion41 D → GlobalTheory.SplitCoef.OSplit D → ∀ i : D.nd.Loc,
    ZDecomp D.nd i → Live D.nd i → ∃ (rep : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
      (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))),
      GoodR D.nd i rep ∧ GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.HidaSetting D.R.t (D.nd.T i) (D.nd.Z i) rep ρ (D.nd.chi i) := by
  intro hC D h32 hS i hZ hL
  classical
  obtain ⟨rep, hr⟩ := (h32 i).1.2
  obtain ⟨hG1, -, hG3, -⟩ := (h32 i).2.2 rep hr
  let ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i)) := fun x =>
    if hx : x ∈ D.nd.Z i then Classical.choose (hZ x hx (rep x) (hr x)) else 1
  have hρ : ∀ x ∈ D.nd.Z i, ∃ e, IsDecomp (t := D.R.t) (rep x) (ρ x) (D.nd.chi i) e := by
    intro x hx
    have := Classical.choose_spec (hZ x hx (rep x) (hr x))
    simp only [ρ, dif_pos hx]
    exact this
  obtain ⟨π, hπ, r0, ρ0, hr0, h0, habs⟩ := hL
  refine ⟨rep, ρ, hr, D.nd.T_local i, D.nd.T_sep i, fun x => ?_, fun h d => ?_,
    GlobalTheory.abs_irreducible_distinct_constituents D h32 hS i rep hr, hG3.2, hρ, fun x hx => ?_⟩
  · have hss := (hr x).2.1
    intro W hW
    obtain ⟨W', h1, h2⟩ := hss W fun g v hv => hW g v hv
    exact ⟨W', fun g v hv => h1 g v hv, h2⟩
  · obtain ⟨f, hf⟩ := hG1 h d
    have : (fun x => (mat (rep x) h).charpolyRev.coeff d) = (f : D.nd.X i → D.nd.O i) :=
      funext fun x => (hf x).symm
    rw [this]
    exact f.2
  · have hpos := pos_of_absIrrSub _ habs
    haveI : Nonempty (Fin D.R.r) := ⟨⟨0, hpos⟩⟩
    refine absIrrSub_of_span_eq_top hpos _ ?_
    refine span_eq_top_of_trace_eq _ (mapRep (IsLocalRing.residue (D.nd.O i)) ρ0) (fun g => ?_)
      (GlobalTheory.BurnsideField.span_mat_eq_top_of_absIrrSub _ habs)
    rw [mat_mapRep, mat_mapRep, Matrix.trace_eq_neg_charpoly_coeff, Matrix.trace_eq_neg_charpoly_coeff,
      residual_charpoly_eq hC D h32 i rep hr x π (ρ x) ρ0 (hρ x hx) r0 hr0 h0 g]

end GlobalTheory.AbsoluteIrreducibilityOfTraceSpan

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIndependentFrobSolutionsCrisProofStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsIndependentFrobSolutionsCris_proof : ExI := by
  first | exact @GlobalTheory.PMon.exI_main | exact GlobalTheory.PMon.exI_main | (intros; apply GlobalTheory.PMon.exI_main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInjectivePushoutOfPrismCoverStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_injective_pushout_of_prismCover : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (S : Strat bk d) (B C : Obj l ↥(OL K)) (h : Hom B C), Cover h → ∀ (Q : Obj l ↥(OL K)) (a : Hom B Q), ∃ (Q' : Obj l ↥(OL K)) (h' : Hom Q Q') (a' : Hom C Q'), a'.comp h = h'.comp a ∧ Function.Injective h'.f := by
  first | exact @GlobalTheory.BSP.cover_po_injective | exact GlobalTheory.BSP.cover_po_injective | (intros; apply GlobalTheory.BSP.cover_po_injective <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsPrismLocalizationAwayOfGeneratedStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isPrismLocalizationAway_of_generated : ∀ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] (B : Obj l R) (s d : B.A), GenAway B s d → ∃ (C : Obj l R) (h : Hom B C), IsLoc s h ∧ C.I = Ideal.span {h.f d} := by
  first | exact @GlobalTheory.BSP.exists_isLoc | exact GlobalTheory.BSP.exists_isLoc | (intros; apply GlobalTheory.BSP.exists_isLoc <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsNonzeroFrobVectorResidueZeroProof
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon

theorem exII_holds : ExII := GlobalTheory.T.exists_nonzero_frobVector_residue_zero

end GlobalTheory.PMon
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowMemSpanCoeffPeriodPowStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pow_mem_span_coeff_period_pow : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (ι : Type) (TB : TopBasis bk.ev bk.J ι) (M : ℕ), ∃ r : ℕ, (l : bk.S) ^ r ∈ Ideal.span (Set.range fun i => TB.c i (τ ^ M)) := by
  first | exact @GlobalTheory.BSP.pow_l_mem_span_coeff | exact GlobalTheory.BSP.pow_l_mem_span_coeff | (intros; apply GlobalTheory.BSP.pow_l_mem_span_coeff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWachFunctorComparisonOfBhattScholze
section
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.HWL

theorem exists_hw_fon_cmp_of_integral : GlobalTheory.Published.BhattScholzeIntegral →
    ∀ D : D7, ∃ (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), Nonempty (CmpOf D.loc D.locA HW F) := by
  intro hI D
  obtain ⟨H, F, hC, -⟩ := exists_hw_fon_cmp_ties (GlobalTheory.T.bhattScholze_coefficients_of_padicInt_lattices hI) D.loc D.locA D.locT
  exact ⟨H, F, hC⟩

end GlobalTheory.HWL
end

