import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0015
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0410
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0546
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0408
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0559
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0050
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0550
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0454
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0555
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0525
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0005
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0496
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0544
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0173
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0551
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0310
import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BddGood
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0552

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInvLift
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.InvLift

variable {l : ℕ} [hl : Fact l.Prime] {K : FinExt l} (bk : BK K) (m : ℕ)

def InvSet : Subring bk.S where
  carrier := {x | ∀ g : ↥(GK K), bk.ev bk.E ^ m ∣ Per.σA (g : GQ l) (bk.ev x) - bk.ev x}
  zero_mem' g := by simp
  one_mem' g := by simp
  neg_mem' {x} hx g := by
    have := (hx g).neg_right
    simpa [map_neg, neg_sub, sub_eq_add_neg, add_comm] using this
  add_mem' {x y} hx hy g := by
    have h := dvd_add (hx g) (hy g)
    rw [map_add, map_add]
    convert h using 1
    ring
  mul_mem' {x y} hx hy g := by
    have h := dvd_add (dvd_mul_of_dvd_right (hy g) (Per.σA (g : GQ l) (bk.ev x)))
      (dvd_mul_of_dvd_left (hx g) (bk.ev y))
    rw [map_mul, map_mul]
    convert h using 1
    ring

theorem C_mem (w : Wq l bk.a) : (C w : bk.S) ∈ InvSet bk m := fun g => by
  rw [bk.ev_C, bk.gal_w, sub_self]
  exact dvd_zero _

omit hl in
theorem coe_sum_fin {R : Type} [CommRing R] {e : ℕ} (c : Fin e → R) :
    ((∑ i, Polynomial.C (c i) * Polynomial.X ^ (i : ℕ) : Polynomial R) : R⟦X⟧) = ∑ i, C (c i) * X ^ (i : ℕ) := by
  rw [← Polynomial.coeToPowerSeries.ringHom_apply, map_sum]
  simp [Polynomial.coeToPowerSeries.ringHom_apply]

theorem exists_div (s : bk.S) : ∃ (q : bk.S) (c : Fin bk.Ep.natDegree → Wq l bk.a),
    s = bk.E * q + ∑ i, C (c i) * X ^ (i : ℕ) := by
  haveI : IsAdicComplete (Ideal.span {(l : Wq l bk.a)}) (Wq l bk.a) := WittVector.isAdicCompleteIdealSpanP
  have hdist : bk.Ep.IsDistinguishedAt (Ideal.span {(l : Wq l bk.a)}) :=
    { mem := fun {i} hi => Ideal.mem_span_singleton.2 (bk.dvd_coeff i hi)
      monic := bk.monic }
  have hI : Ideal.span {(l : Wq l bk.a)} ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]
    exact (WittVector.irreducible l (k := Fq l bk.a)).not_isUnit
  obtain ⟨h1, h2⟩ := (hdist.isWeierstrassDivisorAt hI).isWeierstrassDivisionAt_div_mod s
  refine ⟨(hdist.isWeierstrassDivisorAt hI).div s, fun i => ((hdist.isWeierstrassDivisorAt hI).mod s).coeff i,
    h2.trans ?_⟩
  rw [← coe_sum_fin]
  congr 2
  have ho : bk.Ep.natDegree = _ := congr(ENat.toNat $(hdist.coe_natDegree_eq_order_map (bk.Ep : (Wq l bk.a)⟦X⟧) 1
    (by rwa [constantCoeff_one, ← Ideal.ne_top_iff_one]) (by simp)))
  rw [← ho] at h1
  rw [Polynomial.sum_fin (fun i a => Polynomial.C a * Polynomial.X ^ i) (by simp) h1,
    Polynomial.sum_C_mul_X_pow_eq]

variable {bk m} in
theorem cancel_pow_l (k : ℕ) (a : Ainf l) (h : bk.ev bk.E ^ m ∣ (l : Ainf l) ^ k * a) : bk.ev bk.E ^ m ∣ a := by
  induction k generalizing a with
  | zero => simpa using h
  | succ k ih =>
    apply (GlobalTheory.T.eisensteinImage_pow_ideal_ainf_properties l K bk m).1
    apply ih
    rwa [pow_succ, mul_assoc] at h

end GlobalTheory.BSP.InvLift

open GlobalTheory.BSP.InvLift in

theorem GlobalTheory.BSP.BK.exists_inv_lift : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (m : ℕ), ∃ k : ℕ, ∀ s : bk.S, ∃ γ : bk.S, bk.E ∣ γ - (l : bk.S) ^ k * s ∧ ∀ g : ↥(GK K), bk.ev bk.E ^ m ∣ Per.σA (g : GQ l) (bk.ev γ) - bk.ev γ := by
  intro l hl K bk m
  obtain ⟨M, q, hq1, hq2⟩ := GlobalTheory.BSP.BK.exists_approx_root l K bk m
  have hqinv : q ∈ InvSet bk m := fun g => by
    obtain ⟨k, hk⟩ := GlobalTheory.BSP.approx_root_indep l K bk m M q hq1 hq2 (ainfObj K) bk.ι ((ainfHom K g).comp bk.ι)
    change bk.ev bk.E ^ m ∣ (l : Ainf l) ^ k * (bk.ev q - Per.σA (g : GQ l) (bk.ev q)) at hk
    rw [← neg_sub]
    exact (cancel_pow_l k _ hk).neg_right
  set e := bk.Ep.natDegree
  refine ⟨M * e, fun s => ?_⟩
  obtain ⟨q', c, hs⟩ := exists_div bk s
  refine ⟨∑ i : Fin e, C (c i) * (l : bk.S) ^ (M * (e - i)) * q ^ (i : ℕ), ?_, fun g => ?_⟩
  · have key : ∀ i : Fin e, bk.E ∣ C (c i) * (l : bk.S) ^ (M * (e - i)) * q ^ (i : ℕ) -
        (l : bk.S) ^ (M * e) * (C (c i) * X ^ (i : ℕ)) := by
      intro i
      have h1 : (l : bk.S) ^ (M * e) * X ^ (i : ℕ) = (l : bk.S) ^ (M * (e - i)) * ((l : bk.S) ^ M * X) ^ (i : ℕ) := by
        rw [mul_pow, ← pow_mul, ← mul_assoc, ← pow_add, ← Nat.mul_add]
        congr 3
        have := i.2
        omega
      rw [mul_left_comm, h1]
      have := (hq1.trans (sub_dvd_pow_sub_pow q ((l : bk.S) ^ M * X) i)).mul_left (C (c i) * (l : bk.S) ^ (M * (e - i)))
      convert this using 1
      ring
    have heq : (∑ i : Fin e, C (c i) * (l : bk.S) ^ (M * (e - i)) * q ^ (i : ℕ)) - (l : bk.S) ^ (M * e) * s =
        (∑ i : Fin e, (C (c i) * (l : bk.S) ^ (M * (e - i)) * q ^ (i : ℕ) -
          (l : bk.S) ^ (M * e) * (C (c i) * X ^ (i : ℕ)))) - bk.E * ((l : bk.S) ^ (M * e) * q') := by
      rw [hs, Finset.sum_sub_distrib, mul_add, Finset.mul_sum]
      ring
    rw [heq]
    exact dvd_sub (Finset.dvd_sum fun i _ => key i) (dvd_mul_right _ _)
  · have hmem : (∑ i : Fin e, C (c i) * (l : bk.S) ^ (M * (e - i)) * q ^ (i : ℕ)) ∈ InvSet bk m :=
      Subring.sum_mem _ fun i _ => Subring.mul_mem _ (Subring.mul_mem _ (C_mem bk m _)
        (Subring.pow_mem _ (natCast_mem _ _) _)) (Subring.pow_mem _ hqinv _)
    exact hmem g
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsKernelVectorMemOEOfFrobeniusStable
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.KernelDescent

theorem shape_mul {T : Type*} [CommRing T] {d : ℕ} (I : Finset (Fin d)) (P P' : Matrix (Fin d) (Fin d) T)
    (hP : ∀ i, ∀ j ∉ I, P i j = 0) (hP' : ∀ i ∈ I, ∀ j, P' i j = if i = j then 1 else 0) : P * P' = P := by
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single j]
  · by_cases hj : j ∈ I
    · rw [hP' j hj j, if_pos rfl, mul_one]
    · rw [hP i j hj, zero_mul]
  · intro k _ hk
    by_cases hkI : k ∈ I
    · rw [hP' k hkI j, if_neg hk, mul_zero]
    · rw [hP i k hkI, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ j) h

theorem mul_eq_of_ker {C : Type*} [CommRing C] {d : ℕ} (Y Q M : Matrix (Fin d) (Fin d) C)
    (hQ : ∀ v, Y.mulVec v = 0 → Q.mulVec v = v) (hM : Y * M = 0) : Q * M = M := by
  ext i j
  have h := hQ (fun k => M k j) (by
    funext a
    have := congrFun (congrFun hM a) j
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this)
  have := congrFun h i
  simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this

theorem shape_map {C T : Type*} [CommRing C] [CommRing T] {d : ℕ} (I : Finset (Fin d))
    (Q : Matrix (Fin d) (Fin d) C) (h₁ : ∀ i ∈ I, ∀ j, Q i j = if i = j then 1 else 0)
    (h₂ : ∀ i, ∀ j ∉ I, Q i j = 0) (f g : C →+* T) : Q.map f * Q.map g = Q.map f := by
  refine shape_mul I _ _ (fun i j hj => ?_) (fun i hi j => ?_)
  · rw [Matrix.map_apply, h₂ i j hj, map_zero]
  · rw [Matrix.map_apply, h₁ i hi j]
    split_ifs
    · exact map_one g
    · exact map_zero g

theorem two_copies {l : ℕ} [Fact l.Prime] {C : Type} [Field C] [CharP C l] {d : ℕ} (I : Finset (Fin d))
    (A Q Λ : Matrix (Fin d) (Fin d) C) (h₁ : ∀ i ∈ I, ∀ j, Q i j = if i = j then 1 else 0)
    (h₂ : ∀ i, ∀ j ∉ I, Q i j = 0) (hΛ : Q = A * Q.map (frobenius C l) * Λ)
    (hQA : Q * (A * Q.map (frobenius C l)) = A * Q.map (frobenius C l))
    (T : Type) [CommRing T] (i₁ i₂ : C →+* T) (hA : A.map i₁ = A.map i₂) :
    ∃ c : Fin d × Fin d → Fin d × Fin d → T, ∀ j : Fin d × Fin d,
      i₁ (Q j.1 j.2) - i₂ (Q j.1 j.2) = ∑ i : Fin d × Fin d, (i₁ (Q i.1 i.2) - i₂ (Q i.1 i.2)) ^ l * c i j := by
  rcases subsingleton_or_nontrivial T with hT | hT
  · exact ⟨0, fun _ => Subsingleton.elim _ _⟩
  haveI : CharP T l := charP_of_injective_ringHom i₁.injective l
  have e1 : Q.map i₂ * Q.map i₁ = Q.map i₂ := shape_map I Q h₁ h₂ i₂ i₁
  have e2 : Q.map i₁ = A.map i₂ * (Q.map (frobenius C l)).map i₁ * Λ.map i₁ := by
    rw [← hA, ← Matrix.map_mul, ← Matrix.map_mul, ← hΛ]
  have e3 : Q.map i₂ * (A.map i₂ * (Q.map (frobenius C l)).map i₂) = A.map i₂ * (Q.map (frobenius C l)).map i₂ := by
    rw [← Matrix.map_mul, ← Matrix.map_mul, hQA]
  have e4 : Q.map i₁ - Q.map i₂ = ((1 - Q.map i₂) * A.map i₂) *
      ((Q.map (frobenius C l)).map i₁ - (Q.map (frobenius C l)).map i₂) * Λ.map i₁ := by
    have a1 : ((1 - Q.map i₂) * A.map i₂) * (Q.map (frobenius C l)).map i₂ = 0 := by
      rw [Matrix.mul_assoc, Matrix.sub_mul, Matrix.one_mul, e3, sub_self]
    rw [Matrix.mul_sub, a1, sub_zero, Matrix.mul_assoc (1 - Q.map i₂), Matrix.mul_assoc (1 - Q.map i₂), ← e2,
      Matrix.sub_mul, Matrix.one_mul, e1]
  refine ⟨fun i j => ((1 - Q.map i₂) * A.map i₂) j.1 i.1 * i₁ (Λ i.2 j.2), fun j => ?_⟩
  have := congrFun (congrFun e4 j.1) j.2
  rw [Matrix.sub_apply, Matrix.map_apply, Matrix.map_apply] at this
  rw [this, Matrix.mul_apply, Fintype.sum_prod_type_right]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Matrix.mul_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [Matrix.sub_apply, Matrix.map_apply, frobenius_def, map_pow, sub_pow_char]
  ring

theorem invariant {C : Type} [CommRing C] {d : ℕ} (I : Finset (Fin d))
    (Y Q R : Matrix (Fin d) (Fin d) C) (h₀ : Y * Q = 0) (hQ : ∀ v, Y.mulVec v = 0 → Q.mulVec v = v)
    (h₁ : ∀ i ∈ I, ∀ j, Q i j = if i = j then 1 else 0)
    (h₂ : ∀ i, ∀ j ∉ I, Q i j = 0) (g : C →+* C) (hR : R * Y.map g = Y) : Q.map g = Q := by
  have a1 : Y * Q.map g = 0 := by
    rw [← hR, Matrix.mul_assoc, ← Matrix.map_mul, h₀, Matrix.map_zero _ (map_zero g), Matrix.mul_zero]
  have a2 := mul_eq_of_ker Y Q _ hQ a1
  have a3 : Q * Q.map g = Q := shape_map I Q h₁ h₂ (RingHom.id C) g
  rw [← a2, a3]

end GlobalTheory.BSP.KernelDescent

namespace GlobalTheory.BSP

open KernelDescent in

theorem exists_ker_vector_mem_OE : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (Y A : Matrix (Fin d) (Fin d) (Cb l)), A.det ≠ 0 → (∀ i j, A i j ∈ bk.OE.map (WittVector.constantCoeff (p := l) (R := Cb l))) → Y.map (frobenius (Cb l) l) = Y * A → (∀ g : ↥(GK K), bk.FixFlat g → ∃ R : Matrix (Fin d) (Fin d) (Cb l), IsUnit R ∧ R * Y.map (autCb l (galTilt l (g : GQ l))) = Y) → Y.det = 0 → ∃ v : Fin d → Cb l, v ≠ 0 ∧ (∀ i, v i ∈ bk.OE.map (WittVector.constantCoeff (p := l) (R := Cb l))) ∧ Y.mulVec v = 0 := by
  intro l _ K bk d Y A hA hAm hY hg hdet
  obtain ⟨I, Q, Λ, h₀, hQ, h₁, h₂, hΛ⟩ := GlobalTheory.T.echelon_projector_kernel_frobenius l (Cb l) d Y A hA hY
  have hQA : Q * (A * Q.map (frobenius (Cb l) l)) = A * Q.map (frobenius (Cb l) l) := by
    refine mul_eq_of_ker Y Q _ hQ ?_
    rw [← Matrix.mul_assoc, ← hY, ← Matrix.map_mul, h₀, Matrix.map_zero _ (map_zero _)]
  have hmem := GlobalTheory.T.tilt_invariant_mem_reduction_of_frobenius_equation l K bk (Fin d × Fin d) (fun j => Q j.1 j.2) (fun g hgf j => by
    obtain ⟨R, -, hR⟩ := hg g hgf
    have := invariant I Y Q R h₀ hQ h₁ h₂ (autCb l (galTilt l (g : GQ l)) : Cb l →+* Cb l) hR
    exact congrFun (congrFun this j.1) j.2) (fun T _ i₁ i₂ h =>
      two_copies I A Q Λ h₁ h₂ hΛ hQA T i₁ i₂ (by
        ext i j
        exact h _ (hAm i j)))
  obtain ⟨v, hv, hYv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  have hne : ∃ j, (fun i => Q i j) ≠ 0 := by
    by_contra hc
    push Not at hc
    have : Q = 0 := by
      ext i j
      exact congrFun (hc j) i
    apply hv
    rw [← hQ v hYv, this, Matrix.zero_mulVec]
  obtain ⟨j, hj⟩ := hne
  refine ⟨fun i => Q i j, hj, fun i => hmem (i, j), ?_⟩
  funext a
  have := congrFun (congrFun h₀ a) j
  simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this

end GlobalTheory.BSP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLubinTateCharacterUnramifiedPeriod
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

theorem GlobalTheory.LTChar.main : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (K : FinExt l) (s : ℕ), 0 < s → ∃ (K' : FinExt l) (_ : K.1 ≤ K'.1) (x : P.R.Bˣ) (χ : ↥(GK K') →* (↥(MaximalUnramifiedExtension l))ˣ), (∀ c : ↥(MaximalUnramifiedExtension l), fr l s c = c → (c : Om l) ∈ K'.1) ∧ (∀ g, fr l s (χ g : ↥(MaximalUnramifiedExtension l)) = χ g) ∧ (Continuous fun g => (((χ g : (↥(MaximalUnramifiedExtension l))ˣ) : ↥(MaximalUnramifiedExtension l)) : Om l)) ∧ (∀ g : ↥(GK K'), P.actQ (g : GQ l) (x : P.R.B) = algebraMap ↥(MaximalUnramifiedExtension l) P.R.B (χ g : ↥(MaximalUnramifiedExtension l)) * x) ∧ P.ιB x ∈ Fil P 1 ∧ P.ιB x ∉ Fil P 2 ∧ ∀ j, 0 < j → j < s → ev P j x ∈ Fil P 0 ∧ ev P j x ∉ Fil P 1 := by
  intro l _ P AI T K s hs
  obtain ⟨E, ω, -, -, hE, -⟩ := GlobalTheory.T.unramifiedExt_fixedField_frobeniusPow_degree l s hs
  obtain ⟨x, hu, hφ, h1, h2, hj⟩ := GlobalTheory.LTPeriod.main l P AI T K s hs
  have h1' : P.ιB x ∈ Fil P 1 := (mem_Fil_iff P K).2 h1
  have h2' : P.ιB x ∉ Fil P 2 := fun h => h2 ((mem_Fil_iff P K).1 h)
  have hj' : ∀ j, 0 < j → j < s → ev P j x ∈ Fil P 0 ∧ ev P j x ∉ Fil P 1 := fun j h0 hjs =>
    ⟨(mem_Fil_iff P K).2 (hj j h0 hjs).1, fun h => (hj j h0 hjs).2 ((mem_Fil_iff P K).1 h)⟩
  let K' : FinExt l := supExt K E
  have hKK' : K.1 ≤ K'.1 := le_sup_left
  have hEK' : E.1 ≤ K'.1 := le_sup_right
  choose a ha hax using fun g : GQ l => GlobalTheory.T.lubinTate_period_conj_ratio_unramified l P AI T s hs x hu hφ h1' h2' hj' g
  have hx0 : x ≠ 0 := by
    intro h0
    apply h2'
    rw [h0, map_zero]
    exact Fil_zero_mem 2
  haveI : Nontrivial P.R.B := ⟨⟨x, 0, hx0⟩⟩
  have hcancel : ∀ c c' : ↥(MaximalUnramifiedExtension l), algebraMap ↥(MaximalUnramifiedExtension l) P.R.B c * x = algebraMap ↥(MaximalUnramifiedExtension l) P.R.B c' * x → c = c' :=
    fun c c' h => (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B).injective (hu.mul_right_cancel h)
  have hfix : ∀ (g : ↥(GK K')) (h : GQ l), P.actQ (g : GQ l) (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B (a h)) =
      algebraMap ↥(MaximalUnramifiedExtension l) P.R.B (a h) := fun g h => act_kur P g (hEK' ((hE (a h)).1 (ha h)))
  have hmul : ∀ g h : ↥(GK K'), a ((g : GQ l) * (h : GQ l)) = a g * a h := by
    intro g h
    apply hcancel
    calc algebraMap ↥(MaximalUnramifiedExtension l) P.R.B (a ((g : GQ l) * (h : GQ l))) * x = P.actQ ((g : GQ l) * (h : GQ l)) x := (hax _).symm
      _ = P.actQ (g : GQ l) (P.actQ (h : GQ l) x) := by rw [map_mul, AlgEquiv.mul_apply]
      _ = P.actQ (g : GQ l) (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B (a h) * x) := by rw [hax]
      _ = algebraMap ↥(MaximalUnramifiedExtension l) P.R.B (a h) * (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B (a g) * x) := by rw [map_mul, hfix, hax]
      _ = algebraMap ↥(MaximalUnramifiedExtension l) P.R.B (a g * a h) * x := by rw [map_mul]; ring
  have hone : a 1 = 1 := by
    apply hcancel
    rw [← hax, map_one, AlgEquiv.one_apply, map_one, one_mul]
  have hne : ∀ g, a g ≠ 0 := by
    intro g h0
    have h := hax g
    rw [h0, map_zero, zero_mul] at h
    exact hx0 ((P.actQ g).injective (h.trans (map_zero _).symm))
  let χ : ↥(GK K') →* (↥(MaximalUnramifiedExtension l))ˣ :=
    { toFun := fun g => Units.mk0 (a g) (hne g)
      map_one' := Units.ext hone
      map_mul' := fun g h => Units.ext (hmul g h) }
  refine ⟨K', hKK', hu.unit, χ, fun c hc => hEK' ((hE c).1 hc), fun g => ha _, ?_, fun g => ?_, ?_, ?_,
    fun j h0 hjs => ?_⟩
  · exact GlobalTheory.T.continuous_galois_character_filtration_one l P AI T K' x h1' h2' (fun g => a g) (fun g => hax g)
  · rw [IsUnit.unit_spec]
    exact hax g
  · rw [IsUnit.unit_spec]
    exact h1'
  · rw [IsUnit.unit_spec]
    exact h2'
  · rw [IsUnit.unit_spec]
    exact hj' j h0 hjs

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsNonzeroFrobVectorResidueZero
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMonII

open GlobalTheory.PSer

theorem sh_le_sh_nsmul {l : ℕ} [Fact l.Prime] (y : Formalism.Per.Fl l) (n : ℕ) (hn : ¬ l ∣ n) :
    ‖sh y‖ ≤ ‖sh (n • y)‖ := by
  have hn0 : (n : ZMod l) ≠ 0 := by rwa [Ne, ZMod.natCast_eq_zero_iff]
  set m := ((n : ZMod l)⁻¹).val with hm
  have hmnZ : ((m * n : ℕ) : ZMod l) = ((1 : ℕ) : ZMod l) := by
    push_cast
    rw [hm, ZMod.natCast_zmod_val, inv_mul_cancel₀ hn0]
  have hmn : ((m * n : ℕ) : Formalism.Per.Fl l) = 1 := by
    rw [← Nat.cast_one, CharP.natCast_eq_natCast (Formalism.Per.Fl l) l]
    exact (ZMod.natCast_eq_natCast_iff _ _ _).1 hmnZ
  have hy : y = (m : Formalism.Per.Fl l) * (n • y) := by
    rw [nsmul_eq_mul, ← mul_assoc, ← Nat.cast_mul, hmn, one_mul]
  have hmul : ∀ a b : Formalism.Per.Fl l, sh (a * b) = sh a * sh b := by
    intro a b; simp [sh, map_mul]
  have hle : ∀ x : Formalism.Per.Fl l, ‖sh x‖ ≤ 1 := fun x => (GlobalTheory.RingBasics.mem_OC _).1 (PreTilt.untilt x).2
  calc ‖sh y‖ = ‖sh (m : Formalism.Per.Fl l)‖ * ‖sh (n • y)‖ := by
        conv_lhs => rw [hy]
        rw [hmul, norm_mul]
    _ ≤ 1 * ‖sh (n • y)‖ := mul_le_mul_of_nonneg_right (hle _) (norm_nonneg _)
    _ = ‖sh (n • y)‖ := one_mul _

theorem ev_algebraMap {l : ℕ} [Fact l.Prime] (P : LocPrime l) (m : ℕ) (q : ℚ_[l]) :
    ev P m (algebraMap ℚ_[l] P.R.B q) = algebraMap ℚ_[l] P.R.BdR q := by
  rw [ev, ← AlgHom.coe_pow, AlgHom.commutes, AlgHom.commutes]

end GlobalTheory.PMonII

namespace GlobalTheory.PMonII

open GlobalTheory.PSer

theorem exII : ExII := by
  intro l _ P AI T h hh lam hlam hind
  obtain ⟨S, θ, hS, hker, hQ, hser⟩ := GlobalTheory.T.exists_BcrisPlus_series_with_theta_residues l P AI T
  obtain ⟨-, hPev, hPring, hPq, -, -⟩ := GlobalTheory.PMon.CrisPlus.plus_props l P AI T
  have hθq : ∀ (c : ℚ_[l]) (hm : algebraMap ℚ_[l] P.R.BdR c ∈ S),
      θ ⟨_, hm⟩ = algebraMap ℚ_[l] ℂ_[l] c := by
    intro c hm; obtain ⟨_, h'⟩ := hQ c; exact h'
  have hqS : ∀ c : ℚ_[l], algebraMap ℚ_[l] P.R.BdR c ∈ S := fun c => (hS _).2 (q_mem_Fil P c)
  have hlS : ∀ j, lam j ∈ S := fun j => (hS _).2 (hlam j)
  let μ : Fin h → ℂ_[l] := fun j => θ ⟨lam j, hlS j⟩
  have hμind : ∀ c : Fin h → ℚ_[l], ∑ j, algebraMap ℚ_[l] ℂ_[l] (c j) * μ j = 0 → c = 0 := by
    intro c hc
    apply hind c
    have hm : ∑ j, c j • lam j ∈ S := S.sum_mem fun j _ => by
      rw [Algebra.smul_def]; exact S.mul_mem (hqS _) (hlS j)
    have he : (⟨_, hm⟩ : S) = ∑ j, (⟨_, hqS (c j)⟩ : S) * ⟨lam j, hlS j⟩ := by
      apply Subtype.ext; simp [Algebra.smul_def]
    have h0 : θ ⟨_, hm⟩ = 0 := by
      rw [he, map_sum, ← hc]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul, hθq]
    exact (hker ⟨_, hm⟩).1 h0
  obtain ⟨Pm, μ', hdet, hμ', hnorm, hanti, hlt, horth⟩ := GlobalTheory.T.exists_sorted_normalized_orthBasis_complexPAdic l h μ hμind
  obtain ⟨y, j0, r, R, hr0, hr1, hR1, hyR, hyr, hy0, hzero⟩ :=
    GlobalTheory.T.exists_orthogonal_family_residue_zeros l h μ' hh hnorm hanti hlt horth
  have hb : ∀ k : Fin h, ∃ b : P.R.B, Plus T b ∧ P.φB^[h] b = (l : P.R.B) * b ∧
      ∀ j : ℕ, ∃ hm, θ ⟨ev P j b, hm⟩ = abelian₂ h j (y k) :=
    fun k => hser h R (y k) hh hR1 (hyR k)
  choose b hbP hbφ hbθ using hb
  choose hbm hθb using hbθ

  have hbne : b j0 ≠ 0 := by
    intro h0
    have hc := GlobalTheory.T.untiltFrobeniusSeries_linearIndependent_of_firstTerms l h 1 r (fun _ => y j0) hh hr0 hr1 (fun _ k => hyr k) ?_ (fun _ => 1) ?_
    · exact one_ne_zero (congrFun hc 0)
    · intro n hn a
      by_contra hd
      have ha : a = 0 := Subsingleton.elim _ _
      subst ha
      have hle := sh_le_sh_nsmul (y j0 0) (n 0) hd
      simp only [Finset.univ_unique, Finset.sum_singleton] at hn
      have : (default : Fin 1) = 0 := rfl
      rw [this] at hn
      linarith
    · intro j _
      have e : (⟨ev P j (b j0), hbm j0 j⟩ : S) = 0 := Subtype.ext (by
        simp only [h0, ZeroMemClass.coe_zero, ← evHom_apply, map_zero])
      have hL : abelian₂ h j (y j0) = 0 := by rw [← hθb j0 j, e, map_zero]
      simp [hL]
  let a : Fin h → P.R.B := fun j => ∑ k, algebraMap ℚ_[l] P.R.B (Pm k j) * b k
  have hplus0 : Plus T (0 : P.R.B) := by simpa using hPq 0
  have hev : ∀ (i : ℕ) (j : Fin h), ev P i (a j) = ∑ k, algebraMap ℚ_[l] P.R.BdR (Pm k j) * ev P i (b k) := by
    intro i j
    simp only [a, ← evHom_apply, map_sum, map_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [evHom_apply, evHom_apply, ev_algebraMap]
  refine ⟨a, ?_, ?_, ?_, ?_⟩
  ·
    intro ha
    apply hbne
    have hinv : Pm * Pm⁻¹ = 1 := Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hdet)
    have key : ∑ j, algebraMap ℚ_[l] P.R.B (Pm⁻¹ j j0) * a j = b j0 := by
      simp only [a, Finset.mul_sum, ← mul_assoc, ← map_mul]
      rw [Finset.sum_comm]
      have : ∀ k, ∑ j, algebraMap ℚ_[l] P.R.B (Pm⁻¹ j j0 * Pm k j) * b k =
          algebraMap ℚ_[l] P.R.B ((Pm * Pm⁻¹) k j0) * b k := by
        intro k
        rw [← Finset.sum_mul, ← map_sum, Matrix.mul_apply]
        simp only [mul_comm]
      simp only [this, hinv, Matrix.one_apply]
      simp
    rw [← key]
    simp [ha]
  · intro j
    refine Finset.sum_induction _ (Plus T) (fun x y hx hy => (hPring x y hx hy).1) hplus0 fun k _ => ?_
    exact (hPring _ _ (hPq _) (hbP k)).2
  · intro j
    simp only [a]
    rw [← AlgHom.coe_pow, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, AlgHom.commutes, AlgHom.coe_pow, hbφ k]
    ring
  · intro i
    have hX : ∑ j, lam j * ev P i (a j) ∈ S := S.sum_mem fun j _ => S.mul_mem (hlS j) (by
      rw [hev]; exact S.sum_mem fun k _ => S.mul_mem (hqS _) (hbm k i))
    apply (hker ⟨_, hX⟩).1
    have he : (⟨_, hX⟩ : S) = ∑ j, ∑ k, (⟨lam j, hlS j⟩ : S) * ((⟨_, hqS (Pm k j)⟩ : S) * ⟨_, hbm k i⟩) := by
      apply Subtype.ext
      simp only [hev, Finset.mul_sum]
      simp
    rw [he]
    simp only [map_sum, map_mul, hθq, hθb]
    rw [Finset.sum_comm]
    rw [← hzero i]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hμ' k, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [μ]
    ring

end GlobalTheory.PMonII
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExtIn
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GoodTransfer

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

def ExtIn (Y : Model Xo c β) (S : Set Y.X) (T : CDVR) (io : c.F →+* T.Fr) (x : Sp T.Fr ⟶ Xo.X) : Prop :=
  ∃ (y' : Sp T.V ⟶ Y.X) (z : Sp T.Fr ⟶ Xo.XF c), z ≫ pullback.fst _ _ = x ∧ z ≫ pullback.snd _ _ = spMap io ∧
    z ≫ Y.j = spMap (algebraMap T.V T.Fr) ≫ y' ∧ Set.range y' ⊆ S

theorem ExtIn.mono {Y : Model Xo c β} {S S' : Set Y.X} (h : S ⊆ S') {T : CDVR} {io : c.F →+* T.Fr}
    {x : Sp T.Fr ⟶ Xo.X} (hx : ExtIn Y S T io x) : ExtIn Y S' T io x := by
  obtain ⟨y', z, h1, h2, h3, h4⟩ := hx
  exact ⟨y', z, h1, h2, h3, h4.trans h⟩

end GlobalTheory.GoodTransfer
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusMatrixRelationDiscreteStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobenius_matrix_relation_discrete : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l) (hτ : bk.IsPer τ) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (hρ : ∀ g, IsUnit (ρ g)) (s : WSeed bk d ρ τ), ∀ Φ : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap WittVector.frobenius Φ → ((l : bk.DA bk.ρ₀) ^ (s.c₁ + s.c₂) * bk.iS (frobS l bk.a bk.E) ^ s.N) • s.W.map Φ = s.W * (s.X' * s.F.map (C : Wq l bk.a →+* bk.S) * s.X.map (frobS l bk.a)).map bk.iS := by
  first | exact @GlobalTheory.BKLim.WSeed.crystallineDiscPeriods_frobenius_eq_mul | exact GlobalTheory.BKLim.WSeed.crystallineDiscPeriods_frobenius_eq_mul | (intros; apply GlobalTheory.BKLim.WSeed.crystallineDiscPeriods_frobenius_eq_mul <;> assumption)
end

