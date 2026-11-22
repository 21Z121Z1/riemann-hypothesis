import Formalism.LocalToGlobal.KernelLattices.KerStd
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0011
import Formalism.LocalToGlobal.InertKernelTheory.Bundle0001
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.Bundle0002
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.QuadraticSemicharacterIdentityReformulated
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.QuadraticSemicharactersFactTer
import Formalism.LocalToGlobal.GlobalTheory.GL3.PStdOK
import Formalism.LocalToGlobal.GlobalTheory.GL3.PFamily
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.SelfDualLatticeNorms.HalfPeriodStandardCM
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.SelfDualLatticeNorms.Bundle0001
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitDeterminantRoot.DetMemOfEntries
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitDeterminantRoot.GlobalLUnit
import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LevelGroupNeTopNeBot
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PhiMapsAndOmegaLaw
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemParahoricOfTrivialReduction
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DatumPeriodicMulLatticeFinal
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0106
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0094
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.StandardOrbitSeriesValuationBoundZero
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0009
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0010
import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.StatementB

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormLeOneOfTrace
section
noncomputable section
open scoped ComplexConjugate

namespace GlobalTheory.TraceNormCoordinates

theorem exists_coords (b : ℤ) (d : ℕ) (hd : 0 < d) {x : ℂ} (hx : x ∈ PI.UnitaryGroupMassFormula.UnitDetRoot.KF b d) :
    ∃ p q : ℚ, x = (p : ℂ) + (q : ℂ) * (Complex.I * ((Real.sqrt d : ℝ) : ℂ)) := by
  set s : ℂ := Complex.I * ((Real.sqrt d : ℝ) : ℂ) with hs_def
  have hs : s * s = -(d : ℂ) := by
    have h2 : ((Real.sqrt d : ℝ) : ℂ) * ((Real.sqrt d : ℝ) : ℂ) = (d : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg d)]
      simp
    calc s * s = (Complex.I * Complex.I) * (((Real.sqrt d : ℝ) : ℂ) * ((Real.sqrt d : ℝ) : ℂ)) := by
          rw [hs_def]; ring
      _ = -(d : ℂ) := by rw [Complex.I_mul_I, h2]; ring
  have hdq : (0 : ℚ) < d := by exact_mod_cast hd
  induction hx using IntermediateField.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff] at hx
    subst hx
    refine ⟨(b : ℚ) / 2, 1 / 2, ?_⟩
    simp only [PI.UnitDetRootDefs.cmTheta, hs_def]
    push_cast
    ring
  | algebraMap r => exact ⟨r, 0, by simp⟩
  | add x y _ _ ihx ihy =>
    obtain ⟨p, q, rfl⟩ := ihx
    obtain ⟨p', q', rfl⟩ := ihy
    exact ⟨p + p', q + q', by push_cast; ring⟩
  | mul x y _ _ ihx ihy =>
    obtain ⟨p, q, rfl⟩ := ihx
    obtain ⟨p', q', rfl⟩ := ihy
    refine ⟨p * p' - d * q * q', p * q' + q * p', ?_⟩
    push_cast
    linear_combination (q : ℂ) * q' * hs
  | inv x _ ih =>
    obtain ⟨p, q, rfl⟩ := ih
    by_cases h0 : p = 0 ∧ q = 0
    · obtain ⟨rfl, rfl⟩ := h0
      exact ⟨0, 0, by simp⟩
    · have hN : p ^ 2 + d * q ^ 2 ≠ 0 := by
        intro hz
        apply h0
        have h1 : p ^ 2 = 0 := by nlinarith [sq_nonneg p, mul_nonneg hdq.le (sq_nonneg q)]
        have h2 : q ^ 2 = 0 := by nlinarith [sq_nonneg p, sq_nonneg q, mul_nonneg hdq.le (sq_nonneg q)]
        exact ⟨pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h1, pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h2⟩
      have hNc : ((p : ℂ) ^ 2 + (d : ℂ) * (q : ℂ) ^ 2) ≠ 0 := by exact_mod_cast hN
      refine ⟨p / (p ^ 2 + d * q ^ 2), -q / (p ^ 2 + d * q ^ 2), ?_⟩
      apply inv_eq_of_mul_eq_one_right
      clear_value s
      have e : ((p : ℂ) + q * s) * (((p / (p ^ 2 + d * q ^ 2) : ℚ) : ℂ) + ((-q / (p ^ 2 + d * q ^ 2) : ℚ) : ℂ) * s)
          = ((p : ℂ) ^ 2 - (q : ℂ) ^ 2 * (s * s)) / ((p : ℂ) ^ 2 + (d : ℂ) * (q : ℂ) ^ 2) := by
        push_cast
        ring
      rw [e, hs, div_eq_one_iff_eq hNc]
      ring

theorem norm_le_one_of_trace {F : Type*} [NormedField F] [IsUltrametricDist F] {y y' : F}
    (h : y * y' = 1) (ht : ‖y + y'‖ ≤ 1) : ‖y‖ ≤ 1 := by
  by_contra hlt
  push Not at hlt
  have hn : ‖y‖ * ‖y'‖ = 1 := by rw [← norm_mul, h, norm_one]
  have hy' : ‖y'‖ < ‖y‖ := by nlinarith [norm_nonneg y', norm_nonneg y]
  have hmax := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (ne_of_gt hy')
  rw [hmax, max_eq_left hy'.le] at ht
  linarith

theorem norm_eq_one {a : ℕ} {b c : ℤ} {d : ℕ} (hok : PI.UnitDetRootDefs.CmOK a b c d) (l : ℕ)
    [inst : Fact (Nat.Prime l)]
    (hT : ∀ T v : ℚ_[l], T ^ 2 + (d : ℚ_[l]) * v ^ 2 = 4 → ‖T‖ ≤ 1)
    (ι : ℂ ≃+* ℂ_[l]) {x : ℂ} (hx : x ∈ PI.UnitaryGroupMassFormula.UnitDetRoot.KF b d) (h1 : x * conj x = 1) :
    ‖ι x‖ = 1 := by
  have hd : 0 < d := hok.2.2.2.pos
  obtain ⟨p, q, rfl⟩ := exists_coords b d hd hx
  set s : ℂ := Complex.I * ((Real.sqrt d : ℝ) : ℂ) with hs_def
  have hs : s * s = -(d : ℂ) := by
    have h2 : ((Real.sqrt d : ℝ) : ℂ) * ((Real.sqrt d : ℝ) : ℂ) = (d : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg d)]
      simp
    calc s * s = (Complex.I * Complex.I) * (((Real.sqrt d : ℝ) : ℂ) * ((Real.sqrt d : ℝ) : ℂ)) := by
          rw [hs_def]; ring
      _ = -(d : ℂ) := by rw [Complex.I_mul_I, h2]; ring
  have hcs : conj s = -s := by simp [hs_def]
  have hconj : conj ((p : ℂ) + (q : ℂ) * s) = (p : ℂ) - (q : ℂ) * s := by
    rw [map_add, map_mul, hcs, map_ratCast, map_ratCast]; ring
  rw [hconj] at h1

  have hpq : (p ^ 2 + d * q ^ 2 : ℚ) = 1 := by
    have : (((p ^ 2 + d * q ^ 2 : ℚ)) : ℂ) = 1 := by
      push_cast
      linear_combination h1 + (q : ℂ) ^ 2 * hs
    exact_mod_cast this
  have hT' : ‖((2 * p : ℚ) : ℚ_[l])‖ ≤ 1 := by
    apply hT _ ((2 * q : ℚ) : ℚ_[l])
    have : ((2 * p) ^ 2 + d * (2 * q) ^ 2 : ℚ) = 4 := by linear_combination 4 * hpq
    exact_mod_cast congrArg (fun r : ℚ => (r : ℚ_[l])) this
  set y := ι ((p : ℂ) + (q : ℂ) * s)
  set y' := ι ((p : ℂ) - (q : ℂ) * s)
  have hyy : y * y' = 1 := by rw [← map_mul, h1, map_one]
  have hnr : ∀ r : ℚ, ‖(r : ℂ_[l])‖ = ‖(r : ℚ_[l])‖ := by
    intro r
    rw [← PadicComplex.norm_extends', map_ratCast, PadicComplex.coe_eq, map_ratCast]
  have hsum : y + y' = ((2 * p : ℚ) : ℂ_[l]) := by
    rw [← map_add]
    have : (p : ℂ) + (q : ℂ) * s + ((p : ℂ) - (q : ℂ) * s) = ((2 * p : ℚ) : ℂ) := by push_cast; ring
    rw [this, map_ratCast]
  have htr : ‖y + y'‖ ≤ 1 := by rw [hsum, hnr]; exact hT'
  have hle : ‖y‖ ≤ 1 := norm_le_one_of_trace hyy htr
  have hle' : ‖y'‖ ≤ 1 := norm_le_one_of_trace (by rw [mul_comm]; exact hyy) (by rw [add_comm]; exact htr)
  have hn : ‖y‖ * ‖y'‖ = 1 := by rw [← norm_mul, hyy, norm_one]
  nlinarith [norm_nonneg y, norm_nonneg y']

end GlobalTheory.TraceNormCoordinates
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PhiTopSource
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.TopStep

noncomputable section

namespace GlobalTheory.TopSrc

open GlobalTheory.DatumLaw

theorem of_zero {E : Type} [Field E] {n c : ℕ} (hc : c = 0) (r : Sp E (n + c) ≃ₗ[E] Sp E (n + c)) (κ : Sp E n ≃ₗ[E] Sp E n)
    (h : ∀ x, r (Loc.inX E n c x) = Loc.inX E n c (κ x)) :
    κ.toLinearMap ∘ₗ LinearMap.funLeft E E (Fin.castAdd c) = LinearMap.funLeft E E (Fin.castAdd c) ∘ₗ r.toLinearMap ∧
      LinearEquiv.det κ = LinearEquiv.det r ∧ Loc.n1Arg r = 0 := by
  subst hc
  have e : ∀ x : Sp E n, Loc.inX E n 0 x = x := fun x => by
    funext l
    rw [CongLevel.inX_apply]
    exact dif_pos l.2
  have hr : r = κ := LinearEquiv.ext fun x => by
    have := h x
    rwa [e, e] at this
  subst hr
  refine ⟨rfl, rfl, ?_⟩
  unfold Loc.n1Arg
  simp

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)

theorem phiTop_source (sharp : Bool) {m2 : ℕ} (hm : R.m = m2 + 2) (P : rowSG Pr sel mu) {g : AutY X R (m2 + 1)}
    (hg : g ∈ Jat (Pr := Pr) sharp (m2 + 1) P.1) (x : HomE X.E (R.N (m2 + 1) + cOf R (m2 + 1)) ((R.N R.m - 1) + 0)) :
    PhiTop Ch mu sharp m2 P.1 (x ∘ₗ g.toLinearMap) * rhoS Ch sel mu (m2 + 1) P ((LinearEquiv.det g : X.Eˣ) : X.E) =
      lamRow Ch mu sharp (m2 + 1) P.1 g.toLinearMap * PhiTop Ch mu sharp m2 P.1 x := by
  obtain ⟨a1, a2, a3, a4⟩ := ranks R (j := m2 + 1) (by omega)
  have b1 := rank_X'_eq R
  have b2 : R.r + (m2 + 1) * R.t ≤ R.N R.m - 1 + 0 := by
    rw [b1, add_zero]
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (by omega)) _
  have hb : R.r ≤ R.N R.m - 1 + 0 := by omega
  unfold rhoS
  unfold Jat at hg
  unfold PhiTop lamRow
  generalize R.N R.m - 1 = n at *
  have e1 := fun ψ χ => hm ▸ phiGS_eq (K := X.K) (P := P.1) ψ χ (k₀ := R.k) (rS := R.rS) (r := R.r) (t := R.t) (i := m2 + 1)
    (c' := cOf R (m2 + 1)) (n' := R.N (m2 + 1)) (c := 0) (n := n)
  have e2 := fun ψ χ => hm ▸ phiG_eq (K := X.K) (P := P.1) ψ χ (k₀ := R.k) (r := R.r) (t := R.t) (i := m2 + 1)
    (c' := cOf R (m2 + 1)) (n' := R.N (m2 + 1)) (c := 0) (n := n)
  split_ifs at hg ⊢
  · rw [e1]
    exact phiM_source _ _ (by omega) (by omega) a1 b2 _ inf_le_left
      (fun g hg => levG_of_JGsym (by omega) a4 (by omega) hg) hg x
  · rw [e2, LocE.lamGB, lamGv_eq]
    exact phiM_source _ _ (by omega) (by omega) a1 b2 _ inf_le_left
      (fun g hg => levG_of_JG (by omega) (by omega) hg) hg x
  · exact phiQ_source _ (by omega) a2 a3 hb hg x

theorem phiTop_level : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (m2 : ℕ), X.Ok → Pr.Ok → L.Ok Ch sel mu cst G m2 → ∀ (b : L.β (m2 + 1)) (P : rowSG Pr sel mu) (κ : GLint X.E (R.N (m2 + 1)) P.1) (c : X.Kˣ), (∀ hP : P.1 ∈ Pr.vGs, ∃ h : redGL _ P.1 κ ∈ (L.levG (m2 + 1) b ⟨P.1, hP⟩).H, c = (L.levG (m2 + 1) b ⟨P.1, hP⟩).lam ⟨_, h⟩) → (∀ hQ : P.1 ∈ QE sel (mu : Chr X.F X.E X.K), P.1 ∉ Pr.vGs → ∃ h : κ ∈ (L.levQ (m2 + 1) b ⟨P.1, hQ⟩).H, c = (L.levQ (m2 + 1) b ⟨P.1, hQ⟩).lam ⟨κ, h⟩) → ∀ x : HomE X.E (R.N (m2 + 1)) ((R.N R.m - 1) + 0), PhiTop Ch mu cst.sharp m2 P.1 (x ∘ₗ κ.1.toLinearMap ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1)))) * rhoS Ch sel mu (m2 + 1) P ((LinearEquiv.det κ.1 : X.Eˣ) : X.E) = (c : X.K) * PhiTop Ch mu cst.sharp m2 P.1 (x ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1)))) := by
  intro X Pr R Ch sel S mu cst L G m2 hX hPr hL b P κ c hG hQ x
  have hc : cOf R (m2 + 1) = 0 := by
    have := hL.hm
    unfold cOf
    omega
  have key : ∃ r ∈ Loc.Cbe (Jat (Pr := Pr) cst.sharp (m2 + 1) P.1) (L.h (m2 + 1) b P),
      (∀ x, r (Loc.inX X.E _ (cOf R (m2 + 1)) x) = Loc.inX X.E _ (cOf R (m2 + 1)) (κ.1 x)) ∧
        (c : X.K) = chiInv Ch sel mu cst (m2 + 1) P (L.h (m2 + 1) b P) r := by
    by_cases hP : P.1 ∈ Pr.vGs
    · obtain ⟨h, rfl⟩ := hG hP
      obtain ⟨g, hg, hred⟩ := (hL.grpG (m2 + 1) b ⟨P.1, hP⟩ _).1 h
      have hgi : g ∈ GLint X.E (R.N (m2 + 1)) P.1 := hL.int (m2 + 1) b P hg
      have e : redGL _ P.1 ⟨g, hgi⟩ = redGL _ P.1 κ := redGL_eq _ hred
      have h1 : redGL _ P.1 ((⟨g, hgi⟩ : GLint X.E (R.N (m2 + 1)) P.1)⁻¹ * κ) = 1 := by
        rw [map_mul, map_inv, e, inv_mul_cancel]
      have h2 := CongLevel.cong_mem_prCat X Pr R cst.sharp (m2 + 1) P.1 hP
        (fun a ha h0 => intAt_div_of_redP (qOf_notMem_sq hX hPr hP) ha h0) _ (hL.stabG (m2 + 1) b P hP)
        _ ((⟨g, hgi⟩ : GLint X.E (R.N (m2 + 1)) P.1)⁻¹ * κ).2 fun x hx => by
          rw [redV_redGL _ hx, h1, Units.val_one, Matrix.one_mulVec]
      have h3 : κ.1 ∈ prCat (Pr := Pr) cst.sharp (m2 + 1) P.1 (L.h (m2 + 1) b P) := by
        have := mul_mem hg h2
        rwa [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left] at this
      obtain ⟨r, hr, hrx⟩ := h3
      exact ⟨r, hr, hrx, hL.chrG (m2 + 1) b ⟨P.1, hP⟩ ⟨_, h⟩ κ.1 r hr hrx fun x hx => redV_redGL κ hx⟩
    · have hP' := (@Finset.mem_union _ (Classical.decEq _) _ _ _).1 P.2 |>.resolve_left hP
      obtain ⟨h, rfl⟩ := hQ hP' hP
      have h3 := h
      rw [hL.grpQ, Subgroup.mem_subgroupOf] at h3
      obtain ⟨r, hr, hrx⟩ := h3
      exact ⟨r, hr, hrx, hL.chrQ (m2 + 1) b ⟨P.1, hP'⟩ ⟨_, h⟩ r hr hrx⟩
  obtain ⟨r, hr, hrx, hcr⟩ := key
  rw [hL.last_h] at hr hcr
  have hJ : r ∈ Jat (Pr := Pr) cst.sharp (m2 + 1) P.1 := by simpa using hr.2
  obtain ⟨e1, e2, e3⟩ := of_zero hc r κ.1 hrx
  unfold chiInv at hcr
  rw [e3, hL.cst_ok.psi_int P 0 intAt_zero, inv_one, one_mul, inv_one, one_mul, mul_one] at hcr
  rw [e1, e2, hcr, ← LinearMap.comp_assoc]
  exact phiTop_source Ch sel mu cst.sharp hL.hm P hJ _

end GlobalTheory.TopSrc

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PhiTopTargetGen
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.TopStep

namespace GlobalTheory.TopTargetGen

open GlobalTheory.DatumLaw

section General

theorem coarse_rep {r t m i : ℕ} (ht : 0 < t) (h1 : r ≤ i) (h2 : i < r + m * t) :
    coarse r (List.replicate m t) i = (i - r) / t + 1 := by
  rw [coarse_of_le h1, blkIdx_replicate ht _ _ (by omega)]

theorem supSum_eq {κ : Type} [CommRing κ] {n r : ℕ} (hr : r ≤ n) (M : Matrix (Fin n) (Fin n) κ) (A : ℕ → ℕ → κ)
    (hA : ∀ i j : Fin n, A i.1 j.1 = M i j) :
    supSum r (Finset.range (r - 1)) M = ∑ i ∈ Finset.range (r - 1), A i (i + 1) := by
  unfold supSum
  have h1 : ∀ i : Fin n, (∑ j : Fin n, if i.val + 1 = j.val ∧ j.val < r ∧ i.val ∈ Finset.range (r - 1) then M i j else 0) =
      if i.1 < r - 1 then A i.1 (i.1 + 1) else 0 := fun i => by
    split_ifs with h
    · rw [Finset.sum_eq_single (⟨i.1 + 1, by omega⟩ : Fin n), if_pos ⟨rfl, by simp only; omega, Finset.mem_range.2 h⟩, ← hA]
      · intro j _ hj
        exact if_neg fun h' => hj (Fin.ext h'.1.symm)
      · intro h'
        exact absurd (Finset.mem_univ _) h'
    · exact Finset.sum_eq_zero fun j _ => if_neg fun h' => h (Finset.mem_range.1 h'.2.2)
  rw [Finset.sum_congr rfl fun i _ => h1 i,
    Fin.sum_univ_eq_sum_range (fun i => if i < r - 1 then A i (i + 1) else 0) n, ← Finset.sum_filter]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext i
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

theorem lamJ_eq {κ K : Type} [CommRing κ] [Field K] (ψ : AddChar κ K) (χ : ℕ → κˣ →* Kˣ) {n r t m : ℕ} (ht : 0 < t)
    (hn : n = r + m * t) (M : HJ κ n r t m) (A : ℕ → ℕ → κ)
    (hA : ∀ i j : Fin n, A i.1 j.1 = (M.1 : Matrix (Fin n) (Fin n) κ) i j) :
    ((lamJ ψ χ n r t m M : Kˣ) : K) = lamF ψ χ r r t m A := by
  unfold lamJ lamGen lamF
  rw [MonoidHom.mul_apply, Units.val_mul, supChar_val, supSum_eq (by omega) _ A hA, MonoidHom.comp_apply, detChar_apply,
    List.length_replicate, Units.coe_prod]
  congr 1
  · simp
  refine Finset.prod_congr rfl fun s hs => ?_
  rw [Finset.mem_range] at hs
  have hb : r + s * t + t ≤ n := blk_le hs hn.ge
  rw [← GlobalTheory.TopLaw.blkDet_eq_dB (coarse r (List.replicate m t)) (s + 1) (r + s * t) t hb ?_
    (Subgroup.inclusion (uniUT_le_blockUT n κ r _) M) A hA]
  · unfold ext0
    rw [dif_pos (Units.isUnit _), IsUnit.unit_of_val_units]
  · intro i hi
    by_cases h : i < r
    · rw [coarse_of_lt h]
      omega
    · rw [coarse_rep ht (by omega) (by omega), Nat.add_right_cancel_iff, Nat.div_eq_iff ht]
      omega

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {P : HeightOneSpectrum (𝓞 E)}

theorem red_entB (k₀ : ℕ) {n : ℕ} (ex : ℕ → ℕ) (j : GLint E n P) (p p' : Fin n) :
    redP P (LocE.entB (qOf P) k₀ 0 n 0 n ex ex (j.1.toLinearMap : HomE E (n + 0) (n + 0)) p.1 p'.1) =
      (redGL n P j : Matrix (Fin n) (Fin n) (𝓞 E ⧸ P.asIdeal)) p p' := by
  rw [GlobalTheory.TopStep.entB_zero _ _ _ _ _ rfl, dif_pos ⟨p.2, p'.2⟩]
  rfl

theorem lamY_zero (n : ℕ) (ex : ℕ → ℕ) : LocE.lamY P (qOf P) n 0 ex = stdAt E n P := by
  ext v
  unfold LocE.lamY
  rw [LastSteps.mem_sclLat, mem_stdAt]
  refine forall_congr' fun l => ?_
  have : LocE.scE n ex l.1 = 0 := if_pos l.2
  rw [this, zpow_zero, inv_one, one_mul]

theorem int_entB (k₀ : ℕ) {n : ℕ} (ex : ℕ → ℕ) (j : GLint E n P) :
    IntM P (n + 0) (n + 0) (LocE.entB (qOf P) k₀ 0 n 0 n ex ex (j.1.toLinearMap : HomE E (n + 0) (n + 0))) :=
  ent_int (n := n) (c := 0) (g := j.1) ((lamY_zero (E := E) (P := P) n ex).symm ▸ j.2)

theorem levG_of_mem (hq : ((qOf P : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) (k₀ : ℕ) {n r t m : ℕ} (ht : 0 < t) (hn : n = r + m * t)
    (ex : ℕ → ℕ) (j : GLint E n P) (h : redGL n P j ∈ HJ (𝓞 E ⧸ P.asIdeal) n r t m) :
    LevG P r 0 r t (n + 0) (LocE.entB (qOf P) k₀ 0 n 0 n ex ex (j.1.toLinearMap : HomE E (n + 0) (n + 0))) := by
  obtain ⟨h1, h2, h3⟩ := mem_uniUT.1 h
  have hb := mem_btG.1 h1
  have hr : r ≤ n := by omega
  refine ⟨int_entB k₀ ex j, fun p' hp' => ⟨?_, fun p hp hne hz => ?_⟩, fun i p p' a1 a2 a3 => ?_⟩
  · exact (red_entB k₀ ex j ⟨p', by omega⟩ ⟨p', by omega⟩).trans (h3 _ hp')
  · refine (red_entB k₀ ex j ⟨p, hp⟩ ⟨p', by omega⟩).trans ?_
    by_cases hpr : p < r
    · refine h2 _ _ hpr ?_
      have e1 := SymLevelInv.symIdx_cases r 0 p
      have e2 := SymLevelInv.symIdx_cases r 0 p'
      unfold Zs at hz
      simp only
      omega
    · refine hb _ _ ?_
      simp only
      rw [coarse_of_lt hp', coarse_of_le (by omega)]
      omega
  · refine intAt_div_of_redP hq (int_entB k₀ ex j p p' a2 (by omega)) ?_
    refine (red_entB k₀ ex j ⟨p, a2⟩ ⟨p', by omega⟩).trans (hb _ _ ?_)
    simp only
    rw [coarse_rep ht (show r ≤ p by omega) (by omega)]
    by_cases hpr : p' < r
    · rw [coarse_of_lt hpr]
      exact Nat.succ_pos _
    · rw [coarse_rep ht (show r ≤ p' by omega) (by omega)]
      have b1 : (p' - r) / t < i := by
        rw [Nat.div_lt_iff_lt_mul ht]
        omega
      have b2 : i ≤ (p - r) / t := by
        rw [Nat.le_div_iff_mul_le ht]
        omega
      omega

theorem phiG_target (hq : ((qOf P : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) (ψ : AddChar (𝓞 E ⧸ P.asIdeal) K)
    (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) {k₀ n r t m i c' n' : ℕ} (hm : m = i + 1) (hk : k₀ ≤ n) (ht : 0 < t)
    (hn : n = r + m * t) (j : GLint E n P) (h : redGL n P j ∈ HJ (𝓞 E ⧸ P.asIdeal) n r t m) (x : HomE E (n' + c') (n + 0)) :
    LocE.PhiG (qOf P) ψ χ false k₀ r t m c' n' 0 n ((j.1.toLinearMap : HomE E (n + 0) (n + 0)) ∘ₗ x) *
        LocE.unitV (χ i) ((LinearEquiv.det j.1 : Eˣ) : E) =
      ((lamJ ψ χ n r t m ⟨_, h⟩ : Kˣ) : K) * LocE.PhiG (qOf P) ψ χ false k₀ r t m c' n' 0 n x := by
  subst hm
  rw [phiG_eq, lamJ_eq ψ χ ht hn ⟨_, h⟩
    (red P (LocE.entB (qOf P) k₀ 0 n 0 n (fun i => i + 1) (fun i => i + 1) (j.1.toLinearMap : HomE E (n + 0) (n + 0))))
    (red_entB k₀ (fun i => i + 1) j)]
  refine (phiM_target (c := 0) (k₁ := r) (rS := 0) (r := r) ψ χ hk le_rfl (by rw [hn]; ring)
    (((HJ (𝓞 E ⧸ P.asIdeal) n r t (i + 1)).comap (redGL n P)).map (GLint E n P).subtype) ?_ ?_ (g := j.1) ⟨j, h, rfl⟩ x).trans ?_
  · rintro _ ⟨g, -, rfl⟩
    rw [lamY_zero]
    exact g.2
  · rintro _ ⟨g, hg, rfl⟩
    exact levG_of_mem hq k₀ ht hn _ g hg
  · rw [lamGvS_eq ψ χ le_rfl (int_entB k₀ _ j) hn.ge hn.ge]

end General

theorem phiTop_target_gen : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (m2 : ℕ) (P : HeightOneSpectrum (𝓞 X.E)), R.m = m2 + 2 → ((qOf P : ℕ) : 𝓞 X.E) ∉ P.asIdeal ^ 2 → ∀ (hP : P ∈ Pr.vGs) (j : GLint X.E (R.N R.m - 1) P) (h : redGL _ P j ∈ (rowTyG Ch (rP0 Ch) ⟨P, hP⟩).H) (x : HomE X.E (R.N (m2 + 1) + cOf R (m2 + 1)) (R.N R.m - 1)), PhiTop Ch mu false m2 P (j.1.toLinearMap ∘ₗ x) * LocE.unitV (chiP Ch P (m2 + 1)) ((LinearEquiv.det j.1 : X.Eˣ) : X.E) = (((rowTyG Ch (rP0 Ch) ⟨P, hP⟩).lam ⟨_, h⟩ : X.Kˣ) : X.K) * PhiTop Ch mu false m2 P x := by
  intro X Pr R Ch S mu m2 P hm hq hP j h x
  have h' : redGL _ P j ∈ HJ (𝓞 X.E ⧸ P.asIdeal) (R.N R.m - 1) R.r R.t R.m := by
    have := rowLevel_unipotent_group Ch ⟨P, hP⟩
    rw [this] at h
    exact h
  have e1 : psi0P Ch P = Ch.psi0 ⟨P, hP⟩ := dif_pos hP
  have e2 : chiP Ch P = chiAt Ch ⟨P, hP⟩ := dif_pos hP
  have hk : R.k ≤ R.N R.m - 1 := by
    have := r_le_X' R
    have := (ranks R (j := 0) (by omega)).2.2.2
    omega
  rw [rowLevel_unipotent_character Ch ⟨P, hP⟩ _ h h']
  unfold PhiTop
  rw [if_pos hP, if_neg Bool.false_ne_true, e1, e2]
  exact phiG_target hq _ _ hm hk R.t_odd.pos (rank_X'_eq R) j h' x

end GlobalTheory.TopTargetGen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PhiTopTargetTwist
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.TopStep

namespace GlobalTheory.TopLaw

section Gen

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {P : HeightOneSpectrum (𝓞 E)} {n r b : ℕ}

theorem parL_map_of_red (hq : ((qOf P : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) (j : GLint E n P)
    (h : redGL n P j ∈ HQ (𝓞 E ⧸ P.asIdeal) n r b) {v : Sp E n} (hv : v ∈ LocE.parL P (qOf P) r n 0) :
    j.1 v ∈ LocE.parL P (qOf P) r n 0 := by
  have hq0 := qOf_ne_zero (P := P)
  have hv' : ∀ l : Fin n, IntAt P (((qOf P : E) ^ (if r ≤ l.1 ∧ l.1 < n then (1 : ℤ) else 0))⁻¹ * v l) :=
    GlobalTheory.LastSteps.mem_sclLat.1 hv
  have hv0 : ∀ l : Fin n, IntAt P (v l) := fun l => by
    have h1 := hv' l
    split_ifs at h1
    · have h2 := (intAt_nat (P := P) (qOf P)).mul h1
      rwa [zpow_one, mul_inv_cancel_left₀ hq0] at h2
    · simpa using h1
  refine GlobalTheory.LastSteps.mem_sclLat.2 fun (l : Fin n) => ?_
  show IntAt P (((qOf P : E) ^ (if r ≤ l.1 ∧ l.1 < n then (1 : ℤ) else 0))⁻¹ * j.1 v l)
  split_ifs with hl
  · have e := apply_eq_sum (j.1 : Sp E n →ₗ[E] Sp E n) v l
    rw [LinearEquiv.coe_coe] at e
    rw [e, Finset.mul_sum, zpow_one]
    refine intAt_sum _ fun i _ => ?_
    by_cases hi : r ≤ i.1
    · have h1 := hv' i
      rw [if_pos ⟨hi, i.2⟩, zpow_one] at h1
      rw [← mul_assoc]
      exact h1.mul (glint_entry j l i)
    · have h0 : redP P (j.1 (Pi.single i 1) l) = 0 :=
        mem_btG.1 h l i (by rw [coarse_of_lt (Nat.not_le.1 hi), coarse_of_le hl.1]; omega)
      have h1 := (hv0 i).mul (intAt_div_of_redP hq (glint_entry j l i) h0)
      convert h1 using 1
      ring
  · rw [zpow_zero, inv_one, one_mul]
    exact mem_stdAt.1 (glint_mem j (mem_stdAt.2 hv0)) l

theorem mem_JQ_of_red (hq : ((qOf P : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) (j : GLint E n P)
    (h : redGL n P j ∈ HQ (𝓞 E ⧸ P.asIdeal) n r b) : j.1 ∈ LocE.JQ P (qOf P) r n 0 := by
  refine ⟨j.2, fun v => ⟨fun hv => ?_, parL_map_of_red hq j h⟩⟩
  have h1 := parL_map_of_red hq j⁻¹ (by rw [map_inv]; exact inv_mem h) hv
  have e : (j⁻¹).1 (j.1 v) = v := LinearEquiv.symm_apply_apply j.1 v
  exact e ▸ h1

theorem lamQB_eq_red (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (hn : n = r + b) (j : GLint E n P)
    (h : redGL n P j ∈ HQ (𝓞 E ⧸ P.asIdeal) n r b) :
    LocE.lamQB ξ r n j.1.toLinearMap = (((lamQ ξ n r b ⟨_, h⟩)⁻¹ : Kˣ) : K) := by
  have hA : GlobalTheory.DatumLaw.IntM P n n fun p p' => Loc.atN (j.1.toLinearMap (Loc.eN E n p')) p := fun p p' hp hp' => by
    show IntAt P (Loc.atN _ _)
    rw [GlobalTheory.LastSteps.eN_eq hp', Loc.atN, dif_pos hp]
    exact glint_entry j _ _
  have h1 := blkDet_eq_dB (coarse r [b]) 1 r (n - r) (by omega) (fun i hi => by
    by_cases hr : i < r
    · rw [coarse_of_lt hr]; omega
    · rw [coarse_of_le (Nat.not_lt.1 hr), blkIdx, if_pos (by omega)]; omega) ⟨_, h⟩
    (GlobalTheory.DatumLaw.red P fun p p' => Loc.atN (j.1.toLinearMap (Loc.eN E n p')) p) (fun i l => by
      show redP P (Loc.atN _ _) = _
      rw [GlobalTheory.LastSteps.eN_eq l.2, Loc.atN, dif_pos i.2]
      rfl)
  rw [← GlobalTheory.DatumLaw.redP_dB hA (by omega) (by omega)] at h1
  rw [lamQ_apply, Units.val_inv_eq_inv_val]
  show (GlobalTheory.DatumLaw.ext0 ξ (redP P (GlobalTheory.DatumLaw.dB (fun p p' => Loc.atN (j.1.toLinearMap (Loc.eN E n p')) p) r (n - r))))⁻¹ = _
  rw [← h1, GlobalTheory.DatumLaw.ext0, dif_pos (Units.isUnit _), IsUnit.unit_of_val_units]

end Gen

theorem phiTop_target_twist : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (m2 : ℕ) (P : HeightOneSpectrum (𝓞 X.E)), R.m = m2 + 2 → ((qOf P : ℕ) : 𝓞 X.E) ∉ P.asIdeal ^ 2 → P ∉ Pr.vGs → ∀ (sharp : Bool) (Q : Finset (HeightOneSpectrum (𝓞 X.E))) (hQ : P ∈ Q) (j : GLint X.E (R.N R.m - 1) P) (h : redGL _ P j ∈ (rowTyQ R (mu : Chr X.F X.E X.K) Q ⟨P, hQ⟩).H) (x : HomE X.E (R.N (m2 + 1) + cOf R (m2 + 1)) (R.N R.m - 1)), PhiTop Ch mu sharp m2 P (j.1.toLinearMap ∘ₗ x) * LocE.unitV (resChar (mu : Chr X.F X.E X.K) P)⁻¹ ((LinearEquiv.det j.1 : X.Eˣ) : X.E) = (((rowTyQ R (mu : Chr X.F X.E X.K) Q ⟨P, hQ⟩).lam ⟨_, h⟩ : X.Kˣ) : X.K) * PhiTop Ch mu sharp m2 P x := by
  intro X Pr R Ch S mu m2 P hm hq hP sharp Q hQ j h x
  obtain ⟨a1, a2, a3, -⟩ := GlobalTheory.DatumLaw.ranks R (j := m2 + 1) (by omega)
  unfold PhiTop
  rw [if_neg hP]
  have h1 := GlobalTheory.DatumLaw.phiQ_target (resChar (mu : Chr X.F X.E X.K) P) (k₀ := R.k) (r := R.r) (c' := cOf R (m2 + 1))
    (n' := R.N (m2 + 1)) (c := 0) (n := R.N R.m - 1) (kj := R.r) (by omega) (r_le_X' R) rfl (by omega)
    (mem_JQ_of_red hq j h) x
  exact h1.trans (congrArg (· * _) (lamQB_eq_red _ (rank_X'_eq R) j h))

end GlobalTheory.TopLaw
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.StandardOrbitSeriesValuationBoundZeroStatement
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual addC thetaInZ sumE)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standardOrbitSeries_valuationBound_zero : ∀ (Lc : product_zeroth_first_parts.Loc) (ep : ℂ_[Lc.l]) (be : MvPowerSeries (ZMod Lc.d) ℂ_[Lc.l]), ‖ep‖ = 1 → BeStd Lc.l Lc.d be → OrbitPlaces.OrbitThetaExpansion Lc ep (-1) be → product_zeroth_first_parts.KvalGe Lc.N0 Lc.N1 Lc.l Lc.nu Lc.Th 0 := by
  first | exact @GlobalTheory.KerZero.kvalGe_zero | exact GlobalTheory.KerZero.kvalGe_zero | (intros; apply GlobalTheory.KerZero.kvalGe_zero <;> assumption)
end

