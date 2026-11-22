import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0015
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaBdRPlusSurjectiveKerUnitsEquivariant
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0349
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0428
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0561
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0405
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0003
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0568
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0406
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0257
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0248
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0569

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaConjBoundedCompatibleBreuilKisinFrames
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.HTBound

section mat
variable {𝕜 : Type*} [NormedField 𝕜] [IsUltrametricDist 𝕜] {m n k : Type*} [Fintype n]

theorem nsub_max (x y : 𝕜) : ‖x - y‖ ≤ max ‖x‖ ‖y‖ := by
  simpa [sub_eq_add_neg, norm_neg] using IsUltrametricDist.norm_add_le_max x (-y)

theorem bnd_mul {A : Matrix m n 𝕜} {B : Matrix n k 𝕜} {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hA : ∀ i j, ‖A i j‖ ≤ r) (hB : ∀ i j, ‖B i j‖ ≤ s) : ∀ i j, ‖(A * B) i j‖ ≤ r * s := by
  intro i j
  rw [Matrix.mul_apply]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (mul_nonneg hr hs) fun x _ => ?_
  rw [norm_mul]
  exact mul_le_mul (hA _ _) (hB _ _) (norm_nonneg _) hr

theorem bnd_add {A B : Matrix m k 𝕜} {r : ℝ} (hA : ∀ i j, ‖A i j‖ ≤ r) (hB : ∀ i j, ‖B i j‖ ≤ r) :
    ∀ i j, ‖(A + B) i j‖ ≤ r := fun i j =>
  (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hA i j) (hB i j))

theorem bnd_sub {A B : Matrix m k 𝕜} {r : ℝ} (hA : ∀ i j, ‖A i j‖ ≤ r) (hB : ∀ i j, ‖B i j‖ ≤ r) :
    ∀ i j, ‖(A - B) i j‖ ≤ r := fun i j =>
  (nsub_max _ _).trans (max_le (hA i j) (hB i j))

theorem bnd_smul {A : Matrix m k 𝕜} {r : ℝ} (a : 𝕜) (hA : ∀ i j, ‖A i j‖ ≤ r) :
    ∀ i j, ‖(a • A) i j‖ ≤ ‖a‖ * r := fun i j => by
  rw [Matrix.smul_apply, smul_eq_mul, norm_mul]
  exact mul_le_mul_of_nonneg_left (hA i j) (norm_nonneg a)

end mat

variable {l : ℕ} [hl : Fact l.Prime]

theorem th_le (x : Ainf l) : ‖((Per.θD l).comp (aDp l)) x‖ ≤ 1 := by
  rw [RingHom.comp_apply, (GlobalTheory.MemLoc.thetaD_props l).2.2.2.1]
  exact (GlobalTheory.RingBasics.mem_OC _).1 (Per.θ l x).2

theorem norm_l : ‖((l : ℕ) : ℂ_[l])‖ = (l : ℝ)⁻¹ := by
  rw [GlobalTheory.RingBasics.norm_eq_val, PadicComplex.valuation_p]
  simp

theorem th_pow_dvd (n : ℕ) (x : Ainf l) (h : ((l : ℕ) : Ainf l) ^ n ∣ x) :
    ‖((Per.θD l).comp (aDp l)) x‖ ≤ ((l : ℝ) ^ n)⁻¹ := by
  obtain ⟨w, rfl⟩ := h
  rw [map_mul, map_pow, map_natCast, norm_mul, norm_pow, norm_l, inv_pow]
  exact mul_le_of_le_one_right (by positivity) (th_le w)

theorem th_gal {K : FinExt l} (bk : BK K) (g : ↥(GK K)) (s : bk.S) :
    ((Per.θD l).comp (aDp l)) (Per.σA (g : GQ l) (bk.ev s)) = ((Per.θD l).comp (aDp l)) (bk.ev s) := by
  simp only [RingHom.comp_apply, (GlobalTheory.MemLoc.thetaD_props l).2.2.2.1, GlobalTheory.RingBasics.θ_σA]
  obtain ⟨r, hr⟩ := bk.str.surjective (Ideal.Quotient.mk _ s)
  rw [bk.θ_ev r s hr.symm]
  refine (GlobalTheory.RingIface.sigO_coe l (g : GQ l) (intToOC K r)).trans ?_
  rw [coe_intToOC, GlobalTheory.RingBasics.σC_coe]
  congr 1
  exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 g.2 _ (r : ↥K.1).2

theorem zl_unique (f g : ℤ_[l] →+* ℂ_[l]) (hf : ∀ x, ‖f x‖ ≤ 1) (hg : ∀ x, ‖g x‖ ≤ 1) (x : ℤ_[l]) :
    f x = g x := by
  have key : ∀ n : ℕ, ‖f x - g x‖ ≤ ‖((l : ℕ) : ℂ_[l])‖ ^ n := by
    intro n
    obtain ⟨u, hu⟩ := Ideal.mem_span_singleton'.1 (PadicInt.appr_spec n x)
    have e : x = ((x.appr n : ℕ) : ℤ_[l]) + u * ((l : ℕ) : ℤ_[l]) ^ n := by rw [hu]; ring
    rw [e, map_add, map_add, map_natCast, map_natCast, add_sub_add_left_eq_sub, map_mul, map_mul, map_pow,
      map_pow, map_natCast, map_natCast, ← sub_mul, norm_mul, norm_pow]
    exact mul_le_of_le_one_left (by positivity)
      ((nsub_max _ _).trans (max_le (hf u) (hg u)))
  have ht := tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) (GlobalTheory.RingBasics.norm_p_lt (p := l))
  have h0 := ge_of_tendsto' ht key
  exact sub_eq_zero.1 (norm_le_zero_iff.1 h0)

theorem th_zl (z : ℤ_[l]) :
    ((Per.θD l).comp (aDp l)) (algebraMap ℤ_[l] (Ainf l) z) = algebraMap (Om l) ℂ_[l] (zOm l z) :=
  zl_unique (((Per.θD l).comp (aDp l)).comp (algebraMap ℤ_[l] (Ainf l)))
    ((algebraMap (Om l) ℂ_[l]).comp (zOm l)) (fun _ => th_le _) (fun x => by
      simp [zOm]
      exact PadicInt.norm_le_one x) z

theorem pow_dvd_of_inclW (k : ℕ) (a : Ainf l) (h : ((l : ℕ) : WCb l) ^ k ∣ inclW l a) :
    ((l : ℕ) : Ainf l) ^ k ∣ a := by
  induction k generalizing a with
  | zero => simp
  | succ k ih =>
    obtain ⟨c, hc⟩ := h
    have h0 : a.coeff 0 = 0 := by
      have h1 : (inclW l a).coeff 0 = 0 := by
        rw [hc, pow_succ', mul_assoc]; exact coeff_zero_l_mul _
      change algebraMap (OCb l) (Cb l) (a.coeff 0) = 0 at h1
      exact (map_eq_zero_iff _ (IsFractionRing.injective (OCb l) (Cb l))).1 h1
    obtain ⟨b, rfl⟩ := ainf_exists_l_mul_of_coeff_zero a h0
    have hl0 : ((l : ℕ) : WCb l) ≠ 0 := fun h => by
      have h1 := congrArg (fun x : WCb l => x.coeff 1) h
      simp [WittVector.coeff_p] at h1
    have hb : ((l : ℕ) : WCb l) ^ k ∣ inclW l b := by
      refine ⟨c, mul_left_cancel₀ hl0 ?_⟩
      rw [← mul_assoc, ← pow_succ', ← hc, map_mul, map_natCast]
    exact pow_succ' ((l : ℕ) : Ainf l) k ▸ mul_dvd_mul_left _ (ih b hb)

theorem bounded_compat : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (N : ℕ), ∃ Bd : ℝ, ∀ (N' d d' n : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l])) (ρ' : ↥(GK K) → Matrix (Fin d') (Fin d') (ℤ_[l])) (F : Frame bk N' d ρ) (F' : Frame bk N d' ρ') (Y : Matrix (Fin d) (Fin d) (Ainf l)) (Y' : Matrix (Fin d') (Fin d') (Ainf l)), N' = N → Y.map (inclW l) = inclW l τ ^ N • F.T → Y'.map (inclW l) = inclW l τ ^ N • F'.T → ∀ (g : ↥(GK K)) (U : Matrix (Fin d) (Fin d) (ℂ_[l])) (U' : Matrix (Fin d') (Fin d') (ℂ_[l])), U * Y.map ((Per.θD l).comp (aDp l)) = Y.map ((Per.θD l).comp (aDp l)) * (F.ε g).map ((Per.θD l).comp (aDp l)) → U' * Y'.map ((Per.θD l).comp (aDp l)) = Y'.map ((Per.θD l).comp (aDp l)) * (F'.ε g).map ((Per.θD l).comp (aDp l)) → (∀ i j, ‖U i j‖ ≤ Bd) ∧ (∀ i j, ‖U' i j‖ ≤ Bd) ∧ ∀ (Pi : Matrix (Fin d) (Fin d') (ℤ_[l])) (R : Matrix (Fin d) (Fin d') (bk.S)), (∀ g i j, (l : ℤ_[l]) ^ n ∣ (Pi * ρ' g - ρ g * Pi) i j) → (∀ i j, (l : WCb l) ^ n ∣ (zW Pi * F'.T - F.T * R.map bk.evW) i j) → ∀ i j, ‖(U * Pi.map (fun x => algebraMap (Om l) ℂ_[l] (zOm l x)) - Pi.map (fun x => algebraMap (Om l) ℂ_[l] (zOm l x)) * U') i j‖ ≤ Bd * ((l : ℝ) ^ n)⁻¹ := by
  intro l _ K bk τ hτ N
  have hs0 := GlobalTheory.T.theta_ainf_period_pow_ne_zero l K bk τ hτ (2 * N)
  set s := ((Per.θD l).comp (aDp l)) (τ ^ (2 * N)) with hs
  have hc0 : 0 < ‖s‖ := norm_pos_iff.2 hs0
  have hc1 : ‖s‖ ≤ 1 := th_le _
  have hci : 1 ≤ ‖s‖⁻¹ := (one_le_inv₀ hc0).2 hc1
  refine ⟨‖s‖⁻¹ * ‖s‖⁻¹, ?_⟩
  intro N' d d' n ρ ρ' F F' Y Y' hN hY hY' g U U' hU hU'
  subst N'
  have hb1 : ∀ {m k : Type} (M : Matrix m k (Ainf l)), ∀ i j, ‖(M.map ((Per.θD l).comp (aDp l))) i j‖ ≤ 1 :=
    fun M i j => th_le _

  have inv : ∀ {e : ℕ} {σ : ↥(GK K) → Matrix (Fin e) (Fin e) ℤ_[l]} (G : Frame bk N e σ)
      (Z : Matrix (Fin e) (Fin e) (Ainf l)), Z.map (inclW l) = inclW l τ ^ N • G.T →
      ∃ Z₁ : Matrix (Fin e) (Fin e) (Ainf l),
        Z.map ((Per.θD l).comp (aDp l)) * Z₁.map ((Per.θD l).comp (aDp l)) = s • 1 := by
    intro e σ G Z hZ
    obtain ⟨Z₀, Z₁, h0, h1⟩ := GlobalTheory.T.breuilKisinPreframe_bounded_poles l K bk τ hτ N e σ G.toPre
    have e0 : Z₀ = Z := by
      refine Matrix.ext fun i j => ?_
      apply inclW_injective
      have := congrFun (congrFun (h0.trans hZ.symm) i) j
      simpa using this
    subst e0
    refine ⟨Z₁, ?_⟩
    rw [← Matrix.map_mul, h1]
    refine Matrix.ext fun i j => ?_
    by_cases hij : i = j <;> simp [Matrix.smul_apply, Matrix.one_apply, hij, s]
  obtain ⟨Y₁, hY₁⟩ := inv F Y hY
  obtain ⟨Y₁', hY₁'⟩ := inv F' Y' hY'

  have solve : ∀ {e : ℕ} (y y₁ x V : Matrix (Fin e) (Fin e) ℂ_[l]), y * y₁ = s • 1 → V * y = y * x →
      V = s⁻¹ • (y * x * y₁) := by
    intro e y y₁ x V h1 h2
    rw [← h2, Matrix.mul_assoc, h1, Matrix.mul_smul, Matrix.mul_one, smul_smul, inv_mul_cancel₀ hs0, one_smul]
  have bnd : ∀ {e : ℕ} {σ : ↥(GK K) → Matrix (Fin e) (Fin e) ℤ_[l]} (G : Frame bk N e σ)
      (Z Z₁ : Matrix (Fin e) (Fin e) (Ainf l)) (V : Matrix (Fin e) (Fin e) ℂ_[l]),
      Z.map ((Per.θD l).comp (aDp l)) * Z₁.map ((Per.θD l).comp (aDp l)) = s • 1 →
      V * Z.map ((Per.θD l).comp (aDp l)) = Z.map ((Per.θD l).comp (aDp l)) * (G.ε g).map ((Per.θD l).comp (aDp l)) →
      ∀ i j, ‖V i j‖ ≤ ‖s‖⁻¹ := by
    intro e σ G Z Z₁ V h1 h2
    rw [solve _ _ _ V h1 h2]
    have := bnd_smul s⁻¹ (bnd_mul (mul_nonneg zero_le_one zero_le_one) zero_le_one
      (bnd_mul zero_le_one zero_le_one (hb1 Z) (hb1 (G.ε g))) (hb1 Z₁))
    simpa [norm_inv] using this
  have hUb := bnd F Y Y₁ U hY₁ hU
  have hU'b := bnd F' Y' Y₁' U' hY₁' hU'
  have hle : ‖s‖⁻¹ ≤ ‖s‖⁻¹ * ‖s‖⁻¹ := le_mul_of_one_le_left (by positivity) hci
  refine ⟨fun i j => (hUb i j).trans hle, fun i j => (hU'b i j).trans hle, ?_⟩
  intro Pi R hequi hlink
  set θ' : Ainf l →+* ℂ_[l] := (Per.θD l).comp (aDp l) with hθ'
  have hD1 : ∀ i j, ((l : ℕ) : Ainf l) ^ n ∣ (Pi.map (algebraMap ℤ_[l] (Ainf l)) * Y' - Y * R.map bk.ev) i j := by
    intro i j
    apply pow_dvd_of_inclW
    have e1 : (Pi.map (algebraMap ℤ_[l] (Ainf l))).map (inclW l) = zW Pi := by
      refine Matrix.ext fun a b => ?_
      exact (inclWA l).commutes _
    have e2 : (R.map bk.ev).map (inclW l) = R.map bk.evW := by
      rw [Matrix.map_map]; rfl
    have e : (Pi.map (algebraMap ℤ_[l] (Ainf l)) * Y' - Y * R.map bk.ev).map (inclW l) =
        inclW l τ ^ N • (zW Pi * F'.T - F.T * R.map bk.evW) := by
      rw [Matrix.map_sub _ (map_sub (inclW l)), Matrix.map_mul, Matrix.map_mul, hY, hY', e1, e2,
        Matrix.mul_smul, Matrix.smul_mul, smul_sub]
    have := congrFun (congrFun e i) j
    rw [Matrix.map_apply] at this
    rw [this, Matrix.smul_apply, smul_eq_mul]
    exact Dvd.dvd.mul_left (hlink i j) _
  have hD2 := GlobalTheory.T.breuilKisinLatticeFrame_cocycles_linked l K bk N N d d' n ρ ρ' F F' Pi R hequi hlink g
  have hP : Pi.map (fun x => algebraMap (Om l) ℂ_[l] (zOm l x)) = (Pi.map (algebraMap ℤ_[l] (Ainf l))).map θ' := by
    refine Matrix.ext fun i j => ?_
    simp only [Matrix.map_apply]
    exact (th_zl _).symm
  have hR : ((R.map bk.ev).map (Per.σA (g : GQ l))).map θ' = (R.map bk.ev).map θ' := by
    refine Matrix.ext fun i j => ?_
    simp only [Matrix.map_apply]
    exact th_gal bk g _
  rw [hP]
  set P := (Pi.map (algebraMap ℤ_[l] (Ainf l))).map θ' with hPdef
  set y := Y.map θ' with hy
  set y' := Y'.map θ' with hy'
  set Ry := (R.map bk.ev).map θ' with hRy
  set e := (F.ε g).map θ' with he
  set e' := (F'.ε g).map θ' with he'
  have eD1 : P * y' - y * Ry = (Pi.map (algebraMap ℤ_[l] (Ainf l)) * Y' - Y * R.map bk.ev).map θ' := by
    rw [Matrix.map_sub _ (map_sub θ'), Matrix.map_mul, Matrix.map_mul]
  have eD2 : e * Ry - Ry * e' = (F.ε g * (R.map bk.ev).map (Per.σA (g : GQ l)) - R.map bk.ev * F'.ε g).map θ' := by
    rw [Matrix.map_sub _ (map_sub θ'), Matrix.map_mul, Matrix.map_mul, hR]
  set q : ℝ := ((l : ℝ) ^ n)⁻¹ with hqdef
  have hq : 0 ≤ q := by positivity
  have bD1 : ∀ i j, ‖(P * y' - y * Ry) i j‖ ≤ q := by
    rw [eD1]; intro i j; exact th_pow_dvd n _ (hD1 i j)
  have bD2 : ∀ i j, ‖(e * Ry - Ry * e') i j‖ ≤ q := by
    rw [eD2]; intro i j; exact th_pow_dvd n _ (hD2 i j)
  have key : (U * P - P * U') * y' = U * (P * y' - y * Ry) + y * (e * Ry - Ry * e') - (P * y' - y * Ry) * e' := by
    rw [Matrix.sub_mul, Matrix.mul_assoc P U' y', hU', Matrix.mul_assoc U P y']
    simp only [Matrix.mul_sub, Matrix.sub_mul, ← Matrix.mul_assoc, hU]
    abel
  have hX : U * P - P * U' = s⁻¹ • ((U * P - P * U') * y' * Y₁'.map θ') := by
    rw [Matrix.mul_assoc (U * P - P * U') y', hY₁', Matrix.mul_smul, Matrix.mul_one, smul_smul,
      inv_mul_cancel₀ hs0, one_smul]
  intro i j
  rw [hX, key]
  have hsq : q ≤ ‖s‖⁻¹ * q := le_mul_of_one_le_left hq hci
  have b1 : ∀ i j, ‖(U * (P * y' - y * Ry)) i j‖ ≤ ‖s‖⁻¹ * q := bnd_mul (by positivity) hq hUb bD1
  have b2 : ∀ i j, ‖(y * (e * Ry - Ry * e')) i j‖ ≤ ‖s‖⁻¹ * q := fun i j =>
    (bnd_mul zero_le_one hq (hb1 Y) bD2 i j).trans (by rw [one_mul]; exact hsq)
  have b3 : ∀ i j, ‖((P * y' - y * Ry) * e') i j‖ ≤ ‖s‖⁻¹ * q := fun i j =>
    (bnd_mul hq zero_le_one bD1 (hb1 _) i j).trans (by rw [mul_one]; exact hsq)
  have b4 := bnd_smul s⁻¹ (bnd_mul (by positivity) zero_le_one (bnd_sub (bnd_add b1 b2) b3) (hb1 Y₁'))
  calc _ ≤ _ := b4 i j
    _ = _ := by rw [norm_inv]; ring

end GlobalTheory.HTBound
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerDimensionPosOfCuspidalCharacter
section
noncomputable section

open GlobalTheory.GLq GlobalTheory.Published Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

namespace GlobalTheory.GLq.Generic

variable {g : ℕ} [Fact g.Prime]

theorem br_zero_self {d : ℕ} (M : Mt g d) : br 0 d M = M := by
  funext i j
  simp [br, entN, i.isLt, j.isLt]

theorem res_zero_self {d : ℕ} (χ : Gn g d → ℂ) (h : Gn g d) : res 0 d χ 1 h = χ h := by
  unfold res
  have hI : ∀ x : Gn g d, InPar 0 (x : Mt g d) := fun x i j hj _ => absurd hj (Nat.not_lt_zero _)
  have hT : ∀ x : Gn g d, tl 0 (x : Mt g d) = ((1 : Gn g 0) : Mt g 0) := fun x => by
    funext i; exact i.elim0
  simp only [hI, hT, br_zero_self, true_and, zero_mul, pow_zero, inv_one, one_mul, Units.val_inj]
  rw [Finset.sum_ite_eq']
  simp

theorem wh_zero_fun (ψ : AddChar (ZMod g) ℂ) (n : ℕ) : wh ψ (fun _ : Gn g n => (0 : ℂ)) = 0 := by
  simp [wh, tr]

theorem isClass_of_isIrr {G : Type} [Group G] {χ : G → ℂ} (h : IsIrr χ) : IsClass χ := by
  obtain ⟨V, _, hV⟩ := h
  intro x y
  rw [← hV, ← hV]
  exact FDRep.char_conj V x y

end GlobalTheory.GLq.Generic

theorem GlobalTheory.GLq.wh_cusp_pos : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ), ψ ≠ 1 → ∀ (d : ℕ)
    (χ : Gn g d → ℂ), IsCusp χ → ∃ m : ℕ, 0 < m ∧ wh ψ χ = m := by
  intro g _ ψ hψ d χ hc
  have hc' := hc
  obtain ⟨hd, hirr, _⟩ := hc'
  have hder := GlobalTheory.T.classFunction_degree_eq_sum_derivatives g ψ hψ d χ hd (GlobalTheory.GLq.Generic.isClass_of_isIrr hirr)
  rw [Finset.sum_eq_single 0] at hder
  rotate_left
  · intro m hm hm0
    have hmd : m < d := Finset.mem_range.mp hm
    have hz : res m (d - m) χ 1 = fun _ => 0 := by
      funext y
      exact GlobalTheory.T.harishChandraRestrictionTwoBlock_cuspidal_eq_zero g d m χ hc (Nat.pos_of_ne_zero hm0) hmd 1 y
    have : der ψ m χ 1 = 0 := by
      show wh ψ (res m (d - m) χ 1) = 0
      rw [hz]
      exact GlobalTheory.GLq.Generic.wh_zero_fun ψ _
    rw [this, zero_mul]
  · intro h0
    exact absurd (Finset.mem_range.mpr hd) h0
  have h0 : der ψ 0 χ 1 = wh ψ χ := by
    change wh ψ (n := d) (res 0 d χ 1) = wh ψ χ
    congr 1
    funext h
    exact GlobalTheory.GLq.Generic.res_zero_self χ h
  rw [h0] at hder
  obtain ⟨V, _, hV⟩ := hirr
  have hchar : IsChar χ := ⟨V, hV⟩
  obtain ⟨d', hd'pos, hd'⟩ := (GlobalTheory.T.groupAlgebraTrace_idempotent_and_irreducible_degree (Gn g d) (eU g d ψ) χ).2.1 ⟨V, ‹_›, hV⟩
  obtain ⟨n, hn⟩ := (GlobalTheory.T.groupAlgebraTrace_idempotent_and_irreducible_degree (Gn g d) (eU g d ψ) χ).1 (GlobalTheory.T.whittakerJacquetIdempotents_properties_primeField g d 0 0 ψ).1 hchar
  have hwh : wh ψ χ = n := hn
  refine ⟨n, Nat.pos_of_ne_zero ?_, hwh⟩
  rintro rfl
  rw [hwh, Nat.cast_zero, zero_mul, hd'] at hder
  exact absurd hder (by exact_mod_cast hd'pos.ne')

example : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ), ψ ≠ 1 → ∀ (d : ℕ) (χ : Gn g d → ℂ), IsCusp χ → ∃ m : ℕ, 0 < m ∧ wh ψ χ = m := GlobalTheory.GLq.wh_cusp_pos
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WittCompletedTiltColumnsOfRightInverseModPow
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.CardJ

variable {R : Type*} [CommRing R] [IsLocalRing R]

theorem isUnit_of_mul_eq_one_add_pow (p : R) (hp : ¬ IsUnit p) {n : ℕ} (hn : 1 ≤ n) {x y z : R}
    (h : x * y = 1 + p ^ n * z) : IsUnit x := by
  have hpm : p ∈ IsLocalRing.maximalIdeal R := (IsLocalRing.mem_maximalIdeal _).2 hp
  have hmem : p ^ n * z ∈ IsLocalRing.maximalIdeal R := by
    apply Ideal.mul_mem_right
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [pow_succ]; exact Ideal.mul_mem_left _ _ hpm
  have hu : IsUnit (1 + p ^ n * z) := by
    by_contra hc
    have h1 : (1 + p ^ n * z) ∈ IsLocalRing.maximalIdeal R := (IsLocalRing.mem_maximalIdeal _).2 hc
    have h2 : (1 : R) ∈ IsLocalRing.maximalIdeal R := by
      have := Ideal.sub_mem _ h1 hmem
      simpa using this
    exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).2 h2)
  rw [← h] at hu
  exact isUnit_of_mul_isUnit_left hu

end GlobalTheory.CardJ

namespace GlobalTheory.CardJ

variable {R : Type*} [CommRing R] [IsLocalRing R]

theorem exists_cols_of_rightInv (p : R) (hp : ¬ IsUnit p) (d d' n : ℕ)
    (Q : Matrix (Fin d) (Fin d') R) (S : Matrix (Fin d') (Fin d) R)
    (U Uinv : Matrix (Fin d') (Fin d') R) (J : Finset (Fin d')) (hn : 1 ≤ n)
    (hQS : ∀ i j, p ^ n ∣ (Q * S - (1 : Matrix (Fin d) (Fin d) R)) i j) (hUU : Uinv * U = 1) (hUU' : U * Uinv = 1)
    (hJ : ∀ j ∉ J, ∀ i, p ^ n ∣ (Q * U) i j)
    (hker : ∀ v : Fin d' → R, (∀ i, p ^ n ∣ (Q *ᵥ v) i) → ∀ j ∈ J, p ∣ (Uinv *ᵥ v) j) :
    ∃ e : Fin d ≃ J, IsUnit (Q * U.submatrix id (fun k => (e k : Fin d'))) ∧
      ∀ i j, p ^ n ∣ (Q - (Q * U.submatrix id (fun k => (e k : Fin d'))) *
        Uinv.submatrix (fun k => (e k : Fin d')) id) i j := by
  classical
  set I : Ideal R := Ideal.span {p ^ n} with hI
  set π : R →+* R ⧸ I := Ideal.Quotient.mk I with hπ
  have hdvd : ∀ x : R, p ^ n ∣ x ↔ π x = 0 := fun x => by
    rw [hπ, Ideal.Quotient.eq_zero_iff_mem, hI, Ideal.mem_span_singleton]
  have hpm : p ∈ IsLocalRing.maximalIdeal R := (IsLocalRing.mem_maximalIdeal _).2 hp
  have hres0 : IsLocalRing.residue R p = 0 := (IsLocalRing.residue_eq_zero_iff p).2 hpm
  have hres : ∀ x : R, π x = 0 → IsLocalRing.residue R x = 0 := by
    intro x hx
    obtain ⟨y, rfl⟩ := (hdvd x).2 hx
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    simp [map_mul, map_pow, hres0]
  set M := Q * U with hM
  set S' := Uinv * S with hS'
  have hMS : M * S' = Q * S := by
    rw [hM, hS', Matrix.mul_assoc, ← Matrix.mul_assoc U, hUU', Matrix.one_mul]
  have hQS1 : ∀ i j, π ((Q * S) i j) = (1 : Matrix (Fin d) (Fin d) (R ⧸ I)) i j := by
    intro i j
    have := (hdvd _).1 (hQS i j)
    rw [Matrix.sub_apply, map_sub, sub_eq_zero] at this
    rw [this, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have hoff : ∀ j ∉ J, ∀ i, π (M i j) = 0 := fun j hj i => (hdvd _).1 (hJ j hj i)
  have hsum : ∀ (i : Fin d) (x : Fin d' → R ⧸ I),
      ∑ j, π (M i j) * x j = ∑ j : J, π (M i (j : Fin d')) * x j := by
    intro i x
    have h1 := Finset.sum_coe_sort J (fun j => π (M i j) * x j)
    rw [h1]
    symm
    apply Finset.sum_subset (Finset.subset_univ J)
    intro j _ hj; rw [hoff j hj i, zero_mul]

  set MJ : Matrix (Fin d) J R := M.submatrix id (fun j : J => (j : Fin d')) with hMJ
  set SJ : Matrix J (Fin d) R := S'.submatrix (fun j : J => (j : Fin d')) id with hSJ
  have hMJS : ∀ i k, π ((MJ * SJ) i k) = (1 : Matrix (Fin d) (Fin d) (R ⧸ I)) i k := by
    intro i k
    rw [← hQS1, ← hMS]
    simp only [Matrix.mul_apply, map_sum, map_mul, hMJ, hSJ, Matrix.submatrix_apply, id]
    exact (hsum i (fun j => π (S' j k))).symm

  have hE : ∀ j j0 : J, IsLocalRing.residue R ((SJ * MJ) j j0) = (1 : Matrix J J (IsLocalRing.ResidueField R)) j j0 := by
    intro j j0
    set c : Fin d' → R := fun j' => if h : j' ∈ J then (SJ * MJ - (1 : Matrix J J R)) ⟨j', h⟩ j0 else 0 with hc
    have hUc : Uinv *ᵥ (U *ᵥ c) = c := by
      rw [Matrix.mulVec_mulVec, hUU, Matrix.one_mulVec]
    have hQc : ∀ i, p ^ n ∣ (Q *ᵥ (U *ᵥ c)) i := by
      intro i
      rw [Matrix.mulVec_mulVec, ← hM, hdvd]
      have hA : (MJ.map π) * ((SJ * MJ - (1 : Matrix J J R)).map π) = 0 := by
        have h1 : (MJ.map π) * (SJ.map π) = 1 := by
          ext i k; rw [← Matrix.map_mul]; exact hMJS i k
        rw [Matrix.map_sub _ (fun a b => map_sub π a b), Matrix.map_mul, Matrix.map_one _ (map_zero π) (map_one π), Matrix.mul_sub,
          ← Matrix.mul_assoc, h1, Matrix.one_mul, Matrix.mul_one, sub_self]
      have h2 := congrFun (congrFun hA i) j0
      rw [Matrix.zero_apply, Matrix.mul_apply] at h2
      rw [← h2]
      simp only [Matrix.mulVec, dotProduct, map_sum, map_mul]
      rw [hsum i (fun j' => π (c j'))]
      refine Finset.sum_congr rfl (fun j' _ => ?_)
      simp [hc, hMJ, Matrix.map_apply]
    have hp1 := hker _ hQc j j.2
    rw [hUc] at hp1
    have hcj : c j = (SJ * MJ - (1 : Matrix J J R)) j j0 := by simp [hc]
    rw [hcj] at hp1
    obtain ⟨y, hy⟩ := hp1
    have := congrArg (IsLocalRing.residue R) hy
    rw [Matrix.sub_apply, map_sub, map_mul, hres0, zero_mul, sub_eq_zero] at this
    rw [this, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp

  have hcard : Fintype.card J = d := by
    set κ := IsLocalRing.ResidueField R
    set ρ : R →+* κ := IsLocalRing.residue R
    have hAB : (MJ.map ρ) * (SJ.map ρ) = 1 := by
      ext i k
      rw [← Matrix.map_mul, Matrix.map_apply]
      have h := hMJS i k
      have h0 : π ((MJ * SJ - (1 : Matrix (Fin d) (Fin d) R)) i k) = 0 := by
        rw [Matrix.sub_apply, map_sub, h, Matrix.one_apply, Matrix.one_apply]; split_ifs <;> simp
      have := hres _ h0
      rw [Matrix.sub_apply, map_sub, sub_eq_zero] at this
      rw [this, Matrix.one_apply, Matrix.one_apply]; split_ifs <;> simp
    have hBA : (SJ.map ρ) * (MJ.map ρ) = 1 := by
      ext j j0; rw [← Matrix.map_mul, Matrix.map_apply]; exact hE j j0
    have h1 : d ≤ Fintype.card J := by
      have := Matrix.rank_mul_le_left (MJ.map ρ) (SJ.map ρ)
      rw [hAB, Matrix.rank_one, Fintype.card_fin] at this
      exact this.trans (Matrix.rank_le_card_width _)
    have h2 : Fintype.card J ≤ d := by
      have := Matrix.rank_mul_le_left (SJ.map ρ) (MJ.map ρ)
      rw [hBA, Matrix.rank_one] at this
      exact (this.trans (Matrix.rank_le_card_width _)).trans (by rw [Fintype.card_fin])
    omega

  let e : Fin d ≃ J := (Fintype.equivFinOfCardEq hcard).symm
  refine ⟨e, ?_, ?_⟩
  · set T := Q * U.submatrix id (fun k => (e k : Fin d')) with hT
    set B := S'.submatrix (fun k => (e k : Fin d')) id with hB
    have hTe : ∀ i k, T i k = M i (e k) := by
      intro i k; simp [hT, hM, Matrix.mul_apply]
    have hTB : ∀ i k, π ((T * B) i k) = (1 : Matrix (Fin d) (Fin d) (R ⧸ I)) i k := by
      intro i k
      rw [← hQS1, ← hMS]
      simp only [Matrix.mul_apply, map_sum, map_mul, hTe, hB, Matrix.submatrix_apply, id]
      rw [hsum i (fun j => π (S' j k))]
      exact Equiv.sum_comp e (fun j : J => π (M i (j : Fin d')) * π (S' j k))
    have hdet : π ((T * B).det) = 1 := by
      rw [RingHom.map_det]
      have : π.mapMatrix (T * B) = 1 := by ext i k; exact hTB i k
      rw [this, Matrix.det_one]
    rw [Matrix.det_mul] at hdet
    have h0 : π (T.det * B.det - 1) = 0 := by rw [map_sub, hdet, map_one, sub_self]
    obtain ⟨z, hz⟩ := (hdvd _).2 h0
    rw [Matrix.isUnit_iff_isUnit_det]
    exact GlobalTheory.CardJ.isUnit_of_mul_eq_one_add_pow p hp hn (y := B.det) (z := z) (by rw [← hz]; ring)
  · intro i k
    rw [hdvd, Matrix.sub_apply, map_sub, sub_eq_zero]
    have hQ : Q = M * Uinv := by rw [hM, Matrix.mul_assoc, hUU', Matrix.mul_one]
    conv_lhs => rw [hQ]
    simp only [Matrix.mul_apply, map_sum, map_mul, Matrix.submatrix_apply, id]
    rw [hsum i (fun j => π (Uinv j k))]
    rw [← Equiv.sum_comp e (fun j : J => π (M i (j : Fin d')) * π (Uinv j k))]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    simp [hM, Matrix.mul_apply]

end GlobalTheory.CardJ

namespace GlobalTheory.CardJ

theorem exists_cols_of_rightInv_WCb : ∀ (l : ℕ) [Fact l.Prime] (d d' n : ℕ) (Q : Matrix (Fin d) (Fin d') (WCb l)) (S : Matrix (Fin d') (Fin d) (WCb l)) (U Uinv : Matrix (Fin d') (Fin d') (WCb l)) (J : Finset (Fin d')), 1 ≤ n → (∀ i j, (l : WCb l) ^ n ∣ (Q * S - (1 : Matrix (Fin d) (Fin d) (WCb l))) i j) → Uinv * U = 1 → U * Uinv = 1 → (∀ j ∉ J, ∀ i, (l : WCb l) ^ n ∣ (Q * U) i j) → (∀ v : Fin d' → WCb l, (∀ i, (l : WCb l) ^ n ∣ (Q *ᵥ v) i) → ∀ j ∈ J, (l : WCb l) ∣ (Uinv *ᵥ v) j) → ∃ e : Fin d ≃ J, IsUnit (Q * U.submatrix id (fun k => (e k : Fin d'))) ∧ ∀ i j, (l : WCb l) ^ n ∣ (Q - (Q * U.submatrix id (fun k => (e k : Fin d'))) * Uinv.submatrix (fun k => (e k : Fin d')) id) i j := by
  intro l _ d d' n Q S U Uinv J hn hQS hUU hUU' hJ hker
  haveI : PerfectRing (Cb l) l := GlobalTheory.OEDvr.perfectRing_Cb
  exact exists_cols_of_rightInv (l : WCb l) (WittVector.irreducible l).not_isUnit d d' n Q S U Uinv J
    hn hQS hUU hUU' hJ hker

end GlobalTheory.CardJ
end

