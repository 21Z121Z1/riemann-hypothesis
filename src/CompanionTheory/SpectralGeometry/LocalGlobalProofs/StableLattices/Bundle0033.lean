import Mathlib
import CompanionTheory.AutomorphicTheory.BesselOrbitBounds.BesselMapUniqueness.BesselMapUniqGap
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.SmoothCyc
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.PhMeas
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.IwaCore
import CompanionTheory.AutomorphicTheory.ZuckermanCommutation.ZuckermanFunctors.IsSimpleFam

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.TorusConjugacy
section
open Matrix Formalism.QuantumDeterminants
open scoped ComplexConjugate

noncomputable section

namespace GlobalTheory.CompanionTheory.BmuTorConj

theorem cStd_ne : cStd ≠ 0 := by
  simp [cStd, Complex.I_ne_zero]

theorem exists_scale (r : ℕ) (c : Fin r → ℂ) (hc : ∀ a, c a ≠ 0) :
    ∃ T : ℕ → ℂ, (∀ n, T n ≠ 0) ∧ (∀ n, r ≤ n → T n = 1) ∧
      ∀ a : Fin r, c a * T a.val = cStd * T (a.val + 1) := by
  classical
  obtain ⟨c', hc'd⟩ : ∃ f : ℕ → ℂ, f = fun m => if h : m < r then c ⟨m, h⟩ else 1 := ⟨_, rfl⟩
  have hc' : ∀ m, c' m ≠ 0 := fun m => by
    by_cases h : m < r
    · simp only [hc'd, dif_pos h]; exact hc _
    · simp only [hc'd, dif_neg h]; exact one_ne_zero
  refine ⟨fun n => ∏ m ∈ Finset.Ico n r, (cStd / c' m), ?_, ?_, ?_⟩
  · intro n
    exact Finset.prod_ne_zero_iff.mpr fun m _ => div_ne_zero cStd_ne (hc' m)
  · intro n hn
    simp [Finset.Ico_eq_empty_of_le hn]
  · intro a
    simp only
    rw [Finset.prod_eq_prod_Ico_succ_bot a.isLt]
    have hca : c' a.val = c a := by simp only [hc'd, dif_pos a.isLt]
    rw [hca]
    have hcz := hc a
    field_simp

theorem hpk_row (k r : ℕ) (p q : Fin (2 * r + k + 1)) (hpq : p.val + q.val = 2 * r + k)
    (h : p.val < r ∨ q.val < r) (j : Fin (2 * r + k + 1)) :
    Hpk k r p j = if j = q then 1 else 0 := by
  have hp := p.isLt
  have hq := q.isLt
  unfold Hpk
  by_cases hjq : j = q
  · subst hjq
    rw [if_pos rfl]
    rcases h with h | h
    · rw [if_pos ⟨h, hpq⟩]
    · rw [if_neg (by omega), if_pos ⟨h, hpq⟩]
  · rw [if_neg hjq]
    have hjv : j.val ≠ q.val := fun e => hjq (Fin.ext e)
    rw [if_neg (by omega), if_neg (by omega), if_neg]
    rintro ⟨h1, h2, -⟩
    omega

theorem uw_col (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (hh : h ∈ UWset k r z) (p : Fin (2 * r + k + 1)) (hp : p.val < r ∨ r + k < p.val)
    (i : Fin (2 * r + k + 1)) : h i p = if i = p then 1 else 0 := by
  obtain ⟨-, hcols, -⟩ := hh
  have hplt := p.isLt
  rcases hp with hp | hp
  · have e : eI k r ⟨p.val, hp⟩ = p := Fin.ext rfl
    have hx := congrFun (hcols ⟨p.val, hp⟩).1 i
    rw [e] at hx
    simpa [bvec, mulVec_single, Pi.single_apply] using hx
  · have e : esI k r ⟨2 * r + k - p.val, by omega⟩ = p := by
      apply Fin.ext
      show 2 * r + k - (2 * r + k - p.val) = p.val
      omega
    have hx := congrFun (hcols ⟨2 * r + k - p.val, by omega⟩).2 i
    rw [e] at hx
    simpa [bvec, mulVec_single, Pi.single_apply] using hx

theorem uw_row (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (hh : h ∈ UWset k r z) (q : Fin (2 * r + k + 1)) (hq : q.val < r ∨ r + k < q.val)
    (j : Fin (2 * r + k + 1)) : h q j = if j = q then 1 else 0 := by
  have hqlt := q.isLt
  obtain ⟨p, hpd⟩ : ∃ p : Fin (2 * r + k + 1), p.val = 2 * r + k - q.val := ⟨⟨2 * r + k - q.val, by omega⟩, rfl⟩
  have hp : p.val < r ∨ r + k < p.val := by omega
  have hpq : p.val + q.val = 2 * r + k := by omega
  have hor : p.val < r ∨ q.val < r := by omega
  have hc : ∀ i, h i p = if i = p then 1 else 0 := uw_col k r z h hh p hp
  have hr : ∀ j', Hpk k r p j' = if j' = q then 1 else 0 := hpk_row k r p q hpq hor
  have hU : hᴴ * Hpk k r * h = Hpk k r := hh.1
  have hx := congrFun (congrFun hU p) j
  simp only [mul_apply, conjTranspose_apply, hc, hr] at hx
  simpa [Finset.sum_ite_eq, Finset.sum_ite_eq', ite_mul, hr] using hx

theorem torConj : CompanionTheory.Bmu.TorConj := by
  unfold CompanionTheory.Bmu.TorConj
  intro k r z c hz hc
  obtain ⟨T, hT0, hT1, hTc⟩ := exists_scale r c hc
  obtain ⟨d, hd⟩ : ∃ d : Fin (2 * r + k + 1) → ℂ, d = fun i =>
      if i.val < r then T i.val else if i.val ≤ r + k then 1 else (star (T (2 * r + k - i.val)))⁻¹ :=
    ⟨_, rfl⟩
  have hdlow : ∀ i : Fin (2 * r + k + 1), i.val < r → d i = T i.val := fun i hi => by
    rw [hd]; simp only; rw [if_pos hi]
  have hdmid : ∀ i : Fin (2 * r + k + 1), r ≤ i.val → i.val ≤ r + k → d i = 1 := fun i h1 h2 => by
    rw [hd]; simp only; rw [if_neg (by omega), if_pos h2]
  have hdhigh : ∀ i : Fin (2 * r + k + 1), r + k < i.val → d i = (star (T (2 * r + k - i.val)))⁻¹ :=
    fun i hi => by
      rw [hd]; simp only; rw [if_neg (by omega), if_neg (by omega)]
  have hd0 : ∀ i, d i ≠ 0 := by
    intro i
    by_cases h1 : i.val < r
    · rw [hdlow i h1]; exact hT0 _
    by_cases h2 : i.val ≤ r + k
    · rw [hdmid i (by omega) h2]; exact one_ne_zero
    · rw [hdhigh i (by omega)]; exact inv_ne_zero (star_ne_zero.mpr (hT0 _))
  have hHnz : ∀ i j : Fin (2 * r + k + 1), Hpk k r i j ≠ 0 →
      (i.val < r ∧ i.val + j.val = 2 * r + k) ∨ (j.val < r ∧ i.val + j.val = 2 * r + k) ∨
        (r ≤ i.val ∧ i.val ≤ r + k ∧ i = j) := by
    intro i j h
    unfold Hpk at h
    split_ifs at h with h1 h2 h3 <;> first | exact absurd rfl h | tauto
  have hkey : ∀ i j, Hpk k r i j ≠ 0 → star (d i) * d j = 1 := by
    intro i j h
    have hilt := i.isLt
    have hjlt := j.isLt
    rcases hHnz i j h with ⟨hi, hij⟩ | ⟨hj, hij⟩ | ⟨hi1, hi2, rfl⟩
    · rw [hdlow i hi, hdhigh j (by omega), show 2 * r + k - j.val = i.val by omega]
      exact mul_inv_cancel₀ (star_ne_zero.mpr (hT0 _))
    · rw [hdhigh i (by omega), hdlow j hj, show 2 * r + k - i.val = j.val by omega]
      simp [hT0 j.val]
    · rw [hdmid i hi1 hi2]; simp
  have hdiagU : ∀ e : Fin (2 * r + k + 1) → ℂ, (∀ i j, Hpk k r i j ≠ 0 → star (e i) * e j = 1) →
      diagonal e ∈ UH (Hpk k r) := by
    intro e he
    show (diagonal e)ᴴ * Hpk k r * diagonal e = Hpk k r
    ext i j
    rw [diagonal_conjTranspose, mul_diagonal, diagonal_mul, Pi.star_apply]
    by_cases h0 : Hpk k r i j = 0
    · rw [h0]; ring
    · calc star (e i) * Hpk k r i j * e j = (star (e i) * e j) * Hpk k r i j := by ring
        _ = Hpk k r i j := by rw [he i j h0, one_mul]
  have hUmul : ∀ A B, A ∈ UH (Hpk k r) → B ∈ UH (Hpk k r) → A * B ∈ UH (Hpk k r) := by
    intro A B hA hB
    have hA' : Aᴴ * Hpk k r * A = Hpk k r := hA
    have hB' : Bᴴ * Hpk k r * B = Hpk k r := hB
    show (A * B)ᴴ * Hpk k r * (A * B) = Hpk k r
    rw [conjTranspose_mul]
    calc Bᴴ * Aᴴ * Hpk k r * (A * B) = Bᴴ * (Aᴴ * Hpk k r * A) * B := by
          simp only [Matrix.mul_assoc]
      _ = Hpk k r := by rw [hA', hB']
  have hτU : diagonal d ∈ UH (Hpk k r) := hdiagU d hkey
  have hτinvU : diagonal (fun i => (d i)⁻¹) ∈ UH (Hpk k r) := by
    refine hdiagU _ fun i j h => ?_
    rw [star_inv₀, ← mul_inv, hkey i j h, inv_one]
  have hτinv : (diagonal d)⁻¹ = diagonal (fun i => (d i)⁻¹) := by
    apply Matrix.inv_eq_left_inv
    rw [diagonal_mul_diagonal]
    have he : (fun i => (d i)⁻¹ * d i) = fun _ => (1 : ℂ) := funext fun i => inv_mul_cancel₀ (hd0 i)
    rw [he, diagonal_one]
  have hcomm : ∀ h ∈ UWset k r z, diagonal d * h = h * diagonal d := by
    intro h hh
    ext i j
    rw [diagonal_mul, mul_diagonal]
    by_cases hij : i = j
    · subst hij; ring
    by_cases hi : i.val < r ∨ r + k < i.val
    · rw [uw_row k r z h hh i hi j, if_neg (fun e => hij e.symm)]; ring
    by_cases hj : j.val < r ∨ r + k < j.val
    · rw [uw_col k r z h hh j hj i, if_neg hij]; ring
    push_neg at hi hj
    rw [hdmid i hi.1 hi.2, hdmid j hj.1 hj.2]; ring
  have hzd : ∀ j, (d j)⁻¹ * z j = z j := by
    intro j
    by_cases hj : j.val < r ∨ r + k < j.val
    · rw [hz j hj, mul_zero]
    · push_neg at hj; rw [hdmid j hj.1 hj.2, inv_one, one_mul]
  refine ⟨diagonal d, hτU, hcomm, fun m hm => ?_⟩
  rw [hτinv]
  obtain ⟨hmU, hm2, hm3⟩ := hm
  have hent : ∀ i j, (diagonal d * m * diagonal (fun i => (d i)⁻¹)) i j = d i * m i j * (d j)⁻¹ := by
    intro i j
    rw [mul_diagonal, diagonal_mul]
  refine ⟨⟨hUmul _ _ (hUmul _ _ hτU hmU) hτinvU, ?_, ?_⟩, ?_⟩
  · intro a i hai
    rw [hent, hm2 a i hai]
    split_ifs with h
    · subst h; rw [mul_one, mul_inv_cancel₀ (hd0 _)]
    · simp
  · intro i j hj1 hj2 hi
    rw [hent, hm3 i j hj1 hj2 hi]
    split_ifs with h
    · subst h; rw [mul_one, mul_inv_cancel₀ (hd0 _)]
    · simp
  · have hsum : ∑ a, c a * PI.BesselMapUniq.ellA k r z (diagonal d * m * diagonal (fun i => (d i)⁻¹)) a =
        cStd * ell k r z m := by
      rw [ell, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [PI.BesselMapUniq.ellA]
      have e1 : d (eI k r a) = T a.val := hdlow _ a.isLt
      split_ifs with ha
      · have e2 : d (eI k r ⟨a.val + 1, ha⟩) = T (a.val + 1) := hdlow _ ha
        rw [hent, e1, e2, ← mul_assoc, ← mul_assoc, hTc a,
          mul_right_comm (cStd * T (a.val + 1)), mul_inv_cancel_right₀ (hT0 _)]
      · have hmv : (diagonal d * m * diagonal (fun i => (d i)⁻¹)).mulVec z (eI k r a) =
            d (eI k r a) * m.mulVec z (eI k r a) := by
          simp only [mulVec, dotProduct, hent, Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          calc d (eI k r a) * m (eI k r a) j * (d j)⁻¹ * z j
              = d (eI k r a) * m (eI k r a) j * ((d j)⁻¹ * z j) := by ring
            _ = d (eI k r a) * (m (eI k r a) j * z j) := by rw [hzd j]; ring
        rw [hmv, e1, ← mul_assoc, hTc a, hT1 _ (by omega), mul_one]
    rw [PI.BesselMapUniq.psiGen, psi, hsum]

end GlobalTheory.CompanionTheory.BmuTorConj
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.TruncatedDerivation
section
open Matrix MeasureTheory Filter Topology Set Formalism.QuantumDeterminants CompanionTheory.D.Upq.Sm CompanionTheory.Bmu
open scoped ContDiff InnerProductSpace ComplexConjugate

noncomputable section

namespace GlobalTheory.CompanionTheory.CutDeriv

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem continuous_of : Continuous fun y : PI.MtM n => (Matrix.of y : Mat n) := continuous_id

theorem continuous_scale (c : ℝ) : Continuous fun y : PI.MtM n => (c • Matrix.of y : Mat n) :=
  continuous_of.const_smul c

theorem notMem_tsupport {ρ : Mat n → ℝ} {R : ℝ} (hR : 0 < R) (X : Mat n) {T : Set ℝ} {t : ℝ} (ht : t ∈ T)
    {y : PI.MtM n}
    (hy : y ∉ (fun p : ℝ × Mat n => (Matrix.of.symm (R • (ex X p.1 * p.2)) : PI.MtM n)) '' (T ×ˢ tsupport ρ)) :
    ex X (-t) * (R⁻¹ • Matrix.of y) ∉ tsupport ρ := fun hs =>
  hy ⟨(t, ex X (-t) * (R⁻¹ • Matrix.of y)), ⟨ht, hs⟩, by
    simp only
    rw [← Matrix.mul_assoc, ← ex_add, add_neg_cancel, ex_zero, Matrix.one_mul, smul_smul,
      mul_inv_cancel₀ hR.ne', one_smul]
    rfl⟩

theorem isCompact_img {ρ : Mat n → ℝ} (hc : HasCompactSupport ρ) (R : ℝ) (X : Mat n) {T : Set ℝ}
    (hT : IsCompact T) : IsCompact
      ((fun p : ℝ × Mat n => (Matrix.of.symm (R • (ex X p.1 * p.2)) : PI.MtM n)) '' (T ×ˢ tsupport ρ)) := by
  have h1 : Continuous fun p : ℝ × Mat n => (R • (ex X p.1 * p.2) : Mat n) :=
    (((continuous_ex X).comp continuous_fst).matrix_mul continuous_snd).const_smul R
  exact (hT.prod hc.isCompact).image h1

theorem hasCompactSupport_coef {ρ : Mat n → ℝ} (hc : HasCompactSupport ρ) {R : ℝ} (hR : 0 < R)
    (φ : PI.MtM n → ℂ) : HasCompactSupport fun y : PI.MtM n => (ρ (R⁻¹ • Matrix.of y) : ℂ) * φ y := by
  refine HasCompactSupport.intro (isCompact_img hc R 0 (isCompact_singleton (x := (0 : ℝ)))) fun y hy => ?_
  have := notMem_tsupport hR 0 (mem_singleton _) hy
  rw [neg_zero, ex_zero, Matrix.one_mul] at this
  rw [image_eq_zero_of_notMem_tsupport this, Complex.ofReal_zero, zero_mul]

theorem continuous_coef {ρ : Mat n → ℝ} (hρ : Continuous ρ) (R : ℝ) {F : Mat n → H} (hF : Continuous F) (v : H) :
    Continuous fun y : PI.MtM n => (ρ (R⁻¹ • Matrix.of y) : ℂ) * ⟪F (Matrix.of y), v⟫_ℂ :=
  (Complex.continuous_ofReal.comp (hρ.comp (continuous_scale _))).mul
    ((hF.comp continuous_of).inner continuous_const)

variable {Hm : Mat n} {σ : Mat n → (H →L[ℂ] H)} {μ : Measure (PI.MtM n)} {w : H} {F : Mat n → H}

theorem cutI_eq (hμ : PI.IsHaarOnM (UH Hm) μ) (hFw : ∀ a ∈ UH Hm, F a = σ a w) (R : ℝ) (ρ : Mat n → ℝ) (v : H) :
    cutI σ μ w R ρ v =
      ∫ y : PI.MtM n, ((ρ (R⁻¹ • Matrix.of y) : ℂ) * ⟪F (Matrix.of y), v⟫_ℂ) • F (Matrix.of y) ∂μ := by
  have hae : ∀ᵐ g ∂μ, Matrix.of g ∈ UH Hm := hμ.2.2.1
  refine integral_congr_ae ?_
  filter_upwards [hae] with g hg
  rw [hFw _ hg, inner_conj_symm]

theorem inner_iso (h : URep Hm σ) {g : Mat n} (hg : g ∈ UH Hm) (x y : H) : ⟪σ g x, σ g y⟫_ℂ = ⟪x, y⟫_ℂ :=
  (LinearIsometry.mk (σ g).toLinearMap (h.iso g hg)).inner_map_map x y

variable [CompleteSpace H]

theorem apply_cutI (h : URep Hm σ) (hμ : PI.IsHaarOnM (UH Hm) μ) (hF : Continuous F)
    (hFw : ∀ a ∈ UH Hm, F a = σ a w) {R : ℝ} (hR : 0 < R) {ρ : Mat n → ℝ} (hρ : Continuous ρ)
    (hc : HasCompactSupport ρ) (v : H) {X : Mat n} (hX : ∀ t, ex X t ∈ UH Hm) (t : ℝ) :
    σ (ex X t) (cutI σ μ w R ρ v) =
      ∫ y : PI.MtM n, ((ρ (ex X (-t) * (R⁻¹ • Matrix.of y)) : ℂ) * ⟪F (Matrix.of y), σ (ex X t) v⟫_ℂ) •
        F (Matrix.of y) ∂μ := by
  haveI : IsFiniteMeasureOnCompacts μ :=
    ⟨fun _ hK => CompanionTheory.D.Upq.Quot.IsHaarOnM.lt_top_of_isCompact h.grp hμ hK⟩
  have hae : ∀ᵐ g ∂μ, Matrix.of g ∈ UH Hm := hμ.2.2.1
  have hi : Integrable (fun y : PI.MtM n =>
      ((ρ (R⁻¹ • Matrix.of y) : ℂ) * ⟪F (Matrix.of y), v⟫_ℂ) • F (Matrix.of y)) μ :=
    ((continuous_coef hρ R hF v).smul (hF.comp continuous_of)).integrable_of_hasCompactSupport
      (hasCompactSupport_coef hc hR _).smul_right
  have hl : Continuous (PI.lmulQ (ex X t)) := by
    have : Continuous fun y : PI.MtM n => (ex X t * Matrix.of y : Mat n) :=
      continuous_const.matrix_mul continuous_of
    exact this
  have hg : Continuous fun y : PI.MtM n =>
      ((ρ (ex X (-t) * (R⁻¹ • Matrix.of y)) : ℂ) * ⟪F (Matrix.of y), σ (ex X t) v⟫_ℂ) • F (Matrix.of y) :=
    ((Complex.continuous_ofReal.comp (hρ.comp (continuous_const.matrix_mul (continuous_scale _)))).mul
      ((hF.comp continuous_of).inner continuous_const)).smul (hF.comp continuous_of)
  rw [cutI_eq hμ hFw, ← (σ (ex X t)).integral_comp_comm hi]
  conv_rhs => rw [← hμ.2.2.2 _ (hX t)]
  rw [integral_map hl.measurable.aemeasurable hg.aestronglyMeasurable]
  refine integral_congr_ae ?_
  filter_upwards [hae] with g hg
  have e : (Matrix.of (PI.lmulQ (ex X t) g) : Mat n) = ex X t * Matrix.of g := rfl
  rw [e, hFw _ (h.rep.mul_mem _ (hX t) _ hg), h.rep.apply_mul (hX t) hg, inner_iso h (hX t), map_smul,
    hFw _ hg, Matrix.mul_smul, ← Matrix.mul_assoc, ← ex_add, neg_add_cancel, ex_zero, Matrix.one_mul]

theorem cutDer : CutDer := by
  intro n Hm H _ _ _ σ h μ hμ w hw R hR ρ hρ hc v hv
  haveI : IsFiniteMeasureOnCompacts μ :=
    ⟨fun _ hK => CompanionTheory.D.Upq.Quot.IsHaarOnM.lt_top_of_isCompact h.grp hμ hK⟩
  have hae : ∀ᵐ g ∂μ, Matrix.of g ∈ UH Hm := hμ.2.2.1
  obtain ⟨F, hF, hFw⟩ := SmOn.exists_contDiff hw h.grp.1
  have hFc : Continuous F := hF.continuous
  have hFo : Continuous fun y : PI.MtM n => F (Matrix.of y) := hFc.comp continuous_of
  refine ⟨?_, fun X hX' => ?_⟩
  · have h1 := isSm_integral h.grp h.rep hw hμ (continuous_coef hρ.continuous R hFc v)
      (hasCompactSupport_coef hc hR _)
    convert h1 using 1
    refine integral_congr_ae ?_
    filter_upwards [hae] with g hg
    rw [hFw _ hg, inner_conj_symm]
  have hX : ∀ t, ex X t ∈ UH Hm := fun t => ex_mem_of_lie hX' t
  have hdv : IsSm (UH Hm) σ (ds σ X v) :=
    hv.dsW h.rep (W := [X]) fun Y hY => by rw [List.mem_singleton.1 hY]; exact hX
  have hu : Continuous fun t => σ (ex X t) v :=
    continuous_iff_continuousAt.2 fun t => (hv.hasDerivAt h.rep hX t).continuousAt
  have hu' : Continuous fun t => σ (ex X t) (ds σ X v) :=
    continuous_iff_continuousAt.2 fun t => (hdv.hasDerivAt h.rep hX t).continuousAt
  have hγ : Continuous fun p : ℝ × PI.MtM n => ex X (-p.1) * (R⁻¹ • Matrix.of p.2 : Mat n) :=
    ((continuous_ex X).comp continuous_fst.neg).matrix_mul ((continuous_scale _).comp continuous_snd)
  have hρL := (contDiff_Lx X hρ).continuous
  have hcL : HasCompactSupport (Lx X ρ) := hasCompactSupport_LW hc [X]
  have hc1 : ∀ {ψ : Mat n → ℝ} {u : ℝ → H}, Continuous ψ → Continuous u →
      Continuous fun p : ℝ × PI.MtM n =>
        (ψ (ex X (-p.1) * (R⁻¹ • Matrix.of p.2 : Mat n)) : ℂ) * ⟪F (Matrix.of p.2), u p.1⟫_ℂ :=
    fun hψ hu => (Complex.continuous_ofReal.comp (hψ.comp hγ)).mul
      ((hFo.comp continuous_snd).inner (hu.comp continuous_fst))
  have hd := hasDerivAt_integral_cpt (μ := μ)
    (F := fun t y => ((ρ (ex X (-t) * (R⁻¹ • Matrix.of y)) : ℂ) * ⟪F (Matrix.of y), σ (ex X t) v⟫_ℂ) •
      F (Matrix.of y))
    (F' := fun t y => ((Lx X ρ (ex X (-t) * (R⁻¹ • Matrix.of y)) : ℂ) * ⟪F (Matrix.of y), σ (ex X t) v⟫_ℂ +
      (ρ (ex X (-t) * (R⁻¹ • Matrix.of y)) : ℂ) * ⟪F (Matrix.of y), σ (ex X t) (ds σ X v)⟫_ℂ) •
      F (Matrix.of y))
    (fun t => ((hc1 hρ.continuous hu).comp (Continuous.prodMk_right t)).smul hFo)
    (((hc1 hρL hu).add (hc1 hρ.continuous hu')).smul (hFo.comp continuous_snd))
    (fun t a => by
      have d1 := (hasDerivAt_Lx X (R⁻¹ • Matrix.of a) hρ t).ofReal_comp
      have d2 : HasDerivAt (fun s => ⟪F (Matrix.of a), σ (ex X s) v⟫_ℂ)
          ⟪F (Matrix.of a), σ (ex X t) (ds σ X v)⟫_ℂ t :=
        ((innerSL ℂ (F (Matrix.of a))).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t
          (hv.hasDerivAt h.rep hX t)
      exact (d1.mul d2).smul_const _)
    (isCompact_img hc R X (isCompact_Icc (a := (-1 : ℝ)) (b := 1)))
    (fun a ha => by
      rw [image_eq_zero_of_notMem_tsupport (notMem_tsupport hR X (t := 0) (by norm_num) ha),
        Complex.ofReal_zero, zero_mul, zero_smul])
    (fun t ht a ha => by
      have h0 := notMem_tsupport hR X ht ha
      rw [image_eq_zero_of_notMem_tsupport h0,
        image_eq_zero_of_notMem_tsupport (fun hs => h0 (tsupport_Lx X ρ hs)),
        Complex.ofReal_zero, zero_mul, zero_mul, add_zero, zero_smul])
  have hi : ∀ {ψ : Mat n → ℝ} (u : H), Continuous ψ → HasCompactSupport ψ → Integrable (fun y : PI.MtM n =>
      ((ψ (R⁻¹ • Matrix.of y) : ℂ) * ⟪F (Matrix.of y), u⟫_ℂ) • F (Matrix.of y)) μ := fun u hψ hcψ =>
    ((continuous_coef hψ R hFc u).smul hFo).integrable_of_hasCompactSupport
      (hasCompactSupport_coef hcψ hR _).smul_right
  rw [cutI_eq hμ hFw R (Lx X ρ), cutI_eq hμ hFw R ρ (ds σ X v),
    ← integral_add (hi _ hρL hcL) (hi _ hρ.continuous hc)]
  conv_lhs => unfold ds
  simp_rw [apply_cutI h hμ hFc hFw hR hρ.continuous hc v hX]
  rw [hd.deriv]
  simp only [neg_zero, ex_zero, Matrix.one_mul, h.rep.map_one, ContinuousLinearMap.one_apply, add_smul]

end GlobalTheory.CompanionTheory.CutDeriv

end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.UnitaryIso
section
open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker

noncomputable section

namespace GlobalTheory.CompanionTheory.ZuckUIso

open CompanionTheory.D.Upq.Sm
open PI.UpqRep (InLieHpk dsigW)

section Gen

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ} {H H' : Type} [NormedAddCommGroup H] [NormedSpace ℂ H] [NormedAddCommGroup H'] [NormedSpace ℂ H']
  {G : Set (Mat n)} {σ : Mat n → (H →L[ℂ] H)} {σ' : Mat n → (H' →L[ℂ] H')}

theorem isSm_map (e : H →L[ℂ] H') (he : ∀ g ∈ G, ∀ x, e (σ g x) = σ' g (e x)) {v : H} (hv : IsSm G σ v) :
    IsSm G σ' (e v) :=
  (SmOn.clm hv (e.restrictScalars ℝ)).congr fun g hg => (he g hg v).symm

theorem ds_map (h : RepOn G σ) (e : H →L[ℂ] H') (he : ∀ g ∈ G, ∀ x, e (σ g x) = σ' g (e x)) {X : Mat n}
    (hX : ∀ t, ex X t ∈ G) {v : H} (hv : IsSm G σ v) : ds σ' X (e v) = e (ds σ X v) := by
  have h1 := (e.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hv.differentiableAt h hX).hasDerivAt
  have h2 : (fun t => σ' (ex X t) (e v)) = (e.restrictScalars ℝ) ∘ fun t => σ (ex X t) v := by
    ext t; exact (he _ (hX t) v).symm
  unfold ds
  rw [h2, h1.deriv]; rfl

theorem dsW_map (h : RepOn G σ) (e : H →L[ℂ] H') (he : ∀ g ∈ G, ∀ x, e (σ g x) = σ' g (e x))
    {v : H} (hv : IsSm G σ v) : ∀ {W : List (Mat n)}, LieW G W → dsW σ' W (e v) = e (dsW σ W v)
  | [], _ => rfl
  | X :: W, hW => by
    have hW' : LieW G W := fun Y hY => hW Y (List.mem_cons_of_mem _ hY)
    rw [dsW_cons, dsW_cons, dsW_map h e he hv hW',
      ds_map h e he (hW X List.mem_cons_self) (hv.dsW h hW')]

end Gen

variable {k r : ℕ}

def res (U U' : URep k r) (e : U.R.H →L[ℂ] U'.R.H) (he : ∀ g ∈ GG k r, ∀ x, e (U.R.σ g x) = U'.R.σ g (e x)) :
    U.R.smSub →ₗ[ℂ] U'.R.smSub :=
  (e : U.R.H →ₗ[ℂ] U'.R.H).restrict fun v hv => isSm_map (G := GG k r) e he (v := v) hv

theorem res_coe (U U' : URep k r) (e : U.R.H →L[ℂ] U'.R.H)
    (he : ∀ g ∈ GG k r, ∀ x, e (U.R.σ g x) = U'.R.σ g (e x)) (v : U.R.smSub) :
    (res U U' e he v : U'.R.H) = e v := rfl

theorem isHom_res (F : FRep k r) (U U' : URep k r) (e : U.R.H →L[ℂ] U'.R.H)
    (he : ∀ g ∈ GG k r, ∀ x, e (U.R.σ g x) = U'.R.σ g (e x)) (hn : ∀ x, ‖e x‖ = ‖x‖) :
    IsHom (F, U) (F, U') (dOp F.ι (res U U' e he)) where
  cont W hW := by
    refine ⟨1, [W], by simpa using hW, fun x => le_of_eq ?_⟩
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, one_mul, sn]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [dsigW_eq', dsigW_eq']
    change ‖dsW U'.R.σ W (e (x c : U.R.H))‖ = _
    rw [dsW_map U.repOn e he (v := (x c : U.R.H)) (x c).2 (fun X hX t => ex_mem_of_lie (hW X hX) t), hn]
  equiv g hg := by
    have h1 : res U U' e he ∘ₗ U.sig g = U'.sig g ∘ₗ res U U' e he := by
      ext v
      simp only [LinearMap.comp_apply, res_coe, URep.sig_coe _ hg, he g hg]
    refine LinearMap.ext fun x => funext fun c => ?_
    have h2 : ∀ d, res U U' e he (U.sig g (x d)) = U'.sig g (res U U' e he (x d)) :=
      fun d => LinearMap.congr_fun h1 (x d)
    simp [CompanionTheory.Zuck.act, mAct, dOp, h2]

theorem uIso : UIso := by
  rintro k r F U U' ⟨e, he⟩
  have he' : ∀ g ∈ GG k r, ∀ x, e.symm (U'.R.σ g x) = U.R.σ g (e.symm x) := fun g hg x => by
    apply e.injective
    rw [he g hg, e.apply_symm_apply, e.apply_symm_apply]
  refine ⟨dOp F.ι (res U U' (e.toContinuousLinearEquiv : U.R.H →L[ℂ] U'.R.H) he),
    dOp F.ι (res U' U (e.symm.toContinuousLinearEquiv : U'.R.H →L[ℂ] U.R.H) he'),
    isHom_res F U U' _ he e.norm_map, isHom_res F U' U _ he' e.symm.norm_map, ?_, ?_⟩
  · exact LinearMap.ext fun x => funext fun c => Subtype.ext (e.symm_apply_apply _)
  · exact LinearMap.ext fun x => funext fun c => Subtype.ext (e.apply_symm_apply _)

end GlobalTheory.CompanionTheory.ZuckUIso

end
end

