import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.AParamSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.MultAtEqCount

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ADensStBA
section
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.GeometryOfNumbersTheory MvPolynomial MeasureTheory Module Filter Topology
open scoped ComplexOrder

variable {κ : Type} [Fintype κ] {D : ℕ}

def evalConstSnd (w : ((k : Unit) → GlobalTheory κ k) → ℂ) : Ix κ → ℂ := fun p => w fun _ => p.2

theorem adbLift_segre (z : Ix κ → ℂ) : evalConstSnd (segre (ι := GlobalTheory κ) z) = z := by
  funext p
  simp [evalConstSnd, segre]

theorem adb_segre_smul (c : ℂ) (z : Ix κ → ℂ) :
    segre (ι := GlobalTheory κ) (c • z) = c • segre (ι := GlobalTheory κ) z := by
  funext p
  simp [segre]

theorem adb_segre_injective : Function.Injective (segre (ι := GlobalTheory κ)) := fun z z' h => by
  rw [← adbLift_segre z, h, adbLift_segre]

theorem adb_mem_mcPts_iff {P : Ideal (MRing (GlobalTheory κ))} {z : Ix κ → ℂ} :
    z ∈ mcPts (ι := GlobalTheory κ) P ↔ z ∈ pts P := by
  simp only [mcPts, pts, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hk, h⟩
    obtain ⟨i, hi⟩ := hk ()
    refine ⟨fun h0 => hi (by simp [h0]), h⟩
  · rintro ⟨hz, h⟩
    refine ⟨fun k => ?_, h⟩
    by_contra hc
    push_neg at hc
    exact hz (funext fun p => hc p.2)

def IsSheetParamB (P : Ideal (MRing (GlobalTheory κ)))
    (Ψ : (((k : Unit) → GlobalTheory κ k) → ℂ) →ₗ[ℂ] (Fin (D + 1) → ℂ))
    (U : Set (Fin D → ℂ)) (γ : (Fin D → ℂ) → Ix κ → ℂ) : Prop :=
  IsParam P U γ ∧ ∀ y ∈ U, Ψ (segre (ι := GlobalTheory κ) (γ y)) = Fin.cons 1 y

variable {P : Ideal (MRing (GlobalTheory κ))} {Ψ : (((k : Unit) → GlobalTheory κ k) → ℂ) →ₗ[ℂ] (Fin (D + 1) → ℂ)}
  {U : Set (Fin D → ℂ)} {γ : (Fin D → ℂ) → Ix κ → ℂ}

theorem adb_mem_coneOver_self {y : Fin D → ℂ} (hy : y ∈ U) : γ y ∈ coneOver U γ :=
  ⟨y, hy, 1, one_ne_zero, by simp⟩

theorem IsSheetParamB.eq_of_mem (hs : IsSheetParamB P Ψ U γ) {z : Ix κ → ℂ}
    (hz : z ∈ coneOver U γ) {y : Fin D → ℂ} (hΨ : Ψ (segre (ι := GlobalTheory κ) z) = Fin.cons 1 y) :
    y ∈ U ∧ z = γ y := by
  obtain ⟨y0, hy0, c, hc, rfl⟩ := hz
  have h1 := hs.2 y0 hy0
  rw [adb_segre_smul, map_smul, h1] at hΨ
  have h0 := congrFun hΨ 0
  simp only [Pi.smul_apply, Fin.cons_zero, smul_eq_mul, mul_one] at h0
  subst h0
  rw [one_smul] at hΨ
  have hyy : y0 = y := by
    funext i
    have := congrFun hΨ i.succ
    simpa using this
  subst hyy
  exact ⟨hy0, by rw [one_smul]⟩

theorem IsSheetParamB.isSheet (hs : IsSheetParamB P Ψ U γ) {y : Fin D → ℂ} (hy : y ∈ U) :
    IsSheet P Ψ y (segre (ι := GlobalTheory κ) (γ y)) γ := by
  obtain ⟨⟨hU, hγ, hpts, -⟩, hΨ⟩ := hs
  refine ⟨rfl, ?_⟩
  filter_upwards [hU.mem_nhds hy] with y' hy'
  exact ⟨(hγ y' hy').differentiableAt, adb_mem_mcPts_iff.2 (hpts y' hy'), hΨ y' hy'⟩

theorem IsSheetParamB.eventuallyEq (hs : IsSheetParamB P Ψ U γ) {y : Fin D → ℂ} (hy : y ∈ U)
    {γ' : (Fin D → ℂ) → Ix κ → ℂ} (h' : IsSheet P Ψ y (segre (ι := GlobalTheory κ) (γ y)) γ') :
    γ' =ᶠ[𝓝 y] γ := by
  obtain ⟨hseg, hev⟩ := h'
  have hγy : γ' y = γ y := adb_segre_injective hseg
  obtain ⟨⟨hU, hγ, hpts, O, q, hO, hq, hOpts, hOc, hqγ⟩, hΨ⟩ := hs
  have hγO : γ y ∈ O := by
    have : γ y ∈ O ∩ pts P := by rw [hOpts]; exact adb_mem_coneOver_self hy
    exact this.1
  have hcont : ContinuousAt γ' y := hev.self_of_nhds.1.continuousAt
  have hO' : ∀ᶠ y' in 𝓝 y, γ' y' ∈ O := by
    apply hcont.preimage_mem_nhds
    rw [hγy]
    exact hO.mem_nhds hγO
  filter_upwards [hev, hO'] with y' ⟨_, hmc, hΨ'⟩ hy'O
  have hmem : γ' y' ∈ coneOver U γ := by
    rw [← hOpts]
    exact ⟨hy'O, adb_mem_mcPts_iff.1 hmc⟩
  exact (IsSheetParamB.eq_of_mem ⟨⟨hU, hγ, hpts, O, q, hO, hq, hOpts, hOc, hqγ⟩, hΨ⟩ hmem hΨ').2

theorem IsSheetParamB.sheetDensity_eq (hs : IsSheetParamB P Ψ U γ) {y : Fin D → ℂ} (hy : y ∈ U)
    (φ : Fin D → (Ix κ → ℂ) → ℝ) (h : (Ix κ → ℂ) → ℝ) :
    sheetDensity P Ψ φ h y (segre (ι := GlobalTheory κ) (γ y)) =
      h (γ y) * maDensity (fun j y' => φ j (γ y')) y := by
  have hex : ∃ γ'', IsSheet P Ψ y (segre (ι := GlobalTheory κ) (γ y)) γ'' := ⟨γ, hs.isSheet hy⟩
  simp only [sheetDensity, dif_pos hex]
  have heq := hs.eventuallyEq hy hex.choose_spec
  have hpt : hex.choose y = γ y := heq.self_of_nhds
  rw [hpt]
  congr 1
  unfold maDensity
  congr 4
  funext k
  unfold cxHessian
  have hf : (fun y' => φ k (hex.choose y')) =ᶠ[𝓝 y] fun y' => φ k (γ y') :=
    heq.fun_comp (φ k)
  rw [hf.fderiv.fderiv_eq]

theorem adb_measurable_cxHessian (f : (Fin D → ℂ) → ℝ) (i j : Fin D) :
    Measurable fun y => cxHessian f y i j := by
  have hH := measurable_fderiv ℝ (fderiv ℝ f)
  have hap : ∀ a b : Fin D → ℂ, Measurable fun y => fderiv ℝ (fderiv ℝ f) y a b := fun a b =>
    ((ContinuousLinearMap.apply ℝ ℝ b).continuous.comp
      (ContinuousLinearMap.apply ℝ _ a).continuous).measurable.comp hH
  simp only [cxHessian]
  exact (((Complex.measurable_ofReal.comp ((hap _ _).add (hap _ _))).add
    (measurable_const.mul (Complex.measurable_ofReal.comp ((hap _ _).sub (hap _ _))))).div_const 4)

theorem adb_continuous_mixedDisc :
    Continuous (mixedDisc : (Fin D → Matrix (Fin D) (Fin D) ℂ) → ℂ) := by
  unfold mixedDisc
  exact continuous_const.mul (continuous_finset_sum _ fun S _ => continuous_const.mul
    ((continuous_finset_sum _ fun k _ => continuous_apply k).matrix_det))

theorem adb_measurable_maDensity (φ : Fin D → (Fin D → ℂ) → ℝ) : Measurable (maDensity φ) := by
  have hcx : ∀ k i j, Measurable fun z => cxHessian (φ k) z i j := fun k i j =>
    adb_measurable_cxHessian (φ k) i j
  unfold maDensity mixedDisc
  simp only [Matrix.det_apply, Matrix.sum_apply]
  refine measurable_const.mul (Complex.measurable_re.comp (measurable_const.mul
    (Finset.measurable_sum _ fun S _ => measurable_const.mul
      (Finset.measurable_sum _ fun σ _ => (Finset.measurable_prod _ fun i _ =>
        Finset.measurable_sum _ fun k _ => hcx k _ _).const_smul _))))

def IsConeSetB (s : Set (Ix κ → ℂ)) : Prop :=
  ∀ (c : ℂ) (z : Ix κ → ℂ), c ≠ 0 → (c • z ∈ s ↔ z ∈ s)

theorem isConeSetB_coneOver (U : Set (Fin D → ℂ)) (γ : (Fin D → ℂ) → Ix κ → ℂ) :
    IsConeSetB (coneOver U γ) := by
  intro c z hc
  constructor
  · rintro ⟨y, hy, c', hc', hz⟩
    refine ⟨y, hy, c⁻¹ * c', mul_ne_zero (inv_ne_zero hc) hc', ?_⟩
    rw [mul_smul, ← hz, smul_smul, inv_mul_cancel₀ hc, one_smul]
  · rintro ⟨y, hy, c', hc', rfl⟩
    exact ⟨y, hy, c * c', mul_ne_zero hc hc', by rw [mul_smul]⟩

theorem IsConeSetB.inter {s t : Set (Ix κ → ℂ)} (hs : IsConeSetB s) (ht : IsConeSetB t) :
    IsConeSetB (s ∩ t) := fun c z hc => by
  simp only [Set.mem_inter_iff, hs c z hc, ht c z hc]

theorem IsConeSetB.compl {s : Set (Ix κ → ℂ)} (hs : IsConeSetB s) : IsConeSetB sᶜ := fun c z hc => by
  simp only [Set.mem_compl_iff, hs c z hc]

theorem IsConeSetB.iInter {ι : Sort*} {s : ι → Set (Ix κ → ℂ)} (hs : ∀ i, IsConeSetB (s i)) :
    IsConeSetB (⋂ i, s i) := fun c z hc => by
  simp only [Set.mem_iInter]
  exact forall_congr' fun i => hs i c z hc

theorem IsConeSetB.disjointed {s : ℕ → Set (Ix κ → ℂ)} (hs : ∀ i, IsConeSetB (s i)) (n : ℕ) :
    IsConeSetB (disjointed s n) := by
  rw [disjointed_eq_inter_compl]
  exact (hs n).inter (IsConeSetB.iInter fun i => IsConeSetB.iInter fun _ => (hs i).compl)

theorem IsConeSetB.indicator {s : Set (Ix κ → ℂ)} (hs : IsConeSetB s) {f : (Ix κ → ℂ) → ℝ}
    (hf : IsDegZero f) : IsDegZero (s.indicator f) := fun c z hc => by
  show s.indicator f (c • z) = s.indicator f z
  by_cases h : z ∈ s
  · rw [Set.indicator_of_mem ((hs c z hc).2 h), Set.indicator_of_mem h, hf c z hc]
  · rw [Set.indicator_of_notMem (fun h' => h ((hs c z hc).1 h')), Set.indicator_of_notMem h]

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.HasympAll
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem main_step {L : ℝ} {m p : ℕ} (hp : p.Prime) {W : Ideal (MRing ι)} (hW : IsMultiProjPrime W)
    (hpW : (p : MRing ι) ∈ W)
    (hdim : ringKrullDim (MRing ι ⧸ W) = ((m + 1 + Fintype.card K : ℕ) : WithBot ℕ∞))
    (hR4W : ∀ (a : Fin (m + 1) → K → ℤ) (k : K) (i : ι k), (X ⟨k, i⟩ : MRing ι) ∉ W →
      (a (Fin.last m) = fun k' => if k' = k then 1 else 0) →
      geoNum (m + 1) W a = ∑ᶠ W' ∈ divSupp W (X ⟨k, i⟩),
        (multAt (W ⊔ Ideal.span {(X ⟨k, i⟩ : MRing ι)}) W' : ℤ) * geoNum m W' (Fin.init a))
    (hSW : SymmAt (m + 1) W)
    (IH : ∀ W' : Ideal (MRing ι), IsMultiProjPrime W' → (p : MRing ι) ∈ W' →
      ringKrullDim (MRing ι ⧸ W') = ((m + Fintype.card K : ℕ) : WithBot ℕ∞) →
      HAsymp L m W' ∧ SymmAt m W') :
    HAsymp L (m + 1) W := by
  choose a0 C hC hb using fun b => block_step (L := L) hp hW hpW hdim hR4W IH b
  set a₁ := 1 + ∑ b, a0 b
  set Δ : (K → ℕ) → ℝ := fun a => lg W a - appr L (m + 1) W a with hΔ
  set B := coefB (m + 1) W
  have hB : 0 ≤ B := coefB_nonneg _ _
  have hf : (0 : ℝ) < m.factorial := by exact_mod_cast m.factorial_pos
  set Kst := ∑ b, C b + |L| * B * 2 ^ (m - 1) / m.factorial
  have hKst : 0 ≤ Kst := by
    have := Finset.sum_nonneg fun b (_ : b ∈ Finset.univ) => hC b
    positivity
  have hstep : ∀ a : K → ℕ, ∀ b, (∀ k, a₁ ≤ a k) → a₁ < a b →
      |Δ a - Δ (a - Pi.single b 1)| ≤ Kst * m * ((tdeg a : ℝ) + 1) ^ (m - 1) := by
    intro a b ha hab
    have ha0 : ∀ k, a0 b ≤ a k := fun k => by
      have h1 : a0 b ≤ ∑ b, a0 b := Finset.single_le_sum (f := a0) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ b)
      have := ha k
      omega
    have h1 := hb b a ha0
    set x : K → ℤ := fun k => (a k : ℤ)
    have hx : (fun _ : Fin (m + 1) => fun k => ((a - (Pi.single b 1 : K → ℕ)) k : ℤ)) =
        fun _ => x - uv b := by
      funext _ k
      by_cases hk : k = b
      · subst hk
        have : 1 ≤ a k := by omega
        simp [x, uv, Nat.cast_sub this]
      · simp [x, uv, Pi.single_apply, hk]
    have h2 := geoNum_diff_est m W hSW x b
    rw [show nrm x = tdeg a from nrm_natCast a] at h2
    have hfs : ((m + 1).factorial : ℝ) = (m + 1) * m.factorial := by
      rw [Nat.factorial_succ]; push_cast; ring
    have hid : Δ a - Δ (a - Pi.single b 1) =
        (lg W a - lg W (a - Pi.single b 1) -
          L * (geoNum (m + 1) W (Fin.snoc (fun _ k => (a k : ℤ)) (uv b)) : ℝ) / m.factorial) -
        L / ((m + 1).factorial : ℝ) * ((geoNum (m + 1) W (fun _ => x) : ℝ) -
          geoNum (m + 1) W (fun _ => x - uv b) -
          (m + 1) * geoNum (m + 1) W (Fin.snoc (fun _ => x) (uv b))) := by
      simp only [hΔ, appr]
      rw [hx, hfs]
      field_simp
      ring
    have h3 : |L / ((m + 1).factorial : ℝ) * ((geoNum (m + 1) W (fun _ => x) : ℝ) -
          geoNum (m + 1) W (fun _ => x - uv b) -
          (m + 1) * geoNum (m + 1) W (Fin.snoc (fun _ => x) (uv b)))| ≤
        |L| * B * 2 ^ (m - 1) / m.factorial * m * ((tdeg a : ℝ) + 1) ^ (m - 1) := by
      rw [abs_mul, abs_div, abs_of_pos (by positivity : (0 : ℝ) < ((m + 1).factorial : ℝ)), hfs]
      have hN : (0 : ℝ) ≤ tdeg a := by positivity
      have h4 : ((tdeg a : ℝ) + 2) ^ (m + 1 - 2) ≤ 2 ^ (m - 1) * ((tdeg a : ℝ) + 1) ^ (m - 1) := by
        rw [show m + 1 - 2 = m - 1 by omega, ← mul_pow]
        gcongr
        linarith
      calc |L| / ((m + 1) * m.factorial) * |(geoNum (m + 1) W (fun _ => x) : ℝ) -
            geoNum (m + 1) W (fun _ => x - uv b) -
            (m + 1) * geoNum (m + 1) W (Fin.snoc (fun _ => x) (uv b))|
          ≤ |L| / ((m + 1) * m.factorial) * (B * ((m + 1) * m * ((tdeg a : ℝ) + 2) ^ (m + 1 - 2))) := by
            gcongr
        _ ≤ |L| / ((m + 1) * m.factorial) * (B * ((m + 1) * m * (2 ^ (m - 1) *
              ((tdeg a : ℝ) + 1) ^ (m - 1)))) := by
            gcongr
        _ = |L| * B * 2 ^ (m - 1) / m.factorial * m * ((tdeg a : ℝ) + 1) ^ (m - 1) := by
            field_simp
    have hCb : C b ≤ ∑ b, C b := Finset.single_le_sum (f := C) (fun b _ => hC b) (Finset.mem_univ b)
    rw [hid]
    calc _ ≤ |lg W a - lg W (a - Pi.single b 1) -
            L * (geoNum (m + 1) W (Fin.snoc (fun _ k => (a k : ℤ)) (uv b)) : ℝ) / m.factorial| +
          |L / ((m + 1).factorial : ℝ) * ((geoNum (m + 1) W (fun _ => x) : ℝ) -
            geoNum (m + 1) W (fun _ => x - uv b) -
            (m + 1) * geoNum (m + 1) W (Fin.snoc (fun _ => x) (uv b)))| := abs_sub _ _
      _ ≤ C b * m * ((tdeg a : ℝ) + 1) ^ (m - 1) +
          |L| * B * 2 ^ (m - 1) / m.factorial * m * ((tdeg a : ℝ) + 1) ^ (m - 1) := add_le_add h1 h3
      _ ≤ (∑ b, C b) * m * ((tdeg a : ℝ) + 1) ^ (m - 1) +
          |L| * B * 2 ^ (m - 1) / m.factorial * m * ((tdeg a : ℝ) + 1) ^ (m - 1) := by gcongr
      _ = Kst * m * ((tdeg a : ℝ) + 1) ^ (m - 1) := by ring
  have hw := walk_bound Δ a₁ m hKst hstep
  refine ⟨a₁, |Δ (fun _ => a₁)| + Kst * m, by positivity, fun a ha => ?_⟩
  have h := hw a ha
  have hN : (0 : ℝ) ≤ tdeg a := by positivity
  have hp1 : (1 : ℝ) ≤ ((tdeg a : ℝ) + 1) ^ m := one_le_pow₀ (by linarith)
  have hkey : Kst * m * tdeg a * ((tdeg a : ℝ) + 1) ^ (m - 1) ≤ Kst * m * ((tdeg a : ℝ) + 1) ^ m := by
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm; simp
    · have : ((tdeg a : ℝ) + 1) ^ m = ((tdeg a : ℝ) + 1) ^ (m - 1) * ((tdeg a : ℝ) + 1) := by
        rw [← pow_succ]; congr 1; omega
      rw [this]
      have : (0 : ℝ) ≤ ((tdeg a : ℝ) + 1) ^ (m - 1) := by positivity
      have : (0 : ℝ) ≤ Kst * m := by positivity
      nlinarith
  simp only [Nat.add_sub_cancel]
  push_cast
  have hΔc := abs_nonneg (Δ (fun _ => a₁))
  have hKm : (0 : ℝ) ≤ Kst * m := by positivity
  change |Δ a| ≤ _
  have hm0 : (0 : ℝ) ≤ m := by positivity
  have hA : (1 : ℝ) ≤ ((m : ℝ) + 1) * ((tdeg a : ℝ) + 1) ^ m := by nlinarith
  have hB1 : |Δ (fun _ => a₁)| ≤ |Δ (fun _ => a₁)| * (((m : ℝ) + 1) * ((tdeg a : ℝ) + 1) ^ m) :=
    le_mul_of_one_le_right hΔc hA
  have hB2 : Kst * m * ((tdeg a : ℝ) + 1) ^ m ≤
      Kst * m * (((m : ℝ) + 1) * ((tdeg a : ℝ) + 1) ^ m) := by
    have : ((tdeg a : ℝ) + 1) ^ m ≤ ((m : ℝ) + 1) * ((tdeg a : ℝ) + 1) ^ m :=
      le_mul_of_one_le_left (by positivity) (by linarith)
    exact mul_le_mul_of_nonneg_left this hKm
  calc |Δ a| ≤ |Δ (fun _ => a₁)| + Kst * m * ((tdeg a : ℝ) + 1) ^ m := by linarith
    _ ≤ |Δ (fun _ => a₁)| * (((m : ℝ) + 1) * ((tdeg a : ℝ) + 1) ^ m) +
        Kst * m * (((m : ℝ) + 1) * ((tdeg a : ℝ) + 1) ^ m) := by linarith
    _ = (|Δ (fun _ => a₁)| + Kst * m) * ((m : ℝ) + 1) * ((tdeg a : ℝ) + 1) ^ m := by ring

theorem hasymp_all {L : ℝ} {p : ℕ} (hp : p.Prime)
    (hR4 : ∀ (n : ℕ) (V : Ideal (MRing ι)) (a : Fin (n + 1) → K → ℤ) (k : K) (i : ι k),
      IsMultiProjPrime V → charOf V ≠ 0 →
      ringKrullDim (MRing ι ⧸ V) = ((n + 1 + Fintype.card K : ℕ) : WithBot ℕ∞) →
      (X ⟨k, i⟩ : MRing ι) ∉ V →
      (a (Fin.last n) = fun k' => if k' = k then 1 else 0) →
      geoNum (n + 1) V a = ∑ᶠ W' ∈ divSupp V (X ⟨k, i⟩),
        (multAt (V ⊔ Ideal.span {(X ⟨k, i⟩ : MRing ι)}) W' : ℤ) * geoNum n W' (Fin.init a))
    (hSymm : ∀ (n : ℕ) (V : Ideal (MRing ι)) (a : Fin n → K → ℤ) (σ : Equiv.Perm (Fin n)),
      IsMultiProjPrime V → charOf V ≠ 0 →
      ringKrullDim (MRing ι ⧸ V) = ((n + Fintype.card K : ℕ) : WithBot ℕ∞) →
      geoNum n V (a ∘ σ) = geoNum n V a)
    (hbase : ∀ W : Ideal (MRing ι), IsMultiProjPrime W → (p : MRing ι) ∈ W →
      ringKrullDim (MRing ι ⧸ W) = ((0 + Fintype.card K : ℕ) : WithBot ℕ∞) → HAsymp L 0 W) :
    ∀ (d : ℕ) (W : Ideal (MRing ι)), IsMultiProjPrime W → (p : MRing ι) ∈ W →
      ringKrullDim (MRing ι ⧸ W) = ((d + Fintype.card K : ℕ) : WithBot ℕ∞) →
      HAsymp L d W ∧ SymmAt d W := by
  intro d
  induction d with
  | zero =>
    intro W hW hpW hdim
    exact ⟨hbase W hW hpW hdim,
      fun a σ => hSymm 0 W a σ hW (charOf_ne_zero_of_mem hp.ne_zero hpW) hdim⟩
  | succ m ih =>
    intro W hW hpW hdim
    have hc := charOf_ne_zero_of_mem hp.ne_zero hpW
    have hS : SymmAt (m + 1) W := fun a σ => hSymm (m + 1) W a σ hW hc hdim
    exact ⟨main_step hp hW hpW hdim (fun a k i hX ha => hR4 m W a k i hW hc hdim hX ha) hS
      (fun W' hW' hpW' hdim' => ih W' hW' hpW' hdim'), hS⟩

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
end
end

