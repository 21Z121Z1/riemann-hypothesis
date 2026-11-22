import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.CuspFrame
import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.Bundle0002
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0152
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0007
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutPointRationalEquivariance
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0008
import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.Bundle0003
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0150
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0058
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0050
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0009
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0158
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0159

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FarTermsModerateRegionOfFlagBound
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.Deep

theorem farModerate_e_one_nonneg (B : RowsAut) : 0 ≤ (B.e 1).re := by
  obtain ⟨-, -, -, hpos, -⟩ := B.e_adm
  have h := hpos 1 (fun _ => 1) (fun _ => 1)
  simp at h
  simpa using (Complex.le_def.1 h).1

private theorem epN_pos_and_le_inv_sqrt_and_mul_le_log_two (n f q : ℕ) (hn : 8 ≤ n) (hf : 1 ≤ f) (hq : 1 ≤ q)
    (hqn : q ^ 2 ≤ n) :
    0 < 1 / 10 ^ 6 / ((n : ℝ) ^ 8 * (f : ℝ) ^ 2) ∧
      1 / 10 ^ 6 / ((n : ℝ) ^ 8 * (f : ℝ) ^ 2) ≤ 1 / Real.sqrt (2 * (q : ℝ)) ∧
      2 * (n : ℝ) ^ 2 * (1 / 10 ^ 6 / ((n : ℝ) ^ 8 * (f : ℝ) ^ 2)) ≤ Real.log 2 := by
  have hn' : (8 : ℝ) ≤ n := by exact_mod_cast hn
  have hf' : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hqn' : (q : ℝ) ≤ n := by
    have : q ≤ n := le_trans (Nat.le_self_pow (by norm_num) q) hqn
    exact_mod_cast this
  have hD : 0 < (n : ℝ) ^ 8 * (f : ℝ) ^ 2 := by positivity
  have hn8 : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 8 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have hf2 : (1 : ℝ) ≤ (f : ℝ) ^ 2 := one_le_pow₀ hf'
  have hnD : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 8 * (f : ℝ) ^ 2 := by nlinarith
  have hn2 : (n : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
  refine ⟨by positivity, ?_, ?_⟩
  · have hs : Real.sqrt (2 * (q : ℝ)) ≤ 2 * q :=
      calc Real.sqrt (2 * (q : ℝ)) ≤ Real.sqrt ((2 * (q : ℝ)) ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
        _ = 2 * q := Real.sqrt_sq (by linarith)
    have hspos : 0 < Real.sqrt (2 * (q : ℝ)) := Real.sqrt_pos.2 (by linarith)
    calc 1 / 10 ^ 6 / ((n : ℝ) ^ 8 * (f : ℝ) ^ 2) ≤ 1 / (2 * q) := by
          rw [div_le_div_iff₀ hD (by linarith)]
          nlinarith
      _ ≤ 1 / Real.sqrt (2 * (q : ℝ)) := one_div_le_one_div_of_le hspos hs
  · have hlog : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
    have h1 : (n : ℝ) ^ 2 / ((n : ℝ) ^ 8 * (f : ℝ) ^ 2) ≤ 1 := (div_le_one hD).2 hnD
    have h2 : 2 * (n : ℝ) ^ 2 * (1 / 10 ^ 6 / ((n : ℝ) ^ 8 * (f : ℝ) ^ 2)) =
        2 / 10 ^ 6 * ((n : ℝ) ^ 2 / ((n : ℝ) ^ 8 * (f : ℝ) ^ 2)) := by ring
    rw [h2]
    linarith

theorem farModerate_of_farBound :
    GlobalTheory.FlagMeas.FlagMeasureBound → GlobalTheory.Deep.FarBound → GlobalTheory.IndefiniteRowSideFullHecke.FarTermsModerate.FarModerate := by
  intro hFM hFB Cg hCg
  refine ⟨8, fun B d p q b hq hCH => ?_⟩
  obtain ⟨-, hrd, hf1, -, -, h2q, -, hmin, hdpos, -, htpos, htq, h, hh, hgap, -, -, -, h120, -⟩ :=
    GlobalTheory.Dec.countHyp_numerics B Cg 8 d p q b le_rfl hCH
  obtain ⟨hDS, hSig, hn0, hqn, -, hlf, hb2, -, -, hg1, hgb, -, -, -, -⟩ := hCH
  have htq' : tauStar B q b < 1 / 2 := (htq hq).1
  have he1 : 0 ≤ (B.e 1).re := farModerate_e_one_nonneg B
  have hK : 0 ≤ (∏ v, d v) * (B.e 1).re := mul_nonneg hdpos.le he1
  obtain ⟨hep0, hepq, heplog⟩ := epN_pos_and_le_inv_sqrt_and_mul_le_log_two B.I.n B.I.f q hn0 hf1 hq hqn
  obtain ⟨hA, hB, hC⟩ := GlobalTheory.gap_threshold_pays_far_terms Cg B.I.n B.I.f q B.I.rd (B.g : ℝ) b h
    (tauStar B q b) hCg (by omega) hf1 hq hqn hrd hlf hb2 (Nat.one_le_cast.2 hg1) hgb hh.ge le_rfl htq'.le
  obtain ⟨-, -, hfin, -⟩ := hFM B.I B.μf B.fund B.fund_spec p q hSig h2q 1 (fun _ => 1) le_rfl
    (fun _ => le_rfl) (by simpa using hq) ∅ MeasurableSet.empty (Set.empty_subset _)
  have hpt : ∀ x ∈ GlobalTheory.IndefiniteRowSideFullHecke.FarTermsModerate.moderate B q b, GlobalTheory.IndefiniteRowSideFullHecke.FarTermsModerate.farSum B d x ≤
      ENNReal.ofReal ((∏ v, d v) * (B.e 1).re * Real.exp (-((B.I.n : ℝ) ^ 2 * (B.I.f : ℝ)))) := by
    intro x hx
    obtain ⟨hs, hsum⟩ := hFB B d p q h (epN B) hDS hSig hmin.symm hq hgap hep0 hepq heplog hA hB h120 x
    have hx1 : GlobalTheory.IndefiniteRowSideFullHecke.FarTermsModerate.farSum B d x = ENNReal.ofReal
        (∑' γ : GlobalTheory.IndefiniteRowSideFullHecke.FarTermsLatticeBound.farSet B d (epN B) x, ‖phe B d (x⁻¹ * γ.1 * x)‖) := by
      rw [ENNReal.ofReal_tsum_of_nonneg (fun _ => norm_nonneg _) hs]
      simp only [ofReal_norm]
      rfl
    have hlat : GlobalTheory.IndefiniteRowSideFullHecke.FarTermsLatticeBound.latFactor B.I x ≤
        (3 * Real.sqrt (B.I.n : ℝ) / tauStar B q b ^ 2) ^ (2 * (B.I.n ^ 2 * B.I.f)) := by
      have ht1 : tauStar B q b ≤ tau1 B.I x := le_min htq'.le hx.2
      unfold GlobalTheory.IndefiniteRowSideFullHecke.FarTermsLatticeBound.latFactor
      apply pow_le_pow_left₀ (by positivity)
      exact div_le_div_of_nonneg_left (by positivity) (pow_pos htpos 2)
        (pow_le_pow_left₀ htpos.le ht1 2)
    have hC0 : 0 ≤ 2 * (B.I.f : ℝ) * 3 ^ B.I.f * Real.exp (-(h * epN B ^ 2 / 16)) := by positivity
    rw [hx1]
    apply ENNReal.ofReal_le_ofReal
    calc ∑' γ : GlobalTheory.IndefiniteRowSideFullHecke.FarTermsLatticeBound.farSet B d (epN B) x, ‖phe B d (x⁻¹ * γ.1 * x)‖
        ≤ (∏ v, d v) * (B.e 1).re * GlobalTheory.IndefiniteRowSideFullHecke.FarTermsLatticeBound.latFactor B.I x *
            (2 * (B.I.f : ℝ) * 3 ^ B.I.f * Real.exp (-(h * epN B ^ 2 / 16))) := hsum
      _ ≤ (∏ v, d v) * (B.e 1).re *
            (3 * Real.sqrt (B.I.n : ℝ) / tauStar B q b ^ 2) ^ (2 * (B.I.n ^ 2 * B.I.f)) *
            (2 * (B.I.f : ℝ) * 3 ^ B.I.f * Real.exp (-(h * epN B ^ 2 / 16))) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlat hK) hC0
      _ = (∏ v, d v) * (B.e 1).re *
            ((3 * Real.sqrt (B.I.n : ℝ) / tauStar B q b ^ 2) ^ (2 * (B.I.n ^ 2 * B.I.f)) *
            (2 * (B.I.f : ℝ) * 3 ^ B.I.f * Real.exp (-(h * epN B ^ 2 / 16)))) := by ring
      _ ≤ (∏ v, d v) * (B.e 1).re * Real.exp (-((B.I.n : ℝ) ^ 2 * (B.I.f : ℝ))) :=
          mul_le_mul_of_nonneg_left hC hK
  calc ∫⁻ x in GlobalTheory.IndefiniteRowSideFullHecke.FarTermsModerate.moderate B q b, GlobalTheory.IndefiniteRowSideFullHecke.FarTermsModerate.farSum B d x ∂(B.I.muA B.μf)
      ≤ ∫⁻ _ in GlobalTheory.IndefiniteRowSideFullHecke.FarTermsModerate.moderate B q b,
          ENNReal.ofReal ((∏ v, d v) * (B.e 1).re * Real.exp (-((B.I.n : ℝ) ^ 2 * (B.I.f : ℝ))))
          ∂(B.I.muA B.μf) := setLIntegral_mono measurable_const hpt
    _ = ENNReal.ofReal ((∏ v, d v) * (B.e 1).re * Real.exp (-((B.I.n : ℝ) ^ 2 * (B.I.f : ℝ)))) *
          B.I.muA B.μf (GlobalTheory.IndefiniteRowSideFullHecke.FarTermsModerate.moderate B q b) := setLIntegral_const _ _
    _ ≤ ENNReal.ofReal ((∏ v, d v) * (B.e 1).re * Real.exp (-((B.I.n : ℝ) ^ 2 * (B.I.f : ℝ)))) *
          B.I.muA B.μf B.fund := mul_le_mul_of_nonneg_left (measure_mono fun x hx => hx.1) (by simp)
    _ = ENNReal.ofReal (Real.exp (-((B.I.n : ℝ) ^ 2 * (B.I.f : ℝ))) * mainTerm B d) := by
      rw [← ENNReal.ofReal_toReal hfin.ne,
        ← ENNReal.ofReal_mul (mul_nonneg hK (Real.exp_pos _).le)]
      congr 1
      show _ = Real.exp (-((B.I.n : ℝ) ^ 2 * (B.I.f : ℝ))) *
        ((∏ v, d v) * ((B.I.muA B.μf) B.fund).toReal * (B.e 1).re)
      ring

end GlobalTheory.Deep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagGradedPieceSizesStabiliserMul
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase

noncomputable section

namespace GlobalTheory.FlagSizeInv

open GlobalTheory.PointEquivariance

theorem mem_span_of_image {E : Type} [Field E] {n : ℕ} (φ : E →+* ℂ) (s : Set (Fin n → E)) (z : Fin n → E)
    (h : (fun l => φ (z l)) ∈ Submodule.span ℂ ((fun y : Fin n → E => fun l => φ (y l)) '' s)) :
    z ∈ Submodule.span E s := by
  by_contra hz
  obtain ⟨f, hfz, hf⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hz inferInstance
  have hf0 : ∀ y ∈ s, f y = 0 := fun y hy => by
    have hm : f y ∈ (Submodule.span E s).map f := Submodule.mem_map_of_mem (Submodule.subset_span hy)
    rw [hf] at hm
    simpa using hm
  have hfx : ∀ y : Fin n → E, f y = ∑ l, y l * f (fun j => if l = j then 1 else 0) := fun y => by
    rw [LinearMap.pi_apply_eq_sum_univ f y]
    simp only [smul_eq_mul]
  let F : (Fin n → ℂ) →ₗ[ℂ] ℂ := ∑ l, φ (f (fun j => if l = j then 1 else 0)) • LinearMap.proj l
  have hF : ∀ y : Fin n → E, F (fun l => φ (y l)) = φ (f y) := fun y => by
    rw [hfx y, map_sum]
    simp only [F, LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply, LinearMap.coe_proj,
      Function.eval, smul_eq_mul, map_mul]
    exact Finset.sum_congr rfl fun l _ => mul_comm _ _
  have hle : Submodule.span ℂ ((fun y : Fin n → E => fun l => φ (y l)) '' s) ≤ LinearMap.ker F := by
    rw [Submodule.span_le]
    rintro _ ⟨y, hy, rfl⟩
    show F _ = 0
    rw [hF, hf0 y hy, map_zero]
  have h0 : φ (f z) = 0 := by
    rw [← hF]
    exact LinearMap.mem_ker.1 (hle h)
  exact hfz ((map_eq_zero_iff φ φ.injective).1 h0)

theorem mulVec_mem_span (I : AutInst) {a : ℕ} (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E))
    (v : InfinitePlace I.F) (k : Fin (a + 1)) (γ : Matrix (Fin I.n) (Fin I.n) I.E)
    (h : ∀ y ∈ flagAt I S v k, ((I.P v)⁻¹ * γ.map (I.φ v) * I.P v) *ᵥ y ∈ flagAt I S v k)
    (y : Fin I.n → I.E) (hy : y ∈ S k) : γ *ᵥ y ∈ Submodule.span I.E (S k : Set (Fin I.n → I.E)) := by
  have hP : IsUnit (I.P v).det := (Matrix.isUnit_iff_isUnit_det _).1 (I.P_unit v)
  have hmem : (I.P v)⁻¹ *ᵥ (fun l => I.φ v (y l)) ∈ flagAt I S v k := by
    unfold flagAt
    exact Submodule.subset_span ⟨y, hy, rfl⟩
  have h1 := h _ hmem
  have hcomp : ((I.P v)⁻¹ * γ.map (I.φ v) * I.P v) *ᵥ ((I.P v)⁻¹ *ᵥ (fun l => I.φ v (y l))) =
      (I.P v)⁻¹ *ᵥ (fun l => I.φ v ((γ *ᵥ y) l)) := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hP, Matrix.mul_one,
      ← Matrix.mulVec_mulVec]
    congr 1
    funext l
    exact (RingHom.map_mulVec (I.φ v) γ y l).symm
  rw [hcomp] at h1
  unfold flagAt at h1
  have h2 := Submodule.mem_map_of_mem (f := Matrix.toLin' (I.P v)) h1
  rw [Submodule.map_span, Set.image_image] at h2
  simp only [Matrix.toLin'_apply, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hP,
    Matrix.one_mulVec] at h2
  exact mem_span_of_image (I.φ v) _ _ h2

theorem ratIso_eq (I : AutInst) (γ : GL (Fin I.n) I.E) (Λ N : Submodule (𝓞 I.E) (Fin I.n → I.E))
    (hΛ : ratIso I γ Λ = Λ) (hN : ∀ y, y ∈ N ↔ y ∈ Λ ∧ y ∈ Submodule.span I.E (N : Set (Fin I.n → I.E)))
    (h : ∀ y ∈ N, (γ : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ y ∈ Submodule.span I.E (N : Set (Fin I.n → I.E))) :
    ratIso I γ N = N := by
  rw [ratIso_apply] at hΛ ⊢
  have hinj : Function.Injective (Matrix.toLin' (γ : Matrix (Fin I.n) (Fin I.n) I.E)) := by
    intro y y' hyy
    have hc := congrArg (Matrix.toLin' ((γ⁻¹ : GL (Fin I.n) I.E) : Matrix (Fin I.n) (Fin I.n) I.E)) hyy
    simpa [Matrix.toLin'_apply, Matrix.mulVec_mulVec] using hc
  have hWle : (Submodule.span I.E (N : Set (Fin I.n → I.E))).map
      (Matrix.toLin' (γ : Matrix (Fin I.n) (Fin I.n) I.E)) ≤ Submodule.span I.E (N : Set (Fin I.n → I.E)) := by
    rw [Submodule.map_le_iff_le_comap, Submodule.span_le]
    intro y hy
    exact h y hy
  have hW : (Submodule.span I.E (N : Set (Fin I.n → I.E))).map
      (Matrix.toLin' (γ : Matrix (Fin I.n) (Fin I.n) I.E)) = Submodule.span I.E (N : Set (Fin I.n → I.E)) := by
    refine Submodule.eq_of_le_of_finrank_eq hWle ?_
    have e := LinearEquiv.finrank_map_eq (ratEquiv I γ) (Submodule.span I.E (N : Set (Fin I.n → I.E)))
    exact e
  apply le_antisymm
  · rintro _ ⟨y, hy, rfl⟩
    simp only [LinearMap.restrictScalars_apply, Matrix.toLin'_apply]
    have hy' := (hN y).1 hy
    refine (hN _).2 ⟨?_, h y hy⟩
    rw [← hΛ]
    exact ⟨y, hy'.1, by simp⟩
  · intro y hy
    obtain ⟨hyΛ, hyW⟩ := (hN y).1 hy
    rw [← hΛ] at hyΛ
    obtain ⟨y', hy'Λ, hy'⟩ := hyΛ
    rw [← hW] at hyW
    obtain ⟨y'', hy''W, hy''⟩ := hyW
    have hyy : y'' = y' := hinj (by rw [hy'', ← hy']; rfl)
    subst hyy
    exact ⟨y'', (hN y'').2 ⟨hy'Λ, hy''W⟩, hy'⟩

theorem sizesAt_mul : ∀ (I : AutInst) (xf : I.Gf) (a : ℕ) (j : Fin a → ℕ)
    (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)), IsSatFlag I (lamX I (1, xf)) j S →
    ∀ γ ∈ flagGroup I xf S, ∀ g : I.Ginf, sizesAt I xf S (γ * g) = sizesAt I xf S g := by
  intro I xf a j S hS γ hγ g
  obtain ⟨⟨δ, hδ, hδ1, hδK⟩, hkeep⟩ := hγ
  obtain ⟨c, -, hc1, hc2⟩ := hδ
  unfold IsSatFlag at hS
  obtain ⟨-, -, -, hsat, -⟩ := hS
  have hL : lamX I (δ * (1, xf)) = lamX I (1, xf) := by
    have hk := (lamX_mul_eq_iff I (1, xf) (1, xf⁻¹ * δ.2 * xf)).1 hδK
    have h2 : (δ * (1, xf)).2 = ((1, xf) * (1, xf⁻¹ * δ.2 * xf) : I.GA).2 := by
      simp [mul_assoc]
    rw [← hk, lamX_eq, lamX_eq, h2]
  have hlat : ratIso I c (lamX I (1, xf)) = lamX I (1, xf) := by
    rw [← lamX_rat I (1, xf) δ c hc2, hL]
  obtain ⟨v₀⟩ := (inferInstance : Nonempty (InfinitePlace I.F))
  have hfix : ∀ k, ratIso I c (S k) = S k := fun k =>
    ratIso_eq I c _ (S k) hlat (hsat k) fun y hy =>
      mulVec_mem_span I S v₀ k (c : Matrix (Fin I.n) (Fin I.n) I.E)
        (fun x hx => by rw [← hc1 v₀, hδ1]; exact hkeep v₀ k x hx) y hy
  have hcond : ∀ v, uMat (((γ, 1) : I.GA).1 v) =
      (I.P v)⁻¹ * (c : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v := fun v => by
    show uMat (γ v) = _
    rw [← hδ1]
    exact hc1 v
  have hax : ((γ, 1) : I.GA) * (g, xf) = (γ * g, xf) := by simp
  unfold sizesAt
  funext i
  have key := sizeQ_eq (bas I) (frm I (g, xf)) (frm I (γ * g, xf)) (ratIso I c)
    (fun N => by rw [← hax]; exact zl_ratIso I (g, xf) (γ, 1) c hcond N) (rkK_ratIso I c)
    (S i.succ) (S i.castSucc)
  rw [hfix, hfix] at key
  exact key

end GlobalTheory.FlagSizeInv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagRareOfNonzeroFlagBound
section
open MeasureTheory Formalism.MainNotions.S GlobalTheory.Count

namespace GlobalTheory.FlagRareProof

theorem flagRare_of_nonzeroFlagBound : GlobalTheory.FlagMeas.NonzeroFlagBound → GlobalTheory.IndefiniteRowSideFullHecke.RareFlags.FlagRare := by
  intro h
  refine ⟨⌈Real.exp 15⌉₊, ?_⟩
  intro B p q hsig hn hq hrd hf

  have hn' : Real.exp 15 ≤ (B.I.n : ℝ) := Nat.ceil_le.1 hn
  have hn1 : 1 ≤ B.I.n := by
    have : 0 < ⌈Real.exp 15⌉₊ := Nat.ceil_pos.2 (Real.exp_pos 15)
    omega
  have hlog : 15 ≤ Real.log B.I.n := by
    have := Real.log_le_log (Real.exp_pos 15) hn'
    rwa [Real.log_exp] at this
  have key := h B.I B.μf B.fund B.fund_spec p q hsig hlog hq hrd hf

  have hset : {x | least B.I x < 1 / 2} = {x | stepLt B.I x (1 / 2) ≠ ⊥} := by
    ext x
    have hx := ((GlobalTheory.CountSteps.steps B.I x (1 / 2) (by norm_num)).2.2.2.2.2.2.2.2 hn1).2.2
    simp only [Set.mem_ofPred_eq, ne_eq, hx, not_le]
  have hnf : 0 ≤ (B.I.n : ℝ) * (B.I.f : ℝ) * Real.log B.I.n :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (by linarith)
  rw [prob, hset, Formalism.MainNotions.S.AutInst.vol, ← ENNReal.toReal_div]
  calc _ ≤ Real.exp (-(1 / 3 * (B.I.n : ℝ) * B.I.f * Real.log B.I.n)) :=
        ENNReal.toReal_le_of_le_ofReal (Real.exp_pos _).le key
    _ ≤ _ := Real.exp_le_exp.2 (by nlinarith)

end GlobalTheory.FlagRareProof
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagWedgeFixedAndLengthEqProdDistances
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.FlagPartialWedge

open Formalism.HermitianLatticeCounting.ExpansionTerms (majorantDistance)

theorem len_castLE {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {l n : ℕ} (hl : l ≤ n)
    (y : Fin n → V) (a : Fin l) :
    majorantDistance (fun b : Fin l => y (Fin.castLE hl b)) a = majorantDistance y (Fin.castLE hl a) := by
  have ha := a.isLt
  have hS : (fun b : Fin l => y (Fin.castLE hl b)) '' {b | b < a} = y '' {b | b < Fin.castLE hl a} := by
    ext v
    constructor
    · rintro ⟨b, hb, rfl⟩
      refine ⟨Fin.castLE hl b, ?_, rfl⟩
      simp only [Set.mem_ofPred_eq, Fin.lt_def, Fin.val_castLE] at hb ⊢
      exact hb
    · rintro ⟨b, hb, rfl⟩
      simp only [Set.mem_ofPred_eq, Fin.lt_def, Fin.val_castLE] at hb
      refine ⟨⟨b.val, by omega⟩, ?_, ?_⟩
      · simp only [Set.mem_ofPred_eq, Fin.lt_def]
        exact hb
      · exact congrArg y (Fin.ext rfl)
  unfold majorantDistance
  rw [hS]

theorem fixes_partial_wedge_and_length : ∀ (k r l : ℕ) (hl : l ≤ r + 1) (z : Fin (2 * r + k + 1) → ℂ), Formalism.QuantumDeterminants.inWb k r z → (∀ s ∈ Formalism.QuantumDeterminants.Sset k r z, cmp l s *ᵥ (wedge (fun a : Fin l => Formalism.QuantumDeterminants.fvec k r z (Fin.castLE hl a))) = (wedge (fun a : Fin l => Formalism.QuantumDeterminants.fvec k r z (Fin.castLE hl a)))) ∧ ∀ g ∈ GG k r, ∑ J, ‖(cmp l g⁻¹ *ᵥ (wedge (fun a : Fin l => Formalism.QuantumDeterminants.fvec k r z (Fin.castLE hl a)))) J‖ ^ 2 = ∏ a : Fin l, lenA k r z g (Fin.castLE hl a) ^ 2 := by
  intro k r l hl z hz
  refine ⟨fun s hs => ?_, fun g _ => ?_⟩
  ·
    obtain ⟨U, hU0, hU1, hsF⟩ := Formalism.QuantumDeterminants.S_F hz hs
    rw [GlobalTheory.TensLen.cmp_mulVec_wedge]
    refine GlobalTheory.FlagFix.wedge_eq_of_mul _ _ (U.submatrix (Fin.castLE hl) (Fin.castLE hl)) ?_ ?_ ?_
    · intro c a hac
      simp only [Matrix.submatrix_apply]
      refine hU0 _ _ ?_
      simp only [Fin.lt_def, Fin.val_castLE] at hac ⊢
      exact hac
    · intro c
      simp only [Matrix.submatrix_apply]
      exact hU1 _
    · intro i a
      have ha := a.isLt
      show (s *ᵥ Formalism.QuantumDeterminants.fvec k r z (Fin.castLE hl a)) i =
        ∑ c : Fin l, Formalism.QuantumDeterminants.fvec k r z (Fin.castLE hl c) i * U (Fin.castLE hl c) (Fin.castLE hl a)
      have h1 := congrFun (congrFun hsF i) (Fin.castLE hl a)
      simp only [Matrix.mul_apply, Formalism.QuantumDeterminants.Fm, Matrix.of_apply] at h1
      have h2 : (s *ᵥ Formalism.QuantumDeterminants.fvec k r z (Fin.castLE hl a)) i =
          ∑ j, s i j * Formalism.QuantumDeterminants.fvec k r z (Fin.castLE hl a) j := rfl
      rw [h2, h1]
      refine Formalism.QuantumDeterminants.sum_fin_castLE hl _ ?_
      intro j hj
      show Formalism.QuantumDeterminants.fvec k r z j i * U j (Fin.castLE hl a) = 0
      rw [hU0 j (Fin.castLE hl a) ?_, mul_zero]
      rw [Fin.lt_def, Fin.val_castLE]
      omega
  ·
    rw [GlobalTheory.TensLen.cmp_mulVec_wedge, GlobalTheory.TensLen.sum_norm_wedge]
    refine Finset.prod_congr rfl (fun a _ => ?_)
    congr 1
    exact len_castLE hl (fun b : Fin (r + 1) =>
      (WithLp.toLp 2 (g⁻¹ *ᵥ Formalism.QuantumDeterminants.fvec k r z b) : EuclideanSpace ℂ (Fin (2 * r + k + 1)))) a

end GlobalTheory.FlagPartialWedge
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FundamentalSetMeasureCommensurableIndexRatio
section
open NumberField MeasureTheory Matrix Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.DegVol
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.CovolIdx

theorem tsum_cosets {G : Type} [Group G] (C H : Subgroup G) (hC : C ≤ H) (f : G → ℝ≥0∞) :
    ∑' h : H, f h = ∑' q : H ⧸ C.subgroupOf H, ∑' c : C, f ((q.out : H) * (c : G)) := by
  rw [← ENNReal.tsum_prod]
  let e : (H ⧸ C.subgroupOf H) × C → H := fun p => p.1.out * ⟨p.2, hC p.2.2⟩
  have hmk : ∀ p, (QuotientGroup.mk (e p) : H ⧸ C.subgroupOf H) = p.1 := by
    intro p
    have : (QuotientGroup.mk (e p) : H ⧸ C.subgroupOf H) = QuotientGroup.mk p.1.out := by
      symm
      rw [QuotientGroup.eq]
      simp [e, Subgroup.mem_subgroupOf]
    rw [this, QuotientGroup.out_eq']
  have he : Function.Bijective e := by
    constructor
    · rintro ⟨q, c⟩ ⟨q', c'⟩ h
      have h1 : q = q' := by
        have := hmk (q, c)
        rw [h, hmk] at this
        exact this.symm
      subst h1
      have h2 := mul_left_cancel h
      have h3 : c = c' := Subtype.ext (congrArg Subtype.val h2 :)
      rw [h3]
    · intro h
      have hm : ((QuotientGroup.mk h : H ⧸ C.subgroupOf H).out)⁻¹ * h ∈ C.subgroupOf H := by
        rw [← QuotientGroup.eq, QuotientGroup.out_eq']
      refine ⟨(QuotientGroup.mk h, ⟨_, Subgroup.mem_subgroupOf.1 hm⟩), ?_⟩
      apply Subtype.ext
      simp [e]
  exact ((Equiv.ofBijective e he).tsum_eq (fun h : H => f h)).symm

theorem measure_eq_tsum_inter {G α : Type} [Group G] [MulAction G α] [MeasurableSpace α]
    (μ : Measure α) (R : Set α) (A : Subgroup G) [Countable A] (Ω S : Set α)
    (hm : ∀ s : G, Measurable fun x : α => s • x) (hR : μ Rᶜ = 0)
    (hΩ : MeasurableSet Ω) (hS : MeasurableSet S) (h : ∀ x ∈ R, ∃! s, s ∈ A ∧ s • x ∈ Ω) :
    μ S = ∑' a : A, μ ((fun x => (a : G) • x) ⁻¹' Ω ∩ S) := by
  rw [← measure_iUnion₀]
  · apply measure_congr
    have : ∀ᵐ x ∂μ, x ∈ R := hR
    filter_upwards [this] with x hx
    obtain ⟨s, hs, -⟩ := h x hx
    apply propext
    constructor
    · intro hxS
      exact Set.mem_iUnion.2 ⟨⟨s, hs.1⟩, hs.2, hxS⟩
    · intro hxS
      obtain ⟨a, ha⟩ := Set.mem_iUnion.1 hxS
      exact ha.2
  · intro a b hab
    refine measure_mono_null ?_ hR
    rintro x ⟨ha, hb⟩ hx
    exact hab (Subtype.ext ((h x hx).unique ⟨a.2, ha.1⟩ ⟨b.2, hb.1⟩))
  · intro a
    exact ((hm a hΩ).inter hS).nullMeasurableSet

theorem measure_eq_invVol_mul : ∀ (G α : Type) [Group G] [MulAction G α] [MeasurableSpace α] (μ : Measure α) (R : Set α) (A B : Subgroup G) (Ω K : Set α), (∀ s : G, Measurable fun x : α => s • x) → Countable A → Countable B → μ Rᶜ = 0 → (∀ s ∈ A ⊔ B, (∀ x ∈ R, s • x ∈ R) ∧ μ.map (fun x => s • x) = μ) → A.relIndex B ≠ 0 → B.relIndex A ≠ 0 → MeasurableSet Ω → MeasurableSet K → (∀ x ∈ R, ∃! s, s ∈ A ∧ s • x ∈ Ω) → (∀ x ∈ R, ∃! s, s ∈ B ∧ s • x ∈ K) → μ K = ENNReal.ofReal (GlobalTheory.HL.invVol A B) * μ Ω := by
  intro G α _ _ _ μ R A B Ω K hm cA cB hR hinv hAB hBA hΩ hK fA fB
  have hpre : ∀ s ∈ A ⊔ B, ∀ S, MeasurableSet S → μ ((fun x => s • x) ⁻¹' S) = μ S := by
    intro s hs S hS
    rw [← Measure.map_apply (hm s) hS, (hinv s hs).2]
  let F : G → G → ℝ≥0∞ := fun a b => μ ((fun x => a • x) ⁻¹' Ω ∩ (fun x => b • x) ⁻¹' K)
  have hF : ∀ a b c : G, c ∈ A ⊓ B → F (a * c) b = F a (b * c⁻¹) := by
    intro a b c hc
    refine Eq.trans ?_ (hpre c (Subgroup.mem_sup_left hc.1) _ ((hm a hΩ).inter (hm (b * c⁻¹) hK)))
    simp only [F]
    congr 1
    ext x
    simp [mul_smul]
  have h1 : ∀ b ∈ B, μ K = ∑' a : A, F a b := by
    intro b hb
    rw [← hpre b (Subgroup.mem_sup_right hb) K hK]
    exact measure_eq_tsum_inter μ R A Ω _ hm hR hΩ (hm b hK) fA
  have h2 : ∀ a ∈ A, μ Ω = ∑' b : B, F a b := by
    intro a ha
    rw [← hpre a (Subgroup.mem_sup_left ha) Ω hΩ,
      measure_eq_tsum_inter μ R B K _ hm hR hK (hm a hΩ) fB]
    simp only [F, Set.inter_comm]
  have key : ∑' _q : B ⧸ (A ⊓ B).subgroupOf B, μ K = ∑' _p : A ⧸ (A ⊓ B).subgroupOf A, μ Ω := by
    have e1 : ∀ q : B ⧸ (A ⊓ B).subgroupOf B, μ K =
        ∑' p : A ⧸ (A ⊓ B).subgroupOf A, ∑' c : (A ⊓ B : Subgroup G),
          F (p.out : A) ((q.out : B) * (c : G)) := by
      intro q
      rw [h1 _ q.out.2, tsum_cosets (A ⊓ B) A inf_le_left (fun a => F a (q.out : B))]
      refine tsum_congr fun p => ?_
      rw [← (Equiv.inv (A ⊓ B : Subgroup G)).tsum_eq]
      refine tsum_congr fun c => ?_
      rw [hF _ _ _ (Subtype.property _)]
      simp
    have e2 : ∀ p : A ⧸ (A ⊓ B).subgroupOf A, μ Ω =
        ∑' q : B ⧸ (A ⊓ B).subgroupOf B, ∑' c : (A ⊓ B : Subgroup G),
          F (p.out : A) ((q.out : B) * (c : G)) := by
      intro p
      rw [h2 _ p.out.2, tsum_cosets (A ⊓ B) B inf_le_right (fun b => F (p.out : A) b)]
    rw [tsum_congr e1, tsum_congr e2, ENNReal.tsum_comm]
  rw [Subgroup.inf_subgroupOf_right, Subgroup.inf_subgroupOf_left, ENNReal.tsum_const, ENNReal.tsum_const] at key
  have fq : Finite (B ⧸ A.subgroupOf B) := Subgroup.fintypeOfIndexNeZero hAB |>.finite
  have fp : Finite (A ⧸ B.subgroupOf A) := Subgroup.fintypeOfIndexNeZero hBA |>.finite
  have key' : (A.relIndex B : ℝ≥0∞) * μ K = (B.relIndex A : ℝ≥0∞) * μ Ω := by
    simpa [ENat.card_eq_coe_natCard, Subgroup.relIndex, Subgroup.index] using key
  have hv : ENNReal.ofReal (GlobalTheory.HL.invVol A B) = (A.relIndex B : ℝ≥0∞)⁻¹ * (B.relIndex A : ℝ≥0∞) := by
    unfold GlobalTheory.HL.invVol
    rw [ENNReal.ofReal_div_of_pos (by exact_mod_cast Nat.pos_of_ne_zero hAB), ENNReal.ofReal_natCast,
      ENNReal.ofReal_natCast, div_eq_mul_inv, mul_comm]
  rw [hv, mul_assoc, ← key', ← mul_assoc,
    ENNReal.inv_mul_cancel (by exact_mod_cast hAB) (ENNReal.natCast_ne_top _), one_mul]

end GlobalTheory.CovolIdx
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairNormalFormExistsConjNearReferenceStatement
section
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermFramePairNormalForm_exists_conj_near_reference : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ (g : ℕ) (Λ : Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ → ∀ 𝔠 : Ideal (𝓞 K), 𝔠 ≠ ⊥ → (∀ x ∈ 𝔠, ∃ y ∈ 𝔠, (y : K) = star (x : K)) → (∀ x ∈ 𝔠, (N.T : 𝓞 K) ∣ x) → (∀ (l : ℕ) (hl : l ≤ r + 1), l ≤ N.j → Dl N.F N.F' l hl ≠ 0 → ∀ x ∈ 𝔠, ∀ y ∈ ipow N.𝔡 (2 * ∑ a ∈ Finset.range l, ((r : ℤ) - a)), (x : K) * y / Dl N.F N.F' l hl ∈ (1 : Submodule (𝓞 K) K) ∧ (x : K) * y / star (Dl N.F N.F' l hl) ∈ (1 : Submodule (𝓞 K) K)) → N.Split Λ → ∃ s ∈ N.Rs, N.Split (s • Λ) ∧ N.Near (𝔠 ^ (12 * r + 50)) (s • Λ) := by
  first | exact @GlobalTheory.DegCnt.NormalPos.exists_near | exact GlobalTheory.DegCnt.NormalPos.exists_near | (intros; apply GlobalTheory.DegCnt.NormalPos.exists_near <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianSpacesSameSignatureIsometricStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_spaces_same_signature_isometric : SameKindIsometric := by
  first | exact @GlobalTheory.FlagMeas.sameKindIsometric | exact GlobalTheory.FlagMeas.sameKindIsometric | (intros; apply GlobalTheory.FlagMeas.sameKindIsometric <;> assumption)
end

