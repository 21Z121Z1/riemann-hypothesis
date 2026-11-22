import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0015
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0455
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0580
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0545
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0552
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0647
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0592
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0629
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0479
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0561
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0523
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0404
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0618
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0598
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0448
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0373
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0590
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0648
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0536
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0392
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0595
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0646
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameBreuilKisinDatumExists
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0654
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0002
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0075
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0652
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeExpansionAtLowLevelPoints
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0003

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SaturatedAinfLatticeFreeOverBreuilKisin
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

set_option maxHeartbeats 1000000

namespace GlobalTheory.BKLim.SatLat

theorem main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d N : ℕ) (T0 V V' : Matrix (Fin d) (Fin d) (WCb l)) (Y1 : Matrix (Fin d) (Fin d) (Ainf l)), IsUnit T0 → (∀ i j, V i j ∈ bk.OE) → (∀ i j, V' i j ∈ bk.OE) → V * V' = 1 → Y1.map (inclW l) = inclW l τ ^ N • (T0 * V) → ∃ (Y : Matrix (Fin d) (Fin d) (Ainf l)) (Wm Wm' : Matrix (Fin d) (Fin d) (WCb l)), IsUnit (Y.map (inclW l)) ∧ (∀ i j, Wm i j ∈ bk.OE) ∧ (∀ i j, Wm' i j ∈ bk.OE) ∧ Wm * Wm' = 1 ∧ Y.map (inclW l) = inclW l τ ^ N • (T0 * Wm) ∧ ∀ y : Fin d → Ainf l, (∃ w : Fin d → WCb l, (∀ i, w i ∈ bk.OE) ∧ (fun i => inclW l (y i)) = inclW l τ ^ N • (T0 *ᵥ w)) → ∃ c : Fin d → bk.S, y = Y *ᵥ fun a => bk.ev (c a) := by
  intro l _ K bk τ hτ d N T0 V V' Y1 hT0 hV hV' hVV' hY1
  classical
  obtain ⟨htu, -, -, -⟩ := GlobalTheory.T.breuilKisin_period_isUnit_wittTilt_and_ne_zero l K bk τ hτ
  have hOEcl := GlobalTheory.T.breuilKisin_OE_stability_properties l K bk
  obtain ⟨M, hM⟩ : ∃ M : Matrix (Fin d) (Fin d) (WCb l), M = inclW l τ ^ N • T0 := ⟨_, rfl⟩
  have hMu : IsUnit M.det := by
    rw [hM, Matrix.det_smul]
    exact ((htu.pow N).pow _).mul ((Matrix.isUnit_iff_isUnit_det T0).1 hT0)
  have hMM : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv M hMu
  have hMM' : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul M hMu
  have hVu : IsUnit V.det := by
    have h : V.det * V'.det = 1 := by rw [← Matrix.det_mul, hVV', Matrix.det_one]
    exact ⟨⟨V.det, V'.det, h, by rw [mul_comm]; exact h⟩, rfl⟩
  let ι : (Fin d → Ainf l) → (Fin d → WCb l) := fun y a => inclW l (y a)
  have hιmul : ∀ (A : Matrix (Fin d) (Fin d) (Ainf l)) (v : Fin d → Ainf l),
      ι (A *ᵥ v) = A.map (inclW l) *ᵥ ι v := by
    intro A v; funext i; simp [ι, Matrix.mulVec, dotProduct, map_sum]
  have hevW : ∀ s : bk.S, bk.evW s ∈ bk.OE := fun s n => ⟨0, s, 0, by simp⟩
  have hevWι : ∀ c : Fin d → bk.S, ι (fun a => bk.ev (c a)) = fun a => bk.evW (c a) := fun c => rfl
  let mem : (Fin d → Ainf l) → Prop := fun y => ∀ i, (M⁻¹ *ᵥ ι y) i ∈ bk.OE
  have hY1M : Y1.map (inclW l) = M * V := by rw [hY1, hM, Matrix.smul_mul]
  have hmemV : ∀ c : Fin d → bk.S, mem (Y1 *ᵥ fun a => bk.ev (c a)) := by
    intro c i
    show (M⁻¹ *ᵥ ι (Y1 *ᵥ fun a => bk.ev (c a))) i ∈ bk.OE
    rw [hιmul, hevWι, hY1M, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hMM', Matrix.one_mul]
    simp only [Matrix.mulVec, dotProduct]
    exact Subring.sum_mem _ fun j _ => Subring.mul_mem _ (hV i j) (hevW _)
  obtain ⟨Y, hYu, hYmem⟩ := GlobalTheory.T.ainf_closed_membership_limit l K bk d mem
    (fun i => by
      show (M⁻¹ *ᵥ ι 0) i ∈ bk.OE
      have : ι 0 = 0 := by funext a; simp [ι]
      rw [this, Matrix.mulVec_zero]; exact Subring.zero_mem _)
    (fun y z hy hz i => by
      show (M⁻¹ *ᵥ ι (y + z)) i ∈ bk.OE
      have : ι (y + z) = ι y + ι z := by funext a; simp [ι]
      rw [this, Matrix.mulVec_add]; exact Subring.add_mem _ (hy i) (hz i))
    (fun c y hy i => by
      show (M⁻¹ *ᵥ ι (fun a => bk.ev c * y a)) i ∈ bk.OE
      have : ι (fun a => bk.ev c * y a) = bk.evW c • ι y := by funext a; simp [ι, BK.evW]
      rw [this, Matrix.mulVec_smul]; exact Subring.mul_mem _ (hevW c) (hy i))
    (fun y hy i => by
      have h : (M⁻¹ *ᵥ ι (fun a => (l : Ainf l) * y a)) i ∈ bk.OE := hy i
      have : ι (fun a => (l : Ainf l) * y a) = ((l : ℕ) : WCb l) • ι y := by funext a; simp [ι]
      rw [this, Matrix.mulVec_smul] at h
      exact hOEcl.1 _ h)
    (fun y hy _ z hz i => by
      refine hOEcl.2.1 _ fun n => ⟨_, hy n i, ?_⟩
      rw [← Pi.sub_apply, ← Matrix.mulVec_sub]
      simp only [Matrix.mulVec, dotProduct]
      refine Finset.dvd_sum fun j _ => Dvd.dvd.mul_left ?_ _
      have := map_dvd (inclW l) (hz n j)
      simpa [ι, map_sub, map_pow, map_natCast] using this)
    Y1 M (by rw [hY1M, Matrix.det_mul]; exact (hMu.mul hVu).ne_zero)
    ((Matrix.isUnit_iff_isUnit_det M).2 hMu) hmemV
    (fun y hy => by
      refine ⟨M⁻¹ *ᵥ ι y, hy, ?_⟩
      show ι y = M *ᵥ (M⁻¹ *ᵥ ι y)
      rw [Matrix.mulVec_mulVec, hMM, Matrix.one_mulVec])
  obtain ⟨Wm, hWm⟩ : ∃ Wm : Matrix (Fin d) (Fin d) (WCb l), Wm = M⁻¹ * Y.map (inclW l) := ⟨_, rfl⟩
  have hYWm : Y.map (inclW l) = M * Wm := by rw [hWm, ← Matrix.mul_assoc, hMM, Matrix.one_mul]
  have hcol : ∀ (A : Matrix (Fin d) (Fin d) (Ainf l)) (j : Fin d),
      (A *ᵥ fun a => bk.ev ((Pi.single j (1 : bk.S) : Fin d → bk.S) a)) = fun i => A i j := by
    intro A j; funext i; simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  have hWmOE : ∀ i j, Wm i j ∈ bk.OE := by
    intro i j
    have h : (M⁻¹ *ᵥ ι (fun a => Y a j)) i ∈ bk.OE := (hYmem (fun a => Y a j)).2 ⟨Pi.single j (1 : bk.S), (hcol Y j).symm⟩ i
    rw [hWm]
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, ι] using h
  have hC : ∀ j, ∃ c : Fin d → bk.S, (fun i => Y1 i j) = Y *ᵥ fun a => bk.ev (c a) := fun j =>
    (hYmem _).1 (by rw [← hcol Y1 j]; exact hmemV _)
  choose c hc using hC
  obtain ⟨Cw, hCw⟩ : ∃ Cw : Matrix (Fin d) (Fin d) (WCb l), Cw = Matrix.of fun a j => bk.evW (c j a) := ⟨_, rfl⟩
  have hVW : V = Wm * Cw := by
    have h1 : Y1.map (inclW l) = Y.map (inclW l) * Cw := by
      refine Matrix.ext fun i j => ?_
      have := congrArg (fun v => inclW l (v i)) (hc j)
      simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, hCw, BK.evW, map_sum] using this
    rw [hY1M, hYWm, Matrix.mul_assoc] at h1
    have h2 := congrArg (HMul.hMul M⁻¹) h1
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hMM', Matrix.one_mul, Matrix.one_mul] at h2
    exact h2
  refine ⟨Y, Wm, Cw * V', hYu, hWmOE, ?_, ?_, ?_, ?_⟩
  · intro i j
    simp only [Matrix.mul_apply, hCw, Matrix.of_apply]
    exact Subring.sum_mem _ fun k _ => Subring.mul_mem _ (hevW _) (hV' k j)
  · rw [← Matrix.mul_assoc, ← hVW, hVV']
  · rw [hYWm, hM, Matrix.smul_mul]
  · rintro y ⟨w, hw, hyw⟩
    refine (hYmem y).1 ?_
    intro i
    have : ι y = M *ᵥ w := by
      rw [hM]; refine hyw.trans ?_; funext i; simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
    show (M⁻¹ *ᵥ ι y) i ∈ bk.OE
    rw [this, Matrix.mulVec_mulVec, hMM', Matrix.one_mulVec]; exact hw i

end GlobalTheory.BKLim.SatLat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemistablePeriodPowDvdByBasisAinf
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section
namespace GlobalTheory.BKLim.WHeightSprime

theorem main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l) (hτ : bk.IsPer τ) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (hρ : ∀ g, IsUnit (ρ g)) (s : WSeed bk d ρ τ) (Y : Matrix (Fin d) (Fin d) (Ainf l)), IsUnit (Y.map (inclW l)) → (∀ y, (fun y : Fin d → Ainf l => ∃ x : Fin d → bk.DS bk.ρ₀, ∀ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap bk.ev j → s.W *ᵥ (fun a => j (x a)) = fun a => bk.iA (y a)) y ↔ ∃ c : Fin d → bk.S, y = Y *ᵥ fun a => bk.ev (c a)) → ∃ (k : ℕ) (S' : Matrix (Fin d) (Fin d) (Ainf l)), Y * S' = ((l : Ainf l) ^ k * τ ^ (2 * s.N)) • (1 : Matrix (Fin d) (Fin d) (Ainf l)) := by
  intro l _ K bk τ hτ d ρ hρ s Y hY hP
  obtain ⟨ι, TB, k, v, Z, hnull, hWZ, hsum⟩ := GlobalTheory.T.exists_bounded_semistable_periods_null_family l K bk τ hτ d ρ hρ s
  have hcol : ∀ i (b : Fin d), ∃ c : Fin d → bk.S, (fun a => v i a b) = Y *ᵥ fun a => bk.ev (c a) := by
    intro i b
    refine (hP _).1 ⟨fun a => Z i a b, fun j hj => ?_⟩
    funext a
    have h := congrFun (congrFun (hWZ j hj i) a) b
    simpa [Matrix.mulVec, dotProduct, Matrix.mul_apply] using h
  choose σc hσc using hcol
  set σ : ι → Matrix (Fin d) (Fin d) bk.S := fun i => Matrix.of fun a b => σc i b a with hσdef
  have hv : ∀ i, v i = Y * (σ i).map bk.ev := by
    intro i
    refine Matrix.ext fun a b => ?_
    have h := congrFun (hσc i b) a
    simpa [Matrix.mulVec, dotProduct, Matrix.mul_apply, σ] using h
  have hσn := GlobalTheory.T.null_powerSeries_of_null_ainf_mul l K bk ι TB d Y hY σ (fun n a b => by simpa only [← hv] using hnull n a b)
  have hL : ∀ c b : Fin d, ∃ L : Ainf l, ∀ n : ℕ, ∃ F : Finset ι, ∀ G : Finset ι, F ⊆ G →
      L - ∑ i ∈ G, bk.ev (σ i c b) * TB.b i ∈ (bk.J ^ n).map bk.ev :=
    fun c b => GlobalTheory.T.breuilKisin_exists_adic_sum_of_null_family l K bk ι TB (fun i => σ i c b) (fun n => hσn n c b)
  choose L hL using hL
  refine ⟨k, Matrix.of L, ?_⟩
  refine Matrix.ext fun a b => ?_
  refine GlobalTheory.T.ainf_jAdic_limit_eq_disc_sum l K bk ι TB (fun i => v i a b * TB.b i) _ _ ?_ ?_
  · simpa [Matrix.smul_apply, Matrix.one_apply] using hsum a b
  · classical
    intro n
    choose F hF using fun c => hL c b n
    refine ⟨Finset.univ.biUnion F, fun G hG => ?_⟩
    have e : (Y * Matrix.of L) a b - ∑ i ∈ G, v i a b * TB.b i =
        ∑ c, Y a c * (L c b - ∑ i ∈ G, bk.ev (σ i c b) * TB.b i) := by
      simp only [hv, Matrix.mul_apply, Matrix.map_apply, Matrix.of_apply, mul_sub, Finset.sum_sub_distrib,
        Finset.sum_mul, Finset.mul_sum]
      congr 1
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun i _ => by ring
    rw [e]
    exact Ideal.sum_mem _ fun c _ => Ideal.mul_mem_left _ _
      (hF c G ((Finset.subset_biUnion_of_mem F (Finset.mem_univ c)).trans hG))
end GlobalTheory.BKLim.WHeightSprime
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpehLanglandsQuotient
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL

noncomputable section

namespace GlobalTheory.LocGL

theorem IsLSeg.nu_rep {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {δ : IrrGL k} {Δ : Segment k} (h : IsLSeg Δ δ.rep) (c : ℂ) : IsLSeg (Δ.nu c) (δ.nu c).rep :=
  (h.tw (absPow k c) (isSmoothChar_absPow c)).of_equiv (δ.twEquiv _ _)

theorem IsSpeh.nu_rep {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {δ x : IrrGL k} {m : ℕ} (h : IsSpeh δ m x.rep) (s : ℂ) : IsSpeh (δ.nu s) m (x.nu s).rep := by
  obtain ⟨hd, h'⟩ := h.tw (absPow k s) (isSmoothChar_absPow s)
  exact ⟨hd, h'.of_equiv (x.twEquiv _ _) (.refl _)⟩

theorem isL_speh_nu (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (hP : ∀ (δ δ' : IrrGL k) (Δ Δ' : Segment k), IsLSeg Δ δ.rep → IsUnitarisable δ.rep → IsLSeg Δ' δ'.rep →
      IsUnitarisable δ'.rep → ∀ x y : ℝ, (Δ.nu x).Precedes (Δ'.nu y) → x + 1 ≤ y) :
    ∀ (δ x : IrrGL k) (Δ : Segment k) (m : ℕ), IsLSeg Δ δ.rep → IsUnitarisable δ.rep → IsSpeh δ m x.rep →
      ∀ s : ℝ, IsL ↑(List.ofFn fun i : Fin m => Δ.nu ((s + ((m : ℝ) - 1) / 2 - (i : ℕ) : ℝ) : ℂ)) (x.nu (s : ℂ)).rep := by
  intro δ x Δ m hL hU hS s
  obtain ⟨hd, hc⟩ := hS.nu_rep (s : ℂ)
  set c : Fin m → ℝ := fun i => s + ((m : ℝ) - 1) / 2 - (i : ℕ) with hcdef
  have hy : ∀ i, spehFactor (δ.nu s) m i = δ.nu (c i : ℂ) := fun i => by
    simp only [spehFactor, IrrGL.nu_nu, hcdef]
    congr 1
    push_cast
    ring
  refine ⟨m, spehFactor (δ.nu s) m, hd, ⟨fun i => Δ.nu (c i : ℂ), ⟨?_, ?_⟩, ?_⟩, hc⟩
  · rw [Fin.univ_val_map]
  · intro i j hij hp
    have h1 := hP δ δ Δ Δ hL hU hL hU (c i) (c j) hp
    have h2 : ((i : ℕ) : ℝ) < (j : ℕ) := by exact_mod_cast hij
    simp only [hcdef] at h1
    linarith
  · intro i
    rw [hy i]
    exact hL.nu_rep _

end GlobalTheory.LocGL
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StratifiedCrystalValueMapCommFrobenius
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem frob_coord_compat {C : Type} [CommRing C] {d d' : ℕ} (φ : C →+* C) (E T : C) (hE : E ∈ nonZeroDivisors C)
    (A : Matrix (Fin d) (Fin d) C) (A' : Matrix (Fin d') (Fin d') C) (Y : Matrix (Fin d') (Fin d) C)
    (a a' r r' k j : ℕ) (hY : E ^ a • (A' * Y.map φ) = E ^ a' • (Y * A)) (u m : Fin d → C) (n : Fin d' → C)
    (h1 : T ^ r • (E ^ a • m - T ^ k • A.mulVec fun i => φ (u i)) = 0)
    (h2 : T ^ r' • (E ^ a' • n - T ^ j • A'.mulVec fun i => φ (Y.mulVec u i)) = 0) :
    T ^ (r + r') • (T ^ k • n) = T ^ (r + r') • (T ^ j • Y.mulVec m) := by
  have e1 : (fun i => φ (Y.mulVec u i)) = (Y.map φ).mulVec fun i => φ (u i) := by
    funext i
    simp [Matrix.mulVec, dotProduct]
  rw [e1, Matrix.mulVec_mulVec] at h2
  have h3 := congrArg Y.mulVec h1
  rw [Matrix.mulVec_smul, Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_mulVec,
    Matrix.mulVec_zero] at h3
  have h4 := congrArg (fun Z => Matrix.mulVec Z fun i => φ (u i)) hY
  simp only [Matrix.smul_mulVec] at h4
  funext i
  have h2i := congrFun h2 i
  have h3i := congrFun h3 i
  have h4i := congrFun h4 i
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Pi.zero_apply] at h2i h3i h4i ⊢
  rw [← sub_eq_zero]
  refine (mem_nonZeroDivisors_iff.1 (pow_mem hE (a + a'))).1 _ ?_
  linear_combination (T ^ r * T ^ k * E ^ a) * h2i - (T ^ r' * T ^ j * E ^ a') * h3i +
    T ^ (r + r' + k + j) * h4i

theorem eval_map_Φ : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d d' : ℕ) (S : Strat bk d) (S' : Strat bk d') (M : FCrys l ↥(OL K)) (e : Module.Basis (Fin d) bk.prism.A (M.M bk.prism)) (M' : FCrys l ↥(OL K)) (e' : Module.Basis (Fin d') bk.prism.A (M'.M bk.prism)), Framed S M e → Framed S' M' e' → ∀ Y : Matrix (Fin d') (Fin d) bk.S, IsStratHom S S' Y → ∀ (B : Obj l ↥(OL K)) (V : Eval S B (M.M B)) (V' : Eval S' B (M'.M B)), IsCoord e V → IsCoord e' V' → ∀ w : M.M B →ₗ[B.A] M'.M B, (∀ (Q : Obj l ↥(OL K)) (a : Hom B Q) (g : Hom bk.prism Q) (x : M.M B), V'.v a g (w x) = (Y.map (BK.hf g)).mulVec (V.v a g x)) → ∀ (t : ↥B.I) (x m : M.M B) (k : ℕ), IsFrac (t : B.A) (M.Φ B t x) m k → IsFrac (t : B.A) (M'.Φ B t (w x)) (w m) k := by
  intro l _ K bk d d' S S' M e M' e' hF hF' Y hY B V V' hV hV' w hw t x m k hx
  refine (GlobalTheory.T.exists_prism_cover_receiving_breuilKisin l K bk B).elim fun C hC => hC.elim fun h hC => hC.1.elim fun g => ?_
  have hc := hC.2
  have hinj := (GlobalTheory.T.injective_and_range_of_prism_cover l K bk d' S' B C (M'.M B) V' h g hc).1
  have hE := (GlobalTheory.T.breuilKisinHom_eisenstein_span_and_nonZeroDivisor l K bk C g).2
  have hnj : ∃ n j, IsFrac (t : B.A) (M'.Φ B t (w x)) n j := by
    induction M'.Φ B t (w x) using LocalizedModule.induction_on with
    | h n s =>
      obtain ⟨_, j, rfl⟩ := s
      exact ⟨n, j, rfl⟩
  refine hnj.elim fun n hn => hn.elim fun j hn => ?_
  refine (GlobalTheory.T.framedCrystal_frobenius_coordinates l K bk d S M e hF B V hV t x m k hx C h g).elim fun r h1 => ?_
  refine (GlobalTheory.T.framedCrystal_frobenius_coordinates l K bk d' S' M' e' hF' B V' hV' t (w x) n j hn C h g).elim fun r' h2 => ?_
  rw [hw] at h2
  have hY' : BK.hf g bk.E ^ S.a • (S'.A.map (BK.hf g) * (Y.map (BK.hf g)).map C.D.φ) =
      BK.hf g bk.E ^ S'.a • (Y.map (BK.hf g) * S.A.map (BK.hf g)) := by
    have e1 : (Y.map (BK.hf g)).map C.D.φ = (Y.map (frobS l bk.a)).map (BK.hf g) := by
      ext i j
      exact (g.f_φ (Y i j)).symm
    rw [e1, ← Matrix.map_mul, ← Matrix.map_mul]
    ext i j
    have h5 := congrArg (BK.hf g) (congrFun (congrFun hY.φ i) j)
    simpa only [Matrix.smul_apply, smul_eq_mul, map_mul, map_pow, Matrix.map_apply] using h5
  have key := frob_coord_compat C.D.φ _ _ hE _ _ _ _ _ _ _ _ _ hY' _ _ _ h1 h2
  unfold IsFrac at hn ⊢
  rw [hn, LocalizedModule.mk_eq]
  refine ⟨⟨(t : B.A) ^ (r + r'), r + r', rfl⟩, hinj ?_⟩
  simp only [Submonoid.smul_def, LinearMap.map_smulₛₗ, map_pow, hw]
  exact key

end GlobalTheory.BSP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StratifiedHomComparisonCompatibleEnvelope
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem strat_defect_map {l : ℕ} [Fact l.Prime] {K : FinExt l} {bk : BK K} {d d' : ℕ} (S : Strat bk d)
    (S' : Strat bk d') (Y : Matrix (Fin d') (Fin d) bk.S) {B C : Obj l ↥(OL K)} (σ : Hom B C)
    (f g : Hom bk.prism B) :
    (S'.ε f g * Y.map (BK.hf g) - Y.map (BK.hf f) * S.ε f g).map σ.f =
      S'.ε (σ.comp f) (σ.comp g) * Y.map (BK.hf (σ.comp g)) -
        Y.map (BK.hf (σ.comp f)) * S.ε (σ.comp f) (σ.comp g) := by
  have e1 : (Y.map (BK.hf g)).map σ.f = Y.map (BK.hf (σ.comp g)) := rfl
  have e2 : (Y.map (BK.hf f)).map σ.f = Y.map (BK.hf (σ.comp f)) := rfl
  have m1 := Matrix.map_mul (L := S'.ε f g) (M := Y.map (BK.hf g)) (f := σ.f)
  have m2 := Matrix.map_mul (L := Y.map (BK.hf f)) (M := S.ε f g) (f := σ.f)
  rw [Matrix.map_sub _ (map_sub σ.f), m1, m2, S'.ε_nat, S.ε_nat, e1, e2]

theorem matrix_phi_eq_family_self (C : Type) [CommRing C] (φ : C → C) (e e' : C) (he : Associated e e')
    (d d' a a' b : ℕ) (P : Matrix (Fin d') (Fin d') C) (Q Q' : Matrix (Fin d) (Fin d) C)
    (hQ : Q * Q' = e' ^ b • (1 : Matrix (Fin d) (Fin d) C)) (Δ : Matrix (Fin d') (Fin d) C)
    (h : e' ^ a • (P * Δ.map φ) = e ^ a' • (Δ * Q)) :
    ∃ (h : ℕ) (c : Fin d' × Fin d → Fin d' × Fin d → C), ∀ j : Fin d' × Fin d,
      e ^ h * Δ j.1 j.2 = ∑ k : Fin d' × Fin d, φ (Δ k.1 k.2) * c k j :=
  GlobalTheory.T.matrix_phi_equation_to_family_equation C C (RingHom.id C) φ e e' he d d' a a' b P Q Q' hQ Δ h

theorem obj_eq_zero_of_pow_dvd {l : ℕ} [Fact l.Prime] {K : FinExt l} (B : Obj l ↥(OL K)) (x : B.A)
    (hk : ∀ k : ℕ, ((l : ℕ) : B.A) ^ k ∣ x) : x = 0 := by
  refine B.complete.toIsHausdorff.haus _ fun n => ?_
  obtain ⟨y, hy⟩ := hk n
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, hy]
  exact Ideal.mul_mem_right _ _
    (Ideal.pow_mem_pow (Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)) n)

theorem strat_map_A_mul {l : ℕ} [Fact l.Prime] {K : FinExt l} {bk : BK K} {d : ℕ} (S : Strat bk d)
    {B : Obj l ↥(OL K)} (g : Hom bk.prism B) :
    S.A.map (BK.hf g) * S.A'.map (BK.hf g) = BK.hf g bk.E ^ S.b • (1 : Matrix (Fin d) (Fin d) B.A) := by
  rw [← Matrix.map_mul, S.A_mul]
  ext i j
  by_cases hij : i = j <;> simp [Matrix.one_apply, hij]

theorem env_matrix_eq_zero {l : ℕ} [Fact l.Prime] {K : FinExt l} {bk : BK K}
    (En : Env bk bk.prism (bk.toP bk.E) (bk.toP X)) {d d' : ℕ} (S : Strat bk d) (S' : Strat bk d')
    (Δ : Matrix (Fin d') (Fin d) En.Q.A)
    (h1 : BK.hf En.inr bk.E ^ S.a • (S'.A.map (BK.hf En.inl) * Δ.map En.Q.D.φ) =
      BK.hf En.inl bk.E ^ S'.a • (Δ * S.A.map (BK.hf En.inr)))
    (hσ : ∀ (g : ↥(GK K)) (σ : Hom En.Q (ainfObj K)), σ.comp En.inl = bk.ι →
      σ.comp En.inr = (ainfHom K g).comp bk.ι → Δ.map σ.f = 0) : Δ = 0 := by
  have hass := (GlobalTheory.T.breuilKisin_two_homs_E_regular_associated l K bk En.Q En.inl En.inr).2.1
  obtain ⟨h, c, hc⟩ := matrix_phi_eq_family_self En.Q.A En.Q.D.φ _ _ hass d d' S.a S'.a S.b
    (S'.A.map (BK.hf En.inl)) _ _ (strat_map_A_mul S En.inr) Δ h1
  refine Matrix.ext fun i j => obj_eq_zero_of_pow_dvd En.Q (Δ i j) fun k => ?_
  refine GlobalTheory.T.breuilKisin_envelope_frobenius_solutions_pow_dvd l K bk En (Fin d' × Fin d) c h k (fun p => Δ p.1 p.2) hc ?_ (i, j)
  intro g σ ha hb p
  have h0 : σ.f (Δ p.1 p.2) = 0 := congrFun (congrFun (hσ g σ ha hb) p.1) p.2
  exact ⟨0, h0.trans (mul_zero _).symm⟩

theorem strat_eps_compat_env (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K)
    (En : Env bk bk.prism (bk.toP bk.E) (bk.toP X)) (d d' : ℕ) (S : Strat bk d) (S' : Strat bk d')
    (Y : Matrix (Fin d') (Fin d) bk.S)
    (hφ : bk.E ^ S.a • (S'.A * Y.map (frobS l bk.a)) = bk.E ^ S'.a • (Y * S.A))
    (hg : ∀ g : ↥(GK K), S'.ε bk.ι ((ainfHom K g).comp bk.ι) * Y.map (BK.hf ((ainfHom K g).comp bk.ι)) =
      Y.map (BK.hf bk.ι) * S.ε bk.ι ((ainfHom K g).comp bk.ι)) :
    S'.ε En.inl En.inr * Y.map (BK.hf En.inr) = Y.map (BK.hf En.inl) * S.ε En.inl En.inr := by
  have h1 := GlobalTheory.T.stratifiedHom_defect_frobenius_equation l K bk d d' S S' Y hφ En.Q En.inl En.inr
  have hσ : ∀ (g : ↥(GK K)) (σ : Hom En.Q (ainfObj K)), σ.comp En.inl = bk.ι →
      σ.comp En.inr = (ainfHom K g).comp bk.ι →
      (S'.ε En.inl En.inr * Y.map (BK.hf En.inr) - Y.map (BK.hf En.inl) * S.ε En.inl En.inr).map σ.f = 0 := by
    intro g σ ha hb
    rw [strat_defect_map, ha, hb, hg g, sub_self]
  exact sub_eq_zero.1 (env_matrix_eq_zero En S S' _ h1 hσ)

end GlobalTheory.BSP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StratifiedValueFrobeniusCommTransition
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

set_option maxHeartbeats 1000000 in

theorem GlobalTheory.BSP.psi_nat : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (S : Strat bk d) (B B' : Obj l ↥(OL K)) (N : Type) [AddCommGroup N] [Module B.A N] (N' : Type) [AddCommGroup N'] [Module B'.A N'] (V : Eval S B N) (V' : Eval S B' N') (k : Hom B B') (τ : N →ₛₗ[k.f] N'), (∀ (Q : Obj l ↥(OL K)) (a : Hom B' Q) (g : Hom bk.prism Q) (x : N), V'.v a g (τ x) = V.v (a.comp k) g x) → ∀ (t : B.A) (t' : B'.A) (Ψ : N →ₛₗ[B.D.φ] N) (Ψ' : N' →ₛₗ[B'.D.φ] N'), IsPsi V t Ψ → IsPsi V' t' Ψ' → ∀ x, t' ^ S.a • τ (Ψ x) = k.f t ^ S.a • Ψ' (τ x) := by
  intro l _ K bk d S B B' N _ _ N' _ _ V V' k τ hτ t t' Ψ Ψ' hΨ hΨ' x
  obtain ⟨C, h, ⟨f⟩, hc⟩ := GlobalTheory.T.exists_prism_cover_receiving_breuilKisin l K bk B'
  have hinj := (GlobalTheory.T.injective_and_range_of_prism_cover l K bk d S B' C N' V' h f hc).1
  have hE : BK.hf f bk.E ^ S.a ∈ nonZeroDivisors C.A := pow_mem (GlobalTheory.T.breuilKisinHom_eisenstein_span_and_nonZeroDivisor l K bk C f).2 _
  apply hinj
  have L : V'.v h f (t' ^ S.a • τ (Ψ x)) = h.f t' ^ S.a • V.v (h.comp k) f (Ψ x) := by
    rw [map_smulₛₗ, map_pow, hτ]
  have R : V'.v h f (k.f t ^ S.a • Ψ' (τ x)) = h.f (k.f t) ^ S.a • V'.v h f (Ψ' (τ x)) := by
    rw [map_smulₛₗ, map_pow]
  have hkt : (h.comp k).f t = h.f (k.f t) := rfl
  have key : BK.hf f bk.E ^ S.a • V'.v h f (t' ^ S.a • τ (Ψ x)) =
      BK.hf f bk.E ^ S.a • V'.v h f (k.f t ^ S.a • Ψ' (τ x)) := by
    rw [L, R, smul_comm (BK.hf f bk.E ^ S.a) (h.f t' ^ S.a), smul_comm (BK.hf f bk.E ^ S.a) (h.f (k.f t) ^ S.a),
      hΨ (h.comp k) f x, hΨ' h f (τ x), hτ C h f x, smul_smul, smul_smul, hkt, mul_comm]
  funext i
  have hi := congrFun key i
  simp only [Pi.smul_apply, smul_eq_mul] at hi
  exact (mul_cancel_left_mem_nonZeroDivisors hE).1 hi
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameBreuilKisinDatumExistsStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tame_breuil_kisin_datum_exists : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (κ : Type) [Fintype κ] [DecidableEq κ] (η H : ℕ) (D₁ : BKDat O K l e a ι η H) (D₂ : BKDat O K l e a κ η H) (T₁ T₂ : LocLat (Gl l) ℚ_[l] K O) (R₁ : GalDat t ϖ (sQ l) D₁ T₁) (R₂ : GalDat t ϖ (sQ l) D₂ T₂) (f : LatHom T₁.L T₂.L) (F : BKHom D₁ D₂), IsMapOf R₁.I R₂.I f F.toHom → ∀ y c, R₁.ClassOf y c → R₂.ClassOf (F.app y) (f.post c) := by
  first | exact @GlobalTheory.CocycleNat.main | exact GlobalTheory.CocycleNat.main | (intros; apply GlobalTheory.CocycleNat.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TendstoSignedLatticeSumSubNormCharacterMulStatement
section
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tendsto_signedLatticeSum_sub_normCharacter_mul : ∀ (K : UQ) (B : InvAlg K) (ι : Type) [Fintype ι] [DecidableEq ι] (e π : ι → B.A) (S : Finset ι) (a : K.O), B.LieReg → K.Small a → IsFrame B e π S → ∀ I ⊆ S, ∀ x : B.A, B.Plus x → Tendsto (fun k : ℕ => (((HH B π I (S \ I) (x * algebraMap K.O B.A a ^ (2 * k)) 1 - chi B e I x * HH B π I (S \ I) (algebraMap K.O B.A a ^ (2 * k)) 1 : ℚ) : ℝ) / (B.rho (algebraMap K.O B.A a ^ k) : ℝ))) atTop (𝓝 0) := by
  first | exact @GlobalTheory.UnitLemma.Desc.HH_sub_chi_mul_HH_negligible | exact GlobalTheory.UnitLemma.Desc.HH_sub_chi_mul_HH_negligible | (intros; apply GlobalTheory.UnitLemma.Desc.HH_sub_chi_mul_HH_negligible <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TypeSpaceProjectionToPointEigenspacesStatement
section
open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef NumberField IsDedekindDomain GlobalTheory.EtaJoin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.typeSpace_projection_to_pointEigenspaces : ∀ (D : D7) (M : MtFam D) (i : D.nd.Loc), HeckeTied D M → HeckeRational D M → AVTied D M → SplitUnif D → HeckeScalar M i → D.nd.EigSpan → TypeTie D i := by
  first | exact @GlobalTheory.EtaJoin.TypeTieProof.typeTie_holds | exact GlobalTheory.EtaJoin.TypeTieProof.typeTie_holds | (intros; apply GlobalTheory.EtaJoin.TypeTieProof.typeTie_holds <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentColumnWhittakerTransformMirabolicInvari
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric

namespace GlobalTheory.CuspGeneric

theorem IsMir.succ {E : Type} [Field E] {a m : ℕ} {γ : GL (Fin a) E} (hγ : IsMir m γ) : IsMir (m + 1) γ :=
  fun i k h => hγ i k (by omega)

theorem colT_isMir_invariant : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (ψ : AddChar (Ad E) ℂ), StdPsi ψ →
    ∀ (m : ℕ) (f : GA E a → ℂ), m + 1 < a → Good ψ (m + 1) f → ∀ γ : GL (Fin a) E, IsMir m γ →
    ∀ g, colT ψ (m + 1) f (ratGL E a γ * g) = colT ψ (m + 1) f g := by
  intro E _ _ a ψ hψ m f hma hf γ hγ g
  have key := GlobalTheory.T.whittakerCoefficient_rationalMirabolic_mul E a ψ hψ m f hf.cont hf.left γ hγ.succ (eLast a (m + 1)) g
  unfold colT
  rw [key]
  congr 1
  funext t
  let s0 : UnipotentBlockColumnIndex a (m + 1) (m + 1) := ⟨(⟨m, by omega⟩, ⟨m + 1, hma⟩), Nat.lt_succ_self m, le_refl _, le_refl _⟩
  rw [Finset.sum_eq_single s0]
  · have h1 : eLast (E := E) a (m + 1) s0 = 1 := by simp [eLast, s0]
    rw [h1, one_mul, hγ _ _ (Or.inl (le_refl m))]
    have ht := t.2.1
    simp only [eLast, Matrix.one_apply]
    by_cases h : (t.1.1 : ℕ) = m
    · rw [if_pos (Fin.ext h.symm), if_pos (by omega)]
    · rw [if_neg (fun e => h (congrArg Fin.val e).symm), if_neg (by omega)]
  · intro s _ hs
    have h0 : eLast (E := E) a (m + 1) s = 0 := by
      simp only [eLast]
      rw [if_neg]
      intro e
      apply hs
      have h2 := s.2.2
      apply Subtype.ext
      exact Prod.ext (Fin.ext (by simp [s0]; omega)) (Fin.ext (by simp [s0]; omega))
    rw [h0, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

end GlobalTheory.CuspGeneric
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeExpansionAtLowLevelPointsStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wach_lattice_expansion_at_low_level_points : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), P4 D HW F Cm := by
  first | exact @GlobalTheory.NL.LatLevel.lattice_at_level | exact GlobalTheory.NL.LatLevel.lattice_at_level | (intros; apply GlobalTheory.NL.LatLevel.lattice_at_level <;> assumption)
end

