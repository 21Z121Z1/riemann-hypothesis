import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LogPeriodLimit
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0081
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0041
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0035
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0079
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0072
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0085
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0042
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0075
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0086
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0058
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0062
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0060
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0065
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0066
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0068
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ValueConstantOnOrbitStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0061

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.NzEqNzOfAndPos
section
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
open GlobalTheory.CompanionTheory.Ar.RiemannLimit GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit

namespace GlobalTheory.CompanionTheory.Ar.Cusp.NzCase

theorem nz_eq_nzOf_of_family : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (Ψ : Type) [Fintype Ψ] (R : RiemLat E g Λ) (σ : Ψ → (𝓞 E →+* ℂ)) (I : Submodule (𝓞 E) Λ) (r : ℕ) (y : Fin r → Λ), IsCMFam σ → IsIsoSub R.form I → (∀ a, y a ∈ I) → LinearIndependent (𝓞 E) y → (Submodule.span (𝓞 E) (Set.range y)).toAddSubgroup.relIndex I.toAddSubgroup ≠ 0 → R.nz σ I = R.nzOf σ I y ∧ 0 < R.nz σ I := by
  intro E _ _ _ g Λ _ _ Ψ _ R σ I r y hσ hI hy hli hidx
  by_cases hbot : I = ⊥
  · subst hbot
    have hy0 : ∀ a, y a = 0 := fun a => by simpa using hy a
    have hr : r = 0 := by
      by_contra h
      exact hli.ne_zero (⟨0, Nat.pos_of_ne_zero h⟩ : Fin r) (hy0 _)
    subst hr
    have hno : ¬ ∃ r v, IsNzFamily (⊥ : Submodule (𝓞 E) Λ) r v := by
      rintro ⟨ρ, v, h1, hv, hl, -⟩
      exact hl.ne_zero (⟨0, h1⟩ : Fin ρ) (by simpa using hv ⟨0, h1⟩)
    have hnz : R.nz σ (⊥ : Submodule (𝓞 E) Λ) = 1 := by
      simp only [RiemLat.nz]
      exact dif_neg hno
    have hof : R.nzOf σ (⊥ : Submodule (𝓞 E) Λ) y = 1 := by
      have hs : Submodule.span (𝓞 E) (Set.range y) = ⊥ := by
        simp [Set.range_eq_empty]
      simp [RiemLat.nzOf, hs]
    rw [hnz, hof]
    exact ⟨rfl, one_pos⟩
  · have hr : 1 ≤ r := by
      by_contra h
      have hr0 : r = 0 := by omega
      subst hr0
      have hs : Submodule.span (𝓞 E) (Set.range y) = ⊥ := by
        simp [Set.range_eq_empty]
      have hb : (⊥ : Submodule (𝓞 E) Λ).toAddSubgroup = ⊥ := rfl
      rw [hs, hb, AddSubgroup.relIndex_bot_left] at hidx
      haveI : Finite I.toAddSubgroup := Nat.finite_of_card_ne_zero hidx
      obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
      haveI := R.free
      have hfin : IsOfFinAddOrder (⟨x, hx⟩ : I.toAddSubgroup) := isOfFinAddOrder_of_finite _
      obtain ⟨n, hn, hnx⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.1 hfin
      have hnx' : n • x = 0 := congrArg Subtype.val hnx
      have hzx : (n : ℤ) • x = 0 := by rw [natCast_zsmul]; exact hnx'
      exact hx0 ((smul_eq_zero.1 hzx).resolve_left (by exact_mod_cast hn.ne'))
    have hfam : IsNzFamily I r y := ⟨hr, hy, hli, hidx⟩
    have h := (GlobalTheory.T.isotropic_sublattice_covolume_positive E g Λ Ψ R σ I hσ hI hbot).2 r y hfam
    exact ⟨h.1, h.2.1⟩

end GlobalTheory.CompanionTheory.Ar.Cusp.NzCase
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ProdXbPowEqXcOfPow
section
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm

variable {Ψ : Type} {p q : ℕ} {Ω : Type} [Field Ω] {n : Ψ ⊕ Ψ → ℕ} {K₀ : Type} {J₀ : K₀ → Type}

theorem eq_baseFull (k' : NonPluckerBlocks (blkF Ψ p q K₀)) {s : Ψ ⊕ Ψ} {a : Fin (rk Ψ p q s)}
    (hk : k'.1 = .inr ⟨s, a⟩) (h : 0 < rk Ψ p q s) : k' = baseFull K₀ s h := by
  have hfull : (a : ℕ) + 1 = rk Ψ p q s :=
    BasePt.step_full K₀ ⟨s, a⟩ (by rw [← hk]; exact k'.2)
  apply Subtype.ext
  rw [hk]
  have e : a = ⟨rk Ψ p q s - 1, by omega⟩ := Fin.ext (by show (a : ℕ) = rk Ψ p q s - 1; omega)
  rw [e]
  rfl

theorem xb_of_step [Fintype Ψ] [Fintype K₀] [∀ k, Fintype (J₀ k)]
    (A : ∀ s, Matrix (Fin (n s)) (Fin (rk Ψ p q s)) Ω) (x₀ : (Σ k, J₀ k) → Ω)
    (c : ∀ k : NonPluckerBlocks (blkF Ψ p q K₀), baseIdx (idx (p := p) (q := q) J₀ n) (blkF Ψ p q K₀) k)
    (k' : NonPluckerBlocks (blkF Ψ p q K₀)) {s : Ψ ⊕ Ψ} {a : Fin (rk Ψ p q s)} (hk : k'.1 = .inr ⟨s, a⟩) :
    xb A x₀ ⟨k', c k'⟩ = zOf A c s := by
  have h : 0 < rk Ψ p q s := by have := a.2; omega
  obtain rfl := eq_baseFull k' hk h
  exact xb_rowsOf A x₀ c s h

theorem zOf_of_rk_eq_zero (A : ∀ s, Matrix (Fin (n s)) (Fin (rk Ψ p q s)) Ω)
    (c : ∀ k : NonPluckerBlocks (blkF Ψ p q K₀), baseIdx (idx (p := p) (q := q) J₀ n) (blkF Ψ p q K₀) k)
    {s : Ψ ⊕ Ψ} (h : rk Ψ p q s = 0) : zOf A c s = 1 := by
  haveI : IsEmpty (Fin (rk Ψ p q s)) := by rw [h]; infer_instance
  exact Matrix.det_isEmpty

open Classical in

def stepFac (z : Ω) (s : Ψ ⊕ Ψ) : K₀ ⊕ StepIx Ψ p q → Ω :=
  Sum.elim (fun _ => 1) fun t => if t.1 = s then z else 1

theorem prod_stepFac [Fintype Ψ] [Fintype K₀] (z : Ω) (s : Ψ ⊕ Ψ) (hz : rk Ψ p q s = 0 → z = 1) :
    ∏ k' : NonPluckerBlocks (blkF Ψ p q K₀), stepFac z s k'.1 = z := by
  classical
  by_cases h : 0 < rk Ψ p q s
  · rw [Finset.prod_eq_single (baseFull K₀ s h)]
    · simp [stepFac, baseFull, fullT]
    · rintro ⟨k | ⟨s', a⟩, hk⟩ _ hb
      · simp [stepFac]
      · by_cases e : s' = s
        · subst e
          exact absurd (eq_baseFull _ rfl h) hb
        · simp [stepFac, e]
    · simp
  · rw [hz (by omega)]
    refine Finset.prod_eq_one ?_
    rintro ⟨k | ⟨s', a⟩, hk⟩ _
    · simp [stepFac]
    · by_cases e : s' = s
      · subst e
        have := a.2
        omega
      · simp [stepFac, e]

theorem prod_xb_zpow_bF {Ψ : Type} [Fintype Ψ] {p q : ℕ} {Ω : Type} [Field Ω] {n : Ψ ⊕ Ψ → ℕ}
    (A : ∀ s, Matrix (Fin (n s)) (Fin (rk Ψ p q s)) Ω) {K₀ : Type} [Fintype K₀] {J₀ : K₀ → Type}
    [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω) (m : Ψ ⊕ Ψ → ℕ)
    (c : ∀ k : NonPluckerBlocks (blkF Ψ p q K₀), baseIdx (idx (p := p) (q := q) J₀ n) (blkF Ψ p q K₀) k)
    (r : Ψ × Fin (p + q)) :
    ∏ k', xb A x₀ ⟨k', c k'⟩ ^ bF m r k' =
      xcOf x₀ c ^ (rkW r.2 * m (.inl r.1) + rkO r.2 * m (.inr r.1)) *
        (if p ≤ (r.2 : ℕ) + 1 then (zOf A c (.inl r.1))⁻¹ else 1) *
        (if (r.2 : ℕ) + 1 = p + q then (zOf A c (.inr r.1))⁻¹ else 1) := by
  classical
  set N := rkW r.2 * m (.inl r.1) + rkO r.2 * m (.inr r.1) with hN
  set zW : Ω := if p ≤ (r.2 : ℕ) + 1 then (zOf A c (.inl r.1))⁻¹ else 1 with hzW
  set zO : Ω := if (r.2 : ℕ) + 1 = p + q then (zOf A c (.inr r.1))⁻¹ else 1 with hzO
  have hW : rk Ψ p q (.inl r.1) = 0 → zW = 1 := fun h => by
    rw [hzW, zOf_of_rk_eq_zero A c h]
    simp
  have hO : rk Ψ p q (.inr r.1) = 0 → zO = 1 := fun h => by
    rw [hzO, zOf_of_rk_eq_zero A c h]
    simp
  let g : NonPluckerBlocks (blkF Ψ p q K₀) → Ω := fun k' =>
    Sum.elim (fun _ => xb A x₀ ⟨k', c k'⟩ ^ N) (fun _ => 1) k'.1
  have hg : ∏ k', g k' = xcOf x₀ c ^ N := by
    rw [xcOf, ← Finset.prod_pow]
    refine (Fintype.prod_of_injective (baseInl (Ψ := Ψ) (p := p) (q := q)) ?_ _ _ ?_ ?_).symm
    · intro a b e
      exact Sum.inl.inj (congrArg Subtype.val e)
    · rintro ⟨k | t, hk⟩ hi
      · exact absurd ⟨k, rfl⟩ hi
      · rfl
    · intro k
      rfl
  have hpt : ∀ k', xb A x₀ ⟨k', c k'⟩ ^ bF m r k' =
      g k' * stepFac zW (.inl r.1) k'.1 * stepFac zO (.inr r.1) k'.1 := by
    rintro ⟨k | ⟨s, a⟩, hk⟩
    · have e : bF m r (⟨.inl k, hk⟩ : NonPluckerBlocks (blkF Ψ p q K₀)) = (N : ℤ) := rfl
      rw [e, zpow_natCast]
      simp [g, stepFac]
    · have hx := xb_of_step A x₀ c ⟨.inr ⟨s, a⟩, hk⟩ (s := s) (a := a) rfl
      have hf : (a : ℕ) + 1 = rk Ψ p q s := BasePt.step_full K₀ ⟨s, a⟩ hk
      rw [hx]
      rcases s with τ | τ
      · by_cases e : τ = r.1
        · subst e
          have hf' : (a : ℕ) + 1 = p := hf
          by_cases hc : p ≤ (r.2 : ℕ) + 1
          · simp [bF, twist, g, stepFac, hf', hc, hzW]
          · simp [bF, twist, g, stepFac, hf', hc, hzW]
        · simp [bF, twist, g, stepFac, e]
      · by_cases e : τ = r.1
        · subst e
          have hf' : (a : ℕ) + 1 = q := hf
          by_cases hc : (r.2 : ℕ) + 1 = p + q
          · simp [bF, twist, g, stepFac, hf', hc, hzO]
          · simp [bF, twist, g, stepFac, hf', hc, hzO]
        · simp [bF, twist, g, stepFac, e]
  rw [Finset.prod_congr rfl fun k' _ => hpt k', Finset.prod_mul_distrib, Finset.prod_mul_distrib, hg,
    prod_stepFac zW _ hW, prod_stepFac zO _ hO]

end GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.TMatBlockDiagDetFactors
section
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm

variable {Ψ : Type} {p q : ℕ} {Ω : Type} [Field Ω]

theorem tMat_blockEquiv (Ts : ∀ s, Matrix (Fin (rk Ψ p q s)) (Fin (rk Ψ p q s)) Ω) (τ : Ψ) (a b : Fin q ⊕ Fin p) :
    tMat Ts τ (blockEquiv p q a) (blockEquiv p q b) =
      (Matrix.fromBlocks (Ts (.inr τ)) 0 0 (Ts (.inl τ)) : Matrix (Fin q ⊕ Fin p) (Fin q ⊕ Fin p) Ω) a b := by
  simp [tMat]
  rfl

theorem omBlock_tMat (Ts : ∀ s, Matrix (Fin (rk Ψ p q s)) (Fin (rk Ψ p q s)) Ω) (τ : Ψ) :
    omBlock (tMat Ts τ) = Ts (.inr τ) := by
  ext a b
  exact tMat_blockEquiv Ts τ (.inl a) (.inl b)

theorem wBlock_tMat (Ts : ∀ s, Matrix (Fin (rk Ψ p q s)) (Fin (rk Ψ p q s)) Ω) (τ : Ψ) :
    wBlock (tMat Ts τ) = Ts (.inl τ) := by
  ext a b
  exact tMat_blockEquiv Ts τ (.inr a) (.inr b)

theorem isBlockDiag_tMat (Ts : ∀ s, Matrix (Fin (rk Ψ p q s)) (Fin (rk Ψ p q s)) Ω) (τ : Ψ) :
    IsBlockDiag p (tMat Ts τ) := by
  intro a b hab
  obtain ⟨a, rfl⟩ := (blockEquiv p q).surjective a
  obtain ⟨b, rfl⟩ := (blockEquiv p q).surjective b
  rw [tMat_blockEquiv]
  rcases a with a | a <;> rcases b with b | b
  · exact absurd (by
      have h1 := a.2
      have h2 := b.2
      show ((a : ℕ) < p + q - p ↔ (b : ℕ) < p + q - p)
      omega) hab
  · rfl
  · rfl
  · exact absurd (by
      show (q + (a : ℕ) < p + q - p ↔ q + (b : ℕ) < p + q - p)
      omega) hab

theorem tMat_main {Ψ : Type} {p q : ℕ} {Ω : Type} [Field Ω]
    (Ts : ∀ s, Matrix (Fin (rk Ψ p q s)) (Fin (rk Ψ p q s)) Ω) (τ : Ψ) :
    IsBlockDiag p (tMat Ts τ) ∧ (tMat Ts τ).det = (Ts (.inr τ)).det * (Ts (.inl τ)).det ∧
      ∀ i : Fin (p + q), detFac p i (tMat Ts τ) =
        (if p ≤ (i : ℕ) + 1 then (Ts (.inl τ)).det else 1) * (if (i : ℕ) + 1 = p + q then (Ts (.inr τ)).det else 1) := by
  refine ⟨isBlockDiag_tMat Ts τ, ?_, fun i => ?_⟩
  · have h := (isBlockDiag_tMat Ts τ).det_eq_blocks
    rw [omBlock_tMat, wBlock_tMat] at h
    exact h
  · have h1 : minorIJ (tMat Ts τ) (wIdx (p + q) p) (wIdx (p + q) p) = (Ts (.inl τ)).det := by
      rw [minorIJ_wIdx, wBlock_tMat]
      rfl
    have h2 : minorIJ (tMat Ts τ) (omIdx (p + q) p) (omIdx (p + q) p) = (Ts (.inr τ)).det := by
      rw [minorIJ_omIdx, omBlock_tMat]
      rfl
    rw [detFac, h1, h2]

end GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.TwistedAtlasCompatibilityStatement
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_atlas_compatibility : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n e : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a : Fin N) (k₀ : K) (ca cb : Fin N) (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ e) (pr : RW.X → Rb.X), M.blk (τ, a) = some k₀ → IsWAtlas M Rb τ a k₀ ca cb RW pr → ∀ (x : RW.X) (z₀ z₁ : (Σ k, ι k) → ℂ), SameOrbit z₀ (fstPt k₀ (RW.lift x x)) → SameOrbit z₁ (sndPt k₀ (RW.lift x x)) → basePart M.blk z₀ ∈ mcPts (mCoordIdeal M.x) ∧ SameOrbit (basePart M.blk z₁) (basePart M.blk z₀) ∧ (∀ k, ∃ i, z₀ ⟨k, i⟩ ≠ 0) ∧ ∀ k, ∃ i, z₁ ⟨k, i⟩ ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.PtBase.main | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.PtBase.main | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.PtBase.main <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.TwistedChartCoordinatesRegularStatement
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_chart_coordinates_regular : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n e : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a : Fin N) (k₀ : K) (ca cb : Fin N) (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ e) (pr : RW.X → Rb.X) (ψ : RW.X → OpenPartialHomeomorph RW.X (Fin e → ℂ)) (kb : RW.X → Fin Rb.A.n) (σ : RW.X → Fin n ↪ Fin e) (i₀ : RW.X → Fin e) (V : RW.X → Set RW.X) (u : RW.X → RW.X → ℂ) (hL : ∀ x, IsLocSec M Rb τ a k₀ ca cb RW pr x (ψ x) (kb x) (σ x) (i₀ x) (V x) (u x)), ∀ c : ℝ, IsSNC RW.A (secPot RW (potA M τ a k₀) V (fun x => (hL x).2.1) (fun x => (hL x).2.2.1) c) (diagSec ψ i₀ u) ![1] ![diagSet k₀ RW] := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.diagSec_isSNC_diagSet | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.diagSec_isSNC_diagSet | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.diagSec_isSNC_diagSet <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.TwistedChartHolomorphicStatement
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.secPot_isPotential : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n e : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a : Fin N) (k₀ : K) (ca cb : Fin N) (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ e) (pr : RW.X → Rb.X) (ψ : RW.X → OpenPartialHomeomorph RW.X (Fin e → ℂ)) (kb : RW.X → Fin Rb.A.n) (σ : RW.X → Fin n ↪ Fin e) (i₀ : RW.X → Fin e) (V : RW.X → Set RW.X) (u : RW.X → RW.X → ℂ) (hL : ∀ x, IsLocSec M Rb τ a k₀ ca cb RW pr x (ψ x) (kb x) (σ x) (i₀ x) (V x) (u x)), ∀ c : ℝ, IsPotential RW.A (secPot RW (potA M τ a k₀) V (fun x => (hL x).2.1) (fun x => (hL x).2.2.1) c) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.isPotential_secPot | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.isPotential_secPot | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.isPotential_secPot <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.TwistedChartTransitionAnalyticStatement
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_chart_transition_analytic : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n e : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a : Fin N) (k₀ : K) (ca cb : Fin N) (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ e) (pr : RW.X → Rb.X) (x x' : RW.X) (ψ ψ' : OpenPartialHomeomorph RW.X (Fin e → ℂ)) (kb kb' : Fin Rb.A.n) (σ σ' : Fin n ↪ Fin e) (i₀ i₀' : Fin e) (V V' : Set RW.X) (u u' : RW.X → ℂ), M.blk (τ, a) = some k₀ → IsWAtlas M Rb τ a k₀ ca cb RW pr → IsLocSec M Rb τ a k₀ ca cb RW pr x ψ kb σ i₀ V u → IsLocSec M Rb τ a k₀ ca cb RW pr x' ψ' kb' σ' i₀' V' u' → ∀ w ∈ V ∩ V', ‖u w * ψ w i₀‖ / (potA M τ a k₀).h (RW.lift x w) = ‖u' w * ψ' w i₀'‖ / (potA M τ a k₀).h (RW.lift x' w) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.locSec_norm_eq | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.locSec_norm_eq | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.locSec_norm_eq <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.TwistedMetricLogFormulaStatement
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_metric_log_formula : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (τ : Ψ) (a : Fin N) (k₀ : K), M.blk (τ, a) = some k₀ → ∀ zz : (Σ o : Option K, ι (o.getD k₀)) → ℂ, (∀ o, ∃ i, zz ⟨o, i⟩ ≠ 0) → Real.log ((potA M τ a k₀).h zz) = -(1 / 2) * ∑ p, (xiCoef τ a p : ℝ) * (Real.log ((fsHerm ι (M.dy p)).h (fstPt k₀ zz)) + Real.log ((fsHerm ι (M.dy p)).h (sndPt k₀ zz))) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.log_potA | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.log_potA | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.log_potA <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.TwoPointFibreChartSeventh
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

theorem fibre_base_member : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d) (τ : Ψ) (a b ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ∀ (X : Type) (q : Fin 2 → X → FA.S.X) (Un : Set (Fin d → ℂ)) (Gn : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (ΦYn : (Fin (d + 1) → ℂ) → FA.S.X) (ΦWn : (Fin (d + 2) → ℂ) → X) (l : Fin BM.q) (H : Ψ → (Fin d → ℂ) → Matrix (Fin N) (Fin N) ℂ) (bp : (Fin d → ℂ) → BM.Rb.X), IsOpen Un → IsFibreData FA τ a ca cb q Un Gn ΦYn ΦWn l H bp → ∀ p, p ≠ (τ, a) → ∀ z : Fin (d + 1) → ℂ, Fin.tail z ∈ Un → ∃ Hh : (Fin (d + 1) → ℂ) → ℂ, AnalyticAt ℂ Hh z ∧ ∀ᶠ z' in 𝓝 z, ((FA.S.comap some).potH p).φ (ΦYn z) (ΦYn z') = alphaOf BM l H bp p (Fin.tail z') + (Hh z').re := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d BM FA τ a b ca cb hb hst hca hcb X q Un Gn ΦYn ΦWn l H bp hU hD p hp z hz
  obtain ⟨Hh, hHh, hev⟩ := GlobalTheory.T.two_point_fibre_chart_fifth K ι Φ y Ψ N j M n d BM FA τ a b ca cb hb hst hca hcb X q Un Gn
    ΦYn ΦWn l H bp hU hD p z hz
  refine ⟨Hh, hHh, ?_⟩
  filter_upwards [hev] with z' h
  rw [h]
  congr 1
  unfold alphaOf potAt
  congr 1
  by_cases hτ : p.1 = τ
  · have hpa : p.2 ≠ a := fun e => hp (Prod.ext hτ e)
    have hs := (GlobalTheory.T.elementary_factor_properties N j a b ca cb (z' 0) M.j_le hb hst hca hcb).2.2.2
      (BM.G l p.1 (bp (Fin.tail z'))) (H τ (Fin.tail z')) p.2 hpa
    simp only [flagAt, if_pos hτ]
    rw [hs, hτ]
  · simp only [flagAt, if_neg hτ]

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.TwoPointFibreChartSixth
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

theorem analyticAt_fin_tail {d : ℕ} (z : Fin (d + 1) → ℂ) :
    AnalyticAt ℂ (Fin.tail : (Fin (d + 1) → ℂ) → Fin d → ℂ) z := by
  have : (Fin.tail : (Fin (d + 1) → ℂ) → Fin d → ℂ) =
      ⇑(ContinuousLinearMap.pi fun i : Fin d =>
        (ContinuousLinearMap.proj i.succ : (Fin (d + 1) → ℂ) →L[ℂ] ℂ)) := by
    funext u i
    rfl
  rw [this]
  exact ContinuousLinearMap.analyticAt _ z

theorem analyticAt_minorIJ {e N : ℕ} (A : (Fin e → ℂ) → Matrix (Fin N) (Fin N) ℂ) (z : Fin e → ℂ)
    (hA : ∀ r s, AnalyticAt ℂ (fun u => A u r s) z) (I J : Finset (Fin N)) :
    AnalyticAt ℂ (fun u => minorIJ (A u) I J) z := by
  unfold minorIJ
  by_cases h : I.card = J.card
  · simp only [h, dite_true, Matrix.det_apply, Matrix.submatrix_apply]
    refine Finset.analyticAt_fun_sum _ fun σ _ => ?_
    simp only [Units.smul_def, zsmul_eq_mul]
    exact analyticAt_const.mul (Finset.analyticAt_fun_prod _ fun i _ => hA _ _)
  · simp only [h, dite_false]
    exact analyticAt_const

theorem analyticAt_facOf {e N : ℕ} (j : ℕ) (a i : Fin N) (A : (Fin e → ℂ) → Matrix (Fin N) (Fin N) ℂ) (z : Fin e → ℂ)
    (hA : ∀ r s, AnalyticAt ℂ (fun u => A u r s) z) :
    AnalyticAt ℂ (fun u => facOf N j a (A u) i) z := by
  unfold facOf
  by_cases h₁ : (i : ℕ) + 1 = j
  · by_cases h₂ : (a : ℕ) < j
    · simp only [h₁, h₂, if_true]
      exact analyticAt_minorIJ A z hA _ _
    · simp only [h₁, h₂, if_true, if_false]
      exact analyticAt_const
  · simp only [h₁, if_false]
    exact analyticAt_minorIJ A z hA _ _

theorem fibre_xi_potential : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d) (τ : Ψ) (a b ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ∀ (X : Type) (q : Fin 2 → X → FA.S.X) (Un : Set (Fin d → ℂ)) (Gn : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (ΦYn : (Fin (d + 1) → ℂ) → FA.S.X) (ΦWn : (Fin (d + 2) → ℂ) → X) (l : Fin BM.q) (H : Ψ → (Fin d → ℂ) → Matrix (Fin N) (Fin N) ℂ) (bp : (Fin d → ℂ) → BM.Rb.X), IsOpen Un → IsFibreData FA τ a ca cb q Un Gn ΦYn ΦWn l H bp → ∀ z : Fin (d + 1) → ℂ, Fin.tail z ∈ Un → ∃ Hh : (Fin (d + 1) → ℂ) → ℂ, AnalyticAt ℂ Hh z ∧ ∀ᶠ z' in 𝓝 z, ∑ p, (xiCoef τ a p : ℝ) * ((FA.S.comap some).potH p).φ (ΦYn z) (ΦYn z') = xiPot (Gn (Fin.tail z')) (z' 0) + (Hh z').re := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d BM FA τ a b ca cb hb hab hca hcb X q Un Gn ΦYn ΦWn l H bp hUn hD z hz
  have hD' := hD
  obtain ⟨hH, hbc, hbk, hpt, hG, -, -⟩ := hD'
  choose Hp hPa hPe using fun p => GlobalTheory.T.two_point_fibre_chart_fifth K ι Φ y Ψ N j M n d BM FA τ a b ca cb hb hab hca hcb X q Un Gn ΦYn
    ΦWn l H bp hUn hD p z hz
  have htail : ∀ᶠ z' : Fin (d + 1) → ℂ in 𝓝 z, Fin.tail z' ∈ Un :=
    (analyticAt_fin_tail z).continuousAt.preimage_mem_nhds (hUn.mem_nhds hz)
  have hHa : ∀ τ' r s, AnalyticAt ℂ (fun u => H τ' (Fin.tail u) r s) z := fun τ' r s =>
    AnalyticAt.comp (g := fun w => H τ' w r s) (hH τ' r s _ hz) (analyticAt_fin_tail z)
  have hfac : ∀ i : Fin N, ∃ A : (Fin (d + 1) → ℂ) → ℂ, AnalyticAt ℂ A z ∧ ∀ᶠ z' in 𝓝 z,
      (if IsProperStep N j i then 0 else Real.log ‖facOf N j a (H τ (Fin.tail z')) i‖) = (A z').re := by
    intro i
    by_cases hp : IsProperStep N j i
    · exact ⟨fun _ => 0, analyticAt_const, Eventually.of_forall fun z' => by simp [hp]⟩
    · obtain ⟨A, hA, hAe⟩ := GlobalTheory.T.log_norm_nonvanishing_analytic_harmonic (d + 1) (fun u => facOf N j a (H τ (Fin.tail u)) i) z
        (analyticAt_facOf j a i (fun u => H τ (Fin.tail u)) z (hHa τ))
        (GlobalTheory.T.step_factor_ne_zero N j a i _ ((hpt _ hz).2 τ).1 ((hpt _ hz).2 τ).2)
      exact ⟨A, hA, hAe.mono fun z' h => by simpa [hp] using h⟩
  have hups : ∀ i : Fin N, ∃ A : (Fin (d + 1) → ℂ) → ℂ, AnalyticAt ℂ A z ∧ ∀ᶠ z' in 𝓝 z,
      upsLogAt BM l (τ, i) (bp (Fin.tail z')) = (A z').re := by
    intro i
    by_cases hp : M.blk (τ, i) = none
    · have hO : bp (Fin.tail z) ∈ BM.O l := (hpt _ hz).1.1
      have hreg := ((BM.good l _ hO).2.2 (τ, i) hp).2.1
      have hv := GlobalTheory.T.regular_function_analytic_on_chart (NonPluckerBlocks M.blk) (baseIdx ι M.blk) M.Ω M.x ((BM.F l).υ (τ, i)) d n BM.Rb Un bp (Fin.tail z)
        hUn hz hbc hbk hreg
      have hf : AnalyticAt ℂ (fun u => upsVal BM l (τ, i) (bp (Fin.tail u))) z :=
        AnalyticAt.comp (g := fun w => valAt M.x ((BM.F l).υ (τ, i)) (BM.Rb.lift (bp w) (bp w))) hv
          (analyticAt_fin_tail z)
      obtain ⟨A, hA, hAe⟩ := GlobalTheory.T.log_norm_nonvanishing_analytic_harmonic (d + 1) _ z hf
        (GlobalTheory.T.unipotent_value_ne_zero K ι Φ y Ψ N j M n d BM l (τ, i) _ hO hp)
      exact ⟨A, hA, hAe.mono fun z' h => by simpa [upsLogAt, hp] using h⟩
    · exact ⟨fun _ => 0, analyticAt_const, Eventually.of_forall fun z' => by simp [upsLogAt, hp]⟩
  choose Lf hLa hLe using hfac
  choose Uf hUa hUe using hups
  refine ⟨fun u => ∑ p, ((xiCoef τ a p : ℝ) : ℂ) * Hp p u -
    ∑ i, ((xiCoef τ a (τ, i) : ℝ) : ℂ) * (Lf i u + Uf i u), ?_, ?_⟩
  · refine AnalyticAt.sub (Finset.analyticAt_fun_sum _ fun p _ => analyticAt_const.mul (hPa p))
      (Finset.analyticAt_fun_sum _ fun i _ => analyticAt_const.mul ((hLa i).add (hUa i)))
  · filter_upwards [htail, eventually_all.2 hPe, eventually_all.2 hLe, eventually_all.2 hUe] with z' hw h1 h2 h3
    have hs : ∑ p, (xiCoef τ a p : ℝ) * potAt BM l p (bp (Fin.tail z')) (flagAt H τ ca cb (z' 0) (Fin.tail z') p.1) =
        xiPot (Gn (Fin.tail z')) (z' 0) - ∑ i : Fin N, (xiCoef τ a (τ, i) : ℝ) *
          ((if IsProperStep N j i then 0 else Real.log ‖facOf N j a (H τ (Fin.tail z')) i‖) +
            upsLogAt BM l (τ, i) (bp (Fin.tail z'))) :=
      GlobalTheory.T.two_by_two_minor_gram_identity Ψ N j τ a b ca cb (fun τ' => BM.G l τ' (bp (Fin.tail z'))) (fun τ' => H τ' (Fin.tail z'))
        (fun p => upsLogAt BM l p (bp (Fin.tail z'))) (z' 0) (Gn (Fin.tail z')) M.j_le hb hab hca hcb
        (BM.G_pos l τ _ (hpt _ hw).1).1 (BM.G_pos l τ _ (hpt _ hw).1).2 ((hpt _ hw).2 τ).1 ((hpt _ hw).2 τ).2
        (hG _ hw)
    have e1 : ∑ p, (xiCoef τ a p : ℝ) * ((FA.S.comap some).potH p).φ (ΦYn z) (ΦYn z') =
        ∑ p, (xiCoef τ a p : ℝ) * potAt BM l p (bp (Fin.tail z')) (flagAt H τ ca cb (z' 0) (Fin.tail z') p.1) +
          ∑ p, (xiCoef τ a p : ℝ) * (Hp p z').re := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun p _ => by rw [h1 p, mul_add]
    have e3 : ∑ i : Fin N, (xiCoef τ a (τ, i) : ℝ) *
          ((if IsProperStep N j i then 0 else Real.log ‖facOf N j a (H τ (Fin.tail z')) i‖) +
            upsLogAt BM l (τ, i) (bp (Fin.tail z'))) =
        ∑ i : Fin N, (xiCoef τ a (τ, i) : ℝ) * ((Lf i z').re + (Uf i z').re) :=
      Finset.sum_congr rfl fun i _ => by rw [h2 i, h3 i]
    rw [e1, hs, e3]
    simp only [Complex.sub_re, Complex.re_sum, Complex.re_ofReal_mul, Complex.add_re]
    ring

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.TwoPointFibreTwistedResolutionStatement
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.two_point_fibre_twisted_resolution : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d) (τ : Ψ) (a b ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ∀ (k₀ : K), M.blk (τ, a) = some k₀ → ∀ (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ (d + 2)) (q : Fin 2 → RW.X → FA.S.X), (∀ x x₀, FA.Re.π x₀ = q 0 x → SameOrbit (FA.Re.R.lift x₀ x₀) (fstPt k₀ (RW.lift x x))) → (∀ x x₀, FA.Re.π x₀ = q 1 x → SameOrbit (FA.Re.R.lift x₀ x₀) (sndPt k₀ (RW.lift x x))) → ∀ f : RW.X → ℝ, IsNormFn M τ a k₀ ca cb RW f → ∀ (Un : Set (Fin d → ℂ)) (Gn : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (ΦYn : (Fin (d + 1) → ℂ) → FA.S.X) (ΦWn : (Fin (d + 2) → ℂ) → RW.X) (l : Fin BM.q) (H : Ψ → (Fin d → ℂ) → Matrix (Fin N) (Fin N) ℂ) (bp : (Fin d → ℂ) → BM.Rb.X), IsOpen Un → IsFibreData FA τ a ca cb q Un Gn ΦYn ΦWn l H bp → ∀ z : Fin (d + 2) → ℂ, Fin.tail (Fin.tail z) ∈ Un → z 0 ≠ z 1 → f (ΦWn z) + (1 / 2) * ∑ p, (xiCoef τ a p : ℝ) * ((FA.S.comap some).ph p (q 0 (ΦWn z)) + (FA.S.comap some).ph p (q 1 (ΦWn z))) = logSin (Gn (Fin.tail (Fin.tail z))) (z 0) (z 1) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.NormFib.logNorm_add_weights_eq_logSin | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.NormFib.logNorm_add_weights_eq_logSin | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.NormFib.logNorm_add_weights_eq_logSin <;> assumption)
end

