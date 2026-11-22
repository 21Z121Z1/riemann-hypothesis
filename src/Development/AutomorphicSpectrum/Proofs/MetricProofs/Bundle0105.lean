import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0079
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SpecializesOfUnits
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0096
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0099
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0100
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ColFlags
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0026
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsChartOfLineBundle
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0007
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0005
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0004
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import GroundTheory.HeightsAndTheta.Heights.Regularisation.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0007
import Development.WeilBound.CoreStatements.PlurisubharmonicCones.Bundle0009
import ReciprocityTheory.AnalyticForms.LeviForms.ConvExpandStatement
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0014
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Objects
import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeCptFrameChangeRegular
section
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm

section Pure

variable {Ψ : Type} [Fintype Ψ] {p q : ℕ} {Ω : Type} [Field Ω] {n : Ψ ⊕ Ψ → ℕ}
  {K₀ : Type} [Fintype K₀] {J₀ : K₀ → Type} [∀ k, Fintype (J₀ k)]

theorem aExt_mem (R : Subring Ω) (C : ∀ s, Matrix (Fin (n s)) (Fin (rk Ψ p q s)) Ω)
    (hC : ∀ s j l, C s j l ∈ R) (s : Ψ ⊕ Ψ) (j : Fin (n s)) (a : Fin (p + q)) : aExt C s j a ∈ R := by
  refine R.sum_mem fun l _ => ?_
  split_ifs
  · exact hC _ _ _
  · exact R.zero_mem

theorem coefF_mem (R : Subring Ω) (C : ∀ s, Matrix (Fin (n s)) (Fin (rk Ψ p q s)) Ω)
    (hC : ∀ s j l, C s j l ∈ R) (r : Σ k, idx (p := p) (q := q) J₀ n k) (I : Finset (Fin (p + q))) :
    coefF C r I ∈ R := by
  obtain ⟨k | t, i⟩ := r
  · exact R.zero_mem
  · show (if e : I.card = (t.2 : ℕ) + 1 then _ else 0) ∈ R
    split_ifs with e
    · refine det_mem_subring R _ fun a b => ?_
      exact aExt_mem R C hC t.1 _ _
    · exact R.zero_mem

theorem sMin_mem (R : Subring Ω) (B : ∀ s, Matrix (Fin (rk Ψ p q s)) (Fin (n s)) Ω)
    (hB : ∀ s l j, B s l j ∈ R) (t : StepIx Ψ p q) (I : Finset (Fin (p + q)))
    (J : Fin ((t.2 : ℕ) + 1) → Fin (n t.1)) : sMin B t I J ∈ R := by
  unfold sMin bMin
  split_ifs with e1 e2
  · refine det_mem_subring R _ fun a b => ?_
    simp only [Matrix.submatrix_apply, bExt]
    refine R.sum_mem fun l _ => ?_
    split_ifs
    · exact hB _ _ _
    · exact R.zero_mem
  · exact R.zero_mem
  · exact R.zero_mem

theorem frames_pure (A : ∀ s, Matrix (Fin (n s)) (Fin (rk Ψ p q s)) Ω) (x₀ : (Σ k, J₀ k) → Ω) (m : Ψ ⊕ Ψ → ℕ)
    (R : Subring Ω)
    (c : ∀ k : NonPluckerBlocks (blkF Ψ p q K₀), baseIdx (idx (p := p) (q := q) J₀ n) (blkF Ψ p q K₀) k)
    (hc0 : ∀ k, xb A x₀ ⟨k, c k⟩ ≠ 0) (hrat : ∀ k i, xb A x₀ ⟨k, i⟩ / xb A x₀ ⟨k, c k⟩ ∈ R)
    (Ts : ∀ s, Matrix (Fin (rk Ψ p q s)) (Fin (rk Ψ p q s)) Ω) (C : ∀ s, Matrix (Fin (n s)) (Fin (rk Ψ p q s)) Ω)
    (B : ∀ s, Matrix (Fin (rk Ψ p q s)) (Fin (n s)) Ω) (hT : ∀ s, (Ts s).det ≠ 0)
    (hAT : ∀ s, A s * Ts s = (xcOf x₀ c ^ m s) • C s) (hBC : ∀ s, B s * C s = 1)
    (hC : ∀ s j l, C s j l ∈ R) (hB : ∀ s l j, B s l j ∈ R) :
    ∃ F : FrameData (idx (p := p) (q := q) J₀ n) Ψ (p + q) Ω (blkF Ψ p q K₀), F.c = c ∧
      ((∀ τ, IsBlockDiag p (F.T τ) ∧ (F.T τ).det ≠ 0) ∧
      (∀ r k, blkF Ψ p q K₀ r = some k → ∀ (i : idx J₀ n k) (h : Matrix (Fin (p + q)) (Fin (p + q)) Ω),
        IsBlockDiag p h →
        detFac p r.2 (F.T r.1) * ∑ I, coefF A ⟨k, i⟩ I * minorIJ (F.T r.1 * h) I (stepCols (p + q) p r.2) =
          (∏ k', xb A x₀ ⟨k', F.c k'⟩ ^ bF m r k') * ∑ I, F.u ⟨k, i⟩ I * minorIJ h I (stepCols (p + q) p r.2)) ∧
      (∀ r k, blkF Ψ p q K₀ r = some k → ∀ I I', IsStepRows (p + q) p r.2 I → IsStepRows (p + q) p r.2 I' →
        ∑ i : idx J₀ n k, F.u' I ⟨k, i⟩ * F.u ⟨k, i⟩ I' = if I = I' then 1 else 0) ∧
      ∀ r, blkF Ψ p q K₀ r = none →
        detFac p r.2 (F.T r.1) * 1 = (∏ k', xb A x₀ ⟨k', F.c k'⟩ ^ bF m r k') * F.υ r) ∧
      (∀ r I, F.u r I ∈ R ∧ F.u' I r ∈ R) ∧
      ∀ r, blkF Ψ p q K₀ r = none → F.υ r ≠ 0 ∧ F.υ r ∈ R ∧ (F.υ r)⁻¹ ∈ R := by
  classical
  have hx : xcOf x₀ c ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => hc0 (baseInl k)
  have hz : ∀ s, zOf A c s ≠ 0 := fun s => by
    by_cases h : 0 < rk Ψ p q s
    · rw [← xb_rowsOf A x₀ c s h]
      exact hc0 _
    · have h0 : rk Ψ p q s = 0 := by omega
      have : IsEmpty (Fin (rk Ψ p q s)) := by rw [h0]; exact Fin.isEmpty
      simp [zOf, Matrix.det_isEmpty]
  have hr : ∀ s (J : Fin (rk Ψ p q s) → Fin (n s)), ((A s).submatrix J id).det / zOf A c s ∈ R := fun s J => by
    by_cases h : 0 < rk Ψ p q s
    · rw [← xb_rowsOf A x₀ c s h, ← xb_full A x₀ s h J]
      exact hrat _ _
    · have h0 : rk Ψ p q s = 0 := by omega
      have : IsEmpty (Fin (rk Ψ p q s)) := by rw [h0]; exact Fin.isEmpty
      simp [zOf, Matrix.det_isEmpty]
  let υs : Ψ ⊕ Ψ → Ω := fun s => ((C s).submatrix (rowsOf c s) id).det
  have hu : ∀ s, υs s ≠ 0 ∧ υs s ∈ R ∧ (υs s)⁻¹ ∈ R ∧
      zOf A c s * (Ts s).det = (xcOf x₀ c ^ m s) ^ rk Ψ p q s * υs s := fun s =>
    GlobalTheory.T.minor_ratio_regular_of_matrix_identity R (A s) (C s) (B s) (Ts s) _ (hAT s) (pow_ne_zero _ hx) (hT s) (hBC s) (hC s) (hB s) (rowsOf c s)
      (hz s) (hr s)
  have hW : ∀ s, (Ts s).det = (xcOf x₀ c ^ m s) ^ rk Ψ p q s * υs s * (zOf A c s)⁻¹ := fun s => by
    have := (hu s).2.2.2
    have h' := hz s
    field_simp
    linear_combination this
  let wt : StepIx Ψ p q → Ω := fun t => Sum.elim (fun _ => 1) (fun τ => υs (.inl τ)) t.1
  have hwt : ∀ t, wt t ≠ 0 ∧ wt t ∈ R ∧ (wt t)⁻¹ ∈ R := fun t => by
    obtain ⟨s | s, a⟩ := t
    · simp [wt, R.one_mem]
    · exact ⟨(hu _).1, (hu _).2.1, (hu _).2.2.1⟩
  let F : FrameData (idx (p := p) (q := q) J₀ n) Ψ (p + q) Ω (blkF Ψ p q K₀) :=
    { c := c
      T := tMat Ts
      u := fun r I => match r with
        | ⟨.inl _, _⟩ => 0
        | ⟨.inr t, J⟩ => wt t * cMin C t J I
      u' := fun I r => match r with
        | ⟨.inl _, _⟩ => 0
        | ⟨.inr t, J⟩ => (wt t)⁻¹ * sMin B t I J
      υ := fun r => (if p ≤ (r.2 : ℕ) + 1 then υs (.inl r.1) else 1) *
        (if (r.2 : ℕ) + 1 = p + q then υs (.inr r.1) else 1) }
  refine ⟨F, rfl, ⟨fun τ => ?_, fun r k hk i h hh => ?_, fun r k hk I I' hI hI' => ?_, fun r hr' => ?_⟩,
    fun r I => ⟨?_, ?_⟩, fun r hr' => ?_⟩
  · obtain ⟨h1, h2, -⟩ := GlobalTheory.T.tMat_blockDiag_det_factors Ts τ
    exact ⟨h1, by show (tMat Ts τ).det ≠ 0; rw [h2]; exact mul_ne_zero (hT _) (hT _)⟩
  · obtain ⟨hp, rfl⟩ : IsProperStep (p + q) p r.2 ∧ k = .inr (stepOf Ψ p q r) := by
      unfold blkF at hk
      split_ifs at hk with hp
      exact ⟨hp, (Option.some.inj hk).symm⟩
    have e1 := GlobalTheory.T.minor_expansion_of_scaled_product A C Ts (xcOf x₀ c) m hAT r.1 (stepOf Ψ p q r) (BlockEmbeddings.stepOf_fst r) i h
      (stepCols (p + q) p r.2) (card_stepCols r)
    have key : detFac p r.2 (tMat Ts r.1) * xcOf x₀ c ^ (m (stepOf Ψ p q r).1 * (((stepOf Ψ p q r).2 : ℕ) + 1)) =
        (∏ k', xb A x₀ ⟨k', c k'⟩ ^ bF m r k') * wt (stepOf Ψ p q r) := by
      rw [GlobalTheory.T.prod_xb_pow_eq_xcOf_pow, (GlobalTheory.T.tMat_blockDiag_det_factors Ts r.1).2.2]
      have hr2 := r.2.2
      obtain ⟨hp1, hp2⟩ := hp
      by_cases hi : (r.2 : ℕ) < p
      · have e : stepOf Ψ p q r = ⟨.inl r.1, ⟨r.2, hi⟩⟩ := dif_pos hi
        have w1 : rkW r.2 = (r.2 : ℕ) + 1 := by simp only [rkW]; omega
        have w2 : rkO r.2 = 0 := by simp only [rkO]; omega
        have hn : ¬ p ≤ (r.2 : ℕ) + 1 := by omega
        rw [e, w1, w2]
        simp only [if_neg hn, if_neg hp2]
        simp [wt, mul_comm]
      · have e : stepOf Ψ p q r = ⟨.inr r.1, ⟨r.2 - p, by show _ < q; omega⟩⟩ := dif_neg hi
        have w1 : rkW r.2 = p := by simp only [rkW]; omega
        have w2 : rkO r.2 = (r.2 : ℕ) - p + 1 := by simp only [rkO]; omega
        have hy : p ≤ (r.2 : ℕ) + 1 := by omega
        have h3 : (Ts (.inl r.1)).det = (xcOf x₀ c ^ m (.inl r.1)) ^ p * υs (.inl r.1) * (zOf A c (.inl r.1))⁻¹ :=
          hW _
        rw [e, w1, w2]
        simp only [if_pos hy, if_neg hp2]
        simp only [wt, Sum.elim_inr, mul_one]
        rw [h3]
        ring
    show detFac p r.2 (tMat Ts r.1) * ∑ I, cMin A (stepOf Ψ p q r) i I * minorIJ (tMat Ts r.1 * h) I _ =
      (∏ k', xb A x₀ ⟨k', c k'⟩ ^ bF m r k') *
        ∑ I, (wt (stepOf Ψ p q r) * cMin C (stepOf Ψ p q r) i I) * minorIJ h I _
    rw [e1]
    simp only [mul_assoc, ← Finset.mul_sum]
    rw [← mul_assoc, key, mul_assoc]
  · obtain ⟨hp, rfl⟩ : IsProperStep (p + q) p r.2 ∧ k = .inr (stepOf Ψ p q r) := by
      unfold blkF at hk
      split_ifs at hk with hp
      exact ⟨hp, (Option.some.inj hk).symm⟩
    have e2 := GlobalTheory.T.cauchyBinet_sum_positioned_minors C B hBC (stepOf Ψ p q r) I I' (hI.1.trans (card_stepCols r)) (hI'.1.trans (card_stepCols r))
      (stepRows_pos r hI) (stepRows_pos r hI')
    have hw := (hwt (stepOf Ψ p q r)).1
    refine Eq.trans ?_ e2
    refine Finset.sum_congr rfl fun J _ => ?_
    show ((wt _)⁻¹ * sMin B _ I J) * (wt _ * cMin C _ J I') = _
    field_simp
  · have hnp : ¬ IsProperStep (p + q) p r.2 := fun hp => by
      unfold blkF at hr'
      rw [if_pos hp] at hr'
      simp at hr'
    have hr2 := r.2.2
    have hpi : p ≤ (r.2 : ℕ) + 1 := by
      by_contra h'
      exact hnp ⟨by omega, by omega⟩
    show detFac p r.2 (tMat Ts r.1) * 1 = (∏ k', xb A x₀ ⟨k', c k'⟩ ^ bF m r k') *
      ((if p ≤ (r.2 : ℕ) + 1 then υs (.inl r.1) else 1) * (if (r.2 : ℕ) + 1 = p + q then υs (.inr r.1) else 1))
    rw [GlobalTheory.T.prod_xb_pow_eq_xcOf_pow, (GlobalTheory.T.tMat_blockDiag_det_factors Ts r.1).2.2]
    simp only [if_pos hpi]
    have h3 : (Ts (.inl r.1)).det = (xcOf x₀ c ^ m (.inl r.1)) ^ p * υs (.inl r.1) * (zOf A c (.inl r.1))⁻¹ := hW _
    have h4 : (Ts (.inr r.1)).det = (xcOf x₀ c ^ m (.inr r.1)) ^ q * υs (.inr r.1) * (zOf A c (.inr r.1))⁻¹ := hW _
    have w1 : rkW r.2 = p := by simp only [rkW]; omega
    by_cases hN : (r.2 : ℕ) + 1 = p + q
    · have w2 : rkO r.2 = q := by simp only [rkO]; omega
      simp only [if_pos hN]
      rw [w1, w2, h3, h4]
      ring
    · have w2 : rkO r.2 = 0 := by
        have : (r.2 : ℕ) + 1 = p := by
          by_contra h'
          exact hnp ⟨h', hN⟩
        simp only [rkO]; omega
      simp only [if_neg hN]
      rw [w1, w2, h3]
      ring
  · obtain ⟨k | t, J⟩ := r
    · exact R.zero_mem
    · exact R.mul_mem (hwt t).2.1 (coefF_mem R C hC ⟨.inr t, J⟩ I)
  · obtain ⟨k | t, J⟩ := r
    · exact R.zero_mem
    · exact R.mul_mem (hwt t).2.2 (sMin_mem R B hB t I J)
  · have hnp : ¬ IsProperStep (p + q) p r.2 := fun hp => by
      unfold blkF at hr'
      rw [if_pos hp] at hr'
      simp at hr'
    show ((if p ≤ (r.2 : ℕ) + 1 then υs (.inl r.1) else 1) * (if (r.2 : ℕ) + 1 = p + q then υs (.inr r.1) else 1)) ≠ 0 ∧
      ((if p ≤ (r.2 : ℕ) + 1 then υs (.inl r.1) else 1) * (if (r.2 : ℕ) + 1 = p + q then υs (.inr r.1) else 1)) ∈ R ∧
      ((if p ≤ (r.2 : ℕ) + 1 then υs (.inl r.1) else 1) * (if (r.2 : ℕ) + 1 = p + q then υs (.inr r.1) else 1))⁻¹ ∈ R
    have g : ∀ (P : Prop) [Decidable P] (s : Ψ ⊕ Ψ), (if P then υs s else 1) ≠ 0 ∧ (if P then υs s else 1) ∈ R ∧
        (if P then υs s else 1)⁻¹ ∈ R := fun P _ s => by
      split_ifs
      · exact ⟨(hu s).1, (hu s).2.1, (hu s).2.2.1⟩
      · simp [R.one_mem]
    obtain ⟨a1, a2, a3⟩ := g (p ≤ (r.2 : ℕ) + 1) (.inl r.1)
    obtain ⟨b1, b2, b3⟩ := g ((r.2 : ℕ) + 1 = p + q) (.inr r.1)
    refine ⟨mul_ne_zero a1 b1, R.mul_mem a2 b2, ?_⟩
    rw [mul_inv]
    exact R.mul_mem a3 b3

end Pure

end GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm

namespace GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm

theorem frames_main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K₀ : Type) [Fintype K₀] (J₀ : K₀ → Type) [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω) (𝔐 : HodgeCpt Y S x₀) (bW : WBases 𝔐) (bO : OmBases 𝔐) (n m : CMType H ⊕ CMType H → ℕ) (φ : ∀ s, Fin (n s) → Module.Dual Ω (EE 𝔐)), FormsOK 𝔐 bW bO m φ → CoordTie ℤ 𝔐.ξ (seg (xb (p := D.p) (q := D.q) (aOf 𝔐 bW bO φ) x₀)) → FramesOK (aOf 𝔐 bW bO φ) x₀ m := by
  intro E _ _ _ H D l Xo c Y S Ω _ _ K₀ _ J₀ _ x₀ 𝔐 bW bO n m φ hF tie Q hQ hrel hle
  classical
  choose cb hcb using hrel
  obtain ⟨P, hP, hreg⟩ := GlobalTheory.T.exists_component_in_chart_regular _ tie Q hQ hle cb hcb
  have hc0 := TiePrimes.ne_of_seg hP.1
  have hrat : ∀ k i, xb (aOf 𝔐 bW bO φ) x₀ ⟨k, i⟩ / xb (aOf 𝔐 bW bO φ) x₀ ⟨k, cb k⟩ ∈ regAt 𝔐.ξ P :=
    fun k i => TiePrimes.ratio_mem hP ⟨k, i⟩
  have hin : InChart 𝔐.ξ (seg x₀) (fun k => cb (baseInl k)) P := by
    refine ⟨Finset.prod_ne_zero_iff.2 fun k _ => hc0 (baseInl k), fun c' => ?_⟩
    rw [← Finset.prod_div_distrib]
    exact prod_mem fun k _ => hrat (baseInl k) (c' k)
  choose Ts C B hT hAT hBC hC hB using fun s =>
    GlobalTheory.T.local_frame_of_twist_generation 𝔐.ξ (seg x₀) (LL 𝔐 s) (m s) (n s) (rk (CMType H) D.p D.q s) (VV 𝔐 s) (φ s) (cc 𝔐 bW bO s)
      (hF.1 s) (hF.2.1 s).1 (hF.2.1 s).2 (hF.2.2.1 s) P _ hin
  obtain ⟨F, rfl, h1, h2, h3⟩ := frames_pure (aOf 𝔐 bW bO φ) x₀ m (regAt 𝔐.ξ P) cb hc0 hrat Ts C B hT hAT hBC hC hB
  exact ⟨F, h1, hcb, fun r I => ⟨hreg _ (h2 r I).1, hreg _ (h2 r I).2⟩,
    fun r hr => ⟨(h3 r hr).1, hreg _ (h3 r hr).2.1, hreg _ (h3 r hr).2.2⟩⟩

end GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeCptFrameHeightFormula
section
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.FMX.Roots

section Units

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {p : Cpt ξ}

theorem unit_mul {a b : Ω} (ha : unitAt ξ p a) (hb : unitAt ξ p b) : unitAt ξ p (a * b) :=
  ⟨mul_ne_zero ha.1 hb.1, mul_mem ha.2.1 hb.2.1, by rw [mul_inv]; exact mul_mem ha.2.2 hb.2.2⟩

theorem unit_inv {a : Ω} (ha : unitAt ξ p a) : unitAt ξ p a⁻¹ :=
  ⟨inv_ne_zero ha.1, ha.2.2, by rw [inv_inv]; exact ha.2.1⟩

theorem unit_pow {a : Ω} (ha : unitAt ξ p a) (n : ℕ) : unitAt ξ p (a ^ n) :=
  ⟨pow_ne_zero _ ha.1, pow_mem ha.2.1 _, by rw [← inv_pow]; exact pow_mem ha.2.2 _⟩

theorem span_eq_of_unit {a b : Ω} (h : unitAt ξ p (a / b)) :
    Submodule.span (regAt ξ p) {a} = Submodule.span (regAt ξ p) {b} := by
  have hb : b ≠ 0 := fun hb => h.1 (by rw [hb, div_zero])
  have ha : a ≠ 0 := fun ha => h.1 (by rw [ha, zero_div])
  apply le_antisymm
  · refine (Submodule.span_singleton_le_iff_mem _ _).2 (Submodule.mem_span_singleton.2 ⟨⟨a / b, h.2.1⟩, ?_⟩)
    show a / b * b = a
    field_simp
  · refine (Submodule.span_singleton_le_iff_mem _ _).2 (Submodule.mem_span_singleton.2 ⟨⟨(a / b)⁻¹, h.2.2⟩, ?_⟩)
    show (a / b)⁻¹ * a = b
    field_simp

theorem chart_block {K : Type} [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω} {c : ∀ k, J k}
    (hc : InChart ξ (seg y) c p) :
    (∀ k, y ⟨k, c k⟩ ≠ 0) ∧ ∀ k i, y ⟨k, i⟩ / y ⟨k, c k⟩ ∈ regAt ξ p := by
  classical
  have h1 : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => Finset.prod_ne_zero_iff.1 hc.1 k (Finset.mem_univ k)
  refine ⟨h1, fun k i => ?_⟩
  convert hc.2 (Function.update c k i) using 1
  rw [← Finset.prod_div_distrib, Finset.prod_eq_single k]
  · simp
  · intro k' _ hk
    rw [Function.update_of_ne hk, div_self (h1 k')]
  · simp

theorem step_unit {n r : ℕ} {Fm : Matrix (Fin n) (Fin r) Ω} {U : Matrix (Fin r) (Fin r) Ω}
    {C : Matrix (Fin r) (Fin n) Ω} {Z Xb Xc : Ω} {mm : ℕ} (hZ : Z = Xc ^ mm) (hU : U.BlockTriangular id)
    (hB : ∀ a b, (Fm * U) a b / Z ∈ regAt ξ p) (hC : ∀ a b, C a b ∈ regAt ξ p)
    (hL : ∀ a b, ∑ k, C a k * ((Fm * U) k b / Z) = if a = b then 1 else 0) (hX : unitAt ξ p (Xb / Xc)) (t : Fin r)
    (J₀ : Fin ((t : ℕ) + 1) → Fin n) (hne : (Fm.submatrix J₀ (Fin.castLE t.2)).det ≠ 0)
    (hr : ∀ J : Fin ((t : ℕ) + 1) → Fin n,
      (Fm.submatrix J (Fin.castLE t.2)).det / (Fm.submatrix J₀ (Fin.castLE t.2)).det ∈ regAt ξ p) :
    unitAt ξ p ((∏ l : Fin ((t : ℕ) + 1), U (Fin.castLE t.2 l) (Fin.castLE t.2 l)) *
      (Fm.submatrix J₀ (Fin.castLE t.2)).det / Xb ^ (((t : ℕ) + 1) * mm)) := by
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.T.minor_ratio_regular_of_inverse Ω (regAt ξ p) n r Fm U C Z hU hB hC hL ((t : ℕ) + 1) t.2 J₀ hne hr
  have hw : unitAt ξ p _ := ⟨h3, h1, h2⟩
  have hb : Xb ≠ 0 := fun hb => hX.1 (by rw [hb, zero_div])
  have hc : Xc ≠ 0 := fun hb => hX.1 (by rw [hb, div_zero])
  have e := unit_mul hw (unit_inv (unit_pow hX (((t : ℕ) + 1) * mm)))
  convert e using 1
  rw [hZ, div_pow, ← pow_mul, mul_comm mm]
  field_simp

end Units

theorem rootLat_gen {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
    {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Finset ℕ}
    {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω} {𝔐 : HodgeCpt Y S y}
    (Fl : 𝔐.Flag) (r : CMType H × Fin (D.p + D.q)) (p : Cpt 𝔐.ξ) {q : Σ s, Fin (labelRk D s)}
    (hq : HodgeCpt.rootIdx D r = q) {t : Ω} (ht : ((𝔐.V q.1).gr (Fl.b q.1) q.2).IsGenAt p t) :
    Fl.rootLat r p = Submodule.span (regAt 𝔐.ξ p) {t ^ HodgeCpt.rootSgn D r} := by
  subst hq
  have := GlobalTheory.CompanionTheory.Ar.Flag.tens_gen (fun _ : Unit => (𝔐.V (HodgeCpt.rootIdx D r).1).gr (Fl.b (HodgeCpt.rootIdx D r).1) (HodgeCpt.rootIdx D r).2)
    (fun _ => HodgeCpt.rootSgn D r) p (fun _ => t) fun _ => ht
  simpa [HodgeCpt.Flag.rootLat] using this.2

theorem point_gen {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
    {Xo : Moduli D l} {c : Coeff l} {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)} {S : Finset ℕ}
    {Ω : Type} [Field Ω] [CharZero Ω] {K₀ : Type} [Fintype K₀] {J₀ : K₀ → Type} [∀ k, Fintype (J₀ k)]
    {x₀ : (Σ k, J₀ k) → Ω} {𝔐 : HodgeCpt Y S x₀} {bW : WBases 𝔐} {bO : OmBases 𝔐}
    {n m : CMType H ⊕ CMType H → ℕ} {φ : ∀ s, Fin (n s) → Module.Dual Ω (EE 𝔐)}
    (hF : FormsOK 𝔐 bW bO m φ) (h : ModelOK (aOf 𝔐 bW bO φ) x₀ m)
    {𝔐' : HodgeCpt Y S (yv (p := D.p) (q := D.q) (aOf 𝔐 bW bO φ) x₀)} {pr : 𝔐'.X ⟶ 𝔐.X} {j : 𝔐.Li →+ 𝔐'.Li}
    {Fl : 𝔐'.Flag} (hO : HodgeOver 𝔐' 𝔐 pr (algebraMap Ω (GenField Ω (rk (CMType H) D.p D.q))) j)
    (hV : ∀ s, 𝔐'.V s = (𝔐.V s).pull 𝔐'.ξ pr j) (hC : ColFlags 𝔐 bW bO j Fl)
    (τ : CMType H) (i : Fin (D.p + D.q)) (p' : Cpt 𝔐'.ξ) (cc : ∀ k, idx (p := D.p) (q := D.q) J₀ n k)
    (hc : InChart 𝔐'.ξ (seg (yv (p := D.p) (q := D.q) (aOf 𝔐 bW bO φ) x₀)) cc p') :
    Fl.rootLat (τ, i) p' = Submodule.span (regAt 𝔐'.ξ p')
      {(∏ k, yv (p := D.p) (q := D.q) (aOf 𝔐 bW bO φ) x₀ ⟨k, cc k⟩ ^
        (if h0 : (i : ℕ) = 0 then -(model (aOf 𝔐 bW bO φ) x₀ m h).dy (τ, i)
          else (model (aOf 𝔐 bW bO φ) x₀ m h).dy (τ, ⟨(i : ℕ) - 1, by have := i.2; omega⟩) -
            (model (aOf 𝔐 bW bO φ) x₀ m h).dy (τ, i)) k)} := by
  let yc : K₀ ⊕ StepIx (CMType H) D.p D.q → (GenField Ω (rk (CMType H) D.p D.q)) := fun k => yv (p := D.p) (q := D.q) (aOf 𝔐 bW bO φ) x₀ ⟨k, cc k⟩
  obtain ⟨hY, hR⟩ := chart_block hc
  have hp : genPt 𝔐.ξ ⤳ pr p'.1 := LatModel.dominates_spec hO.1 p'
  obtain ⟨c₁, hc₁⟩ := 𝔐.tie.cover ⟨pr p'.1, hp⟩
  have hc₁' : InChart 𝔐.ξ (seg x₀) c₁ ⟨pr p'.1, hp⟩ := hc₁
  let Xb : (GenField Ω (rk (CMType H) D.p D.q)) := ∏ k, yc (.inl k)
  let Xc : (GenField Ω (rk (CMType H) D.p D.q)) := algebraMap Ω (GenField Ω (rk (CMType H) D.p D.q)) (seg x₀ c₁)
  have hXb : Xb = algebraMap Ω (GenField Ω (rk (CMType H) D.p D.q)) (seg x₀ fun k => cc (.inl k)) := by
    simp only [Xb, map_prod]; rfl
  have hXc : Xc = ∏ k, yv (p := D.p) (q := D.q) (aOf 𝔐 bW bO φ) x₀ ⟨.inl k, c₁ k⟩ := by
    simp only [Xc, map_prod]; rfl
  have hXc0 : Xc ≠ 0 := (map_ne_zero _).2 hc₁.1
  have hXb0 : Xb ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => hY _
  have hX : unitAt 𝔐'.ξ p' (Xb / Xc) := by
    refine ⟨div_ne_zero hXb0 hXc0, ?_, ?_⟩
    · rw [hXb, show Xc = algebraMap Ω (GenField Ω (rk (CMType H) D.p D.q)) (seg x₀ c₁) from rfl, ← map_div₀]
      exact LatModel.dominates_regAt hO.1 p' hp (hc₁'.2 _)
    · rw [inv_div, hXc, show Xb = ∏ k, yc (.inl k) from rfl, ← Finset.prod_div_distrib]
      exact prod_mem fun k _ => hR (.inl k) (c₁ k)
  obtain ⟨UW, CW, hUW, hBW, hCW, hLW, hGW⟩ := GlobalTheory.T.hodgeCpt_frame_twist_compat E H D l Xo c Y S Ω K₀ J₀ x₀ 𝔐 bW bO n m φ hF 𝔐' pr j Fl hO hV hC τ p' hp c₁ hc₁'
  obtain ⟨UO, CO, hUO, hBO, hCO, hLO, hGO⟩ := GlobalTheory.T.hodgeCpt_frame_twist_degree E H D l Xo c Y S Ω K₀ J₀ x₀ 𝔐 bW bO n m φ hF 𝔐' pr j Fl hO hV hC τ p' hp c₁ hc₁'
  let tW : Fin D.p → (GenField Ω (rk (CMType H) D.p D.q)) := fun l => UW l l
  let tO : Fin D.q → (GenField Ω (rk (CMType H) D.p D.q)) := fun l => UO l l
  have unitW : ∀ t : Fin D.p, unitAt 𝔐'.ξ p' ((∏ l : Fin ((t : ℕ) + 1), tW (Fin.castLE t.2 l)) *
      yc (.inr ⟨.inl τ, t⟩) / Xb ^ (((t : ℕ) + 1) * m (.inl τ))) := fun t =>
    step_unit (map_pow _ _ _) hUW hBW hCW hLW hX t (cc (.inr ⟨.inl τ, t⟩)) (hY (.inr ⟨.inl τ, t⟩))
      (hR (.inr ⟨.inl τ, t⟩))
  have unitO : ∀ t : Fin D.q, unitAt 𝔐'.ξ p' ((∏ l : Fin ((t : ℕ) + 1), tO (Fin.castLE t.2 l)) *
      yc (.inr ⟨.inr τ, t⟩) / Xb ^ (((t : ℕ) + 1) * m (.inr τ))) := fun t =>
    step_unit (map_pow _ _ _) hUO hBO hCO hLO hX t (cc (.inr ⟨.inr τ, t⟩)) (hY (.inr ⟨.inr τ, t⟩))
      (hR (.inr ⟨.inr τ, t⟩))
  let G : Fin (D.p + D.q) → (GenField Ω (rk (CMType H) D.p D.q)) := fun i =>
    if h : (i : ℕ) < D.p then tW ⟨i, h⟩ else tO ⟨(i : ℕ) - D.p, by have := i.2; omega⟩
  have hG1 : ∀ (i : Fin (D.p + D.q)) (h : (i : ℕ) < D.p), G i = tW ⟨i, h⟩ := fun i h => dif_pos h
  have hG2 : ∀ (i : Fin (D.p + D.q)) (h : D.p ≤ (i : ℕ)), G i = tO ⟨(i : ℕ) - D.p, by have := i.2; omega⟩ :=
    fun i h => dif_neg (not_lt.2 h)
  let Ee : Fin (D.p + D.q) → (GenField Ω (rk (CMType H) D.p D.q)) := fun i => ∏ k, yc k ^ (-((model (aOf 𝔐 bW bO φ) x₀ m h).dy (τ, i) k))
  have hEe : ∀ i, Ee i ≠ 0 := fun i => Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hY _)
  have hDE : ∀ i, unitAt 𝔐'.ξ p' ((∏ k ∈ Finset.Iic i, G k) / Ee i) := by
    intro i
    obtain ⟨e1, e2⟩ := GlobalTheory.T.model_monomial_weight_product (CMType H) D.p D.q Ω n (aOf 𝔐 bW bO φ) K₀ J₀ x₀ m h (GenField Ω (rk (CMType H) D.p D.q)) yc hY τ i
    obtain ⟨g1, g2⟩ := GlobalTheory.T.prod_Iic_blockDiag_det_factors (GenField Ω (rk (CMType H) D.p D.q)) D.p D.q tW tO G hG1 hG2 i
    by_cases hi : (i : ℕ) < D.p
    · have e : Ee i = _ := e1 hi
      rw [e, g1 hi]
      have := unitW ⟨i, hi⟩
      have hy : yc (.inr ⟨.inl τ, ⟨i, hi⟩⟩) ≠ 0 := hY _
      convert this using 1
      exact div_div_eq_mul_div _ _ _
    · have hi' := not_lt.1 hi
      have e : Ee i = _ := e2 hi'
      rw [e, g2 hi', div_div_eq_mul_div, pow_add, mul_mul_mul_comm, mul_div_mul_comm]
      have hl : (i : ℕ) - D.p < D.q := by have := i.2; omega
      refine unit_mul ?_ (unitO ⟨(i : ℕ) - D.p, hl⟩)
      by_cases h0 : 0 < D.p
      · rw [dif_pos h0]
        have e1 : D.p - 1 + 1 = D.p := by omega
        have := unitW ⟨D.p - 1, by omega⟩
        have eP : (∏ l : Fin (D.p - 1 + 1), tW (Fin.castLE (by omega) l)) = ∏ l, tW l :=
          Fintype.prod_equiv (finCongr e1) _ _ fun l => congrArg tW (Fin.ext rfl)
        have eX : (D.p - 1 + 1) * m (.inl τ) = D.p * m (.inl τ) := by rw [e1]
        simp only [eP, eX] at this
        exact this
      · rw [dif_neg h0]
        have hp0 : D.p = 0 := by omega
        have eX : D.p * m (.inl τ) = 0 := by rw [hp0, zero_mul]
        haveI : IsEmpty (Fin D.p) := by rw [hp0]; infer_instance
        rw [eX, pow_zero, Finset.univ_eq_empty, Finset.prod_empty, mul_one, div_one]
        exact ⟨one_ne_zero, one_mem _, by simp⟩
  have hT := GlobalTheory.T.ratio_successive_nonzero_regular (GenField Ω (rk (CMType H) D.p D.q)) (regAt 𝔐'.ξ p') _ G Ee hEe hDE i
  have hW : (∏ k, yv (p := D.p) (q := D.q) (aOf 𝔐 bW bO φ) x₀ ⟨k, cc k⟩ ^
        (if h0 : (i : ℕ) = 0 then -(model (aOf 𝔐 bW bO φ) x₀ m h).dy (τ, i)
          else (model (aOf 𝔐 bW bO φ) x₀ m h).dy (τ, ⟨(i : ℕ) - 1, by have := i.2; omega⟩) - (model (aOf 𝔐 bW bO φ) x₀ m h).dy (τ, i)) k) =
      if h0 : (i : ℕ) = 0 then Ee i else Ee i / Ee ⟨(i : ℕ) - 1, by have := i.2; omega⟩ := by
    by_cases h0 : (i : ℕ) = 0
    · simp only [dif_pos h0]
      rfl
    · simp only [dif_neg h0]
      show _ = (∏ k, yc k ^ (-((model (aOf 𝔐 bW bO φ) x₀ m h).dy (τ, i) k))) / ∏ k, yc k ^ (-((model (aOf 𝔐 bW bO φ) x₀ m h).dy (τ, ⟨(i : ℕ) - 1, by have := i.2; omega⟩) k))
      rw [← Finset.prod_div_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [Pi.sub_apply, ← zpow_sub₀ (hY k)]
      congr 1
      ring
  have hroot : Fl.rootLat (τ, i) p' = Submodule.span (regAt 𝔐'.ξ p') {G i} := by
    by_cases hi : (i : ℕ) < D.p
    · rw [rootLat_gen Fl (τ, i) p' (q := ⟨.inl τ, ⟨i, hi⟩⟩) (by simp [HodgeCpt.rootIdx, hi]) (hGW ⟨i, hi⟩),
        hG1 i hi]
      simp [HodgeCpt.rootSgn, hi]
      rfl
    · have hi' := not_lt.1 hi
      have hl : (i : ℕ) - D.p < D.q := by have := i.2; omega
      rw [rootLat_gen Fl (τ, i) p' (q := ⟨.inr τ, (⟨(i : ℕ) - D.p, hl⟩ : Fin D.q).rev⟩) (by
        simp only [HodgeCpt.rootIdx, dif_neg hi]
        congr 1
        apply Fin.ext
        simp [Fin.val_rev]
        omega) (hGO ⟨(i : ℕ) - D.p, hl⟩), hG2 i hi']
      simp [HodgeCpt.rootSgn, hi]
      rfl
  rw [hroot, hW]
  exact span_eq_of_unit hT

theorem rootLines : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K₀ : Type) [Fintype K₀] (J₀ : K₀ → Type) [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω) (𝔐 : HodgeCpt Y S x₀) (bW : WBases 𝔐) (bO : OmBases 𝔐) (n m : CMType H ⊕ CMType H → ℕ) (φ : ∀ s, Fin (n s) → Module.Dual Ω (EE 𝔐)), FormsOK 𝔐 bW bO m φ → CoordTie ℤ 𝔐.ξ (seg (xb (p := D.p) (q := D.q) (aOf 𝔐 bW bO φ) x₀)) → ∀ (h : ModelOK (aOf 𝔐 bW bO φ) x₀ m) (𝔐' : HodgeCpt Y S (yv (p := D.p) (q := D.q) (aOf 𝔐 bW bO φ) x₀)) (pr : 𝔐'.X ⟶ 𝔐.X) (j : 𝔐.Li →+ 𝔐'.Li) (Fl : 𝔐'.Flag), HodgeOver 𝔐' 𝔐 pr (algebraMap Ω (GenField Ω (rk (CMType H) D.p D.q))) j → Submodule.span (GenField Ω (rk (CMType H) D.p D.q)) (Set.range j) = ⊤ → (∀ s, 𝔐'.V s = (𝔐.V s).pull 𝔐'.ξ pr j) → ColFlags 𝔐 bW bO j Fl → ∃ xdeg : CMType H × Fin (D.p + D.q) → (K₀ ⊕ StepIx (CMType H) D.p D.q) → ℤ, Fl.RootLines xdeg (fun _ => 1) ∧ ∀ τ i, (model (aOf 𝔐 bW bO φ) x₀ m h).dy (τ, i) = -∑ k ∈ Finset.Iic i, xdeg (τ, k) := by
  intro E _ _ _ H D l Xo c Y S Ω _ _ K₀ _ J₀ _ x₀ 𝔐 bW bO n m φ hF _ h 𝔐' pr j Fl hO _ hV hC
  refine ⟨fun r => if h0 : (r.2 : ℕ) = 0 then -(model (aOf 𝔐 bW bO φ) x₀ m h).dy r
      else (model (aOf 𝔐 bW bO φ) x₀ m h).dy (r.1, ⟨(r.2 : ℕ) - 1, by have := r.2.2; omega⟩) -
        (model (aOf 𝔐 bW bO φ) x₀ m h).dy r, fun r => ⟨one_ne_zero, fun p' _ cc hc => ?_⟩, fun τ i => ?_⟩
  · obtain ⟨τ, i⟩ := r
    rw [point_gen hF h hO hV hC τ i p' cc hc, smul_eq_mul, mul_one]
  · exact GlobalTheory.T.eq_neg_sum_Iic_differences _ _ (fun i => (model (aOf 𝔐 bW bO φ) x₀ m h).dy (τ, i)) i

end GlobalTheory.CompanionTheory.Ar.PB.FMX.Roots
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeMetricFrameProperties
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.hodge_metric_frame_properties : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : Ψ → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (D : ComponentData II Ψ K J Ω W) (Hd : HodgeData D), (∀ z ∈ mcPts (mCoordIdeal D.y), Nonempty (MuFrameAt Hd z)) ∧ (∀ z ∈ D.Xo, ∀ d : MuFrameAt Hd z, 0 < d.norm ∧ (muLine Hd).h z = d.norm) ∧ LogHom D Hd.aMu (phMu Hd) ∧ ConjOff D (phMu Hd) := by
  first | exact @LevelTowerAlt.mu_frame_norm_line | exact LevelTowerAlt.mu_frame_norm_line
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.MixedEnergyRegularizationBoundStatement
section
open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixed_energy_regularization_bound : TailBoundStatement → ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X] (A : FinHolAtlas e X) (Θ L : LocPot X) (s : X → X → ℂ) {n : ℕ} (m : Fin n → ℕ) (W : Fin n → Set X), IsPotential A Θ → IsPosPot A Θ → IsPotential A L → IsSection A L s → IsSNC A L s m W → (∀ y, logNormSec L s y ≤ 0) → ∀ (th : Fin e → LocPot X) (ph : Fin e → X → ℝ) (phT : Fin e → ℝ → X → ℝ) (C₅ C t₀ : ℝ), (∀ i, IsSingWeight A L s (th i) (ph i) C₅) → (∀ i, IsRegFamily A Θ L s (th i) (ph i) (phT i) C t₀) → (∀ i, IsRegFamilyC2 A s (ph i) (phT i)) → IsFiniteMeasure (maMeasure A (fun i => th i + LocPot.ofFun (ph i) + Θ)) ∧ ∃ K : ℝ, ∀ R : ℝ, Real.exp 1 ≤ R → maMeasure A (fun i => th i + LocPot.ofFun (ph i) + Θ) (bdry s ∪ {y | R ≤ rW L s y}) ≤ ENNReal.ofReal (K * Real.log R / R) ∧ ∫⁻ y in (bdry s)ᶜ ∩ {y | R ≤ rW L s y}, ENNReal.ofReal (Real.log (rW L s y)) ∂maMeasure A (fun i => th i + LocPot.ofFun (ph i) + Θ) ≤ ENNReal.ofReal (K * Real.log R ^ 2 / R) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.limit_measure_tail | exact GlobalTheory.CompanionTheory.Ar.Giv.limit_measure_tail | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.limit_measure_tail <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.MixedEnergyUniformBoundStatement
section
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixed_energy_uniform_bound : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X) (R : GroundTheory.Heights₂.Heights.Regular.RegChartData A) (Θ : LocPot X), IsPotential A Θ → IsPosPot A Θ → ∀ (P : Fin e → LocPot X) (C : ℝ), (∀ i, IsPotential A (P i)) → ∃ CE : ℝ, ∀ f : Fin e → X → ℝ, (∀ i, A.Smooth (f i)) → (∀ i, IsPsh A (P i + LocPot.ofFun (f i))) → (∀ i, ∀ x ∈ R.Yo, |f i x| ≤ C + C * Real.log (R.r x)) → (∀ i, ∀ x ∈ R.Yo, f i x ≤ C) → GroundTheory.Heights₂.Heights.AnalyticLimit.TailLogBound A R.Yo R.r (fun i => P i + LocPot.ofFun (f i)) CE := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.tailLogProducts | exact GlobalTheory.CompanionTheory.Ar.Giv.tailLogProducts | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.tailLogProducts <;> assumption)
end

