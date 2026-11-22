import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0216
import Formalism.PeriodIntegrals.Bundle0022
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PseudoCoefficientSeparation
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.RealPlaceAnalysis.Bundle0003
import Formalism.RealPlaceAnalysis.Bundle0002
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0220
import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0032
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0010
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Formalism.LocalToGlobal.IndefiniteReal.SchurOrthogonality
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0221
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0205

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceChartFramesConjMaximalCompact
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.SplitHecke GlobalTheory.LFun.ConjPlace GlobalTheory.AdelicU GlobalTheory.LFun.SplitTie

noncomputable section
namespace GlobalTheory.SplitChartLink

theorem block_frame_conjugation_identity {G H : Type} [Group G] [Group H] (f : G →* H) (a x : G) :
    (f a)⁻¹ * f (a * x * a⁻¹) * f a = 1⁻¹ * f x * 1 := by
  simp only [map_mul, map_inv]
  group

theorem rdA_matHom_embV {D : D7} (T : HSp D) {v : HeightOneSpectrum (𝓞 D.host.F)}
    (φ : GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.SplitProj D v) (g : Gv T v) :
    Matrix.GeneralLinearGroup.map (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdA φ) (Formalism.L2.Theta.matHom T (embV T v g)) =
      splitHom D.sp.cm.sig T.gram (GlobalTheory.SplitProjChart.emb φ) g := by
  have h1 : GlobalTheory.AdelicU.matHom _ D.sp.cm.sig T.gram g =
      Formalism.UG.bc (GlobalTheory.AdelicU.compFin D.host.F D.host.E v) (Formalism.L2.Theta.matHom T (embV T v g)) := by
    have h2 := GlobalTheory.AdelicU.matHom_proj D.sp.cm.sig T.gram v (embV T v g)
    rw [GlobalTheory.AdelicU.proj_emb_self] at h2
    exact h2
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [splitHom_val, h1, GlobalTheory.SplitProjChart.splitProj_emb]
  rfl

theorem link : ∀ (D : D7) (S T : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v), IsSplit (E := D.host.E) v → ∀ e, IsSplitChart D.sp.cm.sig T.gram (frameLat T) h e → ∀ ε : AE D, Formalism.L2.NTheta.IsIdemAt ε w → ∃ φ : GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.SplitProj D v, GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.IsIdemOf φ ε ∧ (∃ BS, GlobalTheory.SplitHecke.Frame S ε (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdA φ) BS) ∧ ∃ BT, GlobalTheory.SplitHecke.Frame T ε (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdA φ) BT ∧ ∃ ψ : Fv D.host.F v ≃+* w.adicCompletion D.host.E, (∀ a, Valued.v (ψ a) = Valued.v a) ∧ qV D.host.F v = qV D.host.E w ∧ ∃ κ ∈ KGL v T.rank, ∀ x, GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.grpCo φ T BT (embV T v (e.symm x)) = κ⁻¹ * Matrix.GeneralLinearGroup.map (ψ.symm : w.adicCompletion D.host.E →+* Fv D.host.F v) x * κ := by
  intro D S T v w h hv e he ε hε
  obtain ⟨v', φ, hφ, hP⟩ := (GlobalTheory.SplitIdemDict.idem_dictionary D).1 ε w hε
  have hv' : v' = v := by
    have := ((GlobalTheory.SplitIdemDict.idem_dictionary D).2 v' φ w hP).1
    subst h
    exact HeightOneSpectrum.ext this.symm
  subst hv'
  have hE : IsCMExt D.host.F D.host.E D.sp.cm.sig := isCMExt_host D
  set τ := GlobalTheory.SplitProjChart.emb φ with hτdef
  have hφτ : splitProj τ = φ := GlobalTheory.SplitProjChart.splitProj_emb φ
  have hτ : splitPrime τ = w := ((GlobalTheory.SplitIdemDict.isProjAt_iff τ w).1 (hφτ ▸ hP)).symm
  obtain ⟨hch, -⟩ := GlobalTheory.SplitProjChart.chart_rdA D v' φ ε hφ
  have hemb : chartEmb hch = τ := AlgHom.ext fun x => by
    rw [chartEmb_apply, GlobalTheory.SplitProjChart.rdA_incA]; rfl
  have hfr : ∀ (V : HSp D) β, GlobalTheory.SplitHecke.Frame V ε (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdA φ) β ↔ IsSplitBasis τ (frameLat V) β :=
    fun V β => by rw [GlobalTheory.AdelicU.SplitFrame.frame_iff_isSplitBasis hφ.1 hch, hemb]
  set ψ := ConjPlace.complEquiv hE h hτ with hψ
  obtain ⟨⟨a, ha, hea⟩, -⟩ := he
  have hBT : IsSplitBasis τ (frameLat T) (Formalism.UG.bc (ψ.symm : w.adicCompletion D.host.E →+* Fv D.host.F v') a) := by
    rw [← ConjPlace.isFrameAt_iff hE h hτ]
    convert ha
    exact Units.ext (Matrix.ext fun i j => ψ.apply_symm_apply _)
  have := GlobalTheory.AdelicU.SelfDual.isLattice_frameLat S
  obtain ⟨BS, hBS⟩ := exists_isSplitBasis τ (frameLat S) hE
  refine ⟨φ, hφ, ⟨BS, (hfr S BS).2 hBS⟩, _, (hfr T _).2 hBT, ψ, ConjPlace.valued_complMap hE h hτ, ?_, 1, one_mem _, ?_⟩
  · rw [← hτ, GlobalTheory.LFun.SplitTie.qV_splitPrime]
  · intro x
    have h3 := hea (e.symm x)
    rw [MulEquiv.apply_symm_apply, ConjPlace.locMat_eq hE h hτ, ← hψ] at h3
    have h4 : splitHom D.sp.cm.sig T.gram τ (e.symm x) =
        Formalism.UG.bc (ψ.symm : w.adicCompletion D.host.E →+* Fv D.host.F v') (a * x * a⁻¹) := by
      have h5 : Formalism.UG.bc (ψ : Fv D.host.F v' →+* w.adicCompletion D.host.E) (splitHom D.sp.cm.sig T.gram τ (e.symm x)) =
          a * x * a⁻¹ := by
        generalize Formalism.UG.bc (ψ : Fv D.host.F v' →+* w.adicCompletion D.host.E) (splitHom D.sp.cm.sig T.gram τ (e.symm x)) = y at h3 ⊢
        subst h3
        group
      rw [← h5]
      exact Units.ext (Matrix.ext fun i j => (ψ.symm_apply_apply _).symm)
    have h6 : Formalism.UG.bc (ψ.symm : w.adicCompletion D.host.E →+* Fv D.host.F v') x =
        Matrix.GeneralLinearGroup.map (ψ.symm : w.adicCompletion D.host.E →+* Fv D.host.F v') x := rfl
    rw [GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.grpCo, rdA_matHom_embV,
      show splitHom D.sp.cm.sig T.gram (GlobalTheory.SplitProjChart.emb φ) (e.symm x) = _ from h4, ← h6]
    exact block_frame_conjugation_identity _ a x

end GlobalTheory.SplitChartLink
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitTorusLeviSumVanishes
section
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace
open PI.DSInfCharCap (actU Egl)
open GlobalTheory.RealInd.Stages Finset GlobalTheory.FlagMeas Formalism.REAL

namespace GlobalTheory.RealInd.BlockSum

theorem detOn_prefix {n b : ℕ} {ε : Fin n → Bool} {W' : Flag n b}
    (hW : IsIsoFlag ε (fun _ => 1) W') {x : Fin b → ℝ} {t : UJ ε} (ht : IsSplit ε W' x t) (m : Fin (b + 1)) :
    detOn (uMat t) (W' m) = Real.exp (∑ l with l.castSucc < m, x l) := by
  induction m using Fin.induction with
  | zero => simp [hW.1, detOn_bot, Fin.not_lt_zero]
  | succ m ih =>
    rw [ht.detOn_succ hW m, ih, ← Real.exp_add]
    congr 1
    have e1 : (Finset.univ.filter fun l : Fin b => l.castSucc < m.succ) = Iic m := by
      ext l; simp [Fin.castSucc_lt_succ_iff]
    have e2 : (Finset.univ.filter fun l : Fin b => l.castSucc < m.castSucc) = Iio m := by
      ext l; simp
    rw [e1, e2, ← Finset.Iio_insert, Finset.sum_insert Finset.notMem_Iio_self]
    simp [add_comm]

theorem blockSum_eq_zero : ∀ {n a b : ℕ} {ε : Fin n → Bool} {W : Flag n a} {W' : Flag n b} {β : Fin b → Fin a}
    {p : Fin (a + 1) → Fin (b + 1)}, IsIsoFlag ε (fun _ => 1) W' → (∀ i, W' (p i) = W i) →
    (∀ l i, β l = i ↔ p i.castSucc ≤ l.castSucc ∧ l.castSucc < p i.succ) →
    ∀ {x : Fin b → ℝ} {t : UJ ε}, IsSplit ε W' x t → t ∈ leviOne ε W → ∀ i, ∑ l with β l = i, x l = 0 := by
  intro n a b ε W W' β p hW hp hβ x t ht hl i
  have hS : ∀ k : Fin (a + 1), ∑ l with l.castSucc < p k, x l = 0 := fun k => by
    have h1 := hl.2 k
    rw [← hp k, detOn_prefix hW ht] at h1
    exact Real.exp_eq_one_iff _ |>.1 h1
  set A := p i.castSucc
  set B := p i.succ
  have hblk : (Finset.univ.filter fun l : Fin b => β l = i) =
      ((Finset.univ.filter fun l : Fin b => l.castSucc < B).filter fun l => ¬ l.castSucc < A) := by
    ext l; simp only [Finset.mem_filter, Finset.mem_univ, true_and, hβ, not_lt]; tauto
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (Finset.univ.filter fun l : Fin b => l.castSucc < B) (fun l => l.castSucc < A) x
  rw [hS i.succ, ← hblk] at hsplit
  have h0 : ∑ l ∈ (Finset.univ.filter fun l : Fin b => l.castSucc < B).filter (fun l => l.castSucc < A), x l = 0 := by
    rw [Finset.filter_filter]
    rcases le_total A B with h | h
    · have : (Finset.univ.filter fun l : Fin b => l.castSucc < B ∧ l.castSucc < A) =
          Finset.univ.filter fun l : Fin b => l.castSucc < A := by
        ext l; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨fun h' => h'.2, fun h' => ⟨lt_of_lt_of_le h' h, h'⟩⟩
      rw [this]; exact hS i.castSucc
    · have : (Finset.univ.filter fun l : Fin b => l.castSucc < B ∧ l.castSucc < A) =
          Finset.univ.filter fun l : Fin b => l.castSucc < B := by
        ext l; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨fun h' => h'.1, fun h' => ⟨h', lt_of_lt_of_le h' h⟩⟩
      rw [this]; exact hS i.succ
  linarith

end GlobalTheory.RealInd.BlockSum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitTorusRefinedFlag
section
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace
open PI.DSInfCharCap (actU Egl)
open GlobalTheory.RealInd.Stages Finset GlobalTheory.FlagMeas Formalism.REAL

namespace GlobalTheory.RealInd.Stages

theorem keeps_of_refine {n a b : ℕ} {W : Flag n a} {W' : Flag n b} {β : Fin b → Fin a}
    {p : Fin (a + 1) → Fin (b + 1)} (hW' : Monotone W') (hp : ∀ i, W' (p i) = W i)
    (hl : W' (Fin.last b) = W (Fin.last a))
    (hβ : ∀ l i, β l = i ↔ p i.castSucc ≤ l.castSucc ∧ l.castSucc < p i.succ)
    {g : Matrix (Fin n) (Fin n) ℂ} {c : Fin a → ℂ}
    (hstep : ∀ i : Fin a, ∀ y ∈ W i.succ, g *ᵥ y - c i • y ∈ W i.castSucc)
    (hlast : ∀ y ∈ W (Fin.last a), g *ᵥ y ∈ W (Fin.last a)) :
    ∀ l, ∀ y ∈ W' l, g *ᵥ y ∈ W' l := by
  intro l
  induction l using Fin.lastCases with
  | last => rw [hl]; exact hlast
  | cast l =>
    intro y hy
    obtain ⟨h1, h2⟩ := (hβ l (β l)).1 rfl
    have hy' : y ∈ W (β l).succ := by
      rw [← hp]; exact hW' h2.le hy
    have hs : g *ᵥ y - c (β l) • y ∈ W' l.castSucc := hW' h1 ((hp _).symm ▸ hstep _ y hy')
    have := (W' _).add_mem hs ((W' _).smul_mem (c (β l)) hy)
    rwa [sub_add_cancel] at this

theorem isSplit_of_refine {n a b : ℕ} {ε : Fin n → Bool} {j : Fin a → ℕ} {W : Flag n a} {W' : Flag n b}
    {β : Fin b → Fin a} {p : Fin (a + 1) → Fin (b + 1)} (hW : IsIsoFlag ε j W)
    (hW' : IsIsoFlag ε (fun _ => 1) W') (hp : ∀ i, W' (p i) = W i) (hl : W' (Fin.last b) = W (Fin.last a))
    (hβ : ∀ l i, β l = i ↔ p i.castSucc ≤ l.castSucc ∧ l.castSucc < p i.succ) {x : Fin a → ℝ} {t : UJ ε}
    (ht : IsSplit ε W x t) : IsSplit ε W' (x ∘ β) t := by
  have k1 := keeps_of_refine hW'.2.1 hp hl hβ ht.2.1 (fun y hy => (ht.1 _ y hy).1)
  have ht' := ht.opp hW
  have hoM : Monotone (opp ε W') := fun _ _ h => Submodule.map_mono (hW'.2.1 h)
  have k2 := keeps_of_refine (W := opp ε W) (W' := opp ε W') hoM
    (fun i => congrArg (fun V => V.map (Jm ε).mulVecLin) (hp i))
    (congrArg (fun V => V.map (Jm ε).mulVecLin) hl) hβ ht'.2.1 (fun y hy => (ht'.1 _ y hy).1)
  refine ⟨fun l y hy => ⟨k1 l y hy, ?_⟩, fun l y hy => ?_, ?_⟩
  · have hJ : (uMat t)ᴴ = Jm ε * uMat t⁻¹ * Jm ε := by
      rw [mul_assoc, inv_mul_Jm, ← mul_assoc, Jm_mul_self, one_mul]
    have hi := GlobalTheory.FlagLeviGroup.inv_keeps (GlobalTheory.FlagLeviGroup.uMat_inv_mul t) _ (k2 l)
    obtain ⟨z, hz, e⟩ := hi _ ⟨y, hy, rfl⟩
    rw [mulVecLin_apply, mulVecLin_apply] at e
    rw [hJ, ← mulVec_mulVec, ← mulVec_mulVec, ← e, mulVec_mulVec, Jm_mul_self, one_mulVec]
    exact hz
  · obtain ⟨h1, h2⟩ := (hβ l (β l)).1 rfl
    have hy' : y ∈ W (β l).succ := by
      rw [← hp]; exact hW'.2.1 (Fin.castSucc_lt_iff_succ_le.1 h2) hy
    have hs := ht.2.1 (β l) y hy'
    rw [← hp] at hs
    exact hW'.2.1 h1 hs
  · rw [hl]; exact ht.2.2

end GlobalTheory.RealInd.Stages
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.StageFunctionContinuous
section
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace
open PI.DSInfCharCap (actU Egl)
open GlobalTheory.RealInd.Stages Finset GlobalTheory.FlagMeas Formalism.REAL

namespace GlobalTheory.RealInd.Stages

theorem stageFun_continuous : ∀ {n : ℕ} {ε : Fin n → Bool} {U V : Type} [NormedAddCommGroup U] [InnerProductSpace ℂ U] [NormedAddCommGroup V] [InnerProductSpace ℂ V] (M : Subgroup (UJ ε)) (Fsp : Submodule ℂ (UJ ε → U)) (ι : Fsp →ₗ[ℂ] V) (μ : Measure ↥(KG ε ⊓ M)) [IsProbabilityMeasure μ], (∀ f : Fsp, ‖ι f‖ ^ 2 = ∫ k : ↥(KG ε ⊓ M), ‖f.1 k‖ ^ 2 ∂μ) → ∀ {F : UJ ε → U}, Continuous F → (∀ g, restr M F g ∈ Fsp) → Continuous (stageFun M Fsp ι F) := by
  intro n ε U V _ _ _ _ M Fsp ι μ _ hnorm F hF hmem

  let Φ : C(UJ ε, C(KG ε, U)) :=
    ContinuousMap.curry ⟨fun p : UJ ε × KG ε => F ((p.2 : UJ ε) * p.1), by fun_prop⟩
  have hΦ : ∀ g (k : KG ε), Φ g k = F ((k : UJ ε) * g) := fun g k => rfl
  have key : ∀ g g₀, ‖stageFun M Fsp ι F g - stageFun M Fsp ι F g₀‖ ≤ ‖Φ g - Φ g₀‖ := by
    intro g g₀
    rw [stageFun_of_mem ι (hmem g), stageFun_of_mem ι (hmem g₀), ← map_sub]
    set f : Fsp := (⟨_, hmem g⟩ - ⟨_, hmem g₀⟩ : Fsp) with hf
    set C := ‖Φ g - Φ g₀‖
    have hC : 0 ≤ C := norm_nonneg _
    have hpt : ∀ k : ↥(KG ε ⊓ M), ‖f.1 k‖ ^ 2 ≤ C ^ 2 := by
      intro k
      have hkM : (k : UJ ε) ∈ M := (Subgroup.mem_inf.1 k.2).2
      have hkK : (k : UJ ε) ∈ KG ε := (Subgroup.mem_inf.1 k.2).1
      have : f.1 k = (Φ g - Φ g₀) ⟨k, hkK⟩ := by
        simp only [hf, Submodule.coe_sub, Pi.sub_apply, ContinuousMap.sub_apply, hΦ,
          restr_of_mem _ _ hkM]
      rw [this]
      exact pow_le_pow_left₀ (norm_nonneg _) (ContinuousMap.norm_coe_le_norm _ _) 2
    have hint : ∫ k : ↥(KG ε ⊓ M), ‖f.1 k‖ ^ 2 ∂μ ≤ C ^ 2 := by
      have h1 := norm_integral_le_of_norm_le_const (μ := μ) (f := fun k => ‖f.1 k‖ ^ 2) (C := C ^ 2)
        (Filter.Eventually.of_forall fun k => by
          rw [Real.norm_of_nonneg (by positivity)]; exact hpt k)
      simp at h1
      exact (le_abs_self _).trans h1
    have h3 : ‖ι f‖ ^ 2 ≤ C ^ 2 := (hnorm f).symm ▸ hint
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) hC two_ne_zero).1 h3
  rw [continuous_iff_continuousAt]
  intro g₀
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) (fun g => key g g₀) ?_
  have : Filter.Tendsto (fun g => Φ g - Φ g₀) (nhds g₀) (nhds 0) := by
    simpa using ((Φ.continuous.tendsto g₀).sub_const (Φ g₀))
  simpa using this.norm

end GlobalTheory.RealInd.Stages
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.StageFunctionNormIntegral
section
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace
open PI.DSInfCharCap (actU Egl)
open GlobalTheory.RealInd.Stages Finset GlobalTheory.FlagMeas Formalism.REAL

namespace GlobalTheory.RealInd.Stages

theorem stageFun_normSq_integral : ∀ {n : ℕ} {ε : Fin n → Bool} {U V : Type} [NormedAddCommGroup U] [InnerProductSpace ℂ U] [NormedAddCommGroup V] [InnerProductSpace ℂ V] (M : Subgroup (UJ ε)) (Fsp : Submodule ℂ (UJ ε → U)) (ι : Fsp →ₗ[ℂ] V) (μ : Measure ↥(KG ε ⊓ M)) [IsProbabilityMeasure μ], (∀ f : Fsp, ‖ι f‖ ^ 2 = ∫ k : ↥(KG ε ⊓ M), ‖f.1 k‖ ^ 2 ∂μ) → ∀ {F : UJ ε → U}, Continuous F → (∀ g, restr M F g ∈ Fsp) → ∫ k : KG ε, ‖stageFun M Fsp ι F k‖ ^ 2 ∂muK ε = ∫ k : KG ε, ‖F k‖ ^ 2 ∂muK ε := by
  intro n ε U V _ _ _ _ M Fsp ι μ _ hnorm F hFc hF

  have h1 : ∀ k : KG ε, ‖stageFun M Fsp ι F k‖ ^ 2 = ∫ c : ↥(KG ε ⊓ M), ‖F ((c : UJ ε) * (k : UJ ε))‖ ^ 2 ∂μ := by
    intro k
    rw [stageFun_of_mem ι (hF k), hnorm]
    refine integral_congr_ae (Filter.Eventually.of_forall fun c => ?_)
    simp only
    rw [restr_of_mem F (k : UJ ε) (Subgroup.mem_inf.1 c.2).2]
  simp_rw [h1]

  have hKc : Continuous fun k : KG ε => F (k : UJ ε) := hFc.comp continuous_subtype_val
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hKc.continuousOn
  have hint : Integrable (Function.uncurry fun (k : KG ε) (c : ↥(KG ε ⊓ M)) => ‖F ((c : UJ ε) * (k : UJ ε))‖ ^ 2)
      ((muK ε).prod μ) := by
    refine Integrable.of_bound (C := C ^ 2) ?_ ?_
    · refine Continuous.aestronglyMeasurable ?_
      refine (continuous_norm.comp (hFc.comp ?_)).pow 2
      exact (continuous_subtype_val.comp continuous_snd).mul (continuous_subtype_val.comp continuous_fst)
    · refine Filter.Eventually.of_forall fun p => ?_
      have hp : (p.2 : UJ ε) * (p.1 : UJ ε) ∈ KG ε := mul_mem (Subgroup.mem_inf.1 p.2.2).1 p.1.2
      have hb := hC (⟨_, hp⟩ : KG ε) (Set.mem_univ _)
      simp only [Function.uncurry, Real.norm_eq_abs, abs_pow, abs_norm]
      exact pow_le_pow_left₀ (norm_nonneg _) hb 2
  rw [integral_integral_swap hint]
  have h3 : ∀ c : ↥(KG ε ⊓ M), ∫ k : KG ε, ‖F ((c : UJ ε) * (k : UJ ε))‖ ^ 2 ∂muK ε =
      ∫ k : KG ε, ‖F k‖ ^ 2 ∂muK ε := by
    intro c
    exact integral_mul_left_eq_self (μ := muK ε) (fun k : KG ε => ‖F (k : UJ ε)‖ ^ 2)
      (⟨c, (Subgroup.mem_inf.1 c.2).1⟩ : KG ε)
  simp_rw [h3]
  simp

end GlobalTheory.RealInd.Stages
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.StageParameterPairingShift
section
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace
open PI.DSInfCharCap (actU Egl)
open GlobalTheory.RealInd.Stages Finset GlobalTheory.FlagMeas Formalism.REAL

namespace GlobalTheory.RealInd.Stages

theorem stageS_pairings : ∀ {a b : ℕ} (n : ℕ) (j : Fin a → ℕ) (β : Fin b → Fin a) (s : Fin a → ℂ) (y : Fin b → ℝ), (∀ i, 1 ≤ j i) → (∀ i, #{l | β l = i} = j i) → (∀ i, ∑ l with β l = i, rho n (fun _ => 1) l = (j i : ℂ) * rho n j i) → (∀ x : Fin a → ℝ, pairing (fun _ => 1) (stageS j β s y + rho n fun _ => 1) (x ∘ β) = pairing j (s + rho n j) x) ∧ ∀ x : Fin b → ℝ, (∀ i, ∑ l with β l = i, x l = 0) → pairing (fun _ => 1) (stageS j β s y) x = pairing (fun _ => 1) (fun l => Complex.I * y l) x := by
  intro a b n j β s y hj hcard hrho
  have hsum : ∀ i, ∑ l with β l = i, stageS j β s y l = (j i : ℂ) * s i := by
    intro i
    have hj0 : (j i : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by have := hj i; omega)
    have h1 : ∀ l ∈ ({l | β l = i} : Finset (Fin b)),
        stageS j β s y l = s i + Complex.I * ((y l - blockMean j β y i : ℝ) : ℂ) := by
      intro l hl
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl
      simp [stageS, hl]
    have h2 : ∑ l with β l = i, ((y l - blockMean j β y i : ℝ) : ℂ) = 0 := by
      rw [← Complex.ofReal_sum, Finset.sum_sub_distrib, Finset.sum_const, hcard, nsmul_eq_mul, blockMean]
      rw [mul_div_cancel₀ _ hj0, sub_self, Complex.ofReal_zero]
    rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, ← Finset.mul_sum, h2, Finset.sum_const, hcard,
      nsmul_eq_mul]
    ring
  constructor
  · intro x
    simp only [pairing, Nat.cast_one, one_mul, Pi.add_apply, Function.comp_apply]
    rw [← Finset.sum_fiberwise Finset.univ β]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h3 : ∀ l ∈ ({l | β l = i} : Finset (Fin b)),
        (stageS j β s y l + rho n (fun _ => 1) l) * (x (β l) : ℂ)
          = (stageS j β s y l + rho n (fun _ => 1) l) * (x i : ℂ) := by
      intro l hl
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl
      rw [hl]
    rw [Finset.sum_congr rfl h3, ← Finset.sum_mul, Finset.sum_add_distrib, hsum, hrho]
    ring
  · intro x hx
    simp only [pairing, Nat.cast_one, one_mul]
    rw [← sub_eq_zero, ← Finset.sum_sub_distrib, ← Finset.sum_fiberwise Finset.univ β]
    refine Finset.sum_eq_zero fun i _ => ?_
    have h4 : ∀ l ∈ ({l | β l = i} : Finset (Fin b)),
        stageS j β s y l * (x l : ℂ) - Complex.I * (y l : ℂ) * (x l : ℂ)
          = (s i - Complex.I * (blockMean j β y i : ℂ)) * (x l : ℂ) := by
      intro l hl
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl
      simp only [stageS, hl]
      push_cast
      ring
    rw [Finset.sum_congr rfl h4, ← Finset.mul_sum, ← Complex.ofReal_sum, hx i]
    simp

end GlobalTheory.RealInd.Stages
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TensTInner
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowEvalHH

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def Wsub (R : RealDat D A Ks) (X : Formalism.L2.SG.HidaSetting.HidaSetting D)
    (c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)) (τ : D.what₂.Tau) :
    Submodule ℂ (X.B.H (X.pl.symm τ)) :=
  ((MP R).sm τ).map ((c τ).toLinearEquiv.toLinearMap)

theorem symm_mem_sm (R : RealDat D A Ks) (X : Formalism.L2.SG.HidaSetting.HidaSetting D)
    (c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)) (τ : D.what₂.Tau) (y : Wsub R X c τ) :
    (c τ).symm (y : X.B.H (X.pl.symm τ)) ∈ (MP R).sm τ := by
  obtain ⟨w, hw, hwy⟩ := Submodule.mem_map.1 y.2
  have : (c τ).symm (y : X.B.H (X.pl.symm τ)) = w := by
    rw [← hwy]
    exact (c τ).symm_apply_apply w
  rw [this]
  exact hw

def vecOf (R : RealDat D A Ks) (X : Formalism.L2.SG.HidaSetting.HidaSetting D)
    (c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)) (y : ∀ τ, Wsub R X c τ) : (MP R).Vec :=
  fun τ => ⟨(c τ).symm (y τ : X.B.H (X.pl.symm τ)), symm_mem_sm R X c τ (y τ)⟩

def tensT {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (y : ∀ τ, X.B.H (X.pl.symm τ)) : X.B.Hs :=
  X.B.tens (Equiv.piCongrLeft X.B.H X.pl.symm y)

open Classical in

def evF (R : RealDat D A Ks) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (t : GA D (Yc D 0)) (c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)) (S : MMap (MP R))
    (y : ∀ τ, Wsub R X c τ) : L2X X :=
  star (if hm : MemLp (fun x => ev (MP R) (vecOf R X c y) S
      (@HMul.hMul (GA D (Yc D 0)) (GA D (Yc D 0)) (GA D (Yc D 0)) _ ((iotaX X h).symm x) t)) 2 (muX X)
    then hm.toLp _ else 0)

end GlobalTheory.RowEvalHH

namespace GlobalTheory.RowEvalHH

theorem tensT_inner {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (a b : ∀ τ, X.B.H (X.pl.symm τ)) :
    ⟪tensT X a, tensT X b⟫_ℂ = ∏ τ, ⟪a τ, b τ⟫_ℂ := by
  unfold tensT
  rw [X.B.tens_spec.1]
  rw [← Equiv.prod_comp X.pl.symm]
  simp only [Equiv.piCongrLeft_apply_apply]

theorem tensT_dense {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) :
    Dense (Submodule.span ℂ (Set.range (tensT X)) : Set X.B.Hs) := by
  have : Set.range (tensT X) = Set.range X.B.tens :=
    (Equiv.piCongrLeft X.B.H X.pl.symm).surjective.range_comp X.B.tens
  rw [this]
  exact X.B.tens_spec.2.2

theorem tensT_w {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) :
    tensT X (fun τ => X.B.w (X.pl.symm τ)) = X.B.tens X.B.w := by
  unfold tensT
  congr 1
  have : (fun τ => X.B.w (X.pl.symm τ)) = (Equiv.piCongrLeft X.B.H X.pl.symm).symm X.B.w := by
    funext τ
    rw [Equiv.piCongrLeft_symm_apply]
  rw [this, Equiv.apply_symm_apply]

end GlobalTheory.RowEvalHH

namespace GlobalTheory.RowEvalHH

theorem Wsub_dense {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)
    (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)) (τ : D.what₂.Tau) :
    Dense (Wsub R X c τ : Set (X.B.H (X.pl.symm τ))) := by
  unfold Wsub
  rw [Submodule.map_coe]
  exact (c τ).surjective.denseRange.dense_image (c τ).continuous (Formalism.IndefR.SchurOrthogonalityAlt.sm_dense (MP R) τ)

end GlobalTheory.RowEvalHH
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftNsmulMemCompletedHomLatticeStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liftLattice_exists_nsmul_mem_standardTensorLattice : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (hn : T.rank ≤ S.rank) (ΛT : Lt D.host.E T.rank), IsSelfDualC T ΛT → IsAA C.X.Λ ΛT → ∀ (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)), Formalism.L2.DIV.IsFrame βS (stdL D.host.E S.rank) → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ), Pg.Nonempty → (∀ PP, PP ∈ Pg ∨ PP ∈ Q → (2 : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ e : AE D, IsIdemSum e (Pg ∪ Q) → ∃ m : ℕ, 0 < m ∧ ∀ x ∈ GlobalTheory.LiftLevel.liftL S T βS βT Pg Q e, m • x ∈ latO S T (stdL D.host.E S.rank : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True := by
  first | exact @GlobalTheory.LiftLevel.liftL_nsmul_mem_latO | exact GlobalTheory.LiftLevel.liftL_nsmul_mem_latO | (intros; apply GlobalTheory.LiftLevel.liftL_nsmul_mem_latO <;> assumption)
end

