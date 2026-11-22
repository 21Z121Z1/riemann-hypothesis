import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LatSpanLeSpan
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0010
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0011
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LevelSubgroupCharacterUnitary

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ActFrame
section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat

namespace Formalism.L2.SG.Pf.Act

open Formalism.L2.SG.Pf Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.Saturated

section FrameFix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D}

theorem frame_mapLF {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) {T : D.host.E}
    (F : FlagG (VS D) D.R.rS T) (a : Fin (D.R.rS + 1)) : frame (mapLF γ (lf D F)) a = γ (F.fvec a) := by
  unfold mapLF
  rw [dif_pos hγ]
  refine Fin.lastCases ?_ (fun i => ?_) a
  · simp [frame, FlagG.fvec, Formalism.L2.SG.TermOp.mapFlag]
  · simp [frame, FlagG.fvec, Formalism.L2.SG.TermOp.mapFlag]

theorem zt_mapLF {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) {T : D.host.E}
    (F : FlagG (VS D) D.R.rS T) : (mapLF γ (lf D F)).zt = γ F.z := by
  unfold mapLF
  rw [dif_pos hγ]

theorem Xflag_mapLF {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) {T : D.host.E}
    (F : FlagG (VS D) D.R.rS T) (j : ℕ) :
    Xflag (mapLF γ (lf D F)) j = (Xflag (lf D F) j).map (γ : (VS D).V →ₗ[D.host.E] (VS D).V) := by
  unfold mapLF
  rw [dif_pos hγ]
  show Submodule.span D.host.E ((fun a => γ (F.e a)) '' {i | i.1 < j}) =
    Submodule.map (γ : (VS D).V →ₗ[D.host.E] (VS D).V) (Submodule.span D.host.E (F.e '' {i | i.1 < j}))
  rw [Submodule.map_span, ← Set.image_comp]
  rfl

theorem z_mapLF {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) {T : D.host.E}
    (F : FlagG (VS D) D.R.rS T) : (mapLF γ (lf D F)).fl.z = γ F.z := by
  unfold mapLF
  rw [dif_pos hγ]
  rfl

theorem one_mem_NLam {T : D.host.E} (Λ : Submodule (𝓞 D.host.E) (VS D).V) (F : LFlag (VS D) D.R.rS T) :
    (1 : (VS D).V ≃ₗ[D.host.E] (VS D).V) ∈ NLam Λ F := by
  refine ⟨⟨(Formalism.HermitianLatticesTheory.isom (VS D).hT).one_mem, gmap_one_sat Λ⟩, fun j x _ => ?_, fun x _ => ?_⟩
  · show x - x ∈ _; rw [sub_self]; exact Submodule.zero_mem _
  · show x - x ∈ _; rw [sub_self]; exact Submodule.zero_mem _

theorem frameFix (Y : Full X) {u u' : D.what₂.Word}
    (s : GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u'))
    (y : TermDef.Carrier (TermDef.PD D s.lam (lf D (X.Fu u)) u')) (β : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (hP : IsPair s.lam (lf D (X.Fu u)) s.frame y.1 β (gS D)) :
    ∃ μ : (VS D).V ≃ₗ[D.host.E] (VS D).V, μ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT ∧ Formalism.HermitianLatticesTheory.gmap μ s.lam' = s.lam' ∧
      (∀ x ∈ Xsp (lf D (X.Fu u')), μ x ∈ Xsp (lf D (X.Fu u'))) ∧
      (∀ x ∈ orth (VS D) (Xsp (lf D (X.Fu u'))), μ x - x ∈ Xsp (lf D (X.Fu u'))) ∧
      TermDef.DCRel s.lam (lf D (X.Fu u)) y.1 (mapLF (β * s.lin * μ) (lf D (X.Fu u'))) := by
  obtain ⟨⟨hβi, hβΛ⟩, hβX, hβz, -⟩ := hP
  have hγi : s.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := s.rep.2.2.1
  have hγΛ : Formalism.HermitianLatticesTheory.gmap s.lin s.lam' = s.lam := s.rep.2.2.2.1
  obtain ⟨⟨hyz, hyzt⟩, -, hyOK⟩ := y.2
  obtain ⟨ψ, hψdef⟩ : ∃ ψ, ψ = β * s.lin := ⟨_, rfl⟩
  have hψ : ψ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := by rw [hψdef]; exact mul_mem hβi hγi
  have hψΛ : Formalism.HermitianLatticesTheory.gmap ψ s.lam' = s.lam := by rw [hψdef, gmap_mul_sat, hγΛ, hβΛ]
  have hψΛ' : Formalism.HermitianLatticesTheory.gmap ψ⁻¹ s.lam = s.lam' := by rw [← hψΛ, gmap_inv_gmap]

  have hfl : ∀ j, (Xflag (lf D (X.Fu u')) j).map (ψ : (VS D).V →ₗ[D.host.E] (VS D).V) = Xflag y.1 j := by
    intro j
    have h1 : Submodule.map (β : (VS D).V →ₗ[D.host.E] (VS D).V) (Xflag (mapLF s.lin (lf D (X.Fu u'))) j) =
        Xflag y.1 j := hβX j
    have h2 := Xflag_mapLF hγi (X.Fu u') j
    rw [hψdef]
    exact (Submodule.map_comp (s.lin : (VS D).V →ₗ[D.host.E] (VS D).V) (β : (VS D).V →ₗ[D.host.E] (VS D).V) _).trans
      ((congrArg (Submodule.map (β : (VS D).V →ₗ[D.host.E] (VS D).V)) h2.symm).trans h1)
  have hzψ : ψ (X.Fu u').z = y.1.fl.z := by
    have h1 : β (mapLF s.lin (lf D (X.Fu u'))).fl.z = y.1.fl.z := hβz
    rw [z_mapLF hγi] at h1
    rw [hψdef]; exact h1
  have hyE : ∀ a, ψ.symm (y.1.fl.e a) ∈ Submodule.span D.host.E (Set.range (X.Fu u').e) := by
    intro a
    have h1 : y.1.fl.e a ∈ Xflag y.1 D.R.rS := Submodule.subset_span ⟨a, a.2, rfl⟩
    rw [← hfl] at h1
    obtain ⟨w, hw, hwe⟩ := h1
    have : ψ.symm (y.1.fl.e a) = w := by rw [← hwe]; simp
    rw [this]
    have hXr : Xflag (lf D (X.Fu u')) D.R.rS = (X.Fu u').X := Xa_r' (X.Fu u')
    rw [hXr] at hw
    exact hw

  set F2 := Formalism.L2.SG.Saturated.mapFlag ψ⁻¹ (inv_mem hψ) y.1.fl with hF2
  have hT0 : ((Tu D u' : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 (D.mem u').A.T_prime.ne_zero
  obtain ⟨δ, hδi, hδe, hδz⟩ := frame_witt hT0 (X.Fu u') F2
  have hδe' : ∀ a, δ ((X.Fu u').e a) = ψ.symm (y.1.fl.e a) := hδe
  have hδz' : δ (X.Fu u').z = (X.Fu u').z := by
    rw [hδz]
    show ψ.symm y.1.fl.z = (X.Fu u').z
    rw [← hzψ, LinearEquiv.symm_apply_apply]
  have hXδ : ∀ x ∈ Submodule.span D.host.E (Set.range (X.Fu u').e), δ x ∈ Submodule.span D.host.E (Set.range (X.Fu u').e) := by
    intro x hx
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun D.host.E).1 hx
    rw [map_sum]
    exact Submodule.sum_mem _ fun a _ => by rw [map_smul, hδe']; exact Submodule.smul_mem _ _ (hyE a)

  obtain ⟨f, L, hff, hef, hLp, hzL, hsplit⟩ := Y.split u' s.lam' s.mem'
  have hee := (X.Fu u').e_iso
  obtain ⟨-, ⟨-, hunΛ', -, -⟩, hXΛ'⟩ := (Y.rowsOK u').1 s.lam' s.mem'

  have hF2eq : Formalism.L2.SG.Saturated.mapFlag δ hδi (X.Fu u') = F2 := flagG_ext (funext hδe) hδz
  have hXSy : XLam s.lam y.1 = XS D y.1.fl := hyOK.2
  have hXsp : Xsp (Formalism.L2.SG.Saturated.mapL ψ⁻¹ (inv_mem hψ) y.1) = Xsp (lf D (X.Fu u')) := by
    rw [Xsp_mapL]
    have h2 := hfl D.R.rS
    have hXr : Xflag (lf D (X.Fu u')) D.R.rS = Xsp (lf D (X.Fu u')) := Xa_r' (X.Fu u')
    have hXr' : Xflag y.1 D.R.rS = Xsp y.1 := Xa_r' y.1.fl
    rw [hXr, hXr'] at h2
    rw [← h2, ← Submodule.map_comp]
    have : ((ψ⁻¹ : (VS D).V ≃ₗ[D.host.E] (VS D).V) : (VS D).V →ₗ[D.host.E] (VS D).V) ∘ₗ
        (ψ : (VS D).V →ₗ[D.host.E] (VS D).V) = LinearMap.id := by
      ext v; show ψ.symm (ψ v) = v; simp
    rw [this, Submodule.map_id]
  have hXS : Formalism.HermitianLatticesTheory.gmap δ (XS D (X.Fu u')) = XS D (X.Fu u') :=
    calc Formalism.HermitianLatticesTheory.gmap δ (XS D (X.Fu u')) = XS D (Formalism.L2.SG.Saturated.mapFlag δ hδi (X.Fu u')) :=
          (XS_mapFlag D δ hδi _).symm
      _ = XS D F2 := congrArg (XS D) hF2eq
      _ = Formalism.HermitianLatticesTheory.gmap ψ⁻¹ (XS D y.1.fl) := XS_mapFlag D ψ⁻¹ (inv_mem hψ) y.1.fl
      _ = Formalism.HermitianLatticesTheory.gmap ψ⁻¹ (XLam s.lam y.1) := congrArg _ hXSy.symm
      _ = XLam (Formalism.HermitianLatticesTheory.gmap ψ⁻¹ s.lam) (Formalism.L2.SG.Saturated.mapL ψ⁻¹ (inv_mem hψ) y.1) :=
          (XLam_mapL ψ⁻¹ (inv_mem hψ) s.lam y.1).symm
      _ = XLam s.lam' (Formalism.L2.SG.Saturated.mapL ψ⁻¹ (inv_mem hψ) y.1) := by rw [hψΛ']
      _ = XLam s.lam' (lf D (X.Fu u')) := by unfold XLam; rw [hXsp]
      _ = XS D (X.Fu u') := hXΛ'
  have hXSΛ' : XS D (X.Fu u') ≤ s.lam' := by rw [← hXΛ']; exact inf_le_left
  have hδ1 : ∀ x ∈ latSpan (aaS D) (X.Fu u').e, δ x ∈ s.lam' := fun x hx => by
    rw [latSpan_aaS] at hx
    have : δ x ∈ Formalism.HermitianLatticesTheory.gmap δ (XS D (X.Fu u')) := (gmap_apply_mem δ _ x).2 hx
    rw [hXS] at this
    exact hXSΛ' this
  have hδ2 : ∀ x ∈ latSpan (aaS D) (X.Fu u').e, δ.symm x ∈ s.lam' := fun x hx => by
    rw [latSpan_aaS] at hx
    rw [← hXS, mem_gmap_iff] at hx
    exact hXSΛ' hx
  set μ := lequiv hee hff hef hδi hXδ with hμdef
  have hμ : μ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := lequiv_isom hee hff hef hδi hXδ
  have hμΛ : Formalism.HermitianLatticesTheory.gmap μ s.lam' = s.lam' :=
    gmap_lequiv hee hff hef hδi hXδ (aaS D) hsplit hLp hunΛ' hδ1 hδ2
  have hμz : μ (X.Fu u').z = (X.Fu u').z := lmap_perp _ (hLp _ hzL)
  have hμe : ∀ a, μ ((X.Fu u').e a) = δ ((X.Fu u').e a) := lequiv_e hee hff hef hδi hXδ
  have hμX : ∀ x ∈ Submodule.span D.host.E (Set.range (X.Fu u').e), μ x = δ x := fun x hx => by
    show lmap (X.Fu u').e f δ x = δ x
    rw [lmap_apply, pj_of_memX hee hef _ hx, pX_of_mem hef _ hx, pY_of_memX hee _ hx]; simp
  refine ⟨μ, hμ, hμΛ, fun x hx => ?_, fun x hx => ?_, ?_⟩
  · rw [hμX x hx]; exact hXδ x hx
  · have hx0 : ∀ a, (VS D).hT ((X.Fu u').e a) x = 0 := fun a =>
      (mem_orth' _ x).1 hx _ (Submodule.subset_span ⟨a, rfl⟩)
    have hY : pY (X.Fu u').e f x = 0 := by rw [pY_apply]; simp [hx0]
    have e1 : μ x = pj (X.Fu u').e f x + δ (pX (X.Fu u').e f x) := by
      show lmap (X.Fu u').e f δ x = _
      rw [lmap_apply, hY]; simp
    have e2 : x = pX (X.Fu u').e f x + pj (X.Fu u').e f x := by
      conv_lhs => rw [decomp (e := (X.Fu u').e) (f := f) x]
      rw [hY, add_zero]
    have e3 : μ x - x = δ (pX (X.Fu u').e f x) - pX (X.Fu u').e f x :=
      calc μ x - x = (pj (X.Fu u').e f x + δ (pX (X.Fu u').e f x)) -
            (pX (X.Fu u').e f x + pj (X.Fu u').e f x) := by rw [← e2, e1]
        _ = δ (pX (X.Fu u').e f x) - pX (X.Fu u').e f x := by abel
    rw [e3]
    exact Submodule.sub_mem _ (hXδ _ (pX_mem x)) (pX_mem x)
  · have hg : β * s.lin * μ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := by rw [← hψdef]; exact mul_mem hψ hμ
    have key : ∀ a, ψ (μ ((X.Fu u').fvec a)) = frame y.1 a := by
      intro a
      refine Fin.lastCases ?_ (fun i => ?_) a
      · simp only [FlagG.fvec, Fin.snoc_last]
        rw [hμz, hzψ]
      · simp only [FlagG.fvec, Fin.snoc_castSucc]
        rw [hμe, hδe', LinearEquiv.apply_symm_apply]
    have hz2 : ψ (μ (X.Fu u').z) = y.1.zt := by rw [hμz, hzψ, hyzt]
    subst hψdef
    refine ⟨1, one_mem_NLam _ _, 1, one_mem_NLam _ _, fun a => ?_, ?_⟩
    · exact (frame_mapLF hg (X.Fu u') a).trans (key a)
    · exact (zt_mapLF hg (X.Fu u')).trans hz2

end FrameFix

end Formalism.L2.SG.Pf.Act
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ExistsGaugeNormalizedStabilizer
section
namespace Formalism.L2.SG.Pf.GE

theorem existsGaugeNormalizedStabilizer : ExistsGaugeMeasureForEachRank := (show PI.ExistsGaugeMeasureForEachRank.ExistsGaugeMeasureForEachRank ↔ ExistsGaugeMeasureForEachRank from Iff.rfl).mp _root_.exists_gaugeNormalizedStabilizer

end Formalism.L2.SG.Pf.GE
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConstBHVolS
section
noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal Matrix

namespace Formalism.L2.SG.Pf.BH

open Formalism.QuantumDeterminants Formalism.L2.SG.Pf

def DimG : Prop :=
  ∀ k r : ℕ, Module.finrank ℝ (Formalism.MainNotions.S.lieE (UH (Hpk k r))) =
    2 * Module.finrank ℝ (Formalism.MainNotions.S.lieE (Nset k r)) + 2 * r + Module.finrank ℝ (Formalism.MainNotions.S.lieE (Formalism.FourierDecayAlt.B2.UWb k r))

def LieG : Prop :=
  ∀ k r : ℕ, Formalism.MainNotions.S.lieOf (UH (Hpk k r)) = {X | Hpk k r * Xᴴ * Hpk k r + X = 0}

def LieWb : Prop :=
  ∀ k r : ℕ, Formalism.MainNotions.S.lieOf (Formalism.FourierDecayAlt.B2.UWb k r) = {X | Hpk k r * Xᴴ * Hpk k r + X = 0 ∧
    ∀ a : Fin r, X *ᵥ bvec (eI k r a) = 0 ∧ X *ᵥ bvec (esI k r a) = 0}

def DimGOf : Prop := LieG → LieWb → DimG

def expL (k r : ℕ) (S : Set (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)) (Y : Formalism.MainNotions.S.lieE S) : Mt k r :=
  fun i j => NormedSpace.exp (Formalism.MainNotions.S.unrealify (Y : EuclideanSpace ℝ _)) i j

def RhoN : Prop :=
  ∀ (k r : ℕ) (Y : Formalism.MainNotions.S.lieE (Nset k r)), rhoS k r (Nset k r) (expL k r (Nset k r) Y) = (‖Y‖₊ : ℝ≥0∞)

def RhoMeas : Prop :=
  ∀ (k r : ℕ) (S : Set (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)), Measurable (rhoS k r S)

def LayerCmp : Prop :=
  ∀ (X Y : Type) [MeasurableSpace X] [MeasurableSpace Y] (μ : Measure X) (ν : Measure Y) (q : X → ℝ≥0∞)
    (p : Y → ℝ≥0∞), Measurable q → Measurable p → ∀ δ c : ℝ≥0∞,
    (∀ t, t < δ → μ {x | q x < t} ≤ c * ν {y | p y < t}) → (∀ t, t < δ → ν {y | p y < t} ≠ ∞) →
    ∀ g : ℝ≥0∞ → ℝ≥0∞, Antitone g → (∀ x, g x ≠ ∞) → (∀ x, δ ≤ x → g x = 0) →
      ∫⁻ x, g (q x) ∂μ ≤ c * ∫⁻ y, g (p y) ∂ν

def ModelVol : Prop :=
  ∀ (E1 E2 : Type) [NormedAddCommGroup E1] [InnerProductSpace ℝ E1] [FiniteDimensional ℝ E1] [MeasurableSpace E1]
    [BorelSpace E1] [NormedAddCommGroup E2] [InnerProductSpace ℝ E2] [FiniteDimensional ℝ E2] [MeasurableSpace E2]
    [BorelSpace E2] (r : ℕ) (s : ℝ), 0 < s →
    ∫⁻ c : Fin r → ℂ, ∫⁻ y1 : E1, ∫⁻ y2 : E2, ∫⁻ y3 : E1,
      (if (‖y1‖₊ : ℝ≥0∞) ^ 2 + ENNReal.ofReal (2 * ∑ a, ‖c a - 1‖ ^ 2) + (‖y2‖₊ : ℝ≥0∞) ^ 2 + (‖y3‖₊ : ℝ≥0∞) ^ 2 <
          ENNReal.ofReal (s ^ 2) then (1 : ℝ≥0∞) else 0) =
      ENNReal.ofReal ((2 : ℝ) ^ r)⁻¹ *
        volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (2 * Module.finrank ℝ E1 + 2 * r + Module.finrank ℝ E2))) s)

def BallDim : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
    [BorelSpace E] (s : ℝ),
    volume (Metric.ball (0 : E) s) = volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) s)

end Formalism.L2.SG.Pf.BH
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LeviMul
section
noncomputable section

open scoped Classical ComplexConjugate TensorProduct
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Matrix Formalism.L2.SG.TermOp Formalism.L2.SG.HidaSetting
  Formalism.L2.SG.Pf.unitaryCongruence

namespace Formalism.L2.SG.NormCut

section LeviMul

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} (TR : TypedRed X)

theorem resT_of_mem (v : TR.Pl) {z : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F} (hz : z ∈ IntAf X.B.I.F X.B.I.E) :
    resT TR v z = TR.res v ⟨z, hz⟩ := by
  unfold resT; rw [dif_pos hz]

theorem res_eq_zero_of_Z (v : TR.Pl) {z : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F} (hz : z ∈ IntAf X.B.I.F X.B.I.E)
    (hZ : ZMod' X.B.I X.B.g z) : TR.res v ⟨z, hz⟩ = 0 :=
  (TR.res_ker ⟨z, hz⟩).2 (Z_smul X.B.I X.B.g X.ew_int hZ) v

def PhiSub (x : X.B.I.Gf) (i : Fin D.R.k) : Submodule (IntAf X.B.I.F X.B.I.E) (VA X.B.I) where
  carrier := {z | ZMod' X.B.I X.B.g (hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ z) -
    ∑ l, hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw l) * hA X.B.I (X.bwd l) z)}
  add_mem' {z w} hz hw := by
    show ZMod' X.B.I X.B.g (hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ (z + w)) -
      ∑ l, hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw l) * hA X.B.I (X.bwd l) (z + w))
    have e : hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ (z + w)) -
        ∑ l, hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw l) * hA X.B.I (X.bwd l) (z + w) =
        (hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ z) -
          ∑ l, hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw l) * hA X.B.I (X.bwd l) z) +
        (hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ w) -
          ∑ l, hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw l) * hA X.B.I (X.bwd l) w) := by
      simp only [Matrix.mulVec_add, hA_add_right, mul_add, Finset.sum_add_distrib]; ring
    rw [e]; exact Z_add X.B.I X.B.g hz hw
  zero_mem' := by
    show ZMod' X.B.I X.B.g (hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ 0) -
      ∑ l, hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw l) * hA X.B.I (X.bwd l) 0)
    have h0 : ∀ u : VA X.B.I, hA X.B.I u 0 = 0 := fun u => (hL X.B.I u).map_zero
    simp only [Matrix.mulVec_zero, h0, mul_zero, Finset.sum_const_zero, sub_zero]
    exact Z_zero X.B.I X.B.g
  smul_mem' c z hz := by
    show ZMod' X.B.I X.B.g (hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ ((c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • z)) -
      ∑ l, hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw l) * hA X.B.I (X.bwd l) ((c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • z))
    have e : hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ ((c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • z)) -
        ∑ l, hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw l) * hA X.B.I (X.bwd l) ((c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • z) =
        (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * (hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ z) -
          ∑ l, hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw l) * hA X.B.I (X.bwd l) z) := by
      simp only [Matrix.mulVec_smul, hA_smul_right, mul_sub, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun l _ => ?_
      ring
    rw [e]; exact Z_smul X.B.I X.B.g c.2 hz

theorem dual_beta_reference_congruence (i : Fin D.R.k) (a : Fin D.R.rS) : ZMod' X.B.I X.B.g (hA X.B.I (X.bwd i) (X.e0 a)) := by
  rw [hA_symm]
  exact Z_sig X.B.I X.B.g ((X.weightVectorsIntegral i).2.2 a).2.2.1

theorem leviM_mul {x y : X.B.I.Gf} (hx : x ∈ X.B.I.Kset) (hy : y ∈ X.B.I.Kset)
    (hyb : ∀ j, X.B.I.fmat y *ᵥ X.bw j ∈ Mo X.B.I X.B.g (Set.range X.e0 ∪ Set.range X.bw))
    (hxe : ∀ a, X.B.I.fmat x *ᵥ X.e0 a ∈ Mo X.B.I X.B.g (Set.range X.e0)) (v : TR.Pl) :
    leviM TR (x * y) v = leviM TR x v * leviM TR y v := by
  have hbw : ∀ j, X.bw j ∈ X.B.I.Lf := fun j => (X.vectorsInLattice.2.2 j).1
  have hbwd : ∀ j, X.bwd j ∈ X.B.I.Lf := fun j => (X.vectorsInLattice.2.2 j).2
  have he0 : ∀ a, X.e0 a ∈ X.B.I.Lf := fun a => (X.vectorsInLattice.1 a).1

  have key : ∀ i, Mo X.B.I X.B.g (Set.range X.e0 ∪ Set.range X.bw) ≤ PhiSub x i := by
    intro i
    refine sup_le (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
    · rintro z (⟨a, rfl⟩ | ⟨m, rfl⟩)
      · show ZMod' X.B.I X.B.g (hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.e0 a) -
          ∑ l, hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw l) * hA X.B.I (X.bwd l) (X.e0 a))
        refine Z_sub X.B.I X.B.g ?_ (Z_sum X.B.I X.B.g _ _ fun l _ =>
          Z_smul X.B.I X.B.g (hA_int X.B.I (hbwd i) (K_mv X.B.I hx (hbw l))) (dual_beta_reference_congruence l a))
        have hQ : Mo X.B.I X.B.g (Set.range X.e0) ≤ Qs X.B.I X.B.g (X.bwd i) :=
          sup_le (Submodule.span_le.2 (by rintro _ ⟨b, rfl⟩; exact dual_beta_reference_congruence i b)) (mL_Qs X.B.I X.B.g (hbwd i))
        exact hQ (hxe a)
      · show ZMod' X.B.I X.B.g (hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw m) -
          ∑ l, hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw l) * hA X.B.I (X.bwd l) (X.bw m))
        have hw : hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw m) = X.ew * hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw m) := by
          conv_lhs => rw [X.bw_w m, Matrix.mulVec_smul, hA_smul_right]
        have e : hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw m) -
            ∑ l, hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw l) * hA X.B.I (X.bwd l) (X.bw m) =
            (hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw m) - hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw m) * X.ew) -
            ∑ l, hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw l) *
              (hA X.B.I (X.bwd l) (X.bw m) - if l = m then X.ew else 0) := by
          simp only [mul_sub, Finset.sum_sub_distrib, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
            if_true]
          ring
        have e2 : hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw m) - hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw m) * X.ew = 0 := by
          rw [hw]
          have := X.ew_idem
          linear_combination (-(hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw m))) * this
        rw [e, e2, zero_sub]
        have := Z_sum X.B.I X.B.g Finset.univ _ fun l _ =>
          Z_smul X.B.I X.B.g (hA_int X.B.I (hbwd i) (K_mv X.B.I hx (hbw l))) (X.bw_dual l m)
        obtain ⟨t, ht, htt⟩ := this
        exact ⟨-t, neg_mem ht, by rw [htt]; ring⟩
    · rintro _ ⟨w, hw, rfl⟩
      show ZMod' X.B.I X.B.g (hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ ((X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • w)) -
        ∑ l, hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw l) * hA X.B.I (X.bwd l) ((X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • w))
      refine ⟨hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ w) -
        ∑ l, hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw l) * hA X.B.I (X.bwd l) w, ?_, ?_⟩
      · exact sub_mem (hA_int X.B.I (hbwd i) (K_mv X.B.I hx hw)) (sum_mem fun l _ =>
          mul_mem (hA_int X.B.I (hbwd i) (K_mv X.B.I hx (hbw l))) (hA_int X.B.I (hbwd l) hw))
      · simp only [Matrix.mulVec_smul, hA_smul_right, mul_sub, Finset.mul_sum]
        congr 1
        refine Finset.sum_congr rfl fun l _ => ?_
        ring
  ext i j
  have hxy : X.B.I.fmat (x * y) *ᵥ X.bw j = X.B.I.fmat x *ᵥ (X.B.I.fmat y *ᵥ X.bw j) := by
    rw [fmat_mul, Matrix.mulVec_mulVec]
  have hZ := key i (hyb j)
  simp only [PhiSub, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_ofPred_eq] at hZ
  rw [← hxy] at hZ

  have hI1 : hA X.B.I (X.bwd i) (X.B.I.fmat (x * y) *ᵥ X.bw j) ∈ IntAf X.B.I.F X.B.I.E :=
    hA_int X.B.I (hbwd i) (K_mv X.B.I (K_mul X.B.I hx hy) (hbw j))
  have hI2 : ∀ l, hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw l) ∈ IntAf X.B.I.F X.B.I.E :=
    fun l => hA_int X.B.I (hbwd i) (K_mv X.B.I hx (hbw l))
  have hI3 : ∀ l, hA X.B.I (X.bwd l) (X.B.I.fmat y *ᵥ X.bw j) ∈ IntAf X.B.I.F X.B.I.E :=
    fun l => hA_int X.B.I (hbwd l) (K_mv X.B.I hy (hbw j))
  have hIs : ∑ l, hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw l) * hA X.B.I (X.bwd l) (X.B.I.fmat y *ᵥ X.bw j) ∈
      IntAf X.B.I.F X.B.I.E := sum_mem fun l _ => mul_mem (hI2 l) (hI3 l)
  have hD := res_eq_zero_of_Z TR v (sub_mem hI1 hIs) hZ
  simp only [leviM, Matrix.mul_apply]
  rw [resT_of_mem TR v hI1]
  simp only [resT_of_mem TR v (hI2 _), resT_of_mem TR v (hI3 _)]
  have e3 : (⟨hA X.B.I (X.bwd i) (X.B.I.fmat (x * y) *ᵥ X.bw j), hI1⟩ : IntAf X.B.I.F X.B.I.E) =
      ⟨_, sub_mem hI1 hIs⟩ + ∑ l, (⟨_, hI2 l⟩ : IntAf X.B.I.F X.B.I.E) * ⟨_, hI3 l⟩ := by
    apply Subtype.ext
    simp only [Subring.coe_add, AddSubmonoidClass.coe_finsetSum, Subring.coe_mul]
    ring
  rw [e3, map_add, hD, zero_add, map_sum]
  simp only [map_mul]

end LeviMul

end Formalism.L2.SG.NormCut
end
end

