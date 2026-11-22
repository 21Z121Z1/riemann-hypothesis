import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0024
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.FamilyGroupSumFactorsWeightAmplitude
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0021
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0245
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValLastX
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EqSemiMeasOfCovolOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0354
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0238
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMulRightInvariantHaarAdelicUnitaryGroupHermiti
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0182
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0199
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0246
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousIntegrand
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0241
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0289

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AmpQNotEqAmpG
section
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.TermLoc Formalism.L2.SG.NGLocModel Formalism.L2.SG.Pf.MainEqCut Formalism.L2.SG.Pf.MainEqSteps Formalism.L2.SG.Pf.MainEqAna Formalism.L2.SG.Pf.MainEqLoc Formalism.L2.SG.Pf.MainEqFam GlobalTheory.SnFam GlobalTheory.Core.One

namespace GlobalTheory.Core.One

attribute [local instance] Formalism.BasicNotions.Host.cmStar

private theorem ampQ_not_eq_ampG {Cl Nu : Type} (L : PN.LocalNG Cl Nu) : ampQ Not L = ampG L := by
  funext d
  unfold ampQ ampG
  rw [Finset.sum_eq_single_of_mem ∅ (by simp) (fun A hA h => absurd (by simp at hA; exact hA.2) h)]
  simp

private theorem hasPt_of_isPt {D : D7} {X : HidaSetting D} (Y : Full X) (u : D.what₂.Word)
    (νL νB : X.B.I.Ginf → Measure X.B.I.Ginf) (ng : PN.Pts D.host.E D.R.rS → ℝ) (γ : PN.Pts D.host.E D.R.rS)
    (h : PN.IsPt (genT (scT (Y.tO u u))) (NOf1 Y u νL νB ng) γ) : HasPt Y u u (Y.tO u u).genSet γ := by
  obtain ⟨c, n, t, ht, hv, -, hp, -⟩ := h
  rw [genT_ngSet] at ht
  exact ⟨t, ht, hv, hp⟩

theorem stepFam1_of : (∀ D : D7, 4 * D.R.rS + 7 ≤ D.R.k → Formalism.L2.SG.FamDefs.LocalLowerBoundAllCosets D.R.k D.R.rS 9) → Formalism.L2.SG.FamDefs.HTie → FamGen1 → FamilyWeightSumUnfoldingIdentity → WeightsFam → FamilyGroupSumFactorsWeightAmplitude → ExistFam → StepFam1 := by
  intro hG6 hH hF hG5 hW hG4 hE Cg cb Cw cT CT C0
  obtain ⟨CSt, hCSt, a4, b4, h4⟩ := hG4 Cg cb Cw cT CT C0
  obtain ⟨aH, bH, hH2⟩ := hH Cg cb Cw cT CT C0
  obtain ⟨a5, b5, h5⟩ := hG5 Cg cb Cw cT CT C0
  obtain ⟨aW, bW, hW2⟩ := hW Cg cb Cw cT CT C0
  obtain ⟨aE, bE, hE2⟩ := hE Cg cb Cw cT CT C0
  refine ⟨9, CSt, hCSt, max a4 (max aH (max a5 (max aW aE))), max b4 (max bH (max b5 (max bW bE))),
    fun C' Cl e1 e2 D large₂ X Y u hc hb X0 ψ hT sd C Th F0 what₂ vR Q i0 i0' νq Irat Ire hBk ν hν => ?_⟩
  simp only [max_le_iff] at e1 e2
  obtain ⟨e1a, e1b, e1c, e1d, e1e⟩ := e1
  obtain ⟨e2a, e2b, e2c, e2d, e2e⟩ := e2
  have hQ := hF D X Y u hc.2.2
  obtain ⟨s, hs1, hs0, hsb, htie⟩ :=
    h4 C' Cl e1a e2a D large₂ X Y u u hc hb X0 ψ hT sd C Th F0 what₂ vR Q i0 i0' νq Irat Ire hBk ν hν
  refine ⟨s, hs1, hs0, hsb, fun γ hγ S => ?_⟩
  have hP := hasPt_of_isPt Y u _ _ _ γ hγ
  obtain ⟨Fm, hFT, hRel, hTerm, hDs, hrw⟩ := hE2 C' Cl e1e e2e D large₂ X Y u u hc _ _ _ _ hQ γ hP
  have hG5Fm := Formalism.L2.SG.FamDefs.orbitFamilyIdentity_at_volume hFT (h5 C' Cl e1c e2c D large₂ X Y u u hc _ _ _ _ hQ γ hP Fm hFT)
  obtain ⟨hWpos, hWle⟩ := hW2 C' Cl e1d e2d D large₂ X Y u u hc hb X0 ψ hT sd C Th F0 what₂ vR Q i0 i0' νq Irat Ire hBk
    _ _ _ _ hQ γ hP Fm hFT hRel hTerm hG5Fm
  refine ⟨Fm, Formalism.L2.SG.FamDefs.famOKS_of (NOf1 Y u (sc s ν) ν (fun _ => 0)) γ S _ (fun L => ampG L) Fm hFT
    hRel hTerm hDs hrw (hG6 D (Formalism.L2.SG.FamDefs.four_rank_add_seven_le_k hc)) hG5Fm
    (hH2 C' Cl e1b e2b D large₂ X Y u u hc _ _ _ γ Fm hFT) hWpos hWle (fun x _ => ?_)⟩
  have h := htie _ _ _ _ hQ γ hP Fm hFT x.1 x.2
  rw [ampQ_not_eq_ampG] at h
  exact h

end GlobalTheory.Core.One
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BaseChangeTensorConjugationInvolutiveOfInvolution
section
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.StdUnn.Conj

theorem baseChangeTensorConjugation_involutive_of_involution {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) (e : R ⊗[F] E) : sigR R σ (sigR R σ e) = e := by
  induction e using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | tmul a x => simp [sigR, hσ]

theorem infinitePlaceComponent_tensorConjugation {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E)
    (w : InfinitePlace F) (z : AF F ⊗[F] E) :
    compInf F E w (sigR (AF F) σ z) = sigR w.Completion σ (compInf F E w z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]
  | tmul a x => simp [compInf, sigR]

theorem mul_eq_conj_mul_of_invertible_cancel {R : Type*} [Ring R] {P Pi F X K : R} (h1 : P * Pi = 1)
    (h : Pi * F * X = (Pi * K * P) * (Pi * F)) : F * X = K * F := by
  have := congrArg (P * ·) h
  simp only [← mul_assoc, h1, one_mul] at this
  rw [this, mul_assoc K P Pi, h1, mul_one]

theorem eq_inv_conj_of_intertwine {R : Type*} [Ring R] {Fi F X K : R} (h1 : Fi * F = 1) (h : F * X = K * F) :
    X = Fi * K * F := by
  rw [mul_assoc, ← h, ← mul_assoc, h1, one_mul]

variable {D : D7}

theorem matHom_chart_conj (A : HSp D) (μ : D.host.E) (κ : GA D (dblSp A) ≃* G D A.rank) (hκ : IsChart A μ κ)
    (Fr : GL (Fin (A.rank + A.rank)) (AE D)) (p : GA D (dblSp A))
    (hp : mt (dblSp A) p * (rat (Tm A μ) : Mx D (A.rank + A.rank) (A.rank + A.rank)) = Fr.1) (k : GA D (dblSp A)) :
    GlobalTheory.AdelicU.matHom _ D.sp.cm.sig (Jst D A.rank) (κ (p⁻¹ * k * p)) =
      Fr⁻¹ * GlobalTheory.AdelicU.matHom (n := A.rank + A.rank) _ D.sp.cm.sig (dblSp A).gram k * Fr := by
  set P := GlobalTheory.AdelicU.matHom (n := A.rank + A.rank) _ D.sp.cm.sig (dblSp A).gram p
  set Kk := GlobalTheory.AdelicU.matHom (n := A.rank + A.rank) _ D.sp.cm.sig (dblSp A).gram k
  have hmt : ∀ g, mt (dblSp A) g = (GlobalTheory.AdelicU.matHom (n := A.rank + A.rank) _ D.sp.cm.sig (dblSp A).gram g).1 := fun _ => rfl
  have hT : (rat (Tm A μ) : Mx D (A.rank + A.rank) (A.rank + A.rank)) = (P⁻¹).1 * Fr.1 := by
    rw [← hp, hmt, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
  have h := hκ (p⁻¹ * k * p)
  have hm : GlobalTheory.AdelicU.matHom (n := A.rank + A.rank) _ D.sp.cm.sig (dblSp A).gram (p⁻¹ * k * p) = P⁻¹ * Kk * P := by
    rw [map_mul, map_mul, map_inv]
  rw [hmt, hm, hT] at h
  change (P⁻¹).1 * Fr.1 * mat (κ (p⁻¹ * k * p)) = (P⁻¹ * Kk * P).1 * ((P⁻¹).1 * Fr.1) at h
  apply Units.ext
  have h2 : Fr.1 * mat (κ (p⁻¹ * k * p)) = Kk.1 * Fr.1 := by
    rw [Units.val_mul, Units.val_mul] at h
    exact mul_eq_conj_mul_of_invertible_cancel (P := P.1) (Units.mul_inv P) h
  change mat (κ (p⁻¹ * k * p)) = _
  rw [Units.val_mul, Units.val_mul]
  exact eq_inv_conj_of_intertwine (Units.inv_mul Fr) h2

theorem mem_KAd_iff_of_conj {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) {n : ℕ} (Q J : Matrix (Fin (n + n)) (Fin (n + n)) E)
    (L : Submodule (𝓞 E) (Fin n → E)) (a b : GL (Fin n) (AF F ⊗[F] E)) (hb : IsLatticeFrame L b)
    (hab : ∀ w, Formalism.UG.bc (compInf F E w) b = Formalism.UG.bc (compInf F E w) a)
    (M M' : GL (Fin (n + n)) (AF F ⊗[F] E)) (u r : (AF F ⊗[F] E)ˣ)
    (hM' : ∀ v i j, compFin F E v (M'.1 i j) ∈ intLoc F E v ∧ compFin F E v ((M'⁻¹).1 i j) ∈ intLoc F E v)
    (hMu : M.1 = (u : AF F ⊗[F] E) • M'.1)
    (hMM : ∀ w, (Formalism.UG.cT (sigR (AF F) σ) M.1 * M.1).map (compInf F E w) = compInf F E w r • 1)
    (k : GAd σ Q) (g : GAd σ J)
    (hg : GlobalTheory.AdelicU.matHom _ σ J g = (blkGL finSumFinEquiv (b, b) * M)⁻¹ * GlobalTheory.AdelicU.matHom _ σ Q k *
      (blkGL finSumFinEquiv (b, b) * M)) :
    k ∈ KAd σ Q L a ↔ g ∈ levelAll σ J (stdLattice E (n + n)) 1 := by
  rw [mem_KAd, mem_levelAll]
  refine and_congr (forall_congr' fun v => ?_) (forall_congr' fun w => ?_)
  · rw [GlobalTheory.Doubling.KFin, stabLoc, stabLoc, Subgroup.mem_comap, Subgroup.mem_comap, matHom_proj, matHom_proj, hg,
      map_mul (Formalism.UG.bc (compFin F E v)), map_mul (Formalism.UG.bc (compFin F E v)) _ (GlobalTheory.AdelicU.matHom _ σ Q k), map_inv]
    exact GlobalTheory.T.mem_latticeStabilizer_iff_scaledFrameConj F E (n + n) _ _ M M' u (isLatticeFrame_dbl hb) hM' hMu v _
  · have hc : Formalism.UG.cT (sigR w.Completion σ) (Formalism.UG.bc (compInf F E w) M).1 * (Formalism.UG.bc (compInf F E w) M).1 =
        ((Units.map (compInf F E w : AF F ⊗[F] E →* w.Completion ⊗[F] E) r : (w.Completion ⊗[F] E)ˣ) :
          w.Completion ⊗[F] E) • 1 := by
      have h := hMM w
      rw [Matrix.map_mul] at h
      refine Eq.trans ?_ h
      congr 1
      ext i j
      exact (infinitePlaceComponent_tensorConjugation σ w (M.1 j i)).symm
    rw [KArch, mem_stabArch, mem_stabArch, matHom_projArch, matHom_projArch, hg,
      GlobalTheory.T.mem_unitaryStandard_iff_conj_similitude _ _ (baseChangeTensorConjugation_involutive_of_involution _ σ hσ) _ _ _ _ hc]
    simp only [map_mul, map_inv, map_one, bc_blkGL, hab w, inv_one, one_mul, mul_one, mul_inv_rev, mul_assoc]

theorem isConj_of_frame : ∀ (D : D7) (A : HSp D) (μ : D.host.E), IsSkew μ → ∀ κ : GA D (dblSp A) ≃* G D A.rank, IsChart A μ κ → ∀ (a b : GL (Fin A.rank) (AE D)), IsLatticeFrame (frameLat A) b → (∀ w, Formalism.UG.bc (compInf D.host.F D.host.E w) b = Formalism.UG.bc (compInf D.host.F D.host.E w) a) → ∀ (M M' : GL (Fin (A.rank + A.rank)) (AE D)) (u : (AE D)ˣ), IntGL M' → M.1 = (u : AE D) • M'.1 → (∀ w, (adj M.1 * M.1).map (compInf D.host.F D.host.E w) = compInf D.host.F D.host.E w (2 * u * cA D u) • 1) → ∀ p : siegel A, mt (dblSp A) p * (rat (Tm A μ) : Mx D (A.rank + A.rank) (A.rank + A.rank)) = (blkGL finSumFinEquiv (b, b) * M).1 → IsConj A a κ p := by
  intro D A μ _ κ hκ a b hb hab M M' u hM' hMu hMM p hp k
  have h2 : IsUnit (2 : AE D) := by
    have := (IsUnit.mk0 (2 : D.host.E) two_ne_zero).map (incA D)
    rwa [map_ofNat] at this
  have hr : IsUnit (2 * (u : AE D) * cA D u) := (h2.mul u.isUnit).mul (u.isUnit.map (cA D))
  have hg := matHom_chart_conj A μ κ hκ (blkGL finSumFinEquiv (b, b) * M) p hp k
  have hMM' : ∀ w, (Formalism.UG.cT (cA D) M.1 * M.1).map (compInf D.host.F D.host.E w) =
      compInf D.host.F D.host.E w hr.unit • 1 := hMM
  have hσ : ∀ x, D.sp.cm.sig (D.sp.cm.sig x) = x := fun x => star_star x
  have key := mem_KAd_iff_of_conj (n := A.rank) D.sp.cm.sig hσ (dblSp A).gram (Jst D A.rank) (frameLat A) a b hb hab
    M M' u hr.unit (fun v i j => ⟨hM'.1 i j v, hM'.2 i j v⟩) hMu hMM' k (κ ((p : GA D (dblSp A))⁻¹ * k * p)) hg
  have e : K D A.rank = levelAll D.sp.cm.sig (Jst D A.rank) (stdLattice D.host.E (A.rank + A.rank)) 1 := rfl
  rw [e]
  exact key

end GlobalTheory.StdUnn.Conj

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselGroupHaarIsMulRightInvariant
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BesUnimod

theorem besGrp_isMulRightInvariant : ∀ (D : D7) (V V₀ A L : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (o : OrthDec V₀ A L)
    (μ : Measure (besGrp d o)), μ.IsHaarMeasure → μ.IsMulRightInvariant := by
  intro D V V₀ A L ρ d o μ hμ
  obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  obtain ⟨j1, j2, j3, j4, j5, j6, j7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D A
  obtain ⟨ν, 𝓝, hν⟩ := GlobalTheory.Per.UnitN.exists_isUnitN D V ρ d.e (isIsoSub_e d)
  obtain ⟨hνH, h𝓝, h𝓝1⟩ := hν
  have hNc : IsClosed (flagN d : Set (GA D V)) := GlobalTheory.Mem.TrueRecord.isClosed_NFlag V (isIsoSub_e d)
  let μA : Measure (GA D A) := Measure.haar
  have hHaar := ((GlobalTheory.MixPer.jacGrp_besGrp_haar D V V₀ A L ρ d o ν 𝓝 ⟨hνH, h𝓝, h𝓝1⟩).2.2 μA inferInstance)
  haveI : LocallyCompactSpace (flagN d) := hNc.locallyCompactSpace
  haveI : SecondCountableTopology (flagN d) := TopologicalSpace.Subtype.secondCountableTopology _
  have hinj : Function.Injective fun γ : NFlagQ V d.e => (⟨γ.1.1, γ.2⟩ : GQ V) :=
    fun a b h => Subtype.ext (Subtype.ext (congrArg (fun x : GQ V => (x : GA D V)) h))
  haveI : Countable (NFlagQ V d.e) := hinj.countable
  haveI : ν.IsMulRightInvariant :=
    GlobalTheory.SemiHaar.rightInv_of_fd (NFlagQ V d.e) ν h𝓝 (by rw [h𝓝1]; exact ENNReal.one_ne_top)
  haveI : μA.IsMulRightInvariant := GlobalTheory.AdelicPointsUnimod.isMulRightInvariant_of_isHaarMeasure D A μA inferInstance
  have hcA : Continuous (embA d o) := by
    have h1 : Continuous (fun h : GA D A => o.emb (h, 1)) := by
      have := o.continuous_emb
      fun_prop
    exact d.continuous_embed.comp h1
  have hnA : ∀ n ∈ flagN d, ∀ h, embA d o h * n * (embA d o h)⁻¹ ∈ flagN d := fun n hn h =>
    GlobalTheory.MixPer.witt_anisotropic_group_normalizes_flag_unipotent D V V₀ ρ d n hn (o.emb (h, 1))
  have hR := GlobalTheory.SemiHaar.semiMeas_rightInv (flagN d) (embA d o) hNc hcA hnA μA ν
  haveI : LocallyCompactSpace (besGrp d o) := by
    obtain ⟨e, -⟩ := GlobalTheory.SemiHaar.exists_homeo (flagN d) (embA d o) hnA hcA (GlobalTheory.BesProj.exists_continuous_proj D V V₀ A L ρ d o)
    exact e.symm.isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (besGrp d o) := TopologicalSpace.Subtype.secondCountableTopology _
  obtain ⟨κ, k1, k2⟩ : ∃ κ : Measure (besGrp d o), κ.IsHaarMeasure ∧ κ.IsMulRightInvariant := ⟨_, hHaar, hR⟩
  rw [Measure.isMulLeftInvariant_eq_smul μ κ]
  infer_instance

end GlobalTheory.BesUnimod
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselGroupSplitRealFinite
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BesSplit

theorem tens_ext {F E A B : Type} [Field F] [Field E] [Algebra F E] [CommRing A] [CommRing B] [Algebra F A]
    [Algebra F B] (z w : (A × B) ⊗[F] E)
    (h1 : Algebra.TensorProduct.map (AlgHom.fst F A B) (AlgHom.id F E) z =
      Algebra.TensorProduct.map (AlgHom.fst F A B) (AlgHom.id F E) w)
    (h2 : Algebra.TensorProduct.map (AlgHom.snd F A B) (AlgHom.id F E) z =
      Algebra.TensorProduct.map (AlgHom.snd F A B) (AlgHom.id F E) w) : z = w := by
  have hz : ∀ z : (A × B) ⊗[F] E, z = LinearMap.rTensor E (LinearMap.inl F A B)
        (Algebra.TensorProduct.map (AlgHom.fst F A B) (AlgHom.id F E) z) +
      LinearMap.rTensor E (LinearMap.inr F A B)
        (Algebra.TensorProduct.map (AlgHom.snd F A B) (AlgHom.id F E) z) := by
    intro z
    induction z with
    | zero => simp
    | tmul x y => simp [← TensorProduct.add_tmul]
    | add x y hx hy =>
      simp only [map_add]
      rw [add_add_add_comm, ← hx, ← hy]
  rw [hz z, hz w, h1, h2]

theorem entry_eq {R R₁ R₂ : Type} [CommRing R] [CommRing R₁] [CommRing R₂] (φ : R →+* R₁) (ψ : R →+* R₂)
    (hinj : ∀ z w, φ z = φ w → ψ z = ψ w → z = w) {n k m : ℕ} {M N K : Matrix (Fin n) (Fin n) R}
    (hi : M.map φ = N.map φ) (hf : M.map ψ = K.map ψ) (P : Matrix (Fin k) (Fin n) R) (Q : Matrix (Fin n) (Fin m) R)
    (i : Fin k) (j : Fin m) {c : R} (hN : (P * (N * Q)) i j = c) (hK : (P * (K * Q)) i j = c) :
    (P * (M * Q)) i j = c := by
  refine hinj _ _ ?_ ?_
  · have e : (P * (M * Q)).map φ = (P * (N * Q)).map φ := by
      rw [Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, hi]
    exact (congrFun (congrFun e i) j).trans (congrArg φ hN)
  · have e : (P * (M * Q)).map ψ = (P * (K * Q)).map ψ := by
      rw [Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, hf]
    exact (congrFun (congrFun e i) j).trans (congrArg ψ hK)

theorem mat_eq {R R₁ R₂ : Type} [CommRing R] [CommRing R₁] [CommRing R₂] (φ : R →+* R₁) (ψ : R →+* R₂)
    (hinj : ∀ z w, φ z = φ w → ψ z = ψ w → z = w) {n k m : ℕ} {M N K : Matrix (Fin n) (Fin n) R}
    (hi : M.map φ = N.map φ) (hf : M.map ψ = K.map ψ) (P : Matrix (Fin k) (Fin n) R) (Q : Matrix (Fin n) (Fin m) R)
    {C : Matrix (Fin k) (Fin m) R} (hN : P * (N * Q) = C) (hK : P * (K * Q) = C) : P * (M * Q) = C :=
  Matrix.ext fun i j => entry_eq φ ψ hinj hi hf P Q i j (congrFun (congrFun hN i) j) (congrFun (congrFun hK i) j)

variable {D : D7}

def realPart (D : D7) : AE D →+* Ainf D.host.F ⊗[D.host.F] D.host.E :=
  (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom

def finitePart (D : D7) : AE D →+* Af D.host.F ⊗[D.host.F] D.host.E :=
  (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom

theorem ext_parts (z w : AE D) (h1 : realPart D z = realPart D w) (h2 : finitePart D z = finitePart D w) : z = w :=
  tens_ext (A := Ainf D.host.F) (B := Af D.host.F) z w h1 h2

theorem map_real_eq {S : HSp D} {x y : GA D S} (h : infHom S x = infHom S y) :
    (Formalism.L2.Theta.mt S x).map (realPart D) = (Formalism.L2.Theta.mt S y).map (realPart D) := congrArg Units.val h

theorem map_finite_eq {S : HSp D} {x y : GA D S} (h : finHom S x = finHom S y) :
    (Formalism.L2.Theta.mt S x).map (finitePart D) = (Formalism.L2.Theta.mt S y).map (finitePart D) := congrArg Units.val h

set_option maxHeartbeats 2000000 in

theorem mem_besGrp_of_parts {S S₀ A L : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (o : OrthDec S₀ A L) {x y z : GA D S}
    (hi : infHom S x = infHom S y) (hf : finHom S x = finHom S z) (hy : y ∈ besGrp d o) (hz : z ∈ besGrp d o) :
    x ∈ besGrp d o := by
  have key : ∀ g : GA D S, g ∈ besGrp d o ↔ g ∈ jacGrp d ∧
      d.p0 ⬝ (Formalism.L2.Theta.mt S g ⬝ (d.j0 ⬝ o.jB)) = o.jB := fun g => by
    have e := Set.ext_iff.1 (GlobalTheory.BesClosed.besGrp_eq_inter d o) g
    rw [← Matrix.mul_assoc (Formalism.L2.Theta.mt S g), ← Matrix.mul_assoc]
    exact e
  have hi' := map_real_eq hi
  have hf' := map_finite_eq hf
  obtain ⟨hy1, hy2⟩ := (key y).1 hy
  obtain ⟨hz1, hz2⟩ := (key z).1 hz
  obtain ⟨hy3, hy4, hy5⟩ := (GlobalTheory.BesClosed.mem_jacGrp_iff_mat d y).1 hy1
  obtain ⟨hz3, hz4, hz5⟩ := (GlobalTheory.BesClosed.mem_jacGrp_iff_mat d z).1 hz1
  refine (key x).2 ⟨(GlobalTheory.BesClosed.mem_jacGrp_iff_mat d x).2 ⟨?_, ?_, fun i j => ⟨fun hji => ?_, ?_⟩⟩, ?_⟩
  · exact mat_eq (realPart D) (finitePart D) ext_parts hi' hf' _ _ hy3 hz3
  · exact mat_eq (realPart D) (finitePart D) ext_parts hi' hf' _ _ hy4 hz4
  · exact entry_eq (realPart D) (finitePart D) ext_parts hi' hf' _ _ i j ((hy5 i j).1 hji) ((hz5 i j).1 hji)
  · exact entry_eq (realPart D) (finitePart D) ext_parts hi' hf' _ _ i i (hy5 i j).2 (hz5 i j).2
  · exact mat_eq (realPart D) (finitePart D) ext_parts hi' hf' _ _ hy2 hz2

theorem besGrp_split : ∀ (D : D7) (V V₀ A L : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (o : OrthDec V₀ A L),
    ∀ a ∈ GinfC V, ∀ b ∈ GfC V, a * b ∈ besGrp d o → a ∈ besGrp d o ∧ b ∈ besGrp d o := by
  intro D V V₀ A L ρ d o a ha b hb hab
  have ha' : finHom V a = 1 := MonoidHom.mem_ker.1 ha
  have hb' : infHom V b = 1 := MonoidHom.mem_ker.1 hb
  exact ⟨mem_besGrp_of_parts d o (by rw [map_mul, hb', mul_one]) (by rw [ha', map_one]) hab (one_mem _),
    mem_besGrp_of_parts d o (by rw [hb', map_one]) (by rw [map_mul, ha', one_mul]) (one_mem _) hab⟩

end GlobalTheory.BesSplit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselPeriodLinearAndTranslationCombination
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSaw.TrcProof

variable {D : D7}

theorem contAut_add {V : HSp D} {f g : GA D V → ℂ} (hf : IsContAut V f) (hg : IsContAut V g) :
    IsContAut V (f + g) :=
  ⟨fun γ hγ x => by simp only [Pi.add_apply, hf.1 γ hγ x, hg.1 γ hγ x], hf.2.add hg.2⟩

theorem contAut_smul {V : HSp D} {f : GA D V → ℂ} (hf : IsContAut V f) (c : ℂ) : IsContAut V (c • f) :=
  ⟨fun γ hγ x => by simp only [Pi.smul_apply, hf.1 γ hγ x], hf.2.const_smul c⟩

theorem contAut_rTrans {V : HSp D} {f : GA D V → ℂ} (h : GA D V) (hf : IsContAut V f) : IsContAut V (rTrans h f) :=
  ⟨fun γ hγ x => by simp only [rTrans, mul_assoc, hf.1 γ hγ], hf.2.comp (continuous_mul_const h)⟩

theorem contAut_sum {V : HSp D} {I : Type} (s : Finset I) (a : I → ℂ) (f : I → GA D V → ℂ)
    (hf : ∀ i ∈ s, IsContAut V (f i)) : IsContAut V (∑ i ∈ s, a i • f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨fun _ _ _ => by simp, continuous_const⟩
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact contAut_add (contAut_smul (hf i (Finset.mem_insert_self i s)) (a i))
      (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

theorem per_sum_right {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {ρ : ℕ} (B : BesLev D ρ)
    {φ : GA D B.A → ℂ} (hφ : IsContAut B.A φ) {I : Type} (s : Finset I) (a : I → ℂ) (f : I → GA D B.V → ℂ)
    (hf : ∀ i ∈ s, IsContAut B.V (f i)) :
    B.per ψ φ (∑ i ∈ s, a i • f i) = ∑ i ∈ s, a i * B.per ψ φ (f i) := by
  have hconv := fun i (hi : i ∈ s) => PerSumProof.conv hψ B (hf i hi) hφ
  simp only [BesLev.per, besPer]
  have e1 : ∀ h n, besFun ψ 1 B.d B.o B.ζ φ (∑ i ∈ s, a i • f i) h n =
      ∑ i ∈ s, a i * besFun ψ 1 B.d B.o B.ζ φ (f i) h n := by
    intro h n
    simp only [besFun, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  simp_rw [e1]
  have e2 : (fun h => ∫ n in B.vN.𝓝, ∑ i ∈ s, a i * besFun ψ 1 B.d B.o B.ζ φ (f i) h n ∂B.vN.ν) =
      fun h => ∑ i ∈ s, a i * ∫ n in B.vN.𝓝, besFun ψ 1 B.d B.o B.ζ φ (f i) h n ∂B.vN.ν := by
    funext h
    rw [integral_finset_sum s fun i hi => ((hconv i hi).1 h).const_mul (a i)]
    exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _
  rw [e2, integral_finset_sum s fun i hi => (hconv i hi).2.const_mul (a i)]
  exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _

end GlobalTheory.SeeSaw.TrcProof

namespace GlobalTheory.SeeSaw

theorem per_linear_trc : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (ρ : ℕ) (B : BesLev D ρ) (φ : GA D B.A → ℂ), IsContAut B.A φ → (∀ (I : Type) (s : Finset I) (a : I → ℂ) (f : I → GA D B.V → ℂ), (∀ i ∈ s, IsContAut B.V (f i)) → B.per ψ φ (∑ i ∈ s, a i • f i) = ∑ i ∈ s, a i * B.per ψ φ (f i)) ∧ ∀ (e : GA D B.V →₀ ℂ) (f : GA D B.V → ℂ), IsContAut B.V f → IsContAut B.V (trc e f) ∧ B.per ψ φ (trc e f) = ∑ g ∈ e.support, e g * B.per ψ φ (rTrans g f) := by
  intro D ψ hψ ρ B φ hφ
  refine ⟨fun I s a f hf => TrcProof.per_sum_right hψ B hφ s a f hf, fun e f hf => ?_⟩
  have hT : ∀ g ∈ e.support, IsContAut B.V (rTrans g f) := fun g _ => TrcProof.contAut_rTrans g hf
  exact ⟨TrcProof.contAut_sum e.support e (fun g => rTrans g f) hT,
    TrcProof.per_sum_right hψ B hφ e.support e (fun g => rTrans g f) hT⟩

end GlobalTheory.SeeSaw

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselToJacobiFlatSchwartzLinear
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FlatLin

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

theorem mixS_add (hψ : IsStdChar D ψ (-1)) {S S₀ T : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (v : VolM D T.rank ρ)
    {f g : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (hg : IsThetaFunO ψ S T g) (x : Mx D T.rank ρ) :
    d.mixS T ψ v.μ v.𝓕 (f + g) x = d.mixS T ψ v.μ v.𝓕 f x + d.mixS T ψ v.μ v.𝓕 g x := by
  funext w
  have h := integral_add (d.integrableOn_mixS hψ.1.1 v.covol hf x w) (d.integrableOn_mixS hψ.1.1 v.covol hg x w)
  simp only [HypDec.mixS, Pi.add_apply, HypDec.integrandS_eq, mul_add] at h ⊢
  exact h

theorem cont_bdd_of_tame {Z : Type} [TopologicalSpace Z] {F : Z → ℂ}
    (t : GlobalTheory.Unf.EvalCont.Tame fun (_ : Unit) (q : Unit × Z) => F q.2) : Continuous F ∧ ∃ C : ℝ, ∀ w, ‖F w‖ ≤ C := by
  refine ⟨t.1.comp ((continuous_const (y := ())).prodMk ((continuous_const (y := ())).prodMk continuous_id)), ?_⟩
  obtain ⟨C', hC'⟩ := t.2 ()
  exact ⟨C', fun w => hC'.self_of_nhds ((), w)⟩

theorem mixS_cont_bdd (hψ : IsStdChar D ψ (-1)) {S S₀ T : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (v : VolM D T.rank ρ)
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (x : Mx D T.rank ρ) :
    Continuous (d.mixS T ψ v.μ v.𝓕 f x) ∧ ∃ C : ℝ, ∀ w, ‖d.mixS T ψ v.μ v.𝓕 f x w‖ ≤ C := by
  obtain ⟨C, hC⟩ := GlobalTheory.IsoMean.isThetaFunO_bounded S T ψ hψ f hf
  have t := GlobalTheory.Unf.EvalCont.tame_mixS (B := Unit) (Z := Unit) hψ d v x (F := fun _ _ => f)
    (GlobalTheory.Unf.EvalCont.tame_of_bounded (C := C) (hf.cont.comp continuous_snd.snd) fun _ q => hC q.2)
  exact cont_bdd_of_tame t

theorem integrableOn_mixT (hψ : IsStdChar D ψ (-1)) {S T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ) (v : VolM D ρ S.rank)
    {f : WO S T → ℂ} (hf : Continuous f ∧ ∃ C : ℝ, ∀ w, ‖f w‖ ≤ C) (y : Mx D S.rank ρ) (w₀ : WO S T₀) :
    IntegrableOn (fun ξ => ψ (symplOH S T (d.incX S ξ) (d.incAdj S y)) * f (d.incX S ξ + d.incAdj S y + d.inc0 S w₀))
      v.𝓕 v.μ := by
  obtain ⟨hc, C, hC⟩ := hf
  obtain ⟨j1, -⟩ := lattice_Mx D T.rank S.rank
  have : BorelSpace (Mx D ρ S.rank) := ⟨rfl⟩
  have : IsFiniteMeasure (v.μ.restrict v.𝓕) :=
    ⟨by rw [Measure.restrict_apply_univ, v.covol.2.2]; exact ENNReal.one_lt_top⟩
  have hY : Continuous (d.incX S) := continuous_const.matrix_mul continuous_id
  refine Integrable.of_bound (Continuous.aestronglyMeasurable ?_) C (.of_forall fun ξ => ?_)
  · exact (hψ.1.1.comp (GlobalTheory.OrientedHeis.continuous_symplOH hY continuous_const)).mul
      (hc.comp ((hY.add continuous_const).add continuous_const))
  · rw [norm_mul, hψ.1.2.1, one_mul]; exact hC _

theorem mixT_add (hψ : IsStdChar D ψ (-1)) {S T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ) (v : VolM D ρ S.rank)
    {f g : WO S T → ℂ} (hf : Continuous f ∧ ∃ C : ℝ, ∀ w, ‖f w‖ ≤ C) (hg : Continuous g ∧ ∃ C : ℝ, ∀ w, ‖g w‖ ≤ C)
    (y : Mx D S.rank ρ) :
    d.mixT S ψ v.μ v.𝓕 (f + g) y = d.mixT S ψ v.μ v.𝓕 f y + d.mixT S ψ v.μ v.𝓕 g y := by
  funext w
  have h := integral_add (integrableOn_mixT hψ d v hf y w) (integrableOn_mixT hψ d v hg y w)
  simp only [HypDec.mixT, Pi.add_apply, HypDec.integrandT_eq, mul_add]
  exact h

theorem evalAt_add (hψ : IsStdChar D ψ (-1)) {V V₀ W W₀ : HSp D} {ρ σ : ℕ} (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ)
    (vS : VolM D W.rank ρ) (vT : VolM D σ V₀.rank) {f g : WO V W → ℂ} (hf : IsThetaFunO ψ V W f)
    (hg : IsThetaFunO ψ V W g) (x : Mx D W.rank ρ) (y : Mx D V₀.rank σ) :
    GlobalTheory.MixPer.evalAt ψ dV dW vS.μ vS.𝓕 vT.μ vT.𝓕 (f + g) x y =
      GlobalTheory.MixPer.evalAt ψ dV dW vS.μ vS.𝓕 vT.μ vT.𝓕 f x y + GlobalTheory.MixPer.evalAt ψ dV dW vS.μ vS.𝓕 vT.μ vT.𝓕 g x y := by
  unfold GlobalTheory.MixPer.evalAt
  rw [mixS_add hψ dV vS hf hg, mixT_add hψ dW vT (mixS_cont_bdd hψ dV vS hf x) (mixS_cont_bdd hψ dV vS hg x)]

theorem flatAt_add (hF : FlatLaw D) (hψ : IsStdChar D ψ (-1)) {V V₀ W W₀ : HSp D} {ρ σ : ℕ} (dV : HypDec V V₀ ρ)
    (dW : HypDec W W₀ σ) (vS : VolM D W.rank ρ) (vT : VolM D σ V₀.rank) (vU : VolU D ρ)
    (x : Matrix (Fin W.rank) (Fin ρ) D.host.E) (hx : LinearIndependent D.host.E x.transpose) (y : Mx D V₀.rank σ)
    {f g : WO V W → ℂ} (hf : IsThetaFunO ψ V W f) (hg : IsThetaFunO ψ V W g) :
    GlobalTheory.MixPer.flatAt ψ dV dW vS.μ vS.𝓕 vT.μ vT.𝓕 vU.ν (rat x) y (f + g) =
      GlobalTheory.MixPer.flatAt ψ dV dW vS.μ vS.𝓕 vT.μ vT.𝓕 vU.ν (rat x) y f +
        GlobalTheory.MixPer.flatAt ψ dV dW vS.μ vS.𝓕 vT.μ vT.𝓕 vU.ν (rat x) y g := by
  funext w
  have h := integral_add ((hF ψ hψ V V₀ W W₀ ρ σ dV dW vS vT vU x hx y f hf).1 w)
    ((hF ψ hψ V V₀ W W₀ ρ σ dV dW vS vT vU x hx y g hg).1 w)
  rw [Pi.add_apply, GlobalTheory.MixPer.flatAt, GlobalTheory.MixPer.flatAt, GlobalTheory.MixPer.flatAt, ← h]
  congr 1
  funext u
  simp only [GlobalTheory.MixPer.flatFun, evalAt_add hψ dV dW vS vT hf hg, Pi.add_apply, mul_add]

theorem flatBF_linear : ∀ (D : D7), FlatLaw D → ∀ (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (st : StepBF ψ B J) (f g : WO B.V J.W → ℂ) (a : ℂ), IsThetaFunO ψ B.V J.W f → IsThetaFunO ψ B.V J.W g → flatBF st (f + g) = flatBF st f + flatBF st g ∧ flatBF st (a • f) = a • flatBF st f := by
  intro D hF ψ ρ B J st f g a hf hg
  exact ⟨flatAt_add hF st.weil.std B.d J.d st.vS st.vT st.vU J.d.e (isIsoSub_e J.d).1 _ hf hg,
    GlobalTheory.HandHom.flatBF_smul st a f⟩

end GlobalTheory.FlatLin

end
end

