import Formalism.SharpRestriction.GlobalSchurBounds.LinkMin
import Formalism.LocalToGlobal.GlobalTheory.GL6.Bundle0004
import Formalism.LocalToGlobal.HermitianForms.TiedSym
import Formalism.LocalToGlobal.GlobalTheory.GL4.Statement
import Formalism.LocalToGlobal.GlobalTheory.GL4.Bundle0016
import Formalism.LocalToGlobal.HermitianForms.Bundle0006
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.PartFiveExplicitOfPropositions
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0003
import Formalism.LocalToGlobal.GlobalTheory.GL5.TheoremThreeAllUnitary
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.Bundle0004
import Formalism.SharpRestriction.CuspSpanNormBounds.NonemptyParameterModels.NumericSettingWithGapSatisfiable

-- bundled from Formalism.SharpRestriction.GlobalSchurBounds.IntegralityOfRationalityLocal
section
noncomputable section

namespace Formalism.MainNotions.RT

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.GlobalTheoryTheory

variable (D : D7) (u : D.what₂.Word)

variable {D u} in

def ChiFin0 {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i} (T : Formalism.L2.Forms.FormsTiedSym D u Ch chOf) : Prop :=
  ∃ n : ℕ, 0 < n ∧ ∀ x : (T.cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.U,
    ((((T.cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.chi x : ℂˣ) : ℂ)) ^ n = 1 ∧
      ∃ r : D.what₂.LL, D.what₂.embLL r = (((T.cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.chi x : ℂˣ) : ℂ)

def FormsTwistCompatibilityFamily : Prop :=
  ∃ (Ch : ℕ → Type) (chOf : ∀ i, (D.mem u).C.cls i → Ch i) (T : Formalism.L2.Forms.FormsTiedSym D u Ch chOf), ChiFin0 T

def FiSt0 : Prop :=
  ∀ v, ∀ φ ∈ (D.fm u).Fi 0, Uop D u 0 v φ ∈ (D.fm u).Fi 0 ∧ Dop D u 0 v φ ∈ (D.fm u).Fi 0

def CrossDia0 : Prop :=
  ∀ v v', v ≠ v' → ∀ φ ∈ (D.fm u).Fi 0, ∀ a,
    dia D u 0 v' a (Uop D u 0 v φ) = Uop D u 0 v (dia D u 0 v' a φ) ∧
    dia D u 0 v' a (Dop D u 0 v φ) = Dop D u 0 v (dia D u 0 v' a φ)

def UnfAll0 : Prop := ∀ v, Nonempty (Unf D u 0 v)

def FiSt0T : Prop := FormsTwistCompatibilityFamily D u → admS D u → HidaSetting D u → FiSt0 D u

def CrossDia0T : Prop := FormsTwistCompatibilityFamily D u → admS D u → HidaSetting D u → CrossDia0 D u

def UnfAll0T : Prop := FormsTwistCompatibilityFamily D u → admS D u → HidaSetting D u → UnfAll0 D u

def IntegralityLevelZeroUnderForms : Prop := FormsTwistCompatibilityFamily D u → admS D u → HidaSetting D u → LocalLatticeBases.HeckeIntegralLevelZero D u

variable {D u}

theorem ramified_lines_of_level_zero (hF : FiSt0 D u) (hX : CrossDia0 D u) (hU : UnfAll0 D u) : LocalLatticeBases.HeckeRamifiedLevelZero D u := by
  intro v φ hφ
  have hφ' : φ ∈ (D.fm u).Fi 0 ∧ ∀ v', Nm D u 0 v' φ = 0 := by
    simpa only [MramI, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker] using hφ
  obtain ⟨hFi, hN⟩ := hφ'
  obtain ⟨H⟩ := hU v
  obtain ⟨hUF, hDF⟩ := hF v φ hFi
  have hpass : ∀ v', v' ≠ v → ∀ f : Fn D u 0 →ₗ[ℂ] Fn D u 0,
      (∀ a, dia D u 0 v' a (f φ) = f (dia D u 0 v' a φ)) → Nm D u 0 v' (f φ) = 0 := by
    intro v' _ f hf
    have h : Nm D u 0 v' (f φ) = f (Nm D u 0 v' φ) := by
      simp only [Nm, LinearMap.sum_apply, map_sum, hf]
    rw [h, hN v', map_zero]
  have memR : ∀ ψ, ψ ∈ (D.fm u).Fi 0 → (∀ v', Nm D u 0 v' ψ = 0) → ψ ∈ MramI D u 0 := by
    intro ψ h1 h2
    simp only [MramI, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker]
    exact ⟨h1, h2⟩
  refine ⟨memR _ hUF fun v' => ?_, memR _ hDF fun v' => ?_, H.UD_ram hFi (hN v) hDF⟩
  · by_cases h : v' = v
    · subst h
      exact H.Nm_U hFi (hN _) hUF
    · exact hpass v' h _ fun a => (hX v v' (Ne.symm h) φ hFi a).1
  · by_cases h : v' = v
    · subst h
      exact H.Nm_D hFi (hN _) hDF
    · exact hpass v' h _ fun a => (hX v v' (Ne.symm h) φ hFi a).2

theorem integrality_of_rationality_local (h : IntAtT D u) : LocalLatticeBases.HeckeIntegralLevelZero D u :=
  fun w hw hs v => h 0 (Nat.zero_le _) w hw hs v

variable {eps : ℝ}

theorem hI_tied (Fm : FamP eps) (tie : FamU Fm fun D u => FormsTwistCompatibilityFamily D u ∧ admS D u)
    (hI : ∀ (D : D7) (u : D.what₂.Word), IntegralityLevelZeroUnderForms D u) : FamU Fm LocalLatticeBases.HeckeIntegralLevelZero := by
  obtain ⟨x0, hx0⟩ := tie
  refine ⟨x0, fun x hx hx1 i u hs => ?_⟩
  obtain ⟨hT, hA⟩ := hx0 x hx hx1 i u hs
  exact hI _ _ hT hA hs

theorem hR_tied (Fm : FamP eps) (tie : FamU Fm fun D u => FormsTwistCompatibilityFamily D u ∧ admS D u)
    (hF : ∀ (D : D7) (u : D.what₂.Word), FiSt0T D u) (hX : ∀ (D : D7) (u : D.what₂.Word), CrossDia0T D u)
    (hU : ∀ (D : D7) (u : D.what₂.Word), UnfAll0T D u) : FamU Fm LocalLatticeBases.HeckeRamifiedLevelZero := by
  obtain ⟨x0, hx0⟩ := tie
  refine ⟨x0, fun x hx hx1 i u hs => ?_⟩
  obtain ⟨hT, hA⟩ := hx0 x hx hx1 i u hs
  exact ramified_lines_of_level_zero (hF _ _ hT hA hs) (hX _ _ hT hA hs) (hU _ _ hT hA hs)

end Formalism.MainNotions.RT

end
end

-- bundled from Formalism.SharpRestriction.GlobalSchurBounds.LinkGLOBAL7Tied4
section
noncomputable section

namespace Formalism.MainNotions.RT

open Formalism.BasicNotions Formalism.MainNotions.Lnk Formalism.MainNotions.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory

def tCVTies {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, Nonempty (Formalism.L2.Forms.ColsTiedSym (Fm.D x i)) ∧ flipTwoThree.adm3 (Fm.D x i)

def ColumnValuationFromTwistCompatibility : Prop :=
  ∀ D : D7, Formalism.L2.Forms.ColsTiedSym D → flipTwoThree.adm3 D → ∀ u : D.what₂.Word, Nonempty (flipTwoThree.ColVal D u)

theorem tCV_of_tied {eps : ℝ} (Fm : FamP eps) (hCV : ColumnValuationFromTwistCompatibility) (hT : tCVTies Fm) :
    ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (i : Fm.Ix x) u, Nonempty (flipTwoThree.ColVal (Fm.D x i) u) := by
  unfold tCVTies at hT
  obtain ⟨x0, hx⟩ := hT
  refine ⟨x0, fun x hx0 i u => ?_⟩
  obtain ⟨⟨t⟩, ha⟩ := hx x hx0 i
  exact hCV _ t ha u

end Formalism.MainNotions.RT
end
end

-- bundled from Formalism.SharpRestriction.GlobalSchurBounds.MassRatioUnfoldedOfTheoremTwo
section
noncomputable section

namespace Formalism.MainNotions.RT

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Lnk Formalism.MainNotions.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory

def MassRatioUnderVolume (D : D7) : Prop := StandardLattice.VolTie D → StandardLattice.VolumeRatio₂ D

def GenusMassUnderVolume (D : D7) : Prop := StandardLattice.VolTie D → StandardLattice.DefiniteVolumeEqMass D

theorem mass_ratio_unfolded_of_theorem_two (D : D7) (h : StandardLattice.Conclusion2 D) : StandardLattice.VolumeRatio₂ D := by
  let _ := D.host.cmStar
  intro W P Q hS hsig hr s hs
  obtain ⟨x, hx, W', ι, h1, h2, h3, h4, h5⟩ := h W P Q hS hsig hr s hs
  refine ⟨x, hx, W', ι, h1, h2, h3, h4, ?_⟩
  have key := Formalism.HermitianLattices.GenusMassVolumes.global_arithmetic_identity D.R.f W.rank D.host.v (Formalism.HermitianLatticesTheory.lValEta D.host.E W.rank)
    (by omega) (StandardLattice.host_v_pos D) (StandardLattice.lVal_pos D _ (by omega))
  rw [StandardLattice.mass_ratio_eq] at h5
  have e : D.vol W / D.vol W' =
      (((2 * Real.pi) ^ W.rank / ((W.rank - 1).factorial : ℝ)) ^ D.R.f *
        ((2 * D.host.v) ^ D.R.f) ^ ((1 : ℝ) / 2 - W.rank) / Formalism.HermitianLatticesTheory.lValEta D.host.E W.rank)⁻¹ :=
    h5.trans key.symm
  calc D.vol W' / D.vol W = (D.vol W / D.vol W')⁻¹ := (inv_div _ _).symm
    _ = _ := by rw [e, inv_inv]

theorem mass_ratio_unfolded_iff (D : D7) : StandardLattice.VolumeRatio₂ D ↔ StandardLattice.Conclusion2 D :=
  ⟨StandardLattice.volumeMass_of_unfolding D, mass_ratio_unfolded_of_theorem_two D⟩

theorem mass_ratio_of_true_volume_ratio (D : D7) (hV : Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.VolRatioTrue D) : MassRatioUnderVolume D := by
  intro hT
  refine mass_ratio_unfolded_of_theorem_two D ?_
  intro W P Q hW hs hr s hsP
  obtain ⟨x, hx, W', ι, hι, hrg, hW', hs', hrat⟩ := hV W P Q hW hs hr s hsP
  refine ⟨x, hx, W', ι, hι, hrg, hW', hs', ?_⟩
  have hs'' : ∀ τ, W'.sig τ = ((if s then P - 1 else P), (if s then Q else Q - 1)) := by
    intro τ
    rw [hs' τ]
    cases s <;> simp
  obtain ⟨⟨μ, hμ⟩, h1⟩ := hT W P Q hW hs
  obtain ⟨⟨𝓕, h𝓕⟩, h2⟩ := h1 μ hμ
  obtain ⟨⟨μ', hμ'⟩, h1'⟩ := hT W' _ _ hW' hs''
  obtain ⟨⟨𝓕', h𝓕'⟩, h2'⟩ := h1' μ' hμ'
  have e1 : μ 𝓕 = ENNReal.ofReal (D.vol W) := h2 𝓕 h𝓕
  have e2 : μ' 𝓕' = ENNReal.ofReal (D.vol W') := h2' 𝓕' h𝓕'
  have e := hrat μ 𝓕 μ' 𝓕' hμ h𝓕 hμ' h𝓕'
  rw [e1, e2, ENNReal.toReal_ofReal (D.vol_pos W).le, ENNReal.toReal_ofReal (D.vol_pos W').le] at e
  exact e

theorem genus_mass_of_class_decomposition (D : D7) (hG : Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.GenusMassStd D)
    (hC : Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.DefClassDecomp D) : GenusMassUnderVolume D :=
  fun hT => Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.mass_volume_identity_of_class_decomp D hT hG hC

theorem auxb_of_massRatio_of_genusMass_of_volTie (D : D7) (hU : MassRatioUnderVolume D) (hv : GenusMassUnderVolume D) (hT : StandardLattice.VolTie D) : StandardLattice.MassRatio₂ D :=
  StandardLattice.massRatio_of_definiteVolume D (StandardLattice.volumeMass_of_unfolding D (hU hT)) (hv hT)

theorem volumeY0EqualsMass_of_massRatio_of_genusMass (D : D7) (hU : MassRatioUnderVolume D) (hv : GenusMassUnderVolume D) (hT : StandardLattice.VolTie D) : StandardLattice.BaseVolumeEqualsMass D :=
  StandardLattice.volumeY0EqualsMass_of_aux2v D (StandardLattice.volume_eq_mass_of_definite D (StandardLattice.volumeMass_of_unfolding D (hU hT)) (hv hT))

theorem volTie_of_realTied (D : D7) (h : Formalism.L2.Theta.RealTied D) : StandardLattice.VolTie D := by
  intro W P Q hW hs
  have hv := h.vol W hW
  simp only [hs] at hv
  exact hv

variable {eps : ℝ}

theorem mass_ratio_family_of_volume (Fm : FamP eps) (hU : ∀ D, MassRatioUnderVolume D) (hv : ∀ D, GenusMassUnderVolume D)
    (tVol : flipTwoThree.fam0 Fm StandardLattice.VolTie) : flipTwoThree.fam0 Fm StandardLattice.MassRatio₂ := by
  obtain ⟨x0, hx⟩ := tVol
  exact ⟨x0, fun x h1 h2 i => auxb_of_massRatio_of_genusMass_of_volTie _ (hU _) (hv _) (hx x h1 h2 i)⟩

theorem volume_mass_family_of_volume (Fm : FamP eps) (hU : ∀ D, MassRatioUnderVolume D) (hv : ∀ D, GenusMassUnderVolume D)
    (tVol : flipTwoThree.fam0 Fm StandardLattice.VolTie) : flipTwoThree.fam0 Fm StandardLattice.BaseVolumeEqualsMass := by
  obtain ⟨x0, hx⟩ := tVol
  exact ⟨x0, fun x h1 h2 i => volumeY0EqualsMass_of_massRatio_of_genusMass _ (hU _) (hv _) (hx x h1 h2 i)⟩

theorem tVol_of_real (Fm : FamP eps) (h : flipTwoThree.fam0 Fm Formalism.L2.Theta.RealTied) : flipTwoThree.fam0 Fm StandardLattice.VolTie := by
  obtain ⟨x0, hx⟩ := h
  exact ⟨x0, fun x h1 h2 i => volTie_of_realTied _ (hx x h1 h2 i)⟩

theorem linkGLOBAL7_tiedV (Fm : FamP eps) (Cabs CH C0 C5 : ℝ) (hCabs : 0 ≤ Cabs) (hCH : 0 < CH) (hC0 : 3 ≤ C0)
    (hU : ∀ D, MassRatioUnderVolume D) (hv : ∀ D, GenusMassUnderVolume D) (tVol : flipTwoThree.fam0 Fm StandardLattice.VolTie)
    (h3 : flipTwoThree.fam0 Fm StandardLattice.SigmaDegreeTwoSidedBoundOfGap)
    (hZa : flipTwoThree.FamilySlopeLowerOpenPart Fm) (hZb : flipTwoThree.FamilySlopeMaxOpenPart Fm C5)
    (tCV : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (i : Fm.Ix x) u, Nonempty (flipTwoThree.ColVal (Fm.D x i) u))
    (hW : FamU Fm fun D u => Nonempty (product_first_zeroth_parts.FreeT D u)) (hμ : FamU Fm product_first_zeroth_parts.SlopeLine)
    (hI : FamU Fm LocalLatticeBases.HeckeIntegralLevelZero) (hR : FamU Fm LocalLatticeBases.HeckeRamifiedLevelZero) (hB : FamU Fm LocalLatticeBases.SecondBranchInclusionLength) :
    TuSize Fm → LinkGLOBAL7 Fm Cabs CH C0 Cabs 0 := by
  exact linkGLOBAL7_min Fm Cabs CH C0 C5 hCabs hCH hC0 (mass_ratio_family_of_volume Fm hU hv tVol) (volume_mass_family_of_volume Fm hU hv tVol) h3
    hZa hZb tCV hW hμ hI hR hB

end Formalism.MainNotions.RT

end
end

-- bundled from Formalism.SharpRestriction.GlobalSchurBounds.TheoremThreeUnderScaleOfGeneral
section
noncomputable section

namespace Formalism.MainNotions.RT

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S MeasureTheory Matrix

def DiscreteSeriesDegreeBoundsOfScaleAgreement (D : D7) : Prop := cdScaleTie D → StandardLattice.DiscreteSeriesDegreeBoundsOfGap D

def DsigExT (D : D7) : Prop := dsigTie D → StandardLattice.DsigEx D

def cdScaleTieR (cd : CDHaar) (s : (n : ℕ) → (Fin n → Bool) → NNReal) : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (P Q : ℕ) (e : Fin P ⊕ Fin Q ≃ Fin n),
    (∀ i, ε (e (Sum.inl i)) = true) → (∀ j, ε (e (Sum.inr j)) = false) →
    ∀ A : Set (Formalism.REAL.UJ ε), MeasurableSet A →
      ((s n ε : ENNReal) • Formalism.REAL.muG ε) A =
        cd.cd P Q {g | ∃ a ∈ A, umat a = Matrix.reindex e e (Formalism.BasicNotions.UpqT.mat g)}

theorem cdScaleTie_iff (D : D7) : cdScaleTie D ↔ cdScaleTieR D.cd D.s.cdScale := Iff.rfl

def DiscreteSeriesDegreeBoundsAtScale (s : (n : ℕ) → (Fin n → Bool) → NNReal) : Prop :=
  ∀ (N : ℕ) (ε : Fin N → Bool) (lam : Fin N → ℝ) (ep0 h0 : ℝ) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (σ : Matrix (Fin N) (Fin N) ℂ → (H →L[ℂ] H)) (w : H),
    let p : ℝ := (Finset.univ.filter (fun a => ε a = true)).card
    let q : ℝ := (Finset.univ.filter (fun a => ε a = false)).card
    1 ≤ p → 1 ≤ q →
    Formalism.QuantumDeterminants.IsHCParam lam → Formalism.QuantumDeterminants.GapAtLeast ε lam h0 →
    Real.exp (-(N : ℝ)) ≤ ep0 → ep0 < 1 / 2 →
    8192 * min p q * (p * q) ^ 3 * Real.log N / ep0 ^ 2 ≤ h0 →
    IsDS ε lam σ → w ≠ 0 →
    (1 - ep0) * Formalism.QuantumDeterminants.fdegHC lam ≤ fdegOf ((s N ε : ENNReal) • Formalism.REAL.muG ε) σ w ∧
    fdegOf ((s N ε : ENNReal) • Formalism.REAL.muG ε) σ w ≤
      4 * (Module.finrank ℂ (lowKSub ε lam σ) : ℝ) * (3 * p * q * StandardLattice.lamAbs lam) ^ (p * q)

theorem theorem_three_explicit_iff_scale (D : D7) : StandardLattice.DiscreteSeriesDegreeBoundsOfGap D ↔ DiscreteSeriesDegreeBoundsAtScale D.s.cdScale := Iff.rfl

def HCFdegR : Prop :=
  ∀ (cd : CDHaar) (s : (n : ℕ) → (Fin n → Bool) → NNReal), cdScaleTieR cd s →
  ∀ (N : ℕ) (ε : Fin N → Bool) (lam : Fin N → ℝ), Formalism.QuantumDeterminants.IsHCParam lam →
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      (σ : Matrix (Fin N) (Fin N) ℂ → (H →L[ℂ] H)) (w : H), IsDS ε lam σ → w ≠ 0 →
      fdegOf ((s N ε : ENNReal) • Formalism.REAL.muG ε) σ w = Formalism.QuantumDeterminants.fdegHC lam

theorem hcFormalDegree_of_R (h : HCFdegR) (D : D7) : Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.HCFormalDegree D := fun hT => h D.cd D.s.cdScale ((cdScaleTie_iff D).mp hT)

def DiscreteSeriesDegreeBoundsAllScales : Prop :=
  ∀ (cd : CDHaar) (s : (n : ℕ) → (Fin n → Bool) → NNReal), cdScaleTieR cd s → DiscreteSeriesDegreeBoundsAtScale s

theorem finrank_lowK_eq (hW : DiscreteSeriesWeylDimension.WeylForK) (hL : DiscreteSeriesWeylDimension.LowKMultOne) {N : ℕ} (ε : Fin N → Bool)
    (lam : Fin N → ℝ) (hlam : Formalism.QuantumDeterminants.IsHCParam lam) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin N) (Fin N) ℂ → (H →L[ℂ] H)) (hDS : IsDS ε lam σ) :
    ((Module.finrank ℂ (lowKSub ε lam σ) : ℕ) : ℝ) = StandardLattice.dTau ε lam := by
  obtain ⟨-, -, hURep, -, -, ⟨S, hS⟩, -⟩ := id hDS
  have hsub : lowKSub ε lam σ = S := by
    apply le_antisymm
    · exact sSup_le fun S' hS' => (hL N ε lam H σ hlam hDS S' S hS' hS).le
    · exact le_sSup hS
  have hKsub : Formalism.REAL.Kset ε ⊆ UJset ε := by
    intro g hg
    obtain ⟨hu, hc⟩ := hg
    show Formalism.REAL.inUJ ε g
    unfold Formalism.REAL.inUJ
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at hu
    rw [Matrix.mul_assoc, ← hc, ← Matrix.mul_assoc, hu, Matrix.one_mul]
  have hU : IsURepOn (Formalism.REAL.Kset ε) σ := by
    obtain ⟨⟨h1, hmul⟩, hnorm, hcont⟩ := hURep
    unfold IsURepOn Formalism.QuantumDeterminants.IsCRepOn
    exact ⟨⟨h1, fun a ha b hb => hmul a (hKsub ha) b (hKsub hb)⟩, fun g hg v => hnorm g (hKsub hg) v,
      fun v => (hcont v).mono hKsub⟩
  have hrho : ∀ a, (Formalism.QuantumDeterminants.lowK ε lam + Formalism.REAL.rhoC ε) a = lam a + StandardLattice.rhoN ε a := by
    intro a
    have e : Formalism.REAL.rhoN ε a = StandardLattice.rhoN ε a := rfl
    simp only [Formalism.QuantumDeterminants.lowK, Pi.add_apply, Pi.sub_apply]
    rw [e]
    ring
  rw [hsub, hW N ε (Formalism.QuantumDeterminants.lowK ε lam) H σ S hU hS]
  unfold StandardLattice.dTau
  simp only [hrho]
  rfl

theorem theorem_three_at_scale_of_degree (s : (n : ℕ) → (Fin n → Bool) → NNReal)
    (hf : ∀ (N : ℕ) (ε : Fin N → Bool) (lam : Fin N → ℝ), Formalism.QuantumDeterminants.IsHCParam lam →
      ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
        (σ : Matrix (Fin N) (Fin N) ℂ → (H →L[ℂ] H)) (w : H), IsDS ε lam σ → w ≠ 0 →
        fdegOf ((s N ε : ENNReal) • Formalism.REAL.muG ε) σ w = Formalism.QuantumDeterminants.fdegHC lam)
    (hW : DiscreteSeriesWeylDimension.WeylForK) (hL : DiscreteSeriesWeylDimension.LowKMultOne) : DiscreteSeriesDegreeBoundsAtScale s := by
  unfold DiscreteSeriesDegreeBoundsAtScale
  intro N ε lam ep0 h0 H _ _ σ w p q hp hq hlam _ hep hep2 _ hDS hw
  have hF := hf N ε lam hlam H σ w hDS hw
  have hK := finrank_lowK_eq hW hL ε lam hlam σ hDS
  rw [hF, hK]
  have hFn : 0 ≤ Formalism.QuantumDeterminants.fdegHC lam := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.fdegHC_nonneg lam hlam
  have hep0 : 0 < ep0 := lt_of_lt_of_le (Real.exp_pos _) hep
  refine ⟨by nlinarith [mul_nonneg hep0.le hFn], ?_⟩
  have hp' : p = (StandardLattice.nPlus ε : ℝ) := rfl
  have hq' : q = (StandardLattice.nMinus ε : ℝ) := rfl
  have hdT : 0 ≤ StandardLattice.dTau ε lam := by rw [← hK]; exact Nat.cast_nonneg _
  have hN : 2 ≤ N := by
    have h1r : (1 : ℝ) ≤ ((Finset.univ.filter (fun a => ε a = true)).card : ℝ) := hp
    have h2r : (1 : ℝ) ≤ ((Finset.univ.filter (fun a => ε a = false)).card : ℝ) := hq
    have h1 : 1 ≤ (Finset.univ.filter (fun a => ε a = true)).card := by exact_mod_cast h1r
    have h2 : 1 ≤ (Finset.univ.filter (fun a => ε a = false)).card := by exact_mod_cast h2r
    obtain ⟨a, ha⟩ := Finset.card_pos.mp (by omega : 0 < (Finset.univ.filter (fun a => ε a = true)).card)
    obtain ⟨b, hb⟩ := Finset.card_pos.mp (by omega : 0 < (Finset.univ.filter (fun a => ε a = false)).card)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    have hab : a.val ≠ b.val := by
      intro h
      have : a = b := Fin.ext h
      rw [this, hb] at ha
      exact Bool.noConfusion ha
    have := a.isLt
    have := b.isLt
    omega
  have hL1 := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.lamAbs_ge_one lam hlam hN
  have hle := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.fdegHC_le_dTau ε lam hlam
  have hpq : p * q = ((StandardLattice.nPlus ε * StandardLattice.nMinus ε : ℕ) : ℝ) := by rw [hp', hq']; push_cast; ring
  rw [hpq, Real.rpow_natCast]
  have h3 : (1 : ℝ) ≤ 3 * p * q := by nlinarith
  have hbase : StandardLattice.lamAbs lam ≤ 3 * p * q * StandardLattice.lamAbs lam := by
    have := mul_le_mul_of_nonneg_right h3 (show (0 : ℝ) ≤ StandardLattice.lamAbs lam by linarith)
    linarith
  have hpow : StandardLattice.lamAbs lam ^ (StandardLattice.nPlus ε * StandardLattice.nMinus ε) ≤
      (3 * p * q * StandardLattice.lamAbs lam) ^ (StandardLattice.nPlus ε * StandardLattice.nMinus ε) := by
    gcongr <;> linarith
  have hnn : 0 ≤ StandardLattice.dTau ε lam * (3 * p * q * StandardLattice.lamAbs lam) ^ (StandardLattice.nPlus ε * StandardLattice.nMinus ε) :=
    mul_nonneg hdT (pow_nonneg (by linarith) _)
  calc Formalism.QuantumDeterminants.fdegHC lam ≤ StandardLattice.dTau ε lam * StandardLattice.lamAbs lam ^ (StandardLattice.nPlus ε * StandardLattice.nMinus ε) := hle
    _ ≤ StandardLattice.dTau ε lam * (3 * p * q * StandardLattice.lamAbs lam) ^ (StandardLattice.nPlus ε * StandardLattice.nMinus ε) :=
        mul_le_mul_of_nonneg_left hpow hdT
    _ ≤ 4 * StandardLattice.dTau ε lam * (3 * p * q * StandardLattice.lamAbs lam) ^ (StandardLattice.nPlus ε * StandardLattice.nMinus ε) := by
        nlinarith

theorem explicit_bound_all_scales_of_formal_degree (hHC : HCFdegR) (hW : DiscreteSeriesWeylDimension.WeylForK) (hL : DiscreteSeriesWeylDimension.LowKMultOne) : DiscreteSeriesDegreeBoundsAllScales := fun cd s hs => theorem_three_at_scale_of_degree s (hHC cd s hs) hW hL

theorem theorem_three_under_scale_of_general (h : DiscreteSeriesDegreeBoundsAllScales) (D : D7) : DiscreteSeriesDegreeBoundsOfScaleAgreement D := fun hT => (theorem_three_explicit_iff_scale D).mpr (h D.cd D.s.cdScale ((cdScaleTie_iff D).mp hT))

theorem theorem_three_under_scale_of_degree (D : D7) (hHC : Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.HCFormalDegree D) (hW : DiscreteSeriesWeylDimension.WeylForK)
    (hL : DiscreteSeriesWeylDimension.LowKMultOne) : DiscreteSeriesDegreeBoundsOfScaleAgreement D := fun hT => (theorem_three_explicit_iff_scale D).mpr (theorem_three_at_scale_of_degree D.s.cdScale (hHC hT) hW hL)

theorem dsigExT_of (D : D7) (hE : DiscreteSeriesWeylDimension.DiscreteSeriesExists) : DsigExT D := by
  intro hT
  unfold StandardLattice.DsigEx
  intro τ
  unfold dsigTie at hT
  obtain ⟨H, i1, i2, σ, hσ⟩ := hE _ (epsSH D.R) (lamSH D.R (D.hc τ))
    (Formalism.MainNotions.S.Inh.obj_isHCParam_lamSH D.R (D.hc τ))
  obtain ⟨hC, -⟩ := id hσ
  obtain ⟨d, hd⟩ := Formalism.MainNotions.BridgeCSchur.fdeg_of_DS _ σ hσ
  have hc := D.s.cdScale_pos (2 * D.R.rS + D.R.k + 1) (epsSH D.R)
  have h3 := Formalism.MainNotions.StandardLattice.isFormalDegree_smul_measure _ σ d _ hc hd
  have h4 := hT τ H σ _ hσ h3
  refine ⟨H, i1, i2, σ, hσ, ?_⟩
  rw [← h4]
  exact h3

variable {eps : ℝ}

theorem fam0_theoremThreeSigmaExplicit_of_weyl (Fm : FamP eps) (h3 : ∀ D, DiscreteSeriesDegreeBoundsOfScaleAgreement D) (hDs : ∀ D, DsigExT D) (hW : DiscreteSeriesWeylDimension.WeylForK)
    (hL : DiscreteSeriesWeylDimension.LowKMultOne) : flipTwoThree.fam0 Fm StandardLattice.SigmaDegreeTwoSidedBoundOfGap := by
  refine ⟨0, fun x _ _ i => ?_⟩
  have ht := Fm.ties x i
  exact StandardLattice.theorem_three_sigma_holds _ (h3 _ ht.cdScale_tie) (DiscreteSeriesWeylDimension.lowest_K_type_count_of_weyl _ hW hL) (hDs _ ht.dsig_tie)

theorem linkGLOBAL7_tied3 (Fm : FamP eps) (Cabs CH C0 C5 : ℝ) (hCabs : 0 ≤ Cabs) (hCH : 0 < CH) (hC0 : 3 ≤ C0)
    (h2b : flipTwoThree.fam0 Fm StandardLattice.MassRatio₂) (h2v : flipTwoThree.fam0 Fm StandardLattice.BaseVolumeEqualsMass)
    (h3 : ∀ D, DiscreteSeriesDegreeBoundsOfScaleAgreement D) (hDs : ∀ D, DsigExT D) (hWK : DiscreteSeriesWeylDimension.WeylForK) (hLK : DiscreteSeriesWeylDimension.LowKMultOne)
    (hZa : flipTwoThree.FamilySlopeLowerOpenPart Fm) (hZb : flipTwoThree.FamilySlopeMaxOpenPart Fm C5)
    (tCV : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (i : Fm.Ix x) u, Nonempty (flipTwoThree.ColVal (Fm.D x i) u))
    (hW : FamU Fm fun D u => Nonempty (product_first_zeroth_parts.FreeT D u)) (hμ : FamU Fm product_first_zeroth_parts.SlopeLine)
    (hI : FamU Fm Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.HeckeIntegralLevelZero) (hR : FamU Fm Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.HeckeRamifiedLevelZero) (hB : FamU Fm Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.SecondBranchInclusionLength) :
    TuSize Fm → LinkGLOBAL7 Fm Cabs CH C0 Cabs 0 :=
  linkGLOBAL7_min Fm Cabs CH C0 C5 hCabs hCH hC0 h2b h2v (fam0_theoremThreeSigmaExplicit_of_weyl Fm h3 hDs hWK hLK) hZa hZb tCV hW hμ hI hR hB

theorem linkGLOBAL7_tied3src (Fm : FamP eps) (Cabs CH C0 C5 : ℝ) (hCabs : 0 ≤ Cabs) (hCH : 0 < CH) (hC0 : 3 ≤ C0)
    (h2b : flipTwoThree.fam0 Fm StandardLattice.MassRatio₂) (h2v : flipTwoThree.fam0 Fm StandardLattice.BaseVolumeEqualsMass)
    (hHC : HCFdegR) (hE : DiscreteSeriesWeylDimension.DiscreteSeriesExists) (hWK : DiscreteSeriesWeylDimension.WeylForK) (hLK : DiscreteSeriesWeylDimension.LowKMultOne)
    (hZa : flipTwoThree.FamilySlopeLowerOpenPart Fm) (hZb : flipTwoThree.FamilySlopeMaxOpenPart Fm C5)
    (tCV : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (i : Fm.Ix x) u, Nonempty (flipTwoThree.ColVal (Fm.D x i) u))
    (hW : FamU Fm fun D u => Nonempty (product_first_zeroth_parts.FreeT D u)) (hμ : FamU Fm product_first_zeroth_parts.SlopeLine)
    (hI : FamU Fm Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.HeckeIntegralLevelZero) (hR : FamU Fm Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.HeckeRamifiedLevelZero) (hB : FamU Fm Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.SecondBranchInclusionLength) :
    TuSize Fm → LinkGLOBAL7 Fm Cabs CH C0 Cabs 0 :=
  linkGLOBAL7_tied3 Fm Cabs CH C0 C5 hCabs hCH hC0 h2b h2v (fun D => theorem_three_under_scale_of_general (explicit_bound_all_scales_of_formal_degree hHC hWK hLK) D)
    (fun D => dsigExT_of D hE) hWK hLK hZa hZb tCV hW hμ hI hR hB

end Formalism.MainNotions.RT

end
end

