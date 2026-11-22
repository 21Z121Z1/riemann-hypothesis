import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0010
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0113
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0025
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0026
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0011
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0028
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.PoinStatementPfF
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IntegrableMonomialMulConjComplexGaussian
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0077
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0104
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0092
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0090
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0088
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0087
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0114
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0042
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0038
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0043
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0067
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0075
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0068
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0044
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0035
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0041
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0051
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0013
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle0001
import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
import Development.AutomorphicSpectrum.Statements.MetricStatements.ExistsFlagModelBaseMetric
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0125
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0108
import Development.WeilBound.CoreStatements.PluriharmonicCharts.Bundle0018

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.CcPreserving
section
open MeasureTheory Filter Topology Matrix NumberField ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.Cmp

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cmp.FdPiece

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem bad_null (X : Data E r) {x0 x : Frame X.Ψ r} (h0 : IsOrth X x0) (hx : IsOrth X x)
    {FF : Set (ReciprocityTheory.L2DbarEstimates.V (nd X))} (hF : IsFundSet X x0 FF) :
    volume {w | w ∈ OmF X x ∧ ∀ z' ∈ FF, ∀ γ ∈ X.Γ, ∀ b ∈ Bor X.Ψ r,
      cpt X x w ≠ lact γ (rmul (cpt X x0 z') b)} = 0 := by
  have := FundSetPf.countable_GL (E := E) (r := r)
  set Sat : Set (Frame X.Ψ r) := ⋃ γ : X.Γ, lact (γ : GL (Fin r) E)⁻¹ ⁻¹' KU.Sset X x0 FF with hSat
  have hSm : MeasurableSet Sat :=
    MeasurableSet.iUnion fun γ => (KU.cont_lact X _).measurable (KU.meas_S X h0 hF.1)
  have hB : ∀ y, ∀ b ∈ Bor X.Ψ r, rmul y b ∈ Sat ↔ y ∈ Sat := fun y b hb => by
    simp only [hSat, Set.mem_iUnion, Set.mem_preimage]
    refine exists_congr fun γ => ?_
    rw [KU.lact_rmul' X, KU.rmul_mem_S X hb]
  have hin : ∀ γ ∈ X.Γ, ∀ z' ∈ FF, ∀ b ∈ Bor X.Ψ r, lact γ (rmul (cpt X x0 z') b) ∈ Sat :=
    fun γ hγ z' hz' b hb => Set.mem_iUnion.2 ⟨⟨γ, hγ⟩, ⟨(z', b), ⟨hz', hb⟩, by
      show rmul (cpt X x0 z') b = lact γ⁻¹ (lact γ _)
      rw [← FundSetPf.lact_mul, inv_mul_cancel, FundSetPf.lact_one]⟩⟩
  have hout : ∀ y ∈ Sat, ∃ γ ∈ X.Γ, ∃ z' ∈ FF, ∃ b ∈ Bor X.Ψ r, y = lact γ (rmul (cpt X x0 z') b) := by
    intro y hy
    obtain ⟨γ, ⟨z', b⟩, ⟨hz', hb⟩, e⟩ := Set.mem_iUnion.1 hy
    refine ⟨γ, γ.2, z', hz', b, hb, ?_⟩
    have e' : rmul (cpt X x0 z') b = lact (γ : GL (Fin r) E)⁻¹ y := e
    rw [e', ← FundSetPf.lact_mul, mul_inv_cancel, FundSetPf.lact_one]
  have hφ : Measurable ((Satᶜ).indicator (1 : Frame X.Ψ r → ENNReal)) :=
    measurable_one.indicator hSm.compl
  have hinv := measInv_holds r X x0 x h0 hx _ hφ (fun y _ b hb => by
    by_cases hy : y ∈ Sat
    · rw [Set.indicator_of_notMem (by simpa using (hB y b hb).2 hy),
        Set.indicator_of_notMem (by simpa using hy)]
    · rw [Set.indicator_of_mem (by simpa using fun h => hy ((hB y b hb).1 h)),
        Set.indicator_of_mem (by simpa using hy)]
      rfl)
  have e : ∀ x' : Frame X.Ψ r, ∫⁻ z, (Satᶜ).indicator (1 : Frame X.Ψ r → ENNReal) (cpt X x' z) ∂muF X x' =
      muF X x' (cpt X x' ⁻¹' Satᶜ) := fun x' => by
    rw [← lintegral_indicator_one ((KU.cont_cpt X x').measurable hSm.compl)]
    rfl
  rw [e, e] at hinv
  have hl : muF X x0 (cpt X x0 ⁻¹' Satᶜ) = 0 := by
    refine measure_mono_null (fun z hz => ?_) (ae_iff.1 hF.2.2.2)
    exact fun ⟨z', hz', γ, hγ, b, hb, h⟩ => hz (h ▸ hin γ hγ z' hz' b hb)
  rw [hl] at hinv
  have hr := (withDensity_apply_eq_zero (OntoC.measurable_densF X x)).1 hinv.symm
  have hr2 := nonpos_iff_eq_zero.1 ((Measure.le_restrict_apply _ _).trans hr.le)
  refine measure_mono_null (fun w hw => ?_) hr2
  refine ⟨⟨?_, fun hs => ?_⟩, hw.1⟩
  · simpa using OntoB.densF_pos hw.1
  · obtain ⟨γ, hγ, z', hz', b, hb, h⟩ := hout _ hs
    exact hw.2 z' hz' γ hγ b hb h

theorem exists_cells (X : Data E r) : ∃ C : Set (Frame X.Ψ r), C.Countable ∧ (∀ x ∈ C, IsOrth X x) ∧
    ∀ y ∈ X.dom, ∃ x ∈ C, ∃ w ∈ OmF X x, ∃ b ∈ Bor X.Ψ r, y = rmul (cpt X x w) b := by
  have hlu := fun x : {x : Frame X.Ψ r // IsOrth X x} => lu_holds r X x.1 x.2
  choose Δ zOf bOf hD _ _ _ hsplit hinv using hlu
  obtain ⟨T, hTc, hT⟩ := TopologicalSpace.isOpen_iUnion_countable (fun x => {y | Δ x y ≠ 0})
    (fun x => isOpen_ne_fun (hD x).continuous continuous_const)
  refine ⟨Subtype.val '' T, hTc.image _, ?_, fun y hy => ?_⟩
  · rintro _ ⟨x, _, rfl⟩
    exact x.2
  obtain ⟨x1, h1, b, hb, e⟩ := ortho_holds r X y hy
  have hz : (0 : ReciprocityTheory.L2DbarEstimates.V (nd X)) ∈ OmF X x1 := by
    show cpt X x1 0 ∈ X.dom
    rw [PoinPf.cpt_zero]
    exact PoinPf.orth_mem_dom X h1
  have hy' : y ∈ ⋃ x, {y | Δ x y ≠ 0} := Set.mem_iUnion.2 ⟨⟨x1, h1⟩, by
    have := (hinv ⟨x1, h1⟩ 0 hz b hb).1
    rwa [PoinPf.cpt_zero, ← e] at this⟩
  rw [← hT] at hy'
  obtain ⟨x, hxT, hne⟩ := Set.mem_iUnion₂.1 hy'
  obtain ⟨h2, h3, h4⟩ := hsplit x y hy hne
  exact ⟨x.1, ⟨x, hxT, rfl⟩, _, h2, _, h3, h4⟩

theorem isNull_image {e : ℕ} {Y : Type} [TopologicalSpace Y] (A : FinHolAtlas e Y)
    {D Z : Set (Fin e → ℂ)} {Φ : (Fin e → ℂ) → Y}
    (hP : ∀ z ∈ D, ∃ W, z ∈ W ∧ W ⊆ D ∧ IsParam A W Φ) (hZ : Z ⊆ D) (h0 : volume Z = 0) :
    IsNull A (Φ '' Z) := by
  choose! W hzW _ hWp using hP
  obtain ⟨T, hTc, hT⟩ := TopologicalSpace.isOpen_iUnion_countable (fun z : D => W z)
    (fun z => (hWp z z.2).1)
  intro j
  have hsub : (A.chart j).target ∩ (A.chart j).symm ⁻¹' (Φ '' Z) ⊆
      ⋃ t ∈ T, (A.chart j ∘ Φ) '' (Z ∩ (W t ∩ Φ ⁻¹' (A.chart j).source)) := by
    rintro u ⟨hu, z, hz, e⟩
    have hz' : z ∈ ⋃ t : D, W t := Set.mem_iUnion.2 ⟨⟨z, hZ hz⟩, hzW z (hZ hz)⟩
    rw [← hT] at hz'
    obtain ⟨t, ht, hzt⟩ := Set.mem_iUnion₂.1 hz'
    refine Set.mem_iUnion₂.2 ⟨t, ht, z, ⟨hz, hzt, ?_⟩, ?_⟩
    · show Φ z ∈ (A.chart j).source
      rw [e]
      exact (A.chart j).map_target hu
    · show A.chart j (Φ z) = u
      rw [e]
      exact (A.chart j).right_inv hu
  refine measure_mono_null hsub ((measure_biUnion_null_iff hTc).2 fun t _ => ?_)
  refine addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume (fun z hz => ?_)
    (measure_mono_null Set.inter_subset_left h0)
  exact (((hWp t t.2).2.2.2 j z hz.2).differentiableAt.restrictScalars ℝ).differentiableWithinAt

def sg (X : Data E r) {Ψ : Type} [Fintype Ψ] {e : ℕ} (lab : Ψ ≃ X.Ψ) (q : LowEnt Ψ r ≃ Fin e) :
    Fin (nd X) ≃ Fin e :=
  (Fintype.equivFin (Ent X)).symm.trans ((Equiv.prodCongr lab (Equiv.refl _)).symm.trans q)

def cc (X : Data E r) {Ψ : Type} [Fintype Ψ] {e : ℕ} (lab : Ψ ≃ X.Ψ) (q : LowEnt Ψ r ≃ Fin e)
    (z : Fin e → ℂ) : ReciprocityTheory.L2DbarEstimates.V (nd X) :=
  WithLp.toLp 2 fun i => z (q ((Equiv.prodCongr lab (Equiv.refl _)).symm ((Fintype.equivFin (Ent X)).symm i)))

theorem cc_preserving (X : Data E r) {Ψ : Type} [Fintype Ψ] {e : ℕ} (lab : Ψ ≃ X.Ψ)
    (q : LowEnt Ψ r ≃ Fin e) : MeasurePreserving (cc X lab q) volume volume := by
  have h : MeasurePreserving (⇑(MeasurableEquiv.piCongrLeft (fun _ : Fin (nd X) => ℂ) (sg X lab q).symm) :
      (Fin e → ℂ) → (Fin (nd X) → ℂ)) volume volume :=
    volume_measurePreserving_piCongrLeft (fun _ : Fin (nd X) => ℂ) (sg X lab q).symm
  have ht : MeasurePreserving (WithLp.toLp 2 : (Fin (nd X) → ℂ) → ReciprocityTheory.L2DbarEstimates.V (nd X)) volume volume :=
    MeasurePreserving.symm (MeasurableEquiv.toLp 2 (Fin (nd X) → ℂ)).symm
      (GlobalTheory.volume_preserving_ofLp_complex (Fin (nd X)))
  have e : (cc X lab q) = WithLp.toLp 2 ∘ (MeasurableEquiv.piCongrLeft (fun _ : Fin (nd X) => ℂ) (sg X lab q).symm) := by
    funext z
    refine congrArg (WithLp.toLp 2) (funext fun i => ?_)
    simp [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply, sg]
    rfl
  rw [e]
  exact ht.comp h

theorem cc_injective (X : Data E r) {Ψ : Type} [Fintype Ψ] {e : ℕ} (lab : Ψ ≃ X.Ψ)
    (q : LowEnt Ψ r ≃ Fin e) : Function.Injective (cc X lab q) := by
  intro z z' h
  have h1 : ∀ i, z (sg X lab q i) = z' (sg X lab q i) := fun i => congrFun (WithLp.toLp_injective 2 h) i
  funext a
  simpa using h1 ((sg X lab q).symm a)

theorem cc_surjective (X : Data E r) {Ψ : Type} [Fintype Ψ] {e : ℕ} (lab : Ψ ≃ X.Ψ)
    (q : LowEnt Ψ r ≃ Fin e) : Function.Surjective (cc X lab q) := by
  intro w
  refine ⟨fun a => w.ofLp ((sg X lab q).symm a), ?_⟩
  have : (fun i => w.ofLp ((sg X lab q).symm (sg X lab q i))) = w.ofLp := funext fun i => by simp
  exact (congrArg (WithLp.toLp 2) this).trans rfl

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N j e n : ℕ) (Ψ : Type) [Fintype Ψ] (S : AnSys e (Ψ × Fin N)) (X : Fin n → Data E N) (x0 : ∀ k, Frame (X k).Ψ N) (FF : ∀ k, Set (ReciprocityTheory.L2DbarEstimates.V (nd (X k)))) (lab : ∀ k, Ψ ≃ (X k).Ψ) (q : LowEnt Ψ N ≃ Fin e) (pr : ∀ k, Frame (X k).Ψ N → S.X), j ≤ N → (∀ k, (X k).p0 = N - j ∧ IsOrth (X k) (x0 k) ∧ IsFundSet (X k) (x0 k) (FF k)) → (∀ y : S.X, y ∈ S.open' ↔ ∃ k, ∃ x ∈ (X k).dom, pr k x = y) → (∀ k k', ∀ x ∈ (X k).dom, ∀ x' ∈ (X k').dom, pr k x = pr k' x' → k = k') → (∀ k (x x' : (X k).dom), pr k x.1 = pr k x'.1 ↔ ReciprocityTheory.ChartRestriction.G.AR.Inst.Rel (X k) x x') → (∀ k (x : Frame (X k).Ψ N), IsOrth (X k) x → ∀ z ∈ cellDom j q, (∃ W, z ∈ W ∧ W ⊆ cellDom j q ∧ IsParam S.A W fun z' => pr k (cpt (X k) x (WithLp.toLp 2 fun i => z' (q ((Equiv.prodCongr (lab k) (Equiv.refl _)).symm ((Fintype.equivFin (Ent (X k))).symm i))) : ReciprocityTheory.L2DbarEstimates.V (nd (X k))))) ∧ ∀ p : Ψ × Fin N, ∃ G : (Fin e → ℂ) → ℂ, AnalyticAt ℂ G z ∧ ∀ᶠ z' in 𝓝 z, (S.potH p).φ (pr k (cpt (X k) x (WithLp.toLp 2 fun i => z (q ((Equiv.prodCongr (lab k) (Equiv.refl _)).symm ((Fintype.equivFin (Ent (X k))).symm i))) : ReciprocityTheory.L2DbarEstimates.V (nd (X k))))) (pr k (cpt (X k) x (WithLp.toLp 2 fun i => z' (q ((Equiv.prodCongr (lab k) (Equiv.refl _)).symm ((Fintype.equivFin (Ent (X k))).symm i))) : ReciprocityTheory.L2DbarEstimates.V (nd (X k))))) = stepPot N j p.2 (lowMat q z' p.1) + (G z').re) → ∃ U : PieceUnif S j n, ∀ k, U.vol k = muF (X k) (x0 k) (FF k) := by
  intro E _ _ _ N j e n Ψ _ S X x0 FF lab q pr hj hX hcov hdisj hrel hloc
  have hbr : ∀ k (x : Frame (X k).Ψ N), IsOrth (X k) x →
      (∀ z : Fin e → ℂ, z ∈ cellDom j q ↔ cc (X k) (lab k) q z ∈ OmF (X k) x) ∧
      ∀ F : Set (ReciprocityTheory.L2DbarEstimates.V (nd (X k))), MeasurableSet F → F ⊆ OmF (X k) x →
        muF (X k) x F = cellVol j q (cc (X k) (lab k) q ⁻¹' F) := fun k x hx =>
    GlobalTheory.T.flag_domain_cell_coordinates E N j e (X k) x Ψ (lab k) q hx hj (hX k).1
  have hrelcpt : ∀ k {y y' : Frame (X k).Ψ N}, y ∈ (X k).dom → y' ∈ (X k).dom →
      ∀ γ ∈ (X k).Γ, ∀ b ∈ Bor (X k).Ψ N, y' = lact γ (rmul y b) → pr k y = pr k y' :=
    fun k y y' hy hy' γ hγ b hb h => (hrel k ⟨y, hy⟩ ⟨y', hy'⟩).2 ⟨γ, hγ, b, hb, h⟩
  have hopen := (GlobalTheory.T.analytic_system_regularity_properties e (Ψ × Fin N) S).2.1
  have hcells := fun k => exists_cells (X k)
  choose C hCc hCo hCcov using hcells
  have hnull : ∀ k, ∀ x ∈ C k, IsNull S.A ((fun z => pr k (cpt (X k) x (cc (X k) (lab k) q z))) ''
      (cc (X k) (lab k) q ⁻¹' {w | w ∈ OmF (X k) x ∧ ∀ z' ∈ FF k, ∀ γ ∈ (X k).Γ, ∀ b ∈ Bor (X k).Ψ N,
        cpt (X k) x w ≠ lact γ (rmul (cpt (X k) (x0 k) z') b)})) := by
    intro k x hx
    have ho := hCo k x hx
    refine isNull_image S.A (D := cellDom j q) (fun z hz => (hloc k x ho z hz).1)
      (fun z hz => ((hbr k x ho).1 z).2 hz.1) ?_
    exact (cc_preserving (X k) (lab k) q).quasiMeasurePreserving.preimage_null
      (bad_null (X k) (hX k).2.1 ho (hX k).2.2)
  refine ⟨{ q := fun _ => q
            π := fun k z => pr k (cpt (X k) (x0 k) (cc (X k) (lab k) q z))
            FF := fun k => cc (X k) (lab k) q ⁻¹' FF k
            mem_open := ?_, param := ?_, pot := ?_, meas := ?_, sub := ?_, inj := ?_, disj := ?_, cover := ?_ }, ?_⟩
  · intro k z hz
    exact (hcov _).2 ⟨k, _, ((hbr k _ (hX k).2.1).1 z).1 hz, rfl⟩
  · intro k z hz
    exact (hloc k _ (hX k).2.1 z hz).1
  · intro k z hz p
    exact (hloc k _ (hX k).2.1 z hz).2 p
  · intro k
    exact (cc_preserving (X k) (lab k) q).measurable (hX k).2.2.1
  · intro k z hz
    exact ((hbr k _ (hX k).2.1).1 z).2 ((hX k).2.2.2.1 hz)
  · intro k z hz z' hz' h
    have hO := (hX k).2.2.2.1
    obtain ⟨γ, hγ, b, hb, e'⟩ := (hrel k ⟨_, hO hz⟩ ⟨_, hO hz'⟩).1 h
    exact cc_injective (X k) (lab k) q ((hX k).2.2.2.2.1 _ hz _ hz' γ hγ b hb e')
  · intro k k' hk
    refine Set.disjoint_left.2 ?_
    rintro _ ⟨z, hz, rfl⟩ ⟨z', hz', e'⟩
    exact hk (hdisj k' k _ ((hX k').2.2.2.1 hz') _ ((hX k).2.2.2.1 hz) e').symm
  · have hsub : (⋃ k, (fun z => pr k (cpt (X k) (x0 k) (cc (X k) (lab k) q z))) '' (cc (X k) (lab k) q ⁻¹' FF k))ᶜ ⊆
        S.open'ᶜ ∪ ⋃ k, ⋃ x ∈ C k, (fun z => pr k (cpt (X k) x (cc (X k) (lab k) q z))) ''
          (cc (X k) (lab k) q ⁻¹' {w | w ∈ OmF (X k) x ∧ ∀ z' ∈ FF k, ∀ γ ∈ (X k).Γ, ∀ b ∈ Bor (X k).Ψ N,
            cpt (X k) x w ≠ lact γ (rmul (cpt (X k) (x0 k) z') b)}) := by
      intro y hy
      by_cases hyo : y ∈ S.open'
      swap
      · exact Or.inl hyo
      refine Or.inr ?_
      obtain ⟨k, x', hx', rfl⟩ := (hcov y).1 hyo
      obtain ⟨x, hxC, w, hw, b, hb, e'⟩ := hCcov k x' hx'
      have h1 : pr k (cpt (X k) x w) = pr k x' :=
        hrelcpt k hw hx' 1 (X k).Γ.one_mem b hb (by rw [FundSetPf.lact_one]; exact e')
      obtain ⟨u, rfl⟩ := cc_surjective (X k) (lab k) q w
      refine Set.mem_iUnion.2 ⟨k, Set.mem_iUnion₂.2 ⟨x, hxC, u, ⟨hw, ?_⟩, h1⟩⟩
      intro z' hz' γ hγ b' hb' e2
      obtain ⟨u', rfl⟩ := cc_surjective (X k) (lab k) q z'
      refine hy (Set.mem_iUnion.2 ⟨k, u', hz', ?_⟩)
      exact (hrelcpt k ((hX k).2.2.2.1 hz') hw γ hγ b' hb' e2).trans h1
    intro a
    refine measure_mono_null (Set.inter_subset_inter_right _ (Set.preimage_mono hsub)) ?_
    rw [Set.preimage_union, Set.inter_union_distrib_left]
    refine measure_union_null (hopen a) ?_
    simp only [Set.preimage_iUnion, Set.inter_iUnion]
    exact measure_iUnion_null fun k => (measure_biUnion_null_iff (hCc k)).2 fun x hx => hnull k x hx a
  · intro k
    exact ((hbr k _ (hX k).2.1).2 _ (hX k).2.2.1 (hX k).2.2.2.1).symm

end GlobalTheory.CompanionTheory.Ar.Cmp.FdPiece
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverBlockFieldEqStatement
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.CovGraph
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_cover_block_field_eq : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Φ' : Type) [Field Φ'] (y' : (Σ k, ι' k) → Φ') (M' : FlagModel y' Ψ N j) (Cv : FlagCover M' M) [CharZero Φ'], (∀ k, ∃ i, y' ⟨k, i⟩ ≠ 0) → blockFnField y' = blockFnField (pairV (transPt Cv) y') := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.CovGraph.blockFnField_pair_transPt | exact GlobalTheory.CompanionTheory.Ar.PB.CovGraph.blockFnField_pair_transPt | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.CovGraph.blockFnField_pair_transPt <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverFramesLiftPointStatement
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.CovGraph
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_cover_frames_lift_point : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Φ' : Type) [Field Φ'] (y' : (Σ k, ι' k) → Φ') (M' : FlagModel y' Ψ N j) (Cv : FlagCover M' M) (z₁ : (Σ k, ι' k) → ℂ) (z₀ : (Σ k, ι k) → ℂ) (F' : FrameData ι' Ψ N M'.Ω M'.blk) (F : FrameData ι Ψ N M.Ω M.blk) (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (p : Ψ × Fin N) (k : K), z₁ ∈ mcPts (mCoordIdeal y') → M'.IsFrame F' → M.IsFrame F → M'.GoodAt F' (mCoordIdeal (basePart M'.blk z₁)) → M.GoodAt F (mCoordIdeal (basePart M'.blk z₁ ∘ Cv.v)) → M'.IsFlagOf F' z₁ h → M.IsFlagOf F z₀ (fun τ => Cv.trans F' F (basePart M'.blk z₁) τ * h τ) → SameOrbit (basePart M.blk z₀) (basePart M'.blk z₁ ∘ Cv.v) → M.blk p = some k → ∃ (e : Φ') (s : ι k → Φ') (t : ℂ), e ≠ 0 ∧ t ≠ 0 ∧ ∀ m, transPt Cv ⟨k, m⟩ = e * s m ∧ IsValueAt y' (s m) z₁ (t * z₀ ⟨k, m⟩) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.CovGraph.BStep.main | exact GlobalTheory.CompanionTheory.Ar.PB.CovGraph.BStep.main | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.CovGraph.BStep.main <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverTwoFramesComparisonStatement
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_cover_two_frames_comparison : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Φ' : Type) [Field Φ'] (y' : (Σ k, ι' k) → Φ') (M' : FlagModel y' Ψ N j) (Cv : FlagCover M' M) (b : (Σ k, baseIdx ι' M'.blk k) → ℂ) (F₁' F₂' : FrameData ι' Ψ N M'.Ω M'.blk) (F₁ F₂ : FrameData ι Ψ N M.Ω M.blk) (H₁ H₂ : Ψ → Matrix (Fin N) (Fin N) ℂ), b ∈ mcPts (mCoordIdeal M'.x) → M'.IsFrame F₁' → M'.IsFrame F₂' → M.IsFrame F₁ → M.IsFrame F₂ → M'.GoodAt F₁' (mCoordIdeal b) → M'.GoodAt F₂' (mCoordIdeal b) → M.GoodAt F₁ (mCoordIdeal (b ∘ Cv.v)) → M.GoodAt F₂ (mCoordIdeal (b ∘ Cv.v)) → (∀ τ, IsBlockDiag j (H₁ τ)) → (∀ τ, IsBlockDiag j (H₂ τ)) → (∀ (p : Ψ × Fin N) (k' : K'), M'.blk p = some k' → ∃ a : ℂ, a ≠ 0 ∧ ∀ m' : ι' k', CovMap.LocImg.plk M' F₁' b p.2 ⟨k', m'⟩ (H₁ p.1) = a * CovMap.LocImg.plk M' F₂' b p.2 ⟨k', m'⟩ (H₂ p.1)) → ∀ (p : Ψ × Fin N) (k : K), M.blk p = some k → ∃ a : ℂ, a ≠ 0 ∧ ∀ m : ι k, CovMap.LocImg.plk M F₁ (b ∘ Cv.v) p.2 ⟨k, m⟩ (Cv.trans F₁' F₁ b p.1 * H₁ p.1) = a * CovMap.LocImg.plk M F₂ (b ∘ Cv.v) p.2 ⟨k, m⟩ (Cv.trans F₂' F₂ b p.1 * H₂ p.1) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.Ind.plk_moved_indep | exact GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.Ind.plk_moved_indep | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.Ind.plk_moved_indep <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagGapPullbackFirst
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.StepW GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

namespace GlobalTheory.CompanionTheory.Ar.PB.StepW.Wgt

theorem eq_on_block {K : Type} {ι : K → Type} {Kk : Type} {ιk : Kk → Type} {κ : Kk → K}
    {v : (Σ k, ιk k) → (Σ k, ι k)} (hb : IsBlockMap κ v) {a b : (Σ k, ι k) → ℂ} (h : a ∘ v = b ∘ v)
    {k : K} (hk : k ∈ Set.range κ) (m : ι k) : a ⟨k, m⟩ = b ⟨k, m⟩ := by
  obtain ⟨q, hq⟩ := hb.2.2.2 ⟨k, m⟩ hk
  rw [← hq]
  exact congrFun h q

theorem main : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ) (BM : BaseMetric M n) (p : Ψ × Fin N) (Kk : Type) [Fintype Kk] (ιk : Kk → Type) [∀ k, Fintype (ιk k)] (κ : Kk → K) (v : (Σ k, ιk k) → (Σ k, ι k)) (e : ℕ) (R : AnLogRes (mCoordIdeal (y ∘ v)) ⊤ e) (pr : R.X → BM.Rb.X), IsStepHyp M BM p κ v R pr → ∀ (x y' : R.X) (z : (Σ k, ι k) → ℂ), y' ∈ R.U x → pr y' ∉ bdry BM.s → z ∈ mcPts (mCoordIdeal y) → z ∘ v = R.lift x y' → stepPh M BM p v R pr y' = stepGap M BM p z := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n BM p Kk _ ιk _ κ v e R pr H x y' z hy' hpr hz hzv
  obtain ⟨hb, hr, -, H1⟩ := H
  obtain ⟨z₀, hz₀, hz₀v, hz₀o⟩ := H1 y'
  have hex : pr y' ∉ bdry BM.s ∧ ∃ z ∈ mcPts (mCoordIdeal y), z ∘ v = R.lift y' y' :=
    ⟨hpr, z₀, hz₀, hz₀v⟩
  have hph : stepPh M BM p v R pr y' = stepGap M BM p hex.2.choose := by
    unfold stepPh
    rw [dif_pos hex]
  obtain ⟨hz₁, hz₁v⟩ := hex.2.choose_spec
  rw [hph]
  generalize hex.2.choose = z₁ at hz₁ hz₁v

  have hbase : ∀ {a b : (Σ k, ι k) → ℂ}, a ∘ v = b ∘ v → basePart M.blk a = basePart M.blk b := by
    intro a b hab
    funext q
    exact eq_on_block hb hab (hr q.1.1 (Or.inl q.1.2)) q.2
  have hz₁o : SameOrbit (basePart M.blk z₁) (BM.Rb.lift (pr y') (pr y')) := by
    rw [hbase (hz₁v.trans hz₀v.symm)]
    exact hz₀o

  obtain ⟨c, hc, hcl⟩ := R.compat x y' y' ⟨hy', R.mem_U y'⟩
  set c' : K → ℂ := Function.extend κ c 1 with hc'
  have hc'0 : ∀ k, c' k ≠ 0 := by
    intro k
    by_cases hk : ∃ a, κ a = k
    · obtain ⟨a, rfl⟩ := hk
      rw [hc', hb.1.extend_apply]
      exact hc a
    · rw [hc', Function.extend_apply' _ _ _ hk]
      exact one_ne_zero
  set z₂ : (Σ k, ι k) → ℂ := fun q => c' q.1 * z₁ q with hz₂
  have hz₂m : z₂ ∈ mcPts (mCoordIdeal y) :=
    ((GlobalTheory.CompanionTheory.Ar.PB.StepW.TorusAct.main K ι Φ y z₁ c' hc'0).2 hz₁).1
  have hz₂v : z₂ ∘ v = z ∘ v := by
    rw [hzv, hcl]
    funext q
    have h1 : z₁ (v q) = R.lift y' y' q := congrFun hz₁v q
    have h2 : c' (v q).1 = c q.1 := by
      rw [hb.2.2.1 q, hc', hb.1.extend_apply]
    simp only [Function.comp, hz₂, h1, h2]
  have ht : stepGap M BM p z₂ = stepGap M BM p z₁ :=
    GlobalTheory.CompanionTheory.Ar.PB.StepW.stepGap_torus K ι Φ y Ψ N j M n BM p z₁ c' hc'0 hz₁.1
  have hz₂o : SameOrbit (basePart M.blk z₂) (BM.Rb.lift (pr y') (pr y')) := by
    obtain ⟨d, hd, hdl⟩ := hz₁o
    refine ⟨fun k => c' k.1 * d k, fun k => mul_ne_zero (hc'0 _) (hd k), ?_⟩
    funext q
    have h1 : basePart M.blk z₁ q = d q.1 * BM.Rb.lift (pr y') (pr y') q := congrFun hdl q
    have h2 : basePart M.blk z₂ q = c' q.1.1 * basePart M.blk z₁ q := rfl
    rw [h2, h1, mul_assoc]
  have hg : stepGap M BM p z₂ = stepGap M BM p z :=
    GlobalTheory.T.flag_gap_same_base_orbit K ι Φ y Ψ N j M n BM p (pr y') z₂ z hpr hz₂m hz hz₂o (hbase hz₂v)
      (fun k hk m => eq_on_block hb hz₂v (hr k (Or.inr hk)) m)
  rw [← ht, hg]

end GlobalTheory.CompanionTheory.Ar.PB.StepW.Wgt
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagGapPullbackSecond
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.StepW.WeightProp

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.StepW GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ]
  {y : (Σ k, ι k) → Φ} {Ψ : Type} {N j n : ℕ}
  {Kk : Type} [Fintype Kk] {ιk : Kk → Type} [∀ k, Fintype (ιk k)]

theorem sameOrbit_basePart {M : FlagModel y Ψ N j} {BM : BaseMetric M n} {p : Ψ × Fin N} {κ : Kk → K}
    {v : (Σ k, ιk k) → (Σ k, ι k)} {e : ℕ} {R : AnLogRes (mCoordIdeal (y ∘ v)) ⊤ e} {pr : R.X → BM.Rb.X}
    (hS : IsStepHyp M BM p κ v R pr) (x : R.X) {z : (Σ k, ι k) → ℂ} (hz : z ∘ v = R.lift x x) :
    SameOrbit (basePart M.blk z) (BM.Rb.lift (pr x) (pr x)) := by
  obtain ⟨hbm, hcov, -, hall⟩ := hS
  obtain ⟨z₁, -, h1, h2⟩ := hall x
  have e : basePart M.blk z = basePart M.blk z₁ := by
    funext q
    obtain ⟨r, hr⟩ := hbm.2.2.2 ⟨q.1.1, q.2⟩ (hcov _ (Or.inl q.1.2))
    have h3 : z (v r) = z₁ (v r) := congrFun (hz.trans h1.symm) r
    rw [hr] at h3
    exact h3
  rw [e]
  exact h2

theorem exists_base_const {L : Type} {μ : L → Type} {b₁ b₂ b : (Σ k, μ k) → ℂ} (h₁ : SameOrbit b₁ b)
    (h₂ : SameOrbit b₂ b) : ∃ c : L → ℂ, (∀ k, c k ≠ 0) ∧ ∀ q, b₁ q = c q.1 * b₂ q := by
  obtain ⟨c₁, hc₁, rfl⟩ := h₁
  obtain ⟨c₂, hc₂, rfl⟩ := h₂
  refine ⟨fun k => c₁ k / c₂ k, fun k => div_ne_zero (hc₁ k) (hc₂ k), fun q => ?_⟩
  have := hc₂ q.1
  field_simp

theorem exists_coord {κ : Kk → K} {v : (Σ k, ιk k) → (Σ k, ι k)} (hbm : IsBlockMap κ v) (k : Kk) (i : ι (κ k)) :
    ∃ m : ιk k, v ⟨k, m⟩ = ⟨κ k, i⟩ := by
  obtain ⟨r, hr⟩ := hbm.2.2.2 ⟨κ k, i⟩ ⟨k, rfl⟩
  have h1 : κ r.1 = κ k := by rw [← hbm.2.2.1 r, hr]
  have h2 : r.1 = k := hbm.1 h1
  obtain ⟨r1, m⟩ := r
  obtain rfl : r1 = k := h2
  exact ⟨m, hr⟩

theorem stepGap_eq {M : FlagModel y Ψ N j} [Fintype Ψ] [DecidableEq Ψ] {BM : BaseMetric M n} {p : Ψ × Fin N} {κ : Kk → K}
    {v : (Σ k, ιk k) → (Σ k, ι k)} {e : ℕ} {R : AnLogRes (mCoordIdeal (y ∘ v)) ⊤ e} {pr : R.X → BM.Rb.X}
    (hS : IsStepHyp M BM p κ v R pr) {x x' : R.X} (hpr : pr x = pr x') (hb : pr x ∉ bdry BM.s)
    (hblk : ∀ k (m : ιk k), M.blk p = some (κ k) → ∃ a : ℂ, ∀ m' : ιk k,
      R.lift x x ⟨k, m'⟩ = a * R.lift x' x' ⟨k, m'⟩)
    {z z' : (Σ k, ι k) → ℂ} (hzm : z ∈ mcPts (mCoordIdeal y)) (hz'm : z' ∈ mcPts (mCoordIdeal y))
    (hz : z ∘ v = R.lift x x) (hz' : z' ∘ v = R.lift x' x') :
    stepGap M BM p z = stepGap M BM p z' := by
  have so := sameOrbit_basePart hS x hz
  have so' := sameOrbit_basePart hS x' hz'
  rw [← hpr] at so'
  obtain ⟨cb, hcb, hcbq⟩ := exists_base_const so so'
  obtain ⟨hbm, hcov, -, -⟩ := hS
  have e1 : ∀ r, z (v r) = R.lift x x r := congrFun hz
  have e2 : ∀ r, z' (v r) = R.lift x' x' r := congrFun hz'
  have ha : ∃ a : ℂ, a ≠ 0 ∧ ∀ k, M.blk p = some k → ∀ m : ι k, z ⟨k, m⟩ = a * z' ⟨k, m⟩ := by
    rcases hp : M.blk p with _ | k₀
    · exact ⟨1, one_ne_zero, fun k hk => by simp at hk⟩
    · obtain ⟨k', rfl⟩ := hcov k₀ (Or.inr hp)
      obtain ⟨i, hi⟩ := hzm.1 (κ k')
      obtain ⟨m, hm⟩ := exists_coord hbm k' i
      obtain ⟨a, ha⟩ := hblk k' m hp
      refine ⟨a, fun h0 => hi ?_, fun k hk m' => ?_⟩
      · rw [← hm, e1, ha, h0, zero_mul]
      · obtain rfl : κ k' = k := Option.some.inj hk
        obtain ⟨m'', hm''⟩ := exists_coord hbm k' m'
        rw [← hm'', e1, e2, ha]
  obtain ⟨a, ha0, ha⟩ := ha
  let c : K → ℂ := fun k =>
    if h : ∀ p', M.blk p' ≠ some k then cb ⟨k, h⟩ else if M.blk p = some k then a else 1
  have hc : ∀ k, c k ≠ 0 := fun k => by
    simp only [c]
    split_ifs
    · exact hcb _
    · exact ha0
    · exact one_ne_zero
  have hT := GlobalTheory.CompanionTheory.Ar.PB.StepW.TorusAct.main K ι Φ y z' c hc
  have h1 : stepGap M BM p (fun q => c q.1 * z' q) = stepGap M BM p z' :=
    GlobalTheory.T.flag_gap_torus_invariant K ι Φ y Ψ N j M n BM p z' c hc hz'm.1
  rw [← h1]
  refine GlobalTheory.T.flag_gap_same_base_orbit K ι Φ y Ψ N j M n BM p (pr x) z _ hb hzm (hT.2 hz'm).1 so ?_ ?_
  · funext q
    have : c q.1.1 = cb q.1 := dif_pos q.1.2
    show basePart M.blk z q = c q.1.1 * z' ⟨q.1.1, q.2⟩
    rw [this, hcbq]
    rfl
  · intro k hk m
    have : c k = a := (dif_neg fun h => h p hk).trans (if_pos hk)
    show z ⟨k, m⟩ = c k * z' ⟨k, m⟩
    rw [this, ha k hk]

theorem main : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ) (BM : BaseMetric M n) (p : Ψ × Fin N) (Kk : Type) [Fintype Kk] (ιk : Kk → Type) [∀ k, Fintype (ιk k)] (κ : Kk → K) (v : (Σ k, ιk k) → (Σ k, ι k)) (e : ℕ) (R : AnLogRes (mCoordIdeal (y ∘ v)) ⊤ e) (pr : R.X → BM.Rb.X), IsStepHyp M BM p κ v R pr → ∀ x x', pr x = pr x' → (∀ k (m : ιk k), M.blk p = some (κ k) → ∃ a : ℂ, ∀ m' : ιk k, R.lift x x ⟨k, m'⟩ = a * R.lift x' x' ⟨k, m'⟩) → stepPh M BM p v R pr x = stepPh M BM p v R pr x' := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n BM p Kk _ ιk _ κ v e R pr hS x x' hpr hblk
  by_cases hb : pr x ∈ bdry BM.s
  · have hb' : pr x' ∈ bdry BM.s := hpr ▸ hb
    rw [stepPh, stepPh, dif_neg fun h => h.1 hb, dif_neg fun h => h.1 hb']
  · have hb' : pr x' ∉ bdry BM.s := hpr ▸ hb
    obtain ⟨z₁, hz₁, hv₁, -⟩ := hS.2.2.2 x
    obtain ⟨z₂, hz₂, hv₂, -⟩ := hS.2.2.2 x'
    have h1 : pr x ∉ bdry BM.s ∧ ∃ z ∈ mcPts (mCoordIdeal y), z ∘ v = R.lift x x := ⟨hb, z₁, hz₁, hv₁⟩
    have h2 : pr x' ∉ bdry BM.s ∧ ∃ z ∈ mcPts (mCoordIdeal y), z ∘ v = R.lift x' x' := ⟨hb', z₂, hz₂, hv₂⟩
    rw [stepPh, stepPh, dif_pos h1, dif_pos h2]
    exact stepGap_eq hS hpr hb hblk h1.2.choose_spec.1 h2.2.choose_spec.1 h1.2.choose_spec.2 h2.2.choose_spec.2

end GlobalTheory.CompanionTheory.Ar.PB.StepW.WeightProp
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.GenericDegreeOfArithSystemStatement
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_degree_of_arith_system : ReciprocityTheory.ChartRestriction.G.Geo.ArithIntersectionSystemStatement → GenDegStatement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.genDeg_of_system | exact GlobalTheory.CompanionTheory.Ar.Giv.genDeg_of_system | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.genDeg_of_system <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.IsArithVarOfSncModel
section
open AlgebraicGeometry CategoryTheory NumberField Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.BMx ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped ComplexOrder

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.isArithVar_of_snc_model : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (x : (Σ k, J k) → Ω) (n : ℕ) (bd : Ideal (MRing J)), 1 ≤ n → CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, x ⟨k, c' k⟩) → Cmp.IsSncModel x n bd → ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (mCoordIdeal x) (n + 1) := by
  first | exact @PositivityTheory.Xgp.t_c_bm_exists_arith | exact PositivityTheory.Xgp.t_c_bm_exists_arith
end

