import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0133
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBCSplit
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0134
import Formalism.HermitianCurvature.Bundle0004
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CoordinateSplitAssocMeasurePreserving
import Formalism.HermitianCurvature.StatementU

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.HeisConjInt
section
open Matrix MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBH

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

variable {k : ℕ}

theorem phi_cont (ρ : ℕ) : Continuous (Dx2.MN.phi (k := k) (ρ := ρ)) := by
  have e : (Dx2.MN.phi (k := k) (ρ := ρ)) = fun x => Dx2.MN.phi x := rfl
  rw [e]
  simp only [Dx2.MN.phi]
  fun_prop

theorem phi_inj (ρ : ℕ) : Function.Injective (Dx2.MN.phi (k := k) (ρ := ρ)) := by
  intro x y h
  obtain ⟨x1, x2, x3⟩ := x
  obtain ⟨y1, y2, y3⟩ := y
  simp only [Dx2.MN.phi, Prod.mk.injEq] at h
  obtain ⟨h1, h3⟩ := h
  simp only [Prod.mk.injEq]
  refine ⟨?_, Subsingleton.elim _ _, ?_⟩
  · funext i a
    have : a = 0 := Subsingleton.elim _ _
    subst this
    exact congrFun h1 i
  · funext a
    have : a = 0 := Subsingleton.elim _ _
    subst this
    exact h3

def heisT (ρ : ℕ) (x : B2.HPar k ρ) : Mt k (1 + ρ) := Matrix.of.symm (B2.heis0 k ρ x)

theorem heis_cont (ρ : ℕ) : Continuous (heisT (k := k) ρ) := B2x5.continuous_heis0 k ρ

theorem heis_emb (ρ : ℕ) : MeasurableEmbedding (heisT (k := k) ρ) :=
  (heis_cont ρ).measurableEmbedding (Formalism.FourierDecayAlt.P.heisenberg_subgroup_closed k ρ).1

def phiE (ρ : ℕ) : U.RC k 1 ρ ≃ᵐ B2.HPar k ρ where
  toFun := Dx2.MN.phi
  invFun p := (fun i _ => p.1 i, (fun _ => 0, fun _ => p.2))
  left_inv x := by
    obtain ⟨x1, x2, x3⟩ := x
    simp only [Dx2.MN.phi, Prod.mk.injEq]
    refine ⟨?_, Subsingleton.elim _ _, ?_⟩
    · funext i a; have : a = 0 := Subsingleton.elim _ _; subst this; rfl
    · funext a; have : a = 0 := Subsingleton.elim _ _; subst this; rfl
  right_inv p := by simp [Dx2.MN.phi]
  measurable_toFun := (phi_cont ρ).measurable
  measurable_invFun := by
    apply Continuous.measurable
    exact (continuous_pi fun i => continuous_pi fun _ => (continuous_apply i).comp continuous_fst).prodMk
      (continuous_const.prodMk (continuous_pi fun _ => continuous_snd))

theorem phi_emb (ρ : ℕ) : MeasurableEmbedding (Dx2.MN.phi (k := k) (ρ := ρ)) := by
  exact (phiE ρ).measurableEmbedding

theorem heis_int (ρ : ℕ) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Φ : B.Mat k (1 + ρ) → B.Mat k (1 + ρ) → E) :
    ∫ p : Mt k (1 + ρ) × Mt k (1 + ρ), Φ (Matrix.of p.1) (Matrix.of p.2) ∂((B2.μHeis k ρ).prod (B2.μHeis k ρ)) =
      ∫ xx : U.RC k 1 ρ × U.RC k 1 ρ, Φ (U.Rn k 1 ρ xx.1) (U.Rn k 1 ρ xx.2)
        ∂((U.muRC k 1 ρ).prod (U.muRC k 1 ρ)) := by
  have e0 : B2.μHeis k ρ = (volume : Measure (B2.HPar k ρ)).map (heisT ρ) := rfl
  have e1 : (B2.μHeis k ρ).prod (B2.μHeis k ρ) =
      ((volume : Measure (B2.HPar k ρ)).prod volume).map (Prod.map (heisT (k := k) ρ) (heisT ρ)) := by
    rw [e0, Measure.map_prod_map _ _ (heis_emb ρ).measurable (heis_emb ρ).measurable]
  rw [e1, ((heis_emb ρ).prodMap (heis_emb ρ)).integral_map]
  have hmp : MeasurePreserving (Prod.map (Dx2.MN.phi (k := k) (ρ := ρ)) (Dx2.MN.phi (k := k) (ρ := ρ)))
      ((U.muRC k 1 ρ).prod (U.muRC k 1 ρ)) ((volume : Measure (B2.HPar k ρ)).prod volume) := by
    have := (Dx2.MN.phi_mp (k := k) (ρ := ρ)).prod (Dx2.MN.phi_mp (k := k) (ρ := ρ))
    simpa [U.muRC] using this
  rw [← hmp.integral_comp ((phi_emb ρ).prodMap (phi_emb ρ))]
  apply integral_congr_ae
  filter_upwards with xx
  rw [Dx2.MN.rn_heis, Dx2.MN.rn_heis]
  rfl

def conjE {r : ℕ} (b : B.Mat k r) (hb : IsUnit b.det) : Mt k r ≃ᵐ Mt k r where
  toFun := conjM b
  invFun := conjM b⁻¹
  left_inv x := by
    show b⁻¹ * (b * Matrix.of x * b⁻¹) * b⁻¹⁻¹ = Matrix.of x
    rw [Matrix.nonsing_inv_nonsing_inv _ hb]
    simp only [Matrix.mul_assoc]
    rw [Matrix.nonsing_inv_mul_cancel_left _ _ hb, Matrix.nonsing_inv_mul _ hb, Matrix.mul_one]
  right_inv x := by
    show b * (b⁻¹ * Matrix.of x * b⁻¹⁻¹) * b⁻¹ = Matrix.of x
    rw [Matrix.nonsing_inv_nonsing_inv _ hb]
    simp only [Matrix.mul_assoc]
    rw [Matrix.mul_nonsing_inv_cancel_left _ _ hb, Matrix.mul_nonsing_inv _ hb, Matrix.mul_one]
  measurable_toFun := B2x5.measurable_conjM b
  measurable_invFun := B2x5.measurable_conjM b⁻¹

theorem heis_conj_int (ρ : ℕ) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {g g' : B.Mat k ρ}
    (hg : g ∈ B.GV k ρ) (hg' : g' ∈ B.GV k ρ) (Φ : Mt k (1 + ρ) × Mt k (1 + ρ) → E) :
    ∫ p, Φ (conjM ((ιLev k 1 ρ g)⁻¹) p.1, conjM ((ιLev k 1 ρ g')⁻¹) p.2) ∂((B2.μHeis k ρ).prod (B2.μHeis k ρ)) =
      ∫ p, Φ p ∂((B2.μHeis k ρ).prod (B2.μHeis k ρ)) := by
  have := sf_heis (k := k) ρ
  have hu : IsUnit ((ιLev k 1 ρ g)⁻¹).det :=
    Matrix.isUnit_nonsing_inv_det_iff.2 (LongWeylElement.lev_unit _ (HermitianFormFactor.UH_unit (Ux3.hpk_det k ρ) hg))
  have hu' : IsUnit ((ιLev k 1 ρ g')⁻¹).det :=
    Matrix.isUnit_nonsing_inv_det_iff.2 (LongWeylElement.lev_unit _ (HermitianFormFactor.UH_unit (Ux3.hpk_det k ρ) hg'))
  have m1 : MeasurePreserving (conjE _ hu) (B2.μHeis k ρ) (B2.μHeis k ρ) :=
    ⟨(conjE _ hu).measurable, heis_meas_conj_inv ρ hg⟩
  have m2 : MeasurePreserving (conjE _ hu') (B2.μHeis k ρ) (B2.μHeis k ρ) :=
    ⟨(conjE _ hu').measurable, heis_meas_conj_inv ρ hg'⟩
  have := (m1.prod m2).integral_comp ((conjE _ hu).measurableEmbedding.prodMap (conjE _ hu').measurableEmbedding) Φ
  exact this

end Formalism.FourierDecayAlt.P.PBH
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.PBCHerg
section
namespace Formalism.FourierDecayAlt.P.PBC

open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory NumberField
open scoped ComplexConjugate ComplexOrder

noncomputable section

open Classical

variable {H : Type} {f : ℕ}

def psiG (g : ℝ) (l c : ℂ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * ((2 * (l * c).re / g : ℝ) : ℂ))

def Fz (Y : Finset H) (κ : H → H → ℂ) (D : Fin f → H → H → ℂ → ℂ) (z : crystallineComparison.V f) : ℂ :=
  ∑ h ∈ Y, ∑ h' ∈ Y, κ h h' * ∏ v, D v h h' (z v)

def Nz (Y : Finset H) (κ : H → H → ℂ) (D : Fin f → H → H → ℂ → ℂ) (z : crystallineComparison.V f) : ℝ :=
  if Good z then (Fz Y κ D z).re else 0

theorem Fz_nonneg (Y : Finset H) (κ : H → H → ℂ) (hκ : TB.PSDOn Y κ) (D : Fin f → H → H → ℂ → ℂ)
    (hD : ∀ v (z : ℂ), z ≠ 0 → TB.PSDOn Y (fun h h' => D v h h' z)) (z : crystallineComparison.V f) (hz : Good z) :
    0 ≤ Fz Y κ D z := by
  let k : Option (Fin f) → H → H → ℂ := fun o => match o with
    | none => κ
    | some v => fun h h' => D v h h' (z v)
  have hk : ∀ o, TB.PSDOn Y (k o) := by
    intro o; rcases o with _ | v
    · exact hκ
    · exact hD v (z v) (hz v)
  have hS := Formalism.FourierDecayAlt.P.schur_product _ (Option (Fin f)) Y k hk
  have hC := JCx1.decay.psd_compress Y _ hS (fun _ : Unit => Y) (fun _ => id) (fun _ h hh => hh)
  have := hC.diag_nonneg (i := ())
  simp only [Matrix.of_apply, id] at this
  convert this using 1
  unfold Fz
  simp [Fintype.prod_option, k]

theorem Nz_nonneg (Y : Finset H) (κ : H → H → ℂ) (hκ : TB.PSDOn Y κ) (D : Fin f → H → H → ℂ → ℂ)
    (hD : ∀ v (z : ℂ), z ≠ 0 → TB.PSDOn Y (fun h h' => D v h h' z)) (z : crystallineComparison.V f) : 0 ≤ Nz Y κ D z := by
  unfold Nz; split_ifs with hz
  · exact (Complex.nonneg_iff.1 (Fz_nonneg Y κ hκ D hD z hz)).1
  · exact le_rfl

theorem isOpen_good : IsOpen {z : crystallineComparison.V f | Good z} := by
  have : {z : crystallineComparison.V f | Good z} = ⋂ v, (fun z : crystallineComparison.V f => z v) ⁻¹' {0}ᶜ := by
    ext z; simp [Good]
  rw [this]
  exact isOpen_iInter_of_finite fun v => (continuous_apply v).isOpen_preimage _ isOpen_compl_singleton

theorem Fz_continuousAt (Y : Finset H) (κ : H → H → ℂ) (D : Fin f → H → H → ℂ → ℂ)
    (hDc : ∀ v, ∀ h ∈ Y, ∀ h' ∈ Y, ContinuousOn (D v h h') {0}ᶜ) (z : crystallineComparison.V f) (hz : Good z) :
    ContinuousAt (Fz Y κ D) z := by
  unfold Fz ContinuousAt
  refine tendsto_finsetSum _ fun h hh => tendsto_finsetSum _ fun h' hh' => ?_
  refine tendsto_const_nhds.mul (tendsto_finsetProd _ fun v _ => ?_)
  have := (hDc v h hh h' hh').continuousAt (isOpen_compl_singleton.mem_nhds (hz v))
  exact this.tendsto.comp (continuous_apply v).continuousAt.tendsto

theorem Nz_lsc (Y : Finset H) (κ : H → H → ℂ) (hκ : TB.PSDOn Y κ) (D : Fin f → H → H → ℂ → ℂ)
    (hD : ∀ v (z : ℂ), z ≠ 0 → TB.PSDOn Y (fun h h' => D v h h' z))
    (hDc : ∀ v, ∀ h ∈ Y, ∀ h' ∈ Y, ContinuousOn (D v h h') {0}ᶜ) : LowerSemicontinuous (Nz Y κ D) := by
  intro z y hy
  by_cases hz : Good z
  · have hc : ContinuousAt (fun z => (Fz Y κ D z).re) z :=
      Complex.continuous_re.continuousAt.comp (Fz_continuousAt Y κ D hDc z hz)
    have h1 : ∀ᶠ z' in 𝓝 z, Good z' := isOpen_good.mem_nhds hz
    have hy' : y < (Fz Y κ D z).re := by simpa [Nz, hz] using hy
    filter_upwards [h1, hc.eventually (lt_mem_nhds hy')] with z' hg hl
    simpa [Nz, hg] using hl
  · have hy' : y < 0 := by simpa [Nz, hz] using hy
    exact Filter.Eventually.of_forall fun z' => hy'.trans_le (Nz_nonneg Y κ hκ D hD z')

theorem ae_good : ∀ᵐ z : crystallineComparison.V f, Good z := by
  have : ∀ v : Fin f, ∀ᵐ z : crystallineComparison.V f, z v ≠ 0 := by
    intro v
    rw [ae_iff]
    simp only [ne_eq, not_not]
    rw [MeasureTheory.volume_pi]
    exact Measure.pi_hyperplane _ v 0
  exact (ae_all_iff.2 this).mono fun z hz => hz

theorem Fz_integrable (Y : Finset H) (κ : H → H → ℂ) (D : Fin f → H → H → ℂ → ℂ)
    (hDi : ∀ v, ∀ h ∈ Y, ∀ h' ∈ Y, Integrable (D v h h')) : Integrable (Fz Y κ D) := by
  unfold Fz
  refine integrable_finsetSum _ fun h hh => integrable_finsetSum _ fun h' hh' => ?_
  exact (Integrable.fintype_prod (f := fun v => D v h h') fun v => hDi v h hh h' hh').const_mul _

theorem Nz_integrable (Y : Finset H) (κ : H → H → ℂ) (D : Fin f → H → H → ℂ → ℂ)
    (hDi : ∀ v, ∀ h ∈ Y, ∀ h' ∈ Y, Integrable (D v h h')) : Integrable (Nz Y κ D) := by
  refine (Fz_integrable Y κ D hDi).re.congr ?_
  filter_upwards [ae_good] with z hz
  simp [Nz, hz]

end

end Formalism.FourierDecayAlt.P.PBC
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.RearrApply
section
namespace Formalism.FourierDecayAlt.P.StabilizerDisintegration.RE

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt

noncomputable section

section gen

variable {α β γ : Type} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]

def inE : α × (β × γ) ≃ᵐ β × (α × γ) :=
  MeasurableEquiv.prodAssoc.symm.trans
    ((MeasurableEquiv.prodCongr MeasurableEquiv.prodComm (MeasurableEquiv.refl γ)).trans MeasurableEquiv.prodAssoc)

theorem inE_apply (p : α × (β × γ)) : inE p = (p.2.1, (p.1, p.2.2)) := rfl

theorem inE_mp (μa : Measure α) (μb : Measure β) (μc : Measure γ) [SFinite μa] [SFinite μb] [SFinite μc] :
    MeasurePreserving (inE : α × (β × γ) ≃ᵐ β × (α × γ)) (μa.prod (μb.prod μc)) (μb.prod (μa.prod μc)) := by
  have e1 := MeasurePreserving.symm _ (measurePreserving_prodAssoc μa μb μc)
  have e2 := (Measure.measurePreserving_swap (μ := μa) (ν := μb)).prod (MeasurePreserving.id μc)
  have e3 := measurePreserving_prodAssoc μb μa μc
  exact e3.comp (e2.comp e1)

end gen

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

def rearr (k r : ℕ) (w : Equiv.Perm (Fin (r + 1))) :
    OD.RR k r w ≃ᵐ ((C2.LPidx w → ℂ) × (G.UT (r + 1) → ℂ)) × B.SS k r :=
  (MeasurableEquiv.prodCongr inE inE).trans Dx2.SL.swap4

@[simp] theorem rearr_apply (w : Equiv.Perm (Fin (r + 1))) (q : OD.RR k r w) :
    rearr k r w q = ((q.1.2.1, q.2.2.1), ((q.1.1, q.1.2.2), (q.2.1, q.2.2.2))) := rfl

private theorem measurePreserving_swap4 {α β γ δ : Type} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    [MeasurableSpace δ] (μa : Measure α) (μb : Measure β) (μc : Measure γ) (μd : Measure δ) [SFinite μa]
    [SFinite μb] [SFinite μc] [SFinite μd] :
    MeasurePreserving (Dx2.SL.swap4 : (α × β) × γ × δ ≃ᵐ (α × γ) × β × δ) ((μa.prod μb).prod (μc.prod μd))
      ((μa.prod μc).prod (μb.prod μd)) := by
  have e1 := measurePreserving_prodAssoc μa μb (μc.prod μd)
  have e2 := MeasurePreserving.symm _ (measurePreserving_prodAssoc μb μc μd)
  have e3 := (Measure.measurePreserving_swap (μ := μb) (ν := μc)).prod (MeasurePreserving.id μd)
  have e4 := measurePreserving_prodAssoc μc μb μd
  have e5 := MeasurePreserving.symm _ (measurePreserving_prodAssoc μa μc (μb.prod μd))
  have h := (e5.comp ((MeasurePreserving.id μa).prod (e4.comp (e3.comp e2)))).comp e1
  convert h using 1
  funext p
  rfl

theorem mp_rearr (S : B.RealPlaceData k r Wp Wq) (w : Equiv.Perm (Fin (r + 1))) {μ0 μ0' : Measure (Mt k r)}
    (hμ0 : B.IsHaarOn (C2.N0set k r S.z) μ0) (hμ0' : B.IsHaarOn (C2.N0set k r S.z') μ0') :
    MeasurePreserving (rearr k r w) (OD.nuR S w μ0 μ0')
      (((volume : Measure (C2.LPidx w → ℂ)).prod (volume : Measure (G.UT (r + 1) → ℂ))).prod
        ((S.μW.prod μ0).prod (S.μW'.prod μ0'))) := by
  haveI : IsFiniteMeasureOnCompacts S.μW := ⟨fun K hK => S.haarW.finite_compact K hK⟩
  haveI : IsFiniteMeasureOnCompacts S.μW' := ⟨fun K hK => S.haarW'.finite_compact K hK⟩
  haveI : IsFiniteMeasureOnCompacts μ0 := ⟨fun K hK => hμ0.finite_compact K hK⟩
  haveI : IsFiniteMeasureOnCompacts μ0' := ⟨fun K hK => hμ0'.finite_compact K hK⟩
  haveI t1 : SFinite S.μW := inferInstance
  haveI t2 : SFinite μ0 := inferInstance
  haveI t5 : SFinite S.μW' := inferInstance
  haveI t6 : SFinite μ0' := inferInstance
  haveI t3 : SFinite (volume : Measure (C2.LPidx w → ℂ)) := inferInstance
  haveI t4 : SFinite (volume : Measure (G.UT (r + 1) → ℂ)) := inferInstance
  have h1 := (inE_mp S.μW (volume : Measure (C2.LPidx w → ℂ)) μ0).prod
    (inE_mp S.μW' (volume : Measure (G.UT (r + 1) → ℂ)) μ0')
  have h2 := measurePreserving_swap4 (volume : Measure (C2.LPidx w → ℂ)) (S.μW.prod μ0)
    (volume : Measure (G.UT (r + 1) → ℂ)) (S.μW'.prod μ0')
  exact h2.comp h1

end

end Formalism.FourierDecayAlt.P.StabilizerDisintegration.RE
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.SfiniteOfIsHaarOn
section
open MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P5

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd

theorem sfinite_of_isHaarOn {k r : ℕ} (U : Set (B.Mat k r)) (μ : Measure (Mt k r)) (h : B.IsHaarOn U μ) :
    SFinite μ := by
  haveI : IsFiniteMeasureOnCompacts μ := ⟨fun K hK => h.finite_compact K hK⟩
  infer_instance

theorem herAnalyticCOfE : HerAnalyticCOfE := by
  intro hE Wp Wq _ _ _ _ _ _ S _ _ P z z' π π' X μ L st l0 D hD hl1 hl2 hz hz' hπ hπ'
  obtain ⟨hAdj, hSD, hFI, hMeas⟩ := hE Wp Wq S P z z' π π' X μ L st l0 D hD hl1 hl2 hz hz' hπ hπ'
  haveI : SFinite μ := sfinite_of_isHaarOn _ μ hD.2.1
  have hTI := topIdentFromParts (S := S) P z z' π π' X μ L st (herK S P z z' π π' L st l0 D) l0 hD
    Formalism.FourierDecayAlt.P.frame_of_admissible_word ofWordRR hAdj
  have hXK := xKappaOfNF Formalism.FourierDecayAlt.P.normal_form_actual kappaFibrePos Wp Wq P z z' π π' X μ L st l0 hD
  have hTD := topDensNonnegOfKappa Wp Wq S P z z' π π' X μ L st l0 (herK S P z z' π π' L st l0 D) hD hl1 hl2 hXK
  exact ⟨hAdj, hSD, hFI, integral_formula_of_steps Wp Wq S P z z' π π' μ L st l0 _ hTI hTD herK_sliceIn hSD hMeas⟩

theorem thmPActualOfE (hZS : NF.ActualZetaSmooth) (hE : HerAnalyticEAll) : ThmPActual :=
  thmPActualOfZ hZS (herAnalyticCOfE hE)

theorem herAnalyticEOfF (hM : TopDensMeasAll) (hF : HerAnalyticFAll) : HerAnalyticEAll := by
  intro Wp Wq _ _ _ _ _ _ S _ _ P z z' π π' X μ L st l0 D hD hl1 hl2 hz hz' hπ hπ'
  obtain ⟨hAdj, hSD, hFI⟩ := hF Wp Wq S P z z' π π' X μ L st l0 D hD hl1 hl2 hz hz' hπ hπ'
  exact ⟨hAdj, hSD, hFI, hM Wp Wq S P z z' π π' μ L st _⟩

theorem thmPActualOfCoreMZ (hZS : NF.ActualZetaSmooth) (hM : TopDensMeasAll) (hF : HerAnalyticFAll) : ThmPActual :=
  thmPActualOfE hZS (herAnalyticEOfF hM hF)

end Formalism.FourierDecayAlt.P5
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.ToStdAppend
section
namespace Formalism.FourierDecayAlt.P.GermFibreKernels

open Formalism.FourierDecayAlt NumberField

noncomputable section

def fs (r : ℕ) (g : ℝ) (b s : ℕ) (t : ℂ) : ℂ :=
  (((g / (2 * Real.pi)) ^ S6.nuBlock (r : ℤ) (b : ℤ) (s : ℤ) : ℝ) : ℂ) * Complex.I ^ (s - 1) * t

theorem toStd_append' (r : ℕ) (g : ℝ) : ∀ (P Q : C.LPt) (b : ℕ),
    D.toStd r g b (P ++ Q) = D.toStd r g b P ++ D.toStd r g (b + D.ptSize P) Q
  | [], Q, b => by simp [D.toStd, D.ptSize]
  | (s, t) :: rest, Q, b => by
    have ih := toStd_append' r g rest Q (b + s)
    simp only [List.cons_append, D.toStd, ih, D.ptSize, List.map_cons, List.sum_cons, add_assoc]

theorem toStd_germPts (r : ℕ) (g : ℝ) (h : C.LPt) (s : ℕ) (t c z : ℂ) :
    D.toStd r g 1 (h ++ [(s - 1, t), (1, c)]) =
      D.toStd r g 1 h ++ [(s - 1, fs r g (1 + D.ptSize h) (s - 1) t), (1, fs r g (1 + D.ptSize h + (s - 1)) 1 c)] ∧
    D.toStd r g 1 (h ++ [(s, z)]) = D.toStd r g 1 h ++ [(s, fs r g (1 + D.ptSize h) s z)] := by
  constructor
  · rw [toStd_append']
    simp [D.toStd, fs]
  · rw [toStd_append']
    simp [D.toStd, fs]

theorem lam_pos (g : ℝ) (hg : 0 < g) (n : ℤ) : 0 < (g / (2 * Real.pi)) ^ n := by positivity

theorem roots_std (r : ℕ) (g : ℝ) (hg : 0 < g) (b s : ℕ) (hs : 2 ≤ s) (t c z : ℂ) :
    fs r g b s z ^ s = (-1) ^ (s + 1) * (fs r g (b + (s - 1)) 1 c * fs r g b (s - 1) t ^ (s - 1)) ↔
      z ^ s = c * t ^ (s - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, s = m + 2 := ⟨s - 2, by omega⟩
  have e1 : m + 2 - 1 = m + 1 := by omega
  have e2 : m + 1 - 1 = m := by omega
  simp only [e1]
  unfold fs
  simp only [e1, e2, Nat.sub_self, pow_zero, mul_one]
  set q := g / (2 * Real.pi) with hq
  have hq0 : q ≠ 0 := (div_pos hg (by positivity)).ne'
  set L3 := ((q ^ S6.nuBlock (r : ℤ) (b : ℤ) ((m + 2 : ℕ) : ℤ) : ℝ) : ℂ) with hL3d
  set L2 := ((q ^ S6.nuBlock (r : ℤ) ((b + (m + 1) : ℕ) : ℤ) ((1 : ℕ) : ℤ) : ℝ) : ℂ) with hL2d
  set L1 := ((q ^ S6.nuBlock (r : ℤ) (b : ℤ) ((m + 1 : ℕ) : ℤ) : ℝ) : ℂ) with hL1d
  have hL : L3 ^ (m + 2) = L2 * L1 ^ (m + 1) := by
    rw [hL3d, hL2d, hL1d, ← Complex.ofReal_pow, ← Complex.ofReal_pow, ← Complex.ofReal_mul]
    congr 1
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add₀ hq0]
    congr 1
    unfold S6.nuBlock
    push_cast; ring
  have hI : (Complex.I ^ (m + 1)) ^ (m + 2) = (-1) ^ (m + 2 + 1) * (Complex.I ^ m) ^ (m + 1) := by
    rw [← pow_mul, ← pow_mul]
    have : (m + 1) * (m + 2) = m * (m + 1) + 2 * (m + 1) := by ring
    rw [this, pow_add, pow_mul Complex.I 2, Complex.I_sq]
    have h3 : (-1 : ℂ) ^ (m + 2 + 1) = (-1) ^ (m + 1) := by
      rw [show m + 2 + 1 = (m + 1) + 2 by ring, pow_add]; norm_num
    rw [h3]; ring
  have hL3 : L3 ≠ 0 := Complex.ofReal_ne_zero.mpr (zpow_ne_zero _ hq0)
  set K := L3 ^ (m + 2) * (Complex.I ^ (m + 1)) ^ (m + 2) with hK
  have eL : (L3 * Complex.I ^ (m + 1) * z) ^ (m + 2) = K * z ^ (m + 2) := by rw [hK]; ring
  have eR : (-1) ^ (m + 2 + 1) * (L2 * c * (L1 * Complex.I ^ m * t) ^ (m + 1)) = K * (c * t ^ (m + 1)) := by
    rw [hK, hI, hL]; ring
  rw [eL, eR]
  have h0 : K ≠ 0 := mul_ne_zero (pow_ne_zero _ hL3) (pow_ne_zero _ (pow_ne_zero _ Complex.I_ne_zero))
  exact mul_right_inj' h0

section loc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)]

theorem betaU_eq : U.betaU = 2 * Complex.I := by
  simp [U.betaU, Formalism.QuantumDeterminants.cStd]

theorem char_std (S : C.HidaSetting E Wp Wq) (hg : (0 : ℝ) < (S.g : ℝ)) (b s : ℕ) (hs : 2 ≤ s) (t z : ℂ) (ht : t ≠ 0) :
    G.psi U.betaU ((s : ℂ) * fs S.G.r (S.g : ℝ) b s z / fs S.G.r (S.g : ℝ) b (s - 1) t) =
      KB.psiL S (-((s : ℂ) * t⁻¹)) z := by
  obtain ⟨m, rfl⟩ : ∃ m, s = m + 2 := ⟨s - 2, by omega⟩
  have e1 : m + 2 - 1 = m + 1 := by omega
  have e2 : m + 1 - 1 = m := by omega
  rw [← GermRealisation.psi_neg_betaL]
  unfold fs
  simp only [e1, e2]
  set q := (S.g : ℝ) / (2 * Real.pi) with hq
  have hq0 : 0 < q := div_pos hg (by positivity)
  have hL : q ^ S6.nuBlock (S.G.r : ℤ) (b : ℤ) ((m + 2 : ℕ) : ℤ) =
      q⁻¹ * q ^ S6.nuBlock (S.G.r : ℤ) (b : ℤ) ((m + 1 : ℕ) : ℤ) := by
    rw [← zpow_neg_one, ← zpow_add₀ hq0.ne']
    congr 1
    unfold S6.nuBlock; push_cast; ring
  have hL1 : (q ^ S6.nuBlock (S.G.r : ℤ) (b : ℤ) ((m + 1 : ℕ) : ℤ) : ℝ) ≠ 0 := (zpow_pos hq0 _).ne'
  rw [hL]
  unfold G.psi
  congr 3
  rw [betaU_eq]
  unfold GermRealisation.betaL
  have hq' : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hq0.ne'
  have hL1' : ((q ^ S6.nuBlock (S.G.r : ℤ) (b : ℤ) ((m + 1 : ℕ) : ℤ) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hL1
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hgc : ((S.g : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hg.ne'
  simp only [Complex.ofReal_mul, Complex.ofReal_inv]
  generalize ((q ^ S6.nuBlock (S.G.r : ℤ) (b : ℤ) ((m + 1 : ℕ) : ℤ) : ℝ) : ℂ) = L at hL1' ⊢
  congr 1
  rw [hq]
  push_cast
  rw [pow_succ]
  field_simp
  ring_nf
  rw [Complex.I_sq]
  ring

end loc

end

end Formalism.FourierDecayAlt.P.GermFibreKernels
end

