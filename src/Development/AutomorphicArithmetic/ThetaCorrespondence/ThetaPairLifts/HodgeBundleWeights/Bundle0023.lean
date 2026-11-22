import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.TamagawaNumberSpecialUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3333
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ToKnownTheoremsOf
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle0022
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3343
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3336
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle0015
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3345
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEffCartierCompl
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Hypotheses2
import Development.WeilBound.CoreStatements.NefModelVolumes.NormGenValLe
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.LocalUnitMapSurjective

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ArchimedeanSectionIntegralFrame
section
section
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore
namespace GlobalTheory.FlatCore.Bdry
theorem nval_evI_eq_zero_alt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.CanonicalExtensionRankOne → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), Laws U x → ∀ (Z : Comp Xo c) (τ : Psi H) (s : ArchSec U x Z (flatWt Dw τ)) (T : CDVR) (io : c.F →+* T.Fr) (y₀ : IntFr Xo c T io), (∀ a, a ≠ 0 → vV T.V (io a) = 0) → (letI := io.toAlgebra; LiesOn Z y₀.1) → nval T.V 1 (evI y₀ s.sig) = 0 := by
  intro hP hQ2 E _ _ _ H Dw l Xo c r U x hL Z τ s T io y₀ hv hZ
  obtain ⟨s₀, hs₀⟩ := _root_.GlobalTheory.T.boundary_isUnit_at_eqChar_points hP hQ2 E H Dw l Xo c r U x hL Z τ ⟨s⟩
  obtain ⟨a, ha, hsa⟩ := GlobalTheory.T.constLengthArchSection_eq_smul_of_same_weight E H Dw l Xo c r U x hL.unf hL.geo Z (flatWt Dw τ) s₀ s
  have h0 : io a ≠ 0 := (map_ne_zero io).2 ha
  rw [hsa, evI_smul, nval_mul, hs₀ T io y₀ hv hZ, nval_of_ne h0, hv a ha]
  simp
end GlobalTheory.FlatCore.Bdry
end

section
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_section_integral_frame_of_laws : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.CanonicalExtensionRankOne → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), Laws U x → ∀ (Z : Comp Xo c) (τ : Psi H) (s : ArchSec U x Z (flatWt Dw τ)) (T : CDVR) (io : c.F →+* T.Fr) (y₀ : IntFr Xo c T io), (∀ a, a ≠ 0 → vV T.V (io a) = 0) → (letI := io.toAlgebra; LiesOn Z y₀.1) → nval T.V 1 (evI y₀ s.sig) = 0 := by
  first | exact @_root_.GlobalTheory.FlatCore.Bdry.nval_evI_eq_zero_alt | exact _root_.GlobalTheory.FlatCore.Bdry.nval_evI_eq_zero_alt | (intros; apply _root_.GlobalTheory.FlatCore.Bdry.nval_evI_eq_zero_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ExistsFlatUnitSection
section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000
noncomputable section
namespace GlobalTheory.FlatUnit
open GlobalTheory.FlatLine
theorem exists_flat_unit_section : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∃ N : ℕ, 0 < N ∧ ∀ w : GlobalTheory.AllWt.Psi T.Q.H → ℤ, ∃ (φ φ' : Rul Y.d.Xo₂ Y.d.c₂) (t : Y.d.c₂.F), φ ∈ GlobalTheory.AllWt.secZ Y.d.Xo₂ Y.d.c₂ (GlobalTheory.AllWt.exOf (T.Q.Dw j) (GlobalTheory.FlatLine.parWt (T.Q.Dw j) fun τ => (N : ℤ) * w τ) 0) ∧ t ≠ 0 ∧ φ * φ' = t • 1 ∧ (∀ la', ∀ v ∈ valSet Y.d.Xo₂ Y.d.c₂ (algCls Y.d.Xo₂ Y.d.c₂) la', 0 ≤ v φ') ∧ ∀ σ, GoodEmb Y.d.c₂ σ → ∀ kk, ∃ C : ℝ, ∀ y ∈ ((Y.U σ).X kk).dom, ((Y.U σ).X kk).pnorm (GlobalTheory.AllWt.modelWt (Y.U σ) (wtOf (T.Q.Dw j) (GlobalTheory.FlatLine.parWt (T.Q.Dw j) fun τ => (N : ℤ) * w τ) 0) kk) (rdU (Y.U σ) φ kk) y ≤ C := by
  intro hP D T j Y e o hY hE
  obtain ⟨N, hN, hA⟩ := _root_.GlobalTheory.T.flat_unit_exists_at_every_level hP D T j Y e o hY hE
  refine ⟨N, hN, fun w => ?_⟩
  classical
  let G : Psi T.Q.H → WTZ D.host.E := fun τ => wtOf (T.Q.Dw j) ((N : ℤ) • flatWt (T.Q.Dw j) τ) 0
  let φw : GlobalTheory.AllWt.Weight (T.Q.Dw j) →+ WTZ D.host.E :=
    { toFun := fun la => wtOf (T.Q.Dw j) la 0, map_zero' := GlobalTheory.AllWt.wtOf_zero,
      map_add' := fun a b => wtOf_add' a b }
  have hsum : wtOf (T.Q.Dw j) (parWt (T.Q.Dw j) fun τ => (N : ℤ) * w τ) 0 = ∑ τ, (-w τ) • G τ := by
    rw [parWt_eq_sum]
    show φw _ = _
    rw [map_sum]
    refine Finset.sum_congr (Finset.eq_univ_of_forall fun x => by simp) fun τ _ => ?_
    show φw _ = (-w τ) • φw _
    rw [map_zsmul, map_zsmul, smul_smul]
    congr 1; ring
  have hpair : ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) τ, ∃ s t : Rul Y.d.Xo₂ Y.d.c₂, (s ∈ GlobalTheory.AllWt.secZ Y.d.Xo₂ Y.d.c₂ (Formalism.L2.Pj.exZ (T.Q.Dw j) (G τ)) ∧ t ∈ GlobalTheory.AllWt.secZ Y.d.Xo₂ Y.d.c₂ (-Formalism.L2.Pj.exZ (T.Q.Dw j) (G τ)) ∧ GlobalTheory.FlatLine.idem Z * s = s ∧ GlobalTheory.FlatLine.idem Z * t = t ∧ s * t = GlobalTheory.FlatLine.idem Z ∧ (∀ σ, GoodEmb Y.d.c₂ σ → ∃ C : ℝ, ∀ z ∈ framesOn (Y.U σ) Z, GlobalTheory.AllWt.homN (Y.U σ) (xiR D) (G τ) s z ≤ C ∧ GlobalTheory.AllWt.homN (Y.U σ) (xiR D) (-(G τ)) t z ≤ C)) ∧ ∃ m : ℕ, 0 < m ∧ ∀ la, ∀ v ∈ GlobalTheory.FlatLine.valOn Z la, 0 ≤ v ((m : Y.d.c₂.F) • s) ∧ 0 ≤ v ((m : Y.d.c₂.F) • t) := fun Z τ => by
    obtain ⟨s, i, h⟩ := hA Z τ
    exact ⟨s, i, h, _root_.GlobalTheory.T.inverse_of_flat_unit_isIntegral hP D T j Y e o hY hE (N : ℤ) Z τ s i h⟩
  have hZ : ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂), ∃ s t : Rul Y.d.Xo₂ Y.d.c₂, (s ∈ GlobalTheory.AllWt.secZ Y.d.Xo₂ Y.d.c₂ (Formalism.L2.Pj.exZ (T.Q.Dw j) (wtOf (T.Q.Dw j) (parWt (T.Q.Dw j) fun τ => (N : ℤ) * w τ) 0)) ∧ t ∈ GlobalTheory.AllWt.secZ Y.d.Xo₂ Y.d.c₂ (-Formalism.L2.Pj.exZ (T.Q.Dw j) (wtOf (T.Q.Dw j) (parWt (T.Q.Dw j) fun τ => (N : ℤ) * w τ) 0)) ∧ GlobalTheory.FlatLine.idem Z * s = s ∧ GlobalTheory.FlatLine.idem Z * t = t ∧ s * t = GlobalTheory.FlatLine.idem Z ∧ (∀ σ, GoodEmb Y.d.c₂ σ → ∃ C : ℝ, ∀ z ∈ framesOn (Y.U σ) Z, GlobalTheory.AllWt.homN (Y.U σ) (xiR D) (wtOf (T.Q.Dw j) (parWt (T.Q.Dw j) fun τ => (N : ℤ) * w τ) 0) s z ≤ C ∧ GlobalTheory.AllWt.homN (Y.U σ) (xiR D) (-(wtOf (T.Q.Dw j) (parWt (T.Q.Dw j) fun τ => (N : ℤ) * w τ) 0)) t z ≤ C)) ∧ ∃ m : ℕ, 0 < m ∧ ∀ la, ∀ v ∈ GlobalTheory.FlatLine.valOn Z la, 0 ≤ v ((m : Y.d.c₂.F) • s) ∧ 0 ≤ v ((m : Y.d.c₂.F) • t) := fun Z => by
    obtain ⟨s, t, h⟩ := GlobalTheory.T.exists_boundedUnit_sum_component _ _ _ _ Y.d.Xo₂ Y.d.c₂ D.R.r Y.U (xiR D) Z (Psi T.Q.H) G
      (fun τ => GlobalTheory.AllWt.even_wtOf _ _) (hpair Z) (fun τ => -w τ)
    refine ⟨s, t, ?_⟩
    rw [hsum]
    exact h
  choose s t hst using hZ
  haveI := CompFin.finite_comp Y.d.Xo₂ Y.d.c₂
  haveI := Fintype.ofFinite (Comp Y.d.Xo₂ Y.d.c₂)
  choose m hm hv using fun Z => (hst Z).2
  have hsZ : ∀ Z, s Z ∈ GlobalTheory.AllWt.suppOn Z := fun Z => by
    rw [← (hst Z).1.2.2.1, mul_comm]; exact GlobalTheory.AllWt.mul_mem_suppOn _ (idem_mem_suppOn Z)
  have htZ : ∀ Z, t Z ∈ GlobalTheory.AllWt.suppOn Z := fun Z => by
    rw [← (hst Z).1.2.2.2.1, mul_comm]; exact GlobalTheory.AllWt.mul_mem_suppOn _ (idem_mem_suppOn Z)
  have hM0 : ((∏ Z, m Z : ℕ) : Y.d.c₂.F) ≠ 0 :=
    Nat.cast_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun Z _ => (hm Z).ne')
  refine ⟨∑ Z, s Z, ((∏ Z, m Z : ℕ) : Y.d.c₂.F) • ∑ Z, t Z, ((∏ Z, m Z : ℕ) : Y.d.c₂.F),
    Submodule.sum_mem _ fun Z _ => (hst Z).1.1, hM0, ?_, ?_, ?_⟩
  · rw [mul_smul_comm, Finset.sum_mul_sum]
    have hd : ∑ Z, ∑ Z', s Z * t Z' = ∑ Z, idem Z := Finset.sum_congr rfl fun Z _ => by
      rw [Finset.sum_eq_single Z]
      · exact (hst Z).1.2.2.2.2.1
      · intro Z' _ hne
        rw [← (hst Z).1.2.2.1, ← (hst Z').1.2.2.2.1, mul_mul_mul_comm, idem_mul_idem_of_ne (Ne.symm hne),
          zero_mul]
      · intro h; exact absurd (Finset.mem_univ Z) h
    rw [hd, sum_idem]
  · intro la' v hv'
    have hV := isVal_valSet la' v hv'
    rw [Finset.smul_sum]
    refine val_sum_nonneg hV _ _ fun Z _ => ?_
    rcases mem_valOn_or (Z := Z) hv' with h | h
    · have hsplit : ((∏ Z, m Z : ℕ) : Y.d.c₂.F) • t Z =
          (∏ Z' ∈ Finset.univ.erase Z, m Z') • ((m Z : Y.d.c₂.F) • t Z) := by
        rw [← Finset.mul_prod_erase Finset.univ m (Finset.mem_univ Z), Nat.cast_mul, mul_comm, mul_smul]
        exact Nat.cast_smul_eq_nsmul Y.d.c₂.F _ _
      rw [hsplit]
      exact val_nsmul_nonneg hV _ (hv Z la' v h).2
    · rw [h _ (Submodule.smul_mem _ _ (htZ Z))]
      exact le_top
  · intro σ hσ kk
    choose C hC using fun Z => (hst Z).1.2.2.2.2.2 σ hσ
    have hL := GlobalTheory.AllWt.lieFacZ_pos (Dw := T.Q.Dw j) (xiR D)
      (wtOf (T.Q.Dw j) (parWt (T.Q.Dw j) fun τ => (N : ℤ) * w τ) 0)
    refine ⟨∑ Z, max (C Z) 0 / GlobalTheory.AllWt.lieFacZ (T.Q.Dw j) (xiR D)
      (wtOf (T.Q.Dw j) (parWt (T.Q.Dw j) fun τ => (N : ℤ) * w τ) 0), fun y hy => ?_⟩
    have e1 : rdU (Y.U σ) (∑ Z, s Z) kk = ∑ Z, rdU (Y.U σ) (s Z) kk := by
      rw [map_sum, Finset.sum_apply]
    rw [e1]
    refine (pnorm_sum_le _ _ _ _ y).trans (Finset.sum_le_sum fun Z _ => ?_)
    by_cases hz : (⟨kk, y⟩ : Σ k, ReciprocityTheory.ChartRestriction.G.FD.Frame ((Y.U σ).X k).Ψ D.R.r) ∈ framesOn (Y.U σ) Z
    · rw [le_div_iff₀ hL]
      have h1 := (hC Z ⟨kk, y⟩ hz).1
      calc _ = GlobalTheory.AllWt.homN (Y.U σ) (xiR D) (wtOf (T.Q.Dw j) (parWt (T.Q.Dw j) fun τ => (N : ℤ) * w τ) 0)
            (s Z) ⟨kk, y⟩ := by unfold GlobalTheory.AllWt.homN GlobalTheory.AllWt.ptN; ring
        _ ≤ C Z := h1
        _ ≤ max (C Z) 0 := le_max_left _ _
    · have h0 : rdU (Y.U σ) (s Z) kk y = 0 := GlobalTheory.AllWt.rdU_eq_zero (Y.U σ) (hsZ Z) hz
      have : ((Y.U σ).X kk).pnorm (GlobalTheory.AllWt.modelWt (Y.U σ)
          (wtOf (T.Q.Dw j) (parWt (T.Q.Dw j) fun τ => (N : ℤ) * w τ) 0) kk) (rdU (Y.U σ) (s Z) kk) y = 0 := by
        unfold ReciprocityTheory.ChartRestriction.G.FD.Data.pnorm; rw [h0, norm_zero, zero_mul]
      rw [this]
      exact div_nonneg (le_max_right _ _) hL.le
end GlobalTheory.FlatUnit
end
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.detLine_flat_unit_exists : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∃ N : ℕ, 0 < N ∧ ∀ w : GlobalTheory.AllWt.Psi T.Q.H → ℤ, ∃ (φ φ' : Rul Y.d.Xo₂ Y.d.c₂) (t : Y.d.c₂.F), φ ∈ GlobalTheory.AllWt.secZ Y.d.Xo₂ Y.d.c₂ (GlobalTheory.AllWt.exOf (T.Q.Dw j) (GlobalTheory.FlatLine.parWt (T.Q.Dw j) fun τ => (N : ℤ) * w τ) 0) ∧ t ≠ 0 ∧ φ * φ' = t • 1 ∧ (∀ la', ∀ v ∈ valSet Y.d.Xo₂ Y.d.c₂ (algCls Y.d.Xo₂ Y.d.c₂) la', 0 ≤ v φ') ∧ ∀ σ, GoodEmb Y.d.c₂ σ → ∀ kk, ∃ C : ℝ, ∀ y ∈ ((Y.U σ).X kk).dom, ((Y.U σ).X kk).pnorm (GlobalTheory.AllWt.modelWt (Y.U σ) (wtOf (T.Q.Dw j) (GlobalTheory.FlatLine.parWt (T.Q.Dw j) fun τ => (N : ℤ) * w τ) 0) kk) (rdU (Y.U σ) φ kk) y ≤ C := by
  first | exact @_root_.GlobalTheory.FlatUnit.exists_flat_unit_section | exact _root_.GlobalTheory.FlatUnit.exists_flat_unit_section | (intros; apply _root_.GlobalTheory.FlatUnit.exists_flat_unit_section <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ProportionalityOfLocalCharts
section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open Filter
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompProport
section Flag
open GlobalTheory.VarFlag
open GlobalTheory.ShFam (EigFrame FlagCpt FlagTor)
open GlobalTheory.Toroidal (gen genι genStr genBd genBdIdeal HasToricChart)
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}
end Flag
section Good
open Formalism.BasicNotions Formalism.L2.Theta GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegCmp
open GlobalTheory.Toroidal (genBd HasToricChart)
theorem growth_eq_top_self_intersection (hP : _root_.GlobalTheory.CovTop.Hypotheses'') (hN : GlobalTheory.Published.NefNumerics)
    (hL : GlobalTheory.Published.SemiAbelianLieSeminegative) {D : D7} {T : Core D} {j : ℕ} {Y : Deep T j} {e : ℕ} {o : ℝ}
    (hY : Y.Good e o) (hf : 2 < Module.finrank ℚ D.host.E / 2) (Z : Comp Y.d.Xo₂ Y.d.c₂) (TF : TorFlag Y.d.Xo₂ Y.d.c₂)
    [IsIntegral (Y₀ TF.X Z)] (hd : topologicalKrullDim (Y₀ TF.X Z) = CompHt.dimFlag (T.Q.Dw j))
    {la : AllWt.Weight (T.Q.Dw j)} (hla : ∀ τ, StrictAnti (la τ)) :
    CompHt.growthOn Y.U Z (AllWt.wtOf (T.Q.Dw j) la 0) = ENNReal.ofReal
      ((letI := algebraΓOfHom (str₀ TF.X Z); topSelfIntersection Y.d.c₂.F (L₀ TF.X Z la) (CompHt.dimFlag (T.Q.Dw j)) : ℤ) : ℝ) := by
  have hg : genericPoint (Y₀ TF.X Z) ∉ bd₀ TF.X Z := fun h => by
    obtain ⟨y, hy⟩ := (dense_U₀ TF.X Z).nonempty
    exact h ((genericPoint_specializes y).mem_open (U₀ TF.X Z).isOpen hy)
  have hc : ∀ m : ℕ, cls (L₀ TF.X Z (m • la)) (isLB_L₀ _ _ _) = m • cls (L₀ TF.X Z la) (isLB_L₀ _ _ _) := fun m => by
    have a := cls_common_add (common₀ TF.X Z)
    induction m with
    | zero =>
      have := a 0 0
      simp only [add_zero] at this
      rw [zero_nsmul, zero_nsmul]
      exact left_eq_add.1 this
    | succ m ih => rw [succ_nsmul, succ_nsmul, ← ih]; exact a _ _
  rw [← growth_vanishing hN _ _ (str₀ TF.X Z) _ (GlobalTheory.VarFlag.isVariety₀_flag _ _ _ _ _ _ TF Z hY.geo).2.1 hd _ hg _
    (isLB_L₀ _ _ la) (_root_.GlobalTheory.T.base_weight_line_bundle_is_nef hP hN hL _ _ _ _ _ _ TF Z hY.geo la (gapGe_of_strictAnti hla)) _ _ hc
    (fun m => vanBd TF.X Z (m • la)) fun _ _ => Iff.rfl, CompHt.growthOn]
  congr 1
  funext m
  have h1 := GlobalTheory.T.cuspForms_extend_vanish_compactifiedFlagSpace D T j Y e o hY hf Z TF (m • la)
  have h2 := le_antisymm h1.space_le (vanBd_le_space D T j Y e o hY hf Z TF (m • la))
  rw [CompHt.nsmul_wtOf, smul_zero, ← h2]
  exact congrArg _ h1.equiv.rank_eq
theorem growth_eq_covolume (hP : _root_.GlobalTheory.CovTop.Hypotheses'') (hN : GlobalTheory.Published.NefNumerics)
    (hL : GlobalTheory.Published.SemiAbelianLieSeminegative) {D : D7} {T : Core D} {j : ℕ} {Y : Deep T j} {e : ℕ} {o : ℝ}
    (hY : Y.Good e o) (hf : 2 < Module.finrank ℚ D.host.E / 2) (TF : TorFlag Y.d.Xo₂ Y.d.c₂)
    (hc : ∀ x ∈ genBd TF.Y, HasToricChart TF.Y x) {σ : Y.d.c₂.F →+* ℂ} (hσ : GoodEmb Y.d.c₂ σ) :
    ∃ q : (Y.U σ).Comp ≃ Comp Y.d.Xo₂ Y.d.c₂,
      (∀ k (x : ((Y.U σ).X k).dom) (s : Sp (CAt σ)), GlobalTheory.AllWt.ptF ((Y.U σ).un k x) s ∈ (q k).1) ∧
      ∀ k (la : AllWt.Weight (T.Q.Dw j)), (∀ τ, StrictAnti (la τ)) →
        CompHt.growthOn Y.U (q k) (AllWt.wtOf (T.Q.Dw j) la 0) = ENNReal.ofReal
          (GlobalTheory.TrueCx.covol ((Y.U σ).X k) * (CompHt.dimFlag (T.Q.Dw j)).factorial /
            (CompHt.vdm (CompHt.stdWt (AllWt.Psi T.Q.H) ((T.Q.Dw j).p + (T.Q.Dw j).q)) : ℤ) * (CompHt.vdm la : ℤ)) := by
  obtain ⟨q, hq, h⟩ := topSelf_eq_covol hP.p16 TF hc hY.geo (Formalism.L2.PjFree.Unf.ofPj (Y.U σ)) hσ (hY.unf σ hσ)
  refine ⟨q, hq, fun k la hla => ?_⟩
  obtain ⟨_, hd, h⟩ := h k
  refine (_root_.GlobalTheory.CompProport.growth_eq_top_self_intersection hP hN hL hY hf _ TF hd hla).trans ?_
  rw [h, GlobalTheory.FlagPoly.flagDegFormula, CompHt.weylProd_eq,
    show ((CompHt.vdm la : ℤ) : ℝ) = _ from CompHt.map_vdm (Int.castRingHom ℝ) la]
  congr 1
  simp only [CompHt.dimFlag, eq_intCast]
  change GlobalTheory.TrueCx.covol ((Y.U σ).X k) * _ = _
  ring
theorem invariant_volume_eq_covolume (hP : _root_.GlobalTheory.CovTop.Hypotheses'') (hN : GlobalTheory.Published.NefNumerics)
    (hL : GlobalTheory.Published.SemiAbelianLieSeminegative) {D : D7} {T : Core D} {j : ℕ} {Y : Deep T j} {e : ℕ} {o : ℝ}
    (hY : Y.Good e o) (hf : 2 < Module.finrank ℚ D.host.E / 2) (TF : TorFlag Y.d.Xo₂ Y.d.c₂)
    (hc : ∀ x ∈ genBd TF.Y, HasToricChart TF.Y x) {σ : Y.d.c₂.F →+* ℂ} (hσ : GoodEmb Y.d.c₂ σ) :
    Proport Y.U ∧ ∃ q : (Y.U σ).Comp ≃ Comp Y.d.Xo₂ Y.d.c₂,
      (∀ k (x : ((Y.U σ).X k).dom) (s : Sp (CAt σ)), GlobalTheory.AllWt.ptF ((Y.U σ).un k x) s ∈ (q k).1) ∧
      ∀ k, CompHt.vZero Y.U (q k) = GlobalTheory.TrueCx.covol ((Y.U σ).X k) * (CompHt.dimFlag (T.Q.Dw j)).factorial /
        (CompHt.vdm (CompHt.stdWt (AllWt.Psi T.Q.H) ((T.Q.Dw j).p + (T.Q.Dw j).q)) : ℤ) := by
  obtain ⟨q, hq, h⟩ := _root_.GlobalTheory.CompProport.growth_eq_covolume hP hN hL hY hf TF hc hσ
  have hs : (0 : ℝ) < (CompHt.vdm (CompHt.stdWt (AllWt.Psi T.Q.H) ((T.Q.Dw j).p + (T.Q.Dw j).q)) : ℤ) :=
    Int.cast_pos.2 (CompHt.vdm_pos CompHt.strictAnti_stdWt)
  have hv : ∀ k, CompHt.vZero Y.U (q k) = GlobalTheory.TrueCx.covol ((Y.U σ).X k) * (CompHt.dimFlag (T.Q.Dw j)).factorial /
      (CompHt.vdm (CompHt.stdWt (AllWt.Psi T.Q.H) ((T.Q.Dw j).p + (T.Q.Dw j).q)) : ℤ) := fun k => by
    have := GlobalTheory.TrueCx.covol_pos ((Y.U σ).X k)
    rw [CompHt.vZero, h k _ CompHt.strictAnti_stdWt, ENNReal.toReal_ofReal (by positivity), mul_div_cancel_right₀ _ hs.ne']
  refine ⟨fun Z la hla => ?_, q, hq, hv⟩
  obtain ⟨k, rfl⟩ := q.surjective Z
  rw [h k la hla, CompHt.topDeg, hv]
theorem proportionality_of_local_charts (hP : _root_.GlobalTheory.CovTop.Hypotheses'') (hN : GlobalTheory.Published.NefNumerics)
    (hL : GlobalTheory.Published.SemiAbelianLieSeminegative) {D : D7} {T : Core D} {j : ℕ} {Y : Deep T j} {e : ℕ} {o : ℝ}
    (hY : Y.Good e o) (hf : 2 < Module.finrank ℚ D.host.E / 2) (TF : TorFlag Y.d.Xo₂ Y.d.c₂)
    (hc : ∀ x ∈ genBd TF.Y, HasToricChart TF.Y x) : Proport Y.U ∧ ∀ Z, 0 < CompHt.vZero Y.U Z := by
  obtain ⟨h, q, -, hv⟩ := _root_.GlobalTheory.CompProport.invariant_volume_eq_covolume hP hN hL hY hf TF hc (σ := Y.d.c₂.F.val.toRingHom) rfl
  refine ⟨h, fun Z => ?_⟩
  obtain ⟨k, rfl⟩ := q.surjective Z
  rw [hv]
  exact div_pos (mul_pos (GlobalTheory.TrueCx.covol_pos _) (by positivity)) (Int.cast_pos.2 (CompHt.vdm_pos CompHt.strictAnti_stdWt))
end Good
end GlobalTheory.CompProport
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.WeilHeightArchimedeanContribution
section
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
noncomputable section
namespace PositivityTheory.Xj7N
open GlobalTheory GlobalTheory.CompHS GlobalTheory.Adelic
section Generic
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}
variable {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ} {D : D7} {V : (c.F →+* ℂ) → HSp D}
  {dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r}
end Generic
section Main
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}
  {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ} {D : D7} {V : (c.F →+* ℂ) → HSp D}
  {dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r}
end Main
theorem weil_height_archimedean_contribution : NV → _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (u : GlobalTheory.AllWt.Weight (T.Q.Dw j)) (t : ℝ), GoodOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) u 0) → GlobalTheory.DegVal.BirOn Y.U Z (wtOf (T.Q.Dw j) u 0) → NoBase Y.U Z (wtOf (T.Q.Dw j) u 0) → 0 < Y.dg u Z → ∀ (N m : ℕ) (b : Module.Basis (Fin N) Y.d.c₂.F (cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0))) (g : Matrix (Fin N) (Fin m) Y.d.c₂.F) (A : (Y.d.c₂.F →+* ℂ) → Matrix (Fin N) (Fin N) ℂ), IsFrame (normOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) u 0)) (latOn Y.U Z (wtOf (T.Q.Dw j) u 0)) b g A → ∀ (σ : Y.d.c₂.F →+* ℂ) (ρ : Om Z →+* ℂ), ρ.comp (algebraMap Y.d.c₂.F (Om Z)) = σ → ∀ τ : ℕ, 0 < τ → ∀ f ∈ smallL Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) u 0) τ t, ‖ρ (genVal Z (f : Rul Y.d.Xo₂ Y.d.c₂))‖ ≤ Real.exp (τ * t) * GlobalTheory.Adelic.archSize (A σ) (fun i => ρ (genVal Z ((b i : cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0)) : Rul Y.d.Xo₂ Y.d.c₂))) ^ τ := by
  intro hNV hP D T j Y e o hY hf Z u t hG hB _ _ N m b g A hF σ ρ hρ τ _ f hfs
  have hd : ∀ σ, GoodEmb Y.d.c₂ σ → ∀ g, (Y.dict σ g).2 ∈ ((Y.U σ).X (Y.dict σ g).1).dom := fun σ hσ => by
    obtain ⟨th, hr, hth, hdU⟩ := hY.dictU σ hσ
    exact hdU.2.2.2.1
  have hD : 1 ≤ GlobalTheory.FlagTan.dimFlag (T.Q.Dw j) := by
    have h2 : D.R.r = (T.Q.Dw j).p + (T.Q.Dw j).q :=
      (hY.unf _ (goodEmb_goodOf Y.d.c₂ Y.d.c₂.F.val.toRingHom)).1
    have hm := D.R.two_le_m
    have hk := D.R.m_add_three_le_k
    have h3 : 2 ≤ (T.Q.Dw j).p + (T.Q.Dw j).q := by
      rw [← h2]; unfold Formalism.BasicNotions.Ranks.r; omega
    exact Nat.mul_pos (by omega) (Nat.choose_pos h3)
  obtain ⟨TF⟩ := DifferentiableLines.nonempty_toroidal_flag_bundle hP.p1 _ _ _ _ Y.d.Xo₂ Y.d.c₂ (GlobalTheory.CompHS.TorFlagEx.one_le_of_dimFlag hD)
  have hspan : ∀ σ, GoodEmb Y.d.c₂ σ → ∀ P ∈ holSub (Y.U σ).X (modelWt (Y.U σ) (wtOf (T.Q.Dw j) u 0)),
      ∃ Q ∈ Submodule.span ℂ (rdU (Y.U σ) '' (cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0) : Set (Rul Y.d.Xo₂ Y.d.c₂))),
        ∀ w ∈ framesOn (Y.U σ) Z, P w.1 w.2 = Q w.1 w.2 := fun σ hσ P hPh => by
    obtain ⟨m', as, fs, hfs', hPQ⟩ := _root_.PositivityTheory.Xj7N.local_unit_map_surjective hNV hP D T j Y e o hY hf Z TF u hG hB σ hσ P hPh
    choose g' hg hgf using fun i => GlobalTheory.T.extVan_section_has_cusp_form_match D T j Y e o hY hf Z TF u (fs i) (hfs' i)
    refine ⟨∑ i, as i • rdU (Y.U σ) (g' i), Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨g' i, hg i, rfl⟩), fun w hw => ?_⟩
    rw [hPQ w hw]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun i _ => by rw [hgf i σ hσ w hw]
  exact norm_small_le hY.unf hd (AllWt.even_wtOf u 0) hspan hF σ ρ hρ τ t f hfs
end PositivityTheory.Xj7N
end
end
end

