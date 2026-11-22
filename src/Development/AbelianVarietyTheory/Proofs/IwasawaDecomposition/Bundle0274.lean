import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0245
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LintegralCompactLe
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0126
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0222
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMulRightInvariantOfFundamentalDomain
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DefClassNum
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdeleClassFiniteness.Bundle0001
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdeleClassFiniteness.LatticeIdealNonzero
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GlNormOneAdelicQuotientVolumeOneEqResidue
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GlNormOneAdelicQuotientVolumeSiegelStep
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LineLatticeClassMeanTraceFormDualLattice
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0199
import Formalism.DegreeFormula.Statement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0034
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0001
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteUnitaryClassSetFinite
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0262
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
import Formalism.LocalToGlobal.HermitianForms.Bundle0006

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousMovPair
section
noncomputable section

open MeasureTheory
open scoped Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open GlobalTheory.FockCompare GlobalTheory.OrientedHeis GlobalTheory.ThetaGrowth
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.WeilSupBound

variable {D : D7} {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ Formalism.L2.Theta.AE D} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}
  {χS χT : (Formalism.L2.Theta.AE D)ˣ →* Circle} {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}

theorem continuous_mov_pair (hθ : IsInfFam θ) (u : RW T S) :
    Continuous fun p : GA D S × GA D T => mov θ p.1⁻¹ p.2⁻¹ u := by
  refine continuous_pi fun τ => ?_
  unfold mov
  simp only [inv_inv]
  exact (((GlobalTheory.RealWeil.continuous_compAt hθ τ _ _).comp
    ((GlobalTheory.RealWeil.continuous_mt T).2.comp continuous_snd)).matrix_mul continuous_const).matrix_mul
    ((GlobalTheory.RealWeil.continuous_compAt hθ τ _ _).comp ((GlobalTheory.RealWeil.continuous_mt S).1.comp continuous_fst))

theorem uniform_level_pair (hom : IsWeilDatumO ψ S T χS χT om) {U : AddSubgroup (WO S T)}
    (hU : IsOpen (U : Set (WO S T))) {C : Set (GA D S × GA D T)} (hC : IsCompact C) :
    ∃ K₀ ∈ 𝓝 (0 : WO S T), IsCompact K₀ ∧ ∀ p ∈ C, ∀ φ, IsThetaFunO ψ S T φ →
      (∀ u ∈ U, u.map (infPart D) = 0 → heisO ψ S T u φ = φ) → ∀ u ∈ K₀, u.map (infPart D) = 0 →
        heisO ψ S T u (om p φ) = om p φ := by
  obtain ⟨i1, i2, -⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  have hcont : Continuous fun z : WO S T × (GA D S × GA D T) => actO S T z.2.1⁻¹ z.2.2⁻¹ z.1 := by
    unfold actO
    simp only [inv_inv]
    exact (((GlobalTheory.RealWeil.continuous_mt T).2.comp (continuous_snd.comp continuous_snd)).matrix_mul
      continuous_fst).matrix_mul ((GlobalTheory.RealWeil.continuous_mt S).1.comp (continuous_fst.comp continuous_snd))
  have hev : ∀ᶠ u in 𝓝 (0 : WO S T), ∀ p ∈ C, actO S T p.1⁻¹ p.2⁻¹ u ∈ U := by
    refine hC.eventually_forall_of_forall_eventually fun p _ => ?_
    refine hcont.continuousAt.preimage_mem_nhds (hU.mem_nhds ?_)
    show actO S T p.1⁻¹ p.2⁻¹ 0 ∈ U
    unfold actO
    rw [Matrix.mul_zero, Matrix.zero_mul]
    exact U.zero_mem
  obtain ⟨K₀, h0, hsub, hK₀⟩ := LocallyCompactSpace.local_compact_nhds (X := WA T S) 0 _ hev
  refine ⟨K₀, h0, hK₀, fun ⟨g, h⟩ hp φ hφ hl u hu hinf => ?_⟩
  have hv : (actO S T g⁻¹ h⁻¹ u).map (infPart D) = 0 := by
    unfold actO
    rw [Matrix.map_mul, Matrix.map_mul, hinf, Matrix.mul_zero, Matrix.zero_mul]
  have e := hom.om_heis g h (actO S T g⁻¹ h⁻¹ u) φ hφ
  rw [hl _ (hsub hu _ hp) hv, actO_mul, mul_inv_cancel, mul_inv_cancel, actO_one] at e
  exact e.symm

theorem cube_bound_at (hom : IsWeilDatumO ψ S T χS χT om) (hc : Chart θ σ) {N : ℕ}
    (b : Module.Basis (Fin N) ℝ (RW T S)) {K₀ : Set (WO S T)} (h0 : K₀ ∈ 𝓝 (0 : WO S T)) (hK₀ : IsCompact K₀) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ p φ, IsThetaFunO ψ S T φ →
      (∀ u ∈ K₀, u.map (infPart D) = 0 → heisO ψ S T u (om p φ) = om p φ) → ∀ B : ℝ, (∀ w, ‖φ w‖ ≤ B) → ∀ y,
      ∫ t in Set.pi Set.univ (fun _ : Fin N => Set.Icc (0 : ℝ) 1),
        ‖om p φ (y + ∑ i, iotaW σ T S (t i • b i))‖ ^ 2 ≤ c * B ^ 2 := by
  obtain ⟨c, hc0, hcube⟩ := cube_bound hom hc b h0 hK₀
  refine ⟨c, hc0, fun ⟨g, h⟩ φ hφ hl B hB y => ?_⟩
  have e := hom.om_heis g h (actO S T g⁻¹ h⁻¹ y) φ hφ
  rw [actO_mul, mul_inv_cancel, mul_inv_cancel, actO_one] at e
  have hn := GlobalTheory.HeisOrtho.norm_heisO (S := S) (T := T) hom.std.1
  have key := hcube (g, h) _ (GlobalTheory.ThetaClosed.thetaClosed ψ θ hom.std hc.inf S T φ hφ |>.1 (actO S T g⁻¹ h⁻¹ y))
    (fun w hw => by
      generalize hu : w - iotaW σ T S (piW θ T S w) = u at hw
      have hinf : u.map (infPart D) = 0 := by
        have hp : piW θ T S u = 0 := by
          rw [← hu, AddMonoidHom.map_sub, hc.pi_iota, sub_self]
        ext i j
        exact ThetaCont.infPart_eq_zero hc _ fun τ => congrFun (congrFun (congrFun hp τ) i) j
      rw [e, hn, hn]
      conv_rhs => rw [← hl u hw hinf, hn, ← hu]
      congr 2
      abel_nf) B (fun w => by rw [hn]; exact hB _)
  simp only [e, hn, zero_add] at key
  simpa only [add_comm y] using key

theorem exists_sup_bound : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D)
    (χS χT : (Formalism.L2.Theta.AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)),
    IsWeilDatumO ψ S T χS χT om → ∀ f, IsThetaFunO ψ S T f → ∀ C : Set (GA D S × GA D T), IsCompact C →
      ∃ c : ℝ, ∀ p ∈ C, ∀ w, ‖om p f w‖ ≤ c := by
  intro D ψ S T χS χT om hom f hf C hC
  have hψ := hom.std
  obtain ⟨θ, hθ⟩ := hψ.2.1
  obtain ⟨σ, hc⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  have b := Module.finBasis ℝ (RW T S)
  generalize Module.finrank ℝ (RW T S) = N at b
  obtain ⟨U, hU, hl⟩ := hf.level
  obtain ⟨K₀, h0, hK₀, hlev⟩ := uniform_level_pair hom hU hC
  obtain ⟨c, hc0, hcube⟩ := cube_bound_at hom hc b h0 hK₀
  obtain ⟨C₁, hC₁0, hC₁⟩ := words_bound (dvL hc hψ S T) (fun w => (LinearMap.proj w).comp (thetaSub ψ S T).subtype)
    (fun m => theta_bounded hψ m.2) N ⟨f, hf⟩
  obtain ⟨κ, hκ⟩ := hC.exists_bound_of_continuousOn
    (f := fun (p : GA D S × GA D T) (i : Fin N) => mov θ p.1⁻¹ p.2⁻¹ (b i))
    (continuous_pi fun i => continuous_mov_pair hθ (b i)).continuousOn
  refine ⟨√(4 ^ N * (c * (C₁ * max 1 κ ^ N) ^ 2)), fun ⟨g, h⟩ hp w => ?_⟩
  let wd : List (RW T S) → thetaSub ψ S T := fun l => l.foldl (fun m z => dvL hc hψ S T z m) ⟨f, hf⟩
  let A : ℕ → Set (WO S T → ℂ) := fun p =>
    {F | ∃ l : List (RW T S), l.length ≤ p ∧ (∀ u ∈ l, ‖u‖ ≤ max 1 κ) ∧ F = om (g, h) (wd l).1}
  refine Real.le_sqrt_of_sq_le (sobolev_iter N 0 (fun i r => iotaW σ T S (r • b i)) A (c * (C₁ * max 1 κ ^ N) ^ 2) w
    (fun i => (hc.continuous_iota T S).comp (continuous_id.smul continuous_const))
    (fun p q hpq F ⟨l, h1, h2⟩ => ⟨l, h1.trans hpq, h2⟩) ?_ ?_ (om (g, h) f) ⟨[], le_rfl, by simp, rfl⟩)
  · rintro p _ ⟨l, h1, h2, rfl⟩
    have hF := hom.om_pres (g, h) _ (wd l).2
    refine ⟨hF.cont, fun i => ⟨_, ⟨l ++ [mov θ g⁻¹ h⁻¹ (b i)], by simpa using h1, fun u hu => ?_, ?_⟩,
      sobolev_step hc hψ (b i) hF⟩⟩
    · rcases List.mem_append.1 hu with hu | hu
      · exact h2 u hu
      · rw [List.mem_singleton.1 hu]
        exact ((norm_le_pi_norm (fun i => mov θ g⁻¹ h⁻¹ (b i)) i).trans (hκ (g, h) hp)).trans (le_max_right _ _)
    · rw [dv_om hom hc g h (b i) (wd l).2]
      simp only [wd, List.foldl_append]
      rfl
  · rintro _ ⟨l, h1, h2, rfl⟩
    exact hcube (g, h) _ (wd l).2 (hlev (g, h) hp _ (wd l).2 fun u hu h0 => words_level hc hψ h0 l _ (hl u hu h0)) _
      (hC₁ _ (le_max_left _ _) l (by simpa using h1) h2) w

end GlobalTheory.WeilSupBound

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CovolumeUnitDetNormSlabLatticeAutLtTop
section
open NumberField IsDedekindDomain Matrix MeasureTheory Topology
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL

noncomputable section

namespace GlobalTheory.SlabFinVol

open GlobalTheory.FlagMeas GlobalTheory.MeanDual

variable (E : Type) [Field E] [NumberField E] (j : ℕ)

theorem covol_le_of_mul_left (Γ Γ' : Set (MatInf E j)) (h : MatInf E j) (hh : 0 < detNorm E j h)
    (A B : Set (MatInf E j)) (hAB : ∀ x ∈ A, h * x ∈ B)
    (hΓ : ∀ δ ∈ Γ', ∃ δ₀ ∈ Γ, ∀ x, h * (δ₀ * x) = δ * (h * x)) :
    covol Γ (haarGL E j) A ≤ covol Γ' (haarGL E j) B := by
  unfold covol
  refine le_iInf fun D' => le_iInf fun hD' => le_iInf fun hc => ?_
  have hmeas : Measurable (fun g : MatInf E j => h * g) :=
    (GlobalTheory.MeanDual.measurePreserving_mul_left E j h hh).measurable
  refine iInf_le_of_le ((fun g => h * g) ⁻¹' D') (iInf_le_of_le (hmeas hD') (iInf_le_of_le ?_ ?_))
  · intro x hx
    obtain ⟨δ, hδ, hx'⟩ := hc (h * x) (hAB x hx)
    obtain ⟨δ₀, hδ₀, H⟩ := hΓ δ hδ
    refine ⟨δ₀, hδ₀, ?_⟩
    show h * (δ₀ * x) ∈ D'
    rw [H]; exact hx'
  · rw [← Measure.map_apply hmeas hD', GlobalTheory.OrbitTerm.map_haarGL_mul_left_eq E j h hh]

def scal (r : ℝ) : MatInf E j := fun _ a b => if a = b then (r : ℂ) else 0

theorem of_scal (r : ℝ) (w : InfinitePlace E) :
    Matrix.of (scal E j r w) = (r : ℂ) • (1 : Matrix (Fin j) (Fin j) ℂ) := by
  ext a b
  simp [scal, Matrix.one_apply]

theorem scal_mul_comm (r : ℝ) (δ x : MatInf E j) : scal E j r * (δ * x) = δ * (scal E j r * x) := by
  apply matInf_ext
  intro w
  simp only [of_mul, of_scal, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul]

theorem detNorm_scal (r : ℝ) (hr : 0 < r) :
    detNorm E j (scal E j r) = (r ^ (2 * j)) ^ Fintype.card (InfinitePlace E) := by
  unfold detNorm
  simp only [of_scal, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]
  rw [Finset.prod_const, Finset.card_univ]
  congr 1
  rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr, ← pow_mul, mul_comm]

theorem exists_scal (hj : 1 ≤ j) (c : ℝ) (hc : 0 < c) : ∃ r : ℝ, 0 < r ∧ detNorm E j (scal E j r) = c := by
  have hN : Fintype.card (InfinitePlace E) ≠ 0 := Fintype.card_ne_zero
  refine ⟨c ^ (((2 * j * Fintype.card (InfinitePlace E) : ℕ) : ℝ))⁻¹, Real.rpow_pos_of_pos hc _, ?_⟩
  rw [detNorm_scal E j _ (Real.rpow_pos_of_pos hc _), ← pow_mul]
  exact Real.rpow_inv_natCast_pow hc.le (by positivity)

def slab (c : ℝ) : Set (MatInf E j) := {x | c ≤ detNorm E j x ∧ detNorm E j x < c * Real.exp 1}

theorem covol_slab_le (hj : 1 ≤ j) (Λ : Submodule (𝓞 E) (Fin j → E)) (c : ℝ) (hc : 0 < c) :
    covol (autGL E j Λ) (haarGL E j) (slab E j c) ≤
      covol (autGL E j Λ) (haarGL E j) {x | 1 ≤ detNorm E j x ∧ detNorm E j x < Real.exp 1} := by
  obtain ⟨r, hr, hd⟩ := exists_scal E j hj c⁻¹ (inv_pos.2 hc)
  refine covol_le_of_mul_left E j _ _ (scal E j r) (hd ▸ inv_pos.2 hc) _ _ ?_
    (fun δ hδ => ⟨δ, hδ, fun x => scal_mul_comm E j r δ x⟩)
  rintro x ⟨h1, h2⟩
  simp only [Set.mem_setOf_eq, detNorm_mul, hd]
  constructor
  · rw [inv_mul_eq_div, le_div_iff₀ hc, one_mul]; exact h1
  · rw [inv_mul_eq_div, div_lt_iff₀ hc, mul_comm]; exact h2

theorem covol_le_of_carries {γ : GL (Fin j) E} {Λ Λ' : Submodule (𝓞 E) (Fin j → E)} (h : Carries E j γ Λ Λ') :
    covol (autGL E j Λ) (haarGL E j) {x | 1 ≤ detNorm E j x ∧ detNorm E j x < Real.exp 1} ≤
      covol (autGL E j Λ') (haarGL E j) (slab E j (detNorm E j (embInf E j γ))) := by
  refine covol_le_of_mul_left E j _ _ (embInf E j γ) (detNorm_embInf E j γ) _ _ ?_ ?_
  · rintro x ⟨h1, h2⟩
    simp only [slab, Set.mem_setOf_eq, detNorm_mul]
    have hp := detNorm_embInf E j γ
    exact ⟨le_mul_of_one_le_right hp.le h1, mul_lt_mul_of_pos_left h2 hp⟩
  · intro x hx
    obtain ⟨δ, hδ, rfl⟩ := (mem_autGL E j).1 hx
    refine ⟨embInf E j (γ⁻¹ * δ * γ), (mem_autGL E j).2 ⟨_, (h.inv.mul hδ).mul h, rfl⟩, fun x => ?_⟩
    apply matInf_ext
    intro w
    simp only [of_mul, embInf_mul, ← Matrix.mul_assoc]
    have := embInf_inv_mul E j γ⁻¹ w
    rw [inv_inv] at this
    rw [this, Matrix.one_mul]

theorem glVol_lt_top (hE : IsTotallyComplex E) : ∀ j : ℕ, 1 ≤ j → glVol E j < ⊤ := by
  intro j hj
  induction j with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [GlobalTheory.NormOneVol.glVol_one E hE]; exact ENNReal.ofReal_lt_top
    · have h := ih hn
      have hs := GlobalTheory.FlagBase.SiegelStep.glVol_step E hE (n + 1) (by omega) (by simpa using h)
      rw [hs]
      simp only [Nat.add_sub_cancel] at h ⊢
      exact ENNReal.mul_lt_top h ENNReal.ofReal_lt_top

end GlobalTheory.SlabFinVol

open GlobalTheory.FlagMeas GlobalTheory.MeanDual in

theorem GlobalTheory.SlabFinVol.covol_unitSlab_lt_top : ∀ (E : Type) [Field E] [NumberField E], IsTotallyComplex E → ∀ j : ℕ, 1 ≤ j → ∀ Λ : Submodule (𝓞 E) (Fin j → E), Submodule.IsLattice E Λ → GlobalTheory.FlagMeas.covol (GlobalTheory.FlagMeas.autGL E j Λ) (GlobalTheory.FlagMeas.haarGL E j) {x | 1 ≤ GlobalTheory.FlagMeas.detNorm E j x ∧ GlobalTheory.FlagMeas.detNorm E j x < Real.exp 1} < ⊤ := by
  intro E _ _ hE j hj Λ hΛ
  have hfin := GlobalTheory.SlabFinVol.glVol_lt_top E hE j hj
  let R : {Λ : Submodule (𝓞 E) (Fin j → E) // Submodule.IsLattice E Λ} →
      {Λ : Submodule (𝓞 E) (Fin j → E) // Submodule.IsLattice E Λ} → Prop :=
    fun Λ Λ' => ∃ γ : GL (Fin j) E, ∀ y, (γ : Matrix (Fin j) (Fin j) E) *ᵥ y ∈ Λ'.1 ↔ y ∈ Λ.1
  have hle : _ ≤ glVol E j := ENNReal.le_tsum (Quot.mk R ⟨Λ, hΛ⟩)
  have hrel := Quot.eqvGen_exact (Quot.out_eq (Quot.mk R ⟨Λ, hΛ⟩))
  have key : ∀ a b : {Λ : Submodule (𝓞 E) (Fin j → E) // Submodule.IsLattice E Λ},
      Relation.EqvGen (fun Λ Λ' : {Λ : Submodule (𝓞 E) (Fin j → E) // Submodule.IsLattice E Λ} =>
        ∃ γ : GL (Fin j) E, ∀ y, (γ : Matrix (Fin j) (Fin j) E) *ᵥ y ∈ Λ'.1 ↔ y ∈ Λ.1) a b →
      ∃ γ : GL (Fin j) E, Carries E j γ a.1 b.1 := by
    intro a b hab
    induction hab with
    | rel x y h => exact h
    | refl x => exact ⟨1, fun y => by simp⟩
    | symm x y _ ih => obtain ⟨γ, h⟩ := ih; exact ⟨γ⁻¹, h.inv⟩
    | trans x y z _ _ ih1 ih2 =>
      obtain ⟨γ, h⟩ := ih1; obtain ⟨δ, h'⟩ := ih2; exact ⟨δ * γ, h'.mul h⟩
  obtain ⟨γ, hγ⟩ := key _ _ hrel
  exact lt_of_le_of_lt ((covol_le_of_carries E j hγ.inv).trans
    (GlobalTheory.SlabFinVol.covol_slab_le E j hj _ _ (detNorm_embInf E j _))) (lt_of_le_of_lt hle hfin)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CurvatureFormMatrixBoundedDomainModelMetricAtZer
section
set_option autoImplicit false

noncomputable section

open Matrix MvPolynomial Filter Topology ComplexConjugate
open GlobalTheory.HermFrame

namespace GlobalTheory.DomainDens

variable {ι : Type} [Fintype ι] {p q n : ℕ} (h : Fintype.card (ι × Fin p × Fin q) = n) (τ : ι)

def flatCoordinateMatrixBlock (u : ReciprocityTheory.L2DbarEstimates.V n) : Matrix (Fin p) (Fin q) ℂ :=
  Formalism.DegreeFormula.unflat (GlobalTheory.UnifDens.flatL h u) τ

theorem block_reshape_apply (u : ReciprocityTheory.L2DbarEstimates.V n) (i : Fin p) (b : Fin q) :
    flatCoordinateMatrixBlock h τ u i b = u (Fintype.equivFinOfCardEq h (τ, i, b)) := rfl

theorem flatCoordinateMatrixBlock_entry_eq_proj (i : Fin p) (b : Fin q) :
    (fun u => flatCoordinateMatrixBlock h τ u i b) = fun u => EuclideanSpace.proj (𝕜 := ℂ) (Fintype.equivFinOfCardEq h (τ, i, b)) u :=
  rfl

theorem flatCoordinateMatrixBlock_at_zero : flatCoordinateMatrixBlock h τ 0 = 0 := by
  ext i b; simp [block_reshape_apply]

theorem matrixHolomorphicPartialDeriv_flatCoordinateMatrixBlock (x ξ : ReciprocityTheory.L2DbarEstimates.V n) : mdel (flatCoordinateMatrixBlock h τ) x ξ = flatCoordinateMatrixBlock h τ ξ := by
  ext i b
  rw [mdel_apply, flatCoordinateMatrixBlock_entry_eq_proj, del_eq_fderiv (ContinuousLinearMap.differentiableAt _),
    ContinuousLinearMap.fderiv]
  rfl

theorem matrixAntiholomorphicPartialDeriv_flatCoordinateMatrixBlock (x η : ReciprocityTheory.L2DbarEstimates.V n) : mdbar (flatCoordinateMatrixBlock h τ) x η = 0 := by
  ext i b
  rw [mdbar_apply, flatCoordinateMatrixBlock_entry_eq_proj, dbar_eq_zero (ContinuousLinearMap.differentiableAt _)]
  rfl

theorem matrixEntriesContDiffAt_flatCoordinateMatrixBlock {k : WithTop ℕ∞} (x : ReciprocityTheory.L2DbarEstimates.V n) : MContDiffAt k (flatCoordinateMatrixBlock h τ) x :=
  fun i b => by
    rw [flatCoordinateMatrixBlock_entry_eq_proj]
    exact (ContinuousLinearMap.contDiff (𝕜 := ℂ) (n := k)
      (EuclideanSpace.proj (𝕜 := ℂ) (ι := Fin n) (Fintype.equivFinOfCardEq h (τ, i, b)) : ReciprocityTheory.L2DbarEstimates.V n →L[ℂ] ℂ)).restrict_scalars ℝ |>.contDiffAt

theorem mContDiffAt_hP {k : WithTop ℕ∞} (x : ReciprocityTheory.L2DbarEstimates.V n) :
    MContDiffAt k (fun u => Formalism.DegreeFormula.hP (flatCoordinateMatrixBlock h τ u)) x := by
  unfold Formalism.DegreeFormula.hP
  exact (mContDiffAt_const 1).sub ((matrixEntriesContDiffAt_flatCoordinateMatrixBlock h τ x).mul (matrixEntriesContDiffAt_flatCoordinateMatrixBlock h τ x).conjTranspose)

theorem mdel_hP (x ξ : ReciprocityTheory.L2DbarEstimates.V n) :
    mdel (fun u => Formalism.DegreeFormula.hP (flatCoordinateMatrixBlock h τ u)) x ξ = -(flatCoordinateMatrixBlock h τ ξ * (flatCoordinateMatrixBlock h τ x)ᴴ) := by
  have hz : MContDiffAt 1 (flatCoordinateMatrixBlock h τ) x := matrixEntriesContDiffAt_flatCoordinateMatrixBlock h τ x
  have e : (fun u => Formalism.DegreeFormula.hP (flatCoordinateMatrixBlock h τ u)) =
      fun u => (fun _ => (1 : Matrix (Fin p) (Fin p) ℂ)) u + -(flatCoordinateMatrixBlock h τ u * (flatCoordinateMatrixBlock h τ u)ᴴ) := by
    funext u; simp [Formalism.DegreeFormula.hP, sub_eq_add_neg]
  rw [e, mdel_add (mContDiffAt_const _) (hz.mul hz.conjTranspose).neg, mdel_const, mdel_neg,
    mdel_mul hz hz.conjTranspose, mdel_conjTranspose, matrixAntiholomorphicPartialDeriv_flatCoordinateMatrixBlock, matrixHolomorphicPartialDeriv_flatCoordinateMatrixBlock]
  simp

theorem hP_zero : Formalism.DegreeFormula.hP (flatCoordinateMatrixBlock h τ 0) = 1 := by simp [Formalism.DegreeFormula.hP, flatCoordinateMatrixBlock_at_zero]

theorem conn_model (x ξ : ReciprocityTheory.L2DbarEstimates.V n) (hu : IsUnit (Formalism.DegreeFormula.hP (flatCoordinateMatrixBlock h τ x)).det) :
    conn (fun u => ((Formalism.DegreeFormula.hP (flatCoordinateMatrixBlock h τ u))⁻¹)ᵀ) x ξ =
      flatCoordinateMatrixBlock h τ ξ * (flatCoordinateMatrixBlock h τ x)ᴴ * (Formalism.DegreeFormula.hP (flatCoordinateMatrixBlock h τ x))⁻¹ := by
  rw [conn, transpose_transpose, mdel_transpose (fun u => (Formalism.DegreeFormula.hP (flatCoordinateMatrixBlock h τ u))⁻¹), transpose_transpose,
    mdel_inv (mContDiffAt_hP h τ x) hu, nonsing_inv_nonsing_inv _ hu, mdel_hP]
  simp only [Matrix.mul_neg, Matrix.neg_mul, neg_neg, ← Matrix.mul_assoc, mul_nonsing_inv _ hu, Matrix.one_mul]

theorem curv_model (ξ η : ReciprocityTheory.L2DbarEstimates.V n) :
    curv (fun u => ((Formalism.DegreeFormula.hP (flatCoordinateMatrixBlock h τ u))⁻¹)ᵀ) 0 ξ η = -(flatCoordinateMatrixBlock h τ ξ * (flatCoordinateMatrixBlock h τ η)ᴴ) := by
  have hu0 : IsUnit (Formalism.DegreeFormula.hP (flatCoordinateMatrixBlock h τ 0)).det := by simp [hP_zero]
  have hev := (mContDiffAt_hP (k := 1) h τ 0).eventually_isUnit hu0
  have hz : MContDiffAt 1 (flatCoordinateMatrixBlock h τ) 0 := matrixEntriesContDiffAt_flatCoordinateMatrixBlock h τ 0
  rw [curv, mdbar_congr (hev.mono fun x hx => conn_model h τ x ξ hx),
    mdbar_mul ((mContDiffAt_const _).mul hz.conjTranspose) ((mContDiffAt_hP h τ 0).inv hu0),
    mdbar_mul (mContDiffAt_const _) hz.conjTranspose, mdbar_conjTranspose, matrixHolomorphicPartialDeriv_flatCoordinateMatrixBlock, mdbar_const, hP_zero,
    flatCoordinateMatrixBlock_at_zero]
  simp

theorem curvPoly_model_zero : ∀ (ι : Type) [Fintype ι] (p q n : ℕ) (h : Fintype.card (ι × Fin p × Fin q) = n) (τ : ι),
    GlobalTheory.GoodMetric.curvPoly
      (fun u => Matrix.transpose (Formalism.DegreeFormula.hP (Formalism.DegreeFormula.unflat (GlobalTheory.UnifDens.flatL h u) τ))⁻¹) 0 =
      -GlobalTheory.DomainDens.blockSym h τ := by
  intro ι _ p q n h τ
  have e2 : ∀ (a c : Fin n) (i j : Fin p),
      curv (fun u => Matrix.transpose (Formalism.DegreeFormula.hP (Formalism.DegreeFormula.unflat (GlobalTheory.UnifDens.flatL h u) τ))⁻¹)
        0 (GlobalTheory.GoodMetric.coordVec a) (GlobalTheory.GoodMetric.coordVec c) i j =
      -∑ b : Fin q, (if Fintype.equivFinOfCardEq h (τ, i, b) = a then 1 else 0) *
        (if Fintype.equivFinOfCardEq h (τ, j, b) = c then 1 else 0) := by
    intro a c i j
    change curv (fun u => ((Formalism.DegreeFormula.hP (flatCoordinateMatrixBlock h τ u))⁻¹)ᵀ) 0 _ _ i j = _
    rw [curv_model h τ, Matrix.neg_apply, mul_apply]
    simp [block_reshape_apply, EuclideanSpace.single_apply]
  refine Matrix.ext fun i j => ?_
  simp only [GlobalTheory.GoodMetric.curvPoly, of_apply, e2, Matrix.neg_apply, blockSym_apply]
  simp only [map_neg, neg_mul, Finset.sum_neg_distrib, neg_inj, map_sum, Finset.sum_mul, mul_ite, ite_mul, one_mul,
    zero_mul, mul_zero, apply_ite (C : ℂ → MvPolynomial (Fin n × Fin n) ℂ), map_one, map_zero]
  rw [Finset.sum_congr rfl fun _ _ => Finset.sum_comm, Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp [Finset.sum_ite_eq]

end GlobalTheory.DomainDens
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteUnitaryClassSetFiniteStatement
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.definiteUnitary_classSet_finite : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (K : Subgroup (finU E n)), IsOpen (K : Set (finU E n)) → ∃ S : Finset (UA E n), ∀ g : UA E n, ∃ γ ∈ ratU E n, ∃ s ∈ S, ∃ x ∈ infU E n, ∃ k ∈ K, g = γ * s * x * (k : UA E n) := by
  first | exact @GlobalTheory.DefU.ClassFin.classSet_finite | exact GlobalTheory.DefU.ClassFin.classSet_finite | (intros; apply GlobalTheory.DefU.ClassFin.classSet_finite <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteUnitaryInfinitePointEqListProdPlaceParts
section
noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU

namespace GlobalTheory.DefU.InfDecomp

theorem list_prod_map_mulSingle {ι M : Type} [DecidableEq ι] [Monoid M] (w : ι) (a : M) :
    ∀ l : List ι, l.Nodup → (l.map (Pi.mulSingle w a : ι → M)).prod = if w ∈ l then a else 1
  | [], _ => by simp
  | i :: l, h => by
    rw [List.nodup_cons] at h
    rw [List.map_cons, List.prod_cons, list_prod_map_mulSingle w a l h.2]
    by_cases hi : i = w
    · subst hi
      simp [h.1]
    · simp [Pi.mulSingle_apply, hi, Ne.symm hi]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def cutPt (v : InfinitePlace E) (x : UA E n) : UA E n := ((embRet (n := n) v.embedding x : embU n v.embedding) : UA E n)

theorem cutPt_mem (v : InfinitePlace E) (x : UA E n) : cutPt v x ∈ embU n v.embedding := (embRet v.embedding x).2

theorem cInf_cutPt (v : InfinitePlace E) (x : UA E n) : cInf (cutPt v x) = cutGL v (cInf x) := by
  unfold cutPt
  rw [cInf_embRet, InfinitePlace.mk_embedding]

open Classical in

theorem evGL_cInf_cutPt (x : UA E n) (v w : InfinitePlace E) :
    evGL w (cInf (cutPt v x)) = (Pi.mulSingle w (evGL w (cInf x)) : InfinitePlace E → GL (Fin n) ℂ) v := by
  rw [cInf_cutPt, Pi.mulSingle_apply]
  split_ifs with h
  · subst h
    exact evGL_cutGL_self _ _
  · exact evGL_cutGL_of_ne (Ne.symm h) _

end GlobalTheory.DefU.InfDecomp

namespace GlobalTheory.DefU

open InfDecomp in

theorem infU_eq_list_prod_embU : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (x : UA E n),
    x ∈ infU E n → ∃ y : InfinitePlace E → UA E n, (∀ v, y v ∈ embU n v.embedding) ∧
      (∀ v, cEmb v.embedding (y v) = cEmb v.embedding x) ∧ (Finset.univ.toList.map y).prod = x := by
  intro E _ _ _ n x hx
  classical
  refine ⟨fun v => cutPt v x, fun v => cutPt_mem v x, fun v => ?_, ?_⟩
  · change GeneralLinearGroup.map (coord v.embedding) (cInf (cutPt v x)) =
      GeneralLinearGroup.map (coord v.embedding) (cInf x)
    rw [cInf_cutPt, coord_embedding]
    exact evGL_cutGL_self v (cInf x)
  · refine Subtype.ext (ga_ext ?_ ?_)
    · change cInf (Finset.univ.toList.map fun v => cutPt v x).prod = cInf x
      rw [map_list_prod, List.map_map]
      refine gl_ext_evGL fun w => ?_
      rw [map_list_prod, List.map_map]
      have e : (evGL w ∘ cInf ∘ fun v : InfinitePlace E => cutPt v x) =
          (Pi.mulSingle w (evGL w (cInf x)) : InfinitePlace E → GL (Fin n) ℂ) := funext fun v => evGL_cInf_cutPt x v w
      rw [e, list_prod_map_mulSingle w _ _ (Finset.nodup_toList _),
        if_pos (Finset.mem_toList.2 (Finset.mem_univ w))]
    · let ψ : UA E n →* GL (Fin n) (Af E) := (GeneralLinearGroup.map (pFin E)).comp (UA E n).subtype
      change ψ (Finset.univ.toList.map fun v => cutPt v x).prod = ψ x
      rw [MonoidHom.mem_ker.1 hx, map_list_prod, List.map_map]
      refine List.prod_eq_one fun g hg => ?_
      obtain ⟨v, -, rfl⟩ := List.mem_map.1 hg
      exact MonoidHom.mem_ker.1 (cutPt_mem v x).1

end GlobalTheory.DefU

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DrowsPos
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

namespace GlobalTheory.Mem.R3

theorem drows_pos : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → Lam3 Z → 0 < D.what₂.Drows := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z _ hH _
  have e1 : Module.finrank D.what₂.LL D.div.RR.V = Fintype.card D.div.RR.ι :=
    Module.finrank_eq_card_basis D.div.RR.b
  have e2 : Module.finrank ℂ D.what₂.EE = Fintype.card D.div.RR.ι :=
    Module.finrank_eq_card_basis (Module.Basis.mk D.jEE_basis.1 (le_of_eq D.jEE_basis.2.symm))
  have e3 : Module.finrank ℂ D.what₂.EE = D.what₂.Drows := by
    simpa using Module.finrank_eq_card_basis D.what₂.onb.toBasis
  have h2 : Module.finrank D.what₂.LL D.div.RR.V = ((R.toCx3 F).data F.cr true).D := by
    rw [← Z.eRR.finrank_eq, Module.finrank_fin_fun]
  have h3 : 0 < ((R.toCx3 F).data F.cr true).D := hH.prim.pos true
  omega

end GlobalTheory.Mem.R3
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DtTiedTrue
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.Mem.Col2.TC.dtTied_true : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∃ T : Formalism.L2.Host.DtTied (I.rec7 l Z) (I.cf l Z), ∀ a, T.eDt a = (QuotientGroup.mk a : DtQ B.host I.SQ) := by
  intro B X I _ _ l Z
  refine ⟨GlobalTheory.Mem.Col2.dtIsoRational (I.rec7 l Z) (I.cf l Z) I.SQ (MulEquiv.refl _) (fun j => rfl) rfl ?_ (fun z => rfl), fun _ => rfl⟩
  show UOQ B.host I.SQ = _
  ext x
  constructor
  · intro h
    exact ⟨x, h, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact hy
end

