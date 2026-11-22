import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0322
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0344
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0360
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0363
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0038
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0007
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LintegralFintypeProdEqProd
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.GenericProdIff
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0361
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0352
import GroundTheory.AutomorphicForms.AnisotropicHeight
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.AffineGLForms.BlockMatrixIdentity.BlockMatOne
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.AdlEqZeroOfMemNbhd
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MetaplecticLowRank.LowC
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobData
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0334
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0357
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0331

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsWeightNilradicalIntegralOne
section
open Matrix MeasureTheory PositivityTheory.Rg.BcB PositivityTheory.Rg.Tf.Loc GlobalTheory.CompanionTheory.LocVan
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.LocVan

theorem exists_isCompact_uOf_subset {n : ℕ} (W₁ W₂ : Submodule ℂ (Fin n → ℂ))
    (g : GL (Fin n) ℂ) {K : Set (GL (Fin n) ℂ)} (hK : IsCompact K) :
    ∃ C : Set (nilrad W₁ W₂), IsCompact C ∧ {Y : nilrad W₁ W₂ | (uOf Y)⁻¹ * g ∈ K} ⊆ C := by
  have hf : Continuous fun c : GL (Fin n) ℂ =>
      ((g * c⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) - 1 :=
    (Units.continuous_val.comp (continuous_const.mul continuous_inv)).sub continuous_const
  have hK' := hK.image hf
  have hemb : Topology.IsClosedEmbedding
      (Subtype.val : nilrad W₁ W₂ → Matrix (Fin n) (Fin n) ℂ) :=
    (isClosed_nilrad W₁ W₂).isClosedEmbedding_subtypeVal
  refine ⟨_, hemb.isCompact_preimage hK', fun Y hY => ?_⟩
  refine ⟨(uOf Y)⁻¹ * g, hY, ?_⟩
  have : g * ((uOf Y)⁻¹ * g)⁻¹ = uOf Y := by group
  simp only [this, uOf_val, add_sub_cancel_left]

theorem isOpen_nSet {n : ℕ} (W₁ W₂ : Submodule ℂ (Fin n → ℂ)) {C : Set (GL (Fin n) ℂ)}
    (hC : IsOpen C) : IsOpen (nSet W₁ W₂ C) := by
  have : nSet W₁ W₂ C = ⋃ X : nilrad W₁ W₂, (fun g => (uOf X)⁻¹ * g) ⁻¹' C := by
    ext g
    simp only [nSet, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_preimage]
    constructor
    · rintro ⟨X, c, hc, rfl⟩
      exact ⟨X, by simpa using hc⟩
    · rintro ⟨X, hX⟩
      exact ⟨X, _, hX, by simp⟩
  rw [this]
  exact isOpen_iUnion fun X => hC.preimage (continuous_const.mul continuous_id)

theorem inv_mul_mem_nSet_iff {n : ℕ} {W₁ W₂ : Submodule ℂ (Fin n → ℂ)} (hW : W₁ ≤ W₂)
    (C : Set (GL (Fin n) ℂ)) (h : nilrad W₁ W₂) (x : GL (Fin n) ℂ) :
    (uOf h)⁻¹ * x ∈ nSet W₁ W₂ C ↔ x ∈ nSet W₁ W₂ C := by
  constructor
  · rintro ⟨X, c, hc, e⟩
    refine ⟨nmul hW h X, c, hc, ?_⟩
    rw [uOf_nmul, mul_assoc, e]
    simp
  · rintro ⟨X, c, hc, rfl⟩
    refine ⟨nmul hW (ninv hW h) X, c, hc, ?_⟩
    rw [uOf_nmul, uOf_ninv, mul_assoc]

theorem exists_nilrad_normaliser : ∀ (n : ℕ) [MeasurableSpace (GL (Fin n) ℂ)] [BorelSpace (GL (Fin n) ℂ)]
  (W₁ W₂ : Submodule ℂ (Fin n → ℂ)) (hW : W₁ ≤ W₂) [MeasurableSpace (nilrad W₁ W₂)]
  [BorelSpace (nilrad W₁ W₂)] (ν : Measure (nilrad W₁ W₂)) [ν.IsAddHaarMeasure],
  (∀ Y : nilrad W₁ W₂, MeasurePreserving (nmul hW Y) ν ν) →
  ∃ w : GL (Fin n) ℂ → ℝ≥0∞, Measurable w ∧
    ∀ g : GL (Fin n) ℂ, ∫⁻ X, w ((uOf X)⁻¹ * g) ∂ν = 1 := by
  intro n _ _ W₁ W₂ hW _ _ ν _ hmp
  haveI := locallyCompact_nilrad W₁ W₂
  haveI := secondCountable_nilrad W₁ W₂
  haveI := secondCountable_GL n
  haveI := locallyCompact_GL n
  obtain ⟨U, hUo, hUc, hUcov⟩ := exists_open_cover n
  have hmeas : Measurable (fun p : nilrad W₁ W₂ × GL (Fin n) ℂ => (uOf p.1)⁻¹ * p.2) :=
    (((continuous_uOf.comp continuous_fst).inv).mul continuous_snd).measurable
  obtain ⟨ρ, hρm, hρ, -⟩ := GlobalTheory.T.integral_fiber_decomposition_invariant ν (fun Y g => (uOf Y)⁻¹ * g) hmeas (nmul hW) hmp
    (fun h₀ h x => by simp only [uOf_nmul, _root_.mul_inv_rev, mul_assoc])
    (fun i => closure (U i)) (fun i => nSet W₁ W₂ (U i))
    (fun i => isClosed_closure.measurableSet)
    (fun i => (isOpen_nSet W₁ W₂ (hUo i)).measurableSet)
    (fun i h x => inv_mul_mem_nSet_iff hW (U i) h x)
    (fun x => by
      obtain ⟨i, hi⟩ := hUcov x
      exact ⟨i, 0, x, hi, by
        have : uOf (0 : nilrad W₁ W₂) = 1 := Units.ext (by simp)
        simp [this]⟩)
    (fun i x => by
      obtain ⟨C, hC, hsub⟩ := exists_isCompact_uOf_subset W₁ W₂ x (hUc i)
      exact ((measure_mono hsub).trans_lt hC.measure_lt_top).ne)
    (fun i x hx => by
      obtain ⟨Y₀, c, hc, rfl⟩ := hx
      have ho : IsOpen {Y : nilrad W₁ W₂ | (uOf Y)⁻¹ * (uOf Y₀ * c) ∈ U i} :=
        (hUo i).preimage ((continuous_uOf.inv).mul continuous_const)
      have hne : ({Y : nilrad W₁ W₂ | (uOf Y)⁻¹ * (uOf Y₀ * c) ∈ U i}).Nonempty :=
        ⟨Y₀, by simpa using hc⟩
      have hpos := ho.measure_pos ν hne
      have hsub : {Y : nilrad W₁ W₂ | (uOf Y)⁻¹ * (uOf Y₀ * c) ∈ U i} ⊆
          {Y : nilrad W₁ W₂ | (uOf Y)⁻¹ * (uOf Y₀ * c) ∈ closure (U i)} :=
        fun Y hY => subset_closure hY
      exact (hpos.trans_le (measure_mono hsub)).ne')
    ∅ (by simp) (by simp) (by simp)
  exact ⟨ρ, hρm, hρ⟩

end GlobalTheory.CompanionTheory.LocVan
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteDimCoefficientsFiniteDetermining
section
open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl GlobalTheory.CompanionTheory.CTFin

noncomputable section

namespace GlobalTheory.CompanionTheory.CTFin.UniSol

theorem exists_finset_separating {K : Type} (A : Submodule ℂ (K → ℂ)) [FiniteDimensional ℂ A] :
    ∃ S : Finset K, ∀ c ∈ A, (∀ κ ∈ S, c κ = 0) → c = 0 := by
  classical
  have key : ∀ (n : ℕ) (B : Submodule ℂ A), Module.finrank ℂ B = n →
      ∃ S : Finset K, ∀ c ∈ B, (∀ κ ∈ S, (c : K → ℂ) κ = 0) → c = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro B hB
      by_cases hbot : B = ⊥
      · refine ⟨∅, fun c hc _ => ?_⟩
        rw [hbot] at hc
        exact (Submodule.mem_bot ℂ).mp hc
      · obtain ⟨c0, hc0B, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
        obtain ⟨κ0, hκ0⟩ : ∃ κ0, (c0 : K → ℂ) κ0 ≠ 0 := by
          by_contra hcon
          push Not at hcon
          exact hc0 (Subtype.ext (funext hcon))
        let ev : A →ₗ[ℂ] ℂ := (LinearMap.proj κ0).comp A.subtype
        let B' : Submodule ℂ A := B ⊓ LinearMap.ker ev
        have hlt : B' < B := by
          refine lt_of_le_of_ne inf_le_left (fun h => hκ0 ?_)
          have hmem : c0 ∈ B' := by
            rw [h]
            exact hc0B
          exact LinearMap.mem_ker.mp (Submodule.mem_inf.mp hmem).2
        have hrk : Module.finrank ℂ B' < n := by
          have := Submodule.finrank_lt_finrank_of_lt hlt
          omega
        obtain ⟨S', hS'⟩ := ih _ hrk B' rfl
        refine ⟨insert κ0 S', fun c hc hvan => hS' c ?_ (fun κ hκ => hvan κ (Finset.mem_insert_of_mem hκ))⟩
        refine Submodule.mem_inf.mpr ⟨hc, LinearMap.mem_ker.mpr ?_⟩
        exact hvan κ0 (Finset.mem_insert_self κ0 S')
  obtain ⟨S, hS⟩ := key _ ⊤ rfl
  refine ⟨S, fun c hc hvan => ?_⟩
  have h0 := hS ⟨c, hc⟩ Submodule.mem_top hvan
  exact congrArg Subtype.val h0

theorem finiteDimensional_coeffSpan {K W : Type} [Group K] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ K W) : FiniteDimensional ℂ (GlobalTheory.Published.AutFin.coeffSpan ρ) := by
  classical
  let b := Module.Free.chooseBasis ℂ W
  let m : (Module.Free.ChooseBasisIndex ℂ W) × (Module.Free.ChooseBasisIndex ℂ W) → (K → ℂ) :=
    fun ij k => b.repr (ρ k (b ij.2)) ij.1
  haveI : FiniteDimensional ℂ (Submodule.span ℂ (Set.range m)) :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_range m)
  have hle : GlobalTheory.Published.AutFin.coeffSpan ρ ≤ Submodule.span ℂ (Set.range m) := by
    unfold GlobalTheory.Published.AutFin.coeffSpan
    refine Submodule.span_le.mpr ?_
    rintro f ⟨ℓ, w, rfl⟩
    have hw : ∀ v : W, ℓ v = ∑ i, b.repr v i * ℓ (b i) := by
      intro v
      conv_lhs => rw [← b.sum_repr v]
      simp only [map_sum, map_smul, smul_eq_mul]
    have hf : (fun k => ℓ ((ρ k) w)) = ∑ ij, (b.repr w ij.2 * ℓ (b ij.1)) • m ij := by
      funext k
      rw [Finset.sum_apply]
      simp only [Pi.smul_apply, smul_eq_mul, m]
      rw [Fintype.sum_prod_type]
      dsimp only
      have h1 : ℓ (ρ k w) = ∑ j, b.repr w j * ℓ (ρ k (b j)) := by
        conv_lhs => rw [← b.sum_repr w]
        simp only [map_sum, map_smul, smul_eq_mul]
      rw [h1, Finset.sum_comm]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [hw (ρ k (b j)), Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      ring
    rw [hf]
    exact Submodule.sum_mem _ (fun ij _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨ij, rfl⟩))
  exact Submodule.finiteDimensional_of_le hle

theorem coeffSpan_unisolvent : ∀ (K W : Type) [Group K] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ K W), ∃ S : Finset K, ∀ c ∈ GlobalTheory.Published.AutFin.coeffSpan ρ, (∀ κ ∈ S, c κ = 0) → c = 0 := by
  intro K W _ _ _ _ ρ
  haveI := finiteDimensional_coeffSpan ρ
  exact exists_finset_separating _

end GlobalTheory.CompanionTheory.CTFin.UniSol

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaussianWeightTotalMass
section
open MeasureTheory ReciprocityTheory.L2DbarEstimates GlobalTheory.CompanionTheory.FSCrofton
open scoped ENNReal ComplexConjugate

noncomputable section

namespace GlobalTheory.CompanionTheory.FSCrofton

theorem integral_exp_neg_norm_sq : ∫ z : ℂ, Real.exp (-‖z‖ ^ 2) = Real.pi := by
  have h := GaussianFourier.integral_rexp_neg_mul_sq_norm (V := ℂ) (b := 1) one_pos
  have hd : (Module.finrank ℝ ℂ : ℝ) / 2 = 1 := by simp [Complex.finrank_real_complex]
  simp only [one_mul, div_one, hd, Real.rpow_one, neg_mul] at h
  exact h

theorem lintegral_exp_neg_norm_sq :
    ∫⁻ z : ℂ, ENNReal.ofReal (Real.exp (-‖z‖ ^ 2)) = ENNReal.ofReal Real.pi := by
  have hi : Integrable (fun z : ℂ => Real.exp (-‖z‖ ^ 2)) := by
    by_contra hn
    have h0 := integral_undef hn
    rw [integral_exp_neg_norm_sq] at h0
    exact Real.pi_ne_zero h0
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall fun z => (Real.exp_pos _).le), integral_exp_neg_norm_sq]

theorem lintegral_gW (d : ℕ) (α : Type) [Fintype α] :
    ∫⁻ C : Fin d → α → ℂ, gW d α C = ENNReal.ofReal (Real.pi ^ (d * Fintype.card α)) := by
  have hw : ∀ C : Fin d → α → ℂ, gW d α C =
      ∏ k, ∏ j, ENNReal.ofReal (Real.exp (-‖C k j‖ ^ 2)) := by
    intro C
    unfold gW
    simp only [← Finset.sum_neg_distrib, Real.exp_sum]
    rw [ENNReal.ofReal_prod_of_nonneg fun _ _ => Finset.prod_nonneg fun _ _ => (Real.exp_pos _).le]
    exact Finset.prod_congr rfl fun k _ =>
      ENNReal.ofReal_prod_of_nonneg fun _ _ => (Real.exp_pos _).le
  have hm : Measurable fun z : ℂ => ENNReal.ofReal (Real.exp (-‖z‖ ^ 2)) := by fun_prop
  have hrow : ∫⁻ r : α → ℂ, ∏ j, ENNReal.ofReal (Real.exp (-‖r j‖ ^ 2)) =
      ENNReal.ofReal Real.pi ^ Fintype.card α := by
    rw [volume_pi, GlobalTheory.RestrMeas.lintegral_fintype_prod_eq_prod (fun _ => hm.aemeasurable)]
    simp [lintegral_exp_neg_norm_sq]
  have hmr : Measurable fun r : α → ℂ => ∏ j, ENNReal.ofReal (Real.exp (-‖r j‖ ^ 2)) :=
    Finset.measurable_prod _ fun j _ => hm.comp (measurable_pi_apply j)
  simp only [hw]
  rw [volume_pi, GlobalTheory.RestrMeas.lintegral_fintype_prod_eq_prod (fun _ => hmr.aemeasurable)]
  simp only [hrow, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← pow_mul, mul_comm, ENNReal.ofReal_pow Real.pi_pos.le, mul_comm]

end GlobalTheory.CompanionTheory.FSCrofton
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GenericProdIrrOfGenericProdIff
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir.Leib
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZMir

theorem genericProdIrr_of_genericProdIff :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
      GenericProdIff k → GenericProdIrr k := by
  intro k _ _ _ _ H h N x hd
  exact H h N (fun a => (x a).1) hd (fun a => (x a).2.rep.V) (fun a => (x a).rep) (fun a => (x a).2.rep.smooth)

end GlobalTheory.CompanionTheory.BZMir
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdempotentLatticeDecompositionStatement
section
open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4 GlobalTheory.CompanionTheory.TorusCh
open scoped Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idempotent_lattice_decomposition : ∀ (R : Type) [Ring R], (∀ x y : R, x * y = y * x) → ∀ (σ : R →+* R), (∀ x, σ (σ x) = x) → ∀ (m : ℕ) (P : (Fin m → SignType) → R), (∀ e, P e * P e = P e) → (∀ e, P e * σ (P e) = 0) → (∀ p, p * p = p → p * σ p = 0 → ∃ e, P e = p) → Function.Injective P → P 0 = 0 → (∀ e e', P (sMeet e e') = P e * P e') → (∀ e e', SLe e e' → P e * P e' = P e) → (∀ e, P e = ∑ j, P (Pi.single j (e j))) ∧ ∀ j, P (Pi.single j (-1)) = σ (P (Pi.single j 1)) := by
  first | exact @GlobalTheory.CompanionTheory.TorusCh.isotropicIdempotent_signs | exact GlobalTheory.CompanionTheory.TorusCh.isotropicIdempotent_signs | (intros; apply GlobalTheory.CompanionTheory.TorusCh.isotropicIdempotent_signs <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableOnFundamentalDomain
section
noncomputable section

open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl PositivityTheory.Affgl.CT Topology Matrix
open scoped Pointwise

namespace GlobalTheory.CompanionTheory.ConstTerm

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a r : ℕ}

omit [IsTotallyComplex E] in

theorem continuous_map_pFin :
    Continuous (GeneralLinearGroup.map (n := Fin a) (pFin E)) :=
  Continuous.units_map _ (continuous_id.matrix_map (continuous_snd :
    Continuous fun x : InfiniteAdeleRing E × IsDedekindDomain.FiniteAdeleRing (𝓞 E) E => x.2))

theorem continuous_pInf : Continuous (pInf E) :=
  (continuous_pi fun w =>
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex
      (IsTotallyComplex.isComplex w)).continuous.comp (continuous_apply w)).comp
    (continuous_fst : Continuous fun x : InfiniteAdeleRing E × IsDedekindDomain.FiniteAdeleRing (𝓞 E) E => x.1)

theorem continuous_map_pInf :
    Continuous (GeneralLinearGroup.map (n := Fin a) (pInf E)) :=
  Continuous.units_map _ (continuous_id.matrix_map continuous_pInf)

theorem continuous_of_isOpen_stab (φ : Sm E a) (hU : IsOpen {k | finRep E a k φ = φ}) : Continuous φ.1 := by
  rw [continuous_iff_continuousAt]
  intro g
  have hF : ContinuousAt (fun h : GA E a => chart φ.1 g (toL (GeneralLinearGroup.map (pInf E) h).val)) 1 := by
    have h1 : ContinuousAt (chart φ.1 g) (toL ((GeneralLinearGroup.map (pInf E) (1 : GA E a)).val)) := by
      rw [map_one]
      exact (contDiffAt_chart φ.2 g isUnit_one).continuousAt
    have h0 : Continuous (fun h : GA E a =>
        ((GeneralLinearGroup.map (n := Fin a) (pInf E) h : GL (Fin a) (Cinf E)) : Matrix (Fin a) (Fin a) (Cinf E))) :=
      Units.continuous_val.comp continuous_map_pInf
    have h2 : Continuous (fun h : GA E a => toL (GeneralLinearGroup.map (pInf E) h).val) := h0
    exact ContinuousAt.comp (f := fun h : GA E a => toL (GeneralLinearGroup.map (pInf E) h).val) h1 h2.continuousAt
  have hev : ∀ᶠ h in 𝓝 (1 : GA E a), GeneralLinearGroup.map (pFin E) h ∈ {k | finRep E a k φ = φ} := by
    refine (continuous_map_pFin.continuousAt (x := (1 : GA E a))).eventually (hU.mem_nhds ?_)
    rw [map_one]
    change finRep E a 1 φ = φ
    simp
  have hG : ContinuousAt (fun h : GA E a => φ.1 (g * h)) 1 := by
    refine hF.congr ?_
    filter_upwards [hev] with h hh
    have e := congrArg (fun ψ : Sm E a => ψ.1 (g * infGL E a (GeneralLinearGroup.map (pInf E) h))) hh
    change φ.1 (g * infGL E a _ * finGL E a _) = φ.1 _ at e
    rw [mul_assoc, infGL_mul_finGL] at e
    rw [e, chart_val]
  have h2 : ContinuousAt (fun x : GA E a => g⁻¹ * x) g := (continuous_const.mul continuous_id).continuousAt
  have h3 : ContinuousAt (fun h : GA E a => φ.1 (g * h)) (g⁻¹ * g) := by rwa [inv_mul_cancel]
  simpa [Function.comp_def] using h3.comp h2

omit [IsTotallyComplex E] in

theorem continuous_unip : Continuous (unip : (BlockIx a r → Ad E) → GA E a) := by
  have hn : Continuous (fun x : BlockIx a r → Ad E => (nilM x : Matrix (Fin a) (Fin a) (Ad E))) :=
    continuous_matrix fun i j => by
      simp only [nilM, Matrix.of_apply]
      split_ifs with h
      · exact continuous_apply _
      · exact continuous_const
  exact Units.continuous_iff.2 ⟨continuous_const.add hn, continuous_const.sub hn⟩

omit [IsTotallyComplex E] in

theorem exists_isCompact_sub_mem :
    ∃ C : Set (BlockIx a r → Ad E), IsCompact C ∧ ∀ x, ∃ n ∈ ratN E a r, x - n ∈ C := by
  obtain ⟨K, hK, h⟩ := Formalism.IndefR.Eqv.G5.adl_cocompact (F := E)
  choose y hy using h
  refine ⟨Set.pi Set.univ fun _ => K, isCompact_univ_pi fun _ => hK, fun x => ?_⟩
  exact ⟨fun p => algebraMap E (Ad E) (y (x p)), ⟨fun p => y (x p), rfl⟩, fun p _ => hy (x p)⟩

omit [IsTotallyComplex E] in

theorem periodic_integrand (φ : GA E a → ℂ) (hl : ∀ (γ : GL (Fin a) E) (g : GA E a), φ (ratGL E a γ * g) = φ g)
    (g : GA E a) {n : BlockIx a r → Ad E} (hn : n ∈ ratN E a r) (x : BlockIx a r → Ad E) :
    φ (unip (n + x) * g) = φ (unip x * g) := by
  obtain ⟨y, rfl⟩ := hn
  have e : (AddMonoidHom.compLeft (algebraMap E (Ad E)).toAddMonoidHom (BlockIx a r)) y =
      fun p => algebraMap E (Ad E) (y p) := rfl
  rw [e, unip_add, unip_algebraMap, mul_assoc, hl]

theorem integrableOn_fundamentalDomain :
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a r : ℕ) (φ : Sm E a),
      (∀ (γ : GL (Fin a) E) (g : GA E a), φ.1 (ratGL E a γ * g) = φ.1 g) →
      IsOpen {k | finRep E a k φ = φ} →
      ∀ [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)]
        (μ : Measure (BlockIx a r → Ad E)) (𝓕 : Set (BlockIx a r → Ad E)), μ.IsAddHaarMeasure →
        IsAddFundamentalDomain (ratN E a r) 𝓕 μ →
        μ 𝓕 < ⊤ ∧ ∀ g : GA E a, IntegrableOn (fun x => φ.1 (unip x * g)) 𝓕 μ := by
  intro E _ _ _ a r φ hl hU _ _ μ 𝓕 hμ hF
  obtain ⟨C, hC, hcov⟩ := exists_isCompact_sub_mem (E := E) (a := a) (r := r)
  have hφ := continuous_of_isOpen_stab φ hU
  haveI : Countable (ratN E a r) := by
    have : Countable E := (Module.finBasis ℚ E).equivFun.toEquiv.countable_iff.2 inferInstance
    exact Function.Surjective.countable
      (f := (AddMonoidHom.compLeft (algebraMap E (Ad E)).toAddMonoidHom (BlockIx a r)).rangeRestrict)
      (AddMonoidHom.rangeRestrict_surjective _)
  have hfin : μ 𝓕 < ⊤ := by
    have h1 : 𝓕 ⊆ ⋃ n : ratN E a r, (n +ᵥ C) ∩ 𝓕 := fun x hx => by
      obtain ⟨n, hn, h⟩ := hcov x
      refine Set.mem_iUnion.2 ⟨⟨n, hn⟩, ⟨x - n, h, ?_⟩, hx⟩
      simp [AddSubgroup.vadd_def]
    calc μ 𝓕 ≤ ∑' n : ratN E a r, μ ((n +ᵥ C) ∩ 𝓕) := (measure_mono h1).trans (measure_iUnion_le _)
      _ = μ C := (hF.measure_eq_tsum C).symm
      _ < ⊤ := hC.measure_lt_top
  refine ⟨hfin, fun g => ?_⟩
  have hc : Continuous fun x : BlockIx a r → Ad E => φ.1 (unip x * g) :=
    hφ.comp (continuous_unip.mul continuous_const)
  obtain ⟨B, hB⟩ := hC.exists_bound_of_continuousOn hc.continuousOn
  refine Measure.integrableOn_of_bounded hfin.ne hc.aestronglyMeasurable (M := B) (Filter.Eventually.of_forall fun x => ?_)
  obtain ⟨n, hn, h⟩ := hcov x
  have := periodic_integrand φ.1 hl g hn (x - n)
  rw [add_sub_cancel] at this
  rw [this]
  exact hB _ h

end GlobalTheory.CompanionTheory.ConstTerm

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCompactParahoricSubgroupStatement
section
open PositivityTheory.LowerBoundConstant GlobalTheory GlobalTheory.Published GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCompact_parahoric_subgroup : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n s : ℕ) (d : Fin s → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin n), IsCompact (Gx k e : Set (GL (Fin n) k)) := by
  first | exact @GlobalTheory.CompanionTheory.MoyPrasad.isCompact_Gx | exact GlobalTheory.CompanionTheory.MoyPrasad.isCompact_Gx | (intros; apply GlobalTheory.CompanionTheory.MoyPrasad.isCompact_Gx <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IteratedDerivGaussianExponentialAtZeroStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iteratedDeriv_gaussian_exponential_at_zero : ∀ (m n : ℕ) (X : Fin n → ℝ) (v : Fin m → Fin n → ℂ), Differentiable ℂ (fun z : ℂ => (Complex.exp ((m : ℂ) * z * ∑ j, (X j : ℂ)) * Complex.exp (-(2 * Real.pi : ℂ) * ∑ a, ∑ j, Complex.exp (2 * z * X j) * ((‖v a j‖ ^ 2 : ℝ) : ℂ)))) ∧ ∀ r : ℕ, iteratedDeriv r (fun z : ℂ => (Complex.exp ((m : ℂ) * z * ∑ j, (X j : ℂ)) * Complex.exp (-(2 * Real.pi : ℂ) * ∑ a, ∑ j, Complex.exp (2 * z * X j) * ((‖v a j‖ ^ 2 : ℝ) : ℂ)))) 0 = PositivityTheory.Rg.Sw.evX ((PositivityTheory.Rg.Sw.dil (m := m) (2 * Real.pi) X ^ r) 1) v * PositivityTheory.Rg.Sw.gs (2 * Real.pi) v := by
  first | exact @GlobalTheory.CompanionTheory.DilFam.main | exact GlobalTheory.CompanionTheory.DilFam.main | (intros; apply GlobalTheory.CompanionTheory.DilFam.main <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwahoriLeviUnipotentFactorStatement
section
open PositivityTheory.LowerBoundConstant GlobalTheory GlobalTheory.Published GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iwahori_levi_unipotent_factor : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n s : ℕ) (d : Fin s → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin n), ∀ g ∈ KOne k (Fin n),
    ∃ m : Levi k (fun a => Fin (d a)), leviEmb k e m ∈ KOne k (Fin n) ∧
      ∃ x ∈ unipRad k e ⊓ KOne k (Fin n), ∃ c ∈ lowC k e, g = leviEmb k e m * x * c := by
  first | exact @GlobalTheory.CompanionTheory.KOneFactor.kone_factor | exact GlobalTheory.CompanionTheory.KOneFactor.kone_factor | (intros; apply GlobalTheory.CompanionTheory.KOneFactor.kone_factor <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetInducedTwoCharacters
section
open GlobalTheory.PRep GlobalTheory.SmGL
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.SmGL.Bernstein

theorem proportional_of_equiv {G V V' W : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup V'] [Module ℂ V'] [AddCommGroup W] [Module ℂ W]
    {τ : Representation ℂ G V} {τ' : Representation ℂ G V'} {σ : Representation ℂ G W}
    (E : τ.Equiv τ')
    (h : ∀ φ ψ : τ'.IntertwiningMap σ, φ.toLinearMap = 0 ∨ ∃ c : ℂ, ψ.toLinearMap = c • φ.toLinearMap)
    (φ ψ : τ.IntertwiningMap σ) :
    φ.toLinearMap = 0 ∨ ∃ c : ℂ, ψ.toLinearMap = c • φ.toLinearMap := by
  rcases h (φ.comp E.symm.toIntertwiningMap) (ψ.comp E.symm.toIntertwiningMap) with h0 | ⟨c, hc⟩
  · left
    ext v
    have := LinearMap.congr_fun h0 (E v)
    simpa using this
  · right
    refine ⟨c, ?_⟩
    ext v
    have := LinearMap.congr_fun hc (E v)
    simpa using this

theorem eq_zero_of_equiv {G V V' W : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup V'] [Module ℂ V'] [AddCommGroup W] [Module ℂ W]
    {τ : Representation ℂ G V} {τ' : Representation ℂ G V'} {σ : Representation ℂ G W}
    (E : τ.Equiv τ') (h : ∀ φ : τ'.IntertwiningMap σ, φ.toLinearMap = 0)
    (φ : τ.IntertwiningMap σ) : φ.toLinearMap = 0 := by
  ext v
  have := LinearMap.congr_fun (h (φ.comp E.symm.toIntertwiningMap)) (E v)
  simpa using this

theorem exists_diagonal_sizeMatrix (a b : ℕ) :
    ∃ D : SizeMatrix (Two (Fin a) (Fin b)) (Two (Fin a) (Fin b)),
      ∀ B : SizeMatrix (Two (Fin a) (Fin b)) (Two (Fin a) (Fin b)), B = D ↔ B.1 false true = 0 := by
  have card_f : Fintype.card (Two (Fin a) (Fin b) false) = a := Fintype.card_fin a
  have card_t : Fintype.card (Two (Fin a) (Fin b) true) = b := Fintype.card_fin b
  refine ⟨⟨fun i j => if i = j then (if i then b else a) else 0, ?_, ?_⟩, fun B => ⟨?_, ?_⟩⟩
  · intro i; cases i <;> simp [card_f, card_t]
  · intro j; cases j <;> simp [card_f, card_t]
  · rintro rfl; simp
  · intro hB
    have r0 := B.2.1 false
    have r1 := B.2.1 true
    have c0 := B.2.2 false
    have c1 := B.2.2 true
    simp only [Fintype.sum_bool, card_f, card_t] at r0 r1 c0 c1
    apply Subtype.ext
    funext i j
    cases i <;> cases j <;> simp <;> omega

set_option maxHeartbeats 600000 in

theorem mackey_maps_proportional : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a b : ℕ) (χ₁ χ₂ : kˣ →* ℂˣ), JacquetOfInducedFiltration k → IsSmoothChar χ₁ → IsSmoothChar χ₂ → IsUnitaryChar χ₁ → IsUnitaryChar χ₂ → (a ≠ b ∨ χ₁ ≠ χ₂) → (∀ φ ψ : (jac (two (stdSum (rfl : a + b = a + b))) (parInd (two (stdSum (rfl : a + b = a + b))) ((extTensor (detRep (Fin a) χ₁) (detRep (Fin b) χ₂)).comp (leviTwo k (Fin a) (Fin b)).symm.toMonoidHom))).IntertwiningMap (((extTensor (detRep (Fin a) χ₁) (detRep (Fin b) χ₂)).comp (leviTwo k (Fin a) (Fin b)).symm.toMonoidHom)), φ.toLinearMap = 0 ∨ ∃ c : ℂ, ψ.toLinearMap = c • φ.toLinearMap) := by
  intro k _ _ _ _ a b χ₁ χ₂ hJ h₁ h₂ u₁ u₂ hne
  have hc : Continuous (leviTwo k (Fin a) (Fin b)).symm.toMonoidHom :=
    continuous_prodMk.2 ⟨continuous_apply _, continuous_apply _⟩
  have hsm : IsSmooth ((extTensor (detRep (Fin a) χ₁) (detRep (Fin b) χ₂)).comp
      (leviTwo k (Fin a) (Fin b)).symm.toMonoidHom) :=
    isSmooth_comp (isSmooth_extTensor ((isSmooth_ofChar_iff _).2 h₁.detChar)
      ((isSmooth_ofChar_iff _).2 h₂.detChar)) _ hc
  obtain ⟨N, bb, hb⟩ := hJ Bool Bool (Fin (a + b)) (Two (Fin a) (Fin b)) (Two (Fin a) (Fin b))
    (two (stdSum (rfl : a + b = a + b))) (two (stdSum (rfl : a + b = a + b)))
  obtain ⟨S, hm, hbot, htop, hE⟩ := hb (TensorProduct ℂ ℂ ℂ) _ hsm
  obtain ⟨D, hD⟩ := exists_diagonal_sizeMatrix a b
  obtain ⟨t₀, ht₀⟩ := bb.surjective D
  refine GlobalTheory.T.filtration_unique_subquotient _ ((extTensor (detRep (Fin a) χ₁) (detRep (Fin b) χ₂)).comp (leviTwo k (Fin a) (Fin b)).symm.toMonoidHom) N S hm hbot htop t₀ ?_ ?_
  · exact proportional_of_equiv (hE t₀ (SizeMatrix.nonempty_rows (bb t₀)).some (SizeMatrix.nonempty_cols (bb t₀)).some).some
      (GlobalTheory.T.cell_functor_scalar_diagonal k a b χ₁ χ₂ (bb t₀) _ _ ((hD _).1 ht₀))
  · intro t ht
    exact eq_zero_of_equiv (hE t (SizeMatrix.nonempty_rows (bb t)).some (SizeMatrix.nonempty_cols (bb t)).some).some
      (GlobalTheory.T.cell_functor_nonscalar_offdiag k a b χ₁ χ₂ h₁ h₂ u₁ u₂ hne (bb t) _ _ fun h0 =>
        ht (bb.injective (((hD _).2 h0).trans ht₀.symm)))

end GlobalTheory.CompanionTheory.SmGL.Bernstein
end

