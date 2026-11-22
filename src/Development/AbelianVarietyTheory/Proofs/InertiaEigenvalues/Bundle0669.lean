import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0023
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0125
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0067
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsUnimodularBlockUpperTriangularSymmetricLevels
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFinsetDefiniteUnitaryDoubleCosets
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0603
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0651
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteClassSetHermitianUnitaryOpenLevel
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0488
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0529
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0522
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0524
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0551
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0663
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0658
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0657
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0036
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIrreducibleIffOfLinearEquiv
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0053
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0646
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnitaryAdmissibleMatrixCoefficient
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0126
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0015
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0377
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0352
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0223
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0378
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0074
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0059
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0088
import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsNonzeroIntertwiningMapFromUnitarySupercusp
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0659

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscreteAutomorphicRepGLLocalComponentIsUnitaris
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DefiniteBC GlobalTheory.BcSpeh MeasureTheory Matrix

namespace GlobalTheory.DiscreteUnit

section General

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] {Γ : Subgroup G} [Countable Γ]

theorem lintegral_lt_top {μ μ' : Measure G} [μ.IsHaarMeasure] [μ'.IsHaarMeasure] {F F' : Set G}
    (hF : IsFundamentalDomain Γ F μ) (hF' : IsFundamentalDomain Γ F' μ') {φ : G → ENNReal}
    (hφ : ∀ γ ∈ Γ, ∀ g, φ (γ * g) = φ g) (h : ∫⁻ g in F', φ g ∂μ' < ⊤) : ∫⁻ g in F, φ g ∂μ < ⊤ := by
  have e := Measure.isMulLeftInvariant_eq_smul μ μ'
  have hF2 : IsFundamentalDomain Γ F' μ := hF'.mono (Measure.absolutelyContinuous_isHaarMeasure μ μ')
  rw [hF.setLIntegral_eq hF2 φ fun γ g => hφ γ γ.2 g, e, Measure.restrict_smul, lintegral_smul_measure]
  exact ENNReal.mul_lt_top ENNReal.coe_lt_top h

theorem integral_mul_right {μ : Measure G} [μ.IsHaarMeasure] {F : Set G} (hF : IsFundamentalDomain Γ F μ) {φ : G → ℂ}
    (hφ : ∀ γ ∈ Γ, ∀ g, φ (γ * g) = φ g) {x : G} (hx : Measure.modularCharacter x = 1) :
    ∫ g in F, φ (g * x) ∂μ = ∫ g in F, φ g ∂μ := by
  have hm : MeasurePreserving (fun g => g * x) μ μ :=
    ⟨measurable_mul_const x, by rw [GlobalTheory.LevelUnimod.map_mul_right_eq, hx, one_smul]⟩
  have hF2 : IsFundamentalDomain Γ ((fun g => g * x) ⁻¹' F) μ :=
    hF.preimage_of_equiv hm.quasiMeasurePreserving Function.bijective_id fun γ g => mul_assoc γ.1 g x
  rw [hF.setIntegral_eq hF2 (f := fun g => φ (g * x)) fun γ g => by
    change φ (γ.1 * g * x) = _
    rw [mul_assoc, hφ γ γ.2]]
  exact hm.setIntegral_preimage_emb (MeasurableEquiv.mulRight x).measurableEmbedding φ F

theorem isUnitarisable_of_embedding {H X : Type} [Group H] [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ H X)
    (ι : H → G) (hι : ∀ h, Measure.modularCharacter (ι h) = 1) (f : X →ₗ[ℂ] (G → ℂ)) (hf : Function.Injective f)
    (hc : ∀ v, Continuous (f v)) (hl : ∀ v, ∀ γ ∈ Γ, ∀ g, f v (γ * g) = f v g)
    (h2 : ∀ v, ∃ (μ : Measure G) (F : Set G), μ.IsHaarMeasure ∧ IsFundamentalDomain Γ F μ ∧
      ∫⁻ g in F, ‖f v g‖ₑ ^ 2 ∂μ < ⊤)
    (hρ : ∀ h v g, f (ρ h v) g = f v (g * ι h)) : IsUnitarisable ρ := by
  obtain ⟨μ, F, hμ, hF, -⟩ := h2 0
  have hm : ∀ v, MemLp (f v) 2 (μ.restrict F) := fun v => by
    obtain ⟨μ', F', hμ', hF', h⟩ := h2 v
    have h3 := lintegral_lt_top hF hF' (fun γ hγ g => by rw [hl v γ hγ g]) h
    refine ⟨(hc v).aestronglyMeasurable, ?_⟩
    rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top two_ne_zero ENNReal.ofNat_ne_top]
    simpa using h3
  have hi : ∀ v w, Integrable (fun g => f v g * starRingEnd ℂ (f w g)) (μ.restrict F) := fun v w =>
    (hm v).integrable_mul (hm w).star
  refine ⟨LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun v w => ∫ g in F, f v g * starRingEnd ℂ (f w g) ∂μ)
    (fun v v' w => ?_) (fun c v w => ?_) (fun v w w' => ?_) (fun c v w => ?_), fun v w => ?_, fun v hv => ?_,
    fun h v w => ?_⟩
  · rw [← integral_add (hi _ _) (hi _ _)]
    simp [add_mul]
  · simp [mul_assoc, integral_const_mul]
  · rw [← integral_add (hi _ _) (hi _ _)]
    simp [mul_add]
  · simp [mul_left_comm _ (starRingEnd ℂ c), integral_const_mul]
  · simp only [LinearMap.mk₂'ₛₗ_apply]
    rw [← integral_conj]
    simp [mul_comm]
  · simp only [LinearMap.mk₂'ₛₗ_apply, Complex.mul_conj]
    rw [integral_complex_ofReal, Complex.ofReal_re]
    have hi2 : Integrable (fun g => Complex.normSq (f v g)) (μ.restrict F) := by
      simpa [Complex.mul_conj] using (hi v v).re
    refine (integral_pos_iff_support_of_nonneg (fun g => Complex.normSq_nonneg _) hi2).2 (pos_iff_ne_zero.2 fun h0 => hv ?_)
    have ho : IsOpen (Function.support fun g => Complex.normSq (f v g)) :=
      (Complex.continuous_normSq.comp (hc v)).isOpen_support
    rw [Measure.restrict_apply ho.measurableSet] at h0
    have h4 := hF.measure_zero_of_invariant _ (fun γ => by
      ext g
      rw [Set.mem_smul_set_iff_inv_smul_mem, Function.mem_support, Function.mem_support]
      change Complex.normSq (f v ((γ⁻¹ : Γ).1 * g)) ≠ 0 ↔ _
      rw [hl v _ (γ⁻¹).2]) h0
    have h5 := Function.support_eq_empty_iff.1 (ho.measure_eq_zero_iff μ |>.1 h4)
    refine hf (funext fun g => ?_)
    rw [map_zero]
    exact Complex.normSq_eq_zero.1 (congrFun h5 g)
  · simp only [LinearMap.mk₂'ₛₗ_apply, hρ]
    exact integral_mul_right hF (φ := fun g => f v g * starRingEnd ℂ (f w g))
      (fun γ hγ g => by rw [hl v γ hγ, hl w γ hγ]) (hι h)

end General

def transInv (A : Type) [CommRing A] (n : ℕ) : GL (Fin n) A ≃* GL (Fin n) A where
  toFun g := ⟨(g⁻¹).valᵀ, g.valᵀ, by rw [← transpose_mul]; simp, by rw [← transpose_mul]; simp⟩
  invFun g := ⟨(g⁻¹).valᵀ, g.valᵀ, by rw [← transpose_mul]; simp, by rw [← transpose_mul]; simp⟩
  left_inv g := Units.ext (transpose_transpose _)
  right_inv g := Units.ext (transpose_transpose _)
  map_mul' g h := Units.ext (by
    change ((g * h)⁻¹).valᵀ = (g⁻¹).valᵀ * (h⁻¹).valᵀ
    rw [← transpose_mul, _root_.mul_inv_rev, Units.val_mul])

theorem continuous_transInv (A : Type) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] (n : ℕ) :
    Continuous (transInv A n) :=
  Units.continuous_iff.2 ⟨Units.continuous_coe_inv.matrix_transpose, Units.continuous_val.matrix_transpose⟩

theorem cornerGL_transInv {R S : Type} [CommRing R] [CommRing S] {n : ℕ} (s : R →ₙ+* S) (g : GL (Fin n) R) :
    cornerGL n s (transInv R n g) = transInv S n (cornerGL n s g) := by
  ext i j
  change (1 : Matrix (Fin n) (Fin n) S) i j - s ((1 : Matrix (Fin n) (Fin n) R) i j) + s ((g⁻¹).val j i) =
    (1 : Matrix (Fin n) (Fin n) S) j i - s ((1 : Matrix (Fin n) (Fin n) R) j i) + s ((g⁻¹).val j i)
  simp only [Matrix.one_apply, eq_comm]

theorem modular_eq_one {k S : Type} [Field k] [Infinite k] [CommRing S] [TopologicalSpace S] [IsTopologicalRing S] {n : ℕ}
    [LocallyCompactSpace (GL (Fin n) S)] [SecondCountableTopology (GL (Fin n) S)] (ι : GL (Fin n) k →* GL (Fin n) S)
    (h : ∀ g, ι (transInv k n g) = transInv S n (ι g)) (g : GL (Fin n) k) : Measure.modularCharacter (ι g) = 1 := by
  borelize (GL (Fin n) S)
  refine GlobalTheory.gl_character_eq_one_of_transpose_inv _ _ (Measure.modularCharacter.comp ι) (fun g g' e => ?_) g
  obtain rfl : g' = transInv _ n g := Units.ext e
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply, h]
  exact GlobalTheory.LevelUnimod.modular_aut _ (continuous_transInv _ n) (continuous_transInv _ n) _

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {N : ℕ}

theorem countable_latticeGL : Countable (latticeGL E N) := by
  haveI : Countable E := (Module.finBasis ℚ E).equivFun.injective.countable
  haveI : Countable (Matrix (Fin N) (Fin N) E) := inferInstanceAs (Countable (Fin N → Fin N → E))
  haveI : Countable (GL (Fin N) E) := Units.val_injective.countable
  let f : FreeGroup (Option (GL (Fin N) E)) →* GA E N :=
    FreeGroup.lift fun o => o.elim (splitCentre E N 1) (ratGL E N)
  have h : latticeGL E N ≤ f.range := sup_le
    (by rintro _ ⟨γ, rfl⟩; exact ⟨.of (some γ), FreeGroup.lift_apply_of⟩)
    (Subgroup.zpowers_le.2 ⟨.of none, FreeGroup.lift_apply_of⟩)
  haveI : Countable (FreeGroup (Option (GL (Fin N) E))) := Quot.mk_surjective.countable
  exact ((Set.countable_range f).mono h).to_subtype

theorem left_latticeGL {φ : Sm E N} (h : IsAutForm φ) (h' : IsSqInt φ.1) :
    ∀ γ ∈ latticeGL E N, ∀ g, φ.1 (γ * g) = φ.1 g := by
  let S : Subgroup (GA E N) :=
    { carrier := {γ | ∀ g, φ.1 (γ * g) = φ.1 g}
      one_mem' := fun g => by rw [one_mul]
      mul_mem' := fun {x y} hx hy g => by rw [mul_assoc, hx, hy]
      inv_mem' := fun {x} hx g => by rw [← hx, mul_inv_cancel_left] }
  have : latticeGL E N ≤ S := sup_le (by rintro _ ⟨γ, rfl⟩; exact h.left γ) (Subgroup.zpowers_le.2 (h'.1 1))
  exact this

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem isUnitarisable_of_isLocCompGL : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (N : ℕ)
    (V : Submodule ℂ (Sm E N)), IsDiscrete V → ∀ (w : HeightOneSpectrum (𝓞 E)) (σ : LocIrr w N),
    IsLocCompGL V w σ → IsUnitarisable σ.ρ := by
  intro E _ _ _ N V hV w σ ⟨f, h0, hf, hρ⟩
  letI : MeasurableSpace (GA E N) := borel _
  haveI : BorelSpace (GA E N) := ⟨rfl⟩
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele E
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele E
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField E
  haveI : LocallyCompactSpace (Matrix (Fin N) (Fin N) (Ad E)) :=
    inferInstanceAs (LocallyCompactSpace (Fin N → Fin N → Ad E))
  haveI : LocallyCompactSpace (Matrix (Fin N) (Fin N) (Ad E))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
  haveI : LocallyCompactSpace (GA E N) := Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  haveI : SecondCountableTopology (Matrix (Fin N) (Fin N) (Ad E)) :=
    inferInstanceAs (SecondCountableTopology (Fin N → Fin N → Ad E))
  haveI : SecondCountableTopology (Matrix (Fin N) (Fin N) (Ad E))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  haveI : SecondCountableTopology (GA E N) := Units.isEmbedding_embedProduct.secondCountableTopology
  haveI := countable_latticeGL (E := E) (N := N)
  haveI : Infinite (w.adicCompletion E) := .of_injective _ (algebraMap E _).injective
  have hinj : Function.Injective f := by
    rcases ((GlobalTheory.CuspRep.isIrreducible_iff _).1 σ.irred).2 (LinearMap.ker f) (fun g v hv => by
      rw [LinearMap.mem_ker] at hv ⊢
      rw [hρ, hv, map_zero]) with h | h
    · exact LinearMap.ker_eq_bot.1 h
    · exact absurd (LinearMap.ker_eq_top.1 h) h0
  refine isUnitarisable_of_embedding (Γ := latticeGL E N) σ.ρ (fun g => finGL E N (locGL E N w g)) (fun g => ?_)
    ((Sm E N).subtype.comp f) (Subtype.val_injective.comp hinj)
    (fun v => GlobalTheory.CuspRep.ContAut.continuous_of_isOpen_stab E N (f v) (hV.aut _ (hf v)).level)
    (fun v => left_latticeGL (hV.aut _ (hf v)) (hV.sqInt _ (hf v))) (fun v => (hV.sqInt _ (hf v)).2)
    fun g v x => congrFun (congrArg Subtype.val (hρ g v)) x
  exact modular_eq_one ((finGL E N).comp (locGL E N w))
    (fun g => (congrArg (finGL E N) (cornerGL_transInv (sLoc E w) g)).trans (cornerGL_transInv (sFin E) _)) g

end GlobalTheory.DiscreteUnit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFinsetDefiniteUnitaryDoubleCosetsStatement
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finset_definiteUnitary_doubleCosets : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), ∀ L : Subgroup (finU E n), IsOpen (L : Set (finU E n)) → ∃ S : Finset (UA E n), ∀ g : UA E n, ∃ γ ∈ ratU E n, ∃ s ∈ S, ∃ k ∈ L, ∃ y ∈ infU E n, g = γ * s * (k : UA E n) * y := by
  first | exact @GlobalTheory.UnitaryBC.ClassTransport.exists_finset_double_cosets | exact GlobalTheory.UnitaryBC.ClassTransport.exists_finset_double_cosets | (intros; apply GlobalTheory.UnitaryBC.ClassTransport.exists_finset_double_cosets <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFixedVectorFiltrationJumpBreuilKisin
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

set_option maxHeartbeats 4000000 in

theorem GlobalTheory.BKGal.JumpDR.jump_gives_fixed_vector : GlobalTheory.Published.FontaineBcris → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a], l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (I : Ident (thetaW a LL) ϖ P T) (jB : (ι → OB l ↥(OL LL)) ≃ₗ[OB l ↥(OL LL)] TW (OB l ↥(OL LL)) T) (Pl : LocPrime l) (AI : LocAinf l Pl), IsStd Pl AI → IsCrisCmp I jB → IsHoriz (thetaW a LL) ϖ (sQ l) P jB → (∀ m ∈ P.M, P.EN m ∈ P.Man) → ∀ i ∈ P.jumps, ∃ x : T.V ⊗[ℚ_[l]] Pl.R.BdR, (∀ g : Gl l, (g : GQ l) ∈ GK (ϖ.field a) → actVdR (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ g x = x) ∧ x ∈ FilV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) (LL := ↥LL.1) (V := T.V) i ∧ x ∉ FilV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) (LL := ↥LL.1) (V := T.V) (i + 1) := by
  intro hF l _ a e _ _ ϖ LL _ _ hl ι _ _ P T I jB Pl AI hStd hCmp hHor hEN i hi
  have Td : LocTied l Pl AI := hStd.some
  obtain ⟨X, hX⟩ := GlobalTheory.T.exists_bcrisTensorLattice_to_deRham_map l Pl AI Td LL T
  obtain ⟨A, hA⟩ := GlobalTheory.T.exists_coeffDeRhamPlus_action_on_VTensorBdR l Pl AI Td LL T
  obtain ⟨n, d, c, hd, h1, h2⟩ := GlobalTheory.T.exists_horizontal_vector_of_breuilKisin_jump l a e LL hl ι P hEN i hi
  let m : Fin n → P.MMl := fun k => ⟨P.xi (d k), hd k⟩
  have key := fun j => GlobalTheory.T.mem_completionFiltration_iff_deRhamFiltration hF l a e ϖ LL hl ι P T I jB Pl AI Td hCmp X hX A hA n
    (fun k => GlobalTheory.BKGal.JumpDR.kLift ↥(OL LL) (c k)) m j
  refine ⟨∑ k, A (ϖ.iD (thetaW a LL) ↥LL.1 (GlobalTheory.BKGal.JumpDR.kLift ↥(OL LL) (c k)))
    (X (jB (toBcris (thetaW a LL) ϖ P (m k)))), ?_, (key i).1 h1, fun h => h2 ((key (i + 1)).2 h)⟩
  intro g hg
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have e1 := GlobalTheory.T.coeffDeRhamPlusAction_constants_galois_comm l Pl AI Td LL T A hA a e ϖ (c k) g hg (X (jB (toBcris (thetaW a LL) ϖ P (m k))))
  have e2 := GlobalTheory.T.bcrisTensorLattice_to_deRham_equivariant l Pl AI Td LL T X hX g (jB (toBcris (thetaW a LL) ϖ P (m k)))
  have e3 := hHor g hg (d k) (hd k)
  rw [e1, ← e2]
  exact congrArg _ (congrArg X e3)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFrobeniusOnStratifiedValueStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_frobenius_on_stratifiedValue : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (S : Strat bk d) (B : Obj l ↥(OL K)) (N : Type) [AddCommGroup N] [Module B.A N] (V : Eval S B N) (t : B.A), t ∈ B.I → ∃ Ψ : N →ₛₗ[B.D.φ] N, IsPsi V t Ψ := by
  first | exact @GlobalTheory.BSP.FrobValue.psi_exists | exact GlobalTheory.BSP.FrobValue.psi_exists | (intros; apply GlobalTheory.BSP.FrobValue.psi_exists <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIrreducibleQuotientFinitelyGeneratedRepStatement
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_irreducible_quotient_finitelyGenerated_rep : ∀ (G V : Type) [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (s : Finset V), Nontrivial V → Submodule.span ℂ {w | ∃ g : G, ∃ v ∈ s, w = ρ g v} = ⊤ → ∃ (W : Type) (_ : AddCommGroup W) (_ : Module ℂ W) (τ : Representation ℂ G W), τ.IsIrreducible ∧ ∃ f : ρ.IntertwiningMap τ, Function.Surjective f := by
  first | exact @GlobalTheory.IrrQuot.main | exact GlobalTheory.IrrQuot.main | (intros; apply GlobalTheory.IrrQuot.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLocalUnitaryEmbeddingDefiniteUnitaryNonsplStatement
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_localUnitary_embedding_definiteUnitary_nonsplit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : HeightOneSpectrum (𝓞 E)) (s : w.adicCompletion E →+* w.adicCompletion E), (∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x)) → (∀ x, Valued.v (s x) = Valued.v x) → ¬ IsSplitAt w → ∃ ι : Formalism.UG.UJ s (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) →* UA E n, Continuous ι ∧ (∀ g, ι g ∈ locU n w ∧ cLoc w (ι g) = g.1) ∧ (∀ x ∈ locU n w, cLoc w x = 1 → x = 1) ∧ ∀ x g, cLoc w x = 1 → x * ι g = ι g * x := by
  first | exact @GlobalTheory.UnitaryBC.exists_locUnitary_embedding | exact GlobalTheory.UnitaryBC.exists_locUnitary_embedding | (intros; apply GlobalTheory.UnitaryBC.exists_locUnitary_embedding <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLogUniformizerTiltBdRPlusCocycle
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.LogFlatLam

variable {l : ℕ} [Fact l.Prime]

theorem eD_smul_tB {P : LocPrime l} {AI : LocAinf l P} {T : LocTied l P AI} {C : Core l} (hF : Fits T C)
    (z : ℤ_[l]) :
    T.eD (P.ιB ((z : ℚ_[l]) • P.tB)) =
      algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (Per.zA l z) * C.j C.t) := by
  rw [map_smul, Algebra.smul_def, map_mul, T.zD, hF.ι, hF.t, Core.tB, C.ι_j, map_mul, GlobalTheory.RingIface.zD_eq_alg]
  simp only [aDp, RingHom.comp_apply]

theorem exists_mem_FilD_neg (C : Core l) (x : Per.BdR l) : ∃ n : ℕ, x ∈ Per.FilD l (-(n : ℤ)) := by
  have he := GlobalTheory.T.isPrimitiveTiltedRootOfUnity_localPeriodRingsData l C
  obtain ⟨n, y, hy⟩ := (GlobalTheory.MemLoc.BdRField.bdR_isField l).2.2.2 C.ε he x
  refine ⟨n, (GlobalTheory.MemLoc.mem_FilD_iff_xi_pow l C.ε he _ x).2 ⟨y, ?_⟩⟩
  simpa using hy

theorem const_eq_zero_of_mem_Fil_one {P : LocPrime l} {AI : LocAinf l P} {T : LocTied l P AI} {C : Core l}
    (hF : Fits T C) (K : FinExt l) (c : ↥K.1) (hc : algebraMap ↥K.1 P.R.BdR c ∈ (P.PD K).Fil 1) : c = 0 := by
  have h1 := (T.fil K 1 _).1 hc
  have e : algebraMap ↥K.1 P.R.BdR c = algebraMap (Om l) P.R.BdR (c : Om l) := rfl
  rw [e, hF.o] at h1
  obtain ⟨z, hz, hze⟩ := (GlobalTheory.BdRQuot.mem_FilD_nat 1 _).1 (by exact_mod_cast h1)
  have hz' : z = C.o (c : Om l) := (GlobalTheory.MemLoc.BdRField.bdR_isField l).2.1 hze
  have h0 : Per.θD l z = 0 := by
    have := (GlobalTheory.MemLoc.thetaD_onto_ker l).2
    rw [← this] at hz
    exact hz
  rw [hz', C.o_sec.th] at h0
  have : (c : Om l) = 0 := (algebraMap (Om l) ℂ_[l]).injective (by simpa using h0)
  exact Subtype.ext this

end GlobalTheory.LogFlatLam

namespace GlobalTheory.LogFlatLam

variable {l : ℕ} [Fact l.Prime]

theorem σD_alg (g : GQ l) (x : Per.BdRp l) :
    Per.σD g (algebraMap (Per.BdRp l) (Per.BdR l) x) = algebraMap (Per.BdRp l) (Per.BdR l) (Per.σDp g x) :=
  GlobalTheory.RingIface.sigD_alg l g x

theorem σDp_alg (g : GQ l) (a : Per.AinfP l) :
    Per.σDp g (algebraMap (Per.AinfP l) (Per.BdRp l) a) =
      algebraMap (Per.AinfP l) (Per.BdRp l) (Per.extP (Per.σA g) a) :=
  GlobalTheory.RingIface.sigDp_alg l g a

theorem σDp_aDp (g : GQ l) (a : Ainf l) : Per.σDp g (aDp l a) = aDp l (Per.σA g a) := by
  simp only [aDp, RingHom.comp_apply, σDp_alg, GlobalTheory.RingBasics.awayMap_algebraMap₂]

end GlobalTheory.LogFlatLam

open GlobalTheory.LogFlatLam in

theorem GlobalTheory.LogFlatLam.exists_lam : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (C : Core l), Fits T C → ∀ (b : P.R.B) (c : ↥(GK K) → ℤ_[l]), ((∀ g : ↥(GK K), actSt P (g : GQ l) (Polynomial.X + Polynomial.C b) = Polynomial.X + Polynomial.C b + Polynomial.C ((c g : ℚ_[l]) • P.tB)) ∧ phiSt P (Polynomial.X + Polynomial.C b) = (l : Bst P) * (Polynomial.X + Polynomial.C b)) → (∀ g, bk.FixFlat g → c g = 0) → (∀ m : ℕ, ∃ (k : ℕ) (s : bk.S), bk.E ∣ s ∧ ∀ g : ↥(GK K), aDp l (Per.σA (g : GQ l) (bk.ev s) - bk.ev s) - (l : Per.BdRp l) ^ k * (aDp l (Per.zA l (c g)) * C.j C.t) ∈ Per.FilP l m) → ∃ lam : Per.BdRp l, (∀ g : ↥(GK K), Per.σDp (g : GQ l) lam = lam + aDp l (Per.zA l (c g)) * C.j C.t) ∧ (∀ m : ℕ, ∃ (k : ℕ) (s : bk.S), bk.E ∣ s ∧ aDp l (bk.ev s) - (l : Per.BdRp l) ^ k * lam ∈ Per.FilP l m) := by
  rintro l _ K bk P AI T C hF b c ⟨hact, -⟩ - happrox
  obtain ⟨ι, hιC, hιg⟩ := GlobalTheory.BstLog.iota_exists l P AI T
  have hinj := (GlobalTheory.MemLoc.BdRField.bdR_isField l).2.1
  set yA := ι (Polynomial.X + Polynomial.C b) with hyA
  have hy : ∀ g : ↥(GK K), P.actQdR (g : GQ l) yA = yA + P.ιB ((c g : ℚ_[l]) • P.tB) := by
    intro g
    rw [hyA, ← hιg, hact g, map_add, hιC]
  have hKc : ∀ (g : ↥(GK K)) (d : ↥K.1), P.actQdR (g : GQ l) (algebraMap ↥K.1 P.R.BdR d) =
      algebraMap ↥K.1 P.R.BdR d := by
    intro g d
    rw [← P.PD_actdR K g, AlgEquiv.commutes]
  obtain ⟨n, hn⟩ := exists_mem_FilD_neg C (T.eD yA)
  have hn' : yA ∈ (P.PD K).Fil (-(n : ℤ)) := (T.fil K _ _).2 hn
  have hg1 : ∀ g : ↥(GK K), (P.PD K).actdR g yA - yA ∈ (P.PD K).Fil 1 := by
    intro g
    rw [P.PD_actdR, hy, add_sub_cancel_left]
    refine (T.fil K 1 _).2 ?_
    rw [eD_smul_tB hF]
    exact_mod_cast (GlobalTheory.BdRQuot.mem_FilD_nat 1 _).2
      ⟨_, Ideal.mul_mem_left _ _ (GlobalTheory.MemLoc.core_t_unit_fil l C).2.1, rfl⟩
  obtain ⟨c0, -, hc0⟩ := GlobalTheory.FilInv.const_of_invariant_mod l P AI T K (-(n : ℤ)) 1 yA hn' hg1
  set lamA := yA - algebraMap ↥K.1 P.R.BdR c0 with hlamA
  obtain ⟨lam, hlam1, hlamE⟩ := (GlobalTheory.BdRQuot.mem_FilD_nat 1 _).1 (by exact_mod_cast (T.fil K 1 lamA).1 hc0)
  have hequiv : ∀ g : ↥(GK K), Per.σDp (g : GQ l) lam = lam + aDp l (Per.zA l (c g)) * C.j C.t := by
    intro g
    apply hinj
    rw [map_add, ← σD_alg, hlamE, ← T.actD, hlamA, map_sub, hKc, hy]
    simp only [map_sub, map_add, eD_smul_tB hF]
    ring
  refine ⟨lam, hequiv, fun m => ?_⟩
  obtain ⟨k, s, hEs, hs⟩ := happrox m
  refine ⟨k, s, hEs, ?_⟩
  set x := aDp l (bk.ev s) - (l : Per.BdRp l) ^ k * lam with hx
  set xA := T.eD.symm (algebraMap (Per.BdRp l) (Per.BdR l) x) with hxA
  have hxA' : T.eD xA = algebraMap (Per.BdRp l) (Per.BdR l) x := by rw [hxA, RingEquiv.apply_symm_apply]
  have hx1 : xA ∈ (P.PD K).Fil 1 := by
    refine (T.fil K 1 _).2 ?_
    rw [hxA']
    refine (GlobalTheory.BdRQuot.mem_FilD_nat 1 _).2 ⟨x, ?_, rfl⟩
    refine Ideal.sub_mem _ (((GlobalTheory.AinfEPow.ePow_facts l K bk 1).2.2.1 _).2 ?_) (Ideal.mul_mem_left _ _ hlam1)
    rw [pow_one]
    exact map_dvd _ hEs
  have hxg : ∀ g : ↥(GK K), (P.PD K).actdR g xA - xA ∈ (P.PD K).Fil (m : ℤ) := by
    intro g
    refine (T.fil K _ _).2 ?_
    rw [map_sub, P.PD_actdR, T.actD, hxA', σD_alg, ← map_sub]
    refine (GlobalTheory.BdRQuot.mem_FilD_nat m _).2 ⟨_, ?_, rfl⟩
    have e : Per.σDp (g : GQ l) x - x = aDp l (Per.σA (g : GQ l) (bk.ev s) - bk.ev s) -
        (l : Per.BdRp l) ^ k * (aDp l (Per.zA l (c g)) * C.j C.t) := by
      rw [hx, map_sub, map_mul, map_pow, map_natCast, σDp_aDp, hequiv, map_sub]
      ring
    rw [e]
    exact hs g
  obtain ⟨c', hc'1, hc'm⟩ := GlobalTheory.FilInv.const_of_invariant_mod l P AI T K 1 (m : ℤ) xA hx1 hxg
  have hc'0 : c' = 0 := const_eq_zero_of_mem_Fil_one hF K c' hc'1
  rw [hc'0, map_zero, sub_zero] at hc'm
  have h := (T.fil K _ _).1 hc'm
  rw [hxA'] at h
  obtain ⟨z, hz, hze⟩ := (GlobalTheory.BdRQuot.mem_FilD_nat m _).1 h
  rw [← hinj hze]
  exact hz
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsNonzeroIntertwiningMapFromUnitarySupercuspStatement
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nonzero_intertwiningMap_from_unitary_supercuspidal : ∀ (G W V : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup W] [Module ℂ W] [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G W) (ρ : Representation ℂ G V) (p : π.IntertwiningMap ρ), IsSmooth π → IsSupercuspidal ρ → IsUnitarisable ρ → (∀ z ∈ Subgroup.center G, ∃ c : ℂ, ∀ w, π z w = c • w) → p ≠ 0 → ∃ ι : ρ.IntertwiningMap π, ι ≠ 0 := by
  first | exact @GlobalTheory.CuspBack.exists_back | exact GlobalTheory.CuspBack.exists_back | (intros; apply GlobalTheory.CuspBack.exists_back <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSmoothDualNeZeroAtVectorStatement
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_smoothDual_ne_zero_at_vector : ∀ (G V : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V), (∀ U ∈ 𝓝 (1 : G), ∃ K : Subgroup G, IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ (K : Set G) ⊆ U) → IsSmooth ρ → ∀ v : V, v ≠ 0 → ∃ l : Module.Dual ℂ V, l ∈ smoothPart ρ.dual ∧ l v ≠ 0 := by
  first | exact @GlobalTheory.SmoothForm.exists_smooth_form_ne_zero | exact GlobalTheory.SmoothForm.exists_smooth_form_ne_zero | (intros; apply GlobalTheory.SmoothForm.exists_smooth_form_ne_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsStratifiedPhiModuleHomValueMapStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_stratifiedPhiModuleHom_valueMap : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d d' : ℕ) (S : Strat bk d) (S' : Strat bk d') (Y : Matrix (Fin d') (Fin d) bk.S), IsStratHom S S' Y → ∀ (B : Obj l ↥(OL K)) (N : Type) [AddCommGroup N] [Module B.A N] (N' : Type) [AddCommGroup N'] [Module B.A N'] (V : Eval S B N) (V' : Eval S' B N'), ∃ w : N →ₗ[B.A] N', ∀ (Q : Obj l ↥(OL K)) (a : Hom B Q) (g : Hom bk.prism Q) (x : N), V'.v a g (w x) = (Y.map (BK.hf g)).mulVec (V.v a g x) := by
  first | exact @GlobalTheory.BSP.evalHom | exact GlobalTheory.BSP.evalHom | (intros; apply GlobalTheory.BSP.evalHom <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsStratifiedPhiModuleValueStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_stratifiedPhiModuleValue : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (S : Strat bk d) (B : Obj l ↥(OL K)), ∃ (N : Type) (_ : AddCommGroup N) (_ : Module B.A N), Nonempty (Eval S B N) := by
  first | exact @GlobalTheory.BSP.exists_eval | exact GlobalTheory.BSP.exists_eval | (intros; apply GlobalTheory.BSP.exists_eval <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsStratifiedValueTransitionBaseChangeStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_stratifiedValue_transition_baseChange : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (S : Strat bk d) (B B' : Obj l ↥(OL K)) (N : Type) [AddCommGroup N] [Module B.A N] (N' : Type) [AddCommGroup N'] [Module B'.A N'] (V : Eval S B N) (V' : Eval S B' N') (k : Hom B B'), ∃ t : N →ₛₗ[k.f] N', SemiBC t ∧ ∀ (Q : Obj l ↥(OL K)) (a : Hom B' Q) (g : Hom bk.prism Q) (x : N), V'.v a g (t x) = V.v (a.comp k) g x := by
  first | exact @GlobalTheory.BSP.eval_transition | exact GlobalTheory.BSP.eval_transition | (intros; apply GlobalTheory.BSP.eval_transition <;> assumption)
end

