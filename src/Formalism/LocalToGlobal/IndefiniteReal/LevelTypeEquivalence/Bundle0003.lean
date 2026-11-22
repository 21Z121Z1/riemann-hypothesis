import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle0001
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0002
import Formalism.LocalToGlobal.IndefiniteReal.PHeisFC
import Formalism.LocalToGlobal.IndefiniteReal.HaarTransfer.MinfUnique
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdicIntegersCompact.IsCompactAdicCompletionIntegers
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0001

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.FuncSt
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
  IsDedekindDomain NumberField
open scoped TensorProduct ContDiff

namespace Formalism.IndefR.Eqv

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def ratMx (D : D7) (m n : ℕ) : AddSubgroup (Mx D m n) :=
  ((incA D).toAddMonoidHom.mapMatrix (m := Fin m) (n := Fin n)).range

def embI (S T : HSp D) {r : ℕ} (C : Matrix (Fin T.rank) (Fin r) D.host.E) (a : Mx D r S.rank) : WO S T :=
  HMul.hMul (C.map (incA D)) a

def ellI (S T : HSp D) {r : ℕ} (C : Matrix (Fin T.rank) (Fin r) D.host.E) (μ : Measure (Mx D r S.rank))
    (𝓕 : Set (Mx D r S.rank)) (f : WO S T → ℂ) : ℂ :=
  ∫ a in 𝓕, f (embI S T C a) ∂μ

def IsPerpI (S T : HSp D) {r : ℕ} (C : Matrix (Fin T.rank) (Fin r) D.host.E)
    (x : Matrix (Fin T.rank) (Fin S.rank) D.host.E) : Prop :=
  Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) C * T.gram * x = 0

def IsIInv (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) {r : ℕ} (C : Matrix (Fin T.rank) (Fin r) D.host.E)
    (ℓ : (WO S T → ℂ) →ₗ[ℂ] ℂ) : Prop :=
  (∀ (a : Mx D r S.rank) f, IsThetaFunO ψ S T f → ℓ (heisO ψ S T (embI S T C a) f) = ℓ f) ∧
    ∀ x, IsPerpI S T C x → ∀ f, IsThetaFunO ψ S T f → ℓ (heisO ψ S T (ratW T S x) f) = ℓ f

def IsSobContO (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (ℓ : (WO S T → ℂ) →ₗ[ℂ] ℂ) : Prop :=
  ∃ (k : ℕ) (L : (Fin k → ℝ) →+ WO S T) (N : ℕ), IsRealFrame L ∧
    ∀ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) →
      ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL T S) 𝓕 μ →
        ∃ c : ℝ, ∀ f, IsThetaFunO ψ S T f → (∀ u ∈ U, u.map (infPart D) = 0 → heisO ψ S T u f = f) →
          ‖ℓ f‖ ≤ c * sobO ψ L N μ 𝓕 f

def FuncUniq (D : D7) : Prop :=
  ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) → ∀ S T : HSp D, Formalism.IndefR.Fin.SvNSchurO ψ S T →
    ∀ (r : ℕ) (C : Matrix (Fin T.rank) (Fin r) D.host.E), IsIsoFrame T C →
      ∀ (μ : Measure (Mx D r S.rank)) (𝓕 : Set (Mx D r S.rank)), μ.IsAddHaarMeasure →
        IsAddFundamentalDomain (ratMx D r S.rank) 𝓕 μ →
        ∀ ℓ : (WO S T → ℂ) →ₗ[ℂ] ℂ, IsIInv ψ S T C ℓ → IsSobContO ψ S T ℓ →
          ∃ c : ℂ, ∀ f, IsThetaFunO ψ S T f → ℓ f = c * ellI S T C μ 𝓕 f

def RatActO (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om →
    Formalism.IndefR.Fin.SvNSchurO ψ S T →
    ∀ γ ∈ GQ S, ∀ γ' ∈ GQ T, ∀ f, IsThetaFunO ψ S T f → ∀ w, om (γ, γ') f w = f (actO S T γ⁻¹ γ'⁻¹ w)

def ParabN (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om →
    Formalism.IndefR.Fin.SvNSchurO ψ S T →
    ∀ (r : ℕ) (C : Matrix (Fin T.rank) (Fin r) D.host.E), IsIsoFrame T C →
      ∀ (μ : Measure (Mx D r S.rank)) (𝓕 : Set (Mx D r S.rank)), μ.IsAddHaarMeasure →
        IsAddFundamentalDomain (ratMx D r S.rank) 𝓕 μ →
        ∀ n ∈ NI T C, ∀ f, IsThetaFunO ψ S T f → ellI S T C μ 𝓕 (om (1, n) f) = ellI S T C μ 𝓕 f

def IsAniso (S : HSp D) : Prop :=
  ∀ x : Fin S.rank → D.host.E, x ≠ 0 → ∑ i, ∑ j, star (x i) * S.gram i j * x j ≠ 0

def ConstTermAn (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle), IsAniso S →
    Formalism.IndefR.Fin.SvNSchurO ψ S T →
    ∀ (r : ℕ) (C : Matrix (Fin T.rank) (Fin r) D.host.E), IsIsoFrame T C →
      ∀ (μ : Measure (Mx D r S.rank)) (𝓕 : Set (Mx D r S.rank)), μ.IsAddHaarMeasure →
        IsAddFundamentalDomain (ratMx D r S.rank) 𝓕 μ →
      ∀ (ν : Measure (NI T C)) (𝓕N : Set (NI T C)), ν.IsHaarMeasure → IsFundamentalDomain (NIQ T C) 𝓕N ν →
        ∃ κ : ℂ, κ ≠ 0 ∧ ∀ om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ), IsWeilDatumO ψ S T χS χT om →
          ∀ h g f, IsThetaFunO ψ S T f →
            ∫ n in 𝓕N, thetaKO om h ((n : GA D T) * g) f ∂ν = κ * ellI S T C μ 𝓕 (om (h, g) f)

end Formalism.IndefR.Eqv

end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.IpTheta
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
  IsDedekindDomain NumberField
open scoped TensorProduct ContDiff ENNReal

namespace Formalism.IndefR.Eqv

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section Basic

variable {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

theorem thetaO_add {f g : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (hg : IsThetaFunO ψ S T g) :
    IsThetaFunO ψ S T (f + g) := by

  obtain ⟨U1, hU1, h1⟩ := hf.level
  obtain ⟨U2, hU2, h2⟩ := hg.level
  constructor
  · intro γ w
    simp only [Pi.add_apply, hf.quasi, hg.quasi]
    ring
  · refine ⟨U1 ⊓ U2, ?_, fun u hu hfin => ?_⟩
    · first
      | exact hU1.inter hU2
      | simpa using hU1.inter hU2
    · have hu' : u ∈ U1 ∧ u ∈ U2 := by simpa using hu
      funext x
      have e1x := congrFun (h1 u hu'.1 hfin) x
      have e2x := congrFun (h2 u hu'.2 hfin) x
      simp only [heisO, Pi.add_apply] at e1x e2x ⊢
      rw [mul_add, e1x, e2x]
  · exact hf.cont.add hg.cont
  · intro k L hL hfin w
    exact (hf.smooth k L hL hfin w).add (hg.smooth k L hL hfin w)

theorem thetaO_smul {f : WO S T → ℂ} (c : ℂ) (hf : IsThetaFunO ψ S T f) : IsThetaFunO ψ S T (c • f) := by

  obtain ⟨U1, hU1, h1⟩ := hf.level
  constructor
  · intro γ w
    simp only [Pi.smul_apply, smul_eq_mul, hf.quasi]
    ring
  · refine ⟨U1, hU1, fun u hu hfin => ?_⟩
    funext x
    have e1x := congrFun (h1 u hu hfin) x
    simp only [heisO, Pi.smul_apply, smul_eq_mul] at e1x ⊢
    rw [mul_left_comm, e1x]
  · exact hf.cont.const_smul c
  · intro k L hL hfin w
    exact (hf.smooth k L hL hfin w).const_smul c

end Basic

section L2

variable {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

end L2

section Unit

variable {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
  {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}

theorem norm_weilRepresentation_thetaFunction_preserved (hω : IsWeilDatumO ψ S T χS χT om) {μ : Measure (WO S T)} {𝓕 : Set (WO S T)}
    (hμ : μ.IsAddHaarMeasure) (h𝓕 : IsAddFundamentalDomain (ratL T S) 𝓕 μ) (p : GA D S × GA D T)
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) : nrm2 μ 𝓕 (om p f) = nrm2 μ 𝓕 f := by
  unfold nrm2
  have hu := hω.om_unit μ 𝓕 hμ h𝓕 p f hf
  simp_rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _)] at hu
  have c1 : Continuous fun w => ‖om p f w‖ ^ 2 := (hω.om_pres p f hf).cont.norm.pow 2
  have c2 : Continuous fun w => ‖f w‖ ^ 2 := hf.cont.norm.pow 2
  rw [integral_eq_lintegral_of_nonneg_ae (f := fun w => ‖om p f w‖ ^ 2)
      (Filter.Eventually.of_forall fun _ => by positivity) c1.aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae (f := fun w => ‖f w‖ ^ 2)
      (Filter.Eventually.of_forall fun _ => by positivity) c2.aestronglyMeasurable, hu]

end Unit

section Cont

variable {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

end Cont

end Formalism.IndefR.Eqv

end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.LevelASt
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta NumberField

namespace Formalism.IndefR.Eqv

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : D7)

def LevOKBase : Prop :=
  ∀ (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ)
    (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank), Lev.IsBaseFrame V β Λ N →
    IsLevelA V (Formalism.L2.DIV.lev D.sp.cm V.gram β L) ∧
    ∃ U : Subgroup (GA D V), IsOpen (U : Set (GA D V)) ∧
      ∀ k ∈ U, k ∈ GfC V → k ∈ Lev.levG V β L ∧ Lev.levChi V β L k = 1

end Formalism.IndefR.Eqv

end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.MinfLev
section
noncomputable section

open Formalism.BasicNotions MeasureTheory

namespace Formalism.IndefR.Eqv

theorem minfDensity_ne_zero (N : ℕ) : Formalism.L2.Theta.minfDensity N ≠ 0 := by
  unfold Formalism.L2.Theta.minfDensity
  exact ENNReal.inv_ne_zero.mpr (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)

theorem minfDensity_ne_top (N : ℕ) : Formalism.L2.Theta.minfDensity N ≠ ⊤ := by
  unfold Formalism.L2.Theta.minfDensity
  exact ENNReal.inv_ne_top.mpr (pow_ne_zero _ two_ne_zero)

theorem minfExUnique_of (h : Formalism.IndefR.Leaf.MinfExistsUnique) : MinfExUnique :=
  fun p q => h p q _ (minfDensity_ne_zero (p + q)) (minfDensity_ne_top (p + q))

end Formalism.IndefR.Eqv

end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.NumFieldHosCountable
section
open scoped TensorProduct ENNReal RestrictedProduct
open MeasureTheory NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Topology Filter

noncomputable section

namespace Formalism.IndefR.Eqv.G5

section Count

variable (F : Type) [Field F] [NumberField F]

theorem numField_countable : Countable F := by
  exact Finsupp.Countable.of_moduleFinite (R := ℚ) (M := F)

theorem numField_hos_countable : Countable (HeightOneSpectrum (𝓞 F)) := by
  have := numField_countable F
  have : Countable (𝓞 F) := inferInstanceAs (Countable {x : F // x ∈ integralClosure ℤ F})
  have hs : Function.Surjective (fun s : Finset (𝓞 F) => Ideal.span (s : Set (𝓞 F))) := by
    intro I
    obtain ⟨s, hs⟩ := (IsNoetherian.noetherian I : I.FG)
    exact ⟨s, hs⟩
  have : Countable (Ideal (𝓞 F)) := hs.countable
  exact Function.Injective.countable (f := fun v : HeightOneSpectrum (𝓞 F) => v.asIdeal)
    (fun v w h => HeightOneSpectrum.ext h)

end Count

section Local

variable {F : Type} [Field F] [NumberField F]

theorem fv_secondCountable (v : HeightOneSpectrum (𝓞 F)) : SecondCountableTopology (Fv F v) := by
  have := numField_countable F
  have : TopologicalSpace.SeparableSpace (Fv F v) :=
    TopologicalSpace.SeparableSpace.of_denseRange _ (HeightOneSpectrum.denseRange_algebraMap F v)
  exact UniformSpace.secondCountable_of_separable (Fv F v)

theorem fv_locallyCompact (v : HeightOneSpectrum (𝓞 F)) : LocallyCompactSpace (Fv F v) := by
  have hc : IsCompact ((v.adicCompletionIntegers F : Set (v.adicCompletion F))) :=
    PI.IntAdCpctOpenWork.isCompact_adicCompletionIntegers v
  have ho : IsOpen ((v.adicCompletionIntegers F : Set (v.adicCompletion F))) :=
    Valued.isOpen_valuationSubring _
  exact hc.locallyCompactSpace_of_mem_nhds_of_addGroup (ho.mem_nhds (zero_mem _))

theorem compl_secondCountable (w : InfinitePlace F) : SecondCountableTopology w.Completion := by
  have := numField_countable F
  have : Countable (WithAbs w.1) := Countable.of_equiv F (WithAbs.equiv w.1).symm
  have : TopologicalSpace.SeparableSpace w.Completion :=
    TopologicalSpace.SeparableSpace.of_denseRange _ (InfinitePlace.Completion.denseRange_coe w)
  exact UniformSpace.secondCountable_of_separable _

theorem ainf_secondCountable : SecondCountableTopology (Ainf F) := by
  have := fun w : InfinitePlace F => compl_secondCountable w
  exact inferInstanceAs (SecondCountableTopology ((w : InfinitePlace F) → w.Completion))

theorem t2Space_Ainf : T2Space (Ainf F) :=
  inferInstanceAs (T2Space ((w : InfinitePlace F) → w.Completion))

end Local

section Fin

variable {F : Type} [Field F] [NumberField F]

theorem af_locallyCompact : LocallyCompactSpace (Af F) := by
  have : ∀ v : HeightOneSpectrum (𝓞 F), LocallyCompactSpace (v.adicCompletion F) :=
    fun v => fv_locallyCompact v
  have : Fact (∀ v : HeightOneSpectrum (𝓞 F),
      IsOpen ((v.adicCompletionIntegers F : Set (v.adicCompletion F)))) :=
    ⟨fun v => Valued.isOpen_valuationSubring _⟩
  exact inferInstanceAs (LocallyCompactSpace
    (Πʳ v : HeightOneSpectrum (𝓞 F), [v.adicCompletion F, v.adicCompletionIntegers F]))

theorem finite_adeles_t2 : T2Space (Af F) :=
  inferInstanceAs (T2Space
    (Πʳ v : HeightOneSpectrum (𝓞 F), [v.adicCompletion F, v.adicCompletionIntegers F]))

theorem af_secondCountable : SecondCountableTopology (Af F) := by
  have := numField_hos_countable F
  have hfv : ∀ v : HeightOneSpectrum (𝓞 F), SecondCountableTopology (v.adicCompletion F) :=
    fun v => fv_secondCountable v
  let R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F
  let A := fun v : HeightOneSpectrum (𝓞 F) => (v.adicCompletionIntegers F : Set (v.adicCompletion F))
  have hAo : ∀ v, IsOpen (A v) := fun v => Valued.isOpen_valuationSubring _
  have hS : ∀ T : Finset (HeightOneSpectrum (𝓞 F)), cofinite ≤ 𝓟 ((T : Set (HeightOneSpectrum (𝓞 F)))ᶜ) := by
    intro T
    rw [le_principal_iff, mem_cofinite, compl_compl]
    exact T.finite_toSet
  let U : Finset (HeightOneSpectrum (𝓞 F)) → Set (Πʳ v, [R v, A v]) :=
    fun T => Set.range (RestrictedProduct.inclusion R A (hS T))
  have hU : ∀ T, IsOpenEmbedding (RestrictedProduct.inclusion R A (hS T)) :=
    fun T => RestrictedProduct.isOpenEmbedding_inclusion_principal hAo (hS T)
  have hsc : ∀ T, SecondCountableTopology (U T) := by
    intro T
    have : SecondCountableTopology (Πʳ v, [R v, A v]_[𝓟 ((T : Set (HeightOneSpectrum (𝓞 F)))ᶜ)]) :=
      RestrictedProduct.isEmbedding_coe_of_principal.secondCountableTopology
    exact (hU T).isEmbedding.toHomeomorph.symm.secondCountableTopology
  have hcov : ⋃ T, U T = Set.univ := by
    refine Set.eq_univ_of_forall fun x => ?_
    have hx : Set.Finite {v | x v ∉ A v} := x.2
    refine Set.mem_iUnion.2 ⟨hx.toFinset, ?_⟩
    show x ∈ Set.range (RestrictedProduct.inclusion R A (hS hx.toFinset))
    rw [RestrictedProduct.range_inclusion]
    refine eventually_principal.2 fun v hv => ?_
    by_contra h
    exact hv (by simpa using h)
  exact @TopologicalSpace.secondCountableTopology_of_countable_cover _ _ _ _ U hsc
    (fun T => (hU T).isOpen_range) hcov

end Fin

section Tens

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem tens_homeo (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
    (hE : Module.finrank F E = 2) : Nonempty ((R ⊗[F] E) ≃ₜ (Fin 2 → R)) := by
  have : Module.Finite F E := Module.finite_of_finrank_eq_succ hE
  let b : Module.Basis (Fin 2) F E := Module.finBasisOfFinrankEq F E hE
  let L : (R ⊗[F] E) ≃ₗ[R] (Fin 2 → R) := (Algebra.TensorProduct.basis R b).equivFun
  have : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  have : ContinuousAdd (R ⊗[F] E) := IsModuleTopology.toContinuousAdd R (R ⊗[F] E)
  exact ⟨{ toEquiv := L.toEquiv
           continuous_toFun := IsModuleTopology.continuous_of_linearMap L.toLinearMap
           continuous_invFun := IsModuleTopology.continuous_of_linearMap L.symm.toLinearMap }⟩

theorem tens_ring (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
    (hE : Module.finrank F E = 2) : IsTopologicalRing (R ⊗[F] E) := by
  have : Module.Finite F E := Module.finite_of_finrank_eq_succ hE
  let b : Module.Basis (Fin 2) F E := Module.finBasisOfFinrankEq F E hE
  have : Module.Finite R (R ⊗[F] E) := Module.Finite.of_basis (Algebra.TensorProduct.basis R b)
  have : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  exact IsModuleTopology.isTopologicalRing R (R ⊗[F] E)

theorem tens_facts (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
    [T2Space R] [LocallyCompactSpace R] [SecondCountableTopology R] (hE : Module.finrank F E = 2) :
    IsTopologicalRing (R ⊗[F] E) ∧ T2Space (R ⊗[F] E) ∧ LocallyCompactSpace (R ⊗[F] E) ∧
      SecondCountableTopology (R ⊗[F] E) ∧ BorelSpace (R ⊗[F] E) := by
  obtain ⟨e⟩ := tens_homeo (E := E) R hE
  exact ⟨tens_ring R hE, e.isEmbedding.t2Space, e.isClosedEmbedding.locallyCompactSpace,
    e.isEmbedding.isInducing.secondCountableTopology, ⟨rfl⟩⟩

theorem sigR_continuous (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R]
    [IsTopologicalRing R] (σ : E →ₐ[F] E) : Continuous (sigR R σ) := by
  have : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  have : ContinuousAdd (R ⊗[F] E) := IsModuleTopology.toContinuousAdd R (R ⊗[F] E)
  have h : (sigR R σ : R ⊗[F] E → R ⊗[F] E) = LinearMap.baseChange R σ.toLinearMap := by
    funext x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul r e => simp [sigR]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  rw [h]
  exact IsModuleTopology.continuous_of_linearMap _

end Tens

section Grp

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem ha_facts (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
    [T2Space R] [LocallyCompactSpace R] [SecondCountableTopology R] (hE : Module.finrank F E = 2)
    (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) :
    IsTopologicalGroup (HA R σ J) ∧ T2Space (HA R σ J) ∧ LocallyCompactSpace (HA R σ J) ∧
      SecondCountableTopology (HA R σ J) ∧ BorelSpace (HA R σ J) := by
  obtain ⟨h1, h2, h3, h4, -⟩ := tens_facts (E := E) R hE
  have : T2Space (Matrix (Fin M) (Fin M) (R ⊗[F] E)) :=
    inferInstanceAs (T2Space (Fin M → Fin M → R ⊗[F] E))
  have : LocallyCompactSpace (Matrix (Fin M) (Fin M) (R ⊗[F] E)) :=
    inferInstanceAs (LocallyCompactSpace (Fin M → Fin M → R ⊗[F] E))
  have : SecondCountableTopology (Matrix (Fin M) (Fin M) (R ⊗[F] E)) :=
    inferInstanceAs (SecondCountableTopology (Fin M → Fin M → R ⊗[F] E))
  have : SecondCountableTopology (Matrix (Fin M) (Fin M) (R ⊗[F] E))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.isInducing.secondCountableTopology
  have : SecondCountableTopology (GL (Fin M) (R ⊗[F] E)) :=
    Units.isEmbedding_embedProduct.isInducing.secondCountableTopology
  have hcl : IsClosed (HR R σ J : Set (GL (Fin M) (R ⊗[F] E))) := by
    have hv : Continuous (fun g : GL (Fin M) (R ⊗[F] E) => (g : Matrix (Fin M) (Fin M) (R ⊗[F] E))) :=
      Units.continuous_val
    have hc : Continuous (fun g : GL (Fin M) (R ⊗[F] E) =>
        Formalism.UG.cT (sigR R σ) (g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) * JR R J *
          (g : Matrix (Fin M) (Fin M) (R ⊗[F] E))) := by
      unfold Formalism.UG.cT
      exact (((hv.matrix_map (sigR_continuous R σ)).matrix_transpose).matrix_mul
        continuous_const).matrix_mul hv
    exact isClosed_eq hc continuous_const
  have hLC : LocallyCompactSpace (HR R σ J) := hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  exact ⟨inferInstanceAs (IsTopologicalGroup (HR R σ J)), inferInstanceAs (T2Space (HR R σ J)), hLC,
    (IsInducing.subtypeVal (t := (HR R σ J : Set (GL (Fin M) (R ⊗[F] E))))).secondCountableTopology, ⟨rfl⟩⟩

end Grp

theorem af_facts (F : Type) [Field F] [NumberField F] :
    T2Space (AF F) ∧ LocallyCompactSpace (AF F) ∧ SecondCountableTopology (AF F) := by
  have : T2Space (Ainf F) := t2Space_Ainf (F := F)
  have : SecondCountableTopology (Ainf F) := ainf_secondCountable (F := F)
  have : T2Space (Af F) := finite_adeles_t2 (F := F)
  have : LocallyCompactSpace (Af F) := af_locallyCompact (F := F)
  have : SecondCountableTopology (Af F) := af_secondCountable (F := F)
  exact ⟨inferInstanceAs (T2Space (Ainf F × Af F)), inferInstanceAs (LocallyCompactSpace (Ainf F × Af F)),
    inferInstanceAs (SecondCountableTopology (Ainf F × Af F))⟩

end Formalism.IndefR.Eqv.G5
end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.SobPhase
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
  IsDedekindDomain NumberField
open scoped TensorProduct ContDiff

namespace Formalism.IndefR.Eqv

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem psi_real (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) :
    ∃ Λ : Ainf D.host.F →+ ℂ, Continuous Λ ∧ ∀ z : AF D.host.F, z.2 = 0 → ψ z = Complex.exp (Λ z.1) := by
  obtain ⟨⟨θ, hθ⟩, hall⟩ := hψ.2
  have hf := hall θ hθ
  let Λ : Ainf D.host.F →+ ℂ :=
    { toFun := fun y => 2 * Real.pi * Complex.I * ((-1 : ℤ) : ℂ) * ∑ ρ, θ ρ (y ⊗ₜ[D.host.F] (1 : D.host.E))
      map_zero' := by simp
      map_add' := fun y y' => by simp only [TensorProduct.add_tmul, map_add, Finset.sum_add_distrib]; ring }
  refine ⟨Λ, ?_, fun z hz => ?_⟩
  · show Continuous fun y => 2 * Real.pi * Complex.I * ((-1 : ℤ) : ℂ) * ∑ ρ, θ ρ (y ⊗ₜ[D.host.F] (1 : D.host.E))
    exact continuous_const.mul (continuous_finset_sum _ fun ρ _ => (hθ ρ).2)
  · have hz' : z = pairA D.host.F z.1 0 := Prod.ext rfl hz
    rw [hz']
    exact hf z.1

theorem norm_iter_exp {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (ℓ : V →L[ℝ] ℂ) :
    ∀ (i : ℕ) (u : V), ‖iteratedFDeriv ℝ i (fun v => Complex.exp (ℓ v)) u‖ ≤ ‖Complex.exp (ℓ u)‖ * ‖ℓ‖ ^ i := by
  have hp : ContDiff ℝ ∞ (fun v => Complex.exp (ℓ v)) :=
    (Complex.contDiff_exp (𝕜 := ℝ)).comp ℓ.contDiff
  intro i
  induction i with
  | zero => intro u; simp [norm_iteratedFDeriv_zero]
  | succ i ih =>
    intro u
    rw [← norm_iteratedFDeriv_fderiv]
    let T : ℂ →L[ℝ] (V →L[ℝ] ℂ) := ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℂ) ℓ
    have hT : ∀ a : ℂ, T a = a • ℓ := fun a => rfl
    have hfd : fderiv ℝ (fun v => Complex.exp (ℓ v)) = T ∘ (fun v => Complex.exp (ℓ v)) := by
      funext v
      rw [Function.comp_apply, hT, ((ℓ.hasFDerivAt (x := v)).cexp).fderiv]
    rw [hfd]
    refine (T.norm_iteratedFDeriv_comp_left hp.contDiffAt (natCast_lt_inf' i).le).trans ?_
    have hTn : ‖T‖ ≤ ‖ℓ‖ := by
      refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun a => ?_
      rw [hT, norm_smul, mul_comm]
    calc ‖T‖ * ‖iteratedFDeriv ℝ i (fun v => Complex.exp (ℓ v)) u‖
        ≤ ‖ℓ‖ * (‖Complex.exp (ℓ u)‖ * ‖ℓ‖ ^ i) :=
          mul_le_mul hTn (ih u) (norm_nonneg _) (norm_nonneg _)
      _ = ‖Complex.exp (ℓ u)‖ * ‖ℓ‖ ^ (i + 1) := by ring

end Formalism.IndefR.Eqv

end
end

