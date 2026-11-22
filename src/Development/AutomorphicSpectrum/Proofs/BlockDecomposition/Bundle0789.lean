import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.InfinitesimalCharacterGlue
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.Bundle0012
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.Bundle0014
import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0209
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0116
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0129
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ConclusionFinite
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InfCharOfCharOfHasInfQ
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0024
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivOfMapEq
import GroundTheory.PAdicHodge.AInfGalois
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0539
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0786
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0378
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0408
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.Bundle0001
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0019
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHaarMeasure
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0043
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0017
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BinaryMassMeans.MeanVal
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0787
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0125
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1416
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1312
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0575
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0773

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinStable
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.LimV

section Abstract

variable {A B : Type}

def prodSpan (U₁ : Submodule ℂ (A → ℂ)) (U₂ : Submodule ℂ (B → ℂ)) : Submodule ℂ (A × B → ℂ) :=
  Submodule.span ℂ {F | ∃ a ∈ U₁, ∃ b ∈ U₂, F = fun x => a x.1 * b x.2}

end Abstract

section Lin

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {N r s : ℕ}

variable (E) in

abbrev KO (n : ℕ) : Subgroup (GL (Fin n) (Af E)) := GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E n

def typeF (K : Subgroup (GL (Fin N) (Af E))) (W : Submodule ℂ (Kinf E N → ℂ)) : Submodule ℂ (GA E N → ℂ) where
  carrier := {f | (∀ u ∈ K, ∀ g, f (g * finGL E N u) = f g) ∧
    ∀ g, (fun k : Kinf E N => f (g * infGL E N (Unitary.toUnits k))) ∈ W}
  add_mem' := fun {f f'} h h' => ⟨fun u hu g => by simp only [Pi.add_apply, h.1 u hu g, h'.1 u hu g],
    fun g => W.add_mem (h.2 g) (h'.2 g)⟩
  zero_mem' := ⟨fun _ _ _ => rfl, fun _ => W.zero_mem⟩
  smul_mem' := fun c f h => ⟨fun u hu g => by simp only [Pi.smul_apply, h.1 u hu g],
    fun g => W.smul_mem c (h.2 g)⟩

def typed (U : Submodule ℂ (Sm E N)) (K : Subgroup (GL (Fin N) (Af E))) (W : Submodule ℂ (Kinf E N → ℂ)) :
    Submodule ℂ (Sm E N) :=
  U ⊓ (typeF K W).comap (Sm E N).subtype

structure FlatFn (e : GA E N → ℂ) : Prop where
  ne : ∀ x, e x ≠ 0
  rinv : ∀ x (k : Kinf E N), ∀ c ∈ KO E N, e (x * cf N k c) = e x
  sm : e ∈ Sm E N

def Carries (e : GA E N → ℂ) (U U' : Submodule ℂ (Sm E N)) : Prop :=
  ∀ φ ∈ U, ∃ φ' ∈ U', ∀ x, φ'.1 x = e x * φ.1 x

def FinStable (U : Submodule ℂ (Sm E N)) : Prop := ∀ (g : GL (Fin N) (Af E)), ∀ φ ∈ U, act (.fin g) φ ∈ U

def indSpan (U₁ : Submodule ℂ (Sm E r)) (U₂ : Submodule ℂ (Sm E s)) : Submodule ℂ (Sm E (r + s)) :=
  Submodule.span ℂ {φ | MemInd2 U₁ U₂ φ}

theorem exists_iw (x : GA E (r + s)) : ∃ (u : BlockIx (r + s) r → Ad E) (m : GA E r × GA E s) (k : Kinf E (r + s))
    (c : GL (Fin (r + s)) (Af E)), c ∈ KO E (r + s) ∧ x = unip u * lev (Ad E) r s m * cf (r + s) k c := by
  obtain ⟨b, hb, k, hy⟩ := GlobalTheory.IwasawaAdelic.exists_upper_mul_unitary_inf E (r + s)
    (GeneralLinearGroup.map (pInf E) x)
  have hb' : (((b⁻¹ : GL (Fin (r + s)) (Cinf E))) : Matrix (Fin (r + s)) (Fin (r + s)) (Cinf E)).BlockTriangular id := by
    letI : Invertible (b : Matrix (Fin (r + s)) (Fin (r + s)) (Cinf E)) := Units.invertible b
    rw [Matrix.coe_units_inv]
    exact Matrix.blockTriangular_inv_of_blockTriangular hb
  obtain ⟨xi, mi, hbi⟩ := IwaFin.exists_unip_mul_lev r s b
    (fun i j hi hj => hb (show j < i from Fin.lt_def.2 (lt_of_lt_of_le hj hi)))
    (fun i j hi hj => hb' (show j < i from Fin.lt_def.2 (lt_of_lt_of_le hj hi)))
  obtain ⟨xf, mf, c, hc, hf⟩ := IwaFin.exists_unip_lev_integral E r s (GeneralLinearGroup.map (pFin E) x)
  have e1 : ∀ p, pInf E (sInf E (xi p) + sFin E (xf p)) = xi p := fun p => by
    rw [map_add, show pInf E (sInf E (xi p)) = xi p from (infEq E).symm_apply_apply _,
      show pInf E (sFin E (xf p)) = 0 from map_zero (infEq E).symm, add_zero]
  have e2 : ∀ p, pFin E (sInf E (xi p) + sFin E (xf p)) = xf p := fun p => by
    rw [map_add, show pFin E (sInf E (xi p)) = 0 from rfl, show pFin E (sFin E (xf p)) = xf p from rfl, zero_add]
  refine ⟨fun p => sInf E (xi p) + sFin E (xf p),
    (infGL E r mi.1 * finGL E r mf.1, infGL E s mi.2 * finGL E s mf.2), k, c, hc, ga_ext ?_ ?_⟩
  · simp only [cf, map_mul, IwaAd.map_unip, IwaAd.map_lev, e1, pInf_infGL, pInf_finGL, mul_one, one_mul]
    rw [hy, hbi]
  · simp only [cf, map_mul, IwaAd.map_unip, IwaAd.map_lev, e2, pFin_infGL, pFin_finGL, mul_one, one_mul]
    rw [hf]

def leviOf (x : GA E (r + s)) : GA E r × GA E s := (exists_iw x).choose_spec.choose

def nodeFn (e₁ : GA E r → ℂ) (e₂ : GA E s → ℂ) (x : GA E (r + s)) : ℂ := e₁ (leviOf x).1 * e₂ (leviOf x).2

def absFn (N : ℕ) (w : ℂ) (x : GA E N) : ℂ := (chiDet N (GlobalTheory.CuspRep.Model.absC E w) x : ℂˣ)

end Lin

section Pair

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

def typeHF (K₁ : Subgroup (GL (Fin a) (Af E))) (K₂ : Subgroup (GL (Fin b) (Af E)))
    (W₁ : Submodule ℂ (Kinf E a → ℂ)) (W₂ : Submodule ℂ (Kinf E b → ℂ)) : Submodule ℂ (H E a b → ℂ) where
  carrier := {F | TypeH K₁ K₂ W₁ W₂ F}
  add_mem' := fun {F F'} h h' => ⟨fun u₁ hu₁ u₂ hu₂ x => by
      simp only [Pi.add_apply, h.1 u₁ hu₁ u₂ hu₂ x, h'.1 u₁ hu₁ u₂ hu₂ x],
    fun x => Submodule.add_mem _ (h.2 x) (h'.2 x)⟩
  zero_mem' := ⟨fun _ _ _ _ _ => rfl, fun _ => Submodule.zero_mem _⟩
  smul_mem' := fun c F h => ⟨fun u₁ hu₁ u₂ hu₂ x => by simp only [Pi.smul_apply, h.1 u₁ hu₁ u₂ hu₂ x],
    fun x => Submodule.smul_mem _ c (h.2 x)⟩

end Pair

end GlobalTheory.CompanionTheory.LimV

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaloisRepresentationAdmitted
section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.HeckeAlg

open GlobalTheory.CuspRep GlobalTheory.CuspRep.InfType

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

theorem dchi_atEmb (χ : HChar E) (τ : E →+* ℂ) (z : ℂ) :
    dchi χ (atEmb τ z) = expo χ τ * z + expo χ (ComplexEmbedding.conjugate τ) * starRingEnd ℂ z := by
  have e : atEmb τ (-Complex.I) = -atEmb τ Complex.I := by
    rw [atEmb_eq]; simp
  rw [atEmb_eq, map_add, map_smul, map_smul]
  simp only [expo, atEmb_conj, map_one, Complex.conj_I, e, map_neg, Complex.real_smul]
  conv_rhs => rw [← Complex.re_add_im z]
  simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
  linear_combination (z.im * dchi χ (atEmb τ Complex.I)) * Complex.I_mul_I

theorem dchi_eq_sum (χ : HChar E) (z : Cinf E) : dchi χ z = ∑ φ : E →+* ℂ, expo χ φ * coord φ z := by
  classical
  have hz : z = ∑ w : InfinitePlace E, atEmb w.embedding (z w) := by
    funext v
    rw [Finset.sum_apply, Finset.sum_eq_single v]
    · simp [atEmb, InfinitePlace.mk_embedding]
    · intro b _ hb
      simp [atEmb, InfinitePlace.mk_embedding, Pi.single_eq_of_ne hb.symm]
    · simp
  conv_lhs => rw [hz]
  conv_rhs => rw [hz]
  rw [map_sum]
  simp only [map_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [dchi_atEmb]
  simp only [coord_atEmb', mul_add, Finset.sum_add_distrib, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

end GlobalTheory.CompanionTheory.HeckeAlg

namespace GlobalTheory.CompanionTheory.RankOneGal

open GlobalTheory.CuspRep GlobalTheory.CuspRep.InfType GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.TripleGal GlobalTheory.Pst GlobalTheory.GalOfCusp
open Formalism.BasicNotions.Loc Neutral.B1

section Char

variable {E Ω : Type} [Field E] [NumberField E] [IsTotallyComplex E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {l : ℕ} [Fact l.Prime]

end Char

end GlobalTheory.CompanionTheory.RankOneGal

namespace GlobalTheory.CompanionTheory.RankOneGal

open GlobalTheory.CuspRep GlobalTheory.CuspRep.InfType GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.TripleGal GlobalTheory.Pst GlobalTheory.GalOfCusp
open Formalism.BasicNotions.Loc

end GlobalTheory.CompanionTheory.RankOneGal

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GlobalVolumeRankOneProduct
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.FreeLocal

open Set

section Gen

variable {V X Y : Type} [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V] [T2Space V]
  [LocallyCompactSpace V] [SecondCountableTopology V] [TopologicalSpace X] [MeasurableSpace X]
  {μ : Measure V} {ν : Measure X} {f : V → Y} {ι : X → Y} {U : Set V} {fib : X → Measure V}

theorem fib_lt_top (h : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι U ν univ fib) (hU : IsOpen U) (b : X)
    {K : Set V} (hK : IsCompact K) (hKU : K ⊆ U) : fib b K < ⊤ := by
  obtain ⟨g, hg1, hgc, hgs, -⟩ := exists_continuousMap_one_of_isCompact_subset_isOpen hK hU hKU
  have hI := (h.2.2 g g.continuous hgc hgs).1 b (mem_univ b)
  calc fib b K = ∫⁻ v, K.indicator 1 v ∂(fib b) := (lintegral_indicator_one hK.measurableSet).symm
    _ ≤ ∫⁻ v, ENNReal.ofReal (g v) ∂(fib b) := lintegral_mono fun v => by
        by_cases hv : v ∈ K
        · simp [indicator_of_mem hv, hg1 hv]
        · simp [indicator_of_notMem hv]
    _ < ⊤ := hI.lintegral_lt_top

theorem sigmaFinite_fib (h : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι U ν univ fib) (hU : IsOpen U)
    (b : X) : SigmaFinite (fib b) := by
  have hc : fib b Uᶜ = 0 :=
    measure_mono_null (compl_subset_compl.2 inter_subset_right) (h.1 b)
  haveI : LocallyCompactSpace U := hU.locallyCompactSpace
  have hσ : IsSigmaCompact U := isSigmaCompact_iff_sigmaCompactSpace.2 inferInstance
  obtain ⟨K, hKc, hKU⟩ := hσ
  have hsub : ∀ n, K n ⊆ U := fun n => hKU ▸ subset_iUnion K n
  refine Measure.FiniteSpanningSetsIn.sigmaFinite
    (μ := fib b) (C := univ)
    { set := fun n => K n ∪ Uᶜ, set_mem := fun _ => mem_univ _, finite := fun n => ?_, spanning := ?_ }
  · exact (measure_union_le _ _).trans_lt
      (ENNReal.add_lt_top.2 ⟨fib_lt_top h hU b (hKc n) (hsub n), by simp [hc]⟩)
  · refine eq_univ_of_forall fun x => ?_
    by_cases hx : x ∈ U
    · rw [← hKU] at hx
      obtain ⟨n, hn⟩ := mem_iUnion.1 hx
      exact mem_iUnion.2 ⟨n, Or.inl hn⟩
    · exact mem_iUnion.2 ⟨0, Or.inr hx⟩

end Gen

section Rat

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem gramR_ratTup_eq (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {M n : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (X : Fin n → Fin M → E) :
    gramR R σ J (ratTup (F := F) R X) = (gramE σ J X).map (inclR R) := by
  ext i j
  simp [gramR, gramE, hE, hR, hform, ratTup, JR, sigR, inclR, Matrix.map_apply, mul_assoc]

theorem ratTup_free (R : Type) [CommRing R] [Algebra F R] {M : ℕ} (X : Fin 1 → Fin M → E)
    (hX : LinearIndependent E X) : LinearIndependent (R ⊗[F] E) (ratTup (F := F) R X) := by
  have h0 : X 0 ≠ 0 := hX.ne_zero 0
  obtain ⟨i, hi⟩ := Function.ne_iff.1 h0
  have hu : IsUnit (inclR (F := F) R (X 0 i)) := (isUnit_iff_ne_zero.2 hi).map _
  refine Fintype.linearIndependent_iff.2 fun g hg k => ?_
  have hk : k = 0 := Subsingleton.elim _ _
  subst hk
  have h1 := congrFun hg i
  simp only [Fin.sum_univ_one, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, ratTup] at h1
  exact (hu.mul_left_eq_zero).1 h1

end Rat

section Arch

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem arch_lb (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M a : ℕ) (J : Matrix (Fin M) (Fin M) E)
    (hJ : IsHermND σ J) (μ : Measure (Fin a → Fin M → Ainf F ⊗[F] E))
    (ν : Measure (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HermR (Ainf F) σ a)) (hμ : μ.IsAddHaarMeasure) (hν : ν.IsAddHaarMeasure)
    (x : Fin a → Fin M → Ainf F ⊗[F] E) (S0 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HermR (Ainf F) σ a)
    (hx : LinearIndependent (Ainf F ⊗[F] E) x)
    (hxS : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.gramR (Ainf F) σ J x = (S0 : Matrix (Fin a) (Fin a) (Ainf F ⊗[F] E)))
    (W : Set (Fin a → Fin M → Ainf F ⊗[F] E)) (hW : IsOpen W) (hxW : x ∈ W) :
    ∃ c : ℝ≥0∞, 0 < c ∧ c ≠ ⊤ ∧ ∃ N ∈ 𝓝 S0, ∀ S ⊆ N, MeasurableSet S →
      c * ν S ≤ μ ((Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.gramR (Ainf F) σ J) ⁻¹' (Subtype.val '' S) ∩ W) := by
  obtain ⟨n, m, eV, eH, f', hV, hH, hf', hG, hsurj⟩ :=
    GlobalTheory.ArchGramFibre.exists_submersion_coords F E σ hCM M a J hJ
  have : BorelSpace (Ainf F ⊗[F] E) := ⟨rfl⟩
  have : BorelSpace (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HermR (Ainf F) σ a) := ⟨rfl⟩
  have : ContinuousAdd (Fin a → Fin M → Ainf F ⊗[F] E) := ⟨by
    have e : (fun p : (Fin a → Fin M → Ainf F ⊗[F] E) × (Fin a → Fin M → Ainf F ⊗[F] E) =>
        p.1 + p.2) = fun p => eV.symm (eV p.1 + eV p.2) := by
      funext p; rw [← hV, Homeomorph.symm_apply_apply]
    rw [e]; fun_prop⟩
  have : ContinuousAdd (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HermR (Ainf F) σ a) := ⟨by
    have e : (fun p : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HermR (Ainf F) σ a × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HermR (Ainf F) σ a => p.1 + p.2) =
        fun p => eH.symm (eH p.1 + eH p.2) := by
      funext p; rw [← hH, Homeomorph.symm_apply_apply]
    rw [e]; fun_prop⟩
  have hμ' : (μ.map eV).IsAddHaarMeasure :=
    Measure.isAddHaarMeasure_map μ (AddMonoidHom.mk' eV hV) eV.continuous eV.surjective
      (eV.map_cocompact).le
  have hν' : (ν.map eH).IsAddHaarMeasure :=
    Measure.isAddHaarMeasure_map ν (AddMonoidHom.mk' eH hH) eH.continuous eH.surjective
      (eH.map_cocompact).le
  have hW' : IsOpen (eV.symm ⁻¹' W) := hW.preimage eV.symm.continuous
  have hx0W : eV x ∈ eV.symm ⁻¹' W := by
    show eV.symm (eV x) ∈ W
    rw [Homeomorph.symm_apply_apply]
    exact hxW
  obtain ⟨c, hc0, hct, N', hN', hlb'⟩ :=
    PI.VolStabS.submLB_holds n m _ _ hμ' hν' f' hf' (eV x) (hsurj x hx) _ hW' hx0W
  have hfx0 : f' (eV x) = eH S0 := by
    have h1 : eH.symm (f' (eV x)) = S0 := Subtype.ext ((hG x).trans hxS)
    rw [← h1, Homeomorph.apply_symm_apply]
  have hN : eH ⁻¹' N' ∈ 𝓝 S0 := eH.continuous.continuousAt.preimage_mem_nhds (hfx0 ▸ hN')
  refine ⟨c, hc0, hct, _, hN, fun S hSN hSm => ?_⟩
  have hS'm : MeasurableSet (eH.symm ⁻¹' S) := eH.symm.continuous.measurable hSm
  have hS'N : eH.symm ⁻¹' S ⊆ N' := fun z hz => by
    have := hSN hz
    rwa [mem_preimage, Homeomorph.apply_symm_apply] at this
  have h := hlb' _ hS'N hS'm
  rw [show (ν.map eH) = ν.map eH.toMeasurableEquiv from rfl,
    show (μ.map eV) = μ.map eV.toMeasurableEquiv from rfl,
    MeasurableEquiv.map_apply, MeasurableEquiv.map_apply] at h
  have e1 : eH.toMeasurableEquiv ⁻¹' (eH.symm ⁻¹' S) = S := by
    ext z
    simp
  have e2 : eV.toMeasurableEquiv ⁻¹' (f' ⁻¹' (eH.symm ⁻¹' S) ∩ eV.symm ⁻¹' W) =
      (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.gramR (Ainf F) σ J) ⁻¹' (Subtype.val '' S) ∩ W := by
    ext X
    simp only [mem_preimage, mem_inter_iff, Homeomorph.toMeasurableEquiv_coe,
      Homeomorph.symm_apply_apply, mem_image]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨⟨_, h1, hG X⟩, h2⟩
    · rintro ⟨⟨s, hs, hsX⟩, h2⟩
      refine ⟨?_, h2⟩
      have : s = eH.symm (f' (eV X)) := Subtype.ext (hsX.trans (hG X).symm)
      rw [← this]
      exact hs
  rw [e1, e2] at h
  exact h

end Arch

section Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem sigmaFinite_free (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R]
    (hR : IsLocR R) (n : ℕ) (μ : Measure (Fin n → Fin M → R ⊗[F] E)) (ν : Measure (HermR R σ n))
    (m : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)) (hm : IsGramFibFree R σ J n μ ν m)
    (S : HermR R σ n) : SigmaFinite (m S) := by
  have hO := GlobalTheory.CompanionTheory.WeilSiegel.FreeOpen.isOpen_free F E σ hCM R hR n M
  obtain ⟨h1, h2, h3, h4, -⟩ := hR
  obtain ⟨t1, t2, t3, t4, -, -, -, t8, -, -⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM R
  haveI := t2
  haveI := t3
  haveI := t4
  haveI := t8 n M
  exact sigmaFinite_fib hm hO S

theorem free_fibre_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 3 ≤ M → ∀ (h₀ : ∀ a b : Fin 1, σ ((0 : Matrix (Fin 1) (Fin 1) E) b a) = (0 : Matrix (Fin 1) (Fin 1) E) a b), ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (laminf : Measure (Ainf F)) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), IsStdInf laminf → (∀ v, IsStdV v (lam v)) → ∀ (minf : HermR (Ainf F) σ 1 → Measure (Fin 1 → Fin M → Ainf F ⊗[F] E)), IsGramFibFree (Ainf F) σ J 1 (coordW (Ainf F) b laminf 1 M) (coordHerm (Ainf F) σ b laminf 1) minf → ∀ (m : ∀ v : HeightOneSpectrum (𝓞 F), HermR (Fv F v) σ 1 → Measure (Fin 1 → Fin M → Fv F v ⊗[F] E)), (∀ v, IsGramFibFree (Fv F v) σ J 1 (coordW (Fv F v) b (lam v) 1 M) (coordHerm (Fv F v) σ b (lam v) 1) (m v)) → SigmaFinite (minf (hermOf (Ainf F) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀)) ∧ (∀ v, SigmaFinite (m v (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀))) ∧ ((framesE σ J (0 : Matrix (Fin 1) (Fin 1) E)).Nonempty → minf (hermOf (Ainf F) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀) ≠ 0 ∧ ∀ v, m v (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀) ≠ 0) := by
  intro F E _ _ _ _ _ σ hCM M J hJ _ h₀ d b laminf lam hinf hlam minf hminf m hm
  have hLi : IsLocR (Ainf F) := GlobalTheory.CompanionTheory.SW.isLocR_Ainf F hCM.1
  have hLv : ∀ v, IsLocR (Fv F v) := GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F
  haveI hBi : BorelSpace (Ainf F) := ⟨rfl⟩
  haveI hBv : ∀ v, BorelSpace (Fv F v) := fun v => ⟨rfl⟩
  refine ⟨sigmaFinite_free σ hCM J (Ainf F) hLi 1 _ _ minf hminf _,
    fun v => sigmaFinite_free σ hCM J (Fv F v) (hLv v) 1 _ _ (m v) (hm v) _, ?_⟩
  rintro ⟨X₀, hX₀, hg⟩
  have hgram : ∀ (R : Type) [CommRing R] [Algebra F R],
      gramR R σ J (ratTup (F := F) R X₀) = (hermOf R σ (0 : Matrix (Fin 1) (Fin 1) E) h₀ :
        Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) := fun R _ _ => by
    rw [gramR_ratTup_eq, hg]
    rfl
  constructor
  · obtain ⟨h1, h2, h3, h4, hA, hRed, hU, -⟩ := hLi
    haveI := h1
    haveI := h2
    haveI := h3
    haveI := h4
    haveI := hA
    haveI := hRed
    haveI : FiniteDimensional F E := Module.Finite.of_basis b
    have hUo : IsOpen {r : Ainf F | IsUnit r} := by
      have := hU.isOpen_range
      convert this using 1
      ext r
      simp [IsUnit]
    have hH := GlobalTheory.CompanionTheory.SW.coord_measures_haar F E σ hCM (Ainf F) d b laminf hinf.1
    haveI := hH.2.1 1 M
    let ν' : Measure (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HermR (Ainf F) σ 1) := coordHerm (Ainf F) σ b laminf 1
    haveI : ν'.IsAddHaarMeasure := hH.2.2 1
    exact (GlobalTheory.LocalFibreNonzero.fib_tens σ (PI.VolStabS.sigma_invol σ hCM.2.2.2) J hJ.1 1 (Ainf F)
      hUo (GlobalTheory.CompanionTheory.WeilSiegel.FreeOpen.lip_of_artinian_reduced (Ainf F)) _ ν' minf hminf
      (ratTup (F := F) (Ainf F) X₀) _ (ratTup_free (Ainf F) X₀ hX₀)
      (fun W hW hxW => arch_lb F E σ hCM M 1 J hJ _ _ (hH.2.1 1 M) (hH.2.2 1) _ _
        (ratTup_free (Ainf F) X₀ hX₀) (hgram (Ainf F)) W hW hxW)).1
  · intro v
    obtain ⟨h1, h2, h3, h4, -⟩ := hLv v
    haveI := h1
    haveI := h2
    haveI := h3
    haveI := h4
    have hH := GlobalTheory.CompanionTheory.SW.coord_measures_haar F E σ hCM (Fv F v) d b (lam v) (hlam v).1
    exact (GlobalTheory.LocalFibreNonzero.fibre_nonzero_finite F E σ hCM M J hJ v 1 _ _ (hH.2.1 1 M) (hH.2.2 1)
      (m v) (hm v) (ratTup (F := F) (Fv F v) X₀) _ (ratTup_free (Fv F v) X₀ hX₀) (hgram (Fv F v))).1

end Main

end GlobalTheory.CompanionTheory.WeilSiegel.FreeLocal
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HassePrinciple
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology PositivityTheory.Rg.Mass
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.MassHasse

theorem hasse : Hasse := by
  intro F E _ _ _ _ _ σ J d b li lam μ 𝓕 mi m hCM hJ _ _ _ _ _ hmi _ β hβ hne
  by_contra hS
  have hnot : ∀ x : Fin 2 → E, hE σ J x x ≠ algebraMap F E β := fun x hx =>
    hS ⟨fun _ => x, by
      funext a c
      simpa [gramE] using hx⟩
  obtain ⟨τ, c, hc0, hc, hw⟩ := Plane.exists_place hCM J hJ β hβ hnot
  obtain ⟨Φ, hΦ, hΦσ⟩ := Plane.exists_hom hCM τ
  have hscal : algebraMap F (Ainf F) β ⊗ₜ[F] (1 : E) = inclR (Ainf F) (algebraMap F E β) := by
    simp only [inclR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.includeRight_apply,
      Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  have hempty : (gramR (Ainf F) σ J ⁻¹' {(hermScal (Ainf F) σ (algebraMap F (Ainf F) β)).1} ∩
      {X | IsUnit (gramR (Ainf F) σ J X).det}) = ∅ := by
    ext Y
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_ofPred_eq,
      Set.mem_empty_iff_false, iff_false, not_and]
    intro hY _
    have h00 : hR (Ainf F) σ J (Y 0) (Y 0) = inclR (Ainf F) (algebraMap F E β) :=
      (congrFun (congrFun hY 0) 0).trans hscal
    have h1 := congrArg Φ h00
    rw [hΦ, hc] at h1
    let w : Fin 2 → ℂ := fun i => Φ (Y 0 i)
    have key : Φ (hR (Ainf F) σ J (Y 0) (Y 0)) = star w ⬝ᵥ (J.map τ *ᵥ w) := by
      simp only [hR, hform, JR, map_sum, map_mul, hΦσ, Matrix.map_apply, hΦ, dotProduct, Matrix.mulVec,
        Pi.star_apply, Finset.mul_sum, w, mul_assoc]
    have h2 := hw w
    rw [← key, h1, Complex.ofReal_re] at h2
    exact absurd (mul_self_pos.2 hc0) (not_lt.2 h2)
  apply hne
  have h1 := hmi.1 (hermScal (Ainf F) σ (algebraMap F (Ainf F) β))
  rw [hempty, Set.compl_empty] at h1
  exact Measure.measure_univ_eq_zero.1 h1

end GlobalTheory.CompanionTheory.SW.MassHasse
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LieSkewAdjointBis
section
open scoped Classical InnerProductSpace ComplexConjugate
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.AutomorphicL2Unitary GlobalTheory.SqIntGL
open scoped GlobalTheory.CuspRep.CuspidalL2GL

namespace GlobalTheory.CompanionTheory.FinDiscOrth

theorem lie_skew_l2Map : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (μ : Measure (GA E N)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (X : Lie E N) (x y : Sm E N), Continuous x.1 → Continuous y.1 → Continuous (lie E N X x).1 → Continuous (lie E N X y).1 → x ∈ squareIntegrableSmoothSubmoduleGL μ → y ∈ squareIntegrableSmoothSubmoduleGL μ → lie E N X x ∈ squareIntegrableSmoothSubmoduleGL μ → lie E N X y ∈ squareIntegrableSmoothSubmoduleGL μ → ⟪l2Map μ x, l2Map μ (lie E N X y)⟫_ℂ = -⟪l2Map μ (lie E N X x), l2Map μ y⟫_ℂ := by
  intro E _ _ _ N μ _ _ X x y cx cy cXx cXy hx hy hXx hXy
  rw [l2Map_apply μ hx, l2Map_apply μ hy, l2Map_apply μ hXx, l2Map_apply μ hXy,
    GlobalTheory.CompanionTheory.LieSkew.lie_skew E N μ X x y ((mem_l2Sub μ).1 hx) ((mem_l2Sub μ).1 hy)
      ((mem_l2Sub μ).1 hXx) ((mem_l2Sub μ).1 hXy) cx cy cXx cXy, neg_neg]

end GlobalTheory.CompanionTheory.FinDiscOrth
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalHaarGLImageScalingStatement
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.IwaAd PositivityTheory.PfSWUS GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.MM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_haar_GL_image_scaling : ∀ (D : D7) (n : ℕ) (a d : GL (Fin n) (AE D)) (b : hermA D n) (k₃ k₄ : Mx D n n) (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers D.host.F)) (lam : Measure (Fin n → HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v ⊗[D.host.F] D.host.E)), lam.IsAddHaarMeasure → (∀ (g : GL (Fin n) (HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v ⊗[D.host.F] D.host.E)) (S : Set (Fin n → HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v ⊗[D.host.F] D.host.E)), lam ((fun x => g.1.mulVec x) '' S) = (absEv D.host.F D.host.E v (Matrix.GeneralLinearGroup.det g) : ℝ≥0∞) * lam S) → PositivityTheory.SiegelWeilFormula.Gen.IsCO (latAt a.1 v) → d.1 * k₃ = -1 → d.1 * k₄ = -(pull a b).1 → {x | ∃ y ∈ (latLoc D.host.F (stdLattice D.host.E n) v), ∃ y' ∈ (latLoc D.host.F (stdLattice D.host.E n) v), x = (PositivityTheory.SiegelWeilFormula.Gen.matV v k₃).mulVec y + (PositivityTheory.SiegelWeilFormula.Gen.matV v k₄).mulVec y'} = ((latLoc D.host.F (stdLattice D.host.E n) v) : Set (Fin n → HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v ⊗[D.host.F] D.host.E)) → PositivityTheory.SiegelWeilFormula.Gen.nu2 lam (latAt a.1 v) (latAt (adj (a⁻¹).1) v) (PositivityTheory.SiegelWeilFormula.Gen.matV v b.1) = (absEv D.host.F D.host.E v (unitFin D.host.F D.host.E v (Matrix.GeneralLinearGroup.det d)) : ℝ) := by
  first | exact @GlobalTheory.CompanionTheory.MM.NuFin.local_haar_GL_image_eq_absValue_det | exact GlobalTheory.CompanionTheory.MM.NuFin.local_haar_GL_image_eq_absValue_det | (intros; apply GlobalTheory.CompanionTheory.MM.NuFin.local_haar_GL_image_eq_absValue_det <;> assumption)
end
end

