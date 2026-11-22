import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0327
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0716
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0127
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0719
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0717
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0028
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0718
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0709
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0706
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0026
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0051
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0022
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0663
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0140
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWildInertiaCyclotomicElement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0057
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0612
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0098
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0713

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InverseLocalArtinContinuousOnInertia
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.ArtinInvCont

theorem absoluteGaloisAbelianization_t2Space (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] :
    T2Space (GlobalTheory.HeckeGal.Gab E Ω) := by
  unfold GlobalTheory.HeckeGal.Gab TopologicalAbelianization
  haveI : IsClosed (((commutator (G E Ω)).topologicalClosure : Subgroup (G E Ω)) : Set (G E Ω)) :=
    Subgroup.isClosed_topologicalClosure _
  infer_instance

theorem continuous_localIdele' (E : Type) [Field E] [NumberField E] (v : HeightOneSpectrum (𝓞 E)) :
    Continuous (Neutral.B1.localIdele E v) := by
  classical
  have hle : (Filter.cofinite : Filter (HeightOneSpectrum (𝓞 E))) ≤ Filter.principal ({v}ᶜ : Set _) := by
    rw [Filter.le_principal_iff]
    exact (Set.finite_singleton v).compl_mem_cofinite
  let f : v.adicCompletion E → RestrictedProduct (fun w : HeightOneSpectrum (𝓞 E) => w.adicCompletion E)
      (fun w => (w.adicCompletionIntegers E : Set (w.adicCompletion E))) (Filter.principal ({v}ᶜ : Set _)) :=
    fun x => ⟨Pi.mulSingle v x, by
      rw [Filter.eventually_principal]
      intro w hw
      have h' : w ≠ v := hw
      rw [Pi.mulSingle_eq_of_ne h']
      exact one_mem _⟩
  have hf : Continuous f := by
    rw [RestrictedProduct.continuous_rng_of_principal]
    exact continuous_mulSingle (A := fun w : HeightOneSpectrum (𝓞 E) => w.adicCompletion E) v
  have hs : Continuous (Neutral.B1.finiteSingle E v) := (RestrictedProduct.continuous_inclusion hle).comp hf
  apply Continuous.units_map
  exact Continuous.prodMk continuous_const hs

theorem isCompact_valOne (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) :
    IsCompact {x : (w.adicCompletion E)ˣ | Valued.v (x : w.adicCompletion E) = 1} := by
  rw [Units.isEmbedding_val₀.isInducing.isCompact_iff]
  have e : (Units.val '' {x : (w.adicCompletion E)ˣ | Valued.v (x : w.adicCompletion E) = 1}) =
      {y : w.adicCompletion E | Valued.v y = 1} := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hy
      have h0 : y ≠ 0 := by
        rintro rfl
        simp at hy
      exact ⟨Units.mk0 y h0, hy, rfl⟩
  rw [e]
  have hK : IsCompact (w.adicCompletionIntegers E : Set (w.adicCompletion E)) :=
    isCompact_iff_compactSpace.2 (GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers E w)
  refine hK.of_isClosed_subset ?_ ?_
  · have h1 : IsClosed {y : w.adicCompletion E | Valued.v y ≤ 1} := by
      have : {y : w.adicCompletion E | Valued.v y ≤ 1} = (w.adicCompletionIntegers E : Set (w.adicCompletion E)) := by
        ext y
        exact (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 E) E w).symm
      rw [this]
      exact hK.isClosed
    have h2 : IsOpen {y : w.adicCompletion E | Valued.v y < 1} := by
      rw [isOpen_iff_mem_nhds]
      intro y hy
      rw [Valued.mem_nhds]
      refine ⟨1, fun z hz => ?_⟩
      have hz' : Valued.v (z - y) < 1 := by simpa using hz
      have : z = (z - y) + y := by ring
      show Valued.v z < 1
      rw [this]
      exact Valuation.map_add_lt _ hz' hy
    have e2 : {y : w.adicCompletion E | Valued.v y = 1} =
        {y : w.adicCompletion E | Valued.v y ≤ 1} ∩ {y : w.adicCompletion E | Valued.v y < 1}ᶜ := by
      ext y
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_compl_iff, not_lt]
      exact ⟨fun h => ⟨h.le, h.ge⟩, fun h => le_antisymm h.1 h.2⟩
    rw [e2]
    exact h1.inter h2.isClosed_compl
  · intro y hy
    exact (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 E) E w).2 (le_of_eq hy)

theorem continuous_inv_on_ine : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (art : Neutral.B1.Ideles E →* GlobalTheory.HeckeGal.Gab E Ω) (a : Weil h →* (w.adicCompletion E)ˣ), GlobalTheory.HeckeGal.IsGlobalArtin art → (∀ σ, ord (w.adicCompletion E) (a σ) = -deg σ) → (∀ σ : Weil h, art (Neutral.B1.localIdele E w (a σ)) = GlobalTheory.HeckeGal.toAb E Ω σ) → Continuous fun σ : Ine (F := E) A => a (ineIncl h σ) := by
  intro E Ω _ _ _ _ _ A w h art a ha hord hart
  haveI := absoluteGaloisAbelianization_t2Space E Ω
  let K : Set (w.adicCompletion E)ˣ := {x | Valued.v (x : w.adicCompletion E) = 1}
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp (isCompact_valOne E w)
  let f : K → GlobalTheory.HeckeGal.Gab E Ω := fun x => art (Neutral.B1.localIdele E w x.1)
  have hf : Continuous f :=
    (ha.quot.continuous.comp (continuous_localIdele' E w)).comp continuous_subtype_val
  have hinj : Function.Injective f := fun x y hxy =>
    Subtype.ext (GlobalTheory.ArtinLocalInj.artin_localIdele_injective GlobalTheory.Published.chevalleyUnits' E Ω art ha w hxy)
  have hemb := hf.isClosedEmbedding hinj
  have hmem : ∀ σ : Ine (F := E) A, a (ineIncl h σ) ∈ K := by
    intro σ
    have hd : deg (ineIncl h σ) = 0 := by
      rw [deg_eq (a := 0) (b := 0) (actsAs_zero_iff.mpr σ.2)]
      simp
    have ho := hord (ineIncl h σ)
    rw [hd, neg_zero, GlobalTheory.SmGL.SphCompletion.ord_completion, neg_eq_zero] at ho
    show Valued.v ((a (ineIncl h σ) : (w.adicCompletion E)ˣ) : w.adicCompletion E) = 1
    rw [← WithZero.exp_log (by simp : Valued.v ((a (ineIncl h σ) : (w.adicCompletion E)ˣ) : w.adicCompletion E) ≠ 0),
      ho, WithZero.exp_zero]
  let g : Ine (F := E) A → K := fun σ => ⟨a (ineIncl h σ), hmem σ⟩
  have hg : Continuous g := by
    rw [hemb.isInducing.continuous_iff]
    have e : f ∘ g = fun σ : Ine (F := E) A => GlobalTheory.HeckeGal.toAb E Ω (σ : G E Ω) :=
      funext fun σ => hart (ineIncl h σ)
    rw [e]
    exact continuous_quot_mk.comp continuous_subtype_val
  exact continuous_subtype_val.comp hg

end GlobalTheory.ArtinInvCont
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InverseTransposeMemCuspFormRapidKernelSpanContra
section
noncomputable section

open NumberField Matrix MeasureTheory GlobalTheory.CuspRep GroundTheory.Global GroundTheory.Global.IdeleGroup

namespace GlobalTheory.JSW

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem invT_invT_gl {R : Type} [CommRing R] (g : GL (Fin a) R) : invT a R (invT a R g) = g := by
  apply Units.ext
  change ((invT a R g)⁻¹).valᵀ = g.val
  rw [← map_inv]
  change ((g⁻¹)⁻¹).valᵀᵀ = g.val
  rw [inv_inv, Matrix.transpose_transpose]

theorem map_invT_gl {R S : Type} [CommRing R] [CommRing S] (p : R →+* S) (g : GL (Fin a) R) :
    GeneralLinearGroup.map p (invT a R g) = invT a S (GeneralLinearGroup.map p g) := by
  apply Units.ext
  change p.mapMatrix ((g⁻¹).valᵀ) = ((GeneralLinearGroup.map p g)⁻¹).valᵀ
  rw [← map_inv]
  ext i j
  rfl

theorem invT_infGL (y : GL (Fin a) (Cinf E)) : invT a (Ad E) (infGL E a y) = infGL E a (invT a (Cinf E) y) := by
  apply ga_ext
  · rw [map_invT_gl, pInf_infGL, pInf_infGL]
  · rw [map_invT_gl, pFin_infGL, pFin_infGL, map_one]

theorem norm_toL_transpose (x : Matrix (Fin a) (Fin a) (Cinf E)) : ‖toL xᵀ‖ = ‖toL x‖ := by
  have key : ∀ y : Matrix (Fin a) (Fin a) (Cinf E), ‖toL yᵀ‖ ≤ ‖toL y‖ := fun y =>
    pi_norm_le_iff_of_nonneg (norm_nonneg _) |>.2 fun i => pi_norm_le_iff_of_nonneg (norm_nonneg _) |>.2 fun j =>
      (norm_le_pi_norm (toL y j) i).trans (norm_le_pi_norm (toL y) j)
  refine le_antisymm (key x) ?_
  simpa using key xᵀ

theorem height_invT (y : GL (Fin a) (Cinf E)) : height (invT a (Cinf E) y) = height y := by
  change 1 + ‖toL (y⁻¹).valᵀ‖ + ‖toL ((invT a (Cinf E) y)⁻¹).val‖ = 1 + ‖toL y.val‖ + ‖toL (y⁻¹).val‖
  rw [← map_inv]
  change 1 + ‖toL (y⁻¹).valᵀ‖ + ‖toL ((y⁻¹)⁻¹).valᵀ‖ = _
  rw [inv_inv, norm_toL_transpose, norm_toL_transpose]
  ring

theorem isRapidInf_invT {X : Type} [MeasurableSpace X] {ν : Measure X} {k : X → ℂ} {γ : X → GL (Fin a) (Cinf E)}
    (hk : IsRapidInf ν k γ) : IsRapidInf ν k (fun x => invT a (Cinf E) (γ x)) := by
  refine ⟨hk.1, ?_, fun N => ?_⟩
  · refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => measurable_pi_lambda _ fun w => ?_
    set p : GL (Fin a) (Cinf E) →* GL (Fin a) ℂ :=
      Matrix.GeneralLinearGroup.map (Pi.evalRingHom (fun _ : InfinitePlace E => ℂ) w)
    have e : (fun x => ((invT a (Cinf E) (γ x) : GL (Fin a) (Cinf E)) : Matrix (Fin a) (Fin a) (Cinf E)) i j w) =
        fun x => (((p (γ x))⁻¹ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) j i := by
      funext x
      rw [← map_inv]; rfl
    rw [e]
    have hγ : ∀ i' j', Measurable fun x => (γ x : Matrix (Fin a) (Fin a) (Cinf E)) i' j' := fun i' j' =>
      (measurable_pi_apply j').comp ((measurable_pi_apply i').comp hk.2.1)
    exact measurable_comp_GL (F := fun g : GL (Fin a) ℂ => ((g⁻¹ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) j i)
      ((Units.continuous_coe_inv : Continuous fun g : GL (Fin a) ℂ =>
        ((g⁻¹ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ)).matrix_elem j i)
      fun i' j' => (measurable_pi_apply w).comp (hγ i' j')
  · simp only [height_invT]
    exact hk.2.2 N

theorem kerInf_comp_invT {X : Type} [MeasurableSpace X] (ν : Measure X) (k : X → ℂ) (γ : X → GL (Fin a) (Cinf E))
    (F : GA E a → ℂ) (g : GA E a) :
    kerInf ν k γ F (invT a (Ad E) g) =
      kerInf ν k (fun x => invT a (Cinf E) (γ x)) (fun h => F (invT a (Ad E) h)) g := by
  unfold kerInf
  congr 1
  funext x
  show k x * F (invT a (Ad E) g * infGL E a (γ x)) =
    k x * F (invT a (Ad E) (g * infGL E a (invT a (Cinf E) (γ x))))
  rw [map_mul, invT_infGL, invT_invT_gl]

theorem comp_invT_mem_mspanR (π : CuspSub E a) (F : GA E a → ℂ) (hF : F ∈ mspanR π) :
    (fun g => F (invT a (Ad E) g)) ∈ mspanR π.contra := by
  let T : Submodule ℂ (GA E a → ℂ) :=
    (rspan π.contra).comap (LinearMap.funLeft ℂ ℂ (invT a (Ad E)))
  have memT : ∀ G : GA E a → ℂ, G ∈ T ↔ (fun g => G (invT a (Ad E) g)) ∈ rspan π.contra := fun G =>
    Submodule.mem_comap
  have hle : rspan π ≤ T := by
    refine rspan_le (fun φ hφ => ?_) (fun F hF h => ?_) fun F hF X _ ν _ k γ hk => ?_
    · rw [memT]
      have h1 : UpperTheory.V.TC.dualFn E a φ ∈ π.contra.V := Submodule.mem_map_of_mem hφ
      exact mem_rspan h1
    · rw [memT] at hF ⊢
      have h2 := rt_mem_rspan hF (invT a (Ad E) h)
      have e : (fun g => F (invT a (Ad E) g * h)) = fun g => F (invT a (Ad E) (g * invT a (Ad E) h)) := by
        funext g; rw [map_mul, invT_invT_gl]
      rw [e]; exact h2
    · rw [memT] at hF ⊢
      have h3 := kerInf_mem_rspan hF ν (isRapidInf_invT hk)
      have e : (fun g => kerInf ν k γ F (invT a (Ad E) g)) =
          kerInf ν k (fun x => invT a (Cinf E) (γ x)) (fun h => F (invT a (Ad E) h)) :=
        funext fun g => kerInf_comp_invT ν k γ F g
      rw [e]; exact h3
  rw [← rspan_eq_mspanR] at hF ⊢
  exact (memT F).1 (hle hF)

example (π : CuspSub E a) {φ : Sm E a} (hφ : φ ∈ π.V) :
    (fun g => φ.1 (invT a (Ad E) g)) ∈ mspanR π.contra ∧ mspanR π.contra ≠ ⊥ :=
  ⟨comp_invT_mem_mspanR π φ.1 (rspan_eq_mspanR π ▸ mem_rspan hφ), rspan_eq_mspanR π.contra ▸ rspan_ne_bot _⟩

theorem invT_mem_mspanR_contra : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (π : CuspSub E a)
    (F : GA E a → ℂ), F ∈ GlobalTheory.JSW.mspanR π → (fun g => F (invT a (Ad E) g)) ∈ GlobalTheory.JSW.mspanR π.contra :=
  fun _ _ _ _ _ π F hF => comp_invT_mem_mspanR π F hF

end GlobalTheory.JSW
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnramifiedCharOfCuspidalSphericalStatement
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isUnramifiedChar_of_cuspidal_spherical : GeometricLemma → BernsteinZelevinskyFiniteness → ZelevinskyPolynomialRing → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] (x : IrrGL k), x.IsCusp → IsSpherical x.rep → x.IsUnramChar := by
  first | exact @GlobalTheory.LocLanglands.isUnramChar_of_isCusp_of_isSpherical | exact GlobalTheory.LocLanglands.isUnramChar_of_isCusp_of_isSpherical | (intros; apply GlobalTheory.LocLanglands.isUnramChar_of_isCusp_of_isSpherical <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatIntMember
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.CoefDuty

namespace GlobalTheory.CoefDuty

theorem latInt_member : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : SideA D cf jE) (M : MtFam D) (C : NChoice D) (tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E), MtInput D M tup C.Q → ∀ big L, Built A M C tup big L → (∀ i, (withLoc L).nd.Q i = C.Q ((withLoc L).nd.w i)) ∧ ∀ j h1 h2 w, (withLoc L).what₂.muAt w ≠ (withLoc L).what₂.mu0 → LatInt (withLoc L) (mtL L M) (C.Q w) j h1 h2 w := by
  intro D cf jE A M C tup hM big L hB
  obtain ⟨Sp, -, -⟩ := hB
  refine ⟨fun i => ?_, fun j h1 h2 w hw => ?_⟩
  · have h : i ∈ L.X.nd.locs (L.X.nd.j i) (L.X.nd.w i) := (L.X.nd.locs_mem _ _ i).2 ⟨rfl, rfl⟩
    exact (Sp.Q_eq _ _ i h).trans (Sp.Qc_eq _ _)
  · obtain ⟨j, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    have h2' : j < D.R.m := h2
    exact ⟨(hM.full w ⟨j, h2'⟩ hw).1, fun v k s ϖ hg hc hu => hM.int w ⟨j, h2'⟩ v k s ϖ hw hg hc hu⟩
end GlobalTheory.CoefDuty
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftBlockDiagReductionToFlagGroupStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (FinPl idem SplitProj IsIdemOf IsProjAt adjCo grpCo frCo)
open GlobalTheory.DownLift.GenSplit
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lift_blockDiag_reduction_to_flagGroup : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), ∀ (i : Fin D.R.m) (t : T) (PP : Pl D.host.E) (hPP : PP ∈ R.Pg) (g : G), (∀ PP' : R.Pg, PP' ≠ ⟨PP, hPP⟩ → R.eG g PP' = 1) → ∀ κ : GA D (Vc D i), κ ∈ GfC (Vc D i) → finE (Vc D i) κ ∈ Formalism.L2.DIV.St (R.βV i) → ((redFn (R.βV i) PP (finE (Vc D i) κ) : GL (Fin (Vc D i).rank) (kP PP)) : Matrix (Fin (Vc D i).rank) (Fin (Vc D i).rank) (kP PP)) = (Matrix.fromBlocks ((R.eG g ⟨PP, hPP⟩ : GL (Fin D.R.r) (kP PP)) : Matrix (Fin D.R.r) (Fin D.R.r) (kP PP)) 0 0 (1 : Matrix (Fin D.R.t) (Fin D.R.t) (kP PP))).submatrix (rowIx (rank_V i)).symm (rowIx (rank_V i)).symm → (∀ PP', PP' ∈ R.Pg ∨ PP' ∈ R.Q t → PP' ≠ PP → redFn (R.βV i) PP' (finE (Vc D i) κ) = 1) → IsLevelLift (Vc D i) (R.βV i) (R.datVt i t) (R.eG g) κ ∧ levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) κ = 1 := by
  first | exact @GlobalTheory.LiftDiag.lift_diag | exact GlobalTheory.LiftDiag.lift_diag | (intros; apply GlobalTheory.LiftDiag.lift_diag <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalHeisenbergSpanPreservesTypeRelationsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.DownLift.SplitCoef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localHeisenbergSpan_preserves_type_relations : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.thP_ωP → ∀ (i : Fin D.R.m) (t : T) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))) (v : HeightOneSpectrum (𝓞 D.host.F)), v ∈ Sb → ∀ (ε : AF D.host.F) (a : AE D), IsPlaceIdem D v ε → a + cA D a = algebraMap (AF D.host.F) (AE D) ε → ∀ f : WO (Vc D i) (Wc D i) → ℂ, TypeIn R i t Sb f → CleanIn R i t Sb f → LikeOff R i t Sb f → ∀ f' ∈ locSpan R.ψ (Vc D i) (Wc D i) a f, TypeIn R i t (dropPl Sb v) f' ∧ CleanIn R i t (dropPl Sb v) f' ∧ LikeOff R i t Sb f' := by
  first | exact @GlobalTheory.DownLift.PlaceTranslate.locSpan_pres | exact GlobalTheory.DownLift.PlaceTranslate.locSpan_pres | (intros; apply GlobalTheory.DownLift.PlaceTranslate.locSpan_pres <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLanglandsExtensionInjective
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LocLanglands.LExtInj

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_irreducible_GL_zero : ∃ t : IrrGL k, t.1 = 0 ∧ IsL (0 : Multiset (Segment k)) t.rep :=
  ⟨IrrGL.of (detRep (Fin 0) (1 : kˣ →* ℂˣ)) ((isSmooth_ofChar_iff _).2 isSmoothChar_one.detChar)
    (isIrreducible_ofChar _), rfl, (Tests.empty_spec (k := k)).2.of_equiv (IrrGL.equivOf _ _ _)⟩

theorem sum_fst_of_lFactors' {𝔪 : Multiset (Segment k)} {c : ℕ} {x : Fin c → IrrGL k} (hx : LFactors 𝔪 x) :
    ∑ a, (x a).1 = (𝔪.map Segment.deg).sum := by
  obtain ⟨Δ, ⟨rfl, -⟩, hΔ⟩ := hx
  rw [Multiset.map_map, ← Finset.sum_eq_multiset_sum]
  exact Finset.sum_congr rfl fun a _ => (hΔ a).deg_eq.symm

theorem deg_of_isL' {V : Type} [AddCommGroup V] [Module ℂ V] {N : ℕ} {𝔪 : Multiset (Segment k)}
    {π : Representation ℂ (GL (Fin N) k) V} (h : IsL 𝔪 π) : (𝔪.map Segment.deg).sum = N := by
  obtain ⟨_, x, hd, hx, -⟩ := h
  exact (sum_fst_of_lFactors' hx).symm.trans hd

theorem eq_of_isL (hM : LanglandsMultisegments) [CharZero k] (𝔪 : Multiset (Segment k)) (x y : IrrGL k)
    (hx : IsL 𝔪 x.rep) (hy : IsL 𝔪 y.rep) : x = y := by
  obtain ⟨t, ht0, ht⟩ := exists_irreducible_GL_zero (k := k)
  have hdeg : x.1 = y.1 := (deg_of_isL' hx).symm.trans (deg_of_isL' hy)
  obtain ⟨nx, cx⟩ := x
  obtain ⟨ny, cy⟩ := y
  obtain rfl : nx = ny := hdeg
  have hd : ∑ a, (![(⟨nx, cx⟩ : IrrGL k), t] a).1 = nx := by simp [Fin.sum_univ_two, ht0]
  have hs := (hM k).2 𝔪 0 ![⟨nx, cx⟩, t] ⟨nx, cy⟩ hd hx ht (by rwa [add_zero])
  obtain ⟨φ⟩ := GlobalTheory.T.nonempty_equiv_prodChosenIrrGL_pair_degreeZero k (⟨nx, cx⟩ : IrrGL k) t ht0 hd
  have hs2 : IsSubquotient (IrrGL.rep (⟨nx, cy⟩ : IrrGL k)) (IrrGL.rep (⟨nx, cx⟩ : IrrGL k)) :=
    hs.trans (.of_injective φ.symm.toIntertwiningMap φ.symm.toLinearEquiv.injective)
  obtain ⟨ψ⟩ := hs2.nonempty_equiv cy.rep.irr cx.rep.irr
  congr 1
  rw [← cx.cl_rep, ← cy.cl_rep]
  exact IrrRep.cl_eq_iff.2 ⟨ψ⟩

end Local

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem isIrrWD_lpTw {y : WD h} (hy : IsIrrWD y) (s : ℝ) : IsIrrWD (y.lpTw s) := by
  obtain ⟨n, a, rfl, ha⟩ := hy
  exact ⟨n, a.tw s, (WD.lpTw_mk a s).symm, isIrreducible_twist ha _⟩

theorem lpTw_injective {y y' : WD h} {s : ℝ} (e : y.lpTw s = y'.lpTw s) : y = y' := by
  have := congrArg (fun z : WD h => z.lpTw (-s)) e
  simpa only [WD.lpTw_add, add_neg_cancel, WD.lpTw_zero] using this

end GlobalTheory.LocLanglands.LExtInj

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocationsDistinguishedByGenerics
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.CoefDuty

noncomputable section

namespace GlobalTheory.CoefDuty
set_option synthInstance.maxHeartbeats 400000 in

theorem sameLoc_iff_heckeCong : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : SideA D cf jE) (M : MtFam D) (C : NChoice D) (tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E) (big : D.what₂.places.Pl → Finset ℂ) (L : LocAll (lay0 D)), Built A M C tup big L → ∀ (j : ℕ) (w : D.what₂.places.Pl) (i i' : L.X.nd.Loc), i ∈ L.X.nd.locs j w → i' ∈ L.X.nd.locs j w → ∀ (x : L.X.nd.X i) (x' : L.X.nd.X i'), (i = i' ↔ ∀ (v : PlE D.host) (k : ℕ), GenAt D (D.what₂.places.resChar w) (C.Q w) v k → iotaO L.X.nd L.Y.naut i ((L.X.nd.hT i v k : L.X.nd.X i → L.X.nd.O i) x) - iotaO L.X.nd L.Y.naut i' ((L.X.nd.hT i' v k : L.X.nd.X i' → L.X.nd.O i') x') ∈ (A.pl.plB w).nonunits) := by
  intro D cf jE A M C tup big L hB j w i i' hi hi' x x'
  obtain ⟨Sp, ⟨Au⟩, -⟩ := hB

  have hiC : ∀ (a : L.X.nd.Loc) (ha : a ∈ L.X.nd.locs j w) (z : L.X.nd.O a),
      iotaO L.X.nd L.Y.naut a z = Sp.iotaC j w (Sp.phO j w a ha z) := by
    intro a ha z
    rw [← Sp.iotaC_coh j w a ha z]
    show ((L.Y.naut.iotaQC a).toRingHom.comp (L.Y.naut.iotaQ a)) (algebraMap _ _ z) = _
    rw [RingHom.comp_apply, Au.iotaQ, Au.iotaQC]
    rfl

  have key : ∀ (a : L.X.nd.Loc) (ha : a ∈ L.X.nd.locs j w) (y : L.X.nd.O a),
      iotaO L.X.nd L.Y.naut a y ∈ (A.pl.plB w).nonunits ↔ y ∈ IsLocalRing.maximalIdeal (L.X.nd.O a) := by
    intro a ha y
    have hw : L.X.nd.w a = w := ((L.X.nd.locs_mem j w a).1 ha).2
    subst hw
    obtain ⟨h, e⟩ := Au.kFbar a y
    rw [ValuationSubring.mem_nonunits_iff]
    have e1 : (A.pl.plB (L.X.nd.w a)).valuation (iotaO L.X.nd L.Y.naut a y) =
        (A.pl.plB (L.X.nd.w a)).valuation ((⟨_, h⟩ : A.pl.plB (L.X.nd.w a)) : ℂ) := rfl
    rw [e1, ← ValuationSubring.valuation_lt_one_iff, ← IsLocalRing.residue_eq_zero_iff,
      ← IsLocalRing.residue_eq_zero_iff, ← map_eq_zero (L.Y.naut.kFbar a), ← e]
    simp only [EmbeddingLike.map_eq_zero_iff]

  have gen : ∀ v k, GenAt D (D.what₂.places.resChar w) (C.Q w) v k ↔
      GenAt D (D.what₂.places.resChar w) (Sp.B.Qc j w) v k := by
    intro v k; rw [Sp.Qc_eq]
  constructor
  · rintro rfl v k hvk
    have hvk' := (gen v k).1 hvk
    have e1 := Sp.ptX_hT j w i hi x v k hvk'
    have e2 := Sp.ptX_hT j w i hi' x' v k hvk'
    have hc : Formalism.L2.NCov.cls (Sp.ptX j w i hi x).1 = Formalism.L2.NCov.cls (Sp.ptX j w i hi' x').1 :=
      (Sp.ptX j w i hi x).2.1.trans (Sp.ptX j w i hi' x').2.1.symm
    generalize (Sp.ptX j w i hi x).1 = ψ at e1 hc
    generalize (Sp.ptX j w i hi' x').1 = ψ' at e2 hc
    generalize (⟨Sp.B.hK j w v k, Algebra.subset_adjoin ⟨v, k, hvk', rfl⟩⟩ : heckeAlg Sp.B j w) = t at e1 e2
    have hmem : t - algebraMap _ _ (ψ t) ∈ Formalism.L2.NCov.cls ψ' := by
      rw [← hc, Formalism.L2.NCov.cls, RingHom.mem_ker]
      change IsLocalRing.residue _ (ψ (t - algebraMap _ _ (ψ t))) = 0
      rw [map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_self, map_zero]
    rw [Formalism.L2.NCov.cls, RingHom.mem_ker] at hmem
    change IsLocalRing.residue _ (ψ' (t - algebraMap _ _ (ψ t))) = 0 at hmem
    rw [map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, map_sub, sub_eq_zero, ← e1, ← e2] at hmem
    have r := GlobalTheory.PtLocalEig.residue_map_equiv (Sp.phO j w i hi).symm hmem
    simp only [RingEquiv.symm_apply_apply] at r
    rw [← map_sub]
    refine (key i hi _).2 ?_
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, r, sub_self]
  · intro H
    apply Sp.mx_inj j w hi hi'
    rw [← (Sp.ptX j w i hi x).2.1, ← (Sp.ptX j w i' hi' x').2.1]
    refine GlobalTheory.PtLocalEig.cls_eq_of_residue _ _ _ ?_
    rintro _ ⟨v, k, hvk, rfl⟩
    rw [← Sp.ptX_hT j w i hi x v k hvk, ← Sp.ptX_hT j w i' hi' x' v k hvk]
    have h1 := H v k ((gen v k).2 hvk)
    have hz : iotaO L.X.nd L.Y.naut i' ((L.X.nd.hT i' v k : L.X.nd.X i' → L.X.nd.O i') x') =
        iotaO L.X.nd L.Y.naut i ((Sp.phO j w i hi).symm
          (Sp.phO j w i' hi' ((L.X.nd.hT i' v k : L.X.nd.X i' → L.X.nd.O i') x'))) := by
      rw [hiC i hi, hiC i' hi', RingEquiv.apply_symm_apply]
    rw [hz, ← map_sub, key i hi, ← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero] at h1
    have h2 := GlobalTheory.PtLocalEig.residue_map_equiv (Sp.phO j w i hi) h1
    rwa [RingEquiv.apply_symm_apply] at h2

end GlobalTheory.CoefDuty

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MaxCompactUnitaryConjRelIndexEq
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

open GlobalTheory.UnimodMass in
theorem GlobalTheory.UnimodMass.umax_relIndex_conj : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (h : GAf L n), ((Umax L n).map (MulAut.conj h).toMonoidHom).relIndex (Umax L n) ≠ 0 ∧ ((Umax L n).map (MulAut.conj h).toMonoidHom).relIndex (Umax L n) = (Umax L n).relIndex ((Umax L n).map (MulAut.conj h).toMonoidHom) := by
  intro L _ _ _ n h
  set U := Umax L n with hUdef
  set V := U.map (MulAut.conj h).toMonoidHom with hVdef
  haveI hW : Finite (DC (GQ L n) (U ⊓ V)) := finite_dc_of_cover (GlobalTheory.T.exists_finset_doubleCosets_conj_maxCompact L n h)
  have hb : IsBounded U := ⟨{1}, fun κ hκ => ⟨1, by simp, by simpa using hκ⟩⟩
  have hU : ∀ t : GAf L n, Finite {γ : GQ L n // t⁻¹ * (γ : GAf L n) * t ∈ U} := fun t => GlobalTheory.T.finite_rational_conj_mem_boundedCompact L n U hb t
  have hV : ∀ t : GAf L n, Finite {γ : GQ L n // t⁻¹ * (γ : GAf L n) * t ∈ V} := by
    intro t
    haveI := hU (t * h)
    refine Finite.of_injective (fun x : {γ : GQ L n // t⁻¹ * (γ : GAf L n) * t ∈ V} =>
      (⟨x.1, ?_⟩ : {γ : GQ L n // (t * h)⁻¹ * (γ : GAf L n) * (t * h) ∈ U})) ?_
    · have hx : t⁻¹ * ((x.1 : GQ L n) : GAf L n) * t ∈ U.map (MulAut.conj h).toMonoidHom := x.2
      rw [Subgroup.mem_map_equiv] at hx
      simpa [MulAut.conj_symm_apply, mul_assoc] using hx
    · intro a b hab
      exact Subtype.ext (by simpa using congrArg Subtype.val hab)
  obtain ⟨h1, e1⟩ := GlobalTheory.T.doubleCosetMass_eq_relIndex_mul_mass (GAf L n) (GQ L n) (U ⊓ V) U inf_le_left hW hU
  obtain ⟨h2, e2⟩ := GlobalTheory.T.doubleCosetMass_eq_relIndex_mul_mass (GAf L n) (GQ L n) (U ⊓ V) V inf_le_right hW hV
  have e3 : mass (GQ L n) V = mass (GQ L n) U := mass_conj (GQ L n) U h
  haveI : Finite (DC (GQ L n) U) := finite_dc_of_le (Γ := GQ L n) (W := U ⊓ V) inf_le_left
  have hpos := mass_pos (Γ := GQ L n) (K := U) hU
  rw [Subgroup.inf_relIndex_left] at h1 e1
  rw [Subgroup.inf_relIndex_right] at h2 e2
  refine ⟨h1, ?_⟩
  rw [e3] at e2
  have : (V.relIndex U : ℚ) = (U.relIndex V : ℚ) := mul_right_cancel₀ hpos.ne' (e1.symm.trans e2)
  exact_mod_cast this
end

