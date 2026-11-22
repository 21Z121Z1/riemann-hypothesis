import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0705
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0703
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0702
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWeilDatumOOneOfRankZero
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0684
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0677
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0676
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0068
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0709
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0708
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0706

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PlaceOverTransportRingIso
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.WeilTransport

theorem conj_nhds : ∀ (E Ω : Type) [Field E] [Field Ω] [Algebra E Ω] [Algebra.IsAlgebraic E Ω] (E' Ω' : Type)
    [Field E'] [Field Ω'] [Algebra E' Ω'] (φ : Ω ≃+* Ω') (U' : Set (G E' Ω')), U' ∈ nhds (1 : G E' Ω') →
    ∃ U : Set (G E Ω), IsOpen U ∧ (1 : G E Ω) ∈ U ∧
      ∀ σ ∈ U, ∀ σ' : G E' Ω', (∀ z, φ (σ z) = σ' (φ z)) → σ' ∈ U' := by
  intro E Ω _ _ _ _ E' Ω' _ _ _ φ U' hU'
  obtain ⟨L', hL'fin, hL'⟩ := (krullTopology_mem_nhds_one_iff E' Ω' U').mp hU'
  let b := Module.finBasis E' L'
  let S : Set Ω := Set.range fun i => φ.symm (b i : Ω')
  let L : IntermediateField E Ω := IntermediateField.adjoin E S
  haveI : Finite S := (Set.finite_range _).to_subtype
  haveI : FiniteDimensional E L := IntermediateField.finiteDimensional_adjoin
    (fun x _ => (Algebra.IsAlgebraic.isAlgebraic x).isIntegral)
  refine ⟨L.fixingSubgroup, L.fixingSubgroup_isOpen, L.fixingSubgroup.one_mem, ?_⟩
  intro σ hσ σ' hrel
  apply hL'
  rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]
  have hb : ∀ i, σ' (b i : Ω') = b i := by
    intro i
    have h1 : φ.symm (b i : Ω') ∈ L := IntermediateField.subset_adjoin E S ⟨i, rfl⟩
    have h2 := (IntermediateField.mem_fixingSubgroup_iff L σ).mp hσ _ h1
    have h3 := hrel (φ.symm (b i : Ω'))
    rw [h2, RingEquiv.apply_symm_apply] at h3
    exact h3.symm
  intro x hx
  have e := congrArg Subtype.val (b.sum_repr ⟨x, hx⟩)
  simp only [AddSubmonoidClass.coe_finset_sum, SetLike.val_smul] at e
  rw [← e, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, hb]

section Transfer

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
  {A : ValuationSubring Ω} {E' Ω' : Type} [Field E'] [NumberField E'] [Field Ω'] [Algebra E' Ω']
  {A' : ValuationSubring Ω'} {φ : Ω ≃+* Ω'}

def conj (φ : Ω ≃+* Ω') (σ : Ω ≃+* Ω) : Ω' ≃+* Ω' := (φ.symm.trans σ).trans φ

@[simp] theorem conj_apply (φ : Ω ≃+* Ω') (σ : Ω ≃+* Ω) (y : Ω') : conj φ σ y = φ (σ (φ.symm y)) := rfl

def conjAlg (φ : Ω ≃+* Ω') (σ : G E Ω)
    (hσ : ∀ y : E', conj φ σ.toRingEquiv (algebraMap E' Ω' y) = algebraMap E' Ω' y) : G E' Ω' :=
  AlgEquiv.ofRingEquiv hσ

@[simp] theorem conjAlg_apply (φ : Ω ≃+* Ω') (σ : G E Ω)
    (hσ : ∀ y : E', conj φ σ.toRingEquiv (algebraMap E' Ω' y) = algebraMap E' Ω' y) (y : Ω') :
    conjAlg φ σ hσ y = φ (σ (φ.symm y)) := rfl

theorem val_le_one_iff (hm : ∀ z, φ z ∈ A' ↔ z ∈ A) (z : Ω) :
    A'.valuation (φ z) ≤ 1 ↔ A.valuation z ≤ 1 := by
  rw [A'.valuation_le_one_iff, A.valuation_le_one_iff, hm]

theorem val_lt_one_iff (hm : ∀ z, φ z ∈ A' ↔ z ∈ A) (z : Ω) :
    A'.valuation (φ z) < 1 ↔ A.valuation z < 1 := by
  rw [valuation_lt_one_iff', valuation_lt_one_iff', ← map_inv₀, hm, hm, map_eq_zero_iff _ φ.injective]

omit [NumberField E'] in
theorem mem_Dec_iff' {K F : Type} [Field K] [Field F] [NumberField F] [Algebra F K] (B : ValuationSubring K)
    (τ : G F K) : τ ∈ Dec (F := F) B ↔ ∀ x, τ x ∈ B ↔ x ∈ B := by
  refine ⟨fun h x => apply_mem_iff_of_mem_Dec h x, fun h => mem_Dec.mpr ?_⟩
  ext x
  have := h ((τ⁻¹ : G F K) x)
  rw [mul_inv_apply] at this
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def]
  exact this.symm

theorem mem_Dec_iff (hm : ∀ z, φ z ∈ A' ↔ z ∈ A) {σ : G E Ω} {σ' : G E' Ω'}
    (hrel : ∀ z, φ (σ z) = σ' (φ z)) : σ' ∈ Dec (F := E') A' ↔ σ ∈ Dec (F := E) A := by
  rw [mem_Dec_iff', mem_Dec_iff']
  constructor
  · intro h x; rw [← hm, hrel, h, hm]
  · intro h x; obtain ⟨z, rfl⟩ := φ.surjective x; rw [← hrel, hm, hm, h]

theorem actsAs_iff (hm : ∀ z, φ z ∈ A' ↔ z ∈ A) {σ : G E Ω} {σ' : G E' Ω'}
    (hrel : ∀ z, φ (σ z) = σ' (φ z)) (q a b : ℕ) : ActsAs A' q σ' a b ↔ ActsAs A q σ a b := by
  unfold ActsAs
  rw [mem_Dec_iff hm hrel]
  refine and_congr_right fun _ => ?_
  constructor
  · intro h x hx
    have := h (φ x) ((val_le_one_iff hm x).mpr hx)
    rwa [← hrel, ← map_pow φ, ← map_pow φ, ← map_sub φ, val_lt_one_iff hm] at this
  · intro h x hx
    obtain ⟨z, rfl⟩ := φ.surjective x
    rw [val_le_one_iff hm] at hx
    rw [← hrel, ← map_pow φ, ← map_pow φ, ← map_sub φ, val_lt_one_iff hm]
    exact h z hx

end Transfer

section Smooth

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
  {E' Ω' : Type} [Field E'] [NumberField E'] [Field Ω'] [Algebra E' Ω'] [IsAlgClosure E' Ω']
  {A' : ValuationSubring Ω'} {w' : HeightOneSpectrum (𝓞 E')} {h' : IsPlaceOver A' w'}

theorem smooth_comp (φ : Ω ≃+* Ω') (e : Weil h →* Weil h')
    (he : ∀ (σ : Weil h) z, φ ((σ : G E Ω) z) = (e σ : G E' Ω') (φ z)) (hdeg : ∀ σ, deg (e σ) = deg σ)
    {M : Type} [Monoid M] (f : Weil h' →* M) (hf : IsSmooth f) : IsSmooth (f.comp e) := by
  haveI : Algebra.IsAlgebraic E Ω := IsAlgClosure.isAlgebraic
  obtain ⟨O', hO', hpre⟩ := isOpen_induced_iff.mp hf
  have h1 : (1 : G E' Ω') ∈ O' := by
    have : (1 : Ine (F := E') A') ∈ Subtype.val ⁻¹' O' := by rw [hpre]; simp
    exact this
  obtain ⟨U, hU, hU1, hUO⟩ := conj_nhds E Ω E' Ω' φ O' (hO'.mem_nhds h1)
  refine IsSmooth.of_open (U := Subtype.val ⁻¹' U) (hU.preimage continuous_subtype_val) hU1 ?_
  intro τ hτ
  have hmem : ((e (ineIncl h τ) : Weil h') : G E' Ω') ∈ Ine (F := E') A' := by
    rw [← deg_eq_zero_iff, hdeg, deg_ineIncl]
  have hO : (⟨_, hmem⟩ : Ine (F := E') A') ∈ Subtype.val ⁻¹' O' := hUO τ hτ _ (he (ineIncl h τ))
  rw [hpre] at hO
  have e1 : ineIncl h' ⟨_, hmem⟩ = e (ineIncl h τ) := Subtype.ext rfl
  rw [Set.mem_setOf_eq, e1] at hO
  exact hO

end Smooth

open GlobalTheory.LocLanglands in
theorem weil_equiv : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (E' Ω' : Type) [Field E'] [NumberField E'] [Field Ω'] [Algebra E' Ω'] [IsAlgClosure E' Ω'] (A' : ValuationSubring Ω') (w' : HeightOneSpectrum (𝓞 E')) (h' : IsPlaceOver A' w') (φ : Ω ≃+* Ω') (j : E →+* E') (i : w.adicCompletion E ≃+* w'.adicCompletion E'), PlaceIso A w A' w' φ j i → ∃ c : Weil h ≃* Weil h', (∀ σ σ', WeilRel φ σ σ' ↔ c σ = σ') ∧ (∀ σ, deg (c σ) = deg σ) ∧ normV w' = normV w ∧ ∀ (M : Type) [Monoid M] (f : Weil h' →* M), GlobalTheory.WeilDeligne.IsSmooth f ↔ GlobalTheory.WeilDeligne.IsSmooth (f.comp c.toMonoidHom) := by
  intro E Ω _ _ _ _ _ A w h E' Ω' _ _ _ _ _ A' w' h' φ j i hP
  haveI : CharZero Ω' := (RingHom.charZero_iff (algebraMap E' Ω').injective).mp inferInstance
  haveI : Algebra.IsAlgebraic E' Ω' := IsAlgClosure.isAlgebraic
  have fixE : ∀ σ : G E Ω, σ ∈ Dec (F := E) A →
      ∀ y : E', conj φ σ.toRingEquiv (algebraMap E' Ω' y) = algebraMap E' Ω' y := by
    intro σ hσ y
    refine GlobalTheory.T.fixed_algebraic_of_limit_of_fixed_elements Ω' A' (conj φ σ.toRingEquiv) ?_ _ ?_ ?_
    · intro z
      rw [conj_apply, hP.mem, AlgEquiv.coe_ringEquiv, apply_mem_iff_of_mem_Dec hσ]
      conv_rhs => rw [← φ.apply_symm_apply z]
      rw [hP.mem]
    · exact (IsIntegral.map (algebraMap E' Ω').toRatAlgHom
        (Algebra.IsIntegral.isIntegral (R := ℚ) y)).isAlgebraic
    · intro δ hδ
      obtain ⟨x, hx⟩ := GlobalTheory.T.dense_numberField_of_continuous_completion_equiv E w E' Ω' A' w' h' j i hP.cont hP.loc y δ hδ
      refine ⟨algebraMap E' Ω' (j x), ?_, hx⟩
      rw [conj_apply, ← hP.ext, RingEquiv.symm_apply_apply, AlgEquiv.coe_ringEquiv, AlgEquiv.commutes]
  have fixE' : ∀ σ' : G E' Ω', ∀ x : E,
      conj φ.symm σ'.toRingEquiv (algebraMap E Ω x) = algebraMap E Ω x := by
    intro σ' x
    rw [conj_apply, RingEquiv.symm_symm, hP.ext, AlgEquiv.coe_ringEquiv, AlgEquiv.commutes, ← hP.ext,
      RingEquiv.symm_apply_apply]
  have hrelC : ∀ (σ : G E Ω) (hσ : ∀ y : E', conj φ σ.toRingEquiv (algebraMap E' Ω' y) = algebraMap E' Ω' y) z,
      φ (σ z) = conjAlg φ σ hσ (φ z) := by
    intro σ hσ z; rw [conjAlg_apply, RingEquiv.symm_apply_apply]
  have hrelC' : ∀ (σ' : G E' Ω') z, φ (conjAlg φ.symm σ' (fixE' σ') z) = σ' (φ z) := by
    intro σ' z; rw [conjAlg_apply, RingEquiv.symm_symm, RingEquiv.apply_symm_apply]
  have q_eq : normV w' = normV w := by
    apply le_antisymm
    · obtain ⟨σ, hσ⟩ := exists_isFrob h
      have hrel := hrelC σ (fixE σ hσ.1)
      refine GlobalTheory.T.absNorm_place_le_of_frobenius E' Ω' A' w' h' (normV w) (one_lt_normV w) (conjAlg φ σ (fixE σ hσ.1)) ?_
      rw [← actsAs_one_iff, actsAs_iff hP.mem hrel, actsAs_one_iff]; exact hσ
    · obtain ⟨τ', hτ'⟩ := exists_isFrob h'
      have hrel := hrelC' τ'
      refine GlobalTheory.T.absNorm_place_le_of_frobenius E Ω A w h (normV w') (one_lt_normV w') (conjAlg φ.symm τ' (fixE' τ')) ?_
      rw [← actsAs_one_iff, ← actsAs_iff hP.mem hrel, actsAs_one_iff]; exact hτ'
  have memW : ∀ σ : Weil h, conjAlg φ (σ : G E Ω) (fixE σ (Weil_le_Dec h σ.2)) ∈ Weil h' := by
    intro σ
    obtain ⟨a, b, hab⟩ := σ.2
    refine ⟨a, b, ?_⟩
    rw [q_eq, actsAs_iff hP.mem (hrelC _ _)]; exact hab
  have memW' : ∀ σ' : Weil h', conjAlg φ.symm (σ' : G E' Ω') (fixE' σ') ∈ Weil h := by
    intro σ'
    obtain ⟨a, b, hab⟩ := σ'.2
    refine ⟨a, b, ?_⟩
    rw [← q_eq, ← actsAs_iff hP.mem (hrelC' _)]; exact hab
  let c : Weil h ≃* Weil h' :=
    { toFun := fun σ => ⟨_, memW σ⟩
      invFun := fun σ' => ⟨_, memW' σ'⟩
      left_inv := fun σ => by ext z; simp
      right_inv := fun σ' => by ext z; simp
      map_mul' := fun σ τ => by ext z; simp }
  have hc : ∀ σ y, ((c σ : Weil h') : G E' Ω') y = φ ((σ : G E Ω) (φ.symm y)) := fun _ _ => rfl
  have hcs : ∀ σ' y, ((c.symm σ' : Weil h) : G E Ω) y = φ.symm ((σ' : G E' Ω') (φ y)) := fun _ _ => rfl
  have hrel : ∀ (σ : Weil h) z, φ ((σ : G E Ω) z) = ((c σ : Weil h') : G E' Ω') (φ z) := by
    intro σ z; rw [hc, RingEquiv.symm_apply_apply]
  have hdeg : ∀ σ, deg (c σ) = deg σ := by
    intro σ
    obtain ⟨a, b, hab⟩ := σ.2
    rw [deg_eq hab, deg_eq (σ := c σ) (a := a) (b := b) (by rw [q_eq, actsAs_iff hP.mem (hrel σ)]; exact hab)]
  refine ⟨c, ?_, hdeg, q_eq, ?_⟩
  · intro σ σ'
    constructor
    · intro hr
      ext y
      obtain ⟨z, rfl⟩ := φ.surjective y
      rw [← hrel]
      exact hr z
    · rintro rfl z
      exact hrel σ z
  · intro M _ f
    constructor
    · exact smooth_comp φ c.toMonoidHom hrel hdeg f
    · intro hf
      have hrel' : ∀ (σ' : Weil h') z, φ.symm ((σ' : G E' Ω') z) = ((c.symm σ' : Weil h) : G E Ω) (φ.symm z) := by
        intro σ' z; rw [hcs, RingEquiv.apply_symm_apply]
      have hdeg' : ∀ σ', deg (c.symm σ') = deg σ' := by
        intro σ'; rw [← hdeg, MulEquiv.apply_symm_apply]
      have := smooth_comp φ.symm c.symm.toMonoidHom hrel' hdeg' (f.comp c.toMonoidHom) hf
      convert this using 1
      ext σ'
      simp

end GlobalTheory.WeilTransport
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RallisNonGraphLagrangianSumEqZeroCuspidal
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open scoped GlobalTheory.GaugeEx

noncomputable section
namespace GlobalTheory.RallisCusp

theorem nonGraph_sum_eq_zero : ∀ D : D7, EisAbs D → TermMove D → TermInv D → CuspKill D → (∀ ψ (V W : HSp D) χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr, SWSetup ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr → ∀ f₁ f₂, IsThetaFunO ψ V W f₁ → IsThetaFunO ψ V W f₂ → ∀ Y : Lag W, Y.1.comap (LinearMap.inl D.host.E _ _) ≠ ⊥ → Continuous fun g : GA D W => lagTerm μ 𝓕 (fr Y) (om (1, g) f₁) f₂) → ∀ (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (νV : Measure (GA D V)) (𝓗 : Set (GA D V)) (νW : Measure (GA D W)) (𝓖 : Set (GA D W)) (μ : Measure (WO V W)) (𝓕 : Set (WO V W)) (fr : Lag W → Matrix (Fin W.rank) (Fin W.rank) D.host.E × Matrix (Fin W.rank) (Fin W.rank) D.host.E), SWSetup ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr → ∀ (θ : InfFam D), IsInfFam θ → ∀ (f₁ f₂ : WO V W → ℂ) (φ₁ φ₂ : GA D W → ℂ), IsThetaFunO ψ V W f₁ → IsThetaFunO ψ V W f₂ → IsAutFunSm θ W φ₁ → IsCuspFun W φ₁ → IsAutFunSm θ W φ₂ → IsCuspFun W φ₂ → ∑' Y : {Y : Lag W // Y.1.comap (LinearMap.inl D.host.E _ _) ≠ ⊥}, ∫ p in 𝓖 ×ˢ 𝓖, star (φ₁ p.1) * φ₂ p.2 * lagTerm μ 𝓕 (fr Y.1) (om (1, p.1) f₁) (om (1, p.2) f₂) ∂(νW.prod νW) = 0 := by
  intro D hEis hMove hInv hKill hcont ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr hS θ hθ f₁ f₂ φ₁ φ₂ hf₁ hf₂ ha₁ hc₁ ha₂ hc₂
  haveI : Countable (Lag W) := lag_countable D W
  haveI : Countable D.host.E := countable_numberField_type D.host.E
  haveI := hS.haarW
  have hw := hS.weil
  have hpres : ∀ p f, IsThetaFunO ψ V W f → IsThetaFunO ψ V W (om p f) := hw.om_pres
  have hom : ∀ (g h : GA D W) f, om (1, g) (om (1, h) f) = om (1, g * h) f := by
    intro g h f
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, one_mul]

  have hmove : ∀ (γ : GQ W) (Y : Lag W) (g : GA D W) (F₂ : WO V W → ℂ), IsThetaFunO ψ V W F₂ →
      lagTerm μ 𝓕 (fr (lagAct W γ Y)) (om (1, g) f₁) F₂ = lagTerm μ 𝓕 (fr Y) (om (1, (γ : GA D W)⁻¹ * g) f₁) F₂ := by
    intro γ Y g F₂ hF₂
    have h1 := (hMove ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr hS (om (1, g) f₁) F₂ (hpres _ _ hf₁) hF₂).1
      (lagAct W γ Y) _ (isLagFrame_lagAct W γ Y (fr Y) (hS.frame Y))
    have h2 := ((hMove ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr hS (om (1, (γ : GA D W)⁻¹ * g) f₁) F₂ (hpres _ _ hf₁) hF₂).2
      γ γ.2 (gqMat W γ) (gqMat_map W γ).symm).1 (fr Y)
    rw [← h1, ← h2, hom, mul_inv_cancel_left]

  have hslice : ∀ g₂ : GA D W, ∑' Y : NGLag W, ∫⁻ g in 𝓖, ‖star (φ₁ g) * lagTerm μ 𝓕 (fr Y.1) (om (1, g) f₁) (om (1, g₂) f₂)‖ₑ ∂νW ≠ ⊤ →
      ∑' Y : NGLag W, ∫ g in 𝓖, star (φ₁ g) * lagTerm μ 𝓕 (fr Y.1) (om (1, g) f₁) (om (1, g₂) f₂) ∂νW = 0 := by
    intro g₂ hfin
    have hF₂ := hpres (1, g₂) f₂ hf₂
    have hGQ : Countable (GQ W) := by
      haveI : Countable (Matrix (Fin W.rank) (Fin W.rank) D.host.E) :=
        inferInstanceAs (Countable (Fin W.rank → Fin W.rank → D.host.E))
      refine Function.Injective.countable (f := fun γ : GQ W => gqMat W γ) ?_
      intro γ δ h
      apply Subtype.ext
      apply GlobalTheory.MixModel.mt_injective W
      have := congrArg (fun c => c.map (incA D)) h
      simpa only [gqMat_map] using this
    refine GlobalTheory.T.tsum_setIntegral_eq_zero_of_stabilizer_integrals νW inferInstance (GQ W) hGQ 𝓖 hS.fdW (ngAct W) (ngAct_one W) (ngAct_mul W)
      (fun Y g => star (φ₁ g) * lagTerm μ 𝓕 (fr Y.1) (om (1, g) f₁) (om (1, g₂) f₂)) ?_ ?_ hfin ?_
    · intro γ Y g
      show star (φ₁ g) * lagTerm μ 𝓕 (fr (lagAct W γ Y.1)) _ _ = _
      rw [hmove γ Y.1 g _ hF₂, ha₁.left _ (inv_mem γ.2) g]
    · intro Y
      exact ((continuous_star.comp ha₁.cont).mul (hcont ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr hS f₁ _ hf₁ hF₂ Y.1 Y.2)).aestronglyMeasurable
    · intro Y Γ hΓ 𝓓 h𝓓 hint
      obtain ⟨s, I, hI, hspan⟩ := GlobalTheory.T.exists_isotropicFrame_lagrangian_first_summand D W Y.1 Y.2
      have hle : Γ ≤ GQ W := fun g hg => ((hΓ g).1 hg).1
      have hfix : ∀ g (hg : g ∈ Γ), lagAct W ⟨g, hle hg⟩ Y.1 = Y.1 := by
        intro g hg
        obtain ⟨h, e⟩ := (hΓ g).1 hg
        exact congrArg Subtype.val e
      have key := hKill W νW hS.haarW s I hI Γ hle
        (fun n hn => (hΓ n).2 ⟨hn.2, Subtype.ext (GlobalTheory.T.rationalUnitaryLagrangianAction_eq_of_mem_frameUnipotent D W Y.1 s I hI hspan ⟨n, hn.2⟩ hn.1)⟩)
        (fun γ hγ n hn => GlobalTheory.T.lagrangianStabilizer_normalizes_frameUnipotent D W Y.1 s I hI hspan ⟨γ, hle hγ⟩ (hfix γ hγ) n hn) 𝓓 h𝓓
        (fun g => lagTerm μ 𝓕 (fr Y.1) (om (1, g) f₁) (om (1, g₂) f₂)) (fun g => star (φ₁ g))
        (hcont ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr hS f₁ _ hf₁ hF₂ Y.1 Y.2) ?_ ?_ ?_ ?_ ?_
      · rw [← key]
        congr 1
        funext g
        ring
      · intro γ hγ g
        show lagTerm μ 𝓕 (fr Y.1) (om (1, γ * g) f₁) (om (1, g₂) f₂) = lagTerm μ 𝓕 (fr Y.1) (om (1, g) f₁) (om (1, g₂) f₂)
        have := hmove ⟨γ, hle hγ⟩ Y.1 (γ * g) _ hF₂
        rw [hfix γ hγ] at this
        rw [this]
        congr 3
        exact congrArg (Prod.mk 1) (inv_mul_cancel_left γ g)
      · intro n hn g
        show lagTerm μ 𝓕 (fr Y.1) (om (1, n * g) f₁) (om (1, g₂) f₂) = lagTerm μ 𝓕 (fr Y.1) (om (1, g) f₁) (om (1, g₂) f₂)
        rw [← hom]
        exact hInv ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr hS Y.1 s I hI hspan n hn _ _ (hpres _ _ hf₁) hF₂
      · exact ⟨fun γ hγ g => by show star (φ₁ (γ * g)) = star (φ₁ g); rw [ha₁.left γ hγ g],
          by
            obtain ⟨U, hU, hk⟩ := ha₁.level
            exact ⟨U, hU, fun k hk1 hk2 g => by show star (φ₁ (g * k)) = star (φ₁ g); rw [hk k hk1 hk2 g]⟩,
          continuous_star.comp ha₁.cont⟩
      · intro r C hC μ' 𝓕' hμ' h𝓕' g
        have := hc₁ r C hC μ' 𝓕' hμ' h𝓕' g
        show ∫ n in 𝓕', (starRingEnd ℂ) (φ₁ ((n : GA D W) * g)) ∂μ' = 0
        rw [integral_conj, this, map_zero]
      · have e : (fun g => lagTerm μ 𝓕 (fr Y.1) (om (1, g) f₁) (om (1, g₂) f₂) * star (φ₁ g)) =
            fun g => star (φ₁ g) * lagTerm μ 𝓕 (fr Y.1) (om (1, g) f₁) (om (1, g₂) f₂) := funext fun g => mul_comm _ _
        show IntegrableOn (fun g => lagTerm μ 𝓕 (fr Y.1) (om (1, g) f₁) (om (1, g₂) f₂) * star (φ₁ g)) 𝓓 νW
        rw [e]
        exact hint
  have hφ₁c : Continuous φ₁ := ha₁.cont
  refine GlobalTheory.T.tsum_setIntegral_prod_eq_zero_of_inner' (X := NGLag W) inferInstance νW inferInstance 𝓖
    (fun Y p => star (φ₁ p.1) * φ₂ p.2 * lagTerm μ 𝓕 (fr Y.1) (om (1, p.1) f₁) (om (1, p.2) f₂)) ?_ ?_ ?_
  · intro Y
    have hm := GlobalTheory.RallisMeas.lagTerm_stronglyMeasurable D ψ V W χV χW om μ 𝓕 hw hS.covol f₁ f₂ hf₁ hf₂ (fr Y.1)
    exact (((continuous_star.comp hφ₁c).comp continuous_fst).mul (ha₂.cont.comp continuous_snd)).aestronglyMeasurable.mul
      hm.aestronglyMeasurable
  · have h0 := hEis ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr hS θ hθ f₁ f₂ hf₁ hf₂ φ₁ φ₂ ha₁ hc₁ ha₂ hc₂
    refine ne_top_of_le_ne_top h0 (lintegral_mono fun g₁ => lintegral_mono fun g₂ => ?_)
    have e : ∀ Y : NGLag W, ‖star (φ₁ g₁) * φ₂ g₂ * lagTerm μ 𝓕 (fr Y.1) (om (1, g₁) f₁) (om (1, g₂) f₂)‖ₑ =
        (fun Y : Lag W => ‖lagTerm μ 𝓕 (fr Y) (om (1, g₁) f₁) (om (1, g₂) f₂)‖ₑ * ‖φ₁ g₁‖ₑ * ‖φ₂ g₂‖ₑ) Y.1 := by
      intro Y
      have hs : ‖star (φ₁ g₁)‖ₑ = ‖φ₁ g₁‖ₑ := by simp [enorm_eq_nnnorm]
      simp only
      rw [enorm_mul, enorm_mul, hs]
      ring
    rw [tsum_congr e]
    exact ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective _
  · intro g₂ hfin
    by_cases h0 : φ₂ g₂ = 0
    · simp [h0]
    · have e1 : ∀ Y : NGLag W, ∫ g₁ in 𝓖, star (φ₁ g₁) * φ₂ g₂ * lagTerm μ 𝓕 (fr Y.1) (om (1, g₁) f₁) (om (1, g₂) f₂) ∂νW =
          φ₂ g₂ * ∫ g₁ in 𝓖, star (φ₁ g₁) * lagTerm μ 𝓕 (fr Y.1) (om (1, g₁) f₁) (om (1, g₂) f₂) ∂νW := by
        intro Y
        rw [← integral_const_mul]
        congr 1
        funext g₁
        ring
      have e2 : ∀ Y : NGLag W, ∫⁻ g₁ in 𝓖, ‖star (φ₁ g₁) * φ₂ g₂ * lagTerm μ 𝓕 (fr Y.1) (om (1, g₁) f₁) (om (1, g₂) f₂)‖ₑ ∂νW =
          ‖φ₂ g₂‖ₑ * ∫⁻ g₁ in 𝓖, ‖star (φ₁ g₁) * lagTerm μ 𝓕 (fr Y.1) (om (1, g₁) f₁) (om (1, g₂) f₂)‖ₑ ∂νW := by
        intro Y
        rw [← lintegral_const_mul' _ _ enorm_ne_top]
        congr 1
        funext g₁
        rw [enorm_mul, enorm_mul, enorm_mul]
        ring
      simp only at hfin ⊢
      rw [tsum_congr e2, ENNReal.tsum_mul_left] at hfin
      rw [tsum_congr e1, tsum_mul_left, hslice g₂ ?_, mul_zero]
      intro htop
      rw [htop, ENNReal.mul_top (enorm_ne_zero.2 h0)] at hfin
      exact hfin rfl

end GlobalTheory.RallisCusp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecUniqueOfLaws
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LocLanglands.Unique

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem segSum_congr (rc rc' : IrrGL (w.adicCompletion E) → WD h) (l : List (Segment (w.adicCompletion E)))
    (H : ∀ Δ ∈ l, rc Δ.first = rc' Δ.first) : segSum rc l = segSum rc' l := by
  unfold segSum
  congr 1
  exact List.map_congr_left fun Δ hΔ => by rw [H Δ hΔ]

theorem first_fst_le_of_isL {k V : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [AddCommGroup V] [Module ℂ V] {N : ℕ} {π : Representation ℂ (GL (Fin N) k) V} {𝔪 : Multiset (Segment k)}
    (hL : IsL 𝔪 π) {Δ : Segment k} (hΔ : Δ ∈ 𝔪) : Δ.first.1 ≤ N := by
  obtain ⟨_, xs, hd, ⟨Δs, ⟨hmap, -⟩, hLs⟩, -⟩ := hL
  rw [← hmap] at hΔ
  obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hΔ
  have h1 := (hLs i).deg_eq
  have h2 : (xs i).1 ≤ ∑ a, (xs a).1 := Finset.single_le_sum (f := fun a => (xs a).1) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  have h3 : (Δs i).d ≤ (Δs i).deg := Nat.le_mul_of_pos_left _ (Δs i).len_pos
  show (Δs i).d ≤ N
  omega

theorem eq_of_isCusp (hLC : LocalConverseGL) (hBZ : BernsteinZelevinskyFiniteness)
    {a : Weil h →* (w.adicCompletion E)ˣ} {ha : IsLocalArtin h a}
    {e e' : AddChar (w.adicCompletion E) Circle → WD h → ℂˣ} {rc rc' : IrrGL (w.adicCompletion E) → WD h}
    {ψ : AddChar (w.adicCompletion E) Circle} (hψc : Continuous ψ) (hψ : ψ ≠ 1) (he : e ψ = e' ψ)
    (H : LawsMin a ha e rc) (H' : LawsMin a ha e' rc') (x : IrrGL (w.adicCompletion E)) (hx : x.IsCusp)
    (ih : ∀ y : IrrGL (w.adicCompletion E), y.1 < x.1 → rc y = rc' y) : rc x = rc' x := by
  haveI : CharZero (w.adicCompletion E) :=
    charZero_of_injective_algebraMap (algebraMap E (w.adicCompletion E)).injective
  obtain ⟨n, c⟩ := x
  obtain ⟨hn, hc⟩ := hx
  rcases n with _ | m
  · exact absurd hn (lt_irrefl 0)
  rcases m with _ | m
  · obtain ⟨χ, hχ, hx⟩ := GlobalTheory.T.irreducible_GL1_is_character hBZ _ ⟨1, c⟩ rfl
    rw [hx, H.one, H'.one]
  · obtain ⟨x', hx'⟩ := H'.bij.2 (rc ⟨m + 2, c⟩)
    have hd : x'.1 = m + 2 := by
      have := H'.dim x'
      rw [hx', H.dim] at this
      exact this.symm
    have hcx' : x'.IsCusp := (H'.cusp x').2 (hx' ▸ (H.cusp _).1 ⟨hn, hc⟩)
    obtain ⟨n', c'⟩ := x'
    obtain rfl : n' = m + 2 := hd
    have hcls : ∀ d : IrrCl (GL (Fin (m + 2)) (w.adicCompletion E)), cls d.rep = ⟨m + 2, d⟩ := fun d => by
      simp [cls, IrrCl.cl_rep]
    have key : c = c' := by
      rw [← c.cl_rep, ← c'.cl_rep]
      refine IrrRep.cl_eq_iff.2 ?_
      refine hLC _ ψ hψc hψ (m + 1) (Nat.succ_pos m) c.rep c'.rep hc hcx'.2 fun τ => ?_
      have h2 : rc (cls τ) = rc' (cls τ) := ih _ (by show m + 1 < m + 2; omega)
      refine ⟨_, H.eps ψ hψc hψ (m + 1) c.rep τ hc, ?_⟩
      have h1 := H'.eps ψ hψc hψ (m + 1) c'.rep τ hcx'.2
      rw [hcls] at h1 ⊢
      rw [he, ← hx', h2]
      exact h1
    subst key
    exact hx'.symm

theorem eq_of_lawsMin : LocalConverseGL → LanglandsExhaustionGL → BernsteinZelevinskyFiniteness → ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (a : Weil h →* (w.adicCompletion E)ˣ) (ha : IsLocalArtin h a) (e : AddChar (w.adicCompletion E) Circle → WD h → ℂˣ) (rc : IrrGL (w.adicCompletion E) → WD h) (rc' : IrrGL (w.adicCompletion E) → WD h) (ψ : AddChar (w.adicCompletion E) Circle) (e' : AddChar (w.adicCompletion E) Circle → WD h → ℂˣ), Continuous ψ → ψ ≠ 1 → e ψ = e' ψ → LawsMin a ha e rc → LawsMin a ha e' rc' → rc = rc' := by
  intro hLC hEx hBZ E Ω _ _ _ _ _ A w h a ha e rc rc' ψ e' hψc hψ he H H'
  haveI : CharZero (w.adicCompletion E) :=
    charZero_of_injective_algebraMap (algebraMap E (w.adicCompletion E)).injective
  have main : ∀ n, ∀ x : IrrGL (w.adicCompletion E), x.1 = n → rc x = rc' x := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro x hxn
      obtain ⟨𝔪, h𝔪⟩ := hEx _ x
      have hL : IsL ((𝔪.toList : List _) : Multiset _) x.rep := by rwa [Multiset.coe_toList]
      rw [H.langlands _ x hL, H'.langlands _ x hL]
      refine segSum_congr rc rc' _ fun Δ hΔ => ?_
      have hle : Δ.first.1 ≤ n := hxn ▸ first_fst_le_of_isL h𝔪 (Multiset.mem_toList.1 hΔ)
      exact eq_of_isCusp hLC hBZ hψc hψ he H H' Δ.first Δ.isCusp_first
        fun y hy => ih y.1 (by omega) y rfl
  funext x
  exact main _ x rfl

end GlobalTheory.LocLanglands.Unique

end
end

