import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0023
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LatticeDataThicknessBound
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ApartAllEmpty
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0022
import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.HasLevel
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RegPolOfRepOf
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Imports
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0006
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0010
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0228
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.ArthurClozel
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0005
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0127
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParameterSphericalProductSpehQuotients
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0269
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0254
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1243
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0195
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0218
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0127
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0006
import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms.BaseChange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0305

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.BlowUpFibreSemilocal
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL GlobalTheory.CongL

namespace GlobalTheory.CongL.LimAtLU

variable {a : ℕ}

theorem int_of_mem_inf {lam : DomWeight a} {x : ℂ} (hx : x ∈ infOfWeight lam) :
    ∃ j : ℤ, ((a : ℂ) - 1) / 2 - x = j := by
  obtain ⟨k, -, rfl⟩ := Multiset.mem_map.1 hx
  exact ⟨(k : ℤ) - lam.w k, by push_cast; ring⟩

open Classical in

noncomputable def jumpsOf (lam : DomWeight a) : Multiset ℤ :=
  (infOfWeight lam).map fun z => if h : ∃ n : ℤ, ((a : ℂ) - 1) / 2 - z = n then h.choose else 0

theorem jumpsOf_map (lam : DomWeight a) :
    (jumpsOf lam).map (fun n : ℤ => (n : ℂ)) = (infOfWeight lam).map (fun z => ((a : ℂ) - 1) / 2 - z) := by
  rw [jumpsOf, Multiset.map_map]
  refine Multiset.map_congr rfl fun z hz => ?_
  have h := int_of_mem_inf hz
  simp only [Function.comp_apply, dif_pos h]
  exact h.choose_spec.symm

theorem eq_jumpsOf {lam : DomWeight a} {J : Multiset ℤ}
    (hJ : J.map (fun n : ℤ => (n : ℂ)) = (infOfWeight lam).map (fun z => ((a : ℂ) - 1) / 2 - z)) : J = jumpsOf lam :=
  Multiset.map_injective Int.cast_injective (hJ.trans (jumpsOf_map lam).symm)

theorem norm_algHom {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}
    (σ : K →ₐ[ℚ_[l]] PadicAlgCl l) (x : K) : ‖σ x‖ = ‖(x : PadicAlgCl l)‖ := by
  rw [← PadicAlgCl.spectralNorm_eq, ← PadicAlgCl.spectralNorm_eq, spectralNorm, spectralNorm,
    minpoly.algHom_eq σ σ.injective, ← minpoly.algHom_eq K.val K.val.injective]
  rfl

theorem overPl_of_induced {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] {l : ℕ}
    [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} (h : IsPlaceOver A w)
    {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] {Bw : LocBridge l E Ω (Dec (F := E) A) O}
    (hj : GlobalTheory.Pst.Induces Bw) {τ : E →+* Qbar l} {LL' : FinExt l} {τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1}
    (hτ : GlobalTheory.Pst.IsInduced Bw τ τ') : OverPl ι (ι.toRingHom.comp τ) w := by
  intro x hx
  simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply,
    RingEquiv.symm_apply_apply]
  rw [hτ]
  have h1 := norm_algHom (LL'.1.val.comp τ') ⟨Bw.j (algebraMap E Ω x), Bw.j_E x⟩
  have h2 : ‖Bw.j (algebraMap E Ω x)‖ < 1 := (hj.valuation_lt_one_iff _).1 ((h x).2 hx)
  exact h1 ▸ h2

end GlobalTheory.CongL.LimAtLU

open Classical GlobalTheory.CongL.LimAtLU in

theorem GlobalTheory.CongL.crysDRU_of_linApprox : ClosedAtL → ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a → ∀ (U : Submodule ℂ (UA E a → ℂ)), IsAutRepU U → (∀ τ : E →+* ℂ, ∃ lam, HasWeightAt U τ lam) → ∀ (r : G E Ω →* GL (Fin a) (Qbar l)) (w : HeightOneSpectrum (𝓞 E)), ((l : ℕ) : 𝓞 E) ∈ w.asIdeal → Continuous r → IsSSRep r → ∀ C : Set (G E Ω →* GL (Fin a) (Qbar l)), LinApprox r C → (∀ ρ ∈ C, Continuous ρ ∧ ∃ U' : Submodule ℂ (UA E a → ℂ), SameWtAt ι w U U' ∧ CrysDRU U' ι ρ w) → CrysDRU U ι r w := by
  intro hC E Ω _ _ _ _ _ _ l _ ι a ha U _ hW r w hwl hr hss C hlin hCC
  intro P AI hT A hA O _ _ _ Bw hBw
  choose lamF hlamF using hW
  have key : ∀ lamG : (E →+* ℂ) → DomWeight a, (∀ σ, HasWeightAt U σ (lamG σ)) →
      (IsdRAt P Bw (r.comp (Dec (F := E) A).subtype) ∧
        ∀ (τ : E →+* Qbar l) (LL' : FinExt l) (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1), IsInduced Bw τ τ' →
          IsJumpsAt P Bw (r.comp (Dec (F := E) A).subtype) τ (jumpsOf (lamG (ι.toRingHom.comp τ)))) ∧
      ((∀ ρ ∈ C, IsCrysAt P Bw (ρ.comp (Dec (F := E) A).subtype)) → IsCrysAt P Bw (r.comp (Dec (F := E) A).subtype)) := by
    intro lamG hG
    refine hC E Ω l a ha P AI hT w A hA O Bw hBw (fun τ => jumpsOf (lamG (ι.toRingHom.comp τ))) r hr hss C hlin
      (fun ρ hρ => ?_)
    obtain ⟨hcont, U', hWW, hcd⟩ := hCC ρ hρ
    have h := hcd P AI hT A hA O Bw hBw
    exact ⟨hcont, GlobalTheory.CrysSst.isSstAt_of_isCrysAt l P AI hT E Ω _ O Bw a _ h.1,
      fun τ LL' τ' hi => h.2.2 τ LL' τ' hi _ _ ((hWW _ (overPl_of_induced ι hA hBw hi) _).1 (hG _)) (jumpsOf_map _)⟩
  refine ⟨(key lamF hlamF).2 fun ρ hρ => ?_, (key lamF hlamF).1.1, fun τ LL' τ' hi lam J hl hJ => ?_⟩
  · obtain ⟨-, U', -, hcd⟩ := hCC ρ hρ
    exact (hcd P AI hT A hA O Bw hBw).1
  · let lamG := Function.update lamF (ι.toRingHom.comp τ) lam
    have hG : ∀ σ, HasWeightAt U σ (lamG σ) := by
      intro σ
      rcases eq_or_ne σ (ι.toRingHom.comp τ) with h | h
      · rw [h]
        simpa [lamG] using hl
      · show HasWeightAt U σ (Function.update lamF (ι.toRingHom.comp τ) lam σ)
        rw [Function.update_of_ne h]
        exact hlamF σ
    have e := (key lamG hG).1.2 τ LL' τ' hi
    rw [eq_jumpsOf hJ]
    simpa [lamG] using e
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CmSubfieldsCompositumClosed
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL

namespace GlobalTheory.CMSub

section Crit

open ComplexEmbedding InfinitePlace IntermediateField

theorem isCMField_of_forall_isConj (K : Type) [Field K] [NumberField K] [IsTotallyComplex K]
    {σ : K ≃ₐ[ℚ] K} (hσ : ∀ φ : K →+* ℂ, IsConj φ σ) : IsCMField K := by
  first
  | exact @_root_.GlobalTheory.CMFieldCriterion.isCMField_of_forall_isConj
  | exact _root_.GlobalTheory.CMFieldCriterion.isCMField_of_forall_isConj
  | (apply _root_.GlobalTheory.CMFieldCriterion.isCMField_of_forall_isConj <;> assumption)
  | (intros; apply _root_.GlobalTheory.CMFieldCriterion.isCMField_of_forall_isConj <;> assumption)
  | (intros; apply @_root_.GlobalTheory.CMFieldCriterion.isCMField_of_forall_isConj <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.CMFieldCriterion.isCMField_of_forall_isConj ..)

end Crit

def conjStable (Ω : Type) [Field Ω] : Subfield Ω where
  carrier := {x | ∃ y : Ω, ∀ φ : Ω →+* ℂ, φ y = starRingEnd ℂ (φ x)}
  mul_mem' := by
    rintro a b ⟨y, hy⟩ ⟨z, hz⟩
    exact ⟨y * z, fun φ => by simp [hy, hz]⟩
  one_mem' := ⟨1, fun φ => by simp⟩
  add_mem' := by
    rintro a b ⟨y, hy⟩ ⟨z, hz⟩
    exact ⟨y + z, fun φ => by simp [hy, hz]⟩
  zero_mem' := ⟨0, fun φ => by simp⟩
  neg_mem' := by
    rintro a ⟨y, hy⟩
    exact ⟨-y, fun φ => by simp [hy]⟩
  inv_mem' := by
    rintro a ⟨y, hy⟩
    exact ⟨y⁻¹, fun φ => by simp [hy]⟩

variable {Ω : Type} [Field Ω] {E : Type} [Field E] [NumberField E] [Algebra E Ω] [IsAlgClosure E Ω]

theorem nonempty_ringHom_complex (E Ω : Type) [Field Ω] [Field E] [NumberField E] [Algebra E Ω]
    [IsAlgClosure E Ω] : Nonempty (Ω →+* ℂ) := by
  let ψ : E →+* ℂ := Classical.choice (inferInstance : Nonempty _)
  letI : Algebra E ℂ := ψ.toAlgebra
  haveI : Algebra.IsAlgebraic E Ω := IsAlgClosure.isAlgebraic
  exact ⟨(IsAlgClosed.lift : Ω →ₐ[E] ℂ).toRingHom⟩

theorem exists_extend (M : IntermediateField E Ω) (ψ : M →+* ℂ) :
    ∃ φ : Ω →+* ℂ, ∀ x : M, φ x = ψ x := by
  letI : Algebra M ℂ := ψ.toAlgebra
  haveI : Algebra.IsAlgebraic E Ω := IsAlgClosure.isAlgebraic
  haveI : Algebra.IsAlgebraic M Ω := Algebra.IsAlgebraic.tower_top (K := E) M
  let f : Ω →ₐ[M] ℂ := IsAlgClosed.lift
  exact ⟨f.toRingHom, fun x => f.commutes x⟩

theorem mem_of_conj {L : IntermediateField E Ω} {x y : Ω} (hx : x ∈ L)
    (hy : ∀ φ : Ω →+* ℂ, φ y = starRingEnd ℂ (φ x)) : y ∈ L := by
  haveI : IsGalois E Ω := IsAlgClosure.isGalois E Ω
  obtain ⟨φ₀⟩ := nonempty_ringHom_complex E Ω
  rw [← InfiniteGalois.fixedField_fixingSubgroup L, IntermediateField.mem_fixedField_iff]
  intro τ hτ
  have hτx : τ x = x := (mem_fixingSubgroup_iff _).mp hτ x hx
  apply φ₀.injective
  have h1 : φ₀ (τ y) = starRingEnd ℂ (φ₀ (τ x)) := hy (φ₀.comp τ.toRingHom)
  rw [h1, hτx, hy φ₀]

theorem algebraMap_mem_conjStable [IsCMField E] (e : E) : algebraMap E Ω e ∈ conjStable Ω :=
  ⟨algebraMap E Ω (IsCMField.complexConj E e), fun φ =>
    IsCMField.complexEmbedding_complexConj E (φ.comp (algebraMap E Ω)) e⟩

def conjField (E Ω : Type) [Field Ω] [Field E] [NumberField E] [IsCMField E] [Algebra E Ω] [IsAlgClosure E Ω] :
    IntermediateField E Ω :=
  (conjStable Ω).toIntermediateField algebraMap_mem_conjStable

theorem le_conjField [IsCMField E] (M : IntermediateField E Ω) [NumberField M] [IsCMField M] :
    M ≤ conjField E Ω := fun x hx =>
  ⟨(IsCMField.complexConj M ⟨x, hx⟩ : M), fun φ =>
    IsCMField.complexEmbedding_complexConj M (φ.comp (algebraMap M Ω)) ⟨x, hx⟩⟩

theorem isCMField_of_le [IsCMField E] (M : IntermediateField E Ω) [NumberField M]
    (h : M ≤ conjField E Ω) : IsCMField M := by
  haveI : IsTotallyComplex M := isTotallyComplex_of_algebra E M
  have hc : ∀ x : M, ∃ y : M, ∀ φ : Ω →+* ℂ, φ y = starRingEnd ℂ (φ x) := fun x => by
    obtain ⟨y, hy⟩ := h x.2
    exact ⟨⟨y, mem_of_conj x.2 hy⟩, hy⟩
  choose c hc using hc
  obtain ⟨φ₀⟩ := nonempty_ringHom_complex E Ω
  have inj : ∀ a b : M, φ₀ a = φ₀ b → a = b := fun a b hab => Subtype.ext (φ₀.injective hab)
  let f : M →+* M :=
    { toFun := c
      map_one' := inj _ _ (by simp [hc])
      map_mul' := fun a b => inj _ _ (by simp [hc])
      map_zero' := inj _ _ (by simp [hc])
      map_add' := fun a b => inj _ _ (by simp [hc]) }
  have hff : ∀ x, c (c x) = x := fun x => inj _ _ (by simp [hc])
  let g : M ≃+* M := RingEquiv.ofRingHom f f (by ext x; exact congrArg Subtype.val (hff x))
    (by ext x; exact congrArg Subtype.val (hff x))
  let σ : M ≃ₐ[ℚ] M := AlgEquiv.ofRingEquiv (f := g) (fun q => by
    rw [eq_ratCast (algebraMap ℚ M) q, map_ratCast])
  refine isCMField_of_forall_isConj M (σ := σ) fun ψ => ?_
  obtain ⟨φ, hφ⟩ := exists_extend M ψ
  ext x
  rw [ComplexEmbedding.conjugate_coe_eq, RingHom.comp_apply]
  have e1 : ((σ : M →+* M) x) = c x := rfl
  rw [e1, ← hφ, ← hφ, hc]

theorem isCMField_sup_le_adjoin : ∀ (Ω : Type) [Field Ω] (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra E Ω] [IsAlgClosure E Ω], (∀ (M N : IntermediateField E Ω) [NumberField M] [NumberField N] [NumberField ↥(M ⊔ N)], IsCMField M → IsCMField N → IsCMField ↥(M ⊔ N)) ∧ (∀ (M N : IntermediateField E Ω) [NumberField M] [NumberField N], N ≤ M → IsCMField M → IsCMField N) ∧ ∀ (M : IntermediateField E Ω) [NumberField M] (S : Set Ω), (∀ x ∈ S, ∀ φ : Ω →+* ℂ, (φ x).im = 0) → M = IntermediateField.adjoin E S → IsCMField M := by
  intro Ω _ E _ _ _ _ _
  refine ⟨fun M N _ _ _ hM hN => isCMField_of_le _ (sup_le (le_conjField M) (le_conjField N)),
    fun M N _ _ hNM hM => isCMField_of_le _ (hNM.trans (le_conjField M)),
    fun M _ S hS hMS => isCMField_of_le _ ?_⟩
  rw [hMS, IntermediateField.adjoin_le_iff]
  intro x hx
  exact ⟨x, fun φ => (Complex.conj_eq_iff_im.mpr (hS x hx φ)).symm⟩

end GlobalTheory.CMSub

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CuspRepSatakeIffLocalComponentSatake
section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL

theorem GlobalTheory.Cong.satake_locComp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (π : CuspSub E a) (w : HeightOneSpectrum (𝓞 E)) (σ : SmIrr (GL (Fin a) (w.adicCompletion E))), π.IsLocComp w σ → (∀ B, (CG.mk π).HasSat w B ↔ GlobalTheory.LFun.HasSatGL w σ.ρ B) ∧ (GlobalTheory.SmGL.IsSpherical σ.ρ ↔ GlobalTheory.PRep.fixed σ.ρ (GlobalTheory.LFun.KGL w a) ≠ ⊥) := by
  intro E _ _ _ a π w σ hσ
  have hK := GlobalTheory.SmGL.SphCompletion.KO_completion (F := E) w a
  refine ⟨fun B => ⟨fun hB => ?_, fun h => GlobalTheory.HeightCounting.Blocks.hasSatGL_locRep hσ h⟩, ?_⟩
  · have hB' : GlobalTheory.LFun.HasSatGL w (π.locRep w) B := hB
    obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).1 hB'.1
    obtain ⟨y, hy0, hy⟩ := LocSph.exists_fixed_of_mem_iSup ((finRep E a).comp (locGL E a w)) σ.ρ σ.irred
      (fun f : LocSph.Maps π w σ => f.1) (fun f => f.2.2) (GlobalTheory.LFun.KGL w a : Set _) x.1 (fun e => hx0 (Subtype.ext e))
      (fun k hk => congrArg Subtype.val (GlobalTheory.LGrp.mem_fixed.1 hx k hk))
      (by rw [LocSph.iSup_range_eq π w σ hσ]; exact x.2)
    obtain ⟨B', hB''⟩ := GlobalTheory.SatInd.exists_hasSatGL_of_isIrreducible σ.smooth σ.irred
      ((Submodule.ne_bot_iff _).2 ⟨y, GlobalTheory.LGrp.mem_fixed.2 hy, hy0⟩)
    exact (GlobalTheory.HeightCounting.Blocks.hasSatGL_locRep hσ hB'').unique hB' ▸ hB''
  · unfold GlobalTheory.SmGL.IsSpherical GlobalTheory.SmGL.IsSphericalFor
    rw [hK]

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CuspRepSatakeParametersUnique
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL

namespace GlobalTheory.AboveL

theorem cg_hasSat_unique : ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (a : ℕ) (π : CG K a) (w : HeightOneSpectrum (𝓞 K)) (B B' : Multiset ℂˣ), π.HasSat w B → π.HasSat w B' → B = B' :=
  fun _ _ _ _ _ _ _ _ _ h h' => CG.HasSat.unique h h'

end GlobalTheory.AboveL
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DefiniteUnitaryLocalComponentSplitPlaceHomeomorp
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL

theorem GlobalTheory.Cong.cLoc_locU_bijective_open_continuous : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (w : HeightOneSpectrum (𝓞 E)), IsSplitAt w → Function.Bijective ((cLoc w).comp (locU a w).subtype) ∧ IsOpenMap ((cLoc w).comp (locU a w).subtype) ∧ Continuous ((cLoc w).comp (locU a w).subtype) := by
  intro E _ _ _ a w hw
  obtain ⟨e, he⟩ := GlobalTheory.locU_equiv_GL E a w hw
  have hf : ((cLoc w).comp (locU a w).subtype : locU a w → GL (Fin a) (w.adicCompletion E)) = e := by
    funext x
    exact (he x).symm
  rw [hf]
  exact ⟨e.bijective, e.toHomeomorph.isOpenMap, e.continuous⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.EigenPartLeTypePartOfPassageStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigenPart_le_typePart_of_passage : HoweUnram → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), GlobalTheory.Chain.LiftInteg D → R.WeakCharacterisation F → R.toRealDat.ExAt → SchurAll R.toRealDat → InertJunk A3 → ∀ s, A3.fam3.Ok3 s → GoodGeneric A3.A.X F.P0 F.ψ0⁻¹ → R.toRealDat.LUnif → R.PGUnit F → R.PGEquiv F → R.PLevW F → R.PThmA → (0 < R.kap ∧ ∀ i t p, 0 < R.lam3 i t p A3.A.v0) → R.PThmB → R.TrISem F A3.trI → (R.toCx3 F).PartsW false → A3.fam3.TypesSep3 → ∀ j pl cV cW, LiftDict R j A3.A.μ0 pl cV cW → ∀ (p : A3.fam3.base3.Ix) c, cxSys D.what₂.embLL ((A3.liftI j A3.A.μ0).HasRes3 (A3.fam3.tr3 j p.1)) (labW j pl cW c) → R.Wc' j c ≤ R.Wp3 j p := by
  first | exact @GlobalTheory.Hk3.Back.wc_le_wp_of_passage | exact GlobalTheory.Hk3.Back.wc_le_wp_of_passage | (intros; apply GlobalTheory.Hk3.Back.wc_le_wp_of_passage <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.EqOfNotApartOfNotSplit
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL

noncomputable section

namespace GlobalTheory.Cong.AdaptLev

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def intU (a : ℕ) (w : HeightOneSpectrum (𝓞 E)) : Subgroup (UA E a) :=
  locU a w ⊓ ⨅ (u : HeightOneSpectrum (𝓞 E)) (_ : ¬ Apart u w), (GlobalTheory.LFun.KGL u a).comap (cLoc u)

def iwaU (a : ℕ) (w : HeightOneSpectrum (𝓞 E)) : Subgroup (UA E a) :=
  intU a w ⊓ (GlobalTheory.SmGL.iwahori (w.adicCompletion E) (Fin a)).comap (cLoc w)

def levelOf (a : ℕ) (w₀ : HeightOneSpectrum (𝓞 E)) (H : HeightOneSpectrum (𝓞 E) → Subgroup (UA E a)) :
    Subgroup (UA E a) :=
  finU E a ⊓ (⨅ (u : HeightOneSpectrum (𝓞 E)) (_ : ¬ Apart u w₀), (cLoc u).ker) ⊓
    ⨅ (w : HeightOneSpectrum (𝓞 E)) (_ : Apart w w₀), ((H w).map (cLoc w)).comap (cLoc w)

variable {a : ℕ}

theorem mem_intU {w : HeightOneSpectrum (𝓞 E)} {x : UA E a} :
    x ∈ intU a w ↔ x ∈ locU a w ∧ ∀ u, ¬ Apart u w → cLoc u x ∈ GlobalTheory.LFun.KGL u a := by
  simp only [intU, Subgroup.mem_inf, Subgroup.mem_iInf, Subgroup.mem_comap]

theorem mem_levelOf {w₀ : HeightOneSpectrum (𝓞 E)} {H : HeightOneSpectrum (𝓞 E) → Subgroup (UA E a)} {x : UA E a} :
    x ∈ levelOf a w₀ H ↔ x ∈ finU E a ∧ (∀ u, ¬ Apart u w₀ → cLoc u x = 1) ∧
      ∀ w, Apart w w₀ → ∃ y ∈ H w, cLoc w y = cLoc w x := by
  simp only [levelOf, Subgroup.mem_inf, Subgroup.mem_iInf, Subgroup.mem_comap, MonoidHom.mem_ker, Subgroup.mem_map, and_assoc]

theorem not_apart_symm {w u : HeightOneSpectrum (𝓞 E)} (h : ¬ Apart w u) : ¬ Apart u w := fun h' => h (Ne.symm h')

theorem not_apart_trans {w u v : HeightOneSpectrum (𝓞 E)} (h1 : ¬ Apart w u) (h2 : ¬ Apart u v) : ¬ Apart w v :=
  fun h => h ((not_not.1 h1).trans (not_not.1 h2))

theorem locU_congr {w u : HeightOneSpectrum (𝓞 E)} (h : ¬ Apart u w) : locU a u = locU a w := by
  have e : u.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E)) := not_not.1 h
  unfold locU
  rw [e]

theorem intU_congr {w u : HeightOneSpectrum (𝓞 E)} (h : ¬ Apart u w) : intU a u = intU a w := by
  ext x
  rw [mem_intU, mem_intU, locU_congr h]
  exact and_congr_right fun _ => forall_congr' fun v =>
    ⟨fun h' hv => h' (not_apart_trans hv (not_apart_symm h)), fun h' hv => h' (not_apart_trans hv h)⟩

theorem intU_le_locU (w : HeightOneSpectrum (𝓞 E)) : intU a w ≤ locU a w := inf_le_left

theorem levelOf_le_finU (w₀ : HeightOneSpectrum (𝓞 E)) (H : HeightOneSpectrum (𝓞 E) → Subgroup (UA E a)) :
    levelOf a w₀ H ≤ finU E a := fun _ hx => (mem_levelOf.1 hx).1

theorem eq_of_not_apart_of_not_split {w u : HeightOneSpectrum (𝓞 E)} (hw : ¬ IsSplitAt w) (h : ¬ Apart u w) : u = w := by
  by_contra hne
  exact hw ⟨u, hne, not_not.1 h⟩

theorem cLoc_mem_KGL_of_not_apart {w u : HeightOneSpectrum (𝓞 E)} (h : ¬ Apart u w) (x : UA E a)
    (hx : cLoc w x ∈ GlobalTheory.LFun.KGL w a) : cLoc u x ∈ GlobalTheory.LFun.KGL u a := by
  rcases GlobalTheory.BCT.GlobLev.eq_or_eq_conjSrc (E := E) (not_not.1 h) with rfl | rfl
  · exact hx
  · exact GlobalTheory.BCT.GlobLev.integral_conjSrc x w hx

theorem mem_intU_of {w : HeightOneSpectrum (𝓞 E)} {x : UA E a} (hx : x ∈ locU a w) (hk : cLoc w x ∈ GlobalTheory.LFun.KGL w a) :
    x ∈ intU a w :=
  mem_intU.2 ⟨hx, fun _ hu => cLoc_mem_KGL_of_not_apart hu x hk⟩

theorem eq_one_of_cLoc_eq_one {w : HeightOneSpectrum (𝓞 E)} {x : UA E a} (hx : x ∈ locU a w) (h1 : cLoc w x = 1) :
    x = 1 := by
  by_cases hw : IsSplitAt w
  · exact congrArg Subtype.val (GlobalTheory.SplitPts.eq_one_of_cLoc hw ⟨x, hx⟩ h1)
  · have hall : ∀ u, cLoc u x = 1 := by
      intro u
      by_cases hu : Apart u w
      · exact ((GlobalTheory.Cong.LevelExt.mem_locU_iff x).1 hx).2 u hu
      · rw [eq_of_not_apart_of_not_split hw hu]; exact h1
    have hinf : cInf x = 1 := MonoidHom.mem_ker.1 (Subgroup.mem_inf.1 hx).1
    refine Subtype.ext (ga_ext ?_ ?_)
    · exact hinf.trans (map_one _).symm
    · rw [Subgroup.coe_one, map_one]
      refine Units.ext (Matrix.ext fun i j => FiniteAdeleRing.ext (R := 𝓞 E) E fun u => ?_)
      have := congrArg (fun g : GL (Fin a) (u.adicCompletion E) => g.val i j) (hall u)
      simp only [Units.val_one, Matrix.one_apply] at this
      refine this.trans ?_
      split_ifs with hij <;> simp [hij]

theorem eq_of_cLoc_eq {w : HeightOneSpectrum (𝓞 E)} {x y : UA E a} (hx : x ∈ locU a w) (hy : y ∈ locU a w)
    (h : cLoc w x = cLoc w y) : x = y := by
  have := eq_one_of_cLoc_eq_one (mul_mem hx (inv_mem hy)) (by rw [map_mul, map_inv, h, mul_inv_cancel])
  exact mul_inv_eq_one.1 this

theorem coe_subgroupOf_image {G : Type} [Group G] {H L : Subgroup G} (h : H ≤ L) :
    Subtype.val '' ((H.subgroupOf L : Subgroup L) : Set L) = (H : Set G) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩; exact hy
  · intro hx; exact ⟨⟨x, h hx⟩, hx, rfl⟩

theorem isCompact_of_le {w : HeightOneSpectrum (𝓞 E)} {H : Subgroup (UA E a)} (hH : H ≤ intU a w)
    (ho : IsOpen ((H.subgroupOf (locU a w)) : Set (locU a w))) (hc : IsCompact (intU a w : Set (UA E a))) :
    IsCompact (H : Set (UA E a)) := by
  have hcl : IsClosed ((H.subgroupOf (locU a w)) : Set (locU a w)) := Subgroup.isClosed_of_isOpen _ ho
  have hc' : IsCompact (((intU a w).subgroupOf (locU a w)) : Set (locU a w)) := by
    rw [Topology.IsInducing.subtypeVal.isCompact_iff, coe_subgroupOf_image (intU_le_locU w)]
    exact hc
  have h2 := (hc'.of_isClosed_subset hcl fun x hx => hH hx).image continuous_subtype_val
  rwa [coe_subgroupOf_image (hH.trans (intU_le_locU w))] at h2

end GlobalTheory.Cong.AdaptLev
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.EventuallyCofiniteUnderOfEventuallyCofinitePlace
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL
namespace GlobalTheory

theorem eventually_cofinite_under_of_eventually_cofinite :
    ∀ (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
      (P : HeightOneSpectrum (𝓞 K) → Prop), (∀ᶠ v in Filter.cofinite, P v) →
      ∀ᶠ w : HeightOneSpectrum (𝓞 M) in Filter.cofinite, P (w.under (𝓞 K)) := by
  intro K M _ _ _ _ _ P hP
  rw [Filter.eventually_cofinite] at hP ⊢
  have hfib : ∀ v : HeightOneSpectrum (𝓞 K),
      ((fun w : HeightOneSpectrum (𝓞 M) => w.under (𝓞 K)) ⁻¹' {v}).Finite := by
    intro v
    refine Set.Finite.of_finite_image (f := HeightOneSpectrum.asIdeal)
      ((IsDedekindDomain.primesOver_finite v.asIdeal (𝓞 M)).subset ?_)
      (fun a _ b _ h => HeightOneSpectrum.ext h)
    rintro _ ⟨w, hw, rfl⟩
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hw
    refine ⟨w.isPrime, ⟨?_⟩⟩
    rw [← hw]
    rfl
  exact (hP.preimage' fun v _ => hfib v).subset fun w hw => hw

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAlgebraicWeightDefiniteUnitaryAutRep
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL

namespace GlobalTheory.Cong

theorem exists_weight_of_isAutRepU : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ)
    (U : Submodule ℂ (UA E a → ℂ)), IsAutRepU U → ∃ lam : (E →+* ℂ) → DomWeight a, ∀ τ, HasWeightAt U τ (lam τ) := by
  intro E _ _ _ a U hU
  choose lam hlam using fun τ : E →+* ℂ => (GlobalTheory.DefU.AU.existsUnique_hasWt E a (GlobalTheory.DefU.AU.mk ⟨U, hU⟩) τ).exists
  exact ⟨lam, hlam⟩

end GlobalTheory.Cong
end

