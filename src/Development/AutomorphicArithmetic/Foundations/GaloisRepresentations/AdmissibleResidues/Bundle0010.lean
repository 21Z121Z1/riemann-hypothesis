import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.NewformAut0
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.RatTorsionFree
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.Bundle0004
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.FreeFlag
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.RealAway
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.AuTeichEx
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.Bundle0009
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0573
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.CharpolyConjugation.Bundle0001
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.OrdIrr
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.RealOld
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.Bundle0002
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.WeightChange
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.Bundle0011
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.AlgOfCyc
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle0008
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0122
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0062
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivOfMapEq
import Formalism.LocalToGlobal.UnitaryNorms.Bundle0002
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.GaloisRepresentationTypes.CharpolyPowTwoByTwo

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.AdmissibleResidualOfHyp
section
noncomputable section

open NumberField IsDedekindDomain IsLocalRing Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Aut UpperTheory.V.Pr

namespace UpperTheory.GalN.V

theorem dual_two {Γ k : Type} [Group Γ] [Field k] (W : Γ →* GL (Fin 2) k) : DualTw W (Matrix.GeneralLinearGroup.det.comp W) :=
  ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero !![0, 1; -1, 0] (by simp), fun s => by
    have hd : ((Matrix.GeneralLinearGroup.det.comp W s : kˣ) : k) = (W s).val.det := rfl
    rw [hd, Matrix.det_fin_two (W s).val]
    ext i j
    simp only [Matrix.mul_apply, Fin.sum_univ_two]
    fin_cases i <;> fin_cases j <;> simp <;> ring⟩

section
variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K] [Algebra K Ω]
  {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N}

def IsModularN (_ : Dat Ω K c e ψ) (ι : Qbar l ≃+* ℂ) (W : G ℚ Ω →* GL (Fin 2) (PadicAlgCl l)) : Prop :=
  (∃ f : Af.Newform (2 * e + 1), f.Att ι (Af.tw W (cycBar ℚ Ω l ^ (-(e : ℤ))))) ∧ WitQ ι W

variable {D : Dat Ω K c e ψ} {ι : Qbar l ≃+* ℂ} {W : G ℚ Ω →* GL (Fin 2) (PadicAlgCl l)}

theorem mod0 (h : D.IsModular ι W) : ∃ f : Af.Newform (2 * e + 1), f.Att ι (Af.tw W (cycBar ℚ Ω l ^ (-(e : ℤ)))) := h
end

def AutEnd2N {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] (c : Coef l) (η : G ℚ Ω →* ℤˣ)
    (Ψ : G ℚ Ω →* c.Oˣ) (σ g₁ : G ℚ Ω) (B : ValuationSubring Ω) (e : ℕ) (ι : Qbar l ≃+* ℂ) : Prop :=
  ∀ (A : Subalgebra c.O (PadicAlgCl l)) [IsDiscreteValuationRing A] [Module.Finite c.O A] (r : G ℚ Ω →* GG 3 A),
    OrdPt l η Ψ σ g₁ B r → TypeII η (UnitaryThreeInertia.push A.val r) → (∀ g ∈ η.ker, (r g).mat 1 1 = 1) →
    ∀ W : G ℚ Ω →* GL (Fin 2) (PadicAlgCl l),
      (∀ g ∈ η.ker, (W g).val = corner (UnitaryThreeInertia.push A.val r g).mat) →
      (W σ).val.trace = 0 →
      (∃ f : Af.Newform (2 * e + 1), f.Att ι (Af.tw W (cycBar ℚ Ω l ^ (-(e : ℤ))))) ∧ WitQ ι W

theorem newAdm (P : Hypotheses₂) (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (e M : ℕ)
    (he : 1 ≤ e) (W : G ℚ Ω →* GL (Fin 2) (Qbar l)) (hirr : IsIrr W)
    (hf : (∃ f : Newform (2 * e + 1), f.Att ι (tw W (cycBar ℚ Ω l ^ (-(e : ℤ))))) ∧ WitQ ι W)
    (hlev : Level l M ![(e : ℤ), -(e : ℤ)] W) (hcyc : IsCycWt l 0 (Matrix.GeneralLinearGroup.det.comp W)) :
    AdmRN ι M ![(e : ℤ), -(e : ℤ)] 0 W := by
  obtain ⟨⟨f, hf⟩, hw⟩ := hf
  exact ⟨hirr, mkQ' (newformAut0 P (2 * e + 1) (by omega) f l Ω ι W _ hf) fun _ => hw, hlev, ⟨_, hcyc, dual_two W⟩,
    Or.inr fun i j => by fin_cases i <;> fin_cases j <;> simp <;> omega⟩

end UpperTheory.GalN.V
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.MonodromyFreeOfType
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000
open UpperTheory.GalN.V
open private au_isTeich au_open from Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.AuTeichEx

namespace UpperTheory.GalN.V

variable {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
  {s : HidaSetting l L Ω} {n : ℕ} {V : s.Lev} {c : Coef l}

variable (s) in

def StFlat (σ : Submodule ℂ (UA L n → ℂ)) : Prop :=
  ∀ (u : s.St) (τ : SmIrr (GLw n (s.w u))), IsCompAlong σ (locU n (s.w u)) ((cLoc (s.w u)).comp (locU n (s.w u)).subtype) τ.ρ →
    ∀ rc, IsRec (s.hw u) rc → (rc (algNorm τ)).mono0

structure PUW (r : Resid V.frame c.O n) (ι : Qbar l ≃+* ℂ) (lam : Wt L l n) (ρ : V.frame.G₀ →* GL (Fin n) (Qbar l)) : Prop where
  pu : PU r ι lam ρ
  aut : ∃ σ : Submodule ℂ (UA L n → ℂ), IsAutRepU σ ∧ (∀ w, IsSplitAt w → ∀ τ : SmIrr (GLw n w),
      IsCompAlong σ (locU n w) ((cLoc w).comp (locU n w).subtype) τ.ρ → Af.LocGlob ι (ρ.comp V.pr) w τ) ∧
    (∀ y : Emb l (fun v : V.frame.Vl => s.w v.1), HasWeightAt σ (ι.toRingHom.comp y.res) (lam y.res).dual) ∧
    (∀ w : Plc L, w.under (𝓞 (Lp L)) ∉ V.S' → IsUnramU σ w) ∧
    (∀ w, IsSplitAt w → ∃ τ : SmIrr (GLw n w), IsCompAlong σ (locU n w) ((cLoc w).comp (locU n w).subtype) τ.ρ) ∧
    (∃ τ : SmIrr (GLw n (s.w s.v0)), IsCompAlong σ (locU n (s.w s.v0)) ((cLoc (s.w s.v0)).comp (locU n (s.w s.v0)).subtype) τ.ρ ∧
      fixd τ.ρ (Kc _ n 1) ≠ ⊥) ∧ StFlat s σ
  unl : Af.IsIrr ρ → V.S' = s.S → (((l : ℕ) : 𝓞 L) ∉ (s.w s.v0).asIdeal → UnlAt ι (ρ.comp V.pr) (s.w s.v0) (s.A s.v0)) →
    Unlinked (ρ.comp V.pr)

end UpperTheory.GalN.V
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.ROrdIrr
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af
open scoped Matrix

namespace UpperTheory.V.Sd

private theorem inf_places (K : Type) [Field K] [NumberField K] : Infinite (HeightOneSpectrum (𝓞 K)) := by
  have : Infinite (HeightOneSpectrum (𝓞 ℚ)) :=
    Infinite.of_surjective _ (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).surjective
  refine Infinite.of_surjective (fun w : HeightOneSpectrum (𝓞 K) => w.under (𝓞 ℚ)) fun v => ?_
  have := v.isMaximal
  obtain ⟨Q, hQ, hl⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 K) v.asIdeal
  exact ⟨⟨Q, hQ.isPrime, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩, HeightOneSpectrum.ext hl.over.symm⟩

private theorem hom_or {Γ C : Type} [Group Γ] [CommGroup C] (I : Subgroup Γ) (f g h : Γ →* C)
    (H : ∀ s ∈ I, f s = g s ∨ f s = h s) : (∀ s ∈ I, f s = g s) ∨ ∀ s ∈ I, f s = h s := by
  by_contra hc
  push Not at hc
  obtain ⟨⟨s, hs, e1⟩, t, ht, e2⟩ := hc
  have a := (H s hs).resolve_left e1
  have b := (H t ht).resolve_right e2
  rcases H _ (I.mul_mem hs ht) with e | e <;> simp only [map_mul] at e
  · exact e1 (mul_right_cancel (b ▸ e))
  · exact e2 (mul_left_cancel (a ▸ e))

private theorem chars_of_red {Γ : Type} [Group Γ] [TopologicalSpace Γ] {k : Type} [NormedField k] (r : Γ →* GL (Fin 2) k)
    (hc : Continuous r) (h : ¬ IsIrr r) : ∃ c d : Γ →* kˣ, Continuous c ∧ Continuous d ∧
      ∀ s, (r s : Matrix (Fin 2) (Fin 2) k).charpoly = (X - C (c s : k)) * (X - C (d s : k)) := by
  simp only [IsIrr, IsIrrSub, not_and, not_forall] at h
  obtain ⟨W, -, hW, hne⟩ := h top_ne_bot (fun _ _ _ => Submodule.mem_top)
  rw [not_or] at hne
  have h2 : Module.finrank k W < 2 := by simpa using Submodule.finrank_lt hne.2
  have h0 : Module.finrank k W ≠ 0 := fun h => hne.1 (Submodule.finrank_eq_zero.mp h)
  obtain ⟨v, hv, hall⟩ := finrank_eq_one_iff'.mp (show Module.finrank k W = 1 by omega)
  have hv0 : (v : Fin 2 → k) ≠ 0 := fun h => hv (Subtype.ext h)
  choose c₀ hc₀ using fun g => hall ⟨_, hW g v v.2⟩
  have hc1 : ∀ g, (r g : Matrix (Fin 2) (Fin 2) k) *ᵥ (v : Fin 2 → k) = c₀ g • (v : Fin 2 → k) := fun g =>
    (congrArg Subtype.val (hc₀ g)).symm
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hv0
  let c₁ : Γ →* k :=
    { toFun := c₀
      map_one' := smul_left_injective k hv0 (by simpa using (hc1 1).symm)
      map_mul' := fun s t => smul_left_injective k hv0 (by
        simp only
        rw [← hc1, map_mul, Units.val_mul, ← Matrix.mulVec_mulVec, hc1, Matrix.mulVec_smul, hc1, smul_smul, mul_comm]) }
  have hcc : Continuous c₁.toHomUnits := by
    refine Units.isEmbedding_val₀.continuous_iff.2 ?_
    have : Continuous fun g => ((r g : Matrix (Fin 2) (Fin 2) k) *ᵥ (v : Fin 2 → k)) i / (v : Fin 2 → k) i :=
      ((continuous_apply i).comp ((Units.continuous_val.comp hc).matrix_mulVec continuous_const)).div_const _
    refine this.congr fun g => ?_
    rw [hc1, Pi.smul_apply, smul_eq_mul, mul_div_cancel_right₀ _ hi]
    rfl
  have hdet : Continuous (Matrix.GeneralLinearGroup.det.comp r : Γ →* kˣ) :=
    Units.isEmbedding_val₀.continuous_iff.2 (Units.continuous_val.comp hc).matrix_det
  refine ⟨c₁.toHomUnits, Matrix.GeneralLinearGroup.det.comp r / c₁.toHomUnits, hcc, hdet.div' hcc, fun s => ?_⟩
  have n0 : c₀ s ≠ 0 := (c₁.toHomUnits s).ne_zero
  have e1 : ((c₁.toHomUnits s : kˣ) : k) = c₀ s := rfl
  have e2 : (((Matrix.GeneralLinearGroup.det.comp r / c₁.toHomUnits) s : kˣ) : k) =
      (r s : Matrix (Fin 2) (Fin 2) k).det / c₀ s := by
    rw [MonoidHom.div_apply, Units.val_div_eq_div_val, e1]; rfl
  have a0 := congrFun (hc1 s) 0
  have a1 := congrFun (hc1 s) 1
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.smul_apply, smul_eq_mul] at a0 a1
  have q : c₀ s ^ 2 - (r s : Matrix (Fin 2) (Fin 2) k).trace * c₀ s + (r s : Matrix (Fin 2) (Fin 2) k).det = 0 := by
    rw [Matrix.trace_fin_two, Matrix.det_fin_two]
    refine mul_right_cancel₀ hi ?_
    fin_cases i
    · simp only [Fin.zero_eta, Pi.zero_apply, mul_zero]
      linear_combination (r s 1 1 - c₀ s) * a0 - r s 0 1 * a1
    · simp only [Fin.mk_one, Pi.zero_apply, mul_zero]
      linear_combination (r s 0 0 - c₀ s) * a1 - r s 1 0 * a0
  have t : (r s : Matrix (Fin 2) (Fin 2) k).trace = c₀ s + (r s : Matrix (Fin 2) (Fin 2) k).det / c₀ s := by
    field_simp
    linear_combination -q
  have u : (r s : Matrix (Fin 2) (Fin 2) k).det = c₀ s * ((r s : Matrix (Fin 2) (Fin 2) k).det / c₀ s) := by
    field_simp
  rw [e1, e2, Matrix.charpoly_fin_two, t]
  conv_lhs => rw [u]
  rw [← u, map_add]
  conv_lhs => enter [2]; rw [u, map_mul]
  ring

private theorem charpoly_tri {K : Type} [Field K] (g r : GL (Fin 2) K)
    (h : ∀ i j, j < i → (g * r * g⁻¹ : GL (Fin 2) K) i j = 0) :
    (r : Matrix (Fin 2) (Fin 2) K).charpoly =
      (X - C ((g * r * g⁻¹ : GL (Fin 2) K) 0 0)) * (X - C ((g * r * g⁻¹ : GL (Fin 2) K) 1 1)) := by
  have e : ((g * r * g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).charpoly =
      (r : Matrix (Fin 2) (Fin 2) K).charpoly := by
    rw [Units.val_mul, Units.val_mul, Matrix.coe_units_inv]
    exact Matrix.charpoly_units_conj g _
  rw [← e, Matrix.charpoly_of_isUpperTriangular _ (fun i j hij => h i j hij), Fin.prod_univ_two]

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime]

private theorem cyc_ine {v : HeightOneSpectrum (𝓞 F)} {A : ValuationSubring Ω} (hl : ((l : ℕ) : 𝓞 F) ∈ v.asIdeal)
    (hA : IsPlaceOver A v) {n : ℤ} (hn : n ≠ 0) : ∃ g ∈ Ine (F := F) A, cycBar F Ω l g ^ n ≠ 1 := by
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  have : Algebra.IsAlgebraic ℚ Ω := Algebra.IsAlgebraic.trans ℚ F Ω
  have : IsAlgClosure ℚ Ω := ⟨inferInstance, inferInstance⟩
  have : IsGalois ℚ Ω := IsAlgClosure.isGalois ℚ Ω
  have hv : A.valuation (l : Ω) < 1 := by
    simpa using (hA _).2 hl
  obtain ⟨u, hu⟩ := GlobalTheory.CycDec.exists_unit_infinite_order l
  obtain ⟨σ, hσ, hσu⟩ := GlobalTheory.CycInertia.cycZ_Ine_surjective Ω l A hv u
  let K : IntermediateField ℚ Ω := (IsScalarTower.toAlgHom ℚ F Ω).fieldRange
  have : FiniteDimensional ℚ K :=
    (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom ℚ F Ω)).toLinearEquiv.finiteDimensional
  have : Finite ((Ω ≃ₐ[ℚ] Ω) ⧸ K.fixingSubgroup) :=
    Subgroup.quotient_finite_of_isOpen _ K.fixingSubgroup_isOpen
  have : K.fixingSubgroup.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  obtain ⟨N, hN, -, hmem⟩ := Subgroup.exists_pow_mem_of_index_ne_zero
    (Subgroup.FiniteIndex.index_ne_zero (H := K.fixingSubgroup)) σ
  let g : G F Ω := { (σ ^ N).toRingEquiv with
    commutes' := fun x => (IntermediateField.mem_fixingSubgroup_iff _ _).1 hmem _ ⟨x, rfl⟩ }
  have hD : σ ^ N ∈ Ine (F := ℚ) A := (Ine (F := ℚ) A).pow_mem hσ N
  have hc : cycZ F Ω l g = cycZ ℚ Ω l (σ ^ N) := rfl
  have hinj : Function.Injective
      (Units.map ((algebraMap ℚ_[l] (Qbar l)).comp PadicInt.Coe.ringHom).toMonoidHom) :=
    Units.map_injective ((algebraMap ℚ_[l] (Qbar l)).injective.comp Subtype.val_injective)
  refine ⟨g, hD, fun h => hu (N * n) (mul_ne_zero (by exact_mod_cast hN.ne') hn) (hinj ?_)⟩
  rw [map_one, ← h, cycBar, MonoidHom.comp_apply, hc, map_pow, hσu, zpow_mul, zpow_natCast, map_zpow]

end UpperTheory.V.Sd

open UpperTheory.V.Sd in
theorem UpperTheory.V.Sd.ordIrr_n :
    UpperTheory.V.Af.HypothesesH → UpperTheory.V.Sd.OrdIrr := by
  intro P F Ω _ _ _ _ _ _ l _ hl2 hs ι ξ s c m a π r hr
  by_contra hirr
  obtain ⟨c₁, c₂, hc₁, hc₂, hch⟩ := chars_of_red r hr.cont hirr

  have hI : ∀ w : HeightOneSpectrum (𝓞 F), ((l : ℕ) : 𝓞 F) ∈ w.asIdeal → ∀ A, IsPlaceOver A w →
      ∃ d : ℤ, d ≠ 0 ∧ ∀ g ∈ Ine (F := F) A, (c₁ / c₂) g = cycBar F Ω l g ^ d := by
    intro w hw A hA
    obtain ⟨κ, ⟨g, hg⟩, hκ, -⟩ := ordAbove P F Ω l hl2 hs ι ξ s c m a π r hr w hw A hA
    have hm := (hr.above w hw).2.1
    have key : ∀ t ∈ Ine (F := F) A, (X - C (c₁ t : Qbar l)) * (X - C (c₂ t : Qbar l)) =
        (X - C ((cycBar F Ω l t ^ m w 0 : (Qbar l)ˣ) : Qbar l)) * (X - C ((cycBar F Ω l t ^ m w 1 : (Qbar l)ˣ) : Qbar l)) := by
      intro t ht
      let t' : ↥(Dec (F := F) A) := ⟨t, Ine_le_Dec A ht⟩
      rw [← hch, charpoly_tri g _ (hg t').1, (hg t').2 0, (hg t').2 1, hκ 0 t' ht, hκ 1 t' ht]
    have hp : ∀ t ∈ Ine (F := F) A, c₁ t * c₂ t = cycBar F Ω l t ^ m w 0 * cycBar F Ω l t ^ m w 1 := fun t ht => by
      have := congrArg (eval 0) (key t ht)
      simp only [eval_mul, eval_sub, eval_X, eval_C, zero_sub, neg_mul_neg] at this
      exact Units.ext this
    rcases hom_or (Ine (F := F) A) c₁ (cycBar F Ω l ^ m w 0) (cycBar F Ω l ^ m w 1) (fun t ht => by
      have := congrArg (eval (c₁ t : Qbar l)) (key t ht)
      simp only [eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul] at this
      exact (mul_eq_zero.1 this.symm).imp (fun e => Units.ext (sub_eq_zero.1 e)) fun e => Units.ext (sub_eq_zero.1 e)) with h | h
    · refine ⟨m w 0 - m w 1, by omega, fun t ht => ?_⟩
      have h1 := hp t ht
      rw [h t ht, MonoidHom.zpow_apply, mul_right_inj] at h1
      rw [MonoidHom.div_apply, h t ht, h1, MonoidHom.zpow_apply, zpow_sub, div_eq_mul_inv]
    · refine ⟨m w 1 - m w 0, by omega, fun t ht => ?_⟩
      have h1 := hp t ht
      rw [h t ht, MonoidHom.zpow_apply, mul_comm (_ ^ m w 0), mul_right_inj] at h1
      rw [MonoidHom.div_apply, h t ht, h1, MonoidHom.zpow_apply, zpow_sub, div_eq_mul_inv]
  obtain ⟨χ, -, art, n, hart, hn, hL⟩ := (algOfCyc P F Ω l ι).1 (c₁ / c₂) (hc₁.div' hc₂) fun w hw => by
    obtain ⟨A, hA⟩ := exists_isPlaceOver Ω w
    obtain ⟨d, -, hd⟩ := hI w hw A hA
    exact ⟨A, hA, d, 1, one_pos, fun t ht => by rw [hd t ht, zpow_neg, mul_inv_cancel, one_pow]⟩
  obtain ⟨χ₀, hχ₀⟩ := hr.pol
  obtain ⟨-, wt, HT, -, -, hG⟩ := UpperTheory.GalN.V.exRN (exR P) F Ω l ι 2 one_le_two π χ₀ hr.reg hχ₀
  have hG := hG r hr.cont hr.att
  have h0 : Ideal.span {((l : ℕ) : 𝓞 F)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast (Fact.out : l.Prime).ne_zero
  have hl : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ((l : ℕ) : 𝓞 F) ∉ v.asIdeal :=
    (Ideal.finite_factors h0).subset fun v hv => Ideal.dvd_span_singleton.mpr (not_not.1 hv)
  obtain rfl : n = 0 := by
    have hinf : Infinite (HeightOneSpectrum (𝓞 F)) := inf_places F
    obtain ⟨w, hw, ⟨B, hB, hF⟩, hu⟩ := (hl.and (hr.att.2.and (GlobalTheory.Mem.UnrAe.unr_ae_and_level F χ).1)).exists
    obtain ⟨A, hA⟩ := exists_isPlaceOver Ω w
    have hR := UpperTheory.GalN.V.ratioW_of_hasSat P.toClassicalTheorems hG hw hA hB
    have r1 : ((r ((frob hA : Weil hA) : G F Ω)⁻¹ : Matrix (Fin 2) (Fin 2) (Qbar l)).charpoly.map ι.toRingHom).IsRoot
        (ι (c₁ (frob hA : G F Ω)⁻¹ : Qbar l)) := IsRoot.map (f := ι.toRingHom) (by rw [hch]; simp)
    have r2 : ((r ((frob hA : Weil hA) : G F Ω)⁻¹ : Matrix (Fin 2) (Fin 2) (Qbar l)).charpoly.map ι.toRingHom).IsRoot
        (ι (c₂ (frob hA : G F Ω)⁻¹ : Qbar l)) := IsRoot.map (f := ι.toRingHom) (by rw [hch]; simp)
    have e1 := UpperTheory.GalN.V.ratio_roots hr.cont hw hR r1 r2
    have e2 := UpperTheory.GalN.V.ratio_roots hr.cont hw hR r2 r1
    have e3 := hL.frob_unr hart (Or.inl hw) hu hA (isFrob_frob (h := hA))
    have e4 : ((χ.val w : ℂˣ) : ℂ) = ι (c₁ (frob hA : G F Ω)⁻¹) / ι (c₂ (frob hA : G F Ω)⁻¹) := by
      rw [← map_div₀, ← Units.val_div_eq_div_val, ← MonoidHom.div_apply, map_inv, Units.val_inv_eq_inv_val, e3, inv_inv,
        RingEquiv.apply_symm_apply]
    have p2 : 0 < ‖ι (c₂ (frob hA : G F Ω)⁻¹ : Qbar l)‖ := norm_pos_iff.2 ((map_ne_zero ι).2 (Units.ne_zero _))
    refine UpperTheory.GalN.V.type_zero_window χ n hn w ?_ ?_
    · rw [e4, norm_div, div_lt_iff₀ p2]; exact e1
    · rw [e4, norm_div, ← mul_div_assoc, lt_div_iff₀ p2, one_mul]; exact e2
  obtain ⟨w, hw⟩ : ∃ w : HeightOneSpectrum (𝓞 F), ((l : ℕ) : 𝓞 F) ∈ w.asIdeal := by
    have hne : Ideal.span {((l : ℕ) : 𝓞 F)} ≠ ⊤ := fun e => by
      have := congrArg Ideal.absNorm e
      rw [Ideal.absNorm_span_natCast, Ideal.absNorm_top, pow_eq_one_iff] at this
      rcases this with h | h
      · exact (Fact.out : l.Prime).ne_one h
      · exact Module.finrank_pos.ne' h
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
    exact ⟨⟨M, hM.isPrime, fun e => h0 (le_bot_iff.1 (e ▸ hle))⟩, hle (Ideal.mem_span_singleton_self _)⟩
  obtain ⟨A, hA⟩ := exists_isPlaceOver Ω w
  obtain ⟨d, hd0, hd⟩ := hI w hw A hA
  obtain ⟨N, hN, hu⟩ := GlobalTheory.Corev.UnrPow.exists_pow_unrAt F χ
  obtain ⟨g, hg, hne⟩ := cyc_ine hw hA (n := d * N) (mul_ne_zero hd0 (by exact_mod_cast hN.ne'))
  obtain ⟨x, hx, e⟩ := (hL.ine_image hart (Or.inr rfl) hA _).1 ⟨g, hg, rfl⟩
  have e2 : χ.loc w x ^ N = 1 := hu w x hx
  refine hne (Units.ext ?_)
  rw [zpow_mul, zpow_natCast, ← hd g hg, Units.val_pow_eq_pow_val, ← e, ← map_pow, ← Units.val_pow_eq_pow_val, e2]
  simp
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.RigEnd2W
section
open private irr2 pair2 freeRes from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.GaloisRepresentationTypes.CharpolyPowTwoByTwo
open UpperTheory.GalN.V

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.HV GlobalTheory.GalOfCusp UpperTheory.V.Th

open UpperTheory.V.U3 UpperTheory.V.Base in

def UpperTheory.GalN.V.RigEnd2W : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (c : Coef l)
    [CharP (ResidueField c.O) l] (N : ℕ) [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N) (η : G ℚ Ω →* ℤˣ) (σ g₁ : G ℚ Ω)
    (B : ValuationSubring Ω) (M : ℕ), Pr.LinkHyp c N e η σ B M → Chr.Psi l e (Chr.dirG ℚ Ω ψ) σ = 1 →
    Pr.HasFrame c η (Chr.Psi l e (Chr.dirG ℚ Ω ψ)) σ B M →
    ∀ (A : Subalgebra c.O (PadicAlgCl l)) [IsDiscreteValuationRing A] [Module.Finite c.O A] (r : G ℚ Ω →* GG 3 A),
      Pr.OrdPt l η (Chr.Psi l e (Chr.dirG ℚ Ω ψ)) σ g₁ B r → TypeII η (UnitaryThreeInertia.push A.val r) → (∀ g ∈ η.ker, (r g).mat 1 1 = 1) →
      ∀ (K : Type) [Field K] [NumberField K] [IsCMField K] [Algebra K Ω], Module.finrank ℚ K = 2 → η.ker = galOf ℚ K Ω →
      ∀ W : G ℚ Ω →* GL (Fin 2) (Qbar l), Continuous W → (∀ g ∈ η.ker, (W g).val = corner (UnitaryThreeInertia.push A.val r g).mat) →
      (∀ g, (W g).val.det = ((η g : ℤˣ) : ℤ)) →
      (∃ π : GlobalTheory.CuspRep.CuspSub K 2, (GlobalTheory.CuspRep.CG.mk π).IsRegAlg ∧
        Af.AttC ι (W.comp (AlgEquiv.restrictScalarsHom ℚ : G K Ω →* G ℚ Ω)) π) →
      Wit ι (W.comp (AlgEquiv.restrictScalarsHom ℚ : G K Ω →* G ℚ Ω)) → FreeAt l W → AdZero2 K η W
end

