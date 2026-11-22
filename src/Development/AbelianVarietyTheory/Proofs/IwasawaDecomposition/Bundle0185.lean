import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0173
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0001
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0155
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0161
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0159
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0169
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0067
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0001
import Formalism.LocalToGlobal.IndefiniteReal.HeckeTupleStatement
import Formalism.LocalRingCardinality.Bundle0007
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0004
import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0036
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
import Formalism.LocalToGlobal.ProjectiveLattices.DepthTie
import Formalism.LocalToGlobal.UnitaryNorms.MemFIffReal
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.SpanPowerMembership
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0174
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0164
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.IsPrincipalMapOfAlgHom
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemConnectedComponentOfOneOfPos
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0009
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0172
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0176
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0175
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0007
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0149
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0166
import Development.AbelianVarietyTheory.Proofs.HeightProofs.LeOfFiniteSplitNotSplitBauer
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalStageNonemptyStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_stage_nonempty : Nonempty GlobalTheory.Mem.LocStage := by
  first | exact @GlobalTheory.Mem.nonempty_locStage | exact GlobalTheory.Mem.nonempty_locStage | (intros; apply GlobalTheory.Mem.nonempty_locStage <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalizationTensorNormalOfCharZero
section
open IsLocalRing GlobalTheory.Toroidal TensorProduct

set_option maxHeartbeats 1000000 in

theorem GlobalTheory.TensorNormal.localization_tensor_normal_of_charZero : ∀ (A C R : Type) [CommRing A] [IsLocalRing A] [Algebra.EssFiniteType ℤ A] [CommRing C] [Algebra A C] [Algebra.EssFiniteType A C] [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [Algebra A R], (∀ (P : Ideal C) [P.IsPrime], IsDomain (Localization.AtPrime P) ∧ IsIntegrallyClosed (Localization.AtPrime P) ∧ CharZero (Localization.AtPrime P)) → IsEtaleCompletion (algebraMap A R) → ((residue R).comp (algebraMap A R)).FormallyUnramified → ∀ (Q : Ideal (TensorProduct A C R)) [Q.IsPrime], IsDomain (Localization.AtPrime Q) ∧ IsIntegrallyClosed (Localization.AtPrime Q) ∧ IsNoetherianRing (Localization.AtPrime Q) := by
  intro A C R _ _ _ _ _ _ _ _ _ _ hC hEt hFU Q _
  have hnoeth : IsNoetherianRing (Localization.AtPrime Q) := by
    haveI : IsNoetherianRing (R ⊗[A] C) := Algebra.EssFiniteType.isNoetherianRing R (R ⊗[A] C)
    haveI : IsNoetherianRing (C ⊗[A] R) :=
      isNoetherianRing_of_ringEquiv _ (Algebra.TensorProduct.comm A R C).toRingEquiv
    infer_instance
  suffices h : IsDomain (Localization.AtPrime Q) ∧ IsIntegrallyClosed (Localization.AtPrime Q) from
    ⟨h.1, h.2, hnoeth⟩
  obtain ⟨Q', _, hQ'm, htr⟩ := GlobalTheory.T.tensor_prime_contraction_maximal A C R Q
  set P := Q.comap (Algebra.TensorProduct.includeLeft : C →ₐ[A] C ⊗[A] R) with hP
  set B := Localization.AtPrime P
  obtain ⟨hBd, hBi, hBc⟩ := hC P
  haveI := hBd; haveI := hBi; haveI := hBc
  haveI : Algebra.EssFiniteType C B := .of_isLocalization B P.primeCompl
  haveI : Algebra.EssFiniteType A B := .comp A C B
  set W' := Localization.AtPrime Q'
  let k := ResidueField W'
  let φ : B →+* k := (residue W').comp ((algebraMap (B ⊗[A] R) W').comp
    (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] R).toRingHom)
  let ρ : R →+* k := (residue W').comp ((algebraMap (B ⊗[A] R) W').comp
    (Algebra.TensorProduct.includeRight : R →ₐ[A] B ⊗[A] R).toRingHom)
  obtain ⟨V, hV, hVloc⟩ := IsLocalRing.exists_factor_valuationRing ρ
  have hker : RingHom.ker φ = maximalIdeal B := by
    ext b
    rw [RingHom.mem_ker, ← hQ'm, Ideal.mem_comap]
    change residue W' (algebraMap _ W' ((Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] R) b)) = 0 ↔ _
    rw [residue_eq_zero_iff]
    exact IsLocalization.AtPrime.to_map_mem_maximal_iff W' Q' _
  have hφρ : ∀ a : A, φ (algebraMap A B a) = ρ (algebraMap A R a) := fun a => by
    simp only [φ, ρ, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes]
  have ha1 : ∀ a : A, V.valuation (φ (algebraMap A B a)) ≤ 1 := fun a => by
    rw [hφρ, ValuationSubring.valuation_le_one_iff]; exact hV _
  have ha2 : ∀ a ∈ maximalIdeal A, V.valuation (φ (algebraMap A B a)) < 1 := fun a ha => by
    have hR : algebraMap A R a ∈ maximalIdeal R := hEt.2.1 ▸ Ideal.mem_map_of_mem _ ha
    have hm : ρ.codRestrict V.toSubring hV (algebraMap A R a) ∈ maximalIdeal V := fun hu =>
      hR (IsUnit.of_map (ρ.codRestrict V.toSubring hV) _ hu)
    rw [hφρ]
    exact (ValuationSubring.valuation_lt_one_iff V _).1 hm
  obtain ⟨D, _, _, _, _, ι, hDi, hDe, hinj, hv1, hvm, hsurj⟩ := GlobalTheory.T.exists_local_domain_valuation_dominated A B k φ V hker ha1 ha2
  haveI := hDi; haveI := hDe
  haveI : CharZero D := ⟨fun m n h => Nat.cast_injective (R := B) (by simpa using congrArg ι h)⟩
  haveI : Algebra.EssFiniteType ℤ D := .comp ℤ A D
  have hunit1 : ∀ d : D, IsUnit d → V.valuation (φ (ι d)) = 1 := fun d hd => by
    obtain ⟨u, rfl⟩ := hd
    have h1 := hv1 u
    have h2 := hv1 ↑u⁻¹
    have h3 : V.valuation (φ (ι u)) * V.valuation (φ (ι ↑u⁻¹)) = 1 := by
      rw [← map_mul, ← map_mul, ← map_mul, Units.mul_inv, map_one, map_one, map_one]
    exact le_antisymm h1 (by
      by_contra hlt
      push_neg at hlt
      have := mul_lt_one_of_lt_of_le hlt h2
      rw [h3] at this
      exact lt_irrefl _ this)
  haveI : IsLocalHom (algebraMap A D) := ⟨fun a ha => by
    by_contra hna
    have hv := hunit1 _ ha
    rw [AlgHom.commutes] at hv
    exact (ha2 a ((mem_maximalIdeal a).2 hna)).ne hv⟩
  let ψ : D ⊗[A] R →ₐ[A] W' := (IsScalarTower.toAlgHom A (B ⊗[A] R) W').comp
    (Algebra.TensorProduct.map ι (AlgHom.id A R))
  let θ : D ⊗[A] R →+* k := (residue W').comp ψ.toRingHom
  have hθt : ∀ (d : D) (r : R), θ (d ⊗ₜ r) = φ (ι d) * ρ r := fun d r => by
    simp only [θ, φ, ρ, ψ, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.comp_apply,
      Algebra.TensorProduct.map_tmul, AlgHom.id_apply, IsScalarTower.coe_toAlgHom',
      Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply, ← map_mul,
      Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  have hθt1 : ∀ d : D, θ (d ⊗ₜ[A] (1 : R)) = φ (ι d) := fun d => by
    simp only [θ, φ, ψ, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.comp_apply,
      Algebra.TensorProduct.map_tmul, AlgHom.id_apply, IsScalarTower.coe_toAlgHom',
      Algebra.TensorProduct.includeLeft_apply]
  have hθ0 : ∀ x, θ x = residue W' (algebraMap (B ⊗[A] R) W' (Algebra.TensorProduct.map ι (AlgHom.id A R) x)) :=
    fun x => rfl
  clear_value θ
  have hθV : ∀ x, θ x ∈ V := fun x => by
    induction x using TensorProduct.induction_on with
    | zero => simpa using V.zero_mem
    | tmul d r => rw [hθt]; exact V.mul_mem _ _ ((ValuationSubring.valuation_le_one_iff V _).1 (hv1 d)) (hV r)
    | add x y hx hy => rw [map_add]; exact V.add_mem _ _ hx hy
  let θV : D ⊗[A] R →+* V := θ.codRestrict V.toSubring hθV
  let q : Ideal (D ⊗[A] R) := (maximalIdeal V).comap θV
  have hmq : ∀ d ∈ maximalIdeal D, d ⊗ₜ[A] (1 : R) ∈ q := by
    intro d hd
    rw [Ideal.mem_comap]
    refine (ValuationSubring.valuation_lt_one_iff V _).2 ?_
    have e2 := hθt1 d
    have e : ((θV (d ⊗ₜ[A] (1 : R)) : V) : k) = θ (d ⊗ₜ[A] (1 : R)) := rfl
    exact (congrArg V.valuation (e.trans e2)).trans_lt (hvm d hd)
  have hQq : Q'.comap (Algebra.TensorProduct.map ι (AlgHom.id A R)) ≤ q := by
    intro x hx
    have h0 : θ x = 0 := by
      rw [hθ0, residue_eq_zero_iff]
      exact (IsLocalization.AtPrime.to_map_mem_maximal_iff W' Q' _).2 hx
    show θV x ∈ maximalIdeal V
    have : θV x = 0 := Subtype.ext h0
    rw [this]; exact zero_mem _
  obtain ⟨hTn, hTl, hTf, hTm, hTfin, hTfu⟩ := GlobalTheory.T.tensor_localization_noetherian A D R hEt hFU q hmq
  obtain ⟨c1, c2⟩ := GlobalTheory.T.completion_normal_of_unramified D (Localization.AtPrime q) _ hTn hTl hTf hTm hTfin hTfu
  haveI := hTn
  obtain ⟨t1, t2⟩ := GlobalTheory.T.domain_integrally_closed_of_completion _ c1 c2
  obtain ⟨w1, w2⟩ := GlobalTheory.T.tensor_localization_normal_domain A B D R ι hinj hsurj Q' q hQq t1 t2
  exact htr w1 w2
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocallyCompactSecondCountableT2
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MemberAdelicTop

theorem locallyCompact_secondCountable_t2 : ∀ (D : D7) (V : HSp D), LocallyCompactSpace (GA D V) ∧ SecondCountableTopology (GA D V) ∧ T2Space (GA D V) := fun D V =>
  GlobalTheory.AdelicUnitaryTop.lcsc_adelicUnitary D.host.F D.host.E D.sp.cm.sig V.rank V.gram

end GlobalTheory.MemberAdelicTop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemFOAssembledIff
section
open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem
open Formalism.L2.Pj

namespace GlobalTheory.Mem

theorem mem_FO_assembled_iff :
    ∀ (X : Stages) (z : ℂ), z ∈ FO X.toD7 ↔ ∃ x ∈ X.B.Ks, X.B.embLL x = z := by
  intro X z
  have hphi : ∀ y : 𝓞 X.B.Ks, X.toD7.what₂.phiO y = X.B.embLL ((y : X.B.Ks) : X.B.LL) := fun _ => rfl
  constructor
  · intro hz
    have hle : FO X.toD7 ≤ X.B.Ks.map X.B.embLL.toRatAlgHom := by
      rw [FO, IntermediateField.adjoin_le_iff]
      rintro _ ⟨y, rfl⟩
      exact ⟨((show 𝓞 X.B.Ks from y : X.B.Ks) : X.B.LL), SetLike.coe_mem _, (hphi y).symm⟩
    obtain ⟨x, hx, rfl⟩ := hle hz
    exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨a, b, -, hab⟩ := IsFractionRing.div_surjective (A := 𝓞 X.B.Ks) (⟨x, hx⟩ : X.B.Ks)
    have hx' : x = ((a : X.B.Ks) : X.B.LL) / ((b : X.B.Ks) : X.B.LL) := by
      have := congrArg (fun t : X.B.Ks => (t : X.B.LL)) hab
      exact this.symm
    rw [hx', map_div₀, ← hphi a, ← hphi b]
    exact div_mem (phiO_mem_FO _ _) (phiO_mem_FO _ _)

end GlobalTheory.Mem
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyAlgHomRayField
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem.Fld

namespace GlobalTheory.UnramInRay

theorem isModulus_of_top {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    {χ : (L ≃ₐ[K] L) →* ℂˣ} (h : IsModulus L χ ⊤) {𝔪 : Ideal (𝓞 K)} (hm : 𝔪 ≠ ⊥) : IsModulus L χ 𝔪 := by
  refine ⟨hm, fun 𝔭 _ => h.2.1 𝔭 fun hd => 𝔭.isPrime.ne_top (top_le_iff.1 (Ideal.le_of_dvd hd)), ?_⟩
  rintro α β ⟨ha, hb, -, -, -, hpos⟩
  have hc : ∀ I : Ideal (𝓞 K), IsCoprime I ⊤ := fun I => Ideal.isCoprime_iff_sup_eq.2 (sup_top_eq I)
  exact h.2.2 α β ⟨ha, hb, hc _, hc _, Submodule.mem_top, hpos⟩

theorem nonempty_algHom_rayField : GlobalArtinReciprocity → ∀ (K L R : Type) [Field K] [NumberField K]
    [IsTotallyComplex K] [Field L] [NumberField L] [Algebra K L] [IsAbelianGalois K L] [Field R] [NumberField R]
    [Algebra K R] (𝔪 : Ideal (𝓞 K)), 𝔪 ≠ ⊥ → IsRayField K R 𝔪 →
    (∀ 𝔭 : HeightOneSpectrum (𝓞 K), UnramIn L 𝔭) → Nonempty (L →ₐ[K] R) := by
  intro H K L R _ _ _ _ _ _ _ _ _ _ 𝔪 hm hR hL
  have := hR.1
  exact rayClassFieldMaximalSt_holds K R L 𝔪 hm hR.2 fun χ =>
    isModulus_of_top (GlobalTheory.UnramModulus.isModulus_top H K L hL χ) hm

end GlobalTheory.UnramInRay

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyRecordOfLocStage
section
open Formalism.BasicNotions

namespace GlobalTheory.Mem

theorem nonempty_record_of_locStage : Nonempty D7 := by
  obtain ⟨L⟩ := GlobalTheory.Mem.nonempty_locStage
  exact Formalism.BasicNotions.Examples₂.nonempty_D7_of_localGap ⟨L.loc, L.locA, L.locT⟩

end GlobalTheory.Mem
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormOneDetEqOneStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV GlobalTheory.QNormal GlobalTheory.Mem.Col2.IdxEx
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_one_det_eq_one : ∀ (F : Type) [Field F] (n c : ℕ), ∀ r ∈ Loc.N1 F n c, LinearEquiv.det r = 1 := by
  first | exact @GlobalTheory.Mem.Col2.IdxEx.det_eq_one_of_mem_unip | exact GlobalTheory.Mem.Col2.IdxEx.det_eq_one_of_mem_unip | (intros; apply GlobalTheory.Mem.Col2.IdxEx.det_eq_one_of_mem_unip <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PrincipalIdealSt
section
open NumberField IsDedekindDomain GlobalTheory.NT GlobalTheory.Mem.Fld GlobalTheory.Published

theorem GlobalTheory.Published.GlobalArtinReciprocity.principalIdealSt (H : GlobalArtinReciprocity) : PrincipalIdealSt := by
  intro K L _ _ _ _ _ _ h 𝔞
  have hKL := h.1
  have : IsTotallyComplex L := isTotallyComplex_of_algebra K L
  obtain ⟨N, _, _, _, hN⟩ := rayField_iff.1 H.rayClassFieldSt L ⊤ top_ne_bot
  let : Algebra K N := ((algebraMap L N).comp (algebraMap K L)).toAlgebra
  have : IsScalarTower K L N := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have := GlobalTheory.RayTopGalois.isGalois_of_isRayField_top K L N hN
  have := hN.1
  have h' := (GlobalTheory.HilbertClass.isRayField_top_iff L).1 h
  have hN' := (GlobalTheory.HilbertClass.isRayField_top_iff N).1 hN
  have hun := GlobalTheory.Mem.UnramTower.unramIn_trans K L N h'.2.1 hN'.2.1
  have hker : (AlgEquiv.restrictNormalHom (F := K) (K₁ := N) L).ker = commutator (N ≃ₐ[K] N) := by
    refine le_antisymm ?_ ?_
    · let M := IntermediateField.fixedField (commutator (N ≃ₐ[K] N))
      have : IsAbelianGalois K M := by
        have : IsMulCommutative (M ≃ₐ[K] M) := ⟨⟨fun a b => by
          obtain ⟨a, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := M) N a
          obtain ⟨b, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := M) N b
          rw [← commutatorElement_eq_one_iff_mul_comm, ← map_commutatorElement, ← MonoidHom.mem_ker,
            IntermediateField.restrictNormalHom_ker, IntermediateField.fixingSubgroup_fixedField]
          exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)⟩⟩
        exact {}
      obtain ⟨f⟩ := rayClassFieldMaximalSt_holds K L M ⊤ top_ne_bot h.2
        (GlobalTheory.UnramModulus.isModulus_top_of_isTotallyComplex H K M fun 𝔭 => GlobalTheory.RayMaximal.unramIn_of_tower (hun 𝔭))
      intro σ hσ
      rw [← IntermediateField.fixingSubgroup_fixedField (commutator (N ≃ₐ[K] N)), IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      let g : M →ₐ[K] N := (IsScalarTower.toAlgHom K L N).comp f
      have hr : g.fieldRange = M := by
        rw [AlgHom.fieldRange_of_normal]
      obtain ⟨y, rfl⟩ : x ∈ g.fieldRange := hr.symm ▸ hx
      have := σ.restrictNormal_commutes L (f y)
      rw [show σ.restrictNormal L = 1 from hσ] at this
      exact this.symm
    · rw [commutator_def, Subgroup.commutator_le]
      intro a _ b _
      rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact mul_comm' _ _
  induction 𝔞 using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => rw [Ideal.zero_eq_bot, Ideal.map_bot]; infer_instance
  | h₂ I hI => rw [Ideal.isUnit_iff.1 hI, Ideal.map_top]; infer_instance
  | h₃ I p _ hp ih =>
    let 𝔭 : HeightOneSpectrum (𝓞 K) := ⟨p, Ideal.isPrime_of_prime hp, hp.ne_zero⟩
    have hP : (p.map (algebraMap (𝓞 K) (𝓞 L))).IsPrincipal := by
      refine (hN'.2.2.2 _ (Ideal.map_ne_bot_of_ne_bot hp.ne_zero)).1 fun χ => ?_
      obtain ⟨σ, hσ⟩ := GlobalTheory.NT.exists_isFrob N 𝔭
      let r : (N ≃ₐ[L] N) →* (AlgEquiv.restrictNormalHom (F := K) (K₁ := N) L).ker :=
        { toFun := fun τ => ⟨τ.restrictScalars K, AlgEquiv.ext fun x => (algebraMap L N).injective
            (((τ.restrictScalars K).restrictNormal_commutes L x).trans (τ.commutes x))⟩
          map_one' := rfl
          map_mul' := fun _ _ => rfl }
      have hr : Function.Bijective r := ⟨fun a b e => AlgEquiv.ext fun x => congrArg (fun t => t.1 x) e, fun t =>
        ⟨AlgEquiv.ofRingEquiv (f := t.1.toRingEquiv) fun x => by
          have := t.1.restrictNormal_commutes L x
          rw [show t.1.restrictNormal L = 1 from t.2] at this
          exact this.symm, rfl⟩⟩
      let φ := χ.comp (MulEquiv.ofBijective r hr).symm.toMonoidHom
      have hv := GlobalTheory.FrobTransfer.heckeIdeal_map_eq_transfer K L N 𝔭 (hun 𝔭) σ hσ χ φ fun τ _ => congrArg χ ((MulEquiv.ofBijective r hr).symm_apply_apply τ)
      have key : ∀ (A : Subgroup (N ≃ₐ[K] N)) (_ : A = commutator _) (ψ : A →* ℂˣ), MonoidHom.transfer ψ = 1 := by
        rintro _ rfl ψ
        exact GlobalTheory.TransferCommutator.transfer_eq_one _ _ ψ
      rw [key _ hker φ] at hv
      exact hv
    obtain ⟨a, ha⟩ := hP
    obtain ⟨b, hb⟩ := ih
    rw [Ideal.map_mul, ha, hb]
    exact ⟨a * b, Ideal.span_singleton_mul_span_singleton a b⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ProjConjLevelLeIntegralGLAtTypePrimeStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV GlobalTheory.QNormal GlobalTheory.Mem.Col2.IdxEx
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.projConjLevel_le_integralGL_at_typePrime : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (sharp : Bool) (j : ℕ) (P : HeightOneSpectrum (𝓞 X.E)), P ∈ Pr.vGs → ∀ h ∈ stabL X.E _ (lamYat (Pr := Pr) (R := R) j P), prCat (Pr := Pr) sharp j P h ≤ GLint X.E (R.N j) P := by
  first | exact @GlobalTheory.Mem.Col2.IdxEx.prCat_le_GLint | exact GlobalTheory.Mem.Col2.IdxEx.prCat_le_GLint | (intros; apply GlobalTheory.Mem.Col2.IdxEx.prCat_le_GLint <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RayClassFieldSplitsInOfIsRayPrimeStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rayClassField_splitsIn_of_isRayPrime : ∀ (D : D7) (jE : D.host.E →+* Qb) (M : Fld) (h : KQbar D jE ≤ M) (hf : FiniteDimensional ℚ M),
    letI := GlobalTheory.ParRay.algK D jE h
    haveI := GlobalTheory.ParRay.nfOf hf
    GlobalTheory.Mem.Fld.IsRayField D.host.K M (GlobalTheory.Mem.RaySplit.condIdeal D.host) →
      ∀ p, IsRayPrime (KQbar D jE) (D.host.QS * D.host.q * D.host.d) p → SplitsIn M p := by
  first | exact @GlobalTheory.ParRay.rayField_splitsIn_of_isRayPrime | exact GlobalTheory.ParRay.rayField_splitsIn_of_isRayPrime | (intros; apply GlobalTheory.ParRay.rayField_splitsIn_of_isRayPrime <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RePosOfIsMultIP
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SchurConst

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

theorem left_cont_of_mem (θ : InfFam D) (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ) (T : MMap M)
    (hT : T ∈ Mult θ M J χ) (v : M.Vec) :
    Continuous (T v) ∧ ∀ γ ∈ GQ V, ∀ g, T v (γ * g) = T v g := by
  unfold Mult at hT
  induction hT using Submodule.span_induction with
  | mem x hx => exact ⟨(IsMultMap.aut hx v).cont, (IsMultMap.aut hx v).left⟩
  | zero => exact ⟨continuous_const, fun _ _ _ => rfl⟩
  | add x y _ _ hx hy =>
    refine ⟨hx.1.add hy.1, fun γ hγ g => ?_⟩
    show x v (γ * g) + y v (γ * g) = x v g + y v g
    rw [hx.2 γ hγ, hy.2 γ hγ]
  | smul a x _ hx =>
    refine ⟨hx.1.const_smul a, fun γ hγ g => ?_⟩
    show a • x v (γ * g) = a • x v g
    rw [hx.2 γ hγ]

theorem eq_zero_of_ae (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) (hμ : μ.IsHaarMeasure)
    (hF : IsFundamentalDomain (GQ V) 𝓕 μ) (φ : GA D V → ℂ) (hc : Continuous φ)
    (hL : ∀ γ ∈ GQ V, ∀ g, φ (γ * g) = φ g) (h2 : ∀ᵐ g ∂(μ.restrict 𝓕), φ g = 0) : φ = 0 := by
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA D.sp.cm.sig V.gram
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableMulHA D.sp.cm.sig V.gram
  have : Countable (GQ V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma D.sp.cm.sig V.gram
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableConstSMul_subgroup (GQ V)
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.smulInvariant_subgroup (GQ V) μ
  let t : Set (GA D V) := {g | φ g ≠ 0}
  have ht : IsOpen t := hc.isOpen_preimage _ isOpen_ne
  have htm : MeasurableSet t := ht.measurableSet
  have h3 : μ (t ∩ 𝓕) = 0 := by
    rw [← Measure.restrict_apply htm]
    exact ae_iff.1 h2
  have hinv : ∀ γ : GQ V, γ • t = t := by
    intro γ
    ext g
    rw [Set.mem_smul_set_iff_inv_smul_mem]
    show φ (((γ⁻¹ : GQ V) : GA D V) * g) ≠ 0 ↔ φ g ≠ 0
    rw [hL _ (γ⁻¹).2]
  have h4 : μ t = 0 := hF.measure_zero_of_invariant t hinv h3
  have h5 : t = ∅ := (ht.measure_eq_zero_iff μ).1 h4
  funext g
  by_contra hg
  have : g ∈ t := hg
  rw [h5] at this
  exact this

theorem exists_vec (M : DSModel V S) (h : ∀ τ, M.sm τ ≠ ⊥) :
    ∃ v : M.Vec, ∏ τ, ⟪(v τ : M.H τ), (v τ : M.H τ)⟫_ℂ ≠ 0 := by
  choose w hw hw0 using fun τ => (Submodule.ne_bot_iff _).1 (h τ)
  refine ⟨fun τ => ⟨w τ, hw τ⟩, Finset.prod_ne_zero_iff.2 fun τ _ => ?_⟩
  exact fun e => hw0 τ (inner_self_eq_zero.1 e)

theorem isMultiplicityInner_add_smul_right (M : DSModel V S) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) (T T' T'' : MMap M)
    {a b : ℂ} (c : ℂ) (h : IsMultIP M μ 𝓕 T T' a) (h' : IsMultIP M μ 𝓕 T T'' b) :
    IsMultIP M μ 𝓕 T (T' + c • T'') (a + c * b) := by
  intro v v'
  have e : (fun g => star (T v g) * (T' + c • T'') v' g) =
      fun g => star (T v g) * T' v' g + c * (star (T v g) * T'' v' g) := by
    funext g
    show star (T v g) * (T' v' g + c * T'' v' g) = _
    ring
  have i2 : IntegrableOn (fun g => c * (star (T v g) * T'' v' g)) 𝓕 μ := (h' v v').1.const_mul c
  rw [e]
  refine ⟨(h v v').1.add i2, ?_⟩
  rw [integral_add (h v v').1 i2, integral_const_mul, (h v v').2, (h' v v').2]
  ring

theorem isMultiplicityInner_symm (M : DSModel V S) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) (T T' : MMap M)
    {a : ℂ} (h : IsMultIP M μ 𝓕 T T' a) : IsMultIP M μ 𝓕 T' T (star a) := by
  intro v v'
  have e : (fun g => star (T' v g) * T v' g) = fun g => (starRingEnd ℂ) (star (T v' g) * T' v g) := by
    funext g
    rw [starRingEnd_apply, star_mul, star_star]
  rw [e]
  refine ⟨?_, ?_⟩
  · exact (Complex.conjCLE.toContinuousLinearMap.integrable_comp (h v' v).1 :)
  · rw [integral_conj, (h v' v).2, map_mul, map_prod]
    simp only [inner_conj_symm]
    rfl

theorem re_pos_of_isMultIP (M : DSModel V S) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) (hμ : μ.IsHaarMeasure)
    (hF : IsFundamentalDomain (GQ V) 𝓕 μ) (T : MMap M) {a : ℂ} (h : IsMultIP M μ 𝓕 T T a) (v : M.Vec)
    (hc : Continuous (T v)) (hL : ∀ γ ∈ GQ V, ∀ g, T v (γ * g) = T v g) (h0 : T v ≠ 0) : 0 < a.re := by
  obtain ⟨hi, he⟩ := h v v
  have e : (fun g => star (T v g) * T v g) = fun g => ((‖T v g‖ ^ 2 : ℝ) : ℂ) := by
    funext g
    rw [Complex.star_def, Complex.conj_mul']
    push_cast
    rfl
  rw [e] at hi he
  have hi' : IntegrableOn (fun g => ‖T v g‖ ^ 2) 𝓕 μ := by
    have := hi.re
    simp only [RCLike.re_to_complex, Complex.ofReal_re] at this
    exact this
  rw [integral_complex_ofReal] at he
  have e2 : ∏ τ, ⟪(v τ : M.H τ), (v τ : M.H τ)⟫_ℂ = ((∏ τ, ‖(v τ : M.H τ)‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [inner_self_eq_norm_sq_to_K]
    push_cast
    rfl
  rw [e2] at he
  have he' := congrArg Complex.re he
  rw [Complex.ofReal_re, Complex.re_mul_ofReal] at he'
  have hp : 0 ≤ ∏ τ, ‖(v τ : M.H τ)‖ ^ 2 := Finset.prod_nonneg fun τ _ => by positivity
  have hnn : 0 ≤ ∫ g in 𝓕, ‖T v g‖ ^ 2 ∂μ := integral_nonneg fun g => by positivity
  have hne : ∫ g in 𝓕, ‖T v g‖ ^ 2 ∂μ ≠ 0 := by
    intro hz
    have := (integral_eq_zero_iff_of_nonneg (fun g => by positivity) hi').1 hz
    refine h0 (eq_zero_of_ae μ 𝓕 hμ hF _ hc hL ?_)
    filter_upwards [this] with g hg
    simpa using hg
  have hpos : 0 < a.re * ∏ τ, ‖(v τ : M.H τ)‖ ^ 2 := he' ▸ lt_of_le_of_ne hnn hne.symm
  by_contra hn
  exact absurd hpos (not_lt.2 (mul_nonpos_of_nonpos_of_nonneg (not_lt.1 hn) hp))

theorem ipM_posDef : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)), IsInfFam θ → μ.IsHaarMeasure → IsFundamentalDomain (GQ V) 𝓕 μ → SchurMult θ M J χ μ 𝓕 → (∀ τ, M.sm τ ≠ ⊥) → (∀ T ∈ Mult θ M J χ, ∀ T' ∈ Mult θ M J χ, ∀ T'' ∈ Mult θ M J χ, ∀ c : ℂ, ipM M μ 𝓕 T (T' + c • T'') = ipM M μ 𝓕 T T' + c * ipM M μ 𝓕 T T'' ∧ ipM M μ 𝓕 T' T = star (ipM M μ 𝓕 T T')) ∧ ∀ T ∈ Mult θ M J χ, T ≠ 0 → 0 < (ipM M μ 𝓕 T T).re := by
  intro D θ V S M J χ μ 𝓕 hθ hμ hF hS hsm
  obtain ⟨v0, hv0⟩ := exists_vec M hsm
  have hs : ∀ T ∈ Mult θ M J χ, ∀ T' ∈ Mult θ M J χ, IsMultIP M μ 𝓕 T T' (ipM M μ 𝓕 T T') :=
    fun T hT T' hT' => ipM_spec M μ 𝓕 T T' (hS hθ hμ hF T hT T' hT')
  refine ⟨fun T hT T' hT' T'' hT'' c => ⟨?_, ?_⟩, fun T hT h0 => ?_⟩
  · exact hasPeterssonInner_unique M μ 𝓕 _ _ v0 hv0
      (hs T hT _ (Submodule.add_mem _ hT' (Submodule.smul_mem _ c hT'')))
      (isMultiplicityInner_add_smul_right M μ 𝓕 T T' T'' c (hs T hT T' hT') (hs T hT T'' hT''))
  · exact hasPeterssonInner_unique M μ 𝓕 _ _ v0 hv0 (hs T' hT' T hT) (isMultiplicityInner_symm M μ 𝓕 T T' (hs T hT T' hT'))
  · obtain ⟨v, hv⟩ : ∃ v, T v ≠ 0 := by
      by_contra hn
      push_neg at hn
      exact h0 (MultilinearMap.ext hn)
    have := left_cont_of_mem θ M J χ T hT v
    exact re_pos_of_isMultIP M μ 𝓕 hμ hF T (hs T hT T hT) v this.1 this.2 hv

end GlobalTheory.SchurConst
end

