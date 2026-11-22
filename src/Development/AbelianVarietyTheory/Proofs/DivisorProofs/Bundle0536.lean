import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0518
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TamagawaSpecialUnitary
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0519
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0515
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0066
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0332
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShortExactMappingConeResolutionHomotopyEquiv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0378
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0522
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0503
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0529
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisAutMemAdelicCompletionIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0393
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0429
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0524
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfTraceFormSkewHermitianStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_zero_of_trace_form_skew_hermitian : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G : Matrix (Fin r) (Fin r) E) (X : Matrix (Fin r) (Fin r) E), (∀ a b, cc (G a b) = G b a) → G.det ≠ 0 → X.trace = 0 → (∀ u w, herm G (X *ᵥ u) w + herm G u (X *ᵥ w) = 0) → (∀ Y : Matrix (Fin r) (Fin r) E, Y.trace = 0 → (∀ u w, herm G (Y *ᵥ u) w + herm G u (Y *ᵥ w) = 0) → (X * Y).trace = 0) → X = 0 := by
  first | exact @GlobalTheory.TraceSkew.traceForm_nondegenerate | exact GlobalTheory.TraceSkew.traceForm_nondegenerate | (intros; apply GlobalTheory.TraceSkew.traceForm_nondegenerate <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyBijectiveOfSupportBijectiveStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleCohomology_bijective_of_support_bijective : GlobalTheory.EtC.A10 := by
  first | (exact @GlobalTheory.EtC.a10) | (exact GlobalTheory.EtC.a10) | (intros; apply GlobalTheory.EtC.a10  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyNegativeVanishingDegreeZeroStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleCohomology_negative_vanishing_degree_zero : GlobalTheory.EtC.A9 := by
  first | exact @GlobalTheory.EtC.etale_cohomology_vanishing_negative_degree_zero | exact GlobalTheory.EtC.etale_cohomology_vanishing_negative_degree_zero | (intros; apply GlobalTheory.EtC.etale_cohomology_vanishing_negative_degree_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleOfEtaleHeightOneOfRegularLocalRingStatement
section
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etale_of_etale_height_one_of_regularLocalRing : ∀ (R A : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsDomain R] [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [Algebra R A] [Module.Finite R A] [FaithfulSMul R A], (((maximalIdeal R).spanFinrank : WithBot ℕ∞) = ringKrullDim R) → 1 ≤ ringKrullDim R → ¬ IsField R → (∀ (p : Ideal R) [p.IsPrime], p.height = 1 → Algebra.Etale (Localization.AtPrime p) (TensorProduct R (Localization.AtPrime p) A)) → Algebra.Etale R A := by
  first | exact @GlobalTheory.BranchPurity.etale_of_etale_height_one | exact GlobalTheory.BranchPurity.etale_of_etale_height_one | (intros; apply GlobalTheory.BranchPurity.etale_of_etale_height_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EveryElementIsNorm
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.every_element_is_norm : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (s : F' ≃ₐ[F] F'), (∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s) → ∀ (n : ℕ) (δ : GL (Fin n) F'), ∃ γ : GL (Fin n) F, IsNorm s δ γ := by
  first | (exact @GlobalTheory.Shin.exists_isNorm) | (exact GlobalTheory.Shin.exists_isNorm) | (intros; apply GlobalTheory.Shin.exists_isNorm  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExcisionConeMapQuasiIso
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC.ExcisionQis

theorem map_descShortComplex {C : Type*} [Category C] [Abelian C] {K₁ K₂ L₁ L₂ M : CochainComplex C ℤ}
    (f' : K₁ ⟶ K₂) (g' : K₂ ⟶ M) (w' : f' ≫ g' = 0) (f : L₁ ⟶ L₂) (g : L₂ ⟶ M) (w : f ≫ g = 0)
    (a : K₁ ⟶ L₁) (b : K₂ ⟶ L₂) (comm : f' ≫ b = a ≫ f) (hg : g' = b ≫ g) :
    mappingCone.map f' f a b comm ≫ mappingCone.descShortComplex (ShortComplex.mk f g w) =
      mappingCone.descShortComplex (ShortComplex.mk f' g' w') := by
  ext n : 1
  apply mappingCone.ext_from _ (n + 1) n rfl
  · simp [mappingCone.map, mappingCone.descShortComplex, HomComplex.Cochain.zero_cochain_comp_v]
  · simp [mappingCone.map, mappingCone.descShortComplex, hg]

theorem cone_single_qis {C : Type*} [Category C] [Abelian C] {F1 F2 F3 F4 : C} (u' : F1 ⟶ F2) (u : F3 ⟶ F4)
    (a : F1 ⟶ F3) (b : F2 ⟶ F4) (comm : u' ≫ b = a ≫ u) [Mono u] (w : biprod.lift a (-u') ≫ biprod.desc u b = 0)
    (hS : (ShortComplex.mk _ _ w).ShortExact) :
    QuasiIso (mappingCone.map ((singleFunctor C 0).map u') ((singleFunctor C 0).map u) ((singleFunctor C 0).map a)
      ((singleFunctor C 0).map b) (by rw [← Functor.map_comp, ← Functor.map_comp, comm])) := by
  haveI : Mono (biprod.lift a (-u')) := hS.mono_f
  haveI : Epi (biprod.desc u b) := hS.epi_g
  let T : ShortComplex C := ShortComplex.mk u (cokernel.π u) (cokernel.condition u)
  have hT : T.ShortExact := ShortComplex.ShortExact.mk' (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel u))
    inferInstance inferInstance
  have w' : u' ≫ b ≫ cokernel.π u = 0 := by
    rw [← Category.assoc, comm, Category.assoc, cokernel.condition, Limits.comp_zero]
  let T' : ShortComplex C := ShortComplex.mk u' (b ≫ cokernel.π u) w'
  have hmono : Mono u' := by
    refine Preadditive.mono_of_cancel_zero _ fun {Q} g hg => ?_
    have hga : g ≫ a = 0 := by
      rw [← cancel_mono u, Category.assoc, ← comm, ← Category.assoc, hg, Limits.zero_comp, Limits.zero_comp]
    have : g ≫ biprod.lift a (-u') = 0 := by
      apply biprod.hom_ext <;> simp [hga, hg]
    rw [← cancel_mono (biprod.lift a (-u')), this, Limits.zero_comp]
  have hepi : Epi (b ≫ cokernel.π u) := by
    refine Preadditive.epi_of_cancel_zero _ fun {Q} h hh => ?_
    have h1 : biprod.desc u b ≫ cokernel.π u ≫ h = 0 := by
      apply biprod.hom_ext'
      · simp
      · simpa using hh
    have h2 : cokernel.π u ≫ h = 0 := by
      rw [← cancel_epi (biprod.desc u b), h1, Limits.comp_zero]
    rw [← cancel_epi (cokernel.π u), h2, Limits.comp_zero]
  have hexact : T'.Exact := by
    rw [ShortComplex.exact_iff_exact_up_to_refinements]
    intro A₀ y hy
    have hy' : (y ≫ b) ≫ T.g = 0 := by simpa using hy
    obtain ⟨A₁, e₁, he₁, z, hz⟩ := (ShortComplex.exact_iff_exact_up_to_refinements T).1 hT.exact (y ≫ b) hy'
    have hw : biprod.lift (-z) (e₁ ≫ y) ≫ (ShortComplex.mk _ _ w).g = 0 := by
      change biprod.lift (-z) (e₁ ≫ y) ≫ biprod.desc u b = 0
      rw [biprod.lift_desc, Preadditive.neg_comp, Category.assoc, hz]
      exact neg_add_cancel _
    obtain ⟨A₂, e₂, he₂, x, hx⟩ := (ShortComplex.exact_iff_exact_up_to_refinements _).1 hS.exact _ hw
    refine ⟨A₂, e₂ ≫ e₁, inferInstance, -x, ?_⟩
    have h2 := congrArg (· ≫ biprod.snd) hx
    simp only [Category.assoc] at h2
    rw [biprod.lift_snd, biprod.lift_snd] at h2
    show (e₂ ≫ e₁) ≫ y = (-x) ≫ u'
    rw [Category.assoc, h2, Preadditive.neg_comp, Preadditive.comp_neg]
  have hT' : T'.ShortExact := ShortComplex.ShortExact.mk' hexact hmono hepi
  have z1 : (singleFunctor C 0).map u ≫ (singleFunctor C 0).map (cokernel.π u) = 0 := by
    rw [← Functor.map_comp, cokernel.condition, Functor.map_zero]
  have z2 : (singleFunctor C 0).map u' ≫ (singleFunctor C 0).map (b ≫ cokernel.π u) = 0 := by
    rw [← Functor.map_comp, w', Functor.map_zero]
  have c2 : (singleFunctor C 0).map u' ≫ (singleFunctor C 0).map b = (singleFunctor C 0).map a ≫ (singleFunctor C 0).map u := by
    rw [← Functor.map_comp, ← Functor.map_comp, comm]
  have hST : (ShortComplex.mk _ _ z1).ShortExact := hT.map_of_exact (HomologicalComplex.single C (ComplexShape.up ℤ) 0)
  have hST' : (ShortComplex.mk _ _ z2).ShortExact := hT'.map_of_exact (HomologicalComplex.single C (ComplexShape.up ℤ) 0)
  haveI := mappingCone.quasiIso_descShortComplex hST
  haveI := mappingCone.quasiIso_descShortComplex hST'
  have key := map_descShortComplex _ _ z2 _ _ z1 ((singleFunctor C 0).map a) ((singleFunctor C 0).map b) c2
    (Functor.map_comp _ _ _)
  haveI : QuasiIso (mappingCone.map _ _ _ _ c2 ≫ mappingCone.descShortComplex (ShortComplex.mk _ _ z1)) := by
    rw [key]; exact mappingCone.quasiIso_descShortComplex hST'
  exact quasiIso_of_comp_right _ (mappingCone.descShortComplex (ShortComplex.mk _ _ z1))

theorem mono_free_away (R : Type) [CommRing R] (A : Type) [CommRing A] (f : A) :
    Mono ((free R).map (yoneda.map (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away f)))))) := by
  haveI : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away f)))) :=
    IsOpenImmersion.of_isLocalization f
  have h1 : Mono (yoneda.map (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away f))))) := inferInstance
  have h2 : Mono ((freeP R).map (yoneda.map (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away f)))))) := by
    have happ : ∀ U, Mono (((freeP R).map (yoneda.map (Spec.map (CommRingCat.ofHom
        (algebraMap A (Localization.Away f)))))).app U) := fun U => by
      have hinj : Function.Injective
          ((yoneda.map (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away f))))).app U) :=
        (mono_iff_injective _).1 inferInstance
      rw [ModuleCat.mono_iff_injective]
      change Function.Injective (Finsupp.mapDomain _)
      exact Finsupp.mapDomain_injective (fun x y hxy => ULift.ext _ _ (hinj (congrArg ULift.down hxy)))
    exact NatTrans.mono_of_mono_app _
  change Mono ((presheafToSheaf _ _).map ((freeP R).map _))
  infer_instance

theorem quasiIso_map_of_corners {C : Type*} [Category C] [Abelian C] {K₁ K₂ K₃ K₄ L₁ L₂ L₃ L₄ : CochainComplex C ℤ}
    (φ' : K₁ ⟶ K₂) (φ : K₃ ⟶ K₄) (α : K₁ ⟶ K₃) (β : K₂ ⟶ K₄) (c₀ : φ' ≫ β = α ≫ φ)
    (ψ' : L₁ ⟶ L₂) (ψ : L₃ ⟶ L₄) (α' : L₁ ⟶ L₃) (β' : L₂ ⟶ L₄) (c₁ : ψ' ≫ β' = α' ≫ ψ)
    (e₁ : K₁ ⟶ L₁) (e₂ : K₂ ⟶ L₂) (e₃ : K₃ ⟶ L₃) (e₄ : K₄ ⟶ L₄) (q₁ : QuasiIso e₁) (q₂ : QuasiIso e₂)
    (q₃ : QuasiIso e₃) (q₄ : QuasiIso e₄) (h₁₂ : φ' ≫ e₂ = e₁ ≫ ψ') (h₃₄ : φ ≫ e₄ = e₃ ≫ ψ) (h₁₃ : α ≫ e₃ = e₁ ≫ α')
    (h₂₄ : β ≫ e₄ = e₂ ≫ β') [QuasiIso (mappingCone.map φ' φ α β c₀)] :
    QuasiIso (mappingCone.map ψ' ψ α' β' c₁) := by
  haveI := q₁; haveI := q₂; haveI := q₃; haveI := q₄
  have key : mappingCone.map φ' ψ' e₁ e₂ h₁₂ ≫ mappingCone.map ψ' ψ α' β' c₁ =
      mappingCone.map φ' φ α β c₀ ≫ mappingCone.map φ ψ e₃ e₄ h₃₄ := by
    rw [← mappingCone.map_comp, ← mappingCone.map_comp]
    congr 1
    · exact h₁₃.symm
    · exact h₂₄.symm
  haveI := GlobalTheory.EtC.ConeRes.quasiIso_mappingCone_map φ' ψ' e₁ e₂ h₁₂
  haveI := GlobalTheory.EtC.ConeRes.quasiIso_mappingCone_map φ ψ e₃ e₄ h₃₄
  haveI : QuasiIso (mappingCone.map φ' ψ' e₁ e₂ h₁₂ ≫ mappingCone.map ψ' ψ α' β' c₁) := by
    rw [key]; infer_instance
  exact quasiIso_of_comp_left (mappingCone.map φ' ψ' e₁ e₂ h₁₂) _

theorem _root_.GlobalTheory.EtC.excisionConeMap_quasiIso : ∀ (R : Type) [CommRing R] (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] (f : A), IsExcisionNbhd A A' f → QuasiIso (excisionConeMap R A A' f) := by
  intro R _ A A' _ _ _ f h
  obtain ⟨e, -, he⟩ := chains_disc_homotopyEquiv R
  haveI : Algebra.Etale A A' := h.1
  have comm : (free R).map (yoneda.map (Spec.map (CommRingCat.ofHom (algebraMap A' (Localization.Away (algebraMap A A' f)))))) ≫
      (free R).map (yoneda.map (Spec.map (CommRingCat.ofHom (algebraMap A A')))) =
      (free R).map (yoneda.map (Spec.map (CommRingCat.ofHom (Localization.awayMap (algebraMap A A') f)))) ≫
      (free R).map (yoneda.map (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away f))))) := by
    simp only [← Functor.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, awayMap_comp_algebraMap]
  have w : biprod.lift ((free R).map (yoneda.map (Spec.map (CommRingCat.ofHom (Localization.awayMap (algebraMap A A') f)))))
      (-(free R).map (yoneda.map (Spec.map (CommRingCat.ofHom (algebraMap A' (Localization.Away (algebraMap A A' f))))))) ≫
      biprod.desc ((free R).map (yoneda.map (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away f))))))
        ((free R).map (yoneda.map (Spec.map (CommRingCat.ofHom (algebraMap A A'))))) = 0 := by
    rw [biprod.lift_desc, Preadditive.neg_comp, ← comm, add_neg_cancel]
  have hS := GlobalTheory.T.freeEtaleSheaf_excision_shortExact R A A' f ⟨h.2.1, h.2.2⟩ w
  haveI := mono_free_away R A f
  haveI := cone_single_qis _ _ _ _ comm w hS
  exact quasiIso_map_of_corners _ _ _ _ _ _ _ _ _ _ _ _ _ _ (e _).quasiIso_hom (e _).quasiIso_hom
    (e _).quasiIso_hom (e _).quasiIso_hom (he _).symm (he _).symm (he _).symm (he _).symm

end GlobalTheory.EtC.ExcisionQis

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsElementPosImUnderCmTypeStatement
section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.WeightTwoSum
open scoped ContDiff nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_element_pos_im_under_cmType : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ), IsCMType φ → ∃ θ : E, ∀ i, 0 < (φ i θ).im := by
  first | exact @GlobalTheory.CMTypeImPos.exists_im_pos | exact GlobalTheory.CMTypeImPos.exists_im_pos | (intros; apply GlobalTheory.CMTypeImPos.exists_im_pos <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEndLatticeTraceOne
section
noncomputable section

namespace GlobalTheory.LieDisc

open NumberField Matrix GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def rankOne (G : Matrix (Fin r) (Fin r) E) (x y : Fin r → E) : Matrix (Fin r) (Fin r) E :=
  Matrix.of fun a b => x a * ∑ k, G b k * cc (y k)

theorem rankOne_mulVec (G : Matrix (Fin r) (Fin r) E) (x y v : Fin r → E) :
    rankOne G x y *ᵥ v = herm G v y • x := by
  ext a
  simp only [rankOne, mulVec, dotProduct, of_apply, herm, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem trace_rankOne (G : Matrix (Fin r) (Fin r) E) (x y : Fin r → E) :
    (rankOne G x y).trace = herm G x y := by
  simp only [Matrix.trace, diag, rankOne, of_apply, herm, Finset.mul_sum, mul_assoc]

def traceIdeal (Λ : Submodule (𝓞 E) (Fin r → E)) : Ideal (𝓞 E) where
  carrier := {s | ∃ Z ∈ endLat Λ, Z.trace = (s : E)}
  zero_mem' := ⟨0, (endLat Λ).zero_mem, by simp⟩
  add_mem' {s t} hs ht := by
    obtain ⟨Z, hZ, e⟩ := hs
    obtain ⟨Z', hZ', e'⟩ := ht
    exact ⟨Z + Z', (endLat Λ).add_mem hZ hZ', by rw [trace_add, e, e']; push_cast; rfl⟩
  smul_mem' c {s} hs := by
    obtain ⟨Z, hZ, e⟩ := hs
    refine ⟨(c : E) • Z, smul_mem_endLat c.isIntegral_coe hZ, ?_⟩
    rw [trace_smul, e, smul_eq_mul, smul_eq_mul]
    push_cast; rfl

theorem exists_endLat_trace_eq_one (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ)
    (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)) (hr : 1 ≤ r)
    (h : SelfDualLat G Λ) : ∃ Z ∈ endLat Λ, Z.trace = 1 := by
  have hint : ∀ x ∈ Λ, ∀ y ∈ Λ, IsIntegral ℤ (herm G x y) := fun x hx => (h.2.2.2.2 x).2 hx
  have htop : traceIdeal Λ = ⊤ := by
    by_contra hT
    refine GlobalTheory.UCls.Det.exists_herm_notMem hr h (traceIdeal Λ) hT fun x hx y hy =>
      ⟨⟨herm G x y, hint x hx y hy⟩, ⟨rankOne G x y, fun v hv => ?_, trace_rankOne G x y⟩, rfl⟩
    rw [rankOne_mulVec]
    exact smul_mem_of_isIntegral (hint v hv y hy) hx
  have h1 : (1 : 𝓞 E) ∈ traceIdeal Λ := htop ▸ Submodule.mem_top
  obtain ⟨Z, hZ, e⟩ := h1
  exact ⟨Z, hZ, by rw [e]; simp⟩

example : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G : Matrix (Fin r) (Fin r) E)
    (Λ : Submodule (𝓞 E) (Fin r → E)), 1 ≤ r → SelfDualLat G Λ → ∃ Z ∈ endLat Λ, Z.trace = 1 :=
  exists_endLat_trace_eq_one

end GlobalTheory.LieDisc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEquivCmTypeRealEmbeddingsMaxRealSubfieldStatement
section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.WeightTwoSum
open scoped ContDiff nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_equiv_cmType_realEmbeddings_maxRealSubfield : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ), IsCMType φ → ∃ e : I ≃ Emb (maximalRealSubfield E), ∀ (i : I) (a : maximalRealSubfield E), φ i (a : E) = ((e i a : ℝ) : ℂ) := by
  first | exact @GlobalTheory.CMTypeRealEmb.exists_equiv | exact GlobalTheory.CMTypeRealEmb.exists_equiv | (intros; apply GlobalTheory.CMTypeRealEmb.exists_equiv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExtensionAdditiveFnPDivGroup
section
set_option autoImplicit false

open TensorProduct Coalgebra Bialgebra CategoryTheory WithConv GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory

namespace PDivGroup

variable {p : ℕ} {R : Type} [CommRing R] (G : PDivGroup p R)

theorem exists_res_eq_of_transl_eq_add {b : G.A 1} (hb : cobOne R (G.A 1) b = 0) (n : ℕ)
    (x : G.A (n + 1)) (hx : G.transl n x = x ⊗ₜ[R] 1 + 1 ⊗ₜ[R] b) :
    ∃ y : G.A (n + 2), G.transl (n + 1) y = y ⊗ₜ[R] 1 + 1 ⊗ₜ[R] b ∧ G.res (n + 1) y = x := by
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.T.transl_coaction_free_coassoc_counital G (n + 1)
  obtain ⟨x', hx'⟩ := GlobalTheory.T.exists_coaction_eq_add_of_primitive (G.transl (n + 1)) h1 h2 h3 b hb
  have hr : G.transl n (G.res (n + 1) x') = G.res (n + 1) x' ⊗ₜ[R] 1 + 1 ⊗ₜ[R] b := by
    rw [transl_res, hx', map_add, LinearMap.rTensor_tmul, LinearMap.rTensor_tmul]
    simp
  obtain ⟨e, he⟩ := GlobalTheory.T.exists_mulP_eq_of_transl_invariant G n (G.res (n + 1) x' - x) (by
    rw [map_sub, hr, hx, sub_tmul]
    abel)
  obtain ⟨e', rfl⟩ := G.res_surjective n e
  refine ⟨x' - G.mulP (n + 1) e', ?_, ?_⟩
  · rw [map_sub, hx', transl_mulP, sub_tmul]
    abel
  · rw [map_sub, res_mulP, ← mulP_res, he, sub_sub_cancel]

theorem exists_funs_transl_eq_add {p : ℕ} {R : Type} [CommRing R] (G : PDivGroup p R)
    (b : G.A 1) (hb : cobOne R (G.A 1) b = 0) :
    ∃ B : G.funs, B.1 1 = b ∧
      ∀ n, G.transl n (B.1 (n + 1)) = B.1 (n + 1) ⊗ₜ[R] 1 + 1 ⊗ₜ[R] b := by
  choose f hf hres using G.exists_res_eq_of_transl_eq_add hb
  have h0 : G.transl 0 b = b ⊗ₜ[R] 1 + 1 ⊗ₜ[R] b := by
    have h : (G.resOne 0 : G.A 1 →ₗ[R] G.A 1) = LinearMap.id := rfl
    rw [transl_apply, h, LinearMap.lTensor_id, LinearMap.id_apply]
    rw [cobOne_apply, sub_sub, sub_eq_zero] at hb
    exact hb
  let s : ∀ n, {x : G.A (n + 1) // G.transl n x = x ⊗ₜ[R] 1 + 1 ⊗ₜ[R] b} := fun n =>
    Nat.rec (motive := fun n => {x : G.A (n + 1) // G.transl n x = x ⊗ₜ[R] 1 + 1 ⊗ₜ[R] b})
      ⟨b, h0⟩ (fun n x => ⟨f n x.1 x.2, hf n x.1 x.2⟩) n
  refine ⟨⟨fun n => Nat.casesOn (motive := fun n => G.A n) n (G.res 0 b) fun n => (s n).1, ?_⟩,
    rfl, fun n => (s n).2⟩
  rintro (_ | n)
  · rfl
  · exact hres n (s n).1 (s n).2

end PDivGroup

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrobeniusHodgeTateLatticeAinf
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.PDivLat.Frob

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (Ideal.span {(p : O)}) O]

theorem frob_phiInv (a : Ainf p O) : WittVector.frobenius (phiInv p O a) = a := by
  ext n
  rw [WittVector.coeff_frobenius_charP, phiInv, WittVector.map_coeff]
  exact frobeniusEquiv_symm_pow_p _ p _

theorem phiInv_ofPadic' (c : ℤ_[p]) : phiInv p O (ofPadic p O c) = ofPadic p O c := by
  ext n
  simp only [phiInv, ofPadic, RingHom.coe_comp, Function.comp_apply, WittVector.map_coeff]
  exact RingHom.congr_fun (RingHom.ext_zmod
    (((_root_.frobeniusEquiv (PreTilt O p) p).symm : PreTilt O p →+* PreTilt O p).comp
      (ZMod.castHom (dvd_refl p) (PreTilt O p))) (ZMod.castHom (dvd_refl p) (PreTilt O p))) _

theorem frob_ofPadic (c : ℤ_[p]) :
    WittVector.frobenius (ofPadic p O c) = ofPadic p O c := by
  conv_lhs => rw [← phiInv_ofPadic' c]
  exact frob_phiInv _

def frobT (G : PDivGroup p O) (y : TDual G) : TDual G where
  toFun t := WittVector.frobenius (y t)
  map_add' s t := by rw [map_add, map_add]
  map_smul' c t := by
    rw [LinearMap.map_smulₛₗ, smul_eq_mul, map_mul, frob_ofPadic, smul_eq_mul]

def xiPhiInvT (ε : PreTilt O p) (G : PDivGroup p O) (m : TDual G) : TDual G where
  toFun t := xi ε * phiInv p O (m t)
  map_add' s t := by rw [map_add, map_add, mul_add]
  map_smul' c t := by
    rw [LinearMap.map_smulₛₗ, smul_eq_mul, map_mul, phiInv_ofPadic', smul_eq_mul, mul_left_comm]

def frobLatt (G : PDivGroup p O) :
    latt G →ₛₗ[(WittVector.frobenius : Ainf p O →+* Ainf p O)] latt G where
  toFun y := ⟨frobT G y.1, fun n => by
    obtain ⟨x, hx⟩ := y.2 (n + 1)
    exact ⟨x, fun t => by rw [← hx]; rfl⟩⟩
  map_add' y z := by
    apply Subtype.ext; apply LinearMap.ext; intro t
    show WittVector.frobenius ((y.1 + z.1) t) = _
    rw [LinearMap.add_apply, map_add]; rfl
  map_smul' a y := by
    apply Subtype.ext; apply LinearMap.ext; intro t
    show WittVector.frobenius ((a • y.1) t) = _
    rw [LinearMap.smul_apply, smul_eq_mul, map_mul]; rfl

end GlobalTheory.PDivLat.Frob

open GlobalTheory.PDivLat.Frob in

theorem GlobalTheory.PDivLat.exists_frobenius_latt : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∃ φ : ∀ G : PDivGroup p O, latt G →ₛₗ[(WittVector.frobenius : Ainf p O →+* Ainf p O)] latt G, (∀ G y t, (φ G y).1 t = WittVector.frobenius (y.1 t)) ∧ ∀ G m, ∃ n, φ G n = (WittVector.frobenius (xi ε) : Ainf p O) • m := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε
  obtain ⟨-, -, -, h0, hs, hphi⟩ := GlobalTheory.T.ainfGhostThetaFrobIter_values_xi_mu_padic p C v O hv ε hε
  refine ⟨fun G => frobLatt G, fun G y t => rfl, fun G m => ?_⟩
  refine ⟨⟨xiPhiInvT ε G m.1, fun n => ?_⟩, ?_⟩
  · cases n with
    | zero => exact ⟨0, fun t => by
        show ghost p O 0 (xi ε * phiInv p O (m.1 t)) = _
        rw [ghost_mul, h0, zero_mul, LinearMap.zero_apply]⟩
    | succ k =>
      obtain ⟨x, hx⟩ := m.2 k
      exact ⟨(p : O) • x, fun t => by
        show ghost p O (k + 1) (xi ε * phiInv p O (m.1 t)) = _
        rw [ghost_mul, hs, hphi, hx, LinearMap.smul_apply, smul_eq_mul]⟩
  · apply Subtype.ext; apply LinearMap.ext; intro t
    show WittVector.frobenius (xi ε * phiInv p O (m.1 t)) = _
    rw [map_mul, frob_phiInv]; rfl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralTraceOneUnramified
section
open NumberField Matrix GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.LieDisc

noncomputable section

namespace GlobalTheory.LieDisc

theorem exists_integral_add_cc_eq_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E],
    Unr E → ∃ t : E, IsIntegral ℤ t ∧ t + cc t = 1 := by
  intro E _ _ _ hE
  have : Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E) := hE
  let σ := IsCMField.ringOfIntegersComplexConj E
  let I : Ideal (𝓞 (maximalRealSubfield E)) :=
    { carrier := {a | ∃ t : 𝓞 E, algebraMap _ (𝓞 E) a = t + σ t}
      add_mem' := by
        rintro a b ⟨s, hs⟩ ⟨t, ht⟩
        exact ⟨s + t, by rw [map_add, hs, ht, map_add]; ring⟩
      zero_mem' := ⟨0, by simp⟩
      smul_mem' := by
        rintro c a ⟨t, ht⟩
        refine ⟨algebraMap _ (𝓞 E) c * t, ?_⟩
        rw [smul_eq_mul, map_mul, ht, map_mul, AlgEquiv.commutes]
        ring }
  have hI : I = ⊤ := by
    by_contra hI
    obtain ⟨m, hm, hIm⟩ := Ideal.exists_le_maximal _ hI
    obtain ⟨P, hP, hPm⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 E) m
      (by rw [(RingHom.injective_iff_ker_eq_bot _).1
        (FaithfulSMul.algebraMap_injective (𝓞 (maximalRealSubfield E)) (𝓞 E))]; exact bot_le)
    have htr : ∀ t : 𝓞 E, t + σ t ∈ P := by
      intro t
      have hco : ((t + σ t : 𝓞 E) : E) = (t : E) + IsCMField.complexConj E t := by
        rw [← IsCMField.coe_ringOfIntegersComplexConj]
        rfl
      have hfix := (IsCMField.complexConj_eq_self_iff E ((t : E) + IsCMField.complexConj E t)).1 (by
        rw [map_add, IsCMField.complexConj_apply_apply, add_comm])
      have hi : IsIntegral ℤ (⟨_, hfix⟩ : maximalRealSubfield E) := by
        have h0 : IsIntegral ℤ ((t + σ t : 𝓞 E) : E) := (t + σ t).isIntegral_coe
        rw [hco] at h0
        exact (isIntegral_algebraMap_iff (algebraMap (maximalRealSubfield E) E).injective).1 h0
      let a : 𝓞 (maximalRealSubfield E) := ⟨_, hi⟩
      have hA : algebraMap _ (𝓞 E) a = t + σ t := by
        apply RingOfIntegers.ext
        rw [hco]
        rfl
      have h1 : a ∈ Ideal.comap (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) P := hPm ▸ hIm ⟨t, hA⟩
      exact hA ▸ Ideal.mem_comap.1 h1
    have hσ : ∃ s, σ.toAlgHom s ≠ s := by
      by_contra hc
      push Not at hc
      apply IsCMField.complexConj_ne_one E
      ext x
      obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) x
      have hc' : ∀ s : 𝓞 E, IsCMField.complexConj E (algebraMap (𝓞 E) E s) = algebraMap (𝓞 E) E s :=
        fun s => congrArg (fun z : 𝓞 E => (z : E)) (hc s)
      simp [hc']
    obtain ⟨t, ht⟩ := GlobalTheory.UCls.Det.exists_sub_notMem σ.toAlgHom hσ P hP.ne_top
    apply ht
    have h2 := P.sub_mem (htr t) (P.mul_mem_right (σ t) (htr 1))
    convert h2 using 1
    change t - σ t = t + σ t - (1 + σ 1) * σ t
    rw [map_one]
    ring
  obtain ⟨t, ht⟩ : (1 : 𝓞 (maximalRealSubfield E)) ∈ I := hI ▸ Submodule.mem_top
  refine ⟨(t : E), t.isIntegral_coe, ?_⟩
  have h := congrArg (fun z : 𝓞 E => (z : E)) ht
  rw [map_one] at h
  change (1 : E) = (t : E) + ((σ t : 𝓞 E) : E) at h
  rw [IsCMField.coe_ringOfIntegersComplexConj] at h
  rw [cc]
  exact h.symm

end GlobalTheory.LieDisc
end
end

