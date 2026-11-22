import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0079
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0008
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0029
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0022
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0010
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2513
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0597
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2465
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.TrivBasicOpenOfTrivFibre
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaloisClosureLocalDomainExtension
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.GalClosure

theorem exists_galois_embedding (R R' : Type) [CommRing R] [IsDomain R] [CharZero R] [CommRing R'] [IsDomain R']
    [Algebra R R'] [Module.Finite R R'] (hinj : Function.Injective (algebraMap R R')) :
    ∃ L : IntermediateField (FractionRing R) (AlgebraicClosure (FractionRing R)),
      FiniteDimensional (FractionRing R) L ∧ IsGalois (FractionRing R) L ∧
      ∃ j : R' →ₐ[R] L, Function.Injective j := by
  first
  | exact @_root_.GlobalTheory.GaloisEmbeddingExistence.exists_galois_embedding
  | exact _root_.GlobalTheory.GaloisEmbeddingExistence.exists_galois_embedding
  | (apply _root_.GlobalTheory.GaloisEmbeddingExistence.exists_galois_embedding <;> assumption)
  | (intros; apply _root_.GlobalTheory.GaloisEmbeddingExistence.exists_galois_embedding <;> assumption)
  | (intros; apply @_root_.GlobalTheory.GaloisEmbeddingExistence.exists_galois_embedding <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.GaloisEmbeddingExistence.exists_galois_embedding ..)

end GlobalTheory.GalClosure

namespace GlobalTheory.GalClosure

theorem isGal_integralClosure_of_tower (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (L : Type) [Field L]
    [Algebra (FractionRing R) L] [FiniteDimensional (FractionRing R) L] [IsGalois (FractionRing R) L] [Algebra R L]
    [IsScalarTower R (FractionRing R) L] :
    IsGal (algebraMap R (integralClosure R L)) := by
  set K := FractionRing R
  set B := integralClosure R L
  haveI : IsFractionRing B L := integralClosure.isFractionRing_of_finite_extension K L
  have hRL : ∀ r : R, algebraMap B L (algebraMap R B r) = algebraMap K L (algebraMap R K r) := fun r => by
    rw [← IsScalarTower.algebraMap_apply R K L]; rfl
  have hfix : ∀ τ : Gal (algebraMap R B), ∀ k : K,
      IsFractionRing.ringEquivOfRingEquiv (K := L) (L := L) τ.1 (algebraMap K L k) = algebraMap K L k := by
    intro τ k
    have h := IsLocalization.ringHom_ext (M := nonZeroDivisors R) (S := K)
      (j := (IsFractionRing.ringEquivOfRingEquiv (K := L) (L := L) τ.1).toRingHom.comp (algebraMap K L))
      (k := algebraMap K L) (by
        ext r
        simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
        rw [← hRL, IsFractionRing.ringEquivOfRingEquiv_algebraMap, τ.2 r])
    exact congrArg (fun f => f k) h
  let toAut : Gal (algebraMap R B) → (L ≃ₐ[K] L) := fun τ => AlgEquiv.ofRingEquiv (hfix τ)
  have htoAut : ∀ τ b, toAut τ (algebraMap B L b) = algebraMap B L (τ.1 b) := fun τ b =>
    IsFractionRing.ringEquivOfRingEquiv_algebraMap _ b
  refine ⟨Finite.of_injective toAut fun τ τ' h => Subtype.ext (RingEquiv.ext fun b => ?_), fun x hx => ?_⟩
  · apply IsFractionRing.injective B L
    rw [← htoAut, ← htoAut, h]
  · have hg : ∀ g : L ≃ₐ[K] L, g (x : L) = x := by
      intro g
      let gR : L →ₐ[R] L := (g : L →ₐ[K] L).restrictScalars R
      let gR' : L →ₐ[R] L := (g.symm : L →ₐ[K] L).restrictScalars R
      let τ : B ≃+* B :=
        { toFun := fun b => ⟨g b, (mem_integralClosure_iff R L).2 ((b.2 : IsIntegral R (b : L)).map gR)⟩
          invFun := fun b => ⟨g.symm b, (mem_integralClosure_iff R L).2 ((b.2 : IsIntegral R (b : L)).map gR')⟩
          left_inv := fun b => Subtype.ext (g.symm_apply_apply (b : L))
          right_inv := fun b => Subtype.ext (g.apply_symm_apply (b : L))
          map_mul' := fun a b => Subtype.ext (map_mul g (a : L) b)
          map_add' := fun a b => Subtype.ext (map_add g (a : L) b) }
      have hτ : τ ∈ Gal (algebraMap R B) := fun r => Subtype.ext (by
        show g ((algebraMap R B r : B) : L) = ((algebraMap R B r : B) : L)
        have e : ((algebraMap R B r : B) : L) = algebraMap K L (algebraMap R K r) := hRL r
        rw [e, AlgEquiv.commutes])
      exact congrArg Subtype.val (hx τ hτ)
    obtain ⟨k, hk⟩ := IntermediateField.mem_bot.1 ((IsGalois.mem_bot_iff_fixed (F := K) (x : L)).2 hg)
    have hint : IsIntegral R k := by
      have h1 : IsIntegral R (algebraMap K L k) := hk ▸ (x.2 : IsIntegral R (x : L))
      exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom R K L) (algebraMap K L).injective).1 h1
    obtain ⟨r, hr⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
    refine ⟨r, Subtype.ext ?_⟩
    have := hRL r
    rw [hr, hk] at this
    exact this

end GlobalTheory.GalClosure

namespace GlobalTheory.GalClosure

theorem exists_galois_finExt_isLocalHom : ∀ (R R' : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing R'] [IsDomain R']
    [IsLocalRing R'] (ρ : R →+* R'), Base R → FinExt ρ → ∃ (R'' : Type) (_ : CommRing R'') (_ : IsDomain R'')
    (_ : IsLocalRing R'') (σ : R' →+* R''), FinExt σ ∧ IsLocalHom σ ∧ FinExt (σ.comp ρ) ∧ IsGal (σ.comp ρ) := by
  intro R R' _ _ _ _ _ _ ρ hR hρ
  obtain ⟨⟨hRn, -, hRic, hRc⟩, hR0⟩ := hR
  obtain ⟨-, hinj, hfin⟩ := hρ
  letI : Algebra R R' := ρ.toAlgebra
  haveI : Module.Finite R R' := hfin
  obtain ⟨L, hLf, hLg, j, hj⟩ := exists_galois_embedding R R' hinj
  set B := integralClosure R L
  obtain ⟨hBfin, hBloc, hBn, hBic, -⟩ := GlobalTheory.integralClosure_finite_local_of_isAdicComplete R hRc L
  have hmem : ∀ x : R', j x ∈ B := fun x => (Algebra.IsIntegral.isIntegral (R := R) x).map j
  let jB : R' →ₐ[R] B := j.codRestrict B hmem
  let σ : R' →+* B := jB.toRingHom
  have hcomp : σ.comp ρ = algebraMap R B := RingHom.ext fun r => jB.commutes r
  have hadm : AdmBase B (maximalIdeal B) :=
    ⟨hBn, inferInstance, hBic, GlobalTheory.CompleteFiniteExtension.isAdicComplete_of_finite_local R B⟩
  have hσinj : Function.Injective σ := fun a b h => hj (congrArg (fun y : B => (y : L)) h)
  have hcfin : (σ.comp ρ).Finite := hcomp ▸ RingHom.finite_algebraMap.2 hBfin
  have hσfin : σ.Finite := RingHom.Finite.of_comp_finite hcfin
  refine ⟨B, inferInstance, inferInstance, hBloc, σ, ⟨hadm, hσinj, hσfin⟩,
    RingHom.IsIntegral.isLocalHom hσfin.to_isIntegral hσinj, ⟨hadm, hσinj.comp hinj, hcfin⟩, ?_⟩
  rw [hcomp]
  exact isGal_integralClosure_of_tower R L

end GlobalTheory.GalClosure
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaloisQuotientInvariantOpen
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_quotient_of_invariant_open {Γ : Type} [Group Γ] [Finite Γ] {Y S : Scheme.{0}} (act : Γ → (Y ⟶ Y))
    (h1 : act 1 = 𝟙 _) (hm : ∀ σ τ, act (σ * τ) = act σ ≫ act τ) (s : Y ⟶ S) (hs : ∀ σ, act σ ≫ s = s)
    (H : Y.Opens) (hH : ∀ σ, act σ ⁻¹ᵁ H = H)
    (hO : ∀ x ∈ H, ∃ O : Y.Opens, IsAffineOpen O ∧ O ≤ H ∧ ∀ σ, act σ x ∈ O) :
    ∃ (X : Over S) (π : H.toScheme ⟶ X.left), π ≫ X.hom = H.ι ≫ s ∧ IsAffineHom π ∧ Surjective π ∧
      (∀ σ, (act σ).resLE H H (hH σ).ge ≫ π = π) ∧
      (∀ x y : H.toScheme, π x = π y → ∃ σ, act σ (H.ι x) = H.ι y) ∧
      ∀ V : X.left.Opens, Function.Injective (π.app V).hom ∧ ∀ f : Γ(H.toScheme, π ⁻¹ᵁ V),
        (∀ σ (h : π ⁻¹ᵁ V ≤ ((act σ).resLE H H (hH σ).ge) ⁻¹ᵁ (π ⁻¹ᵁ V)),
          (((act σ).resLE H H (hH σ).ge).appLE _ _ h).hom f = f) → f ∈ Set.range (π.app V).hom := by
  let r : Γ → (H.toScheme ⟶ H.toScheme) := fun σ => (act σ).resLE H H (hH σ).ge
  have hr : ∀ σ, r σ ≫ H.ι = H.ι ≫ act σ := fun σ => Scheme.Hom.resLE_comp_ι _ _
  have r1 : r 1 = 𝟙 _ := by
    rw [← cancel_mono H.ι, hr, h1, Category.id_comp, Category.comp_id]
  have rm : ∀ σ τ, r (σ * τ) = r σ ≫ r τ := fun σ τ => by
    rw [← cancel_mono H.ι, hr, hm, Category.assoc, hr, reassoc_of% hr]
  let ρ : Γ →* Aut H.toScheme := MonoidHom.mk'
    (fun σ => ⟨r σ⁻¹, r σ, by rw [← rm, inv_mul_cancel, r1], by rw [← rm, mul_inv_cancel, r1]⟩)
    (fun σ τ => Iso.ext (show r (σ * τ)⁻¹ = r τ⁻¹ ≫ r σ⁻¹ by rw [mul_inv_rev, rm]))
  have hρ : ∀ σ, (ρ σ).hom = r σ⁻¹ := fun _ => rfl
  have hρ' : ∀ σ, r σ = (ρ σ⁻¹).hom := fun σ => by rw [hρ, inv_inv]
  have hpt : ∀ σ (x : H.toScheme), H.ι (r σ x) = act σ (H.ι x) := fun σ x => congr($(hr σ) x)
  have : OrbitsInAffineOpens ρ := ⟨fun x => by
    obtain ⟨O, hO₁, hO₂, hO₃⟩ := hO (H.ι x) x.2
    refine ⟨H.ι ⁻¹ᵁ O, hO₁.preimage_of_isOpenImmersion H.ι (by rwa [Scheme.Opens.opensRange_ι]), fun g => ?_⟩
    change H.ι (r g⁻¹ x) ∈ O
    rw [hpt]
    exact hO₃ _⟩
  obtain ⟨X', π, hπ⟩ := QuotientGluing.exists_isAffineQuotient ρ
  have hinv : ∀ g, (ρ g).hom ≫ H.ι ≫ s = H.ι ≫ s := fun g => by
    rw [hρ, reassoc_of% hr, hs]
  refine ⟨Over.mk (hπ.desc (H.ι ≫ s) hinv), π, hπ.comp_desc _ hinv, hπ.isAffineHom, hπ.surjective, fun σ => ?_,
    fun x y hxy => ?_, fun V => ⟨hπ.app_injective V, fun f hf => ?_⟩⟩
  · exact (congrArg (· ≫ π) (hρ' σ)).trans (hπ.comp_eq _)
  · obtain ⟨g, rfl⟩ := (hπ.apply_eq_iff x y).mp hxy
    exact ⟨g⁻¹, (hpt _ _).symm⟩
  · exact hπ.mem_range_app V f fun g => ⟨hπ.preimage_le V g, hf g⁻¹ _⟩

theorem exists_galois_quotient : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → IsGal ρ → ∀ (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R') D' A' G') (a : GalAct ρ hD U'), ∀ (H : G'.left.Opens) (hH : ∀ σ, a.act σ ⁻¹ᵁ H = H), (∀ x ∈ H, ∃ O : G'.left.Opens, IsAffineOpen O ∧ O ≤ H ∧ ∀ σ, a.act σ x ∈ O) → ∃ (X : Over (Sp R)) (π : H.toScheme ⟶ X.left), π ≫ X.hom = H.ι ≫ G'.hom ≫ spMap ρ ∧ IsAffineHom π ∧ Surjective π ∧ (∀ σ, (a.act σ).resLE H H (hH σ).ge ≫ π = π) ∧ (∀ x y : H.toScheme, π x = π y → ∃ σ, a.act σ (H.ι x) = H.ι y) ∧ ∀ V : X.left.Opens, Function.Injective (π.app V).hom ∧ ∀ f : Γ(H.toScheme, π ⁻¹ᵁ V), (∀ σ (h : π ⁻¹ᵁ V ≤ ((a.act σ).resLE H H (hH σ).ge) ⁻¹ᵁ (π ⁻¹ᵁ V)), (((a.act σ).resLE H H (hH σ).ge).appLE _ _ h).hom f = f) → f ∈ Set.range (π.app V).hom := by
  intro R _ _ _ _ R' _ _ _ ρ _ hG D D' hD A' G' _ _ _ U' a H hH hO
  have := hG.1
  refine exists_quotient_of_invariant_open a.act a.act_one a.act_mul (G'.hom ≫ spMap ρ) (fun σ => ?_) H hH hO
  have e : spMap (Gal.hom σ) ≫ spMap ρ = spMap ρ := by
    rw [← Spec.map_comp]
    congr 1
    ext x
    exact σ.2 x
  rw [← Category.assoc, (a.cart σ).1.w, Category.assoc, e]

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorTopExteriorPower
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DetSpan

open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations

theorem ord_nonneg_of_int (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (x : R) :
    0 ≤ ord_vw R (algebraMap R (FractionRing R) x) := by
  unfold ord_vw
  by_cases hx : x = 0
  · subst hx; simp
  · have h0 : (IsDiscreteValuationRing.maximalIdeal R).valuation (FractionRing R) (algebraMap R (FractionRing R) x) ≠ 0 := by
      rw [Valuation.ne_zero_iff]
      exact (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 hx
    have h1 := (IsDiscreteValuationRing.maximalIdeal R).valuation_le_one (K := FractionRing R) x
    have := (WithZero.log_le_log h0 one_ne_zero).2 h1
    rw [WithZero.log_one] at this
    omega

theorem ord_le (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (n : ℕ) (D t u : R)
    (h : D ^ n = t * u) (hD : D ≠ 0) :
    ord_vw R (algebraMap R (FractionRing R) u) ≤ n * ord_vw R (algebraMap R (FractionRing R) D) := by
  unfold ord_vw
  set v := (IsDiscreteValuationRing.maximalIdeal R).valuation (FractionRing R)
  have inj := IsFractionRing.injective R (FractionRing R)
  have hDn : D ^ n ≠ 0 := pow_ne_zero _ hD
  have hu : u ≠ 0 := by rintro rfl; rw [mul_zero] at h; exact hDn h
  have ne : ∀ y : R, y ≠ 0 → v (algebraMap R (FractionRing R) y) ≠ 0 := fun y hy => by
    rw [Valuation.ne_zero_iff]; exact (map_ne_zero_iff _ inj).2 hy
  have e1 : v (algebraMap R (FractionRing R) D) ^ n = v (algebraMap R (FractionRing R) t) * v (algebraMap R (FractionRing R) u) := by
    rw [← map_pow, ← map_pow, h, map_mul, map_mul]
  have e2 : v (algebraMap R (FractionRing R) D) ^ n ≤ v (algebraMap R (FractionRing R) u) := by
    rw [e1]
    exact mul_le_of_le_one_left' ((IsDiscreteValuationRing.maximalIdeal R).valuation_le_one (K := FractionRing R) t)
  have e3 := (WithZero.log_le_log (pow_ne_zero _ (ne D hD)) (ne u hu)).2 e2
  rw [WithZero.log_pow, nsmul_eq_mul] at e3
  linarith

theorem wedge_eq_smul_gen_val_le : ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (L : Type) [AddCommGroup L] [Module R L]
    [Module.Free R L] [Module.Finite R L] (n : ℕ), Module.finrank R L = n →
    ∀ (e : Fin n → (L →ₗ[R] R)) (D : R), D ≠ 0 → (∀ ω : L →ₗ[R] R, D • ω ∈ Submodule.span R (Set.range e)) →
    ∀ (l : ℕ), ∃ (δ₀ : L [⋀^Fin n]→ₗ[R] R) (u₀ : R), Submodule.span R {δ₀} = ⊤ ∧
      Matrix.detRowAlternating.compLinearMap (LinearMap.pi e) = u₀ • δ₀ ∧
      GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.val_vp R l (algebraMap R (FractionRing R) u₀) ≤
        n • GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.val_vp R l (algebraMap R (FractionRing R) D) := by
  intro R _ _ _ L _ _ _ _ n hn e D hD hspan l
  classical
  let b := Module.finBasisOfFinrankEq R L hn
  refine ⟨b.det, Matrix.detRowAlternating.compLinearMap (LinearMap.pi e) b, ?_, ?_, ?_⟩
  · rw [eq_top_iff]
    intro f _
    rw [AlternatingMap.eq_smul_basis_det b f]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  · exact AlternatingMap.eq_smul_basis_det b _
  · set u := Matrix.detRowAlternating.compLinearMap (LinearMap.pi e) b with hu_def
    choose t ht using fun k => (Submodule.mem_span_range_iff_exists_fun R).1 (hspan (b.coord k))
    let E : Matrix (Fin n) (Fin n) R := Matrix.of fun i j => e i (b j)
    have hu : u = E.det := by
      rw [← Matrix.det_transpose]
      rfl
    have hm : Matrix.of t * E = D • (1 : Matrix (Fin n) (Fin n) R) := by
      ext k j
      have := congrArg (fun f : L →ₗ[R] R => f (b j)) (ht k)
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, Module.Basis.coord_apply,
        Module.Basis.repr_self] at this
      simp only [Matrix.mul_apply, Matrix.of_apply, E, Matrix.smul_apply, Matrix.one_apply, this, smul_eq_mul,
        Finsupp.single_apply]
      by_cases hkj : k = j
      · subst hkj; simp
      · simp [hkj, Ne.symm hkj]
    have hkey : D ^ n = (Matrix.of t).det * u := by
      rw [hu, ← Matrix.det_mul, hm, Matrix.det_smul, Matrix.det_one, Fintype.card_fin, _root_.mul_one]
    have hord := ord_le R n D _ u hkey hD
    have hu0 : u ≠ 0 := by
      rintro h0; rw [h0, mul_zero] at hkey; exact pow_ne_zero n hD hkey
    have inj := IsFractionRing.injective R (FractionRing R)
    have hc : (0 : ℚ) ≤ (ord_vw R ((l : ℕ) : FractionRing R) : ℚ) := by
      rw [← map_natCast (algebraMap R (FractionRing R))]
      exact_mod_cast ord_nonneg_of_int R (l : R)
    unfold val_vp
    rw [if_neg ((map_ne_zero_iff _ inj).2 hu0), if_neg ((map_ne_zero_iff _ inj).2 hD), ← WithTop.coe_nsmul,
      WithTop.coe_le_coe, nsmul_eq_mul, ← mul_div_assoc]
    apply div_le_div_of_nonneg_right _ hc
    exact_mod_cast hord

end GlobalTheory.DetSpan
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorTorsionBundleAbelianSchemeSqZero
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.CechPic

theorem pow_add_sqZero {A : Type*} [CommRing A] (v M : A) (hM : M * M = 0) (k : ℕ) :
    (v + M) ^ (k + 1) = v ^ (k + 1) + (k + 1) * M * v ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih]; push_cast
    linear_combination ((k : A) + 1) * v ^ k * hM

theorem sqZero_root_correction_mul_pow_eq_zero {A : Type*} [CommRing A] {G Sa Sb Na Nb H M : A} (k : ℕ)
    (hS : Sa = G ^ (k + 1) * Sb) (hNa : Na = Sa - 1) (hNb : Nb = Sb - 1) (hNa2 : Na * Na = 0)
    (hNb2 : Nb * Nb = 0) (hH : ((k + 1 : ℕ) : A) * H = 1) (hM : M = (1 + Na * H) - G * (1 + Nb * H))
    (hM2 : M * M = 0) : M * (G * (1 + Nb * H)) ^ k = 0 := by
  push_cast at hH
  have r1 : ∀ N : A, N * N = 0 → (1 + N * H) ^ (k + 1) = 1 + N := fun N hN => by
    rw [pow_add_sqZero 1 (N * H) (by linear_combination H ^ 2 * hN) k, one_pow, one_pow]
    linear_combination N * hH
  have e1 : (1 + Na * H) ^ (k + 1) = Sa := by rw [r1 Na hNa2]; linear_combination hNa
  have e2 : (G * (1 + Nb * H)) ^ (k + 1) = G ^ (k + 1) * Sb := by
    rw [mul_pow, r1 Nb hNb2]; linear_combination G ^ (k + 1) * hNb
  have e3 := pow_add_sqZero (G * (1 + Nb * H)) M hM2 k
  have hu : G * (1 + Nb * H) + M = 1 + Na * H := by linear_combination hM
  rw [hu] at e3
  linear_combination H * (e1 - e2 + hS - e3) - M * (G * (1 + Nb * H)) ^ k * hH

end GlobalTheory.CechPic

namespace GlobalTheory.CechPic

open scoped CategoryTheory.Obj
open IsLocalRing

theorem eq_zero_of_sqZero_baseChange_nsmul : ∀ (k : ℕ) (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀),
    Function.Surjective π → RingHom.ker π ^ 2 = ⊥ → IsUnit ((k + 1 : ℕ) : R) →
    ∀ (X X₀ : Scheme.{0}) (s : X ⟶ Sp R) (s₀ : X₀ ⟶ Sp R₀) (i : X₀ ⟶ X), IsPullback i s₀ s (spMap π) →
    Function.Surjective i.appTop.hom → ∀ m : GlobalTheory.CechPic.Pic X, GlobalTheory.CechPic.pull i m = 0 →
    (k + 1) • m = 0 → m = 0 := by
  intro k R R₀ _ _ π hπ hk h2 X X₀ s s₀ i hP hsurj m hm hm2
  haveI : IsClosedImmersion (spMap π) :=
    IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom π) hπ
  haveI : IsClosedImmersion i :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion) hP.flip inferInstance
  haveI : Surjective i := GlobalTheory.LiftSys.surjective_of_isPullback_sqZero (I := RingHom.ker π)
    (by rw [hk]; rfl) hπ rfl hP
  have hsq : ∀ (W : X.Opens) (x y : Γ(X, W)), (i.app W).hom x = 0 → (i.app W).hom y = 0 → x * y = 0 :=
    GlobalTheory.SquareZero.mul_eq_zero_of_app_eq_zero R R₀ π hπ hk X X₀ s s₀ i hP
  obtain ⟨D, hD, rfl, hD1⟩ := exists_cocycle_one_on_thickening X X₀ i m hm
  have h2X : IsUnit ((k + 1 : ℕ) : Γ(X, ⊤)) := by
    have := h2.map ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ s.appTop).hom
    rwa [map_natCast] at this
  rw [← cls_lbPow hD (k + 1) (LB.isLB_linComb hD _ _), cls_eq_zero_iff] at hm2
  obtain ⟨σ₂, hσ₂⟩ := hm2
  have hle : ∀ a, D.U a ≤ (lbPow D (k + 1)).U (fun _ => a) := fun a y hy =>
    Set.mem_iInter.2 fun _ => hy
  let σ : ∀ a, Γ(X, D.U a)ˣ := fun a => res (hle a) (σ₂.s (fun _ => a))
  have hσ : ∀ a b, res (inf_le_left : D.U a ⊓ D.U b ≤ D.U a) (σ a) =
      D.g a b ^ (k + 1) * res inf_le_right (σ b) := by
    intro a b
    refine unit_ext fun y hy => ?_
    have e := (isGen_iff_germ σ₂).1 hσ₂ y (fun _ => a) (fun _ => b) (hle a hy.1) (hle b hy.2)
    have hg := gm_linComb D (fun _ : PUnit => 𝟙 X) (fun _ => ((k + 1 : ℕ) : ℤ)) (𝟙 X) y
      (fun _ => a) (fun _ => b) (hle a hy.1) (hle b hy.2)
    rw [Fintype.prod_unique, Category.id_comp, zpow_natCast] at hg
    erw [hg] at e
    rw [map_mul, map_pow, gm_res (𝟙 X) y _ hy, gm_res (𝟙 X) y _ hy]
    dsimp only [σ]
    erw [gm_res (𝟙 X) y (hle a) hy.1, gm_res (𝟙 X) y (hle b) hy.2]
    exact e
  have hg1 : ∀ a b (y : X₀) (hy : i y ∈ D.U a ⊓ D.U b), gm i y _ (D.g a b) = 1 := by
    intro a b y hy
    have e := gm_pull (𝟙 X₀) i y (D.U a ⊓ D.U b) hy (D.g a b)
    rw [Category.id_comp, hD1 a b, map_one] at e
    exact e.symm
  have hσi : ∀ a b (y : X₀) (ha : i y ∈ D.U a) (hb : i y ∈ D.U b), gm i y _ (σ a) = gm i y _ (σ b) := by
    intro a b y ha hb
    have hab : i y ∈ D.U a ⊓ D.U b := ⟨ha, hb⟩
    rw [← gm_res i y (inf_le_left : D.U a ⊓ D.U b ≤ D.U a) hab, hσ a b, map_mul, map_pow,
      hg1 a b y hab, gm_res i y inf_le_right hab, one_pow, _root_.one_mul]
  have hpi : ∀ a (y : X₀) (ha : i y ∈ D.U a), gm (𝟙 X₀) y (i ⁻¹ᵁ D.U a) (pullU i _ (σ a)) = gm i y _ (σ a) := by
    intro a y ha
    rw [gm_pull (𝟙 X₀) i y _ ha, Category.id_comp]
  obtain ⟨U₀, hU₀⟩ := glue_unit (X := X₀) (i ⁻¹ᵁ ⊤) (fun a => i ⁻¹ᵁ D.U a) (fun a _ _ => trivial)
    (fun y _ => TopologicalSpace.Opens.mem_iSup.2 (exists_chart hD (i y))) (fun a => pullU i _ (σ a))
    (fun a b y hy => by rw [hpi a y hy.1, hpi b y hy.2]; exact hσi a b y hy.1 hy.2)
  obtain ⟨v, hv⟩ := hsurj (show Γ(X₀, ⊤) from U₀.val)
  have hvu : IsUnit v := X.toRingedSpace.isUnit_of_isUnit_germ ⊤ v fun x hx => by
    obtain ⟨y, rfl⟩ := Surjective.surj (f := i) x
    have h1 : IsUnit ((i.stalkMap y).hom ((X.presheaf.germ ⊤ (i y) hx).hom v)) := by
      rw [Scheme.Hom.germ_stalkMap_apply]
      erw [hv]
      exact U₀.isUnit.map _
    exact isUnit_of_map_unit _ _ h1
  let Vu : Γ(X, ⊤)ˣ := hvu.unit
  have hVu : ∀ (y : X₀), gm i y ⊤ Vu = gm (𝟙 X₀) y (i ⁻¹ᵁ ⊤) U₀ := by
    intro y
    have e := gm_pull (𝟙 X₀) i y ⊤ trivial Vu
    rw [Category.id_comp] at e
    rw [← e]
    congr 1
    exact Units.ext hv
  let σ' : ∀ a, Γ(X, D.U a)ˣ := fun a => σ a * res (le_top : D.U a ≤ ⊤) Vu⁻¹
  have hσ'1 : ∀ a, (i.app (D.U a)).hom (σ' a).val = 1 := by
    intro a
    have e : pullU i (D.U a) (σ' a) = 1 := unit_ext fun y hy => by
      rw [map_one, gm_pull (𝟙 X₀) i y _ hy, Category.id_comp]
      dsimp only [σ']
      rw [map_mul, gm_res i y le_top hy, map_inv, hVu y, ← hpi a y hy, ← hU₀ a]
      erw [gm_res (𝟙 X₀) y (fun _ _ => trivial : i ⁻¹ᵁ D.U a ≤ i ⁻¹ᵁ ⊤) hy]
      exact mul_inv_cancel _
    exact congrArg Units.val e
  have hσ' : ∀ a b, res (inf_le_left : D.U a ⊓ D.U b ≤ D.U a) (σ' a) =
      D.g a b ^ (k + 1) * res inf_le_right (σ' b) := by
    intro a b
    dsimp only [σ']
    rw [map_mul, map_mul, hσ a b]
    simp only [res_res, _root_.mul_assoc]
  let n : ∀ a, Γ(X, D.U a) := fun a => (σ' a).val - 1
  have hn0 : ∀ a, (i.app (D.U a)).hom (n a) = 0 := fun a => by
    simp only [n, map_sub, map_one, hσ'1 a, sub_self]
  have hn2 : ∀ a, n a * n a = 0 := fun a => hsq _ _ _ (hn0 a) (hn0 a)
  let Hh : ∀ a, Γ(X, D.U a) := fun a => (res (le_top : D.U a ≤ ⊤) h2X.unit⁻¹).val
  let t : ∀ a, Γ(X, D.U a) := fun a => 1 + n a * Hh a
  have ht : ∀ a, IsUnit (t a) := fun a =>
    IsUnit.of_mul_eq_one (1 - n a * Hh a) (by linear_combination (-(Hh a * Hh a)) * hn2 a)
  have hti : ∀ a, (i.app (D.U a)).hom (t a) = 1 := fun a => by
    simp only [t, map_add, map_one, map_mul, hn0 a, zero_mul, add_zero]
  refine (cls_eq_zero_iff hD).2 ⟨⟨fun a => (ht a).unit⟩, fun a b => ?_⟩
  apply Units.ext
  let ρa := (X.presheaf.map (homOfLE (inf_le_left : D.U a ⊓ D.U b ≤ D.U a)).op).hom
  let ρb := (X.presheaf.map (homOfLE (inf_le_right : D.U a ⊓ D.U b ≤ D.U b)).op).hom
  let ρt := (X.presheaf.map (homOfLE (le_top : D.U a ⊓ D.U b ≤ ⊤)).op).hom
  show ρa (t a) = (D.g a b).val * ρb (t b)
  let Hc : Γ(X, D.U a ⊓ D.U b) := (res (le_top : D.U a ⊓ D.U b ≤ ⊤) h2X.unit⁻¹).val
  have hHa : ρa (Hh a) = Hc := congrArg Units.val (res_res inf_le_left le_top h2X.unit⁻¹)
  have hHb : ρb (Hh b) = Hc := congrArg Units.val (res_res inf_le_right le_top h2X.unit⁻¹)
  have hH : ((k + 1 : ℕ) : Γ(X, D.U a ⊓ D.U b)) * Hc = 1 := by
    show ((k + 1 : ℕ) : Γ(X, D.U a ⊓ D.U b)) * ρt h2X.unit⁻¹.val = 1
    rw [show ((k + 1 : ℕ) : Γ(X, D.U a ⊓ D.U b)) = ρt ((k + 1 : ℕ) : Γ(X, ⊤)) from (map_natCast ρt _).symm,
      ← map_mul, h2X.mul_val_inv, map_one]
  have hS : ρa (σ' a).val = (D.g a b).val ^ (k + 1) * ρb (σ' b).val := by
    have := congrArg Units.val (hσ' a b)
    rw [Units.val_mul, Units.val_pow_eq_pow_val] at this
    exact this
  have hNa : ρa (n a) = ρa (σ' a).val - 1 := by simp only [n, map_sub, map_one]
  have hNb : ρb (n b) = ρb (σ' b).val - 1 := by simp only [n, map_sub, map_one]
  have hNa2 : ρa (n a) * ρa (n a) = 0 := by rw [← map_mul, hn2 a, map_zero]
  have hNb2 : ρb (n b) * ρb (n b) = 0 := by rw [← map_mul, hn2 b, map_zero]
  have hTa : ρa (t a) = 1 + ρa (n a) * Hc := by simp only [t, map_add, map_one, map_mul, hHa]
  have hTb : ρb (t b) = 1 + ρb (n b) * Hc := by simp only [t, map_add, map_one, map_mul, hHb]
  have hG1 : (i.app (D.U a ⊓ D.U b)).hom (D.g a b).val = 1 := congrArg Units.val (hD1 a b)
  have hM0 : (i.app (D.U a ⊓ D.U b)).hom (ρa (t a) - (D.g a b).val * ρb (t b)) = 0 := by
    rw [map_sub, map_mul, app_restrict, app_restrict, hti a, hti b, hG1, map_one, map_one,
      _root_.one_mul, sub_self]
  have key := sqZero_root_correction_mul_pow_eq_zero k hS hNa hNb hNa2 hNb2 hH (by rw [hTa, hTb]) (hsq _ _ _ hM0 hM0)
  have hu : IsUnit (((D.g a b).val * (1 + ρb (n b) * Hc)) ^ k) :=
    ((D.g a b).isUnit.mul (hTb ▸ (ht b).map ρb)).pow k
  exact sub_eq_zero.1 (hu.mul_left_eq_zero.1 key)

end GlobalTheory.CechPic

namespace GlobalTheory.CechPic

theorem exists_isGen_of_lbPow_of_sqZero_abelianScheme : ∀ (T : Type) [CommRing T] [IsLocalRing T] (e : T),
    (∀ a ∈ IsLocalRing.maximalIdeal T, a * e = 0) → e ∈ IsLocalRing.maximalIdeal T →
    ∀ (A : Over (Sp T)) [GrpObj A], IsAbelianScheme A → ∀ (M : LB A.left), M.IsLB → ∀ k : ℕ,
    IsUnit (k : T) → (∃ t : (GlobalTheory.UPel.HT.Hecke.lbPow M k).Gen, t.IsGen) →
    ∀ (X' : Scheme.{0}) (π : X' ⟶ A.left) (f' : X' ⟶ Sp (T ⧸ Ideal.span {e})),
    IsPullback π f' A.hom (spMap (Ideal.Quotient.mk (Ideal.span {e}))) →
    (∃ t : (M.pull π).Gen, t.IsGen) → ∃ t : M.Gen, t.IsGen := by
  intro T _ _ e hme hem A _ hA M hM k hk hpow X' π f' hP hπ
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := by
    cases k with
    | zero => exact absurd hk (by rw [Nat.cast_zero]; exact not_isUnit_zero)
    | succ k => exact ⟨k, rfl⟩
  set q := Ideal.Quotient.mk (Ideal.span {e})
  have hee : e * e = 0 := hme e hem
  have hker : RingHom.ker q ^ 2 = ⊥ := by
    rw [Ideal.mk_ker, Ideal.span_singleton_pow, Ideal.span_singleton_eq_bot, pow_two, hee]
  haveI : IsClosedImmersion (spMap q) :=
    IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom q) Ideal.Quotient.mk_surjective
  have hq : Function.Surjective (spMap q).appTop.hom :=
    (IsClosedImmersion.isAffine_surjective_of_isAffine (spMap q)).2
  have hf' : Function.Bijective f'.appTop.hom :=
    GlobalTheory.AbLaw.CubeOpen.bijective_appTop GlobalTheory.globalFns_holds A hA hP
  have hsurj : Function.Surjective π.appTop.hom := by
    intro w
    obtain ⟨c, rfl⟩ := hf'.2 w
    obtain ⟨d, rfl⟩ := hq c
    refine ⟨A.hom.appTop d, ?_⟩
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
      ← Scheme.Hom.comp_appTop, hP.w]
  have hpull : pull π (cls M hM) = 0 := by
    rw [← cls_pull hM π (pull_isLB hM π), cls_eq_zero_iff]
    exact hπ
  have hnsmul : (k + 1) • cls M hM = 0 := by
    have h := cls_linComb hM (fun _ : Fin (k + 1) => 𝟙 A.left) (fun _ => 1) (LB.isLB_linComb hM _ _)
    have h0 : cls (LB.LinComb M (fun _ : Fin (k + 1) => 𝟙 A.left) (fun _ => 1)) (LB.isLB_linComb hM _ _) = 0 :=
      (cls_eq_zero_iff _).2 hpow
    rw [h0] at h
    simpa [pull_id] using h.symm
  exact (cls_eq_zero_iff hM).1 (eq_zero_of_sqZero_baseChange_nsmul k T (T ⧸ Ideal.span {e}) q
    Ideal.Quotient.mk_surjective hker hk A.left X' A.hom f' π hP hsurj _ hpull hnsmul)

end GlobalTheory.CechPic
end
end

