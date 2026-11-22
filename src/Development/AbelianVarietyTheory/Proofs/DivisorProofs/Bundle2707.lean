import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2578
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2596
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0079
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2620
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0111
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2593
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0066
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2633
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0012
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2594
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0010
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2513
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0597
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0001
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsLocalRingQuotientPow
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0019
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2597
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0030

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFormsMapOfDividedPowerDerivation
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

namespace GlobalTheory.PDForm

section Lift

variable {R B : Type} [CommRing R] [CommRing B] [Algebra R B] {J : Ideal B} (δ : DividedPowers J)

theorem rel_isTwoSided (h : ∀ x ∈ rel R δ, ∀ y, x * y ∈ rel R δ) : (rel R δ).IsTwoSided :=
  ⟨fun b ha ↦ h _ ha b⟩

variable [(rel R δ).IsTwoSided]

def kq : K1 R δ →ₗ[B] DR R B ⧸ rel R δ :=
  (N1 R δ).liftQ ((Ideal.Quotient.mkₐ B (rel R δ)).toLinearMap ∘ₗ ι1) fun x hx ↦ by
    rw [LinearMap.mem_ker, LinearMap.comp_apply, AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk,
      Ideal.Quotient.eq_zero_iff_mem]
    exact hx

theorem kq_mk (ω : Ω[B⁄R]) : kq δ (Submodule.Quotient.mk ω) = Ideal.Quotient.mk (rel R δ) (ι1 ω) := rfl

end Lift

theorem exists_lift_of_pdDerivation (R B : Type) [CommRing R] [CommRing B] [Algebra R B] (J : Ideal B)
    (δ : DividedPowers J) (C : Type) [CommRing C] [Algebra R C] (JC : Ideal C) (δC : DividedPowers JC)
    (π : C →ₐ[R] B) (w : C →+ K1 R δ) (hw : ∀ x y, w (x * y) = π x • w y + π y • w x)
    (hw0 : ∀ r, w (algebraMap R C r) = 0)
    (hwd : ∀ n, ∀ a ∈ JC, w (δC.dpow (n + 1) a) = π (δC.dpow n a) • w a) :
    ∃ ρ : DR R C → DR R B, (∀ x y, ρ (x + y) - ρ x - ρ y ∈ rel R δ) ∧ (∀ x y, ρ (x * y) - ρ x * ρ y ∈ rel R δ) ∧
      (∀ c, ρ (algebraMap C (DR R C) c) - algebraMap B (DR R B) (π c) ∈ rel R δ) ∧
      (∀ c ω, Submodule.Quotient.mk ω = w c → ρ (ι1 (D R C c)) - ι1 ω ∈ rel R δ) ∧
      (∀ x ∈ rel R δC, ρ x ∈ rel R δ) ∧ (∀ x, ∃ ω, ρ (ι1 x) - ι1 ω ∈ rel R δ) ∧
      ∀ (j : ℕ), ∀ x ∈ ⋀[C]^j Ω[C⁄R], ∃ y ∈ ⋀[B]^j Ω[B⁄R], ρ x - y ∈ rel R δ := by
  haveI : (rel R δ).IsTwoSided := rel_isTwoSided δ ((GlobalTheory.T.divPowerCompatRel_filtration_twoSided_rel_eq_bot_of_base.1 R B J δ).1)
  letI algC : Algebra C (DR R B ⧸ rel R δ) :=
    ((algebraMap B (DR R B ⧸ rel R δ)).comp (π : C →+* B)).toAlgebra' fun c x ↦ Algebra.commutes (π c) x
  haveI : IsScalarTower R C (DR R B ⧸ rel R δ) := IsScalarTower.of_algebraMap_eq fun r ↦ by
    change _ = algebraMap B _ (π (algebraMap R C r))
    rw [AlgHom.commutes, ← IsScalarTower.algebraMap_apply]
  have smulC : ∀ (c : C) (q : DR R B ⧸ rel R δ), c • q = π c • q := fun c q ↦ by
    rw [Algebra.smul_def, Algebra.smul_def]; rfl
  let v : Derivation R C (DR R B ⧸ rel R δ) := Derivation.mk'
    { toFun := fun c ↦ kq δ (w c)
      map_add' := fun a b ↦ by simp
      map_smul' := fun r c ↦ by
        rw [RingHom.id_apply, Algebra.smul_def r c, hw, hw0, smul_zero, add_zero, map_smul, AlgHom.commutes,
          algebraMap_smul] }
    fun a b ↦ by
      change kq δ (w (a * b)) = a • kq δ (w b) + b • kq δ (w a)
      rw [hw, map_add, map_smul, map_smul, smulC, smulC]
  have hv : ∀ c, v c = kq δ (w c) := fun _ ↦ rfl
  have key : ∀ ω : Ω[C⁄R], ∃ η : Ω[B⁄R], v.liftKaehlerDifferential ω = Ideal.Quotient.mk (rel R δ) (ι1 η) := by
    intro ω
    induction ω using ind1 with
    | h b c =>
      obtain ⟨η, hη⟩ := Submodule.Quotient.mk_surjective _ (w c)
      refine ⟨π b • η, ?_⟩
      rw [map_smul, Derivation.liftKaehlerDifferential_comp_D, hv, ← hη, kq_mk, smulC, map_smul,
        Algebra.smul_def (π b) (ι1 η), map_mul, Ideal.Quotient.mk_algebraMap, Algebra.smul_def]
    | h0 => exact ⟨0, by simp⟩
    | ha x y hx hy =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨b, hb⟩ := hy
      exact ⟨a + b, by rw [map_add, ha, hb, map_add, map_add]⟩
  let Φ : DR R C →ₐ[C] DR R B ⧸ rel R δ := ExteriorAlgebra.lift C ⟨v.liftKaehlerDifferential, fun m ↦ by
    obtain ⟨η, h⟩ := key m
    rw [h, ← map_mul, ExteriorAlgebra.ι_sq_zero, map_zero]⟩
  have hΦι : ∀ ω : Ω[C⁄R], Φ (ι1 ω) = v.liftKaehlerDifferential ω := fun ω ↦ ExteriorAlgebra.lift_ι_apply _ _ _ _
  have hΦD : ∀ c, Φ (ι1 (D R C c)) = kq δ (w c) := fun c ↦ by
    rw [hΦι, Derivation.liftKaehlerDifferential_comp_D, hv]
  obtain ⟨ρ, hρ⟩ : ∃ ρ : DR R C → DR R B, ∀ x, Ideal.Quotient.mk (rel R δ) (ρ x) = Φ x :=
    ⟨_, fun x ↦ Function.surjInv_eq Ideal.Quotient.mk_surjective (Φ x)⟩
  have cv : ∀ x a, ρ x - a ∈ rel R δ ↔ Φ x = Ideal.Quotient.mk (rel R δ) a := fun x a ↦ by
    rw [← Ideal.Quotient.eq, hρ]
  refine ⟨ρ, fun x y ↦ ?_, fun x y ↦ ?_, fun c ↦ ?_, fun c ω h ↦ ?_, fun x hx ↦ ?_, fun x ↦ ?_, fun j x hx ↦ ?_⟩
  · rw [sub_sub]
    exact (cv _ _).2 (by rw [map_add, map_add, hρ, hρ])
  · exact (cv _ _).2 (by rw [map_mul, map_mul, hρ, hρ])
  · exact (cv _ _).2 (by rw [AlgHom.commutes, Ideal.Quotient.mk_algebraMap]; rfl)
  · exact (cv _ _).2 (by rw [hΦD, ← h, kq_mk])
  · rw [← Ideal.Quotient.eq_zero_iff_mem, hρ]
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨n, a, ha, rfl⟩ := hx
      rw [map_sub, map_smul, map_sub, map_smul, hΦD, hΦD, hwd n a ha, map_smul, smulC, sub_self]
    | zero => exact map_zero _
    | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
    | smul r x _ ih => rw [smul_eq_mul, map_mul, ih, mul_zero]
  · obtain ⟨η, h⟩ := key x
    exact ⟨η, (cv _ _).2 (by rw [hΦι, h])⟩
  · induction hx using Submodule.pow_induction_on_left' with
    | algebraMap c =>
      refine ⟨algebraMap B _ (π c), ?_, (cv _ _).2 (by rw [AlgHom.commutes, Ideal.Quotient.mk_algebraMap]; rfl)⟩
      change _ ∈ LinearMap.range _ ^ 0
      rw [pow_zero]; exact Submodule.algebraMap_mem _
    | add x y i _ _ hx hy =>
      obtain ⟨a, ha, ha'⟩ := hx
      obtain ⟨b, hb, hb'⟩ := hy
      exact ⟨a + b, add_mem ha hb, (cv _ _).2 (by rw [map_add, (cv _ _).1 ha', (cv _ _).1 hb', map_add])⟩
    | mem_mul m hm i x hx ih =>
      obtain ⟨ω, rfl⟩ := hm
      obtain ⟨η, hη⟩ := key ω
      obtain ⟨y, hy, hy'⟩ := ih
      refine ⟨ι1 η * y, ?_, (cv _ _).2 ?_⟩
      · have := GlobalTheory.CechDR.mul_mem (ι_mem η) hy
        rwa [add_comm] at this
      · rw [map_mul, (cv _ _).1 hy', map_mul, ← hη, ← hΦι]

end GlobalTheory.PDForm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaloisClosureLocalDomainExtensionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_galois_closure_local_domain_extension : ∀ (R R' : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), Base R → FinExt ρ → ∃ (R'' : Type) (_ : CommRing R'') (_ : IsDomain R'') (_ : IsLocalRing R'') (σ : R' →+* R''), FinExt σ ∧ IsLocalHom σ ∧ FinExt (σ.comp ρ) ∧ IsGal (σ.comp ρ) := by
  first | exact @GlobalTheory.GalClosure.exists_galois_finExt_isLocalHom | exact GlobalTheory.GalClosure.exists_galois_finExt_isLocalHom | (intros; apply GlobalTheory.GalClosure.exists_galois_finExt_isLocalHom <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaloisConjugateGenericBundleIso
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.GenDesc

namespace GlobalTheory.Mum.GenDesc

theorem exists_inv (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (R' : Type) [CommRing R'] [IsDomain R']
    [IsLocalRing R'] (ρ : R →+* R') (hρ : Function.Injective ρ) (D : DegData R (maximalIdeal R))
    (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R')))
    (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'] (U' : Unif (maximalIdeal R') D' A' G') (a : GalAct ρ hD U')
    (G : Over (Sp R)) [GrpObj G] (β : G'.left ⟶ G.left) (hβ : β ≫ G.hom = G'.hom ≫ spMap ρ) :
    (∀ σ, a.act σ ≫ β = β) → ∀ σ : Gal ρ, ∃ ψ : pullback G'.hom (jK R') ⟶ pullback G'.hom (jK R'),
      ψ ≫ genMap hρ β hβ = genMap hρ β hβ ∧
      ψ ≫ pullback.snd G'.hom (jK R') = pullback.snd G'.hom (jK R') ≫ spMap (fracAut σ.1).toRingHom ∧
      LBIso (U'.LG.L.pull (pullback.fst G'.hom (jK R'))) ((U'.LG.L.pull (pullback.fst G'.hom (jK R'))).pull ψ) := by
  intro hinv σ
  have h₁ : G'.hom ≫ spMap (Gal.hom σ) = a.act σ ≫ G'.hom := ((a.cart σ).1.w).symm
  have h₂ : jK R' ≫ spMap (Gal.hom σ) = spMap (fracAut σ.1).toRingHom ≫ jK R' := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext x
    exact (fracAut_algebraMap σ.1 x).symm
  let ψ := pullback.map G'.hom (jK R') G'.hom (jK R') (a.act σ) (spMap (fracAut σ.1).toRingHom) (spMap (Gal.hom σ)) h₁ h₂
  have hψ₁ : ψ ≫ pullback.fst G'.hom (jK R') = pullback.fst G'.hom (jK R') ≫ a.act σ := pullback.lift_fst _ _ _
  have hψ₂ : ψ ≫ pullback.snd G'.hom (jK R') = pullback.snd G'.hom (jK R') ≫ spMap (fracAut σ.1).toRingHom :=
    pullback.lift_snd _ _ _
  have hfr : spMap (fracAut σ.1).toRingHom ≫ spMap (fracMap ρ hρ) = spMap (fracMap ρ hρ) := by
    rw [← Spec.map_comp]
    congr 1
    ext x
    exact fracAut_fracMap hρ σ x
  refine ⟨ψ, ?_, hψ₂, ?_⟩
  · refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, genMap_fst, ← Category.assoc, hψ₁, Category.assoc, hinv σ]
    · rw [Category.assoc, genMap_snd, ← Category.assoc, hψ₂, Category.assoc, hfr]
  · obtain ⟨h, bc, hbc, hU, -⟩ := a.unif σ
    obtain ⟨wL, hwL, -⟩ := hU.lg
    have hL : LBIso U'.LG.L (U'.LG.L.pull (a.act σ)) := by
      rw [← hbc]
      exact ⟨wL, hwL⟩
    have hL₀ := U'.LG.isLB
    refine LBIso.trans (pull_isLB hL₀ _) (pull_isLB hL₀ _) (pull_isLB (pull_isLB hL₀ _) _)
      (GlobalTheory.GenSpread.lbIso_pull_of_lbIso hL (pullback.fst G'.hom (jK R')) rfl) ?_
    exact GlobalTheory.GenSpread.lbIso_pull_pull hL₀ ψ hψ₁.symm

end GlobalTheory.Mum.GenDesc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorLineBundlePullbackSpecLocalRingStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_generator_lineBundle_pullback_spec_localRing : ∀ (R : Type) [CommRing R] [IsLocalRing R] (X : Scheme.{0}) (L : LB X), L.IsLB →
    ∀ p : (𝟙_ (Over (Sp R))).left ⟶ X, ∃ ρ : LB.Gen (L.pull p), ρ.IsGen := by
  first | exact @GlobalTheory.LocalPullGen.main | exact GlobalTheory.LocalPullGen.main | (intros; apply GlobalTheory.LocalPullGen.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorOfTheoremOfCubeTenPoints
section
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.CubeGen

section
variable {X Y Z : Scheme.{0}} {L : LB X}

def Triv (L : LB X) (Y : Scheme.{0}) (F : ∀ (U : Type) [CommGroup U], ((Y ⟶ X) → U) → U) : Prop :=
  ∃ (K : Type) (_ : Fintype K) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L φ ε)), t.IsGen ∧
    ∀ (U : Type) [CommGroup U] (h : (Y ⟶ X) → U), ∏ k, h (φ k) ^ ε k = F U h

theorem Triv.mul {F F' : ∀ (U : Type) [CommGroup U], ((Y ⟶ X) → U) → U} (h : Triv L Y F) (h' : Triv L Y F') :
    Triv L Y (fun U _ g => F U g * F' U g) := by
  obtain ⟨K, _, φ, ε, t, ht, e⟩ := h
  obtain ⟨K', _, φ', ε', t', ht', e'⟩ := h'
  exact ⟨K ⊕ K', inferInstance, _, _, LB.mulGen L φ ε φ' ε' t t', DVR.mulGen_isGen _ _ _ _ _ _ _ ht ht',
    fun U _ g => (Fintype.prod_sum_type _).trans (congrArg₂ (· * ·) (e U g) (e' U g))⟩

theorem Triv.inv {F : ∀ (U : Type) [CommGroup U], ((Y ⟶ X) → U) → U} (h : Triv L Y F) :
    Triv L Y (fun U _ g => (F U g)⁻¹) := by
  obtain ⟨K, _, φ, ε, t, ht, e⟩ := h
  refine ⟨K, inferInstance, _, _, LB.invGen L φ ε t, DVR.invGen_isGen _ _ _ _ ht, fun U _ g => ?_⟩
  simp only [zpow_neg, Finset.prod_inv_distrib, e U g]

theorem Triv.pull {F : ∀ (U : Type) [CommGroup U], ((Y ⟶ X) → U) → U} (h : Triv L Y F) (r : Z ⟶ Y) :
    Triv L Z (fun U _ g => F U (fun ψ => g (r ≫ ψ))) := by
  obtain ⟨K, _, φ, ε, t, ht, e⟩ := h
  exact ⟨K, inferInstance, _, _, LB.pullGen L φ ε t r, DVR.pullGen_isGen _ _ _ _ ht _,
    fun U _ g => e U (fun ψ => g (r ≫ ψ))⟩

theorem Triv.exists_gen (hL : L.IsLB) {F : ∀ (U : Type) [CommGroup U], ((Y ⟶ X) → U) → U} (h : Triv L Y F)
    (f : Y ⟶ X) (hf : ∀ (U : Type) [CommGroup U] (g : (Y ⟶ X) → U), F U g = g f) :
    ∃ t : LB.Gen (L.pull f), t.IsGen := by
  obtain ⟨K, _, φ, ε, t, ht, e⟩ := h
  obtain ⟨t', ht', -⟩ := Geo.Tor.exists_gen hL (φ' := fun _ : PUnit => f) (ε' := fun _ => 1)
    (fun U _ g => by rw [e, hf]; simp) t ht
  exact ⟨t', ht'⟩

theorem triv_of_sec (θ : L.Sec) (f : Y ⟶ X) (hf : ∀ y, f y ∈ secNz θ) : Triv L Y (fun _ _ g => g f) := by
  have hu : ∀ j, IsUnit ((SpecialFibreGenerator.secAlong θ f).f j) := fun j =>
    Y.toRingedSpace.isUnit_of_isUnit_germ _ _ fun y hy => by
      obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hf y)
      obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 (SpecialFibreGenerator.mem_nonzeroLocus_secAlong θ f hi)
      exact (Y.mem_basicOpen _ y hy).1 (SpecialFibreGenerator.mem_basicOpen_of_chart _ hy hk)
  exact ⟨Fin 1, inferInstance, _, _, ⟨fun j => (hu j).unit⟩,
    fun i j => Units.ext ((SpecialFibreGenerator.secAlong θ f).compat i j), fun U _ g => by simp⟩

end

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {L : RigLB G} {T : Over S}

theorem triv_cub (c : CubicalStr G L) (x x' y : T ⟶ G) : Triv L.L T.left (fun _ _ h =>
    h (x * x' * y).left * (h (x * x').left)⁻¹ * (h (x * y).left)⁻¹ * (h (x' * y).left)⁻¹ * h x.left * h x'.left *
        h y.left * (h (1 : T ⟶ G).left)⁻¹) :=
  ⟨thK, inferInstance, _, _, LB.pullGen L.L (thφ G (x3 G)) thε c.t (lift x (lift x' y)).left,
    DVR.pullGen_isGen _ _ _ _ c.isGen _, fun _ _ h => prod_cub x x' y h⟩

theorem triv_one (L : RigLB G) (T : Over S) : Triv L.L T.left (fun _ _ h => h (1 : T ⟶ G).left) :=
  ⟨PUnit, inferInstance, _, _, LB.pullGen L.L (fun _ => eSec G) (fun _ => 1) L.rig T.hom,
    DVR.pullGen_isGen _ _ _ _ L.rigGen _, fun _ _ h => by rw [GlobalTheory.UU.one_left]; simp⟩

end GlobalTheory.Mum.CubeGen

namespace GlobalTheory.Mum

open CubeGen

theorem exists_gen_of_cubeTen (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (P : GlobalTheory.UU.CP G)
    (θ : P.L.L.Sec) (T : Over S) (x a b c : T ⟶ G) (W : T.left.Opens)
    (hW : ∀ f ∈ cubeTen x a b c, W ≤ f.left ⁻¹ᵁ secNz θ) :
    ∃ t : LB.Gen (P.L.L.pull (W.ι ≫ x.left)), t.IsGen := by
  have s : ∀ f ∈ cubeTen x a b c, Triv P.L.L W (fun _ _ g => g (W.ι ≫ f.left)) := fun f hf =>
    triv_of_sec θ _ fun y => hW f hf y.2
  have s₁ := s (x * a) (by simp [cubeTen])
  have s₂ := s (x * a⁻¹) (by simp [cubeTen])
  have s₃ := s a (by simp [cubeTen])
  have s₄ := s a⁻¹ (by simp [cubeTen])
  have s₅ := s (x * b) (by simp [cubeTen])
  have s₆ := s (x * c) (by simp [cubeTen])
  have s₇ := s (x * (b * c)⁻¹) (by simp [cubeTen])
  have s₈ := s b (by simp [cubeTen])
  have s₉ := s c (by simp [cubeTen])
  have s₀ := s (b * c)⁻¹ (by simp [cubeTen])
  have e := (triv_one P.L T).pull W.ι
  have c₁ := (triv_cub P.c x a a⁻¹).pull W.ι
  have c₂ := (triv_cub P.c x b c).pull W.ι
  have c₃ := (triv_cub P.c x (b * c) (b * c)⁻¹).pull W.ι
  have t₂ := ((((c₁.mul s₁).mul s₂).mul s₃.inv).mul s₄.inv)
  have t₃ := (((((((c₂.mul c₃).mul s₅).mul s₆).mul s₇).mul s₈.inv).mul s₉.inv).mul s₀.inv)
  refine ((t₃.mul t₂.inv).mul e).exists_gen P.L.isLB _ fun U _ g => ?_
  simp only [mul_inv_cancel_right, mul_inv_cancel, _root_.mul_assoc x b c]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorOnSmallerOpenOfNonvanishingSectioStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_generator_on_smaller_open_of_nonvanishing_section : ∀ (Z : Scheme.{0}) (L : LB Z), L.IsLB → ∀ (O O' : Z.Opens), O ≤ O' → ∀ u : LB.Sec (L.pull O'.ι), (∀ z : O'.toScheme, O'.ι z ∈ O → z ∈ nonzeroLocus u) → ∃ t : LB.Gen (L.pull O.ι), t.IsGen := by
  first | exact @GlobalTheory.GenRestrict.exists_gen_restrict | exact GlobalTheory.GenRestrict.exists_gen_restrict | (intros; apply GlobalTheory.GenRestrict.exists_gen_restrict <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorTopExteriorPowerStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_generator_top_exterior_power : ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (L : Type) [AddCommGroup L] [Module R L]
    [Module.Free R L] [Module.Finite R L] (n : ℕ), Module.finrank R L = n →
    ∀ (e : Fin n → (L →ₗ[R] R)) (D : R), D ≠ 0 → (∀ ω : L →ₗ[R] R, D • ω ∈ Submodule.span R (Set.range e)) →
    ∀ (l : ℕ), ∃ (δ₀ : L [⋀^Fin n]→ₗ[R] R) (u₀ : R), Submodule.span R {δ₀} = ⊤ ∧
      Matrix.detRowAlternating.compLinearMap (LinearMap.pi e) = u₀ • δ₀ ∧
      GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.val_vp R l (algebraMap R (FractionRing R) u₀) ≤
        n • GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.val_vp R l (algebraMap R (FractionRing R) D) := by
  first | exact @GlobalTheory.DetSpan.wedge_eq_smul_gen_val_le | exact GlobalTheory.DetSpan.wedge_eq_smul_gen_val_le | (intros; apply GlobalTheory.DetSpan.wedge_eq_smul_gen_val_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorTorsionBundleAbelianSchemeSqZeroStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_generator_torsion_bundle_abelianScheme_sqZero : ∀ (T : Type) [CommRing T] [IsLocalRing T] (e : T), (∀ a ∈ IsLocalRing.maximalIdeal T, a * e = 0) → e ∈ IsLocalRing.maximalIdeal T → ∀ (A : Over (Sp T)) [GrpObj A], IsAbelianScheme A → ∀ (M : LB A.left), M.IsLB → ∀ k : ℕ, IsUnit (k : T) → (∃ t : (GlobalTheory.UPel.HT.Hecke.lbPow M k).Gen, t.IsGen) → ∀ (X' : Scheme.{0}) (π : X' ⟶ A.left) (f' : X' ⟶ Sp (T ⧸ Ideal.span {e})), IsPullback π f' A.hom (spMap (Ideal.Quotient.mk (Ideal.span {e}))) → (∃ t : (M.pull π).Gen, t.IsGen) → ∃ t : M.Gen, t.IsGen := by
  first | (exact @GlobalTheory.CechPic.exists_isGen_of_lbPow_of_sqZero_abelianScheme) | (exact GlobalTheory.CechPic.exists_isGen_of_lbPow_of_sqZero_abelianScheme) | (intros; apply GlobalTheory.CechPic.exists_isGen_of_lbPow_of_sqZero_abelianScheme <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorTransferThroughTensorIso
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.TensGen

theorem exists_flat {X X' Y : Scheme.{0}} (M : LB X) {I K : Type} [Fintype I] [Fintype K] (F : I → (X' ⟶ X))
    (e : I → ℤ) (φ' : K → (Y ⟶ X')) (ε : K → ℤ)
    (t : LB.Gen (LB.LinComb M (fun p : K × I => φ' p.1 ≫ F p.2) (fun p => ε p.1 * e p.2))) (ht : t.IsGen) :
    ∃ t₂ : LB.Gen (LB.LinComb (LB.LinComb M F e) φ' ε), t₂.IsGen ∧
      ∀ (jj : K → I → M.ι) (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z), r z ∈ LB.wchart (LB.LinComb M F e) φ' jj →
        gm r z _ (t₂.s jj) = gm r z (LB.wchart M (fun p : K × I => φ' p.1 ≫ F p.2) (fun p => jj p.1 p.2))
          (t.s (fun p => jj p.1 p.2)) := by
  have le : ∀ jj : K → I → M.ι, LB.wchart (LB.LinComb M F e) φ' jj ≤
      LB.wchart M (fun p : K × I => φ' p.1 ≫ F p.2) (fun p => jj p.1 p.2) := fun jj y hy =>
    Set.mem_iInter.2 fun p => by
      have h₁ : (F p.2) ((φ' p.1) y) ∈ M.U (jj p.1 p.2) := Set.mem_iInter.1 (Set.mem_iInter.1 hy p.1) p.2
      exact h₁
  have v : ∀ (jj : K → I → M.ι) (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z), r z ∈ LB.wchart (LB.LinComb M F e) φ' jj →
      gm r z _ (res (le jj) (t.s (fun p => jj p.1 p.2))) =
        gm r z (LB.wchart M (fun p : K × I => φ' p.1 ≫ F p.2) (fun p => jj p.1 p.2)) (t.s (fun p => jj p.1 p.2)) :=
    fun jj Z r z hz => gm_res r z _ hz _
  refine ⟨⟨fun jj => res (le jj) (t.s (fun p => jj p.1 p.2))⟩, fun i j => unit_ext fun y hy => ?_, v⟩
  rw [map_mul, gm_res _ y _ hy, gm_res _ y _ hy]
  change gm (𝟙 Y) y _ (res (le i) _) = _ * gm (𝟙 Y) y _ (res (le j) _)
  rw [v i _ (𝟙 Y) y hy.1, v j _ (𝟙 Y) y hy.2, gen_trans ht (𝟙 Y) y (le i hy.1) (le j hy.2)]
  congr 1
  refine Eq.trans ?_ (gm_linComb (LB.LinComb M F e) φ' ε (𝟙 Y) y i j hy.1 hy.2).symm
  have b : ∀ a, gm (𝟙 Y ≫ φ' a) y ((LB.LinComb M F e).U (i a) ⊓ (LB.LinComb M F e).U (j a))
      ((LB.LinComb M F e).g (i a) (j a)) = ∏ k, gm ((𝟙 Y ≫ φ' a) ≫ F k) y (M.U (i a k) ⊓ M.U (j a k)) (M.g (i a k) (j a k)) ^ e k :=
    fun a => gm_linComb M F e (𝟙 Y ≫ φ' a) y (i a) (j a) (Set.mem_iInter.1 hy.1 a) (Set.mem_iInter.1 hy.2 a)
  simp only [b, trF, Fintype.prod_prod_type, ← Finset.prod_zpow, ← zpow_mul, Category.assoc]
  refine Finset.prod_congr rfl fun a _ => Finset.prod_congr rfl fun k _ => ?_
  rw [mul_comm]

theorem exists_gen_transfer : ∀ (R : Type) [CommRing R] [IsDomain R] (D D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D D' W) {Y : Scheme.{0}} {K : Type} [Fintype K] (φ' : K → (Y ⟶ D'.P.A.left)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb D.P.L (fun p : K × ((Fin r × Fin r) × Fin 4) => φ' p.1 ≫ tensφ T.pr p.2) (fun p => ε p.1 * tensε W p.2))), t.IsGen → ∃ t' : LB.Gen (LB.LinComb D'.P.L φ' ε), t'.IsGen ∧ ∀ (Z : Scheme.{0}) (q : Z ⟶ Y) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι) (J' : (Z ⟶ D'.P.A.left) → D'.P.L.ι), Good D.P.L z J → Good D'.P.L z J' → (∏ a, gm (q ≫ φ' a) z _ (T.w.s (fun k => J ((q ≫ φ' a) ≫ tensφ T.pr k), J' (q ≫ φ' a))) ^ ε a) * val t' q z J' = val t q z J := by
  intro R _ _ D D' r W T Y K _ φ' ε t ht
  obtain ⟨t₂, ht₂, h₂⟩ := exists_flat D.P.L (tensφ T.pr) (tensε W) φ' ε t ht
  have hA : (LB.LinComb (LB.LinComb D.P.L (tensφ T.pr) (tensε W)) φ' ε).IsLB :=
    LB.isLB_linComb (LB.isLB_linComb D.P.isLB _ _) _ _
  have hB : (LB.LinComb D'.P.L φ' ε).IsLB := LB.isLB_linComb D'.P.isLB _ _
  obtain ⟨t', ht', hv⟩ := GlobalTheory.WtTower.exists_gen_of_iso hA hB (isoInv (LB.linCombIso T.w φ' ε))
    (isoInv_isGen (DVR.linCombIso_isGen T.w T.w_gen φ' ε)) t₂ ht₂
  refine ⟨t', ht', fun Z q z J J' hJ hJ' => ?_⟩
  let i : K → (Fin r × Fin r) × Fin 4 → D.P.L.ι := fun a k => J ((q ≫ φ' a) ≫ tensφ T.pr k)
  let j : K → D'.P.L.ι := fun a => J' (q ≫ φ' a)
  have hi : q z ∈ LB.wchart (LB.LinComb D.P.L (tensφ T.pr) (tensε W)) φ' i :=
    Set.mem_iInter.2 fun a => Set.mem_iInter.2 fun k => hJ ((q ≫ φ' a) ≫ tensφ T.pr k)
  have hj : q z ∈ LB.wchart D'.P.L φ' j := hJ'.mem φ' q
  have e1 := hv Z q z j i hj hi
  have hm : q z ∈ (LB.LinComb D'.P.L φ' ε).U j ⊓ (LB.LinComb (LB.LinComb D.P.L (tensφ T.pr) (tensε W)) φ' ε).U i :=
    ⟨hj, hi⟩
  have hm' : q z ∈ (LB.div (LB.LinComb (LB.LinComb D.P.L (tensφ T.pr) (tensε W)) φ' ε) (LB.LinComb D'.P.L φ' ε)).U (i, j) :=
    ⟨hi, hj⟩
  have e2 : gm q z ((LB.LinComb D'.P.L φ' ε).U j ⊓ (LB.LinComb (LB.LinComb D.P.L (tensφ T.pr) (tensε W)) φ' ε).U i)
      ((isoInv (LB.linCombIso T.w φ' ε)).s (j, i)) =
      (∏ a, gm (q ≫ φ' a) z _ (T.w.s (i a, j a)) ^ ε a)⁻¹ :=
    (map_inv _ _).trans (congrArg (·⁻¹) ((gm_res q z _ hm _).trans
      (GlobalTheory.WtTower.gm_linCombIso T.w φ' ε (i, j) q z hm')))
  have e3 : gm q z _ (t₂.s i) = val t q z J :=
    (h₂ i Z q z hi).trans (val_of t q z J _ fun p => by simp only [i, Category.assoc]).symm
  change _ * gm q z _ (t'.s j) = _
  rw [e1, e2, e3]
  exact mul_inv_cancel_left _ _

end GlobalTheory.TensGen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenericFibresCommonPullDegToFieldStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_generic_fibres_common_pullDeg_to_field : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D₁ D₂ : DegData R (maximalIdeal R)) (W : Type) [CommRing W] [IsDomain W] (φ : R →+* W), Function.Injective φ → ∀ D' : DegPre W, IsPullDeg φ D₁.toPre D' → IsPullDeg φ D₂.toPre D' → ∃ (E₁ E₂ : DegPre (FractionRing R)) (L : Type) (_ : Field L) (β : FractionRing R →+* L) (E' : DegPre L), Nonempty (IsPullDeg (algebraMap R (FractionRing R)) D₁.toPre E₁) ∧ Nonempty (IsPullDeg (algebraMap R (FractionRing R)) D₂.toPre E₂) ∧ Nonempty (IsPullDeg β E₁ E') ∧ Nonempty (IsPullDeg β E₂ E') := by
  first | exact @GlobalTheory.Mum.exists_generic_common_pull | exact GlobalTheory.Mum.exists_generic_common_pull | (intros; apply GlobalTheory.Mum.exists_generic_common_pull <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenericallyRegularQuotientDominatingPrimeStatement
section
open IsLocalRing TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_genericallyRegular_quotient_dominating_prime : ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsRegularRing Λ] [PerfectField (FractionRing Λ)] (B : Type) [CommRing B] [Algebra Λ B] [Algebra.FiniteType Λ B] (p : Ideal B) [p.IsPrime], (∀ a : Λ, algebraMap Λ B a ∈ p → a = 0) → ∃ g, g ∉ p ∧ ∀ (q : Ideal B) [q.IsPrime], p ≤ q → g ∉ q → IsRegularLocalRing (Localization.AtPrime q ⧸ p.map (algebraMap B (Localization.AtPrime q))) := by
  first | exact @GlobalTheory.prime_generically_regular_quotient | exact GlobalTheory.prime_generically_regular_quotient | (intros; apply GlobalTheory.prime_generically_regular_quotient <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGloballyGeneratedAmplePowerToroidalPullbacStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_globallyGenerated_ample_power_toroidalPullback : ∀ (o : Type) [CommRing o] [IsNoetherianRing o] (Z S : Scheme.{0}) (z : Z ⟶ Sp o) (π : S ⟶ Z) (OZ : LB Z) (W M : LB S) (a N : ℕ), IsProjOver z → OZ.IsLB → GlobalTheory.IsAmpleLB OZ → W.IsLB → M.IsLB → 1 ≤ a → 1 ≤ N → LBIso (lbPow W N) (lbPow (OZ.pull π) a) → (∃ k₀ : ℕ, ∀ k, k₀ ≤ k → GlobalTheory.IsAmpleLB (GlobalTheory.CechPic.tens (lbPow (OZ.pull π) k) M)) → ∃ N' : ℕ, 1 ≤ N' ∧ GlobalTheory.IsGenerated (lbPow W N') ∧ ∃ k : ℕ, GlobalTheory.IsAmpleLB (GlobalTheory.CechPic.tens (lbPow W (N' * k)) M) := by
  first | exact @GlobalTheory.PullPowGen.exists_isGenerated_and_isAmpleLB | exact GlobalTheory.PullPowGen.exists_isGenerated_and_isAmpleLB | (intros; apply GlobalTheory.PullPowGen.exists_isGenerated_and_isAmpleLB <;> assumption)
end

