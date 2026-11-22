import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2647
import Development.AbelianVarietyTheory.Definitions.Divisors.OrdGeOfForall
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0011
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.RegularOfBoundedAtPadicAlgClPoints
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2381
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MetricFlagQuotientConnectingMap
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0025
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MetricFlagSuccessiveQuotientExact
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2625
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsTauZeroNonzeroAll
import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2114
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0010
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0141
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2170
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2515
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveLiftIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2404
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2564
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2648
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0016
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2411

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRangeOfBaseChangeRatioSections
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
namespace GlobalTheory.ConstDescent

open TensorProduct

theorem mem_range_of_tmul_one_eq {K L B : Type} [Field K] [Field L] [CommRing B] [Algebra K L]
    [Algebra K B] (b₁ b₂ : B) (l : L) (hb : b₂ ≠ 0) (h : b₁ ⊗ₜ[K] (1 : L) = b₂ ⊗ₜ[K] l) :
    l ∈ Set.range (algebraMap K L) := by
  by_contra hl
  have hx : l ∉ (K ∙ (1 : L)) := by
    intro hm
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hm
    exact hl ⟨c, by rw [Algebra.algebraMap_eq_smul_one, hc]⟩
  obtain ⟨f, hf, hp⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hx inferInstance
  have h1 : f 1 = 0 := by
    have : f 1 ∈ (K ∙ (1 : L)).map f :=
      Submodule.mem_map_of_mem (Submodule.mem_span_singleton_self 1)
    rw [hp] at this
    simpa using this
  have h2 := congrArg ((TensorProduct.rid K B).toLinearMap ∘ₗ LinearMap.lTensor B f) h
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    LinearMap.lTensor_tmul, TensorProduct.rid_tmul, h1, zero_smul] at h2
  exact hb ((smul_eq_zero.1 h2.symm).resolve_left hf)

end GlobalTheory.ConstDescent

namespace GlobalTheory.ConstDescent

theorem exists_affine_res_ne_zero {X : Scheme.{0}} {U : X.Opens} (f : Γ(X, U)) (hf : f ≠ 0) :
    ∃ (V : X.Opens) (hV : IsAffineOpen V) (hVU : V ≤ U), X.presheaf.map (homOfLE hVU).op f ≠ 0 := by
  have : ∃ (x : X) (hx : x ∈ U), X.presheaf.germ U x hx f ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hf (TopCat.Presheaf.section_ext X.sheaf U f 0 (fun x hx => by rw [map_zero]; exact hc x hx))
  obtain ⟨x, hx, hne⟩ := this
  obtain ⟨V, hV, hxV, hVU⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := U) hx
  refine ⟨V, hV, hVU, fun h0 => hne ?_⟩
  rw [← TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE hVU) x hxV, h0, map_zero]

end GlobalTheory.ConstDescent

namespace GlobalTheory.ConstDescent

theorem fromSpec_appLE_hom {X : Scheme.{0}} {U V : X.Opens} (hV : IsAffineOpen V) (hVU : V ≤ U)
    (e : ⊤ ≤ hV.fromSpec ⁻¹ᵁ U) (f : Γ(X, U)) :
    (Scheme.ΓSpecIso Γ(X, V)).hom.hom ((hV.fromSpec.appLE U ⊤ e).hom f) =
      (X.presheaf.map (homOfLE hVU).op).hom f := by
  have : hV.fromSpec.appLE U ⊤ e ≫ (Scheme.ΓSpecIso Γ(X, V)).hom =
      X.presheaf.map (homOfLE hVU).op := by
    rw [Scheme.Hom.appLE, IsAffineOpen.fromSpec_app_of_le hV U hVU, Category.assoc, Category.assoc,
      Category.assoc, ← Functor.map_comp_assoc]
    have h' : ((homOfLE le_top).op ≫ (homOfLE e).op :
        Opposite.op (⊤ : (Spec Γ(X, V)).Opens) ⟶ Opposite.op ⊤) = 𝟙 _ := Subsingleton.elim _ _
    rw [h', CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id, Category.comp_id]
  rw [← this]
  rfl

theorem appLE_top_top {X Y : Scheme.{0}} (f : X ⟶ Y) (e : (⊤ : X.Opens) ≤ f ⁻¹ᵁ ⊤) :
    f.appLE ⊤ ⊤ e = f.appTop := by
  rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
  rfl

theorem appLE_congr {X Y : Scheme.{0}} {f g : X ⟶ Y} (hfg : f = g) (U : Y.Opens) (V : X.Opens)
    (e₁ : V ≤ f ⁻¹ᵁ U) (e₂ : V ≤ g ⁻¹ᵁ U) : f.appLE U V e₁ = g.appLE U V e₂ := by
  subst hfg; rfl

end GlobalTheory.ConstDescent

namespace GlobalTheory.ConstDescent

open TensorProduct

theorem mem_range_of_pullback_eq {K L : Type} [Field K] [Field L] (ψ : K →+* L) {X : Scheme.{0}}
    (h : X ⟶ Sp K) (U : X.Opens) (f₁ f₂ : Γ(X, U)) (l : L) (hf : f₂ ≠ 0)
    (heq : ((pullback.fst h (spMap ψ)).app U).hom f₁ =
      ((pullback.fst h (spMap ψ)).app U).hom f₂ * resTop _ (scal (pullback.snd h (spMap ψ)) l)) :
    l ∈ Set.range ψ := by
  obtain ⟨V, hV, hVU, hne⟩ := exists_affine_res_ne_zero f₂ hf
  let B : CommRingCat := Γ(X, V)
  let e : Spec B ⟶ X := hV.fromSpec
  let α : CommRingCat.of K ⟶ B := Spec.preimage (e ≫ h)
  letI : Algebra K B := α.hom.toAlgebra
  letI : Algebra K L := ψ.toAlgebra
  let Z : CommRingCat := CommRingCat.of (B ⊗[K] L)
  let a : Spec Z ⟶ Spec B := Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom)
  let b : Spec Z ⟶ Sp L :=
    Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : L →ₐ[K] B ⊗[K] L).toRingHom)
  have hcomm : (a ≫ e) ≫ h = b ≫ spMap ψ := by
    rw [Category.assoc, ← Spec.map_preimage (e ≫ h)]
    simp only [a, b, spMap, ← Spec.map_comp]
    congr 1
    ext x
    show (algebraMap K B x) ⊗ₜ[K] (1 : L) = (1 : B) ⊗ₜ[K] (algebraMap K L x)
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  let k : Spec Z ⟶ pullback h (spMap ψ) := pullback.lift (a ≫ e) b hcomm
  have hk1 : k ≫ pullback.fst h (spMap ψ) = a ≫ e := pullback.lift_fst _ _ _
  have hk2 : k ≫ pullback.snd h (spMap ψ) = b := pullback.lift_snd _ _ _
  have heU : ⊤ ≤ e ⁻¹ᵁ U := by
    intro z _
    show e z ∈ U
    apply hVU
    have hr : e z ∈ Set.range hV.fromSpec := ⟨z, rfl⟩
    rw [hV.range_fromSpec] at hr
    exact hr
  have hk : ⊤ ≤ k ⁻¹ᵁ ((pullback.fst h (spMap ψ)) ⁻¹ᵁ U) := by
    intro z _
    show (pullback.fst h (spMap ψ)) (k z) ∈ U
    rw [← Scheme.Hom.comp_apply, hk1, Scheme.Hom.comp_apply]
    exact heU (show a z ∈ (⊤ : (Spec B).Opens) from trivial)

  have heU' : ⊤ ≤ (a ≫ e) ⁻¹ᵁ U := by
    intro z _
    exact heU (show a z ∈ (⊤ : (Spec B).Opens) from trivial)
  have key1m : (pullback.fst h (spMap ψ)).app U ≫ k.appLE _ ⊤ hk =
      e.appLE U ⊤ heU ≫ (Scheme.ΓSpecIso B).hom ≫
        CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom ≫ (Scheme.ΓSpecIso Z).inv := by
    refine (Scheme.Hom.comp_appLE k _ U ⊤ hk).symm.trans ?_
    refine (appLE_congr hk1 U ⊤ _ heU').trans ?_
    refine (Scheme.Hom.appLE_comp_appLE a e U ⊤ ⊤ heU (fun _ _ => trivial)).symm.trans ?_
    congr 1
    refine (appLE_top_top a _).trans ?_
    rw [← Category.assoc, Iso.eq_comp_inv]
    exact Scheme.ΓSpecIso_naturality _
  have key2m : (Scheme.ΓSpecIso (CommRingCat.of L)).inv ≫ (pullback.snd h (spMap ψ)).appTop ≫
      k.appTop = CommRingCat.ofHom (Algebra.TensorProduct.includeRight : L →ₐ[K] B ⊗[K] L).toRingHom ≫
        (Scheme.ΓSpecIso Z).inv := by
    rw [← Scheme.Hom.comp_appTop, hk2, ← Scheme.ΓSpecIso_inv_naturality]
  have key1 : ∀ s : Γ(X, U), (k.appLE _ ⊤ hk).hom (((pullback.fst h (spMap ψ)).app U).hom s) =
      (Scheme.ΓSpecIso Z).inv.hom
        (((Scheme.ΓSpecIso B).hom.hom ((e.appLE U ⊤ heU).hom s)) ⊗ₜ[K] (1 : L)) := fun s =>
    congrArg (fun φ => φ.hom s) key1m
  have key2 : (k.appLE _ ⊤ hk).hom (resTop _ (scal (pullback.snd h (spMap ψ)) l)) =
      (Scheme.ΓSpecIso Z).inv.hom ((1 : B) ⊗ₜ[K] l) := by
    have e1 : ∀ c, (k.appLE _ ⊤ hk).hom (resTop ((pullback.fst h (spMap ψ)) ⁻¹ᵁ U) c) =
        k.appTop.hom c := by
      intro c
      show ((pullback h (spMap ψ)).presheaf.map _ ≫ k.appLE _ ⊤ hk).hom c = _
      rw [Scheme.Hom.map_appLE, appLE_top_top]
    rw [e1]
    exact congrArg (fun φ => φ.hom l) key2m
  have h3 := congrArg (k.appLE _ ⊤ hk).hom heq
  rw [map_mul, key1, key1, key2, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, _root_.mul_one,
    _root_.one_mul] at h3
  have inj : Function.Injective (Scheme.ΓSpecIso Z).inv.hom := fun x y hxy => by
    simpa using congrArg (Scheme.ΓSpecIso Z).hom.hom hxy
  have h4 := inj h3
  have hb : (Scheme.ΓSpecIso B).hom.hom ((e.appLE U ⊤ heU).hom f₂) ≠ 0 := by
    rw [fromSpec_appLE_hom hV hVU heU f₂]
    exact hne
  obtain ⟨c, hc⟩ := mem_range_of_tmul_one_eq _ _ l hb h4
  exact ⟨c, hc⟩

end GlobalTheory.ConstDescent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSpanSupPowOfForallCompleteDvrLocalTestStatement
section
open AlgebraicGeometry CategoryTheory IsLocalRing ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef GlobalTheory.Poinc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_span_sup_pow_of_forall_complete_dvr_local_test : ∀ (O : Type) [CommRing O] [IsDomain O] [IsLocalRing O] [IsIntegrallyClosed O] [CharZero O] [Algebra.EssFiniteType ℤ O] (g : O) (b : ℕ → O), g ≠ 0 → (∀ m n, m ≤ n → b m - b n ∈ maximalIdeal O ^ m) → (∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (maximalIdeal V) V → ∀ ρ : O →+* V, Function.Injective ρ → IsLocalHom ρ → ∀ e, ρ (b e) ∈ Ideal.span {ρ g} ⊔ maximalIdeal V ^ e) → ∀ n, b n ∈ Ideal.span {g} ⊔ maximalIdeal O ^ n := by
  first | exact @GlobalTheory.Poinc.mem_span_sup_pow_of_forall_complete_dvr | exact GlobalTheory.Poinc.mem_span_sup_pow_of_forall_complete_dvr | (intros; apply GlobalTheory.Poinc.mem_span_sup_pow_of_forall_complete_dvr <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemStalkOfClassicalValuesNormLeOne
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.Poinc

theorem mem_O_of_norm_val_le_one : ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (M : RatModel o' Ω), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.Z → ∀ (U₀ : M.Z.Opens), (U₀ : Set M.Z).Nonempty → ∀ x : M.Z, IsClosed ({x} : Set M.Z) → ∀ f ∈ M.ringOn (U₀ : Set M.Z), (∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z), M.Cen U₀ x y → ‖M.val (gPt p ≫ y) f‖ ≤ 1) → f ∈ M.O x := by
  intro o' Ω _ _ _ _ M hn U₀ hU x hx f hf hb
  obtain ⟨h1, h2⟩ := flat_and_lft_toInt M
  obtain ⟨φ, rfl⟩ := (RatModel.mem_ringOn_iff_exists hU).1 hf
  obtain ⟨W, ψ, hxW, h⟩ := GlobalTheory.regular_of_bounded_at_padicAlgCl_points.1 M.Z (M.s ≫ spMap (algebraMap ℤ o')) x hx
    (hn x).2 U₀ φ hU fun p _ y e1 e2 => (RatModel.val_valF e2 φ) ▸ hb p y ⟨e1, e2⟩
  have hWU := M.nonempty_inf ⟨x, hxW⟩ hU
  have e : valF M.pt W ψ = valF M.pt U₀ φ := (M.valF_resG inf_le_left hWU ψ).symm.trans
    ((congrArg _ h).trans (M.valF_resG inf_le_right hWU φ))
  exact e ▸ RatModel.valF_mem_O hxW ψ

end GlobalTheory.Poinc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MetricFlagQuotientConnectingMapStatement
section
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.metric_flag_quotient_connecting_map : ∀ (k : Type) [CommRing k] (B Y Y₁ : Scheme.{0}) (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (q₁ : Y₁ ⟶ Sp k)
    (π : Y ⟶ B) (σ : Y₁ ⟶ B) (ρ : Y ⟶ Y₁) (w : π ≫ q = p) (wσ : ρ ≫ σ = π) (wρ : ρ ≫ q₁ = p) (wq : σ ≫ q = q₁)
    (E : B.Modules) (n : ℕ) (h : VMetric q E n) (H : h.IsCInf) (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) n)
    (l : Fin n) (A₀ A₁ : Y₁.Modules) (u : A₀ ⟶ A₁) (v : A₁ ⟶ (Scheme.Modules.pullback σ).obj E),
    GlobalTheory.VB.IsSubbundle u → GlobalTheory.VB.IsSubbundle v → GlobalTheory.VB.IsVB A₀ l → GlobalTheory.VB.IsVB A₁ (l + 1) →
    (∃ e : (Scheme.Modules.pullback ρ).obj A₁ ≅ fl.F l.succ, e.hom ≫ fl.ι l.succ =
      (Scheme.Modules.pullback ρ).map v ≫ (Scheme.Modules.pullbackComp ρ σ).hom.app E ≫
        (Scheme.Modules.pullbackCongr wσ).hom.app E) →
    (∃ e : (Scheme.Modules.pullback ρ).obj A₀ ≅ fl.F l.castSucc, e.hom ≫ fl.ι l.castSucc =
      (Scheme.Modules.pullback ρ).map (u ≫ v) ≫ (Scheme.Modules.pullbackComp ρ σ).hom.app E ≫
        (Scheme.Modules.pullbackCongr wσ).hom.app E) →
    ∃ M : HermLB q₁, (M.pull ρ wρ).Isometric (VMetric.grLB fl l (H.pull π w)) := by
  first | exact @GlobalTheory.StepLine.isometric_grLB_of_steps_pull | exact GlobalTheory.StepLine.isometric_grLB_of_steps_pull | (intros; apply GlobalTheory.StepLine.isometric_grLB_of_steps_pull <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MetricFlagSuccessiveQuotientExactStatement
section
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.metric_flag_successive_quotient_exact : ∀ (k : Type) [CommRing k] (B Y Y₁ : Scheme.{0}) (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (q₁ : Y₁ ⟶ Sp k)
    (π : Y ⟶ B) (σ : Y₁ ⟶ B) (ρ : Y ⟶ Y₁) (w : π ≫ q = p) (wσ : ρ ≫ σ = π) (wρ : ρ ≫ q₁ = p) (wq : σ ≫ q = q₁)
    (E : B.Modules) (n : ℕ) (h : VMetric q E n) (H : h.IsCInf) (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) n)
    (i i' : Fin n), (i' : ℕ) = i + 1 → ∀ (S P E₁ : Y₁.Modules) (s : S ⟶ P) (j : P ⟶ (Scheme.Modules.pullback σ).obj E)
    (t : P ⟶ E₁) (wst : s ≫ t = 0) (fl₁ : Vert.Flag ((Scheme.Modules.pullback ρ).obj E₁) 2),
    (ShortComplex.mk s t wst).ShortExact → GlobalTheory.VB.IsSubbundle s → GlobalTheory.VB.IsSubbundle j → GlobalTheory.VB.IsVB S i →
    GlobalTheory.VB.IsVB P ((i : ℕ) + 2) → GlobalTheory.VB.IsVB E₁ 2 →
    (∃ e : (Scheme.Modules.pullback ρ).obj P ≅ fl.F i'.succ, e.hom ≫ fl.ι i'.succ =
      (Scheme.Modules.pullback ρ).map j ≫ (Scheme.Modules.pullbackComp ρ σ).hom.app E ≫
        (Scheme.Modules.pullbackCongr wσ).hom.app E) →
    (∃ e : (Scheme.Modules.pullback ρ).obj S ≅ fl.F i.castSucc, e.hom ≫ fl.ι i.castSucc =
      (Scheme.Modules.pullback ρ).map (s ≫ j) ≫ (Scheme.Modules.pullbackComp ρ σ).hom.app E ≫
        (Scheme.Modules.pullbackCongr wσ).hom.app E) →
    (∃ (x : fl.F i.succ ⟶ (Scheme.Modules.pullback ρ).obj P) (g : fl.F i.succ ⟶ fl₁.F 1),
      x ≫ (Scheme.Modules.pullback ρ).map j ≫ (Scheme.Modules.pullbackComp ρ σ).hom.app E ≫
        (Scheme.Modules.pullbackCongr wσ).hom.app E = fl.ι i.succ ∧
      g ≫ fl₁.ι 1 = x ≫ (Scheme.Modules.pullback ρ).map t ∧ Epi g) →
    ∃ (h₁ : VMetric q₁ E₁ 2) (H₁ : h₁.IsCInf),
      (VMetric.grLB fl₁ 0 (H₁.pull ρ wρ)).Isometric (VMetric.grLB fl i (H.pull π w)) ∧
      (VMetric.grLB fl₁ 1 (H₁.pull ρ wρ)).Isometric (VMetric.grLB fl i' (H.pull π w)) := by
  first | exact @GlobalTheory.SubqPair.exists_isometric_pair | exact GlobalTheory.SubqPair.exists_isometric_pair | (intros; apply GlobalTheory.SubqPair.exists_isometric_pair <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedArithIntersectionNonnegOfSmallSectionDiff
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.HSNef

open MvPolynomial in

theorem mixed_diff_nonneg : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (A B : HermLB p) (Φ : MvPolynomial (Fin 2) ℝ →ₗ[ℝ] ℝ), IsArFun ![A, B] D Φ → Le B A → ∀ x y : ℕ, HtNef ((A.pow x).tens (B.pow y)) D → 0 ≤ Φ ((MvPolynomial.X 0 - MvPolynomial.X 1) * (MvPolynomial.C (x : ℝ) * MvPolynomial.X 0 + MvPolynomial.C (y : ℝ) * MvPolynomial.X 1) ^ D) := by
  intro hC k _ X _ p D hX A B Φ hΦ hle x y hN
  classical
  haveI := hX.isLocallyNoetherian
  obtain ⟨s, hs, hs0⟩ := (GlobalTheory.T.hermLBLeBySmallSection_iff_exists_smallSection_difference k X p A B).1 hle
  have hg :=  (sec_ne_zero_iff s).1 hs0
  let L : Fin 2 → HermLB p := ![A, B]
  let F : Option (Fin 2) → HermLB p := fun o => o.elim (A.tens B.dual) L
  let E : Option (Fin 2) → Fin 2 → ℤ := fun o => o.elim ![1, -1] (fun i => Pi.single i 1)
  have hiso : ∀ j, (comb L (E j)).Isometric (F j) := by
    rintro (_ | i)
    · apply HermLB.icls_eq_iff.1
      simp [icls_comb, Fin.sum_univ_two, L, E, F, HermLB.icls_tens, HermLB.icls_dual, sub_eq_add_neg]
    · exact isometric_comb_single L i
  have hΦ' := ((hC.arIso k X p D hX).2 (Fin 2) L Φ hΦ).2.2 (Option (Fin 2)) F E hiso
  let n : Fin 2 → ℤ := ![(x : ℤ), (y : ℤ)]
  obtain ⟨h, hh⟩ := (hC.arExists k X p D hX).1 (comb L n)
  have hNiso : (comb L n).Isometric ((A.pow x).tens (B.pow y)) := by
    apply HermLB.icls_eq_iff.1
    simp [icls_comb, Fin.sum_univ_two, L, n, HermLB.icls_tens, HermLB.icls_pow]
  have hr := isRatSec_ratOfSec s hg
  obtain ⟨-, hmix⟩ := hC.arMix k X p D hX (Fin 2) (A.tens B.dual) L _ hΦ' n h hh (ratOfSec s hg) hr
  have hpoly : aeval (fun j => lin fun i => ((E j i : ℤ) : ℝ))
      (MvPolynomial.X none * rename some (lin fun i => ((n i : ℤ) : ℝ)) ^ D) =
      (MvPolynomial.X 0 - MvPolynomial.X 1) * (C (x : ℝ) * MvPolynomial.X 0 + C (y : ℝ) * MvPolynomial.X 1) ^ D := by
    simp [aeval_rename, lin, Fin.sum_univ_two, E, n, Function.comp_def, Pi.single_apply]
    left
    ring
  rw [LinearMap.comp_apply, AlgHom.toLinearMap_apply, hpoly] at hmix
  rw [hmix]
  have h1 : 0 ≤ ∑ᶠ z, (((A.tens B.dual).div hr).mult z : ℝ) * h z :=
    finsum_nonneg fun z => mul_nonneg (Int.cast_nonneg (mult_divOfSec_nonneg (hL := (A.tens B.dual).isLB) z))
      (hN.2 h (hNiso.isArithHeight hX hh) z)
  have h2 : ∀ σ, ((comb L n).φ σ).chernInt D (offSupp p σ ((A.tens B.dual).div hr))
      (logNorm ((A.tens B.dual).φ σ) (ratOfSec s hg)) ≤ 0 := by
    intro σ
    have hneg : ((comb L n).φ σ).chernPart D (-1) = 0 := by
      rw [hNiso.chernPart_eq]
      exact Weight.chernPart_neg_eq_zero (((A.pow x).tens (B.pow y)).cInf σ) (hN.1 σ)
    rw [Weight.chernInt, hneg, MeasureTheory.Measure.restrict_zero, MeasureTheory.integral_zero_measure, sub_zero]
    refine MeasureTheory.setIntegral_nonpos (isOpen_offSupp _).measurableSet fun z hz => ?_
    have hz' : z ∈ ptsIn p σ (Out.nonzeroLocus s) := by
      rw [← offSupp_divOfSec (hL := (A.tens B.dual).isLB)]
      exact hz
    rw [logNorm_ratOfSec _ hz']
    have h0 : 0 ≤ ((A.tens B.dual).φ σ).nsq (secVal p σ s) z := by
      unfold Weight.nsq
      positivity
    have := Real.log_nonpos h0 (hs σ z)
    linarith
  have h3 : (comb L n).archInt (A.tens B.dual) D hr ≤ 0 := by
    have := finsum_nonneg fun σ => neg_nonneg.2 (h2 σ)
    rw [finsum_neg_distrib] at this
    unfold HermLB.archInt
    linarith
  linarith

end GlobalTheory.HSNef
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelWeightGapL1CardBoundStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.model_weight_gap_l1_card_bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), GoodEmb c σ → IsUnf U → 1 ≤ Dw.p → 1 ≤ Dw.q → ∀ (u1 : GlobalTheory.AllWt.Weight Dw) (g : ℝ), (∀ τ (a b : Fin (Dw.p + Dw.q)), (b : ℕ) = a + 1 → g ≤ (u1 τ a : ℝ) - u1 τ b) → ∀ k : U.Comp, (∀ τ (a b : Fin r), (b : ℕ) = a + 1 → (b : ℕ) ≠ (U.X k).p0 → g ≤ (modelWt U (wtOf Dw u1 0) k τ a : ℝ) - modelWt U (wtOf Dw u1 0) k τ b) ∧ (∀ τ (a b : Fin r), (a : ℕ) = 0 → (b : ℕ) = r - 1 → g ≤ (modelWt U (wtOf Dw u1 0) k τ b : ℝ) - modelWt U (wtOf Dw u1 0) k τ a) ∧ (∑ τ, ∑ a, |(modelWt U (wtOf Dw u1 0) k τ a : ℝ)|) = GlobalTheory.CovHt.l1 u1 ∧ (U.X k).Ψ.card = Nat.card (GlobalTheory.AllWt.Psi H) := by
  first | exact @GlobalTheory.ModelWtGap.model_weight_gap_l1_card | exact GlobalTheory.ModelWtGap.model_weight_gap_l1_card | (intros; apply GlobalTheory.ModelWtGap.model_weight_gap_l1_card <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModuleActionOfFieldFibresStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.RealMult.Obj

attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.module_action_of_field_fibres : ∀ (R O : Type) [CommRing R] [CommRing O] [Module.Free ℤ O] [Module.Finite ℤ O] (M : Type)
    [AddCommGroup M] [Module R M] [Module O M] [SMulCommClass R O M] [Module.Finite R M] [Module.Projective R M],
    (∀ (K : Type) [Field K] [Algebra R K], ∃ (N : Type) (_ : AddCommGroup N) (_ : Module K N) (_ : Module O N)
      (_ : SMulCommClass K O N) (e : K ⊗[R] M ≃ₗ[K] N),
      (∀ (a : O) (m : M), e (1 ⊗ₜ (a • m)) = a • e (1 ⊗ₜ m)) ∧
      letI : Module (K ⊗[ℤ] O) N := TensorProduct.Algebra.module
      Module.Invertible (K ⊗[ℤ] O) N) →
    letI : Module (R ⊗[ℤ] O) M := TensorProduct.Algebra.module
    Module.Invertible (R ⊗[ℤ] O) M := by
  first | exact @GlobalTheory.invertible_of_fibres_invertible | exact GlobalTheory.invertible_of_fibres_invertible | (intros; apply GlobalTheory.invertible_of_fibres_invertible <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MonomorphismTrivialOnKernelStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.LatVal GlobalTheory.LatJet

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.monomorphism_trivial_on_kernel : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀), Function.Surjective π →
    (∃ N : ℕ, RingHom.ker π ^ N = ⊥) → ∀ (A : Over (Sp R)) [GrpObj A], IsProper A.hom →
    ∀ (n : ℕ) (D : Over (Sp R)) [GrpObj D], IsSeparated D.hom → ∀ (x : Fin n → (A ⟶ D)), (∀ j, IsMonHom (x j)) →
    (∀ (T₀ : Over (Sp R₀)) (y : Over.mk (T₀.hom ≫ spMap π) ⟶ A), (∀ j, y ≫ x j = 1) → y = 1) →
    ∀ (T : Over (Sp R)) (y : T ⟶ A), (∀ j, y ≫ x j = 1) → y = 1 := by
  first | exact @GlobalTheory.KernelThickening.kernel_trivial_of_nilpotent | exact GlobalTheory.KernelThickening.kernel_trivial_of_nilpotent | (intros; apply GlobalTheory.KernelThickening.kernel_trivial_of_nilpotent <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MorphismDescendsNearFibreRigidity
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.MorDesc

theorem factor_of_isIso_appTop {X T A : Scheme.{0}} (f : X ⟶ T) [IsIso f.appTop] [IsAffine A]
    (g : X ⟶ A) : ∃ g₀ : T ⟶ A, f ≫ g₀ = g := by
  refine ⟨T.toSpecΓ ≫ Spec.map (g.appTop ≫ inv f.appTop) ≫ A.isoSpec.inv, ?_⟩
  rw [← Category.assoc, Scheme.toSpecΓ_naturality, Category.assoc, ← Category.assoc (Spec.map _),
    ← Spec.map_comp, Category.assoc, IsIso.inv_hom_id, Category.comp_id, ← Category.assoc,
    ← Scheme.toSpecΓ_naturality, Category.assoc, ← Scheme.isoSpec_hom, Iso.hom_inv_id, Category.comp_id]

theorem morphism_descends : ∀ (R : Type) [CommRing R] (S Y Z W : Scheme.{0}) (π : S ⟶ Sp R) (y : Y ⟶ Sp R) (p : Z ⟶ Y) (q : Z ⟶ S), IsProper π → Surjective π → Function.Bijective π.appTop.hom → Flat y → IsPullback p q y π → ∀ (O : Z.Opens) (h : O.toScheme ⟶ W) (y₀ : Y) (w : W), (∀ z : Z, p z = y₀ → z ∈ O) → (∀ z : O.toScheme, p (O.ι z) = y₀ → h z = w) → ∃ (V : Y.Opens) (hV : p ⁻¹ᵁ V ≤ O) (h₀ : V.toScheme ⟶ W), y₀ ∈ V ∧ (p ∣_ V) ≫ h₀ = Z.homOfLE hV ≫ h := by
  intro R _ S Y Z W π y p q hprop _ hbij hflat hpb O h y₀ w hfib hconst
  haveI : IsProper π := hprop
  haveI : IsProper p := MorphismProperty.of_isPullback (P := @IsProper) hpb.flip hprop
  obtain ⟨O', hO', hwO', -⟩ := exists_isAffineOpen_mem_and_subset (show w ∈ (⊤ : W.Opens) from trivial)
  haveI : IsAffine O'.toScheme := hO'
  let T : Z.Opens := O.ι ''ᵁ (h ⁻¹ᵁ O')
  have hTO : T ≤ O := Scheme.Opens.ι_image_le O _
  have hcl : IsClosed (p '' (T : Set Z)ᶜ) := p.isClosedMap _ T.isOpen.isClosed_compl
  let V : Y.Opens := ⟨(p '' (T : Set Z)ᶜ)ᶜ, hcl.isOpen_compl⟩
  have hVT : p ⁻¹ᵁ V ≤ T := by
    intro z hz
    by_contra hzT
    exact hz ⟨z, hzT, rfl⟩
  have hy₀ : y₀ ∈ V := by
    rintro ⟨z, hzT, hz⟩
    apply hzT
    have hzO := hfib z hz
    refine ⟨⟨z, hzO⟩, ?_, Scheme.Opens.ι_apply O _⟩
    show h ⟨z, hzO⟩ ∈ O'
    rw [hconst ⟨z, hzO⟩ (by rw [Scheme.Opens.ι_apply]; exact hz)]
    exact hwO'
  have hV : p ⁻¹ᵁ V ≤ O := hVT.trans hTO
  have hrange : Set.range (Z.homOfLE hV ≫ h) ⊆ Set.range O'.ι := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    obtain ⟨u, hu, hux⟩ := hVT x.2
    have : Z.homOfLE hV x = u := by
      apply Subtype.ext
      refine (Scheme.homOfLE_apply hV x).trans ?_
      exact hux.symm.trans (Scheme.Opens.ι_apply O u)
    show h (Z.homOfLE hV x) ∈ O'
    rw [this]
    exact hu
  have hg := IsOpenImmersion.lift_fac O'.ι _ hrange
  haveI hiso : IsIso (p.app (V.ι ''ᵁ ⊤)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr
      (GlobalTheory.T.app_bijective_of_flat_baseChange_globalFunctions R S Y Z π y p q inferInstance inferInstance hbij hflat hpb _)
  haveI : IsIso (p ∣_ V).appTop := by
    rw [morphismRestrict_appTop]
    refine @IsIso.comp_isIso _ _ _ _ _ _ _ hiso ?_
    first
      | exact Functor.map_isIso _ _
      | exact (Z.presheaf.mapIso (eqToIso _).op).isIso_hom
      | (apply Functor.map_isIso)
  obtain ⟨g₀, hg₀⟩ := factor_of_isIso_appTop (p ∣_ V) (IsOpenImmersion.lift O'.ι _ hrange)
  refine ⟨V, hV, g₀ ≫ O'.ι, hy₀, ?_⟩
  rw [← Category.assoc, hg₀, hg]

end GlobalTheory.MorDesc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MorphismEqOfEqOnThickeningsStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.morphism_eq_of_eq_on_thickenings : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), I ≤ Ideal.jacobson ⊥ → ∀ (X Z : Over (Spec (CommRingCat.of R))), IsProper X.hom → IsSeparated Z.hom → ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (b : ∀ e, (Y e).left ⟶ X.left), (∀ e, IsPullback (b e) (Y e).hom X.hom (thick R I e)) → ∀ g g' : X ⟶ Z, (∀ e, b e ≫ g.left = b e ≫ g'.left) → g = g' := by
  first | exact @GlobalTheory.FormalAlg.hom_eq_of_reductions_eq | exact GlobalTheory.FormalAlg.hom_eq_of_reductions_eq | (intros; apply GlobalTheory.FormalAlg.hom_eq_of_reductions_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundlePullbackTrivialOfImFormIntStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mumfordBundle_pullback_trivial_of_im_form_int : ∀ (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A] (g : ℕ), IsAbelianScheme A → ∀ (M : LB A.left) (u : HolUnif A M g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ), M.IsLB → GlobalTheory.TorusRM.IsFactorAH u Hm χ → ∀ w : Fin g → ℂ, (∀ l ∈ u.Λ, ∃ n : ℤ, (w ⬝ᵥ Hm.mulVec (star l)).im = n) → ∃ t : ((abelian₂ A M).pull (lift (fst A (𝟙_ (Over (Sp ℂ)))) (snd A (𝟙_ (Over (Sp ℂ))) ≫ u.ex w)).left).Gen, t.IsGen := by
  first | exact @GlobalTheory.TorusRM.hasGen_lam_pull_of_im_int | exact GlobalTheory.TorusRM.hasGen_lam_pull_of_im_int | (intros; apply GlobalTheory.TorusRM.hasGen_lam_pull_of_im_int <;> assumption)
end

