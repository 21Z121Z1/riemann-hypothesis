import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0046
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0075
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2724
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2291
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2712
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2681
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueFactorCompletedStalkOfMap
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsSecNonzeroLocusEqOfLbIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0141
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsNsmulIffEq
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0088
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2392
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2713
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLogCanonicalMultipleOfGloballyKlt
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep GlobalTheory.FieldPair

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.KltGlobal

variable {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} {n : ℕ}
  {Δ : X → ℚ} {η : RatForms p n} {x y : X} {m : ℕ} {g h : X.functionFieldˣ}

theorem compactSpace_of_isProjOver' {R : Type} [CommRing R] {Y : Scheme.{0}} {f : Y ⟶ Sp R}
    (hf : IsProjOver f) : CompactSpace Y := by
  obtain ⟨N, i, hi, rfl⟩ := hf
  have := isProper_str R N
  have : IsProper (i ≫ PSpace.str R N) := inferInstance
  exact QuasiCompact.compactSpace_of_compactSpace (i ≫ PSpace.str R N)

theorem unitAt_of_specializes' {z : X} {f : X.functionField} (hz : z ⤳ y) (hf : UnitAt y f) :
    UnitAt z f :=
  (unitAt_iff hf.ne_zero).2 ⟨regAt_of_specializes hz hf.regAt, regAt_of_specializes hz hf.inv.regAt⟩

theorem ord_eq_zero_of_unitAt' {E : DivOver p} {z : X} (hE : E.IsAt z) {u : X.functionFieldˣ}
    (hu : UnitAt z (u : X.functionField)) : E.ord u = 0 := by
  have h1 := (E.ord_nonneg_iff u).2 ((hE _).2 hu.regAt)
  have h2 := (E.ord_nonneg_iff u⁻¹).2 ((hE _).2 (by rw [Units.val_inv_eq_inv_val]; exact hu.inv.regAt))
  rw [E.ord_inv] at h2
  omega

theorem isLogEqn_pow' (hg : IsLogEqn p Δ η x m g) (r : ℕ) : IsLogEqn p Δ η x (m * r) (g ^ r) := by
  intro z hz E hE
  rw [E.ord_pow]
  push_cast
  rw [← hg z hz E hE]
  ring

theorem isLogEqn_of_unitAt' (hg : IsLogEqn p Δ η y m g)
    (hu : UnitAt y ((h : X.functionField) / g)) : IsLogEqn p Δ η y m h := by
  intro z hz E hE
  have h0 : E.ord (h * g⁻¹) = 0 := ord_eq_zero_of_unitAt' hE (by
    rw [Units.val_mul, Units.val_inv_eq_inv_val, ← div_eq_mul_inv]
    exact unitAt_of_specializes' hz hu)
  have e : E.ord h = E.ord g := by
    have := E.ord_mul (h * g⁻¹) g
    rwa [inv_mul_cancel_right, h0, zero_add] at this
  rw [hg z hz E hE, e]

theorem unitAt_of_isLogEqn' [LocallyOfFiniteType p] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X]
    (hg : IsLogEqn p Δ η y m g) (hh : IsLogEqn p Δ η y m h) :
    UnitAt y ((h : X.functionField) / g) := by
  have h0 : ∀ z, z ⤳ y → ∀ F : DivOver p, F.IsAt z → F.ord (h * g⁻¹) = 0 := by
    intro z hz F hF
    have a := hg z hz F hF
    have b := hh z hz F hF
    rw [F.ord_mul, F.ord_inv]
    have : (F.ord g : ℚ) = F.ord h := a.symm.trans b
    have : F.ord g = F.ord h := by exact_mod_cast this
    omega
  have reg : ∀ v : X.functionFieldˣ, (∀ z, z ⤳ y → ∀ F : DivOver p, F.IsAt z → F.ord v = 0) →
      RegAt y (v : X.functionField) := fun v hv =>
    regAt_of_forall_coheight_eq_one fun z hz h1 =>
      have ⟨F, hF⟩ := DivOver.exists_isAt_of_coheight_eq_one (p := p) h1
      (hF _).1 ((F.ord_nonneg_iff v).1 (hv z hz F hF).ge)
  have hne : (h : X.functionField) / g ≠ 0 := div_ne_zero h.ne_zero g.ne_zero
  have e1 : ((h * g⁻¹ : X.functionFieldˣ) : X.functionField) = h / g := by
    rw [Units.val_mul, Units.val_inv_eq_inv_val, div_eq_mul_inv]
  have e2 : (((h * g⁻¹)⁻¹ : X.functionFieldˣ) : X.functionField) = ((h : X.functionField) / g)⁻¹ := by
    rw [Units.val_inv_eq_inv_val, e1]
  refine (unitAt_iff hne).2 ⟨e1 ▸ reg _ h0, e2 ▸ reg _ fun z hz F hF => ?_⟩
  rw [F.ord_inv, h0 z hz F hF, neg_zero]

theorem exists_isLogEqn_of_form' [PerfectField k] [LocallyOfFiniteType p]
    (hn : topologicalKrullDim X = n) {η₀ : RatForms p n} (hη₀ : η₀ ≠ 0) (hη : η ≠ 0)
    (hg : IsLogEqn p Δ η x m g) : ∃ g' : X.functionFieldˣ, IsLogEqn p Δ η₀ x m g' := by
  by_cases hE : Nonempty (DivOver p)
  · obtain ⟨E⟩ := hE
    obtain ⟨ω, hω, f₀, e₀, -⟩ := E.isFormOrd_formOrd hn hη₀
    obtain ⟨f, e⟩ := (E.isFreeGen_toRat hω).2 η
    have hf : f ≠ 0 := fun h0 => hη (by rw [← e, h0]; exact zero_smul _ _)
    obtain ⟨c, hc⟩ : ∃ c : X.functionFieldˣ, η = (c : X.functionField) • η₀ :=
      ⟨Units.mk0 f hf * f₀⁻¹, by rw [e₀, smul_smul, ← e]; simp⟩
    refine ⟨g * (c ^ m)⁻¹, fun z hz F hF => ?_⟩
    have a := hg z hz F hF
    rw [hc, F.formOrd_smul hn hη₀] at a
    rw [F.ord_mul, F.ord_inv, F.ord_pow]
    push_cast at a ⊢
    linear_combination a
  · exact ⟨1, fun z _ F _ => (hE ⟨F⟩).elim⟩

theorem exists_nhds_isLogEqn' [IsLocallyNoetherian X] [CompactSpace X]
    (hfin : {z : X | ∃ E : DivOver p, E.IsAt z ∧ E.formOrd η ≠ 0}.Finite)
    (hΔ : (Function.support Δ).Finite) (hg : IsLogEqn p Δ η x m g) :
    ∃ U : X.Opens, x ∈ U ∧ ∀ y ∈ U, IsLogEqn p Δ η y m g := by
  set B : Set X := {z | ∃ E : DivOver p, E.IsAt z ∧ (m : ℚ) * (E.formOrd η + Δ z) ≠ E.ord g}
    with hB
  have hBf : B.Finite := by
    refine ((hfin.union hΔ).union (CartierDiv.principal g).finite_support_mult).subset ?_
    rintro z ⟨E, hE, hne⟩
    by_cases h1 : E.formOrd η = 0
    · by_cases h2 : Δ z = 0
      · right
        show (CartierDiv.principal g).mult z ≠ 0
        rw [(CartierDiv.isEqn_principal g z).mult_eq, ← hE.ord_eq]
        intro h3
        apply hne
        rw [h1, h2, h3]
        simp
      · exact Or.inl (Or.inr h2)
    · exact Or.inl (Or.inl ⟨E, hE, h1⟩)
  have key : ∀ y, y ∈ closure B → ∃ z ∈ B, z ⤳ y := by
    intro y hy
    have hc : closure B = ⋃ z ∈ B, closure {z} := by
      conv_lhs => rw [← Set.biUnion_of_singleton B]
      exact hBf.closure_biUnion _
    rw [hc] at hy
    simp only [Set.mem_iUnion] at hy
    obtain ⟨z, hz, hy⟩ := hy
    exact ⟨z, hz, specializes_iff_mem_closure.2 hy⟩
  refine ⟨⟨(closure B)ᶜ, isClosed_closure.isOpen_compl⟩, show x ∉ closure B from fun hx => ?_,
    fun y hy z hz E hE => ?_⟩
  · obtain ⟨z, ⟨E, hE, hne⟩, hzx⟩ := key x hx
    exact hne (hg z hzx E hE)
  · have hy' : y ∉ closure B := hy
    by_contra hne
    exact hy' (closure_mono (Set.singleton_subset_iff.2 (show z ∈ B from ⟨E, hE, hne⟩))
      (specializes_iff_mem_closure.1 hz))

end GlobalTheory.KltGlobal

namespace GlobalTheory.Discrepancy

open GlobalTheory.KltGlobal

theorem exists_isLogCanonicalMultiple_of_kltAt :
    ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X]
      (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p →
      topologicalKrullDim X = n → ∀ Δ : X → ℚ, IsEffQDiv Δ → (∀ y, KltAt p n Δ y) →
      ∃ (m : ℕ) (G : CartierDiv X), 0 < m ∧ IsLogCanonicalMultiple p n Δ m G := by
  intro X _ _ _ p n hP hn Δ hΔ hklt
  classical
  haveI : CompactSpace X := compactSpace_of_isProjOver' hP
  haveI : LocallyOfFiniteType p := isProjOver_locallyOfFiniteType ℂ X p hP
  obtain ⟨η₀, -, -, hη₀, -, -, -⟩ := hklt (genericPoint X)
  have hfin := GlobalTheory.FormOrdFinite.finite_setOf_formOrd_ne_zero ℂ X p n hP hn η₀ hη₀
  have h1 : ∀ x, ∃ (m : ℕ) (g : X.functionFieldˣ) (U : X.Opens), 0 < m ∧ x ∈ U ∧
      ∀ y ∈ U, IsLogEqn p Δ η₀ y m g := by
    intro x
    obtain ⟨η, m, g, hη, hm, hg, -⟩ := hklt x
    obtain ⟨g', hg'⟩ := exists_isLogEqn_of_form' hn hη₀ hη hg
    obtain ⟨U, hU, hy⟩ := exists_nhds_isLogEqn' hfin hΔ.finite hg'
    exact ⟨m, g', U, hm, hU, hy⟩
  choose mm gg UU hm hU hy using h1
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x => (UU x : Set X))
    (fun x => (UU x).isOpen) (fun x _ => Set.mem_iUnion.2 ⟨x, hU x⟩)
  set M := ∏ i ∈ t, mm i with hM
  have hM0 : 0 < M := Finset.prod_pos fun i _ => hm i
  have hMd : ∀ i ∈ t, mm i * (M / mm i) = M := fun i hi =>
    Nat.mul_div_cancel' (Finset.dvd_prod_of_mem _ hi)
  have sel : ∀ y : X, ∃ i ∈ t, y ∈ UU i := fun y => by
    have := ht (Set.mem_univ y)
    simpa using this
  choose s hs hsy using sel
  let e : X → X.functionFieldˣ := fun y => gg (s y) ^ (M / mm (s y))
  have he : ∀ y, ∀ w ∈ UU (s y), IsLogEqn p Δ η₀ w M (e y) := fun y w hw => by
    have := isLogEqn_pow' (hy (s y) w hw) (M / mm (s y))
    rwa [hMd _ (hs y)] at this
  let G : CartierDiv X := show cartierGroup X from
    ⟨fun y => germOf y (e y), fun x => ⟨UU (s x), hsy x, e x, fun y hy' =>
      germOf_eq_iff.2 (unitAt_of_isLogEqn' (he y y (hsy y)) (he x y hy'))⟩⟩
  refine ⟨M, G, hM0, η₀, hη₀, fun x g hg => ?_⟩
  have h0 : G.IsEqn x (e x) := rfl
  exact isLogEqn_of_unitAt' (he x x (hsy x)) (h0.iff_unitAt.1 hg)

end GlobalTheory.Discrepancy

example : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p →
  topologicalKrullDim X = n → ∀ Δ : X → ℚ, IsEffQDiv Δ → (∀ y, KltAt p n Δ y) →
  ∃ (m : ℕ) (G : CartierDiv X), 0 < m ∧ IsLogCanonicalMultiple p n Δ m G :=
  GlobalTheory.Discrepancy.exists_isLogCanonicalMultiple_of_kltAt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsModificationClosureOfGraphStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_modification_closure_of_graph : ∀ (R : Type) [CommRing R] [IsDomain R] (o : Type) [CommRing o] (b : o →+* R) (Z : Scheme.{0}) (s : Z ⟶ Sp o), IsProper s → ∀ y : Sp (FractionRing R) ⟶ Z, y ≫ s = jK R ≫ spMap b → ∃ (M : Modif R) (h : M.S ⟶ Z), M.gp ≫ h = y ∧ h ≫ s = M.π ≫ spMap b := by
  first | exact @GlobalTheory.Mum.exists_modif_graph | exact GlobalTheory.Mum.exists_modif_graph | (intros; apply GlobalTheory.Mum.exists_modif_graph <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMorphismOfSectionRatiosVeryAmple
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

open GlobalTheory.LBGerm

theorem ratMap_gs_appLE {Z S : Scheme.{0}} (r : Z ⟶ S) (U : S.Opens) (h : ⊤ ≤ r ⁻¹ᵁ U) (w : Z) (a : Γ(S, U)) :
    gs r w U a = gs (𝟙 Z) w ⊤ ((r.appLE U ⊤ h).hom a) := by
  rw [Scheme.Hom.appLE, CommRingCat.comp_apply, gs_res (𝟙 Z) w h trivial, gs_pull (𝟙 Z) r w U (h trivial) a,
    Category.id_comp]

theorem ratMap_eq_of_gs_eq {T S : Scheme.{0}} (g₁ g₂ : T ⟶ S) {U : S.Opens} (hU : IsAffineOpen U)
    (h₁ : ∀ w, g₁ w ∈ U) (h₂ : ∀ w, g₂ w ∈ U) (h : ∀ (a : Γ(S, U)) (w : T), gs g₁ w U a = gs g₂ w U a) :
    g₁ = g₂ := by
  have hf : ⊤ ≤ g₁ ⁻¹ᵁ U := fun w _ => h₁ w
  have hg : ⊤ ≤ g₂ ⁻¹ᵁ U := fun w _ => h₂ w
  have key : ∀ (r : T ⟶ S) (hr : ⊤ ≤ r ⁻¹ᵁ U),
      (⊤ : T.Opens).ι ≫ r = (⊤ : T.Opens).toSpecΓ ≫ Spec.map (r.appLE U ⊤ hr) ≫ hU.fromSpec := by
    intro r hr
    rw [Scheme.Opens.toSpecΓ_SpecMap_appLE_assoc, hU.toSpecΓ_fromSpec, Scheme.Hom.resLE_comp_ι]
  have e : g₁.appLE U ⊤ hf = g₂.appLE U ⊤ hg := by
    ext a
    exact fn_ext fun w _ => (ratMap_gs_appLE g₁ U hf w a).symm.trans ((h a w).trans (ratMap_gs_appLE g₂ U hg w a))
  exact Scheme.hom_ext_of_forall g₁ g₂ fun w => ⟨⊤, trivial, by rw [key g₁ hf, key g₂ hg, e]⟩

theorem ratMap_gs_ofRingHom {X Y : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) (V : Y.Opens)
    (θ : Γ(X, U) →+* Γ(Y, V)) {Z : Scheme.{0}} (u : Z ⟶ V.toScheme) (w : Z) :
    (u ≫ V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom θ) ≫ hU.fromSpec) w ∈ U ∧ ∀ b : Γ(X, U),
      gs (u ≫ V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom θ) ≫ hU.fromSpec) w U b = gs (u ≫ V.ι) w V (θ b) := by
  have h0 : ⊤ ≤ hU.fromSpec ⁻¹ᵁ U := hU.fromSpec_preimage_self.ge
  have h' : ⊤ ≤ (u ≫ V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom θ) ≫ hU.fromSpec) ⁻¹ᵁ U :=
    fun z _ => h0 (Set.mem_univ ((u ≫ V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom θ)) z))
  have h : ⊤ ≤ (u ≫ V.ι) ⁻¹ᵁ V := fun z _ => (u z).2
  refine ⟨h' trivial, fun b => ?_⟩
  have h1 : hU.fromSpec.appLE U ⊤ h0 = (Scheme.ΓSpecIso _).inv := by
    rw [Scheme.Hom.appLE, IsAffineOpen.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
    exact Category.comp_id _
  have h2 : (u ≫ V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom θ) ≫ hU.fromSpec).appLE U ⊤ h' =
      hU.fromSpec.appLE U ⊤ h0 ≫ (u ≫ V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom θ)).appTop :=
by
    have e := Scheme.Hom.appLE_comp_appLE (u ≫ V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom θ)) hU.fromSpec U ⊤ ⊤ h0 le_rfl
    rw [show (u ≫ V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom θ)).appLE ⊤ ⊤ le_rfl =
      (u ≫ V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom θ)).appTop from Scheme.Hom.appLE_eq_app (f := u ≫ V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom θ)) (U := ⊤)] at e
    simpa only [Category.assoc] using e.symm
  have h3 : (u ≫ V.ι).appLE V ⊤ h = V.topIso.inv ≫ u.appTop := by
    rw [← Scheme.Hom.appLE_comp_appLE u V.ι V ⊤ ⊤ (fun x _ => x.2) le_rfl]
    erw [Scheme.Opens.ι_appLE]
    simp only [Scheme.Opens.topIso_inv]
    congr 1
    exact Scheme.Hom.appLE_eq_app (f := u) (U := ⊤)
  have h4 : (u ≫ V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom θ) ≫ hU.fromSpec).appLE U ⊤ h' =
      CommRingCat.ofHom θ ≫ (u ≫ V.ι).appLE V ⊤ h := by
    rw [h2, h1, h3, Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop, Scheme.Opens.toSpecΓ_appTop]
    simp only [Category.assoc]
    rw [Scheme.ΓSpecIso_naturality_assoc]
    exact Iso.inv_hom_id_assoc _ _
  rw [ratMap_gs_appLE _ U h' w b, ratMap_gs_appLE _ V h w (θ b), h4]
  rfl

theorem ratMap_gs_eval₂ {K : Type} [CommRing K] {Z S S' : Scheme.{0}} {Idx : Type} (g₁ : Z ⟶ S) (g₂ : Z ⟶ S')
    {U₁ : S.Opens} {U₂ : S'.Opens} (w : Z) (hw₁ : g₁ w ∈ U₁) (hw₂ : g₂ w ∈ U₂) (f₁ : K →+* Γ(S, U₁))
    (f₂ : K →+* Γ(S', U₂)) (r₁ : Idx → Γ(S, U₁)) (r₂ : Idx → Γ(S', U₂))
    (hc : ∀ a, gs g₁ w U₁ (f₁ a) = gs g₂ w U₂ (f₂ a)) (hr : ∀ l, gs g₁ w U₁ (r₁ l) = gs g₂ w U₂ (r₂ l))
    (P : MvPolynomial Idx K) :
    gs g₁ w U₁ (MvPolynomial.eval₂Hom f₁ r₁ P) = gs g₂ w U₂ (MvPolynomial.eval₂Hom f₂ r₂ P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simp only [MvPolynomial.eval₂Hom_C]; exact hc a
  | add p q hp hq => rw [map_add, map_add, gs_add _ _ _ hw₁, gs_add _ _ _ hw₂, hp, hq]
  | mul_X p n hp => rw [map_mul, map_mul, gs_mul _ _ _ hw₁, gs_mul _ _ _ hw₂, hp, MvPolynomial.eval₂Hom_X',
      MvPolynomial.eval₂Hom_X', hr n]

theorem ratMap_gs_cst {K : Type} [CommRing K] {Z S : Scheme.{0}} (p : S ⟶ Spec (CommRingCat.of K)) (g : Z ⟶ S)
    (U : S.Opens) (w : Z) (hw : g w ∈ U) (a : K) :
    gs g w U (AbLaw.cst p U a) = gs (g ≫ p) w ⊤ ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom a) := by
  rw [AbLaw.cst, RingHom.comp_apply, RingHom.comp_apply, AbLaw.rs, gs_res g w le_top hw]
  exact gs_pull g p w ⊤ trivial _

theorem ratMap_key {A X Z : Scheme.{0}} {L : LB X} (hL : L.IsLB) (π : A ⟶ X) {k k' m : ℕ}
    (σ : Fin (m + 1) → H0 L k) (hcov : ⨆ i, π ⁻¹ᵁ nonzeroLocus (σ i) = ⊤) (s₀ : H0 L k) (t₀ : H0 L k')
    (t : Fin (m + 1) → H0 L k') (i₀ : Fin (m + 1)) (r : Fin (m + 1) → Γ(A, π ⁻¹ᵁ nonzeroLocus (σ i₀)))
    (hr : ∀ (j : Fin (m + 1)) (c : Fin 1 → L.ι) (a : A), π a ∈ nonzeroLocus (σ i₀) → π a ∈ secChart L c →
      secGerm π a (σ j) c = gs (𝟙 A) a (π ⁻¹ᵁ nonzeroLocus (σ i₀)) (r j) * secGerm π a (σ i₀) c)
    (c : Fin 1 → L.ι) (g z : Z ⟶ A) (w : Z) (hc : (g ≫ π) w ∈ secChart L c)
    (ht₀ : IsUnit (secGerm (g ≫ π) w t₀ c)) (hti : IsUnit (secGerm (g ≫ π) w (t i₀) c))
    (hrat : ∀ i, SecRatioEq L (z ≫ π) (g ≫ π) (σ i) s₀ (t i) t₀) :
    z w ∈ π ⁻¹ᵁ nonzeroLocus (σ i₀) ∧ ∀ (l : Fin (m + 1)) (ρ : Z.presheaf.stalk w),
      ρ * secGerm (g ≫ π) w (t i₀) c = secGerm (g ≫ π) w (t l) c →
        gs z w (π ⁻¹ᵁ nonzeroLocus (σ i₀)) (r l) = ρ := by
  obtain ⟨l₀, hl₀⟩ := TopologicalSpace.Opens.mem_iSup.1
    (show z w ∈ ⨆ i, π ⁻¹ᵁ nonzeroLocus (σ i) by rw [hcov]; trivial)
  obtain ⟨j, hj⟩ := exists_chart hL (π (z w))
  let c' : Fin 1 → L.ι := fun _ => j
  have hc' : (z ≫ π) w ∈ secChart L c' := Set.mem_iInter.2 fun _ => hj
  have germ := fun i => secRatioEq_iff_germ.1 (hrat i) w c' c hc' hc
  have uσ : IsUnit (secGerm (z ≫ π) w (σ l₀) c') := (GlobalTheory.mem_nonzeroLocus_iff_pull (σ l₀) (z ≫ π) w hc').1 hl₀
  have us₀ : IsUnit (secGerm (z ≫ π) w s₀ c') := by
    have h := uσ.mul ht₀
    rw [germ l₀] at h
    exact isUnit_of_mul_isUnit_left h
  have uσi : IsUnit (secGerm (z ≫ π) w (σ i₀) c') := by
    have h := us₀.mul hti
    rw [← germ i₀] at h
    exact isUnit_of_mul_isUnit_left h
  have hD : z w ∈ π ⁻¹ᵁ nonzeroLocus (σ i₀) := (GlobalTheory.mem_nonzeroLocus_iff_pull (σ i₀) (z ≫ π) w hc').2 uσi
  refine ⟨hD, fun l ρ hρ => ?_⟩
  have hrl := congrArg (z.stalkMap w).hom (hr l c' (z w) hD hc')
  rw [map_mul, ← secGerm_comp z π w _ hc', ← secGerm_comp z π w _ hc', ← gs_stalkMap z w _ hD] at hrl
  refine (us₀.mul hti).mul_right_cancel ?_
  linear_combination (-(gs z w (π ⁻¹ᵁ nonzeroLocus (σ i₀)) (r l))) * germ i₀ + (-(secGerm (g ≫ π) w t₀ c)) * hrl +
    germ l + (-(secGerm (z ≫ π) w s₀ c')) * hρ

theorem exists_morphism_of_secRatio : ∀ (K : Type) [Field K] (A : Over (Sp K)) [IsIntegral A.left] (X : Scheme.{0}) (L : LB X), L.IsLB → ∀ (π : A.left ⟶ X) (k k' m : ℕ) (σ : Fin (m + 1) → H0 L k), VeryAmpleAlong A.hom π L σ → ∀ (s₀ : H0 L k) (t₀ : H0 L k') (t : Fin (m + 1) → H0 L k'), (∃ a : A.left, π a ∈ nonzeroLocus t₀) → ∀ (Y : Over (Sp K)) (x y : Y ⟶ A), IsDominant x.left → (∀ i, SecRatioEq L (y.left ≫ π) (x.left ≫ π) (σ i) s₀ (t i) t₀) → ∃ (V : Over (Sp K)) (j f : V ⟶ A), IsOpenImmersion j.left ∧ Nonempty V.left ∧ ∀ (Z : Over (Sp K)) (u : Z ⟶ V) (z : Z ⟶ A), (∀ i, SecRatioEq L (z.left ≫ π) ((u ≫ j).left ≫ π) (σ i) s₀ (t i) t₀) → u ≫ f = z := by
  intro K _ A _ X L hL π k k' m σ hva s₀ t₀ t ⟨a, ha⟩ Y x y hdom hrat
  haveI := hdom
  obtain ⟨hcov, hloc⟩ := hva
  obtain ⟨q, hq⟩ := x.left.denseRange.exists_mem_open (π ⁻¹ᵁ nonzeroLocus t₀).isOpen ⟨a, ha⟩
  obtain ⟨i₀, hi₀⟩ := TopologicalSpace.Opens.mem_iSup.1
    (show y.left q ∈ ⨆ i, π ⁻¹ᵁ nonzeroLocus (σ i) by rw [hcov]; trivial)
  obtain ⟨hD, r, hr, hsurj⟩ := hloc i₀
  obtain ⟨jx, hjx⟩ := exists_chart hL (π (x.left q))
  obtain ⟨jy, hjy⟩ := exists_chart hL (π (y.left q))
  let c : Fin 1 → L.ι := fun _ => jx
  let c' : Fin 1 → L.ι := fun _ => jy
  have hcx : (x.left ≫ π) q ∈ secChart L c := Set.mem_iInter.2 fun _ => hjx
  have hcy : (y.left ≫ π) q ∈ secChart L c' := Set.mem_iInter.2 fun _ => hjy
  have e := secRatioEq_iff_germ.1 (hrat i₀) q c' c hcy hcx
  have u1 : IsUnit (secGerm (y.left ≫ π) q (σ i₀) c') := (GlobalTheory.mem_nonzeroLocus_iff_pull (σ i₀) (y.left ≫ π) q hcy).1 hi₀
  have u2 : IsUnit (secGerm (x.left ≫ π) q t₀ c) := (GlobalTheory.mem_nonzeroLocus_iff_pull t₀ (x.left ≫ π) q hcx).1 hq
  have u3 : IsUnit (secGerm (x.left ≫ π) q (t i₀) c) := by
    have h := u1.mul u2
    rw [e] at h
    exact isUnit_of_mul_isUnit_right h
  let W₀ : A.left.Opens := π ⁻¹ᵁ secChart L c
  let b : H0 L k' → Γ(A.left, W₀) := fun s => (π.app (secChart L c)).hom (s.f c)
  let V : A.left.Opens := A.left.basicOpen (b t₀ * b (t i₀))
  have hVW : V ≤ W₀ := A.left.basicOpen_le _
  have hb : ∀ {Z : Scheme.{0}} (g : Z ⟶ A.left) (w : Z) (_ : g w ∈ W₀) (s : H0 L k'),
      gs g w W₀ (b s) = secGerm (g ≫ π) w s c := fun g w hw s => gs_pull g π w _ hw _
  have memV : ∀ {Z : Scheme.{0}} (g : Z ⟶ A.left) (w : Z), g w ∈ V → (g ≫ π) w ∈ secChart L c ∧
      IsUnit (secGerm (g ≫ π) w t₀ c) ∧ IsUnit (secGerm (g ≫ π) w (t i₀) c) := by
    intro Z g w hw
    have hW : g w ∈ W₀ := hVW hw
    have h := (GlobalTheory.LBGerm.isUnit_gs_iff g w W₀ hW _).2 hw
    rw [gs_mul g w W₀ hW, hb g w hW, hb g w hW] at h
    exact ⟨hW, isUnit_of_mul_isUnit_left h, isUnit_of_mul_isUnit_right h⟩
  have hxq : x.left q ∈ V :=
    (GlobalTheory.LBGerm.isUnit_gs_iff x.left q W₀ hcx (b t₀ * b (t i₀))).1
      (by rw [gs_mul _ q W₀ hcx, hb _ q hcx, hb _ q hcx]; exact u2.mul u3)
  have hu : IsUnit ((A.left.presheaf.map (homOfLE hVW).op).hom (b (t i₀))) := by
    have h := A.left.toRingedSpace.isUnit_res_basicOpen (b t₀ * b (t i₀))
    rw [map_mul] at h
    exact isUnit_of_mul_isUnit_right h
  let ρ : Fin (m + 1) → Γ(A.left, V) := fun l =>
    (A.left.presheaf.map (homOfLE hVW).op).hom (b (t l)) * ↑hu.unit⁻¹
  have hρ : ∀ {Z : Scheme.{0}} (g : Z ⟶ A.left) (w : Z) (_ : g w ∈ V) (l : Fin (m + 1)),
      gs g w V (ρ l) * secGerm (g ≫ π) w (t i₀) c = secGerm (g ≫ π) w (t l) c := by
    intro Z g w hw l
    have hW : g w ∈ W₀ := hVW hw
    have one : gs g w V 1 = 1 := by rw [gs_eq g w V hw, map_one, map_one]
    rw [← hb g w hW, ← hb g w hW, ← gs_res g w hVW hw (b (t i₀)), ← gs_res g w hVW hw (b (t l)),
      gs_mul g w V hw, _root_.mul_assoc, ← gs_mul g w V hw, hu.val_inv_mul, one, _root_.mul_one]
  let ev := MvPolynomial.eval₂Hom (AbLaw.cst A.hom (π ⁻¹ᵁ nonzeroLocus (σ i₀))) r
  let ev' := MvPolynomial.eval₂Hom (AbLaw.cst A.hom V) ρ
  have transfer : ∀ {Z : Scheme.{0}} (g z : Z ⟶ A.left) (w : Z), g w ∈ V → g ≫ A.hom = z ≫ A.hom →
      (∀ i, SecRatioEq L (z ≫ π) (g ≫ π) (σ i) s₀ (t i) t₀) →
      z w ∈ π ⁻¹ᵁ nonzeroLocus (σ i₀) ∧ ∀ P, gs g w V (ev' P) = gs z w _ (ev P) := by
    intro Z g z w hw hp hrt
    obtain ⟨hc, h0, hi⟩ := memV g w hw
    obtain ⟨hzD, hR⟩ := ratMap_key hL π σ hcov s₀ t₀ t i₀ r hr c g z w hc h0 hi hrt
    refine ⟨hzD, ratMap_gs_eval₂ g z w hw hzD _ _ ρ r (fun a => ?_) (fun l => (hR l _ (hρ g w hw l)).symm)⟩
    rw [ratMap_gs_cst A.hom g V w hw, ratMap_gs_cst A.hom z _ w hzD, hp]
  have hker : RingHom.ker ev ≤ RingHom.ker ev' := by
    intro P hP
    rw [RingHom.mem_ker] at hP ⊢
    apply app_injective_of_isDominant x.left V
    rw [map_zero]
    refine fn_ext fun w hw => ?_
    have tr := transfer x.left y.left w hw ((Over.w x).trans (Over.w y).symm) hrat
    rw [gs_pull (𝟙 _) x.left w V hw, Category.id_comp, tr.2 P, hP, GlobalTheory.LBGerm.gs_zero _ _ _ tr.1,
      GlobalTheory.LBGerm.gs_zero _ _ _ hw]
  let θ := (RingHom.liftOfSurjective ev hsurj) ⟨ev', hker⟩
  have hθ : ∀ P, θ (ev P) = ev' P := RingHom.liftOfSurjective_comp_apply ev hsurj ⟨ev', hker⟩
  let f₀ : V.toScheme ⟶ A.left := V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom θ) ≫ hD.fromSpec
  have hf₀ : ∀ {Z : Scheme.{0}} (u : Z ⟶ V.toScheme) (w : Z), (u ≫ f₀) w ∈ π ⁻¹ᵁ nonzeroLocus (σ i₀) ∧
      ∀ P, gs (u ≫ f₀) w _ (ev P) = gs (u ≫ V.ι) w V (ev' P) := fun u w => by
    obtain ⟨h1, h2⟩ := ratMap_gs_ofRingHom hD V θ u w
    exact ⟨h1, fun P => (h2 (ev P)).trans (by rw [hθ])⟩
  have hmem : ∀ {Z : Scheme.{0}} (u : Z ⟶ V.toScheme) (w : Z), (u ≫ V.ι) w ∈ V := fun u w => (u w).2
  have hover : f₀ ≫ A.hom = V.ι ≫ A.hom := by
    refine ratMap_eq_of_gs_eq _ _ (isAffineOpen_top (Sp K)) (fun _ => trivial) (fun _ => trivial) fun a w => ?_
    obtain ⟨a', rfl⟩ : ∃ a' : K, (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom a' = a :=
      ⟨(Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom a, by simp⟩
    have h := hf₀ (𝟙 V.toScheme) w
    have hc := h.2 (MvPolynomial.C a')
    rw [MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_C, ratMap_gs_cst _ _ _ w h.1,
      ratMap_gs_cst _ _ _ w (hmem (𝟙 _) w)] at hc
    simpa only [Category.id_comp] using hc
  refine ⟨Over.mk (V.ι ≫ A.hom), Over.homMk V.ι rfl, Over.homMk f₀ hover, ?_, ⟨⟨x.left q, hxq⟩⟩, ?_⟩
  · exact (inferInstance : IsOpenImmersion V.ι)
  · intro Z u z hz
    apply Over.OverMorphism.ext
    change u.left ≫ f₀ = z.left
    have hz' : ∀ i, SecRatioEq L (z.left ≫ π) ((u.left ≫ V.ι) ≫ π) (σ i) s₀ (t i) t₀ := hz
    have hp : (u.left ≫ V.ι) ≫ A.hom = z.left ≫ A.hom := by
      rw [Category.assoc]
      exact (Over.w u).trans (Over.w z).symm
    refine ratMap_eq_of_gs_eq _ _ hD (fun w => (hf₀ u.left w).1)
      (fun w => (transfer _ _ w (hmem u.left w) hp hz').1) fun b' w => ?_
    obtain ⟨P, rfl⟩ := hsurj b'
    exact ((hf₀ u.left w).2 P).trans ((transfer _ _ w (hmem u.left w) hp hz').2 P)

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMumfordBundleIsoTwoHomNormalisedAtOrigin
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

namespace GlobalTheory.Mum.Two

theorem exists_lamVal_origin_two : ∀ {S : Scheme.{0}} (B₀ B : Over S) [GrpObj B₀] [IsCommMonObj B₀] [GrpObj B] [IsCommMonObj B] (M₀ : LB B₀.left) (M : LB B.left), M₀.IsLB → M.IsLB → ∀ (a b : B₀ ⟶ B) [IsMonHom a] [IsMonHom b], LBIso (abelian₂ B₀ M₀) ((abelian₂ B M).pull (lift (fst B₀ B₀ ≫ a) (snd B₀ B₀ ≫ b) : G2 B₀ ⟶ G2 B).left) → ∃ w : LB.Iso (abelian₂ B₀ M₀) ((abelian₂ B M).pull (lift (fst B₀ B₀ ≫ a) (snd B₀ B₀ ≫ b) : G2 B₀ ⟶ G2 B).left), w.IsGen ∧ ∀ (T : Over S) (z : T.left) (J : (T.left ⟶ B.left) → M.ι) (J' : (T.left ⟶ B₀.left) → M₀.ι), Good M z J → Good M₀ z J' → GlobalTheory.PolDeg.lamVal w (lift (1 : T ⟶ B₀) (1 : T ⟶ B₀)).left z J J' = 1 := by
  intro S B₀ B _ _ _ _ M₀ M hM₀ hM a b _ _ H
  obtain ⟨w₀, hw₀⟩ := H
  let F : (G2 B₀).left ⟶ (G2 B).left := (lift (fst B₀ B₀ ≫ a) (snd B₀ B₀ ≫ b) : G2 B₀ ⟶ G2 B).left
  let e : (𝟙_ (Over S)).left ⟶ (G2 B₀).left := (lift (1 : 𝟙_ (Over S) ⟶ B₀) 1).left
  let q : (𝟙_ (Over S)).left ⟶ B.left := (1 : 𝟙_ (Over S) ⟶ B).left
  let q' : (𝟙_ (Over S)).left ⟶ B₀.left := (1 : 𝟙_ (Over S) ⟶ B₀).left
  have eF : e ≫ F = (lift (1 : 𝟙_ (Over S) ⟶ B) 1).left := by
    show (lift (1 : 𝟙_ (Over S) ⟶ B₀) 1 ≫ lift (fst B₀ B₀ ≫ a) (snd B₀ B₀ ≫ b)).left = _
    rw [comp_lift, lift_fst_assoc, lift_snd_assoc, MonObj.one_comp, MonObj.one_comp]
  have hq : ∀ I : ULift.{0} (Finset (Fin 2)), (e ≫ F) ≫ (psum B (x2 B) I.down).left = q := fun I => by
    rw [eF]
    exact congrArg (fun z => z.left) (GlobalTheory.PolDeg.NormIso.lift_one_psum B (T := 𝟙_ (Over S)) I.down)
  have hq' : ∀ I : ULift.{0} (Finset (Fin 2)), e ≫ (psum B₀ (x2 B₀) I.down).left = q' := fun I =>
    congrArg (fun z => z.left) (GlobalTheory.PolDeg.NormIso.lift_one_psum B₀ (T := 𝟙_ (Over S)) I.down)
  obtain ⟨w, hw, hv⟩ := GlobalTheory.PolDeg.NormIso.exists_normalised M M₀ hM hM₀ (K := ULift.{0} (Finset (Fin 2)))
    (fun I => (psum B (x2 B) I.down).left) (fun I => (psum B₀ (x2 B₀) I.down).left)
    (fun I => (-1) ^ (2 - I.down.card)) (by decide) F e (toUnit (G2 B₀)).left
    (congrArg (fun z => z.left) (toUnit_unique (lift (1 : 𝟙_ (Over S) ⟶ B₀) 1 ≫ toUnit (G2 B₀)) (𝟙 _))) q q' hq hq'
    w₀ hw₀
  refine ⟨w, hw, fun T z J J' hJ hJ' => ?_⟩
  have hp : (lift (1 : T ⟶ B₀) (1 : T ⟶ B₀)).left = (toUnit T).left ≫ e := by
    show _ = (toUnit T ≫ lift (1 : 𝟙_ (Over S) ⟶ B₀) 1).left
    rw [comp_lift, MonObj.comp_one]
  have key : ∀ (p : T.left ⟶ (G2 B₀).left) (j : (abelian₂ B M).ι) (k : (abelian₂ B₀ M₀).ι),
      (fun I : ULift.{0} (Finset (Fin 2)) => J (p ≫ F ≫ (psum B (x2 B) I.down).left)) = j →
      (fun I : ULift.{0} (Finset (Fin 2)) => J' (p ≫ (psum B₀ (x2 B₀) I.down).left)) = k →
      GlobalTheory.PolDeg.lamVal w p z J J' = gw (L := abelian₂ B M) (L' := abelian₂ B₀ M₀) w p z j k := by
    rintro p _ _ rfl rfl
    rfl
  rw [hp]
  refine (key _ (fun _ => J ((toUnit T).left ≫ q)) (fun _ => J' ((toUnit T).left ≫ q')) (funext fun I => ?_)
    (funext fun I => ?_)).trans (hv T.left (toUnit T).left z _ _ (hJ ((toUnit T).left ≫ q)) (hJ' ((toUnit T).left ≫ q')))
  · rw [← hq I, Category.assoc, Category.assoc]
  · rw [← hq' I, Category.assoc]

end GlobalTheory.Mum.Two
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsParameterSchemeTriplesAbelianSchemeStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_parameterScheme_triples_abelianScheme : ∀ (S : Scheme.{0}) [IsIntegral S] [IsLocallyNoetherian S] (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (V : A.left.Opens), (∀ s : S, ∃ x ∈ V, A.hom x = s) → ∃ (Y : Over S) (x a v : Y ⟶ A) (p : Y.left ⟶ V.toScheme) (e : V.toScheme ⟶ (x.left ⁻¹ᵁ V).toScheme), IsIntegral Y.left ∧ Smooth x.left ∧ Surjective x.left ∧ p ≫ V.ι = v.left ∧ (∀ y, (x * a).left y ∈ V ∧ (x * a⁻¹).left y ∈ V ∧ (v * a).left y ∈ V ∧ (v * a⁻¹).left y ∈ V) ∧ Smooth ((x.left ⁻¹ᵁ V).ι ≫ p) ∧ GeometricallyIntegral ((x.left ⁻¹ᵁ V).ι ≫ p) ∧ e ≫ (x.left ⁻¹ᵁ V).ι ≫ p = 𝟙 _ := by
  first | exact @GlobalTheory.ParamTriple.exists_param | exact GlobalTheory.ParamTriple.exists_param | (intros; apply GlobalTheory.ParamTriple.exists_param <;> assumption)
end

