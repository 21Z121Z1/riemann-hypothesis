import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0011
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsSymplecticOfTranslFixed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2387
import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0034
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0028
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsRefinementOfIsLimit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1017
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExistsNoethModel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0163
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0130
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.SiegelPullbackTransfer.ExistsGenTransfer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3234
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3233
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3235
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0085
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3219
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0057
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0013
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3217
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2141
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0084
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitePointsCycAway
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelPullbackIffEighthPowerPullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaObjectEighthPowerPrincipalSiegel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2907
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3210
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDivPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowEqPowOfModEqSim
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3238
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3220
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvTranspose
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2842
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2859
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2841
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2852
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3236
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3206
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.Data
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit GlobalTheory.SiegelTypings

namespace GlobalTheory.SiegFGData

theorem data : ∀ (g n : ℕ), 3 ≤ n → Odd n → ∀ (R : Type) [CommRing R] (β : cycAway n →+* R) (c : SiegPre g n (zetaAway n) (spMap β)), c.Principal → ∃ (R₀ : Subring R) (β₀ : cycAway n →+* R₀) (A₀ : Over (Sp R₀)) (_ : GrpObj A₀) (P₀ : LB (A₀ ⊗ A₀).left) (lv₀ : Std g n → (𝟙_ (Over (Sp R₀)) ⟶ A₀)), Algebra.FiniteType ℤ R₀ ∧ R₀.subtype.comp β₀ = β ∧ IsSymmetricPair g A₀ P₀ ∧ (∀ a b, lv₀ (a + b) = lv₀ a * lv₀ b) ∧ Out.RelAmple A₀ (diagPull A₀ P₀) ∧ IsPullbackTriple c.A c.P (lvOf c) A₀ P₀ lv₀ (spMap R₀.subtype) := by
  intro g n hn _ R _ β c hc
  have h0 : n ≠ 0 := by omega
  obtain ⟨R₁, β₁, A₁, _, P₁, lv₁, hfg, hβ, hA₁, hd₁, hP₁, htr⟩ := GlobalTheory.T.siegelObject_data_descends_finiteType_subring g n hn R β c
  have htr' := htr
  obtain ⟨φ, φ₂, hφ, sq₁, sq₂, iso, hl⟩ := htr
  have : IsNoetherianRing R₁ := Algebra.FiniteType.isNoetherianRing ℤ R₁
  have hsym : IsSymmetricPair g c.A c.P := isSymmetricPair (ζ := (cycBase h0).ζ) (by omega) (isUnit_natCast h0) c
  have hlev : IsLevel c.A (lvOf c) := isLevel_lvOf (ζ := (cycBase h0).ζ) c
  obtain ⟨hAb, hdim, hPlb, hr1, hr2, hsy⟩ := hsym
  obtain ⟨F₅, H₅⟩ := GlobalTheory.T.rigidSymmetricBundle_descends_to_subring_finset R R₁ c.A c.P A₁ P₁ φ φ₂ hA₁ hPlb hP₁ hφ ⟨sq₁, sq₂⟩ iso hr1 hr2 hsy
  obtain ⟨F₂, H₂⟩ := GlobalTheory.T.relAmple_diagonal_bundle_descends_subring R R₁ c.A c.P A₁ P₁ φ φ₂ hA₁ hPlb hP₁ hφ ⟨sq₁, sq₂⟩ iso hc.1
  classical
  let S : Subalgebra R₁ R := Algebra.adjoin R₁ ((F₅ ∪ F₂ : Finset R) : Set R)
  let R₂ : Subring R := S.toSubring
  have h12 : R₁ ≤ R₂ := fun x hx => S.algebraMap_mem ⟨x, hx⟩
  have hF : ((F₅ ∪ F₂ : Finset R) : Set R) ⊆ R₂ := Algebra.subset_adjoin
  have hfg₂ : Algebra.FiniteType ℤ R₂ := GlobalTheory.SpreadGroup.finiteType_of_fg hfg (Subalgebra.fg_adjoin_finset _)
  obtain ⟨A₂, _, lv₂, π, π₂, hA₂, hd₂, hπ, sqπ, htr₂⟩ :=
    GlobalTheory.T.pullbackPolarizedLevelTriple_of_subring_le R R₁ R₂ h12 g n c.A c.P (lvOf c) A₁ P₁ lv₁ hA₁ hd₁ hPlb hP₁ htr'
  obtain ⟨t1, t2, t3⟩ := H₅ R₂ h12 (fun x hx => hF (by simp [hx])) A₂ π π₂ hπ sqπ
  have am := H₂ R₂ h12 (fun x hx => hF (by simp [hx])) A₂ π π₂ hπ sqπ
  refine ⟨R₂, (Subring.inclusion h12).comp β₁, A₂, inferInstance, P₁.pull π₂, lv₂, hfg₂, ?_,
    ⟨hA₂, hd₂, pull_isLB hP₁ _, t1, t2, t3⟩, ?_, am, htr₂⟩
  · rw [← hβ]
    rfl
  · intro a b
    obtain ⟨ψ, ψ₂, hψ, -, -, -, hl₂⟩ := htr₂
    have : IsSeparated A₂.hom := by have := hA₂.proper; infer_instance
    refine Over.OverMorphism.ext (GlobalTheory.T.eq_of_spMap_subtype_comp_eq_of_isSeparated R R₂ A₂.left A₂.hom _ _ ?_ ?_)
    · exact (Over.w (lv₂ (a + b))).trans (Over.w (lv₂ a * lv₂ b)).symm
    · let f := spMap R₂.subtype
      let u : Over.mk ((𝟙_ (Over (Sp R))).hom ≫ f) ⟶ 𝟙_ (Over (Sp R₂)) := toUnit _
      have hu : u.left = (𝟙_ (Over (Sp R))).hom ≫ f := Over.toUnit_left
      have hid : (𝟙_ (Over (Sp R))).hom = 𝟙 _ := rfl
      have m := hψ.2 (𝟙_ (Over (Sp R))) (lvOf c a) (lvOf c b) (u ≫ lv₂ a) (u ≫ lv₂ b)
        (by rw [Over.comp_left, hu, hid, Category.id_comp]; exact (hl₂ a).symm)
        (by rw [Over.comp_left, hu, hid, Category.id_comp]; exact (hl₂ b).symm)
      rw [← MonObj.comp_mul, Over.comp_left, hu, hid, Category.id_comp, ← hlev.1] at m
      exact (hl₂ (a + b)).symm.trans m.symm

end GlobalTheory.SiegFGData
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarCohomologousEvenFormsAlgebraClosed
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

set_option autoImplicit false

namespace GlobalTheory.ChernCalc

theorem dbarCoh_algebra : ∀ (M : Type) [TopologicalSpace M] (n : ℕ) (A : HolAtlas M n) , DbarCoh A 1 1 ∧ (∀ w : A.Pt → Ev n, A.IsForm (fld A w) → A.dbar (fld A w) = 0 → DbarCoh A w w) ∧ ∀ (c : ℂ) (w w' z z' : A.Pt → Ev n), DbarCoh A w w' → DbarCoh A z z' → DbarCoh A (c • w) (c • w') ∧ DbarCoh A (w + z) (w' + z') ∧ DbarCoh A (w * z) (w' * z') := by
  intro M _ n A
  obtain ⟨h1, hc, hl, -, -⟩ := GlobalTheory.formCalculus M n A
  have h0 : A.IsForm 0 := by simpa using (hc 0 1 1 h1 h1).2.2.1
  have d0 : A.dbar 0 = 0 := by simpa using (hc 0 1 1 h1 h1).2.2.2.2.2.2.2.2
  have e1 : fld A 1 = 1 := rfl
  have d1 : A.dbar 1 = 0 := by
    have h := (hl 1 1 h1 h1).2
    rw [e1, mul_one, mul_one, one_mul] at h
    simpa using h
  have diag : ∀ w : A.Pt → Ev n, A.IsForm (fld A w) → A.dbar (fld A w) = 0 → DbarCoh A w w :=
    fun w hw dw => ⟨hw, hw, dw, dw, 0, h0, by rw [d0, sub_self]⟩
  refine ⟨diag 1 h1 d1, diag, ?_⟩
  rintro c w w' z z' ⟨hw, hw', dw, dw', u, hu, eu⟩ ⟨hz, hz', dz, dz', v, hv, ev⟩
  have es (x : A.Pt → Ev n) : fld A (c • x) = c • fld A x := rfl
  have ea (x y : A.Pt → Ev n) : fld A (x + y) = fld A x + fld A y := rfl
  have em (x y : A.Pt → Ev n) : fld A (x * y) = fld A x * fld A y := rfl
  have ecomm (x y : A.Pt → Ev n) : fld A x * fld A y = fld A y * fld A x := by rw [← em, ← em, mul_comm]
  have hs (α : A.Fld) (h : A.IsForm α) := (hc c α α h h).2.2.1
  have ds (α : A.Fld) (h : A.IsForm α) := (hc c α α h h).2.2.2.2.2.2.2.2
  have ha (α β : A.Fld) (h : A.IsForm α) (h' : A.IsForm β) := (hc c α β h h').1
  have hm (α β : A.Fld) (h : A.IsForm α) (h' : A.IsForm β) := (hc c α β h h').2.1
  have da (α β : A.Fld) (h : A.IsForm α) (h' : A.IsForm β) := (hc c α β h h').2.2.2.2.2.2.1
  refine ⟨⟨hs _ hw, hs _ hw', ?_, ?_, c • u, hs _ hu, ?_⟩,
    ⟨ha _ _ hw hz, ha _ _ hw' hz', ?_, ?_, u + v, ha _ _ hu hv, ?_⟩,
    ⟨hm _ _ hw hz, hm _ _ hw' hz', ?_, ?_, fld A w * v + fld A z' * u, ha _ _ (hm _ _ hw hv) (hm _ _ hz' hu), ?_⟩⟩
  · rw [es, ds _ hw, dw, smul_zero]
  · rw [es, ds _ hw', dw', smul_zero]
  · rw [es, es, ds _ hu, ← eu, smul_sub]
  · rw [ea, da _ _ hw hz, dw, dz, add_zero]
  · rw [ea, da _ _ hw' hz', dw', dz', add_zero]
  · rw [ea, ea, da _ _ hu hv, ← eu, ← ev]
    abel
  · rw [em, (hl w _ hw hz).2, dw, dz, zero_mul, mul_zero, add_zero]
  · rw [em, (hl w' _ hw' hz').2, dw', dz', zero_mul, mul_zero, add_zero]
  · rw [em, em, da _ _ (hm _ _ hw hv) (hm _ _ hz' hu), (hl w _ hw hv).2, (hl z' _ hz' hu).2, dw, dz', ← eu, ← ev,
      zero_mul, zero_mul, zero_add, zero_add, mul_sub, mul_sub, ecomm z' w, ecomm z' w']
    abel

end GlobalTheory.ChernCalc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetReLePowMulDetReStatement
section
open Filter Topology MeasureTheory GlobalTheory.HSAmp
open scoped ComplexOrder Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.det_re_le_pow_mul_det_re_of_posDef : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (A B : Matrix ι ι ℂ) (κ : ℝ), A.PosDef → B.PosDef → (∀ c : ι → ℂ, (star c ⬝ᵥ A *ᵥ c).re ≤ κ * (star c ⬝ᵥ B *ᵥ c).re) → A.det.re ≤ κ ^ Fintype.card ι * B.det.re := by
  first | exact @GlobalTheory.HSAmp.det_re_le_pow_mul_det_re | exact GlobalTheory.HSAmp.det_re_le_pow_mul_det_re | (intros; apply GlobalTheory.HSAmp.det_re_le_pow_mul_det_re <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenlatticeSlopeLowerBoundDefiniteCase
section
open CategoryTheory NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.DefPt ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open scoped Matrix Classical

namespace GlobalTheory.DefPt

theorem eigLat_slope_definite : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (ξ : ℝ) (V : (c.F →+* ℂ) → HSp D) (dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r) (G : Type) [Group G] [Finite G] (lev : G → (Dw.La →ₗ[𝓞 D.host.E] Dw.La) × (Dw.La →ₗ[𝓞 D.host.E] Dw.La)) (χ : G →* (c.F)ˣ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (c₁ : ℝ), DefCase U ξ → Finite (Comp Xo c) → Nonempty (Comp Xo c) → (∀ σ, GoodEmb c σ → ∀ g, (dict σ g).2 ∈ ((U σ).X (dict σ g).1).dom) → ActLev (Xo := Xo) c lev → FreePt Xo c lev → Dom a n → GoodW U ξ V dict (wtZ a n) → FlatExistsAt U ξ c₁ → eigLat U lev χ (wtZ a n) ≠ ⊥ ∧ defBound Dw a n c₁ ≤ slope_sq (normW U ξ V dict (wtZ a n)) (eigLat U lev χ (wtZ a n)) / 2 := by
  intro D H Dw l Xo c r U ξ V dict G _ _ lev χ a n c₁ hD hF hN hdom hA hfree hDom hW hflat
  exact GlobalTheory.T.levelMove_eigenlattice_slope_definite D H Dw l Xo c r U ξ V dict G lev χ a n (defBound Dw a n c₁) hD hF hN hdom hA hfree hDom hW
    (GlobalTheory.T.definiteCase_cuspForm_fibre_slope_ge_bound D.host.E H Dw l Xo c r U ξ a n c₁ hD hDom hflat)

end GlobalTheory.DefPt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerE8BundleIsoOfPrincipalSiegelIsoStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.SiegLev GlobalTheory.SiegLevCalc GlobalTheory.SiegelPullComp GlobalTheory.SiegelPull
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eighthPower_E8Bundle_iso_of_principalSiegelIso : ∀ (g n N : ℕ) (B : Type) [CommRing B] (ζ : B) (K : Type) [Field K] (s : Sp K ⟶ Sp B) (c : SiegPre g n ζ s) (b : TBase K N) (C : SiegPre g N (b.ζ : K) (𝟙 (Sp K))) (W : Matrix (Fin 8) (Fin 8) ℤ) (J : Type) (a : J → Matrix (Fin 8) (Fin 8) ℤ) (bas : (Fin (2 * (8 * g)) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin g ⊕ Fin g → ℤ))) (t : TObj (8 * g) N J b (𝟙 (Sp K))) (Q : PolAV (Sp K)) (pr : Fin 8 → (Q.A ⟶ c.A)), (∀ u, IsMonHom (pr u)) → (∀ (T' : Over (Sp K)) (y : Fin 8 → (T' ⟶ c.A)), ∃! x : T' ⟶ Q.A, ∀ u, x ≫ pr u = y u) → LBIso Q.L (LB.LinComb c.P (K := Fin 8 × Fin 8) (fun uv => (lift (pr uv.1) (pr uv.2)).left) (fun uv => W uv.1 uv.2)) → SRel C c 0 0 (𝟙 _) → IsSharp W a bas t C → ∃ φ : t.A ≅ Q.A, IsMonHom φ.hom ∧ LBIso t.L (Q.L.pull φ.hom.left) := by
  first | exact @GlobalTheory.SharpIso.iso_of_sRel | exact GlobalTheory.SharpIso.iso_of_sRel | (intros; apply GlobalTheory.SharpIso.iso_of_sRel <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfDivisibleInLattice
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField
open scoped TensorProduct
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_zero_of_divisible_in_lattice : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (z : AfP p ⊗[ℚ] VQ D), (∀ n : ℕ, 0 < n → n.Coprime p → ∃ w ∈ LaHat D, z = n • w) → z = 0 := by
  first | (exact @GlobalTheory.LKGeo.eq_zero_of_forall_nsmul_laHat) | (exact GlobalTheory.LKGeo.eq_zero_of_forall_nsmul_laHat) | (intros; apply GlobalTheory.LKGeo.eq_zero_of_forall_nsmul_laHat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdelicEndomorphismLattice
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField
open scoped TensorProduct
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_adelic_endomorphism_lattice : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (g : ℕ → D.La →+ D.La), (∀ n m : ℕ, 0 < n → 0 < m → (n * m).Coprime p → ∀ x, ∃ z, g (n * m) x = g n x + n • z) → ∃ h₀ : Module.End (AfP p) (AfP p ⊗[ℚ] VQ D), (∀ v ∈ LaHat D, h₀ v ∈ LaHat D) ∧ ∀ n : ℕ, 0 < n → n.Coprime p → ∀ x, ∃ w ∈ LaHat D, h₀ (inAf D x) = inAf D (g n x) + n • w := by
  first | (exact @GlobalTheory.LKGeo.ModLim.exists_limit) | (exact GlobalTheory.LKGeo.ModLim.exists_limit) | (intros; apply GlobalTheory.LKGeo.ModLim.exists_limit <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdelicWeilRepUnitaryPairSchroedingerModelStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_adelicWeilRep_unitaryPair_schroedingerModel : ∀ (D : D7) (B : Base D.host.F D.host.E), B.IsGood D.sp.cm.sig →
    ∀ (n d : ℕ) (X : Spc D.host.F D.host.E n) (Y : Spc D.host.F D.host.E d) (r s r' s' : ℕ),
      X.IsHerm D.sp.cm.sig B r s → Y.IsSkew D.sp.cm.sig B r' s' →
      ∀ Mo : Model D.sp.cm.sig X Y, Mo.IsGood B.ψ →
      ∀ χX χW : Chr D.host.F D.host.E, GlobalTheory.LFun.IsHecke D.host.F D.host.E χX → GlobalTheory.LFun.IsHecke D.host.F D.host.E χW →
        GlobalTheory.WeilM.ResEtaPow (Units.map (algebraMap D.host.F (AF D.host.F)).toMonoidHom).range χX n →
        GlobalTheory.WeilM.ResEtaPow (Units.map (algebraMap D.host.F (AF D.host.F)).toMonoidHom).range χW d →
        ∃ om, Mo.IsWeil B.ψ χX χW om := by
  first | exact @GlobalTheory.WeilSchrodinger.exists_isWeil | exact GlobalTheory.WeilSchrodinger.exists_isWeil | (intros; apply GlobalTheory.WeilSchrodinger.exists_isWeil <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdjointEndomorphismUniformisedGroupStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_adjoint_endomorphism_uniformised_group : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ g : G ⟶ G, IsMonHom g → ∃ g' : G ⟶ G, IsMonHom g' ∧ LBIso (cubeLB G ![fst G G ≫ g, snd G G] U.LG.L) (cubeLB G ![fst G G, snd G G ≫ g'] U.LG.L) := by
  first | exact @GlobalTheory.Mum.GroupAdjoint.exists_adjoint_on_group | exact GlobalTheory.Mum.GroupAdjoint.exists_adjoint_on_group | (intros; apply GlobalTheory.Mum.GroupAdjoint.exists_adjoint_on_group <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAlgebraicFactorOfUnimodularTensor
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum

theorem TensO.idem_binv_alg {r : ℕ} (s : SymUnit r) (i₀ : Fin r)
    (hp : 0 < (s.1 : Matrix (Fin r) (Fin r) ℤ) i₀ i₀) :
    (∃ b : ℕ, 0 < b ∧ Star.star (TensO.idem s i₀) * TensO.idem s i₀ =
        b • (Star.star (TensO.idem s i₀) * TensO.binv s * TensO.idem s i₀)) ∧
      Star.star (TensO.idem s i₀) * TensO.binv s * TensO.idem s i₀ =
        Star.star (TensO.idem s i₀) * Star.star (TensO.binv s) * TensO.idem s i₀ ∧
      ∃ g : TensO s, g * (Star.star (TensO.idem s i₀) * TensO.binv s * TensO.idem s i₀) = TensO.idem s i₀ := by
  have hf : Star.star (TensO.binv s) = TensO.binv s := by
    show ((s.1⁻¹ : (Matrix (Fin r) (Fin r) ℤ)ˣ) : Matrix (Fin r) (Fin r) ℤ) *
      ((s.1⁻¹ : (Matrix (Fin r) (Fin r) ℤ)ˣ) : Matrix (Fin r) (Fin r) ℤ).transpose *
        (s.1 : Matrix (Fin r) (Fin r) ℤ) = ((s.1⁻¹ : (Matrix (Fin r) (Fin r) ℤ)ˣ) : Matrix (Fin r) (Fin r) ℤ)
    rw [TensO.inv_transpose, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
  have hEE : (Matrix.single i₀ i₀ (1 : ℤ) : Matrix (Fin r) (Fin r) ℤ) * Matrix.single i₀ i₀ 1 =
      Matrix.single i₀ i₀ 1 := by simp
  have hET : (Matrix.single i₀ i₀ (1 : ℤ) : Matrix (Fin r) (Fin r) ℤ).transpose = Matrix.single i₀ i₀ 1 := by simp
  have hmain : ((s.1⁻¹ : (Matrix (Fin r) (Fin r) ℤ)ˣ) : Matrix (Fin r) (Fin r) ℤ) *
      (Matrix.single i₀ i₀ (1 : ℤ) : Matrix (Fin r) (Fin r) ℤ).transpose * (s.1 : Matrix (Fin r) (Fin r) ℤ) *
      ((s.1⁻¹ : (Matrix (Fin r) (Fin r) ℤ)ˣ) : Matrix (Fin r) (Fin r) ℤ) * Matrix.single i₀ i₀ (1 : ℤ) =
      ((s.1⁻¹ : (Matrix (Fin r) (Fin r) ℤ)ˣ) : Matrix (Fin r) (Fin r) ℤ) * Matrix.single i₀ i₀ (1 : ℤ) := by
    rw [hET, Matrix.mul_assoc _ (s.1 : Matrix (Fin r) (Fin r) ℤ), Units.mul_inv, Matrix.mul_one, Matrix.mul_assoc, hEE]
  have hefe : Star.star (TensO.idem s i₀) * TensO.binv s * TensO.idem s i₀ = TensO.binv s * TensO.idem s i₀ := hmain
  refine ⟨⟨((s.1 : Matrix (Fin r) (Fin r) ℤ) i₀ i₀).toNat, by omega, ?_⟩, by rw [hf], TensO.ofMat s s.1, ?_⟩
  · rw [hefe]
    have h : ((s.1⁻¹ : (Matrix (Fin r) (Fin r) ℤ)ˣ) : Matrix (Fin r) (Fin r) ℤ) *
        (Matrix.single i₀ i₀ (1 : ℤ) : Matrix (Fin r) (Fin r) ℤ).transpose * (s.1 : Matrix (Fin r) (Fin r) ℤ) *
        Matrix.single i₀ i₀ (1 : ℤ) = ((s.1 : Matrix (Fin r) (Fin r) ℤ) i₀ i₀).toNat •
        (((s.1⁻¹ : (Matrix (Fin r) (Fin r) ℤ)ˣ) : Matrix (Fin r) (Fin r) ℤ) * Matrix.single i₀ i₀ (1 : ℤ)) := by
      rw [hET, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (Matrix.single i₀ i₀ (1 : ℤ)),
        Matrix.single_mul_mul_single, ← Matrix.mul_smul]
      congr 1
      rw [Matrix.smul_single, nsmul_eq_mul, Int.toNat_of_nonneg hp.le]
      simp
    exact h
  · rw [hefe]
    have h : (s.1 : Matrix (Fin r) (Fin r) ℤ) *
        (((s.1⁻¹ : (Matrix (Fin r) (Fin r) ℤ)ˣ) : Matrix (Fin r) (Fin r) ℤ) * Matrix.single i₀ i₀ (1 : ℤ)) =
        Matrix.single i₀ i₀ (1 : ℤ) := by
      rw [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
    exact h

theorem Tens.nonempty_factor : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) →
    ∀ (D D' : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ),
      ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → IsUnit (W + W.transpose).det →
      ∀ T : Tens D.toPre D'.toPre W, 1 ≤ r → (∃ F : Factor D.toPre D'.toPre, F.Alg) := by
  intro R _ _ _ hR D D' r W hpos hdet T hr
  let s := symUnitOf W hdet
  let i₀ : Fin r := ⟨0, hr⟩
  letI := T.mod s
  obtain ⟨hhom, h1, hmul, hadd⟩ := GlobalTheory.T.mumfordTensorData_matrixAction_ringHom_properties R D.toPre D'.toPre W T
  obtain ⟨hinc, hip, hpi, hcx⟩ := GlobalTheory.T.mumfordTensorData_factorInclusion_projection_props R D.toPre D'.toPre W T i₀
  obtain ⟨hxx, hxe, hinj, honto⟩ := GlobalTheory.T.mumfordTensorData_latticeFactor_props R D.toPre D'.toPre W T s i₀
  obtain ⟨w, hw, htau⟩ := GlobalTheory.T.mumfordTensorPairing_factorInclusion_periods R hR D D' W hdet hpos T i₀
  have hp : 0 < (s.1 : Matrix (Fin r) (Fin r) ℤ) i₀ i₀ := by
    have h := hpos.diag_pos (i := i₀)
    have h' : (0 : ℝ) < (((W + W.transpose) i₀ i₀ : ℤ) : ℝ) := h
    exact_mod_cast h'
  exact ⟨{
    O := TensO s
    mod := T.mod s
    o := { onB := { act := fun a => T.act (TensO.mat s a)
                    hom := fun a => hhom _
                    map_one := h1
                    map_mul := fun a b => hmul _ _
                    map_add := fun a b => hadd _ _
                    rosati := GlobalTheory.T.rosatiAdj_mumfordTensorPower_of_posDef R hR D D' W hdet hpos T }
           c_lin := GlobalTheory.T.tensor_action_compatible_with_degeneration R D.toPre D'.toPre W T s
           tau_bal := GlobalTheory.T.tensorDegData_periods_balanced_matrixAction R hR D D' W hdet hpos T }
    e := TensO.idem s i₀
    f := TensO.binv s
    inc := T.inc i₀
    pr := T.pr i₀
    xi := T.xi i₀
    xp := T.xp i₀
    w := w
    idem := TensO.idem_mul_idem s i₀
    inc_hom := hinc
    pr_hom := T.pr_hom i₀
    inc_pr := hip
    pr_inc := hpi
    xp_xi := hxx
    xi_xp := hxe
    c_xi := hcx
    inj := hinj
    onto := honto
    w_gen := hw
    tau := htau }, TensO.idem_binv_alg s i₀ hp⟩

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAmplePowerLiftOfNonvanishingOnClosedStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ample_power_lift_of_nonvanishing_on_closed : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (L : LB X), IsAmpleLB L → ∀ (T : Scheme.{0}) (i : T ⟶ X) [IsClosedImmersion i] (n : ℕ) (s : (lbPow (L.pull i) n).Sec), 1 ≤ n → ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus s = ⊤ → ∃ (N : ℕ) (u : (lbPow L N).Sec), 1 ≤ N ∧ Set.range i ⊆ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus u := by
  first | exact @GlobalTheory.LiftAmple.exists_sec_nonzero_on_closed | exact GlobalTheory.LiftAmple.exists_sec_nonzero_on_closed | (intros; apply GlobalTheory.LiftAmple.exists_sec_nonzero_on_closed <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAmplePowerSectionNonvanishingOnFiniteStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ample_power_section_nonvanishing_on_finite : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), IsAmpleLB P.L.B → ∀ S : Set X, S.Finite → ∃ e : ℕ, 0 < e ∧ ∃ f ∈ P.H e 0, S ⊆ NV P e 0 f := by
  first | exact @GlobalTheory.HSAmp.exists_sec_nonvanishing_finite | exact GlobalTheory.HSAmp.exists_sec_nonvanishing_finite | (intros; apply GlobalTheory.HSAmp.exists_sec_nonvanishing_finite <;> assumption)
end

