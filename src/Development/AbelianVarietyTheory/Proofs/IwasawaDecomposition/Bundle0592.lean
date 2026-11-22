import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GeometricallyConnectedOfIsPullbackOfSurjective
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsNeZeroIsStandardSmoothOfRelativeDimension
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ToroidalBoundaryMetricData
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0576
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.Bundle0001
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0037
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0586
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineStableLieEigenspaceFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0573
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegersAlt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0577
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0568
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0572

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ComplexPointsNonemptyDenseVariety
section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open scoped TensorProduct Topology GlobalTheory.AffinePoints

namespace GlobalTheory.CxPtsDense

open GlobalTheory.CxPts

variable {F : Type} [Field F] {X : Scheme.{0}} (p : X ⟶ Sp F) (σ : F →+* ℂ)

theorem exists_param [GeometricallyIntegral p] [LocallyOfFiniteType p] {U : X.Opens} (hU : IsAffineOpen U)
    {f : Γ(X, U)} (hf : f ≠ 0) :
    ∃ (B : Type) (_ : TopologicalSpace B) (s : B → CxPts p σ), Nonempty B ∧ Continuous s ∧
      ptsIn p σ U ⊆ Set.range s ∧ Dense (s ⁻¹' ptsIn p σ (X.basicOpen f)) := by
  let : Algebra F Γ(X, U) := (algX p U).toAlgebra
  let : Algebra F ℂ := σ.toAlgebra
  have hft : (algX p U).FiniteType :=
    (HasRingHomProperty.appLE @LocallyOfFiniteType p ‹_› ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ le_top).comp
      (RingHom.FiniteType.of_surjective _
        (Scheme.ΓSpecIso (CommRingCat.of F)).symm.commRingCatIsoToRingEquiv.surjective)
  have : Algebra.FiniteType F Γ(X, U) := hft
  have hg : hU.fromSpec ≫ p = Spec.map (CommRingCat.ofHom (algebraMap F Γ(X, U))) := by
    have h := IsAffineOpen.SpecMap_appLE_fromSpec p (isAffineOpen_top _) hU
      (show U ≤ p ⁻¹ᵁ ⊤ from le_top)
    rw [← h, IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]
    rfl
  have : Nontrivial Γ(X, U) := nontrivial_of_ne _ _ hf
  have : NoZeroDivisors (ℂ ⊗[F] Γ(X, U)) :=
    @UnitRigidity.noZeroDivisors_tensor F Γ(X, U) _ _ _ (algX p U).toAlgebra X p _
      hU.fromSpec (inferInstanceAs (IsOpenImmersion hU.fromSpec)) hg ℂ _ _
  have hinj := Algebra.TensorProduct.includeRight_injective (R := F) (A := ℂ) (B := Γ(X, U))
      (algebraMap F ℂ).injective
  have : Nontrivial (ℂ ⊗[F] Γ(X, U)) := hinj.nontrivial
  have : IsDomain (ℂ ⊗[F] Γ(X, U)) := NoZeroDivisors.to_isDomain _
  let φ (q : ℂ ⊗[F] Γ(X, U) →ₐ[ℂ] ℂ) : Γ(X, U) →+* ℂ :=
    q.toRingHom.comp (Algebra.TensorProduct.includeRight (R := F) (A := ℂ)).toRingHom
  have hφa (q) (a) : φ q a = q (1 ⊗ₜ a) := rfl
  have hφ (q) (a : F) : φ q (algX p U a) = σ a := by
    have : ((1 : ℂ) ⊗ₜ[F] algX p U a) = algebraMap ℂ (ℂ ⊗[F] Γ(X, U)) (σ a) :=
      (Algebra.TensorProduct.tmul_one_eq_one_tmul (R := F) (A := ℂ) (B := Γ(X, U)) a).symm
    rw [hφa, this, AlgHom.commutes]
    rfl
  let s (q : ℂ ⊗[F] Γ(X, U) →ₐ[ℂ] ℂ) : CxPts p σ := ofHom hU (φ q) (hφ q)
  have hsU (q) : s q ∈ ptsIn p σ U := ofHom_mem _ _ _
  have hsv (q) (a) : ev p σ U a (s q) = q (1 ⊗ₜ a) := ev_ofHom _ _ _ a
  refine ⟨_, inferInstance, s, ?_, ?_, fun y hy => ?_, ?_⟩
  · obtain ⟨m, hm⟩ := Ideal.exists_maximal (ℂ ⊗[F] Γ(X, U))
    let := Ideal.Quotient.field m
    have : Module.Finite ℂ ((ℂ ⊗[F] Γ(X, U)) ⧸ m) := finite_of_finite_type_of_isJacobsonRing _ _
    exact ⟨(IsAlgClosed.lift (R := ℂ) (S := (ℂ ⊗[F] Γ(X, U)) ⧸ m) (M := ℂ)).comp (Ideal.Quotient.mkₐ ℂ m)⟩
  · refine continuous_iff_continuousAt.2 fun q => tendsto_subtype_rng.2
      (GlobalTheory.Points.tendsto_of_isAffineOpen hU (hsU q) (Filter.Eventually.of_forall hsU) fun a => ?_)
    have h : Continuous (ev p σ U a ∘ s) := by
      have : ev p σ U a ∘ s = fun q => q (1 ⊗ₜ a) := funext fun q => hsv q a
      rw [this]
      exact GlobalTheory.AffinePoints.continuous_eval _
    exact h.continuousAt
  · let ψ : Γ(X, U) →ₐ[F] ℂ :=
      { evHom hy with commutes' := fun a => (ev_eq hy _).symm.trans (ev_algX hy a) }
    let q : ℂ ⊗[F] Γ(X, U) →ₐ[ℂ] ℂ :=
      Algebra.TensorProduct.lift (AlgHom.id ℂ ℂ) ψ fun _ _ => Commute.all _ _
    refine ⟨q, Subtype.ext (GlobalTheory.Points.ext_of_valR hU (hsU q) hy fun a => ?_)⟩
    refine (hsv q a).trans ?_
    simp only [q, Algebra.TensorProduct.lift_tmul, map_one, one_mul]
    exact (ev_eq hy a).symm
  · have hf' : ((1 : ℂ) ⊗ₜ[F] f) ≠ 0 := (map_ne_zero_iff _ hinj).2 hf
    refine (GlobalTheory.AffinePoints.dense_nonvanishing hf').mono fun q hq => ?_
    refine (mem_ptsIn_basicOpen (hsU q) f).2 ?_
    rw [hsv]
    exact hq

theorem exists_ne_zero_basicOpen_le [IsIntegral X] {U W : X.Opens} (hU : IsAffineOpen U)
    (hne : (U : Set X).Nonempty) (hW : (W : Set X).Nonempty) :
    ∃ f : Γ(X, U), f ≠ 0 ∧ X.basicOpen f ≤ W := by
  obtain ⟨x, hxU, hxW⟩ := nonempty_preirreducible_inter U.isOpen W.isOpen hne hW
  obtain ⟨f, hfW, hf⟩ := hU.exists_basicOpen_le (V := W) ⟨x, hxW⟩ hxU
  refine ⟨f, ?_, hfW⟩
  rintro rfl
  rw [Scheme.basicOpen_zero] at hf
  exact hf

theorem nonempty_and_dense_of_geometricallyIntegral [GeometricallyIntegral p] [LocallyOfFiniteType p] :
    Nonempty (CxPts p σ) ∧ ∀ W : X.Opens, (W : Set X).Nonempty → Dense (ptsIn p σ W) := by
  have : IsIntegral X := GeometricallyIntegral.isIntegral_of_subsingleton p
  refine ⟨?_, fun W hW y => ?_⟩
  · obtain ⟨U, hU, hx, -⟩ := Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens (Opens.mem_top (genericPoint X))
    obtain ⟨f, hf, -⟩ := exists_ne_zero_basicOpen_le hU ⟨_, hx⟩ ⟨_, hx⟩
    obtain ⟨B, _, s, ⟨b⟩, -⟩ := exists_param p σ hU hf
    exact ⟨s b⟩
  · obtain ⟨U, hU, hx, -⟩ := Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens
      (Opens.mem_top (y.1 (IsLocalRing.closedPoint ℂ)))
    obtain ⟨f, hf, hfW⟩ := exists_ne_zero_basicOpen_le hU ⟨_, hx⟩ hW
    obtain ⟨B, _, s, -, hs, hr, hd⟩ := exists_param p σ hU hf
    obtain ⟨b, rfl⟩ := hr (mem_ptsIn.2 hx)
    exact closure_mono (ptsIn_mono hfW) (hs.closure_preimage_subset _ (hd b))

theorem nonempty_and_dense : ∀ (F : Type) [Field F] (Y : GlobalTheory.ProjVar.Var F) (σ : F →+* ℂ),
    Nonempty (CxPts Y.str σ) ∧ ∀ W : Y.X.Opens, (W : Set Y.X).Nonempty → Dense (CxPts.ptsIn Y.str σ W) :=
  fun _ _ Y σ => nonempty_and_dense_of_geometricallyIntegral Y.str σ

end GlobalTheory.CxPtsDense
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjSmoothOnPreimageCharts
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TopologicalSpace Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.ShFam
open ReciprocityTheory.L2DbarEstimates (V bas wd wdb leviV)
open Filter Topology
open scoped ContDiff

namespace GlobalTheory.ShFam

attribute [local instance] Over.cartesianMonoidalCategory

def conjV (n : ℕ) : V n ≃ₗᵢ[ℝ] V n := LinearIsometryEquiv.piLpCongrRight 2 fun _ => Complex.conjLIE

theorem conjV_apply (n : ℕ) (v : V n) (a : Fin n) : conjV n v a = starRingEnd ℂ (v a) := rfl

theorem conjV_bas (n : ℕ) (j : Fin n) : conjV n (bas n j) = bas n j := by
  ext a
  simp only [conjV_apply, bas, EuclideanSpace.single_apply]
  split_ifs <;> simp

theorem conjV_I_smul_bas (n : ℕ) (j : Fin n) : conjV n (Complex.I • bas n j) = -(Complex.I • bas n j) := by
  ext a
  simp only [conjV_apply, bas, PiLp.smul_apply, PiLp.neg_apply, EuclideanSpace.single_apply, smul_eq_mul]
  split_ifs <;> simp

theorem fderiv_comp_conjV (n : ℕ) (F : V n → ℂ) (y w : V n) :
    fderiv ℝ (F ∘ conjV n) y w = fderiv ℝ F (conjV n y) (conjV n w) := by
  change fderiv ℝ (F ∘ (conjV n).toContinuousLinearEquiv) y w = _
  rw [ContinuousLinearEquiv.comp_right_fderiv]
  rfl

theorem wd_comp_conjV (n : ℕ) (j : Fin n) (F : V n → ℂ) (y : V n) :
    wd n j (F ∘ conjV n) y = wdb n j F (conjV n y) := by
  simp only [wd, wdb, fderiv_comp_conjV, conjV_bas, conjV_I_smul_bas, map_neg]
  ring

theorem wdb_comp_conjV (n : ℕ) (j : Fin n) (F : V n → ℂ) (y : V n) :
    wdb n j (F ∘ conjV n) y = wd n j F (conjV n y) := by
  simp only [wd, wdb, fderiv_comp_conjV, conjV_bas, conjV_I_smul_bas, map_neg]
  ring

theorem leviV_comp_conjV (n : ℕ) (g : V n → ℝ) (y : V n) (ξ : Fin n → ℂ) :
    leviV n ((fun v => (g v : ℂ)) ∘ conjV n) y ξ =
      starRingEnd ℂ (leviV n (fun v => (g v : ℂ)) (conjV n y) (star ξ)) := by
  set G : V n → ℂ := fun v => (g v : ℂ) with hGdef
  have hG : ∀ k, wd n k G = fun w => starRingEnd ℂ (wdb n k G w) := fun k => by
    have e : G = fun w => starRingEnd ℂ (G w) := funext fun w => (Complex.conj_ofReal _).symm
    funext w
    conv_lhs => rw [e]
    exact ReciprocityTheory.L2DbarEstimates.ChartWirtingerDerivatives.wd_conj' n k G w
  have h1 : ∀ k, wdb n k (G ∘ conjV n) = (wd n k G) ∘ conjV n := fun k =>
    funext fun w => wdb_comp_conjV n k G w
  have h2 : ∀ j k w, wd n j (wdb n k (G ∘ conjV n)) w =
      starRingEnd ℂ (wd n j (wdb n k G) (conjV n w)) := fun j k w => by
    rw [h1, wd_comp_conjV, hG, ReciprocityTheory.L2DbarEstimates.ChartWirtingerDerivatives.wdb_conj']
  simp only [leviV, h2, map_sum, map_mul, Complex.conj_conj, Pi.star_apply, Complex.star_def]

theorem smoothOn_comp_ddcForm_of_isConjMap : ∀ (k : Type) [Field k] (Y : Scheme.{0}) (p : Y ⟶ Sp k) (d : ℕ)
    [SmoothOfRelativeDimension d p] (σ σ' : k →+* ℂ) (j : CxPts p σ' → CxPts p σ), IsConjMap j →
    ∀ (W : Set (CxPts p σ)) (φ : CxPts p σ → ℝ), IsOpen W → (AnRead.all p σ d).SmoothOn W φ →
    IsOpen (j ⁻¹' W) ∧ (AnRead.all p σ' d).SmoothOn (j ⁻¹' W) (φ ∘ j) ∧
    ∀ (c' : AlgChart p σ' d), ∀ z ∈ c'.e.source, ∃ c : AlgChart p σ d, j z ∈ c.e.source ∧
      ∀ (ψ : CxPts p σ → ℝ) (ξ : Fin d → ℂ), ddcForm (ψ ∘ j) c' z ξ = ddcForm ψ c (j z) (star ξ) := by
  intro k _ Y p d _ σ σ' j hj W φ hW hφ
  rcases isEmpty_or_nonempty (CxPts p σ') with hE | ⟨⟨z0⟩⟩
  · refine ⟨?_, fun c' => ?_, fun c' z => (hE.false z).elim⟩
    · rw [Set.eq_empty_of_isEmpty (j ⁻¹' W)]
      exact isOpen_empty
    · rw [Set.eq_empty_of_isEmpty (j ⁻¹' W)]
      simp
  · have hσ : σ = (starRingEnd ℂ).comp σ' := by
      have h1 := (j z0).2
      rw [hj z0, Category.assoc, z0.2, spMap, spMap, spMap, ← Spec.map_comp] at h1
      have h2 := congrArg CommRingCat.Hom.hom (Spec.map_injective h1)
      exact h2.symm
    obtain ⟨hcont, hch⟩ := GlobalTheory.ConjChart.continuous_and_exists_conj_chart k Y p d σ σ' j hσ hj
    have key : ∀ c' : AlgChart p σ' d, ∃ c : AlgChart p σ d, (∀ z, j z ∈ c.e.source ↔ z ∈ c'.e.source) ∧
        (∀ z ∈ c'.e.source, c.e (j z) = conjV d (c'.e z)) ∧
        ∀ v ∈ c'.e.target, j (c'.e.symm v) = c.e.symm (conjV d v) := fun c' => by
      obtain ⟨c, hs, he⟩ := hch c'
      have e1 : ∀ z ∈ c'.e.source, c.e (j z) = conjV d (c'.e z) := fun z hz => by
        ext a
        rw [he z hz a, conjV_apply]
      refine ⟨c, hs, e1, fun v hv => ?_⟩
      have hz : c'.e.symm v ∈ c'.e.source := c'.e.map_target hv
      rw [← c.e.left_inv ((hs _).2 hz), e1 _ hz, c'.e.right_inv hv]
    refine ⟨hW.preimage hcont, fun c' => ?_, fun c' z hz => ?_⟩
    · obtain ⟨c, hs, e1, e2⟩ := key c'
      show ContDiffOn ℝ ∞ ((φ ∘ j) ∘ c'.e.symm) (c'.e.target ∩ c'.e.symm ⁻¹' (j ⁻¹' W))
      have hc := hφ.chart hW c
      refine ((hc.comp (conjV d).contDiff.contDiffOn fun v hv => ?_).congr fun v hv => ?_)
      · have hz : c'.e.symm v ∈ c'.e.source := c'.e.map_target hv.1
        refine ⟨?_, ?_⟩
        · have e3 : conjV d v = c.e (j (c'.e.symm v)) := by rw [e1 _ hz, c'.e.right_inv hv.1]
          rw [e3]
          exact c.e.map_source ((hs _).2 hz)
        · show c.e.symm (conjV d v) ∈ W
          rw [← e2 v hv.1]
          exact hv.2
      · show (φ ∘ j) (c'.e.symm v) = (φ ∘ c.e.symm) (conjV d v)
        simp only [Function.comp_apply, e2 v hv.1]
    · obtain ⟨c, hs, e1, e2⟩ := key c'
      refine ⟨c, (hs z).2 hz, fun ψ ξ => ?_⟩
      have h := leviV_comp_conjV d (fun v => ψ (c.e.symm v)) (c'.e z) ξ
      simp only [ddcForm, AlgChart.levi]
      congr 1
      rw [e1 z hz]
      refine Eq.trans (congrArg Complex.re (ReciprocityTheory.L2DbarEstimates.leviV_congr ?_ ξ))
        (Eq.trans (congrArg Complex.re h) (Complex.conj_re _))
      refine eventually_of_mem (c'.e.open_target.mem_nhds (c'.e.map_source hz)) fun v hv => ?_
      simp only [Function.comp_apply, e2 v hv]

end GlobalTheory.ShFam
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoordinateSectionsOfWeight
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
  GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.Pad

namespace GlobalTheory.ShFam.ValCoord

open GlobalTheory.ShFam.Descent

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}

theorem exists_bc {A B : Type} [CommRing A] [CommRing B] {φ : c.F →+* A} {x : Sp A ⟶ Z.X} (fr : EigFrame Z φ x)
    (ρ : A →+* B) {x' : Sp B ⟶ Z.X} (hx : spMap ρ ≫ x = x') :
    ∃ g : EigFrame Z (ρ.comp φ) x', ∀ τ i, g.v τ i = spMap (dualMap ρ) ≫ fr.v τ i := by
  subst hx
  exact EigFrame.exists_baseChange E H Dw l Xo c O β Z A B φ x fr ρ

theorem spMap_dualMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (ρ : A →+* B) (χ : B →+* C) :
    spMap (dualMap χ) ≫ spMap (dualMap ρ) = spMap (dualMap (χ.comp ρ)) := by
  rw [sp_comp]
  congr 1
  ext z <;> simp [dualMap]

theorem tri_bc {A B C : Type} [CommRing A] [CommRing B] [CommRing C] {φ : c.F →+* A} {x : Sp A ⟶ Z.X}
    {fr : EigFrame Z φ x} {ρ : A →+* B} {x₀ : Sp B ⟶ Z.X} (hx₀ : spMap ρ ≫ x = x₀) {g₀ : EigFrame Z (ρ.comp φ) x₀}
    (hg : ∀ τ i, g₀.v τ i = spMap (dualMap ρ) ≫ fr.v τ i) {χ : B →+* C} {φ' : c.F →+* C} {x' : Sp C ⟶ Z.X}
    {g : EigFrame Z φ' x'} {t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Cˣ} (h : fr.Tri (χ.comp ρ) g t) : g₀.Tri χ g t := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, ?_, fun τ i => ?_⟩
  · rw [h1, ← hx₀, ← Category.assoc, sp_comp]
  · rw [h2]; rfl
  · obtain ⟨cf, c1, c2, c3⟩ := h3 τ i
    refine ⟨cf, c1, c2, ?_⟩
    have e : (fun k => spMap (dualMap χ) ≫ g₀.v τ k) = fun k => spMap (dualMap (χ.comp ρ)) ≫ fr.v τ k :=
      funext fun k => by rw [hg, ← Category.assoc, spMap_dualMap_comp]
    rw [e]
    exact c3

variable {F : Type} [Field F] [NumberField F] {e : F ≃+* c.F} (Y : FlagCpt Z e)

theorem core {k : Type} [Field k] [Algebra c.F k] (P : FrPt Xo c k) {ex : Ix Dw → ℤ} (hex : ex none = 0)
    {f : Rul Xo c} (hf : f ∈ GlobalTheory.AllWt.secZ Xo c ex) {n : Letter Dw → ℤ} (hn : ∀ z, n z = -ex (some z))
    {p : Sp k ⟶ Y.Y.X} (hp : p ≫ Y.π = GlobalTheory.AllWt.ptF P ≫ Z.jQ) {y : Y.Y.X} {ψ : Y.Y.X.presheaf.stalk y →+* k}
    {φ₁ : c.F →+* Y.Y.X.presheaf.stalk y} {fr : EigFrame Z φ₁ (stalkPt Y.Y y ≫ Y.π ≫ genι Z)}
    {t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Y.Y.Fnˣ} {t' : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → kˣ}
    (h1 : p = spMap ψ ≫ stalkPt Y.Y y)
    (h2 : fr.Tri (algebraMap (Y.Y.X.presheaf.stalk y) Y.Y.X.functionField) Y.f0 t)
    (h3 : fr.Tri ψ (frameOf Z P) t') :
    ∃ (y₀ : Y.Y.X) (ψ₀ : Y.Y.X.presheaf.stalk y₀ →+* k) (ρ : Y.Y.X.presheaf.stalk y →+* Y.Y.X.presheaf.stalk y₀)
      (g₀ : EigFrame Z (ρ.comp φ₁) (stalkPt Y.Y y₀ ≫ Y.π ≫ genι Z)) (r : Y.Y.X.presheaf.stalk y₀),
      p = spMap ψ₀ ≫ stalkPt Y.Y y₀ ∧
      g₀.Tri (algebraMap (Y.Y.X.presheaf.stalk y₀) Y.Y.X.functionField) Y.f0 t ∧ g₀.Tri ψ₀ (frameOf Z P) t' ∧
      ψ = ψ₀.comp ρ ∧
      algebraMap (Y.Y.X.presheaf.stalk y) Y.Y.X.functionField =
        (algebraMap (Y.Y.X.presheaf.stalk y₀) Y.Y.X.functionField).comp ρ ∧
      algebraMap (Y.Y.X.presheaf.stalk y₀) Y.Y.X.functionField r =
        Y.val f * ((∏ z : Letter Dw, t z.1 z.2 ^ n z : Y.Y.Fnˣ) : Y.Y.Fn) ∧
      evR Xo c f P = ψ₀ r * ((∏ z : Letter Dw, t' z.1 z.2 ^ (-n z) : kˣ) : k) := by
  classical
  obtain ⟨y₀, ψ₀, hp₀, hsp, hopen⟩ : ∃ (y₀ : Y.Y.X) (ψ₀ : Y.Y.X.presheaf.stalk y₀ →+* k),
      spMap ψ₀ ≫ stalkPt Y.Y y₀ = p ∧ y₀ ⤳ y ∧ Y.π y₀ ∈ Set.range Z.jQ := by
    refine ⟨_, (Scheme.stalkClosedPointTo (R := .of k) p).hom, Scheme.Spec_stalkClosedPointTo_fromSpecStalk p, ?_, ?_⟩
    · have : p (IsLocalRing.closedPoint k) ∈ Set.range (Y.Y.X.fromSpecStalk y) := by
        rw [h1]
        exact ⟨_, (Scheme.Hom.comp_apply _ _ _).symm⟩
      rwa [Scheme.range_fromSpecStalk] at this
    · have := congrArg (fun q : Sp k ⟶ gen Z => q (IsLocalRing.closedPoint (CommRingCat.of k))) hp
      simp only [Scheme.Hom.comp_apply] at this
      exact ⟨_, this.symm⟩
  haveI : ∀ z : Y.Y.X, Mono (stalkPt Y.Y z) := fun z => inferInstanceAs (Mono (Y.Y.X.fromSpecStalk z))
  let ρ := (Y.Y.X.presheaf.stalkSpecializes hsp).hom
  have hρ : spMap ρ ≫ stalkPt Y.Y y = stalkPt Y.Y y₀ := Scheme.SpecMap_stalkSpecializes_fromSpecStalk hsp
  have hψ : ψ = ψ₀.comp ρ := by
    apply sp_inj
    apply (cancel_mono (stalkPt Y.Y y)).1
    rw [← h1, ← sp_comp, Category.assoc, hρ, hp₀]
  have hgen : ∀ z : Y.Y.X,
      spMap (algebraMap (Y.Y.X.presheaf.stalk z) Y.Y.X.functionField) ≫ stalkPt Y.Y z = genericPt Y.Y :=
    fun z => Scheme.SpecMap_stalkSpecializes_fromSpecStalk ((genericPoint_spec Y.Y.X).specializes trivial)
  have hι : algebraMap (Y.Y.X.presheaf.stalk y) Y.Y.X.functionField =
      (algebraMap (Y.Y.X.presheaf.stalk y₀) Y.Y.X.functionField).comp ρ := by
    apply sp_inj
    apply (cancel_mono (stalkPt Y.Y y)).1
    rw [hgen, ← sp_comp, Category.assoc, hρ, hgen]
  have hx₀ : spMap ρ ≫ (stalkPt Y.Y y ≫ Y.π ≫ genι Z) = stalkPt Y.Y y₀ ≫ Y.π ≫ genι Z := by
    rw [← Category.assoc, hρ]
  obtain ⟨g₀, hg₀⟩ := exists_bc fr ρ hx₀
  have T1 : g₀.Tri (algebraMap (Y.Y.X.presheaf.stalk y₀) Y.Y.X.functionField) Y.f0 t :=
    tri_bc hx₀ hg₀ (by rw [← hι]; exact h2)
  have T2 : g₀.Tri ψ₀ (frameOf Z P) t' := tri_bc hx₀ hg₀ (by rw [← hψ]; exact h3)

  letI : Algebra c.F (Y.Y.X.presheaf.stalk y₀) := (ρ.comp φ₁).toAlgebra
  letI : Algebra c.F Y.Y.X.functionField := (constF e Y.Y).toAlgebra
  haveI := Z.jQ_open
  have hr : Set.range (stalkPt Y.Y y₀ ≫ Y.π) ⊆ Set.range Z.jQ := by
    rintro _ ⟨q, rfl⟩
    have h1 : stalkPt Y.Y y₀ q ⤳ y₀ := by
      have : stalkPt Y.Y y₀ q ∈ Set.range (Y.Y.X.fromSpecStalk y₀) := ⟨q, rfl⟩
      rwa [Scheme.range_fromSpecStalk] at this
    exact (h1.map Y.π.continuous).mem_open Z.jQ.isOpenEmbedding.isOpen_range hopen
  let xF := IsOpenImmersion.lift Z.jQ _ hr
  have hxF : xF ≫ Z.jQ = stalkPt Y.Y y₀ ≫ Y.π := IsOpenImmersion.lift_fac _ _ _
  have hpt0 : GlobalTheory.AllWt.ptF Y.y0 = spMap (algebraMap (Y.Y.X.presheaf.stalk y₀) Y.Y.X.functionField) ≫ xF := by
    rw [← cancel_mono Z.jQ, Category.assoc, hxF, ← Category.assoc, hgen]
    exact Y.y0_x
  have hc : constF e Y.Y = (algebraMap (Y.Y.X.presheaf.stalk y₀) Y.Y.X.functionField).comp (ρ.comp φ₁) := by
    rw [h2.2.1, hι]; rfl
  have hs : xF ≫ pullback.snd _ _ = spMap (algebraMap c.F (Y.Y.X.presheaf.stalk y₀)) := by
    obtain ⟨φ₂, h⟩ := Spec.map_surjective (xF ≫ pullback.snd _ _)
    have k1 : spMap (algebraMap (Y.Y.X.presheaf.stalk y₀) Y.Y.X.functionField) ≫ spMap φ₂.hom =
        spMap (constF e Y.Y) := by
      have h0 : GlobalTheory.AllWt.ptF Y.y0 ≫ pullback.snd _ _ = spMap (constF e Y.Y) := pullback.lift_snd _ _ _
      rw [← h0, hpt0, Category.assoc, ← h]
      rfl
    rw [sp_comp] at k1
    have k2 := sp_inj k1
    have k3 : φ₂.hom = ρ.comp φ₁ := RingHom.ext fun r =>
      IsFractionRing.injective (Y.Y.X.presheaf.stalk y₀) Y.Y.X.functionField
        ((RingHom.congr_fun k2 r).trans (RingHom.congr_fun hc r))
    rw [← h]
    exact congrArg spMap k3
  have hxj : xF ≫ Z.j = stalkPt Y.Y y₀ ≫ Y.π ≫ genι Z := by
    show xF ≫ Z.jQ ≫ pullback.fst _ _ = _
    rw [← Category.assoc, hxF, Category.assoc]
  obtain ⟨P', hP', htie⟩ := exists_tie_point (Z := Z) hs hxj rfl g₀
  have tie0 : Comparison₂ Y.y0 Y.f0 := ⟨rfl, by
    show _ ≫ Z.jQ ≫ pullback.fst _ _ = _
    rw [← Category.assoc, Y.y0_x, Category.assoc], Y.flagComponentFramedPoint_frame⟩
  let ι₀ : Y.Y.X.presheaf.stalk y₀ →ₐ[c.F] Y.Y.X.functionField :=
    { algebraMap (Y.Y.X.presheaf.stalk y₀) Y.Y.X.functionField with
      commutes' := fun r => (RingHom.congr_fun hc r).symm }
  have hx1 : Y.y0.x = spMap ι₀.toRingHom ≫ P'.x := by
    rw [← ptF_fst Y.y0, ← ptF_fst P', hpt0, hP', Category.assoc]
  obtain ⟨u, hu, hu'⟩ := Comparison₂.bm_of_tri htie tie0 (ψ := ι₀) hx1 T1
  have e1 := BM.evR hu hf
  have hcP : algebraMap c.F k = ψ₀.comp (ρ.comp φ₁) := by
    rw [h3.2.1, hψ]; rfl
  let ψa : Y.Y.X.presheaf.stalk y₀ →ₐ[c.F] k :=
    { ψ₀ with commutes' := fun r => (RingHom.congr_fun hcP r).symm }
  have hptP : GlobalTheory.AllWt.ptF P = spMap ψ₀ ≫ xF := by
    rw [← cancel_mono Z.jQ, Category.assoc, hxF, ← hp, ← hp₀, Category.assoc]
  have hx2 : P.x = spMap ψa.toRingHom ≫ P'.x := by
    rw [← ptF_fst P, ← ptF_fst P', hptP, hP', Category.assoc]
  obtain ⟨v, hv, hv'⟩ := Comparison₂.bm_of_tri htie (tie_frameOf Z P) (ψ := ψa) hx2 T2
  have e2 := BM.evR hv hf

  have hchi : ∀ {A : Type} [CommRing A] [Algebra c.F A] (w : Ix Dw → Aˣ)
      (s : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Aˣ), (∀ τ i, w (some ⟨τ, i⟩) = s τ i) →
      GlobalTheory.ShFam.Descent.chi ex w = ∏ z : Letter Dw, s z.1 z.2 ^ ex (some z) := by
    intro A _ _ w s hw
    simp only [GlobalTheory.ShFam.Descent.chi, Fintype.prod_option, hex, zpow_zero, one_mul]
    exact Finset.prod_congr rfl fun z _ => by rw [← hw z.1 z.2]
  have E1 : Y.val f = ((∏ z : Letter Dw, t z.1 z.2 ^ ex (some z) : Y.Y.Fnˣ) : Y.Y.Fn) *
      algebraMap (Y.Y.X.presheaf.stalk y₀) Y.Y.X.functionField (evR Xo c f P') := by
    rw [← hchi u t hu']
    exact e1
  have E2 : evR Xo c f P = ((∏ z : Letter Dw, t' z.1 z.2 ^ ex (some z) : kˣ) : k) * ψ₀ (evR Xo c f P') := by
    rw [← hchi v t' hv']
    exact e2
  refine ⟨y₀, ψ₀, ρ, g₀, evR Xo c f P', hp₀.symm, T1, T2, hψ, hι, ?_, ?_⟩
  · have pn : (∏ z : Letter Dw, t z.1 z.2 ^ n z) = (∏ z : Letter Dw, t z.1 z.2 ^ ex (some z))⁻¹ := by
      simp only [hn, zpow_neg, Finset.prod_inv_distrib]
    rw [E1, pn, mul_right_comm, Units.mul_inv, one_mul]
  · simp only [hn, neg_neg]
    rw [E2, mul_comm]

theorem coordAt_val_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] [NumberField F] (e : F ≃+* c.F) (Y : FlagCpt Z e) (k : Type) [Field k] [Algebra c.F k] (P : FrPt Xo c k) (ex : Ix Dw → ℤ), ex none = 0 → ∀ f ∈ GlobalTheory.AllWt.secZ Xo c ex, ∀ a : k, CoordAt Y P (fun z => -ex (some z)) (Y.val f) a ↔ Carried Y P ∧ a = evR Xo c f P := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ _ e Y k _ _ P ex hex f hf a
  constructor
  · intro h
    refine ⟨h.carried, ?_⟩
    obtain ⟨p, hp, y, ψ, φ₁, fr, t, t', r₀, h1, h2, h3, h4, h5⟩ := h
    obtain ⟨y₀, ψ₀, ρ, g₀, r, -, -, -, hψ, hι, hr, hev⟩ :=
      core Y P hex hf (n := fun z => -ex (some z)) (fun _ => rfl) hp h1 h2 h3
    have hρ : ρ r₀ = r := IsFractionRing.injective (Y.Y.X.presheaf.stalk y₀) Y.Y.X.functionField (by
      rw [← RingHom.comp_apply, ← hι, h4, hr])
    rw [h5, hev, hψ, RingHom.comp_apply, hρ]
  · rintro ⟨⟨p, hp, y, ψ, φ₁, fr, t, t', h1, h2, h3⟩, rfl⟩
    obtain ⟨y₀, ψ₀, ρ, g₀, r, hp₀, T1, T2, -, -, hr, hev⟩ :=
      core Y P hex hf (n := fun z => -ex (some z)) (fun _ => rfl) hp h1 h2 h3
    exact ⟨p, hp, y₀, ψ₀, _, g₀, t, t', r, hp₀, T1, T2, hr, hev⟩

end GlobalTheory.ShFam.ValCoord
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DvdUnitPowSubOne
section
open ReciprocityTheory.ChartRestriction.G.FD NumberField GlobalTheory.UnipKill

namespace GlobalTheory.UnipKill

theorem unit_pow_congr_one : ∀ (E : Type) [Field E] [NumberField E] (u : (𝓞 E)ˣ) (M : 𝓞 E),
    M ≠ 0 → ∃ k : ℕ, 0 < k ∧ M ∣ ((u ^ k : (𝓞 E)ˣ) : 𝓞 E) - 1 := by
  intro E _ _ u M hM
  set I : Ideal (𝓞 E) := Ideal.span {M} with hI
  have hIb : I ≠ ⊥ := by
    rw [hI, Ne, Ideal.span_singleton_eq_bot]; exact hM
  haveI : Finite (𝓞 E ⧸ I) := Ideal.finiteQuotientOfFreeOfNeBot I hIb
  haveI : Finite (𝓞 E ⧸ I)ˣ := Finite.of_injective (fun x : (𝓞 E ⧸ I)ˣ => (x : 𝓞 E ⧸ I)) (fun a b h => Units.ext h)
  set v : (𝓞 E ⧸ I)ˣ := Units.map (Ideal.Quotient.mk I : 𝓞 E →* 𝓞 E ⧸ I) u with hv
  refine ⟨orderOf v, (isOfFinOrder_of_finite v).orderOf_pos, ?_⟩
  have h1 : v ^ orderOf v = 1 := pow_orderOf_eq_one v
  have h2 : Ideal.Quotient.mk I ((u ^ orderOf v : (𝓞 E)ˣ) : 𝓞 E) = Ideal.Quotient.mk I 1 := by
    have := congrArg (fun w : (𝓞 E ⧸ I)ˣ => (w : 𝓞 E ⧸ I)) h1
    simp only [hv, Units.val_pow_eq_pow_val, Units.coe_map, MonoidHom.coe_coe, Units.val_one] at this
    simpa [Units.val_pow_eq_pow_val, map_pow] using this
  exact Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp h2)

end GlobalTheory.UnipKill
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineStableLieEigenspaceFrameStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.FlagBundle
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_affine_stable_lie_eigenspace_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (z : gen Z), ∃ (U : (gen Z).Opens) (hU : IsAffineOpen U) (φ : c.F →+* Γ(gen Z, U)) (f : EigFrame Z φ (hU.fromSpec ≫ genι Z)), z ∈ U ∧ hU.fromSpec ≫ genStr Z = spMap φ ∧ f.Stable := by
  first | exact @GlobalTheory.ShFam.EigSpread.exists_stable_eigFrame | exact GlobalTheory.ShFam.EigSpread.exists_stable_eigFrame | (intros; apply GlobalTheory.ShFam.EigSpread.exists_stable_eigFrame <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBaseChangeStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_eigFrame_baseChange' : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (A B : Type) [CommRing A] [CommRing B] (φ : c.F →+* A) (x : Sp A ⟶ Z.X) (fr : EigFrame Z φ x) (ψ : A →+* B), ∃ g : EigFrame Z (ψ.comp φ) (spMap ψ ≫ x), ∀ τ i, g.v τ i = spMap (dualMap ψ) ≫ fr.v τ i := by
  first | exact @GlobalTheory.ShFam.EigFrame.exists_baseChange | exact GlobalTheory.ShFam.EigFrame.exists_baseChange | (intros; apply GlobalTheory.ShFam.EigFrame.exists_baseChange <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBaseFieldMultipleOfNthRootComplexificationStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.ShFam GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.FrameUnif GlobalTheory.Reg
open scoped Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_base_field_multiple_of_nth_root_complexification : ∀ (K : Type) [Field K] [Algebra K ℂ] (A : Type) [CommRing A] [Algebra K A] [IsDomain (ℂ ⊗[K] A)] (n : ℕ) (w : ℂ ⊗[K] A) (C : ℂ) (u : A), 0 < n → C ≠ 0 → u ≠ 0 → w ^ n = C ⊗ₜ[K] u → ∃ (a : K) (b : A), a ≠ 0 ∧ u = a • b ^ n := by
  first | exact @GlobalTheory.KeyFourth.exists_eq_smul_pow_of_pow_eq_tmul | exact GlobalTheory.KeyFourth.exists_eq_smul_pow_of_pow_eq_tmul | (intros; apply GlobalTheory.KeyFourth.exists_eq_smul_pow_of_pow_eq_tmul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsComplexArcOfAnalyticModelOnFlowOrbitStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory GlobalTheory.ArcQ GlobalTheory.ArcCM GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.CuspFrom
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_complex_arc_of_analytic_model_on_flow_orbit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r) (Uw : UnfWit U) (k : U.Comp) (ξ' : Fin r → E) (x : Frame (U.X k).Ψ r) (B : GlobalTheory.CM.PAT H (Sp ℂ)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → letI := H.starRing; ∀ (A : AnArc (𝓞 E)) (gam : (Uw.F.Di (Uw.ik k)).La ≃ₗ[𝓞 E] A.La) (ξ : Module.Dual ℤ A.X) (DB : Datum H) (tyB : Fin A.gB → (E →+* ℂ)) (eB : DB.La ≃+ A.abelian₂) (ex : (Fin A.gB → ℂ) → (Over.mk (spMap (RingHom.id ℂ)) ⟶ B.t.G)), OnOrbit Uw k ξ' x A gam ξ → Module.finrank (𝓞 E) A.X = 1 → (∀ y y', (2 * l.M' : ℤ) ∣ A.be y y') → PrimAn H A → AbDat H A DB tyB eB → DB.p = Dw.p - 1 → DB.q = Dw.q - 1 → 1 ≤ Dw.p → 1 ≤ Dw.q → GlobalTheory.CM.IsExp B (RingHom.id ℂ) DB tyB (A.abelian₂.subtype.toAddMonoidHom.comp eB.toAddMonoidHom) ex → ∃ (aC : ArcIn Dw l (RingHom.id c.F) ℂ σ) (Λ : GtAn₀ aC) (hA : Λ.A = A), (∀ v, Λ.Lifts (aC.eta v) (cast (congrArg AnArc.La hA.symm) (gam (Uw.F.t (Uw.ik k) v)))) ∧ ∀ v, Λ.Lifts (aC.etaA v) (cast (congrArg AnArc.La hA.symm) (gam (Uw.F.t (Uw.ik k) v))) := by
  first | exact @GlobalTheory.CuspFrom.exists_arcIn_input | exact GlobalTheory.CuspFrom.exists_arcIn_input | (intros; apply GlobalTheory.CuspFrom.exists_arcIn_input <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFramedPointOverOfLieEigenspaceFrameStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.FlagBundle
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_framed_point_over_of_lie_eigenspace_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (L : Type) [Field L] (φ : c.F →+* L) (z : Sp L ⟶ Xo.XF c) (x : Sp L ⟶ Z.X) (g : EigFrame Z φ x), z ≫ pullback.snd _ _ = spMap φ → z ≫ Z.jQ ≫ genι Z = x → letI := φ.toAlgebra; ∃ y : FrPt Xo c L, GlobalTheory.AllWt.ptF y = z ∧ ∀ τ i, ∃ w : Sp (DualNumber L) ⟶ Z.oF.t.G.left, w ≫ Z.oF.t.G.hom = spMap (algebraMap L (DualNumber L)) ≫ z ∧ w ≫ Z.m0.toSABMap.φ = y.u τ i ∧ w ≫ Z.m.φ = g.v τ i := by
  first | exact @GlobalTheory.ShFam.exists_frPt_ptF_over_of_eigFrame | exact GlobalTheory.ShFam.exists_frPt_ptF_over_of_eigFrame | (intros; apply GlobalTheory.ShFam.exists_frPt_ptF_over_of_eigFrame <;> assumption)
end

