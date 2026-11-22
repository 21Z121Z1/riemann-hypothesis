import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegersAlt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ToroidalBoundaryMetricData
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0579
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0576
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineStableLieEigenspaceFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GradedLineBundleExists
import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.IsLocallyConstantRankAtStalkEigenSub
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CoefficientFieldIntegersDedekindFractionField
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0013
import Formalism.LocalToGlobal.UnitaryNorms.Bundle0006
import Formalism.LocalRingCardinality.Bundle0004
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0032
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0036
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0041
import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2153
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1010
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0578
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0586
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0568

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineEigenframeFlag
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)

namespace GlobalTheory.ShFam.Spread

open GlobalTheory.LieLocFrame (res res_sum res_res)
open GlobalTheory.LieMet (tan_ext)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (spMap_comp_spMap)
open scoped CategoryTheory.MonObj

attribute [local instance] Over.cartesianMonoidalCategory

theorem exists_affine_germs {X : Scheme.{0}} (y : X) {W : X.Opens} (hW : y ∈ W) {κ : Type} [Finite κ]
    (a : κ → X.presheaf.stalk y) : ∃ (U : X.Opens) (_ : IsAffineOpen U) (hy : y ∈ U) (s : κ → Γ(X, U)), U ≤ W ∧
      ∀ i, X.presheaf.germ U y hy (s i) = a i := by
  choose V hV s hs using fun i => X.presheaf.exists_germ_eq (a i)
  have ho : IsOpen ((W : Set X) ∩ ⋂ i, (V i : Set X)) :=
    W.isOpen.inter (isOpen_iInter_of_finite fun i => (V i).isOpen)
  obtain ⟨U, hU, hy, hle⟩ := exists_isAffineOpen_mem_and_subset (X := X) (U := ⟨_, ho⟩) (x := y)
    ⟨hW, Set.mem_iInter.2 hV⟩
  have hl : ∀ i, U ≤ V i := fun i z hz => Set.mem_iInter.1 (hle hz).2 i
  exact ⟨U, hU, hy, fun i => X.presheaf.map (homOfLE (hl i)).op (s i), fun z hz => (hle hz).1,
    fun i => (X.presheaf.germ_res_apply (homOfLE (hl i)) y hy (s i)).trans (hs i)⟩

theorem spMap_germ {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) {y : X} (hy : y ∈ U) :
    spMap (X.presheaf.germ U y hy).hom ≫ (show Sp Γ(X, U) ⟶ X from hU.fromSpec) =
      (show Sp (X.presheaf.stalk y) ⟶ X from X.fromSpecStalk y) :=
  hU.fromSpecStalk_eq_fromSpecStalk hy

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
  {R S T : Type} [CommRing R] [CommRing S] [CommRing T]

theorem exists_bc {φ : c.F →+* R} {x : Sp R ⟶ Z.X} (f : EigFrame Z φ x) (ψ : R →+* S) {φ' : c.F →+* S}
    {x' : Sp S ⟶ Z.X} (hφ : ψ.comp φ = φ') (hx : spMap ψ ≫ x = x') :
    ∃ g : EigFrame Z φ' x', ∀ τ i, g.vec τ i = res ψ hx (f.vec τ i) := by
  subst hφ hx
  obtain ⟨g, hg⟩ := GlobalTheory.ShFam.EigFrame.exists_baseChange E H Dw l Xo c O β Z R S φ x f ψ
  exact ⟨g, fun τ i => tan_ext (hg τ i)⟩

theorem exists_coord {φ : c.F →+* R} {x : Sp R ⟶ Z.X} (f g : EigFrame Z φ x) (τ : E →+* ℂ) :
    ∃ A B : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) R, B * A = 1 ∧ ∀ i, g.vec τ i = ∑ k, A i k • f.vec τ k := by
  choose A hA _ using fun i => f.existsUnique_sum τ (g.vec τ i) (g.act_vec τ i)
  choose B hB _ using fun i => g.existsUnique_sum τ (f.vec τ i) (f.act_vec τ i)
  refine ⟨Matrix.of A, Matrix.of B, Matrix.ext fun i => congrFun ?_, hA⟩
  refine (f.existsUnique_sum τ (f.vec τ i) (f.act_vec τ i)).unique ?_ ?_
  · refine (hB i).trans ?_
    simp only [show ∀ i, g.vec τ i = ∑ k, A i k • f.vec τ k from hA, Finset.smul_sum, smul_smul, Matrix.mul_apply, Matrix.of_apply, Finset.sum_smul]
    exact Finset.sum_comm
  · simp only [Matrix.one_apply, ite_smul, one_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true,
      zero_smul R]

theorem exists_change {φ : c.F →+* R} {x : Sp R ⟶ Z.X} (f : EigFrame Z φ x)
    (A B : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) R) (h : ∀ τ, B τ * A τ = 1) :
    ∃ g : EigFrame Z φ x, ∀ τ i, g.vec τ i = ∑ k, A τ i k • f.vec τ k := by
  have hs : ∀ τ (a : Fin (Dw.mult τ) → R), ∑ i, a i • ∑ k, A τ i k • f.vec τ k =
      ∑ k, (Matrix.vecMul a (A τ)) k • f.vec τ k := fun τ a => by
    simp only [Finset.smul_sum, smul_smul, Matrix.vecMul, dotProduct, Finset.sum_smul]
    exact Finset.sum_comm
  refine ⟨EigFrame.ofVec (fun τ i => ∑ k, A τ i k • f.vec τ k) (fun τ i a => ?_) fun τ w hw => ?_,
    fun τ i => tan_ext rfl⟩
  · simp only [map_sum, map_smul, f.act_vec, Finset.smul_sum]
    exact Finset.sum_congr rfl fun k _ => smul_comm _ _ _
  · obtain ⟨a, ha, hu⟩ := f.existsUnique_sum τ w hw
    refine ⟨Matrix.vecMul a (B τ), ?_, fun b hb => ?_⟩
    · show w = _
      rw [hs, Matrix.vecMul_vecMul, h, Matrix.vecMul_one]
      exact ha
    · rw [← hu _ (hb.trans (hs τ b)), Matrix.vecMul_vecMul, mul_eq_one_comm.1 (h τ), Matrix.vecMul_one]

theorem tri_of_bc {φ : c.F →+* R} {x : Sp R ⟶ Z.X} (f : EigFrame Z φ x) (ψ : R →+* S) {φ' : c.F →+* S}
    {x' : Sp S ⟶ Z.X} (hφ : ψ.comp φ = φ') (hx : spMap ψ ≫ x = x') (g : EigFrame Z φ' x')
    (hg : ∀ τ i, g.vec τ i = res ψ hx (f.vec τ i)) (χ : S →+* T) {ω : R →+* T} (hω : χ.comp ψ = ω)
    {φ'' : c.F →+* T} {x'' : Sp T ⟶ Z.X} {k : EigFrame Z φ'' x''} {t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Tˣ}
    (h : g.Tri χ k t) : f.Tri ω k t := by
  subst hφ hx hω
  refine ⟨by rw [h.1, ← Category.assoc, spMap_comp_spMap], h.2.1, fun τ i => ?_⟩
  have e : (fun j => spMap (dualMap (χ.comp ψ)) ≫ f.v τ j) = fun j => spMap (dualMap χ) ≫ g.v τ j := funext fun j => by
    have e₁ : g.v τ j = spMap (dualMap ψ) ≫ f.v τ j := congrArg (fun v => (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv v).left) (hg τ j)
    rw [e₁, ← Category.assoc, spMap_comp_spMap]
    congr 2
    exact RingHom.ext fun a => by ext <;> simp [dualMap]
  rw [e]
  exact h.2.2 τ i

theorem exists_frame_nhds : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (C : FlagCpt Z e) (y : C.Y.X) (V : C.Y.X.Opens), y ∈ V → ∃ (U : C.Y.X.Opens) (hU : IsAffineOpen U) (hy : y ∈ U) (φ : c.F →+* Γ(C.Y.X, U)) (fr : EigFrame Z φ (((show Sp Γ(C.Y.X, U) ⟶ C.Y.X from hU.fromSpec) ≫ C.π) ≫ genι Z)) (t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → C.Y.Fnˣ), U ≤ V ∧ ((show Sp Γ(C.Y.X, U) ⟶ C.Y.X from hU.fromSpec) ≫ C.π) ≫ genStr Z = spMap φ ∧ fr.Tri (fnOf U (gen_mem hy)) C.f0 t ∧ ∀ y' ∈ U, ∀ τ i, (C.gr τ i).IsEqn y' (t τ i) := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ e C y V hV
  obtain ⟨φ₁, f, t, hT, ht⟩ := C.gr_spec y
  obtain ⟨U₀, hU₀, φ₀, f₀, hy₀, hs₀, -⟩ := GlobalTheory.ShFam.EigSpread.exists_stable_eigFrame E H Dw l Xo c O β Z (C.π y)
  let j := algebraMap (C.Y.X.presheaf.stalk y) C.Y.X.functionField
  let gm₀ : Γ(gen Z, U₀) →+* C.Y.X.presheaf.stalk y :=
    (C.Y.X.presheaf.germ (C.π ⁻¹ᵁ U₀) y hy₀).hom.comp (C.π.app U₀).hom
  have hgm : ∀ (U : C.Y.X.Opens) (hy : y ∈ U) (h : U ≤ C.π ⁻¹ᵁ U₀),
      (C.Y.X.presheaf.germ U y hy).hom.comp (C.π.appLE U₀ U h).hom = gm₀ := fun U hy h =>
    RingHom.ext fun a => C.Y.X.presheaf.germ_res_apply (homOfLE h) y hy _
  have hρ : ∀ (U : C.Y.X.Opens) (hU : IsAffineOpen U) (h : U ≤ C.π ⁻¹ᵁ U₀),
      spMap (C.π.appLE U₀ U h).hom ≫ (show Sp Γ(gen Z, U₀) ⟶ gen Z from hU₀.fromSpec) =
        (show Sp Γ(C.Y.X, U) ⟶ C.Y.X from hU.fromSpec) ≫ C.π := fun U hU h =>
    IsAffineOpen.SpecMap_appLE_fromSpec C.π hU₀ hU h
  have hx₀ : spMap gm₀ ≫ (show Sp Γ(gen Z, U₀) ⟶ gen Z from hU₀.fromSpec) = stalkPt C.Y y ≫ C.π := by
    obtain ⟨U, hU, hy, h⟩ := exists_isAffineOpen_mem_and_subset (X := C.Y.X) (U := C.π ⁻¹ᵁ U₀) (x := y) hy₀
    rw [← hgm U hy h, ← spMap_comp_spMap, Category.assoc, hρ U hU h, ← Category.assoc, spMap_germ]
    rfl
  have hs₀' : (show Sp Γ(gen Z, U₀) ⟶ gen Z from hU₀.fromSpec) ≫ genStr Z = spMap φ₀ := hs₀
  have hφ₀ : gm₀.comp φ₀ = φ₁ := by
    letI := (constF e C.Y).toAlgebra
    have hgen : spMap j ≫ stalkPt C.Y y = genericPt C.Y :=
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk ((genericPoint_spec C.Y.X).specializes trivial)
    have h1 : spMap (j.comp (gm₀.comp φ₀)) = spMap (constF e C.Y) := by
      rw [← spMap_comp_spMap, ← spMap_comp_spMap, ← hs₀', ← Category.assoc (spMap gm₀), hx₀, ← Category.assoc,
        ← Category.assoc, hgen]
      exact (congrArg (· ≫ genStr Z) C.y0_x.symm).trans ((Category.assoc _ _ _).trans
        ((congrArg (_ ≫ ·) Z.jQ_over).trans (ptF_snd C.y0)))
    have h2 : j.comp (gm₀.comp φ₀) = constF e C.Y := congrArg CommRingCat.Hom.hom (Spec.map_injective h1)
    exact RingHom.ext fun r => IsFractionRing.injective (C.Y.X.presheaf.stalk y) C.Y.X.functionField
      ((RingHom.congr_fun h2 r).trans (RingHom.congr_fun hT.2.1 r))
  have hx₁ : spMap gm₀ ≫ (show Sp Γ(gen Z, U₀) ⟶ gen Z from hU₀.fromSpec) ≫ genι Z =
      stalkPt C.Y y ≫ C.π ≫ genι Z := by rw [← Category.assoc, hx₀, Category.assoc]
  obtain ⟨g, hg⟩ := exists_bc f₀ gm₀ hφ₀ hx₁
  choose A B hAB hA using exists_coord g f
  choose N hN hN' using fun p : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) => (ht p.1 p.2).exists_nhds
  have ho : IsOpen ((V ⊓ C.π ⁻¹ᵁ U₀ : C.Y.X.Opens) ∩ ⋂ p, (N p : Set C.Y.X)) :=
    (V ⊓ C.π ⁻¹ᵁ U₀).isOpen.inter (isOpen_iInter_of_finite fun p => (N p).isOpen)
  obtain ⟨U, hU, hy, s, hle, hs⟩ := exists_affine_germs y (W := ⟨_, ho⟩) ⟨⟨hV, hy₀⟩, Set.mem_iInter.2 hN⟩
    (fun p : Bool × (Σ τ : E →+* ℂ, Fin (Dw.mult τ) × Fin (Dw.mult τ)) =>
      (cond p.1 (A p.2.1) (B p.2.1)) p.2.2.1 p.2.2.2)
  have h₀ : U ≤ C.π ⁻¹ᵁ U₀ := fun z hz => (hle hz).1.2
  let gm : Γ(C.Y.X, U) →+* C.Y.X.presheaf.stalk y := (C.Y.X.presheaf.germ U y hy).hom
  let ρ : Γ(gen Z, U₀) →+* Γ(C.Y.X, U) := (C.π.appLE U₀ U h₀).hom
  let A' : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) Γ(C.Y.X, U) :=
    fun τ => Matrix.of fun i k => s (true, ⟨τ, i, k⟩)
  let B' : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) Γ(C.Y.X, U) :=
    fun τ => Matrix.of fun i k => s (false, ⟨τ, i, k⟩)
  have hA' : ∀ τ i k, gm (A' τ i k) = A τ i k := fun τ i k => hs (true, ⟨τ, i, k⟩)
  have hB' : ∀ τ i k, gm (B' τ i k) = B τ i k := fun τ i k => hs (false, ⟨τ, i, k⟩)
  have hAB' : ∀ τ, B' τ * A' τ = 1 := fun τ => Matrix.ext fun i k => germ_injective_of_isIntegral C.Y.X y hy (by
    show gm _ = gm _
    have := congrFun (congrFun (hAB τ) i) k
    simp only [Matrix.mul_apply, map_sum, map_mul, hA', hB', Matrix.one_apply] at this ⊢
    rw [this]
    split_ifs <;> simp)
  have hx₂ : spMap ρ ≫ (show Sp Γ(gen Z, U₀) ⟶ gen Z from hU₀.fromSpec) ≫ genι Z =
      ((show Sp Γ(C.Y.X, U) ⟶ C.Y.X from hU.fromSpec) ≫ C.π) ≫ genι Z := by rw [← Category.assoc, hρ U hU h₀]
  have hx₃ : spMap gm ≫ ((show Sp Γ(C.Y.X, U) ⟶ C.Y.X from hU.fromSpec) ≫ C.π) ≫ genι Z =
      stalkPt C.Y y ≫ C.π ≫ genι Z := by
    rw [Category.assoc, ← Category.assoc, spMap_germ]
    rfl
  obtain ⟨g', hg'⟩ := exists_bc f₀ ρ rfl hx₂
  obtain ⟨fr, hfr⟩ := exists_change g' A' B' hAB'
  refine ⟨U, hU, hy, ρ.comp φ₀, fr, t, fun z hz => (hle hz).1.1, ?_, ?_,
    fun y' hy' τ i => hN' ⟨τ, i⟩ y' (Set.mem_iInter.1 (hle hy').2 ⟨τ, i⟩)⟩
  · rw [← hρ U hU h₀, Category.assoc, hs₀']
    exact spMap_comp_spMap φ₀ ρ
  · refine tri_of_bc fr gm (by rw [← RingHom.comp_assoc, hgm U hy h₀, hφ₀]) hx₃ f (fun τ i => ?_) j
      (RingHom.ext fun a => algebraMap_germ hy a) hT
    rw [hfr, res_sum, hA]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hA', hg, hg', res_res ρ hx₂ gm hx₃ (hgm U hy h₀) hx₁]

end GlobalTheory.ShFam.Spread
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBasisOfIntFrame
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj GlobalTheory.LieMet GlobalTheory.LocM
open GlobalTheory.GradedPieces GlobalTheory.Points

namespace GlobalTheory.TotalFrame

attribute [local instance] Over.cartesianMonoidalCategory

theorem exists_basis_sigma {O S M J : Type} [CommRing O] [CommRing S] [AddCommGroup M] [Module S M] [Fintype J]
    {χ : J → O →+* S} (h : EigenSplit.IsSplitting χ) (ρ : O →+* Module.End S M) {m : J → ℕ}
    (u : ∀ σ, Fin (m σ) → M) (li : ∀ σ, LinearIndependent S (u σ))
    (hs : ∀ σ, Submodule.span S (Set.range (u σ)) = EigenSplit.eigenSub ρ (χ σ)) :
    ∃ b : Module.Basis (Σ σ, Fin (m σ)) S M, ∀ σ a, b ⟨σ, a⟩ = u σ a := by
  classical
  have hi := EigenSplit.isInternal_eigenSub h ρ
  simp only [← hs] at hi
  exact ⟨hi.collectedBasis fun σ => Module.Basis.span (li σ), fun σ a => by
    rw [DirectSum.IsInternal.collectedBasis_coe]
    exact congrArg Subtype.val (Module.Basis.span_apply (li σ) a)⟩

section Tangent

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} {t : SAB H X}
  {S T : Type} [CommRing S] [CommRing T] {x : Sp S ⟶ X} {m : ℕ}

theorem exists_basis {v : Fin m → (Sp (DualNumber S) ⟶ t.G.left)} (hv : ∀ i, IsTanAtG t x (v i))
    (hb : ∀ w, IsTanAtG t x w → ∃! cf, IsCombAtG t x v cf w) :
    ∃ b : Module.Basis (Fin m) S (TanM x t.G), ∀ i, b i = tanOf (hv i) := by
  refine ⟨Module.Basis.mk (v := fun i => tanOf (hv i)) (Fintype.linearIndependent_iffₛ.2 fun c c' h => congrFun
    ((hb _ (isTan_tv (∑ i, c i • tanOf (hv i)))).unique ((isComb_iff (fun i => tanOf (hv i)) c _).2 rfl)
      ((isComb_iff (fun i => tanOf (hv i)) c' _).2 h))) fun w _ => ?_, fun i => Module.Basis.mk_apply _ _ i⟩
  obtain ⟨a, ha, -⟩ := hb _ (isTan_tv w)
  rw [(isComb_iff (fun i => tanOf (hv i)) a w).1 ha]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem exists_basis_map {J : Type} [Fintype J] (b : Module.Basis J S (TanM x t.G)) (φ : S →+* T) {x' : Sp T ⟶ X}
    (hx : spMap φ ≫ x = x') :
    ∃ b' : Module.Basis J T (TanM x' t.G), ∀ i, (tv (b' i)).left = spMap (dualMap φ) ≫ (tv (b i)).left := by
  let e := Fintype.equivFin J
  have hb : ∀ w, IsTanAtG t x w → ∃! cf, IsCombAtG t x (fun i => (tv (b.reindex e i)).left) cf w := fun w hw =>
    ⟨(b.reindex e).repr (tanOf hw), (isComb_iff _ _ (tanOf hw)).2 ((b.reindex e).sum_repr _).symm, fun a ha => by
      rw [(isComb_iff _ _ (tanOf hw)).1 ha, Module.Basis.repr_sum_self]⟩
  obtain ⟨b', hb'⟩ := exists_basis (fun i => isTan_map φ hx (isTan_tv (b.reindex e i)))
    (basis_map φ hx (fun i => isTan_tv _) hb)
  refine ⟨b'.reindex e.symm, fun i => ?_⟩
  rw [Module.Basis.reindex_apply, hb', left_tanOf, Module.Basis.reindex_apply, Equiv.symm_symm, Equiv.symm_apply_apply]

theorem dualMap_epsMul (φ : S →+* T) (a : S) {Y : Scheme.{0}} (v : Sp (DualNumber S) ⟶ Y) :
    spMap (dualMap φ) ≫ spMap (epsMul a) ≫ v = spMap (epsMul (φ a)) ≫ spMap (dualMap φ) ≫ v := by
  rw [← Category.assoc, ← Category.assoc, spMap_comp_spMap, spMap_comp_spMap]
  congr 2
  refine RingHom.ext fun z => TrivSqZeroExt.ext ?_ ?_ <;> simp [dualMap, epsMul, mul_comm]

variable {Dw : Datum H} {l : Level H} {c : Coeff l} {w : Vecs Dw t S} {χ : (E →+* ℂ) → 𝓞 E →+* S}

variable (c x w χ) in

def FramesSeparate : Prop :=
  ∀ r s : S, (∀ (k : Type) [Field k] (φ : S →+* k) (f : c.F →+* k), IsFrame t f (spMap φ ≫ x) (w.bc φ) →
    (∀ σ a, f (embK c σ a) = φ (χ σ a)) → φ r = φ s) → r = s

theorem span_eq_eigenSub (hw : FramesSeparate x c w χ) (σ : E →+* ℂ) (ht : ∀ i, IsTanAtG t x (w σ i))
    {v : Fin m → (Sp (DualNumber S) ⟶ t.G.left)} (e : Fin (Dw.mult σ) ↪ Fin m) (he : ∀ i, v (e i) = w σ i)
    (hv : ∀ i, IsTanAtG t x (v i)) (hb : ∀ u, IsTanAtG t x u → ∃! cf, IsCombAtG t x v cf u) :
    Submodule.span S (Set.range fun i => tanOf (ht i)) = EigenSplit.eigenSub (actR t.act) (χ σ) := by
  classical
  refine le_antisymm (Submodule.span_le.2 ?_) fun u hu => ?_
  · rintro _ ⟨i, rfl⟩
    refine EigenSplit.mem_eigenSub.2 fun a => ?_
    obtain ⟨g, hc, -⟩ := hb _ (isTan_tv (actR t.act a (tanOf (ht i))))
    obtain ⟨g', hc', -⟩ := hb _ (isTan_tv (χ σ a • tanOf (ht i)))
    have hcc : g = g' := funext fun l => hw _ _ fun k _ φ f hf hfj => by
      have h1 := comb_map φ rfl hc
      have h2 := comb_map φ rfl hc'
      have h3 : spMap (dualMap φ) ≫ (tv (actR t.act a (tanOf (ht i)))).left =
          spMap (dualMap φ) ≫ (tv (χ σ a • tanOf (ht i))).left := by
        refine (Category.assoc _ _ _).symm.trans (((hf.1 σ i).2 a).trans ?_)
        rw [hfj]
        exact (dualMap_epsMul φ _ _).symm
      rw [h3] at h1
      exact congrFun ((basis_map φ rfl hv hb _ (isTan_map φ rfl (isTan_tv _))).unique h1 h2) l
    subst hcc
    exact ((isComb_iff (fun i => tanOf (hv i)) g _).1 hc).trans ((isComb_iff (fun i => tanOf (hv i)) g _).1 hc').symm
  · obtain ⟨g, hc, -⟩ := hb _ (isTan_tv u)
    rw [(isComb_iff (fun i => tanOf (hv i)) g _).1 hc]
    refine Submodule.sum_mem _ fun l _ => ?_
    by_cases hl : ∃ i, e i = l
    · obtain ⟨i, rfl⟩ := hl
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, tan_ext (he i).symm⟩)
    have h0 : g l = 0 := hw _ _ fun k _ φ f hf hfj => by
      have hvk := fun i => isTan_map φ rfl (hv i)
      have huk := isTan_map φ rfl (isTan_tv u)
      obtain ⟨d, hd, -⟩ := hf.2 σ _ huk fun a => by
        rw [hfj, ← dualMap_epsMul, Category.assoc]
        exact congrArg (fun q => spMap (dualMap φ) ≫ (tv q).left) (EigenSplit.mem_eigenSub.1 hu a)
      have h1 := (comb_iff hvk _ huk).1 (comb_map φ rfl hc)
      have h2 := (comb_iff (fun i => (hf.1 σ i).1) _ huk).1 hd
      have h3 : ∑ i, d i • tanOf (hf.1 σ i).1 = ∑ l, Function.extend e d 0 l • tanOf (hvk l) :=
        Fintype.sum_of_injective e e.injective _ _
          (fun l hl => by rw [Function.extend_apply' _ _ _ hl, Pi.zero_apply, zero_smul])
          (fun i => by
            rw [e.injective.extend_apply]
            exact congrArg (d i • ·) (tan_ext (congrArg (spMap (dualMap φ) ≫ ·) (he i).symm)))
      rw [map_zero, Fintype.linearIndependent_iffₛ.1 (linInd_of_basis hvk (basis_map φ rfl hv hb)) _ _
        (h1.symm.trans (h2.trans h3)) l, Function.extend_apply' _ _ _ hl, Pi.zero_apply]
    rw [h0, zero_smul]
    exact Submodule.zero_mem _

theorem exists_basis_total (hw : FramesSeparate x c w χ) (hχ : EigenSplit.IsSplitting χ)
    (h : ∀ σ, ∃ (n : ℕ) (v : Fin n → (Sp (DualNumber S) ⟶ t.G.left)) (e : Fin (Dw.mult σ) ↪ Fin n),
      (∀ i, v (e i) = w σ i) ∧ (∀ i, IsTanAtG t x (v i)) ∧ ∀ u, IsTanAtG t x u → ∃! cf, IsCombAtG t x v cf u)
    (φ : S →+* T) {x' : Sp T ⟶ X} (hx : spMap φ ≫ x = x') :
    ∃ b : Module.Basis (Σ σ : E →+* ℂ, Fin (Dw.mult σ)) T (TanM x' t.G), ∀ σ a, (tv (b ⟨σ, a⟩)).left = w.bc φ σ a := by
  choose n v e he hv hb using h
  have ht : ∀ σ i, IsTanAtG t x (w σ i) := fun σ i => he σ i ▸ hv σ (e σ i)
  have li : ∀ σ, LinearIndependent S fun i => tanOf (ht σ i) := fun σ => by
    obtain ⟨b, hb'⟩ := exists_basis (hv σ) (hb σ)
    convert b.linearIndependent.comp (e σ) (e σ).injective using 1
    exact funext fun i => Eq.trans (tan_ext (w := tanOf (hv σ (e σ i))) (he σ i).symm) (hb' (e σ i)).symm
  obtain ⟨b, hb'⟩ := exists_basis_sigma hχ _ (fun σ i => tanOf (ht σ i)) li
    fun σ => span_eq_eigenSub hw σ (ht σ) (e σ) (he σ) (hv σ) (hb σ)
  obtain ⟨b', hb''⟩ := exists_basis_map b φ hx
  exact ⟨b', fun σ a => by rw [hb'', hb']; rfl⟩

end Tangent

section Model

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

def embV {l : Level H} (c : Coeff l) (W : ValuationSubring ℂ) (σ : E →+* ℂ) : 𝓞 E →+* c.V W :=
  (embK c σ).codRestrict (c.V W) fun a =>
    GlobalTheory.CoeffRings.mem_of_isIntegral _ (map_isIntegral_int (embK c σ) (RingOfIntegers.isIntegral a))

theorem isSplitting_embV {l : Level H} (c : Coeff l) (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits)
    (hd : ¬ p ∣ (discr E).natAbs) {S : Type} [CommRing S] (j : c.V W →+* S) :
    EigenSplit.IsSplitting fun σ : E →+* ℂ => j.comp (embV c W σ) := by
  refine EigenSplit.isSplitting_of_isDomain (fun σ τ h => ?_) (NumberField.Embeddings.card E ℂ) j ?_
  · exact IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E))
      (RingHom.ext fun a => congrArg (fun f : 𝓞 E →+* c.V W => (((f a : c.V W) : c.F) : ℂ)) h)
  · have hu := (((GlobalTheory.CoeffRings.coeff_isDedFrac E H l c).2.2.2 p W hp hW).2.1 _
      (hp.coprime_iff_not_dvd.2 hd).symm).map j
    rw [map_natCast] at hu
    rcases Int.natAbs_eq (discr E) with h | h <;> rw [h]
    · rwa [Int.cast_natCast]
    · rw [Int.cast_neg, Int.cast_natCast]
      exact hu.neg

variable {Z : Mdl Y i₀} {U : Z.X.Opens} {hU : IsAffineOpen U} {w : Vecs Dw (Y Z.i).t Γ(Z.X, U)}

variable (hU) in

theorem fn_ext_affine {f g : Γ(Z.X, U)} (h : ∀ (k : Type) [Field k] (φ : Γ(Z.X, U) →+* k),
    Set.range (spMap φ ≫ hU.fromSpec) ⊆ Z.opn → φ f = φ g) : f = g :=
  fn_ext Z fun k _ x hx ho => by
    rw [valR_eq x U hx, valR_eq x U hx]
    exact h k (valMap x U hx).hom (by
      rw [show spMap (valMap x U hx).hom ≫ hU.fromSpec = x from specMap_valMap_fromSpec hU x hx]
      exact ho)

theorem frame_at (hw : IntFrame Z hU w) {j : Z.i.c.V W →+* Γ(Z.X, U)} (hj : spMap j = hU.fromSpec ≫ Z.s)
    {k : Type} [Field k] (φ : Γ(Z.X, U) →+* k) (ho : Set.range (spMap φ ≫ hU.fromSpec) ⊆ Z.opn) :
    ∃ f : Z.i.c.F →+* k, IsFrame (Y Z.i).t f (spMap φ ≫ hU.fromSpec ≫ Z.π) (w.bc φ) ∧
      ∀ σ a, f (embK Z.i.c σ a) = φ (j (embV Z.i.c W σ a)) := by
  obtain ⟨a, ψ, hx, hf, -⟩ := hw.2 k φ ho
  rw [Category.assoc] at hf
  refine ⟨_, hf, fun σ r => ?_⟩
  have e : spMap (ψ.comp ((Z.alg a).comp (Z.i.c.V W).subtype)) = spMap (φ.comp j) := by
    rw [← spMap_comp_spMap _ ψ, ← spMap_comp_spMap _ φ, hj, ← Z.alg_s a, ← Category.assoc, hx, Category.assoc]
  exact congrArg (fun q => q.hom (embV Z.i.c W σ r)) (Spec.map_injective e)

end Model

theorem exists_basis_of_intFrame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ)
    (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits → ¬ p ∣ (discr E).natAbs →
    ∀ (Y : LocalSystem Xo p W) (i₀ : Idx H p) (Z : Mdl Y i₀) (U : Z.X.Opens) (hU : IsAffineOpen U)
      (w : Vecs Dw (Y Z.i).t Γ(Z.X, U)), IntFrame Z hU w → ∀ (R : Type) [CommRing R] (φ : Γ(Z.X, U) →+* R)
      (x : Sp R ⟶ Z.X), spMap φ ≫ hU.fromSpec = x →
      ∃ b : Module.Basis (Σ σ : E →+* ℂ, Fin (Dw.mult σ)) R (TanM (x ≫ Z.π) (Y Z.i).t.G),
        ∀ σ a, (tv (b ⟨σ, a⟩)).left = w.bc φ σ a := by
  intro E _ _ _ H Dw Xo p W hp hW hd Y i₀ Z U hU w hw R _ φ x hx
  let j : Z.i.c.V W →+* Γ(Z.X, U) := (Spec.preimage (hU.fromSpec ≫ Z.s)).hom
  have hj : spMap j = hU.fromSpec ≫ Z.s := Spec.map_preimage _
  refine exists_basis_total (c := Z.i.c) (fun r s h => fn_ext_affine hU fun k _ ψ ho => ?_)
    (isSplitting_embV Z.i.c hp hW hd j) hw.1 φ (hx ▸ (Category.assoc _ _ _).symm)
  obtain ⟨f, hf, hfj⟩ := frame_at hw hj ψ ho
  exact h k ψ f hf hfj

end GlobalTheory.TotalFrame
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCoreConstantsBaseSolutionEquivariant
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RealGeo
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RealGeoConst

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

theorem phiAt_eq (T : CoreJ D) (i : Fin D.R.m) (σ : T.Q.c.F →+* ℂ) (hV : T.V ((i : ℕ) + 1) σ = Wc D i)
    (c : (T.U ((i : ℕ) + 1) σ).Comp → ℂ) (f : T.R ((i : ℕ) + 1)) :
    phiAt T i σ hV c f = adel (Wc D i) (castDict hV (T.dict ((i : ℕ) + 1) σ))
      (muPin (Wc D i) (castDict hV (T.dict ((i : ℕ) + 1) σ)) (castDict hV (T.mu ((i : ℕ) + 1) σ)) c)
      (rdU (T.U ((i : ℕ) + 1) σ) f) := by
  have key : ∀ (W : HSp D) (hV : T.V ((i : ℕ) + 1) σ = W),
      castDict hV (adel (T.V ((i : ℕ) + 1) σ) (T.dict ((i : ℕ) + 1) σ)
        (muPin (T.V ((i : ℕ) + 1) σ) (T.dict ((i : ℕ) + 1) σ) (T.mu ((i : ℕ) + 1) σ) c) (rdU (T.U ((i : ℕ) + 1) σ) f)) =
      adel W (castDict hV (T.dict ((i : ℕ) + 1) σ))
        (muPin W (castDict hV (T.dict ((i : ℕ) + 1) σ)) (castDict hV (T.mu ((i : ℕ) + 1) σ)) c)
        (rdU (T.U ((i : ℕ) + 1) σ) f) := by
    intro W hV
    subst hV
    rfl
  exact key _ hV

theorem eqAt_base (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F)
    (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec)
    (hL : R.toLevCh.Is A.μ0) (hT : TieIn T R κ v₀) (i : Fin D.R.m) (O : OMDat T.toCore R i Unit (fun _ => A.μ0))
    (cc : (T.U ((i : ℕ) + 1) T.σ₀).Comp → ℂ) (h : O.EquivAt (κ i) cc) (hV : T.V ((i : ℕ) + 1) T.σ₀ = Wc D i) :
    EqAt T R κ O T.σ₀ hV cc := by
  intro g k hk f hf
  obtain ⟨h1, h2⟩ := h g k hk f hf
  obtain ⟨y, hy⟩ := GlobalTheory.ChiDetValues.chiC_mem_coeff T R κ v₀ hL hT i g
  have hy' : D.what₂.embLL (algebraMap T.Q.c.F D.what₂.LL y) =
      ∏ PP : R.Pg, ((R.chi ((i : ℕ) + 1) PP.1 (Matrix.GeneralLinearGroup.det (R.eG g PP)) : ℂˣ) : ℂ) := by
    rw [hy, chiC, Units.coe_prod]
  refine ⟨h1, y, hy', fun x => ?_⟩
  have e : T.σ₀ y = D.what₂.embLL (algebraMap T.Q.c.F D.what₂.LL y) :=
    (RingHom.congr_fun (res_embLL T hT.alg hT.laws.pins.2.2.1) y).symm
  rw [phiAt_eq, phiAt_eq, e, hy']
  exact h2 x

set_option maxHeartbeats 1000000 in

theorem exists_constants : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (cc : ∀ i : Fin D.R.m, (T.U ((i : ℕ) + 1) T.σ₀).Comp → ℂ), R.toLevCh.Is A.μ0 → TieIn T R κ v₀ → T.pb = R.C.P.pb → (∀ i, OMPins T R κ v₀ O i) → (∀ i, (O i).OneMapOf (κ i) (v₀ i (sg0 D A)) (cc i) 1) → ∃ cE, (∀ i : Fin D.R.m, cE ((i : ℕ) + 1) T.σ₀ = cc i) ∧ TieIn (setCE T cE) R κ v₀ ∧ (∀ i, OMPins (setCE T cE) R κ v₀ O i) ∧ Fired (setCE T cE) R κ v₀ O (fun _ => 1) := by
  intro D G _ _ Pl0 T0 A T _ R κ v₀ O cc hL hT hpb hP hO
  have H : ∀ (n : ℕ) (σ : T.Q.c.F →+* ℂ), ∃ c : (T.U (n + 1) σ).Comp → ℂ, CUnit c ∧ ∀ hn : n < D.R.m,
      (σ = T.σ₀ → HEq c (cc ⟨n, hn⟩)) ∧ (GoodEmb T.Q.c σ → ∀ hV : T.V (n + 1) σ = Wc D ⟨n, hn⟩,
        EqAt T R κ (O ⟨n, hn⟩) σ hV c) := by
    intro n σ
    by_cases hn : n < D.R.m
    · by_cases hσ : σ = T.σ₀
      · subst hσ
        exact ⟨cc ⟨n, hn⟩, (hO ⟨n, hn⟩).2.1.2.2.2.1, fun _ => ⟨fun _ => HEq.rfl, fun _ hV =>
          eqAt_base T R κ v₀ hL hT ⟨n, hn⟩ (O ⟨n, hn⟩) (cc ⟨n, hn⟩) (hO ⟨n, hn⟩).1 hV⟩⟩
      · by_cases hg : GoodEmb T.Q.c σ ∧ T.V (n + 1) σ = Wc D ⟨n, hn⟩
        · obtain ⟨c, hc, hE⟩ := GlobalTheory.T.exists_equivariant_unit_constants_goodEmbedding T R κ v₀ O hL hT hpb hP ⟨n, hn⟩ σ hg.1 hg.2
          exact ⟨c, hc, fun _ => ⟨fun h => absurd h hσ, fun _ _ => hE⟩⟩
        · exact ⟨fun _ => 1, fun _ => norm_one, fun _ => ⟨fun h => absurd h hσ, fun h1 h2 => absurd ⟨h1, h2⟩ hg⟩⟩
    · exact ⟨fun _ => 1, fun _ => norm_one, fun h => absurd h hn⟩
  choose c hc hc' using H
  have h0 : ∀ i : Fin D.R.m, c i T.σ₀ = cc i := fun i => eq_of_heq ((hc' i T.σ₀ i.2).1 rfl)
  refine ⟨fun j => Nat.casesOn (motive := fun j => ∀ σ : T.Q.c.F →+* ℂ, (T.U j σ).Comp → ℂ) j (fun _ _ => 1) c, h0, ?_,
    hP, fun i => ?_, fun i σ hσ hV => (hc' i σ i.2).2 hσ hV⟩
  · refine ⟨{ toLawsM := hT.laws.toLawsM, cUnit := ?_, muVal := hT.laws.muVal, muConj := hT.laws.muConj,
              intAll := hT.laws.intAll, modelW := hT.laws.modelW, familyUniformisationBasePointOrthogonal := hT.laws.familyUniformisationBasePointOrthogonal, kfHalf := hT.laws.kfHalf,
              adPin := hT.laws.adPin }, hT.alg, hT.kap, hT.hv₀, hT.chiR, hT.x0⟩
    intro j _ σ _
    cases j with
    | zero => exact fun _ => norm_one
    | succ n => exact hc n σ
  · have h := hO i
    rw [← h0 i] at h
    exact h

end GlobalTheory.RealGeoConst
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHolomorphicArcSmoothAlgebraNonvanishingStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_holomorphic_arc_smooth_algebra_nonvanishing : ∀ (F A : Type) [Field F] [CommRing A] [IsDomain A] [Algebra F A], Algebra.Smooth F A → ∀ (ψ₀ : A →+* ℂ) (p : A), p ≠ 0 → ∃ (ψ : ℂ → (A →+* ℂ)) (r : ℝ), IsHolPts ψ r ∧ ψ 0 = ψ₀ ∧ (∀ u ∈ Metric.ball (0 : ℂ) r, (ψ u).comp (algebraMap F A) = ψ₀.comp (algebraMap F A)) ∧ ∀ u ∈ Metric.ball (0 : ℂ) r, u ≠ 0 → ψ u p ≠ 0 := by
  first | exact @GlobalTheory.HolArc.exists_holPts_ne_zero | exact GlobalTheory.HolArc.exists_holPts_ne_zero | (intros; apply GlobalTheory.HolArc.exists_holPts_ne_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntMultipleOfInteger
section
open ReciprocityTheory.ChartRestriction.G.FD NumberField GlobalTheory.UnipKill

namespace GlobalTheory

theorem algInt_dvd_nonzero_intCast : ∀ (E : Type) [Field E] [NumberField E] (u : 𝓞 E), u ≠ 0 → ∃ c : ℤ, c ≠ 0 ∧ u ∣ (c : 𝓞 E) := by
  intro E _ _ u hu
  refine ⟨Algebra.intNorm ℤ (𝓞 E) u, Algebra.intNorm_ne_zero.2 hu, ?_⟩
  have := Algebra.dvd_algebraMap_intNorm_self ℤ (𝓞 E) u
  simpa using this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntegerExponentSectionOfChartRegularStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.ShFam GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.FrameUnif GlobalTheory.Reg
open scoped Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integer_exponent_section_of_chart_regular : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (h : GenFrEx Xo c) (w : Ix Dw → ℤ) (b : ∀ Z : Comp Xo c, Om Z), (∀ C : FChart h, ((∏ i, C.t i ^ w i : (Om C.Z)ˣ) : Om C.Z) * b C.Z ∈ C.R) → ∃ f ∈ GlobalTheory.AllWt.secZ Xo c w, ∀ Z, evC h Z f = b Z := by
  first | exact @GlobalTheory.SecGlueInt.exists_secZ_of_regular | exact GlobalTheory.SecGlueInt.exists_secZ_of_regular | (intros; apply GlobalTheory.SecGlueInt.exists_secZ_of_regular <;> assumption)
end

