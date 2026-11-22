import Mathlib
import Formalism.LocalToGlobal.Divisibility.RowSideTie
import Formalism.LocalRingCardinality.Bundle0001
import Formalism.QuotientMetricDivisors.FinalW
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0108
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0628
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StructureSheafCohomologyPullbackCompCupId
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0439
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricPositionCharMultiplicityEqSumDegenerate
import Development.AbelianVarietyTheory.Definitions.Divisors.SplitDoublingNBlock
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0629
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanRangeInfKerLeOfBasis
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2.DIV Formalism.L2.Indef

namespace GlobalTheory

theorem perCol_base_smul_form (D : D7) (u : D.what₂.Word) (φ : D.what₂.Mu u) (c : ℂ)
    (F : D.what₂.Amb D.what₂.mu0) :
    D.what₂.perCol u D.what₂.mu0 φ (c • F) = c * D.what₂.perCol u D.what₂.mu0 φ F := by
  simp only [D.perCol_base_eq_PtilCol, PeriodMap.PtilCol, PeriodMap.Ptil, map_smul, smul_eq_mul]

theorem perCol_eq_pairing_of_kills (D : D7) (h : Formalism.BasicNotions.Rows.BuDefQ D.what₂) (u : D.what₂.Word)
    (φ : D.what₂.Mu u)
    (hK : ∀ F ∈ D.what₂.Usp D.what₂.mu0, D.what₂.perCol u D.what₂.mu0 φ F = 0)
    (F : D.what₂.Amb D.what₂.mu0) (hF : F ∈ D.what₂.V0 D.what₂.mu0) :
    D.what₂.perCol u D.what₂.mu0 φ F = D.what₂.Bu u φ (D.what₂.iota D.what₂.mu0 F) := by
  set n : D.what₂.Amb D.what₂.mu0 := (D.what₂.Usp D.what₂.mu0).starProjection F with hn
  have hnU : n ∈ D.what₂.Usp D.what₂.mu0 := Submodule.starProjection_apply_mem _ _
  have hq : F - n ∈ D.what₂.Qsp D.what₂.mu0 :=
    ⟨Submodule.sub_mem _ hF hnU.1, Submodule.sub_starProjection_mem_orthogonal F⟩
  have hι : D.what₂.iota D.what₂.mu0 F = D.what₂.iota D.what₂.mu0 (F - n) := by
    have : D.what₂.iota D.what₂.mu0 n = 0 := hnU.2
    rw [map_sub, this, sub_zero]
  have hF' : F = (F - n) + n := by abel
  rw [h u φ, hι, D.what₂.sec_iota _ _ hq]
  conv_lhs => rw [hF']
  rw [D.perCol_add, hK n hnU, add_zero]

theorem span_range_inf_ker_le_of_basis {K : Type} [Field K] (σ : K →+* ℂ) {W E A I : Type}
    [AddCommGroup W] [Module ℂ W] [AddCommGroup E] [Module ℂ E] [AddCommGroup A] [Module K A]
    [Finite I] {n : ℕ} (b : Module.Basis I K A)
    (j : (Fin n → K) →ₛₗ[σ] W) (j' : A →ₛₗ[σ] E) (f : W →ₗ[ℂ] E) (g : (Fin n → K) →ₗ[K] A)
    (hli : LinearIndependent ℂ (fun i => j' (b i))) (hf : ∀ x, f (j x) = j' (g x)) :
    Submodule.span ℂ (Set.range j) ⊓ LinearMap.ker f = Submodule.span ℂ (j '' {x | g x = 0}) := by
  classical
  obtain ⟨m, ⟨e⟩⟩ := Finite.exists_equiv_fin I
  let b' := b.reindex e
  let M := LinearMap.toMatrix' (b'.equivFun.toLinearMap ∘ₗ g)
  have hM : ∀ x, M.mulVec x = b'.equivFun (g x) := fun x => by
    rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']
    rfl
  have key := span_range_inf_ker_eq_span_rational_ker σ j
    (j'.comp b'.equivFun.symm.toLinearMap) f M ?_ ?_
  · rw [key]
    congr 2
    ext x
    simp only [Set.mem_setOf_eq, hM, EmbeddingLike.map_eq_zero_iff]
  · have h1 : (fun l => (j'.comp b'.equivFun.symm.toLinearMap) (Pi.single l 1))
        = (fun i => j' (b i)) ∘ e.symm := by
      funext l
      simp [b', Pi.single_apply]
    rw [h1]
    exact hli.comp _ e.symm.injective
  · intro x
    rw [hf, hM]
    simp

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecLocalRingHomExtOfInjectiveLocalHom
section
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem GlobalTheory.spec_local_hom_ext_of_injective (R R' : Type) [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R']
    (φ : R →+* R') (hl : IsLocalHom φ) (hi : Function.Injective φ) (Y : Scheme.{0}) (x y : Sp R ⟶ Y)
    (h : spMap φ ≫ x = spMap φ ≫ y) : x = y := by
  have hc : (spMap φ) (IsLocalRing.closedPoint R') = IsLocalRing.closedPoint R := by
    have : IsLocalHom (CommRingCat.Hom.hom (CommRingCat.ofHom φ)) := hl
    exact Spec_closedPoint (R := CommRingCat.of R) (S := CommRingCat.of R') (f := CommRingCat.ofHom φ)
  have hp : x (IsLocalRing.closedPoint R) = y (IsLocalRing.closedPoint R) := by
    rw [← hc]
    change (spMap φ ≫ x) (IsLocalRing.closedPoint R') = (spMap φ ≫ y) (IsLocalRing.closedPoint R')
    rw [h]
  obtain ⟨p, hpx⟩ : ∃ p, x (IsLocalRing.closedPoint R) = p := ⟨_, rfl⟩
  have ex : ∀ z : Sp R ⟶ Y, z (IsLocalRing.closedPoint R) = p →
      ∃ a, Spec.map a ≫ Y.fromSpecStalk p = z := by
    intro z hz
    subst hz
    exact ⟨_, Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := CommRingCat.of R) z⟩
  obtain ⟨a, rfl⟩ := ex x hpx
  obtain ⟨b, rfl⟩ := ex y (hp ▸ hpx)
  have h2 : spMap φ ≫ Spec.map a = spMap φ ≫ Spec.map b := by
    rw [← Category.assoc, ← Category.assoc] at h
    exact (cancel_mono _).1 h
  have h3 : a ≫ CommRingCat.ofHom φ = b ≫ CommRingCat.ofHom φ := by
    apply Spec.map_injective
    simpa [spMap, Spec.map_comp] using h2
  have hab : a = b := by
    ext s
    apply hi
    have := congrArg (fun g => g.hom s) h3
    simpa using this
  rw [hab]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StableUnderGeneralizationSectionComponentsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stableUnderGeneralization_section_connectedComponentIn : ∀ (X S : Scheme.{0}) (f : X ⟶ S) (e : S ⟶ X), Smooth f → e ≫ f = 𝟙 _ → StableUnderGeneralization {x : X | x ∈ connectedComponentIn (f ⁻¹' {f x}) (e (f x))} := by
  first | exact @GlobalTheory.stableUnderGeneralization_sectionComponents | exact GlobalTheory.stableUnderGeneralization_sectionComponents | (intros; apply GlobalTheory.stableUnderGeneralization_sectionComponents <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrictlyHenselianLocalRingAcyclicEverySheafStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.strictlyHenselianLocalRing_acyclic_every_sheaf : GlobalTheory.EtC.B2 := by
  first | (exact @GlobalTheory.EtC.b2) | (exact GlobalTheory.EtC.b2) | (intros; apply GlobalTheory.EtC.b2  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StructureSheafCohomologyBasisBijective
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.AbCoh

theorem exists_fin_span_of_cover {X : Scheme.{0}} (T : X.affineOpens) (B : Set Γ(X, T.1))
    (hB : ∀ x ∈ T.1, ∃ f ∈ B, x ∈ X.basicOpen f) :
    ∃ (n : ℕ) (b : Fin n → Γ(X, T.1)), Ideal.span (Set.range b) = ⊤ ∧ ∀ i, b i ∈ B := by
  have hsp : Ideal.span B = ⊤ := by
    rw [← T.2.self_le_iSup_basicOpen_iff]
    intro x hx
    obtain ⟨f, hf, hxf⟩ := hB x hx
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨f, hf⟩, hxf⟩
  obtain ⟨F, hFB, hF⟩ := (Ideal.span_eq_top_iff_finite B).1 hsp
  refine ⟨F.card, fun i ↦ (F.equivFin.symm i).1, ?_, fun i ↦ hFB (F.equivFin.symm i).2⟩
  rw [eq_top_iff, ← hF]
  exact Ideal.span_mono fun x hx ↦ ⟨F.equivFin ⟨x, hx⟩, by simp⟩

theorem le_basicOpen_of_isUnit_mp {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R)
    {T S : AffOp X} (u : T ⟶ S) (f : (OAff s).obj T) (hu : IsUnit (mp (OAff s) u f)) :
    S.unop.1 ≤ X.basicOpen (show Γ(X, T.unop.1) from f) := by
  change IsUnit (X.presheaf.map (homOfLE (show S.unop.1 ≤ T.unop.1 from leOfHom u.unop)).op
    (show Γ(X, T.unop.1) from f)) at hu
  have h1 := Scheme.basicOpen_of_isUnit X hu
  rw [Scheme.basicOpen_res] at h1
  rw [← h1]; exact inf_le_right

theorem cohO_basis_bijective : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (P : Type) [Preorder P] (G : P → X.affineOpens) (hG : Monotone G), (∀ (U : X.affineOpens) (x : X), x ∈ U.1 → ∃ a, x ∈ (G a).1 ∧ (G a).1 ≤ U.1) → (∀ (a b : P) (x : X), x ∈ (G a).1 → x ∈ (G b).1 → ∃ c, c ≤ a ∧ c ≤ b ∧ x ∈ (G c).1) → Function.Bijective (CoefMap.restrict (OAff s) hG.functor.op).pull1 ∧ Function.Bijective (CoefMap.restrict (OAff s) hG.functor.op).pull2 ∧ (CohomZeroIsConstants (OAff s) → CohomZeroIsConstants (hG.functor.op ⋙ OAff s)) := by
  intro R _ X s P _ G hG h1 h2
  have H := _root_.GlobalTheory.CechDR.hasLoc_OAff s
  have hcov : ∀ T : AffOp X, ∃ (n : ℕ) (b : Fin n → (OAff s).obj T),
      Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S : AffOp X) (u : T ⟶ S),
        IsUnit (mp (OAff s) u (b i)) →
          ∃ (t : Pᵒᵖ) (v : T ⟶ hG.functor.op.obj t) (w : hG.functor.op.obj t ⟶ S), v ≫ w = u := by
    intro T
    obtain ⟨n, b, hb, hbB⟩ := exists_fin_span_of_cover T.unop
      {f | ∃ a, X.basicOpen f ≤ (G a).1 ∧ (G a).1 ≤ T.unop.1} (fun x hx ↦ by
        obtain ⟨a, hxa, haT⟩ := h1 T.unop x hx
        obtain ⟨f, hf, hxf⟩ := T.unop.2.exists_basicOpen_le (V := (G a).1) ⟨x, hxa⟩ hx
        exact ⟨f, ⟨a, hf, haT⟩, hxf⟩)
    refine ⟨n, b, hb, fun i S u hu ↦ ?_⟩
    obtain ⟨a, hfa, haT⟩ := hbB i
    have hS := le_basicOpen_of_isUnit_mp s u (b i) hu
    exact ⟨Opposite.op a, (homOfLE (show G a ≤ T.unop from haT)).op,
      (homOfLE (show S.unop ≤ G a from hS.trans hfa)).op, Quiver.Hom.unop_inj (Subsingleton.elim _ _)⟩
  have hdir : ∀ (t₁ t₂ : Pᵒᵖ) (S : AffOp X), (hG.functor.op.obj t₁ ⟶ S) → (hG.functor.op.obj t₂ ⟶ S) →
      ∃ (n : ℕ) (b : Fin n → (OAff s).obj S), Ideal.span (Set.range b) = ⊤ ∧
        ∀ (i : Fin n) (S' : AffOp X) (u : S ⟶ S'), IsUnit (mp (OAff s) u (b i)) →
          ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ Nonempty (hG.functor.op.obj t₃ ⟶ S') := by
    intro t₁ t₂ S a₁ a₂
    have hS₁ : S.unop.1 ≤ (G t₁.unop).1 := leOfHom a₁.unop
    have hS₂ : S.unop.1 ≤ (G t₂.unop).1 := leOfHom a₂.unop
    obtain ⟨n, b, hb, hbB⟩ := exists_fin_span_of_cover S.unop
      {f | ∃ c, c ≤ t₁.unop ∧ c ≤ t₂.unop ∧ X.basicOpen f ≤ (G c).1} (fun x hx ↦ by
        obtain ⟨c, hc₁, hc₂, hxc⟩ := h2 t₁.unop t₂.unop x (hS₁ hx) (hS₂ hx)
        obtain ⟨f, hf, hxf⟩ := S.unop.2.exists_basicOpen_le (V := (G c).1) ⟨x, hxc⟩ hx
        exact ⟨f, ⟨c, hc₁, hc₂, hf⟩, hxf⟩)
    refine ⟨n, b, hb, fun i S' u hu ↦ ?_⟩
    obtain ⟨c, hc₁, hc₂, hfc⟩ := hbB i
    have hS := le_basicOpen_of_isUnit_mp s u (b i) hu
    exact ⟨Opposite.op c, ⟨(homOfLE hc₁).op⟩, ⟨(homOfLE hc₂).op⟩,
      ⟨(homOfLE (show S'.unop ≤ G c from hS.trans hfc)).op⟩⟩
  have hs := _root_.GlobalTheory.sep_of_factoring_cover (OAff s) hG.functor.op H hcov
  have hg := _root_.GlobalTheory.CatCoh.Desc.glue_comma_of_basis (OAff s) hG.functor.op H hcov hdir
  have hv := _root_.GlobalTheory.CatCoh.Desc.Basis.oneCocycle_vanishing_comma_of_basis (OAff s) hG.functor.op H hcov hdir
  have hv2 := GlobalTheory.T.twoCocycle_coboundary_of_basisFunctor (OAff s) hG.functor.op H hcov hdir
  refine ⟨⟨_root_.GlobalTheory.CatCoh.CoefMap.restrict_pull1_injective_of_sep_glue _ _ hs hg,
      _root_.GlobalTheory.CatCoh.pull1_restrict_surjective_of_comma _ _ hs hg hv⟩,
    ⟨GlobalTheory.T.comma_descent_injective _ _ hs hg hv, GlobalTheory.T.comma_descent_restriction_equiv _ _ hs hg hv hv2⟩, ?_⟩
  intro h0 g hg0
  have hcomp : ∀ ⦃t t' : Pᵒᵖ⦄ (a : t ⟶ t'), g t' = mp (OAff s) (hG.functor.op.map a) (g t) := by
    intro t t' a
    have e : d0 (hG.functor.op ⋙ OAff s) g t t' a = 0 := by rw [hg0]; rfl
    rw [amitsur_d0_apply] at e
    exact sub_eq_zero.1 e
  obtain ⟨g1, hg1c, hg1e⟩ := _root_.GlobalTheory.compat_family_extend (OAff s) hG.functor.op hs hg g hcomp
  have hd : d0 (OAff s) g1 = 0 := by
    funext T T' φ
    rw [amitsur_d0_apply, hg1c φ, sub_self]
    rfl
  obtain ⟨r, hr, huniq⟩ := h0 g1 hd
  refine ⟨r, fun t ↦ ?_, fun r' hr' ↦ huniq r' fun T ↦ ?_⟩
  · rw [← hg1e t]; exact hr _
  · refine sub_eq_zero.1 (hs T _ fun t u ↦ ?_)
    rw [map_sub, ← hg1c u, hg1e t, hr' t, AlgHom.commutes]
    exact sub_self _

end GlobalTheory.AbCoh
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StructureSheafCohomologyPullbackCompCupIdStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.structureSheafCohomology_pullback_comp_cup_id : (∀ (R R' : Type) [CommRing R] [CommRing R'] (X X' : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (σ : R →+* R') (φ : X' ⟶ X) (h : φ ≫ s = s' ≫ spMap σ) (R'' : Type) [CommRing R''] (X'' : Scheme.{0}) (s'' : X'' ⟶ Sp R'') (τ : R' →+* R'') (ψ : X'' ⟶ X') (h' : ψ ≫ s' = s'' ≫ spMap τ) (ρ : R →+* R'') (χ : X'' ⟶ X) (h'' : χ ≫ s = s'' ≫ spMap ρ), χ = ψ ≫ φ → (∀ r, ρ r = τ (σ r)) → (∀ a, pullHO1 h' (pullHO1 h a) = pullHO1 h'' a) ∧ (∀ a, pullHO2 h' (pullHO2 h a) = pullHO2 h'' a) ∧ (∀ a, GlobalTheory.CechDR.pullForm h' (GlobalTheory.CechDR.pullForm h a) = GlobalTheory.CechDR.pullForm h'' a) ∧ (∀ a, pullHH1 h' (pullHH1 h a) = pullHH1 h'' a) ∧ ∀ a, pullHH2 h' (pullHH2 h a) = pullHH2 h'' a) ∧ (∀ (R R' : Type) [CommRing R] [CommRing R'] (X X' : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (σ : R →+* R') (φ : X' ⟶ X) (h : φ ≫ s = s' ≫ spMap σ), (∀ a b, pullHO2 h (cup _ a b) = cup _ (pullHO1 h a) (pullHO1 h b)) ∧ (∀ a b, pullHH2 h (cupHH s a b) = cupHH s' (pullHH1 h a) (pullHH1 h b)) ∧ ∀ a, toHO1 s' (pullHH1 h a) = pullHO1 h (toHO1 s a)) ∧ ∀ (R : Type) [CommRing R] (A : Over (Sp R)), (∀ a, pO1 (𝟙 A) a = a) ∧ (∀ a, structureSheafH2Pullback (𝟙 A) a = a) ∧ (∀ a, pF (𝟙 A) a = a) ∧ (∀ a, deRhamH1Pullback (𝟙 A) a = a) ∧ ∀ a, deRhamH2Pullback (𝟙 A) a = a := by
  first | exact @GlobalTheory.AbCoh.pull_comp_cup_id | exact GlobalTheory.AbCoh.pull_comp_cup_id | (intros; apply GlobalTheory.AbCoh.pull_comp_cup_id <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubstMemIntegralDifferentialSubmodule
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

set_option autoImplicit false

noncomputable section

namespace GlobalTheory

namespace Katz

theorem derivation_prod_erase {R A ι : Type} [CommRing R] [CommRing A] [Algebra R A]
    [DecidableEq ι] (D : Derivation R A A) (f : ι → A) (S : Finset ι) :
    D (∏ s ∈ S, f s) = ∑ i ∈ S, (∏ s ∈ S.erase i, f s) * D (f i) := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
    rw [Finset.prod_insert ha, Derivation.leibniz, ih, Finset.sum_insert ha, Finset.erase_insert ha,
      smul_eq_mul, smul_eq_mul, Finset.mul_sum, add_comm]
    congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    have hai : a ≠ i := by rintro rfl; exact ha hi
    rw [Finset.erase_insert_of_ne hai,
      Finset.prod_insert (fun h => ha (Finset.mem_of_mem_erase h)), mul_assoc]

theorem pderiv_prod_pow {R τ σ : Type} [CommRing R] [Fintype σ] [DecidableEq σ]
    (u : σ → MvPowerSeries τ R) (a : σ → ℕ) (j : τ) :
    pderiv R j (∏ s, u s ^ a s) =
      ∑ i, a i • ((∏ s ∈ Finset.univ.erase i, u s ^ a s) * (u i ^ (a i - 1) * pderiv R j (u i))) := by
  rw [derivation_prod_erase]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [pderiv_pow, nsmul_eq_mul, mul_assoc, mul_left_comm]

theorem subst_mem_quasiInt : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (σ τ : Type) [Finite σ] (u : σ → MvPowerSeries (τ) (Fr p k)) (f : MvPowerSeries (σ) (Fr p k)), (∀ i, constantCoeff (u i) = 0) → (∀ i, u i ∈ intBy p k τ 1) → f ∈ quasiInt p k σ → subst u f ∈ quasiInt p k τ := by
  intro p _ k _ _ _ σ τ _ u f hu0 hu hf
  classical
  have : Fintype σ := Fintype.ofFinite σ
  set φ := algebraMap (WittVector p k) (Fr p k) with hφ
  have ha : HasSubst u := hasSubst_of_constantCoeff_zero hu0
  have hlift : ∀ i, ∃ v : MvPowerSeries τ (WittVector p k), MvPowerSeries.map φ v = u i := by
    intro i
    have hui : ∀ α, ∃ w : WittVector p k, coeff α (u i) = φ (1 * w) := hu i
    let w0 : MvPowerSeries τ (WittVector p k) := fun α => (hui α).choose
    refine ⟨w0, ?_⟩
    ext α
    rw [coeff_map, (hui α).choose_spec, one_mul]
    rfl
  choose v hv using hlift
  intro γ j
  rw [coeff_subst ha]
  have hP : ∀ α : σ →₀ ℕ, (α.prod fun s e => u s ^ e) =
      MvPowerSeries.map φ (∏ s, v s ^ α s) := by
    intro α
    rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), map_prod]
    exact Finset.prod_congr rfl fun s _ => by rw [map_pow, hv]
  have hterm : ∀ α : σ →₀ ℕ,
      (γ j : Fr p k) * (coeff α f • coeff γ (α.prod fun s e => u s ^ e)) ∈ φ.range := by
    intro α
    rw [hP, coeff_map, smul_eq_mul]
    by_cases hγ : γ j = 0
    · rw [hγ, Nat.cast_zero, zero_mul]; exact zero_mem _
    have hle : Finsupp.single j 1 ≤ γ := by
      intro t
      by_cases ht : t = j
      · subst ht; simp only [Finsupp.single_eq_same]; omega
      · rw [Finsupp.single_apply, if_neg (Ne.symm ht)]; exact Nat.zero_le _
    set δ := γ - Finsupp.single j 1 with hδ
    have hδγ : δ + Finsupp.single j 1 = γ := tsub_add_cancel_of_le hle
    have hδj : (δ j : Fr p k) + 1 = γ j := by
      rw [← hδγ, Finsupp.add_apply, Finsupp.single_eq_same]; push_cast; rfl
    have key := coeff_pderiv (R := WittVector p k) (i := j) (∏ s, v s ^ α s) δ
    rw [hδγ, pderiv_prod_pow, map_sum] at key
    have hk : (γ j : Fr p k) * φ (coeff γ (∏ s, v s ^ α s)) =
        φ (∑ i, coeff δ (α i • ((∏ s ∈ Finset.univ.erase i, v s ^ α s) *
          (v i ^ (α i - 1) * pderiv (WittVector p k) j (v i))))) := by
      rw [key, map_mul, map_add, map_natCast, map_one, ← hδj]
      ring
    rw [mul_left_comm, hk, map_sum, Finset.mul_sum]
    refine Subring.sum_mem _ fun i _ => ?_
    obtain ⟨w, hw⟩ := (hf : ∀ (α : σ →₀ ℕ) (i : σ), ∃ w : WittVector p k,
      (α i : Fr p k) * coeff α f = φ w) α i
    rw [map_nsmul, map_nsmul, nsmul_eq_mul, ← mul_assoc, mul_comm (coeff α f), hw, ← map_mul]
    exact ⟨_, rfl⟩
  have hfin := coeff_subst_finite ha f γ
  rw [finsum_eq_sum _ hfin, Finset.mul_sum]
  have hmem : (γ j : Fr p k) * ∑ α ∈ hfin.toFinset, coeff α f • coeff γ (α.prod fun s e => u s ^ e)
      ∈ φ.range := by
    rw [Finset.mul_sum]; exact Subring.sum_mem _ fun α _ => hterm α
  rw [← Finset.mul_sum]
  obtain ⟨w, hw⟩ := hmem
  exact ⟨w, hw.symm⟩

end Katz

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveDeformationAffineSections
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AbCoh

theorem mem_map_of_smul_eq_zero_of_flat {R S : Type} [CommRing R] [CommRing S] [Algebra R S]
    [Module.Flat R S] (t : R) (J : Ideal R) (hJ : ∀ a, a ∈ J ↔ a * t = 0) (b : S) (hb : t • b = 0) :
    b ∈ J.map (algebraMap R S) := by
  let f : J →ₗ[R] R := J.subtype
  let g : R →ₗ[R] R := LinearMap.mulLeft R t
  have ex : Function.Exact f g := by
    intro y
    change t * y = 0 ↔ y ∈ Set.range f
    rw [_root_.mul_comm, ← hJ]
    exact ⟨fun hy ↦ ⟨⟨y, hy⟩, rfl⟩, fun ⟨x, hx⟩ ↦ hx ▸ x.2⟩
  have ex' := Module.Flat.lTensor_exact S ex
  have h0 : g.lTensor S (b ⊗ₜ[R] (1 : R)) = 0 := by
    rw [LinearMap.lTensor_tmul]
    change b ⊗ₜ[R] (t * 1) = 0
    rw [_root_.mul_one, ← _root_.mul_one t, ← smul_eq_mul, ← TensorProduct.smul_tmul, hb,
      TensorProduct.zero_tmul]
  obtain ⟨y, hy⟩ := (ex' _).1 h0
  have key : ∀ y : S ⊗[R] J, TensorProduct.rid R S (f.lTensor S y) ∈ J.map (algebraMap R S) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul s j =>
      rw [LinearMap.lTensor_tmul, TensorProduct.rid_tmul, Algebra.smul_def]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ j.2)
    | add x z hx hz => rw [map_add, map_add]; exact add_mem hx hz
  have := key y
  rwa [hy, TensorProduct.rid_tmul, _root_.one_smul] at this

theorem mem_map_ann_iff {R S : Type} [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]
    (t : R) (J : Ideal R) (hJ : ∀ a, a ∈ J ↔ a * t = 0) (b : S) :
    b ∈ J.map (algebraMap R S) ↔ t • b = 0 := by
  refine ⟨fun hb ↦ ?_, mem_map_of_smul_eq_zero_of_flat t J hJ b⟩
  rw [Algebra.smul_def]
  induction hb using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, ha, rfl⟩ := hx
    rw [← map_mul, _root_.mul_comm, (hJ a).1 ha, map_zero]
  | zero => exact MulZeroClass.mul_zero _
  | add x y _ _ hx hy => rw [_root_.mul_add, hx, hy, _root_.add_zero]
  | smul a x _ hx => rw [smul_eq_mul, _root_.mul_left_comm, hx, MulZeroClass.mul_zero]

theorem mem_map_span_singleton_iff {R S : Type} [CommRing R] [CommRing S] [Algebra R S] (t : R) (b : S) :
    b ∈ (Ideal.span {t}).map (algebraMap R S) ↔ ∃ c : S, b = t • c := by
  rw [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton']
  constructor
  · rintro ⟨a, rfl⟩; exact ⟨a, by rw [Algebra.smul_def, _root_.mul_comm]⟩
  · rintro ⟨c, rfl⟩; exact ⟨c, by rw [Algebra.smul_def, _root_.mul_comm]⟩

end GlobalTheory.AbCoh

namespace GlobalTheory.AbCoh

theorem preα_surjective_and_ker : ∀ (R R' R₀ : Type) [CommRing R] [CommRing R'] [CommRing R₀] (t : R) (σ : R →+* R') (σ₀ : R →+* R₀) (X X' X₀ : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (s₀ : X₀ ⟶ Sp R₀) (φ : X' ⟶ X) (φ₀ : X₀ ⟶ X) (h : IsPullback φ s' s (spMap σ)) (h₀ : IsPullback φ₀ s₀ s (spMap σ₀)) [IsAffineHom φ] [IsAffineHom φ₀], SmallExt t σ σ₀ → Flat s → ∀ U : AffOp X, Function.Surjective (preα φ s s' U) ∧ (∀ b, preα φ s s' U b = 0 ↔ ∃ c, b = t • c) ∧ Function.Surjective (preα φ₀ s s₀ U) ∧ ∀ b : (OAff s).obj U, preα φ₀ s s₀ U b = 0 ↔ t • b = 0 := by
  intro R R' R₀ _ _ _ t σ σ₀ X X' X₀ s s' s₀ φ φ₀ h h₀ _ _ hE hF U
  obtain ⟨hσ, hk, hσ₀, hk₀⟩ := hE
  have A := secPull_surjective_and_ker R R' (Ideal.span {t}) σ hσ hk X' X s' s φ h (prePair φ U.unop) rfl
  have B := secPull_surjective_and_ker R R₀ (RingHom.ker σ₀) σ₀ hσ₀ rfl X₀ X s₀ s φ₀ h₀
    (prePair φ₀ U.unop) rfl
  haveI : Flat s := hF
  have hfl : (algebraMap R (Sec s U.unop.1)).Flat := by
    change ((s.appLE ⊤ U.unop.1 le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom).Flat
    exact RingHom.Flat.comp (RingHom.Flat.of_bijective
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv))
      (Flat.flat_appLE s (isAffineOpen_top _) U.unop.2 le_top)
  haveI : Module.Flat R (Sec s U.unop.1) := hfl
  exact ⟨A.1, fun b ↦ (A.2 b).trans (mem_map_span_singleton_iff t b), B.1,
    fun b ↦ (B.2 b).trans (mem_map_ann_iff t _ (fun a ↦ RingHom.mem_ker.trans (hk₀ a)) b)⟩

end GlobalTheory.AbCoh
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmCocycleApplyFinsetSum
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory

theorem symmCocycle_swap {A B : Type} [AddCommGroup A] [AddCommGroup B] (γ : A → A → B)
    (hs : ∀ x y, γ x y = γ y x) (hc : ∀ x y z, γ y z - γ (x + y) z + γ x (y + z) - γ x y = 0)
    (a b c e : A) :
    γ (a + b) (c + e) + γ a b + γ c e = γ (a + c) (b + e) + γ a c + γ b e := by
  have h1 := hc (a + b) c e
  have h2 := hc a b c
  have h3 := hc (a + c) b e
  have h4 := hc a c b
  rw [add_right_comm a c b] at h3
  rw [add_comm c b, hs c b] at h4
  rw [← sub_eq_zero]
  calc _ = ((γ c e - γ (a + b + c) e + γ (a + b) (c + e) - γ (a + b) c)
        - (γ b c - γ (a + b) c + γ a (b + c) - γ a b))
        - ((γ b e - γ (a + b + c) e + γ (a + c) (b + e) - γ (a + c) b)
        - (γ b c - γ (a + c) b + γ a (b + c) - γ a c)) := by abel
    _ = 0 := by rw [h1, h2, h3, h4]; simp

theorem symmCocycle_sum : ∀ (A B : Type) [AddCommGroup A] [AddCommGroup B] (γ : A → A → B), (∀ x y, γ x y = γ y x) → (∀ x y z, γ y z - γ (x + y) z + γ x (y + z) - γ x y = 0) → γ 0 0 = 0 → ∀ (d : ℕ) (x y : Fin d → A), γ (∑ m, x m) (∑ m, y m) = ∑ m, γ (x m) (y m) + ((∑ m, γ (∑ j ∈ Finset.univ.filter (· < m), (x j + y j)) (x m + y m)) - (∑ m, γ (∑ j ∈ Finset.univ.filter (· < m), x j) (x m)) - ∑ m, γ (∑ j ∈ Finset.univ.filter (· < m), y j) (y m)) := by
  intro A B _ _ γ hs hc h0 d
  induction d with
  | zero => intro x y; simp [h0]
  | succ d ih =>
    intro x y
    have ih' := ih (fun j => x (Fin.castSucc j)) (fun j => y (Fin.castSucc j))
    simp only [Finset.sum_filter] at ih' ⊢
    simp only [Fin.sum_univ_castSucc, Fin.castSucc_lt_castSucc_iff, Fin.castSucc_lt_last,
      if_true, lt_irrefl, if_false, add_zero] at ih' ⊢
    have hl : ∀ i : Fin d, ¬ (Fin.last d < i.castSucc) := fun i => not_lt.mpr (Fin.castSucc_lt_last i).le
    simp only [hl, if_false, add_zero] at ih' ⊢
    have k := symmCocycle_swap γ hs hc (∑ m : Fin d, x m.castSucc) (x (Fin.last d)) (∑ m : Fin d, y m.castSucc) (y (Fin.last d))
    rw [ih'] at k
    rw [Finset.sum_add_distrib]
    rw [← sub_eq_zero] at k ⊢
    rw [← k]
    abel

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricPositionCharMultiplicityEqSumDegenerateStatement
section
open GlobalTheory.FinGL Formalism.L2.DIV Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symmetricPositionCharMultiplicity_eq_sum_degenerateWhittaker : ∀ (F : Type) [Field F] [Fintype F] (ψ : AddChar F ℂ), ψ ≠ 1 → ∀ (r : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (τ : Representation ℂ (GL (Fin r) F) V) (k : ℕ), k + 1 ≤ r → nPos ψ τ 0 k = ∑ j ∈ Finset.range (k + 1), gam (Fintype.card F) (k - j) * whCut ψ τ j := by
  first | exact @GlobalTheory.FinGL.PosOne.nPos_zero_eq_sum | exact GlobalTheory.FinGL.PosOne.nPos_zero_eq_sum | (intros; apply GlobalTheory.FinGL.PosOne.nPos_zero_eq_sum <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TiltLiftOfRingAutomorphismStatement
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tilt_lift_of_ring_automorphism : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (γ : O ≃+* O), ∃ Γ : PreTilt O p ≃+* PreTilt O p, (∀ x, (Γ x).untilt = γ x.untilt) ∧ ∀ a : Ainf p O, WittVector.fontaineTheta O p (WittVector.map (Γ : PreTilt O p →+* PreTilt O p) a) = γ (WittVector.fontaineTheta O p a) := by
  first | exact @GlobalTheory.DetInv.ringEquiv_tilt_theta | exact GlobalTheory.DetInv.ringEquiv_tilt_theta | (intros; apply GlobalTheory.DetInv.ringEquiv_tilt_theta <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedHarishChandraIsotypicPartStatement
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedHarishChandra_isotypic_part : ∀ (F : Type) [Field F] [Finite F], ∀ (t : F →+* F) (a b n : ℕ), n = a + b → ∀ (α A : GL (Fin a) F → ℂ) (β B : GL (Fin b) F → ℂ), IsChar ℂ ℂ A → IsChar ℂ ℂ B → Kills α A → Kills β B → Kills (hcTw t a b α β n) (hc a b A B n) := by
  first | (exact @GlobalTheory.Shin.HcIso.kills_hcTw) | (exact GlobalTheory.Shin.HcIso.kills_hcTw) | (intros; apply GlobalTheory.Shin.HcIso.kills_hcTw <;> assumption)
end

