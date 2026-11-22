import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0004
import Formalism.LocalToGlobal.Divisibility.ProjLemmas
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0926
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0031
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Formalism.LocalToGlobal.IndefiniteReal.DatumF
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsFundamentalDomainOfHaar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1087
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1036
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0978
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1053
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1072
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0988
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1061
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1084
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1088
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalLagrangianInvariantForm
import GroundTheory.AutomorphicForms.GL2.GJMatrixAdelic

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RangeAdjointThLeSpanGood
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

namespace GlobalTheory.AdjGood

open GlobalTheory.AdjBlock

theorem range_adjoint_le_span {K V H E : Type} [Field K] [AddCommGroup V] [Module K V]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {σ : K →+* ℂ} {j : V →ₛₗ[σ] H} {ι : Type} [Fintype ι] {b : Module.Basis ι K V}
    [FiniteDimensional ℂ H] [FiniteDimensional ℂ E] (hli : LinearIndependent ℂ fun i => j (b i))
    (hsp : Submodule.span ℂ (Set.range j) = ⊤) {e : Module.End K V}
    (he : ∀ v w, inner ℂ (j (e v)) (j w) = inner ℂ (j v) (j (e w))) {Θ : H →ₗ[ℂ] E}
    (hΘ : ∀ v, Θ (j (e v)) = Θ (j v)) :
    LinearMap.range (LinearMap.adjoint Θ) ≤ Submodule.span ℂ (j '' (LinearMap.range e : Set V)) := by
  obtain ⟨U, hU⟩ := exists_cx hli hsp e
  have h1 : Θ ∘ₗ U = Θ := ext_of_span hsp fun v => by rw [LinearMap.comp_apply, hU, hΘ]
  have h2 : ∀ v y, inner ℂ (j (e v)) y = inner ℂ (j v) (U y) := fun v y => by
    have : innerₛₗ ℂ (j (e v)) = innerₛₗ ℂ (j v) ∘ₗ U := ext_of_span hsp fun w => by
      simp only [LinearMap.comp_apply, innerₛₗ_apply_apply, hU, he]
    exact LinearMap.congr_fun this y
  have h3 : LinearMap.adjoint U = U := ext_of_span hsp fun v => by
    refine ext_inner_right ℂ fun y => ?_
    rw [LinearMap.adjoint_inner_left, hU, h2]
  have h4 : LinearMap.range U ≤ Submodule.span ℂ (j '' (LinearMap.range e : Set V)) := by
    rw [LinearMap.range_eq_map, ← hsp, Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨v, rfl⟩, rfl⟩
    rw [hU]
    exact Submodule.subset_span ⟨e v, ⟨v, rfl⟩, rfl⟩
  refine le_trans ?_ h4
  rw [← h1, LinearMap.adjoint_comp, h3]
  exact LinearMap.range_comp_le_range _ _

theorem model_good_span {G Γ W K : Type} [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    [Field K] [NumberField K] [StarRing K] {ι : Γ →* G} {S : CSD K} {σ : K →+* ℂ} {ρ : Γ →* Module.End ℂ W}
    {J : Subgroup G} {χ : J →* ℂˣ} (P : Bridge.ClassPres ι S σ ρ J χ) (M : HMod (G → W))
    (hM : M.Is (Bridge.AdForms ι ρ J χ) (Bridge.adInner ι J P.y)) {j : S.Forms →ₛₗ[σ] M.H}
    (hj : ∀ x, M.e (j x) = P.extL x)
    {G0 E : Type} [Group G0] [Fintype G0] [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] {r : Representation K G0 S.Forms} (hr : S.ActGood r) {X : Finset (G0 → K)}
    (hX : ∀ c ∈ X, IsAbsIrrChar c) {Θ : M.H →ₗ[ℂ] E} (gE : Representation ℂ G0 E)
    (hΘ : ∀ g v, Θ (j (r g v)) = gE g (Θ (j v)))
    (he : ∀ y, ∑ g, σ ((idemOf X).coeff g) • gE g (Θ y) = Θ y) :
    LinearMap.range (LinearMap.adjoint Θ) ≤
      Submodule.span ℂ (j '' (LinearMap.range (S.gaOp r (goodAt X (⊥ : Subgroup G0) 1)) : Set S.Forms)) := by
  obtain ⟨h1, h2, h3⟩ := model_form P M hM hj
  rw [goodAt, level_idempotent_bot, mul_one]
  refine range_adjoint_le_span h1 h2 (sum_selfAdj r _ (fun g => ?_) fun g v w => ?_) fun v => ?_
  · simp only [coeff_idemOf, map_sum, map_mul, map_div₀, map_natCast, inv_inv]
    refine Finset.sum_congr rfl fun c hc => ?_
    rw [← (hX c hc).map_inv σ, ← (hX c hc).map_inv σ, inv_one, inv_inv]
  · rw [h3, h3, hr.unitary]
  · rw [← he (j v)]
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smulₛₗ, hΘ, RingHom.id_apply]

theorem proj_rows_core {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A}
    (hC : Core R F) (y : R.HE.H) : ∑ g, D.what₂.embLL ((idemOf A.X).coeff g) • R.gE g y = y := by
  refine hC.models.HE.1 ?_
  have h1 : R.HE.e y ∈ R.EEat R.triv := by
    rw [← hC.models.HE.2.1]
    exact LinearMap.mem_range_self _ y
  have h2 : postOn (R.MY 0) R.e0 (R.HE.e y) - R.HE.e y = 0 := h1.2
  refine Eq.trans ?_ ((postOn_gaL (R.MY 0) (R.βY 0) (R.dat0 R.triv) R.eG _ _).symm.trans (sub_eq_zero.1 h2))
  rw [map_sum]
  exact Finset.sum_congr rfl fun g _ => by rw [map_smul, hC.models.gE]; rfl

theorem range_adjoint_Th_le_span_good : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) {s : ℕ}, A.fam.Ok s → Core R F → (∀ t g (v : (A.MtildeCSD t).Forms), R.Th t (R.jX t (A.leftGroupActionRight t g v)) = R.gE g (R.Th t (R.jX t v))) → ∀ t, LinearMap.range (LinearMap.adjoint (R.Th t)) ≤ Submodule.span ℂ (R.jX t '' ((A.fam.R t).goodF A.X : Set (A.fam.R t).S.Forms)) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F s hOk hC hG t
  exact model_good_span (W := R.cX.W) (ι := Bridge.ratF D.sp.X') (ρ := R.cX.coef.ρ) (J := (levEnv _ R.βX (R.datXt t)).J)
    (χ := (levEnv _ R.βX (R.datXt t)).χ) (R.B.R t).pres (R.HX t) (hC.models.HX t) (hC.models.jX t) (hOk.what₂ t).act hOk.irr
    R.gE (hG t) fun y => proj_rows_core hC _

end GlobalTheory.AdjGood

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueDegreeOfIsOpenImmersion
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.QCoh (IsFiniteQC)
open GlobalTheory.VB GlobalTheory.IndefiniteRowSideFullHecke

namespace GlobalTheory.CurveDegreesCompare

set_option autoImplicit false in
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits in

theorem _root_.GlobalTheory.CurveDegreesCompare.residueDegree_comp {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
    (f ≫ g).residueDegree x = g.residueDegree (f x) * f.residueDegree x := by
  letI := (g.residueFieldMap (f x)).hom.toAlgebra
  letI := (f.residueFieldMap x).hom.toAlgebra
  letI : Algebra (Z.residueField (g (f x))) (X.residueField x) :=
    ((f ≫ g).residueFieldMap x).hom.toAlgebra
  haveI : IsScalarTower (Z.residueField (g (f x))) (Y.residueField (f x))
      (X.residueField x) := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    change ((f ≫ g).residueFieldMap x).hom = _
    rw [Scheme.residueFieldMap_comp]
    rfl
  change Module.finrank (Z.residueField (g (f x))) (X.residueField x) =
    Module.finrank (Z.residueField (g (f x))) (Y.residueField (f x)) *
      Module.finrank (Y.residueField (f x)) (X.residueField x)
  exact (Module.finrank_mul_finrank _ _ _).symm

set_option autoImplicit false in
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits in

theorem _root_.GlobalTheory.CurveDegreesCompare.residueDegree_of_isOpenImmersion {X Y : Scheme.{0}} (f : X ⟶ Y)
    [IsOpenImmersion f] (x : X) : f.residueDegree x = 1 := by
  letI := (f.residueFieldMap x).hom.toAlgebra
  have hbij : Function.Bijective (algebraMap (Y.residueField (f x)) (X.residueField x)) :=
    ConcreteCategory.bijective_of_isIso (f.residueFieldMap x)
  let e : Y.residueField (f x) ≃ₗ[Y.residueField (f x)] X.residueField x :=
    (AlgEquiv.ofBijective (Algebra.ofId _ _) hbij).toLinearEquiv
  change Module.finrank (Y.residueField (f x)) (X.residueField x) = 1
  rw [← e.finrank_eq, Module.finrank_self]

theorem isFractionRing_residueField (X : Scheme.{0}) [IsIntegral X] [IsAffine X] {x : X}
    (hx : x = genericPoint X) :
    letI := (X.Γevaluation x).hom.toAlgebra
    IsFractionRing Γ(X, ⊤) (X.residueField x) := by
  subst hx
  letI := (X.Γevaluation (genericPoint X)).hom.toAlgebra
  haveI : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, trivial⟩⟩
  have := functionField_isFractionRing_of_isAffineOpen X ⊤ (isAffineOpen_top X)
  let φ : X.functionField →+* X.residueField (genericPoint X) := (X.residue _).hom
  let e : X.functionField ≃ₐ[Γ(X, ⊤)] X.residueField (genericPoint X) :=
    { RingEquiv.ofBijective φ ⟨φ.injective, X.residue_surjective _⟩ with
      commutes' := fun _ => rfl }
  exact IsLocalization.isLocalization_of_algEquiv _ e

theorem finrank_appTop_eq {P T : Scheme.{0}} [IsIntegral P] [IsIntegral T] [IsAffine P]
    [IsAffine T] (g : P ⟶ T) (hg : g (genericPoint P) = genericPoint T) :
    g.appTop.hom.finrank (T.isoSpec.hom (genericPoint T)) = g.residueDegree (genericPoint P) := by
  rw [genericPoint_eq_of_isOpenImmersion, genericPoint_eq_bot_of_affine]
  letI := g.appTop.hom.toAlgebra
  letI := (g.residueFieldMap (genericPoint P)).hom.toAlgebra
  letI := (T.Γevaluation (g (genericPoint P))).hom.toAlgebra
  letI := (P.Γevaluation (genericPoint P)).hom.toAlgebra
  haveI := isFractionRing_residueField T hg
  haveI := isFractionRing_residueField P rfl
  letI : Algebra Γ(T, ⊤) (P.residueField (genericPoint P)) :=
    (g.appTop ≫ P.Γevaluation (genericPoint P)).hom.toAlgebra
  haveI : IsScalarTower Γ(T, ⊤) Γ(P, ⊤) (P.residueField (genericPoint P)) :=
    IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower Γ(T, ⊤) (T.residueField (g (genericPoint P)))
      (P.residueField (genericPoint P)) :=
    IsScalarTower.of_algebraMap_eq' congr($(Scheme.Γevaluation_naturality g _).hom).symm
  have h : (⊥ : PrimeSpectrum Γ(T, ⊤)).asIdeal.primeCompl ≤ nonZeroDivisors Γ(T, ⊤) := fun x hx =>
    mem_nonZeroDivisors_of_ne_zero fun h0 => hx (h0 ▸ Ideal.zero_mem _)
  refine Eq.trans ?_ (IsFractionRing.finrank_eq Γ(T, ⊤) _ Γ(P, ⊤) _).symm
  change Module.rankAtStalk (R := Γ(T, ⊤)) Γ(P, ⊤) ⊥ = _
  rw [Module.rankAtStalk, IsLocalization.finrank_eq _ _ h]
  exact IsLocalizedModule.finrank_eq _ (LocalizedModule.mkLinearMap _ _) h

theorem finrank_genericPoint {C' C : Scheme.{0}} [IsIntegral C'] [IsIntegral C] (π : C' ⟶ C)
    [IsAffineHom π] (h : π (genericPoint C') = genericPoint C) :
    π.finrank (genericPoint C) = π.residueDegree (genericPoint C') := by
  let ι := C.affineOpenCover.f (C.affineOpenCover.idx (genericPoint C))
  let t := (C.affineOpenCover.covers (genericPoint C)).choose
  have ht : ι t = genericPoint C := (C.affineOpenCover.covers (genericPoint C)).choose_spec
  obtain ⟨y, hy, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := π) (g := ι) _ t
    (h.trans ht.symm)
  haveI : Nonempty _ := ⟨t⟩
  haveI := isIntegral_of_isOpenImmersion ι
  haveI : Nonempty ↥(pullback π ι) := ⟨y⟩
  haveI := isIntegral_of_isOpenImmersion (pullback.fst π ι)
  haveI : IsAffine (pullback π ι) := isAffine_of_isAffineHom (pullback.snd π ι)
  have e₀ := genericPoint_eq_of_isOpenImmersion ι
  have e₁ := genericPoint_eq_of_isOpenImmersion (pullback.fst π ι)
  have e₂ : pullback.snd π ι (genericPoint _) = genericPoint _ :=
    ι.isOpenEmbedding.injective (by
      rw [← Scheme.Hom.comp_apply, ← pullback.condition, Scheme.Hom.comp_apply, e₁, h, e₀])
  have e₃ : t = genericPoint _ := ι.isOpenEmbedding.injective (ht.trans e₀.symm)
  have e₄ := residueDegree_comp (pullback.fst π ι) π (genericPoint _)
  rw [pullback.condition, residueDegree_comp, residueDegree_of_isOpenImmersion,
    residueDegree_of_isOpenImmersion (pullback.fst π ι), e₁, one_mul, mul_one] at e₄
  change (pullback.snd π ι).appTop.hom.finrank ((Scheme.isoSpec _).hom t) = _
  rw [e₃, finrank_appTop_eq _ e₂, e₄]

section Clauses

variable (k : Type) [Field k] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)] [IsIntegral C]

variable {C}

end Clauses

end GlobalTheory.CurveDegreesCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictsToQuadraticPowOfRestrictsToQuadraticSig
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.ResEtaFOfPow

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem sig_invol {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := ⟨(IsAlgClosed.lift (R := ℚ) (M := ℂ) (S := E)).toRingHom⟩
  apply τ.injective
  rw [h.2.2.2, h.2.2.2, star_star]

theorem sig_ne {σ : E →ₐ[F] E} (h : IsCMExt F E σ) : ∃ x, σ x ≠ x := by
  by_contra hc
  push_neg at hc
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := ⟨(IsAlgClosed.lift (R := ℚ) (M := ℂ) (S := E)).toRingHom⟩
  have hr : NumberField.ComplexEmbedding.IsReal τ := by
    ext x
    simp only [NumberField.ComplexEmbedding.conjugate_coe_eq]
    have e := h.2.2.2 τ x
    rw [hc] at e
    exact e.symm
  have hc2 := h.2.1.isComplex (NumberField.InfinitePlace.mk τ)
  exact (NumberField.InfinitePlace.isComplex_mk_iff.1 hc2) hr

variable (F E) in

abbrev normI : (AF F ⊗[F] E)ˣ →* (AF F)ˣ := Units.map (Algebra.norm (AF F) : AF F ⊗[F] E →* AF F)

variable (F E) in

abbrev normGrp : Subgroup (AF F)ˣ :=
  (Units.map (algebraMap F (AF F)).toMonoidHom).range ⊔ (normI F E).range

theorem algebraMap_inj : Function.Injective (algebraMap (AF F) (AF F ⊗[F] E)) :=
  Algebra.TensorProduct.includeLeft_injective (S := F) (algebraMap F E).injective

theorem exists_form {σ : E →ₐ[F] E} (h : IsCMExt F E σ) : ∃ δ : F, ¬ IsSquare δ ∧
    ∀ a : (AF F)ˣ, a ∈ (normI F E).range ↔
      ∃ x y : AF F, (a : AF F) = x ^ 2 - algebraMap F (AF F) δ * y ^ 2 := by
  obtain ⟨δ, hδ, hh⟩ := GlobalTheory.T.quadraticExt_norm_form_over_algebra F E σ h.2.2.1 (sig_invol h) (sig_ne h)
  obtain ⟨h1, h2⟩ := hh (AF F)
  have hN : ∀ z : AF F ⊗[F] E, algebraMap (AF F) (AF F ⊗[F] E) (Algebra.norm (AF F) z) =
      z * sigR (AF F) σ z := fun z => by
    obtain ⟨x, y, e1, e2⟩ := h1 z
    rw [e1, e2]
  refine ⟨δ, hδ, fun a => ⟨?_, ?_⟩⟩
  · rintro ⟨z, rfl⟩
    obtain ⟨x, y, e1, -⟩ := h1 z
    exact ⟨x, y, e1⟩
  · rintro ⟨x, y, e⟩
    obtain ⟨z, hz⟩ := h2 x y
    rw [← e] at hz
    have hu : IsUnit z := isUnit_of_mul_isUnit_left (hz ▸ a.isUnit.map _)
    refine ⟨hu.unit, Units.ext (algebraMap_inj (F := F) (E := E) ?_)⟩
    exact (hN z).trans hz

theorem isOpen_normGrp {σ : E →ₐ[F] E} (h : IsCMExt F E σ) : IsOpen (normGrp F E : Set (AF F)ˣ) := by
  obtain ⟨δ, hδ, hf⟩ := exists_form h
  have h0 : δ ≠ 0 := fun e => hδ (e ▸ IsSquare.zero)
  refine Subgroup.isOpen_of_mem_nhds _ (Filter.mem_of_superset (GlobalTheory.T.quadraticForm_ideleValues_mem_nhds_one F δ h0) fun a ha => ?_)
  exact Subgroup.mem_sup_right ((hf a).2 ha)

theorem normGrp_ne_top {σ : E →ₐ[F] E} (h : IsCMExt F E σ) : normGrp F E ≠ ⊤ := by
  obtain ⟨δ, hδ, hf⟩ := exists_form h
  obtain ⟨a, ha⟩ := GlobalTheory.T.exists_idele_ne_algebraMap_mul_norm_of_not_isSquare F δ hδ
  intro e
  have hm : a ∈ normGrp F E := e ▸ Subgroup.mem_top a
  obtain ⟨_, ⟨t, rfl⟩, n, hn, rfl⟩ := Subgroup.mem_sup.1 hm
  obtain ⟨x, y, e⟩ := (hf n).1 hn
  exact ha t x y (by rw [Units.val_mul, e]; rfl)

theorem sq_mem_normGrp {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (a : (AF F)ˣ) : a * a ∈ normGrp F E := by
  obtain ⟨δ, -, hf⟩ := exists_form h
  exact Subgroup.mem_sup_right ((hf _).2 ⟨a, 0, by simp [pow_two]⟩)

theorem exists_isEtaF {σ : E →ₐ[F] E} (h : IsCMExt F E σ) :
    ∃ η : (AF F)ˣ →* Circle, Formalism.IndefR.DatumF.IsEtaF E η := by
  obtain ⟨a, ha⟩ : ∃ a, a ∉ normGrp F E := by
    by_contra hc
    push_neg at hc
    exact normGrp_ne_top h (eq_top_iff.2 fun a _ => hc a)
  obtain ⟨η, h1, h2⟩ := GlobalTheory.VolHeckeCompare.exists_char_of_not_mem _ (sq_mem_normGrp h) a ha
  refine ⟨η, ?_, fun b => h1 (Subgroup.mem_sup_left ⟨b, rfl⟩), fun x => h1 (Subgroup.mem_sup_right ⟨x, rfl⟩),
    fun e => h2 (by rw [e]; rfl)⟩
  refine continuous_of_continuousAt_one η ?_
  refine (continuousAt_const (y := (1 : Circle))).congr ?_
  filter_upwards [(isOpen_normGrp h).mem_nhds (one_mem _)] with b hb
  exact (h1 hb).symm

open Classical in

theorem resEtaF_of_resEtaPow : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (χ : (AF F ⊗[F] E)ˣ →* Circle) (n : ℕ),
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ n → Formalism.IndefR.DatumF.ResEtaF χ n := by
  intro F E _ _ _ _ _ σ B hB χ n hχ
  have hcm : IsCMExt F E σ := hB.cm
  refine ⟨exists_isEtaF hcm, fun η hη a => ?_⟩
  obtain ⟨-, h1, h2, h3⟩ := hη
  have hS : ∀ x ∈ normGrp F E, η x = 1 := by
    have : normGrp F E ≤ η.ker := sup_le (by rintro _ ⟨y, rfl⟩; exact h1 y) (by rintro _ ⟨y, rfl⟩; exact h2 y)
    exact fun x hx => this hx
  have hsq : ∀ x, η x * η x = 1 := fun x => by rw [← map_mul]; exact hS _ (sq_mem_normGrp hcm x)
  have key : ∀ x, ((χ (Formalism.IndefR.DatumF.idFF F E x) : Circle) : ℂ) = if x ∈ normGrp F E then 1 else (-1) ^ n :=
    fun x => hχ x
  apply Circle.ext
  rw [key a, Circle.coe_pow]
  by_cases ha : a ∈ normGrp F E
  · rw [if_pos ha, hS a ha]; simp
  rw [if_neg ha]
  rcases Nat.even_or_odd n with ⟨k, rfl⟩ | hn
  · rw [← two_mul, pow_mul, pow_mul, neg_one_sq, one_pow, ← Circle.coe_pow, sq, hsq a]; simp
  have hn1 : ((-1 : ℂ)) ^ n = -1 := hn.neg_one_pow
  obtain ⟨b, hb⟩ : ∃ b, η b ≠ 1 := by
    by_contra hh
    push_neg at hh
    exact h3 (MonoidHom.ext hh)
  have hbS : b ∉ normGrp F E := fun hm => hb (hS b hm)
  have hab : a * b ∈ normGrp F E := by
    by_contra hn2
    have e := key (a * b)
    rw [map_mul, map_mul, Circle.coe_mul, key a, key b, if_neg ha, if_neg hbS, if_neg hn2, hn1] at e
    norm_num at e
  have hηb : (η b : ℂ) = -1 := GlobalTheory.VolHeckeCompare.circle_eq_neg_one (hsq b) hb
  have e2 : (η a : ℂ) * η b = 1 := by rw [← Circle.coe_mul, ← map_mul, hS _ hab]; simp
  rw [hηb] at e2
  have hηa : (η a : ℂ) = -1 := by linear_combination -e2
  rw [hηa]

end GlobalTheory.ResEtaFOfPow
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictsToQuadraticSignPowIdelicRestrictionStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.restrictsToQuadraticSignPow_idelic_restriction : ∀ (D : D7) (χ : (AE D)ˣ →* Circle) (n : ℕ),
    GlobalTheory.WeilM.ResEtaPow (Units.map (algebraMap D.host.F (AF D.host.F)).toMonoidHom).range χ n → ResEta D χ n := by
  first | exact @GlobalTheory.ResEtaOfPow.resEta_of_resEtaPow | exact GlobalTheory.ResEtaOfPow.resEta_of_resEtaPow | (intros; apply GlobalTheory.ResEtaOfPow.resEta_of_resEtaPow <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RightDerivativeMultiplicityMapValueEq
section
open NumberField IsDedekindDomain Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolRead
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolRead.MultDer

theorem smoothVec_zero {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (L : Set (Matrix (Fin n) (Fin n) ℂ)) (π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : SmoothVec L π 0 := by
  intro k Xs _
  simp only [map_zero]
  exact contDiff_const

theorem smoothVec_of_mem {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau)
    {w : M.H τ} (hw : w ∈ M.sm τ) : SmoothVec (lieAt V τ) (M.rep τ) w := by
  induction hw using Submodule.span_induction with
  | mem x hx => exact hx
  | zero => exact smoothVec_zero _ _
  | add x y _ _ hx hy =>
    intro k Xs h
    simp only [map_add]
    exact (hx k Xs h).add (hy k Xs h)
  | smul c x _ hx =>
    intro k Xs h
    simp only [map_smul]
    exact (hx k Xs h).const_smul c

theorem rder_eq : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ) (T : MMap M), IsInfFam θ → IsMultMap θ M J χ T → ∀ (v : M.Vec) (τ : D.what₂.Tau), SmoothVec (lieAt V τ) (M.rep τ) (v τ : M.H τ) ∧ ∀ X ∈ lieAt V τ, ∃ u : M.sm τ, (u : M.H τ) = dRep (M.rep τ) X (v τ : M.H τ) ∧ Rder θ V τ X (T v) = T (Function.update v τ u) := by
  intro D θ V S M J χ T _ hT v τ
  have hs := smoothVec_of_mem M τ (v τ).2
  refine ⟨hs, fun X hX => ?_⟩
  have hH := GlobalTheory.SmoothAutCheck.gramAt_herm V τ
  have hU := GlobalTheory.SmoothAutCheck.gramAt_unit V τ
  have hπ := (GlobalTheory.HolDict.ModelRep.model_rep D V S M τ).2.1
  obtain ⟨h1, -, h3⟩ := GlobalTheory.T.smoothVectors_unitaryRep_stable_conj_skewAdjoint _ _ _ _ hH hU hπ _ hs
  refine ⟨⟨_, Submodule.subset_span (h3 X hX).1⟩, rfl, ?_⟩
  funext x
  obtain ⟨ℓ, hℓ, hℓT⟩ := hT.cont τ v x
  have hd := GlobalTheory.T.hasDerivAt_sobolevContinuous_orbit _ _ _ _ hH hU hπ _ hs ℓ hℓ X hX
  rw [← hℓT]
  have e : (fun t : ℝ => T v (x * oneP θ V τ X t)) =
      fun t : ℝ => ℓ (M.rep τ (NormedSpace.exp (t • X)) (v τ : M.H τ)) := by
    funext t
    have hg := GlobalTheory.SmoothAutCheck.exp_mem_UH hU hX t
    let w : M.sm τ := ⟨_, Submodule.subset_span (h1 _ hg)⟩
    have h4 := congrFun (hT.equiv τ _ hg v w rfl) x
    exact ((hℓT w).trans h4).symm
  show deriv (fun t : ℝ => T v (x * oneP θ V τ X t)) 0 = _
  rw [e]
  exact hd.deriv

end GlobalTheory.HolRead.MultDer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RootFlatPushforwardGeoFun
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory.AtP

theorem den_factorization_le {p : ℕ} (hp : p.Prime) (q : ℚ) (e : ℕ) (k : ℤ) (m : ℕ) (hm : ¬ p ∣ m)
    (h : q * (p : ℚ) ^ e = k / m) : q.den.factorization p ≤ e := by
  have hm0 : m ≠ 0 := by rintro rfl; exact hm (dvd_zero p)
  have hm0' : (m : ℚ) ≠ 0 := by exact_mod_cast hm0
  have hq : q = Rat.divInt k ((m * p ^ e : ℕ) : ℤ) := by
    rw [Rat.divInt_eq_div]
    push_cast
    have hp0 : (p : ℚ) ^ e ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.ne_zero)
    rw [eq_div_iff (mul_ne_zero hm0' hp0), mul_comm (m : ℚ), ← mul_assoc, h, div_mul_cancel₀ _ hm0']
  have hd : q.den ∣ m * p ^ e := by
    have := Rat.den_dvd k ((m * p ^ e : ℕ) : ℤ)
    rw [← hq] at this
    exact_mod_cast this
  have hne : m * p ^ e ≠ 0 := mul_ne_zero hm0 (pow_ne_zero _ hp.ne_zero)
  have := (Nat.factorization_le_iff_dvd (Rat.den_nz q) hne).2 hd p
  rw [Nat.factorization_mul hm0 (pow_ne_zero _ hp.ne_zero), Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hm, hp.factorization_pow, Finsupp.single_eq_same, zero_add] at this
  exact this

end GlobalTheory.AtP

namespace GlobalTheory.AtP

theorem main : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (β : G.Cˣ) (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' → ∀ (h₂ : Gr G 1), ∃ k : ℕ, ∀ y : grp G β, f' (h₂⁻¹ * toP1 G β y * h₂) ≠ 0 → (∀ i, ((Module.finBasis ℚ G.C).repr (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) i).den.factorization p ≤ k) ∧ (((((y : G.Cˣ × ℚˣ).2)⁻¹ : ℚˣ) : ℚ)).den.factorization p ≤ k := by
  intro p _ G β K' f' hf h₂
  have hp : p.Prime := Fact.out
  obtain ⟨B, e₁, hB⟩ := GlobalTheory.T.regular_elements_bounded_padic p G K' f' hf β h₂
  obtain ⟨e₂, he⟩ := GlobalTheory.T.bounded_coordinates_p_power_denominator p G B
  refine ⟨max e₁ e₂, fun y hy => ?_⟩
  obtain ⟨hb, k, m, hm, hs⟩ := hB y hy
  refine ⟨fun i => ?_, ?_⟩
  · obtain ⟨k', m', hm', hc⟩ := he _ hb i
    exact (den_factorization_le hp _ e₂ k' m' hm' hc).trans (le_max_right _ _)
  · rw [Units.val_inv_eq_inv_val]
    exact (den_factorization_le hp _ e₁ k m hm hs).trans (le_max_left _ _)

end GlobalTheory.AtP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatSpanBoxIndicatorSchrodingerStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped GlobalTheory.VacAny
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartzBruhat_span_box_indicator_schrodinger : ∀ (F : Type) [Field F] [NumberField F] (v : Pl F) (ψ : AddChar (Fv F v) ℂ), (∀ x : Fv F v, (∀ y ∈ v.adicCompletionIntegers F, ψ (x * y) = 1) ↔ x ∈ v.adicCompletionIntegers F) → ∀ (κ : Type) [Fintype κ] (s : (κ → Fv F v) → ℂ), s ∈ SB (κ → Fv F v) → s ≠ 0 → ∃ (x₀ : κ → Fv F v) (N₀ : ℕ), ∀ N ≥ N₀, Set.indicator {x : κ → Fv F v | ∀ i, Valued.v (x i - x₀ i) ≤ WithZero.exp (-(N : ℤ))} (1 : (κ → Fv F v) → ℂ) ∈ Submodule.span ℂ (Set.range fun w : (κ → Fv F v) × (κ → Fv F v) => schr ψ w s) := by
  first | exact @GlobalTheory.SchrBox.indicator_box_mem_span | exact GlobalTheory.SchrBox.indicator_box_mem_span | (intros; apply GlobalTheory.SchrBox.indicator_box_mem_span <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzFourierSecondVariableRapidDecayStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct FourierTransform
open MeasureTheory GroundTheory.Automorphic.GJMatrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_fourier_secondVariable_rapid_decay : ∀ (U V : Type) [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U] [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (h : SchwartzMap (U × V) ℂ) (k : ℕ), ∃ C : ℝ, ∀ (u : U) (w : V), (1 + ‖u‖) ^ k * (1 + ‖w‖) ^ k * ‖𝓕 (fun t : V => h (u, t)) w‖ ≤ C := by
  first | exact @GlobalTheory.FourierSndDecay.fourier_snd_rapid_decay | exact GlobalTheory.FourierSndDecay.fourier_snd_rapid_decay | (intros; apply GlobalTheory.FourierSndDecay.fourier_snd_rapid_decay <;> assumption)
end

