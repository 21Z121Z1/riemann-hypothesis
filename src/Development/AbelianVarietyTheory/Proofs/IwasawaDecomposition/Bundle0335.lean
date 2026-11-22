import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0016
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0318
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodProjectorSmallestSpaceForms
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0008
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0319
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0023
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0283
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0316

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValAtEqOfResidueFieldHom
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions

namespace GlobalTheory.TrueGeo

theorem valAt_eq_of_residueField_hom {K : Type} [Field K] {Z : Scheme.{0}} [IsIntegral Z] (y : Sp K ⟶ Z) (x : Z)
    (σ : Z.residueField x ⟶ CommRingCat.of K) (hy : Spec.map σ ≫ Z.fromSpecResidueField x = y)
    (a : Z.presheaf.stalk x) :
    valAt y (algebraMap _ Z.functionField a) = σ.hom ((Z.residue x).hom a) := by
  have hx : below y = x := by
    rw [← hy]
    exact Scheme.fromSpecResidueField_apply x _
  subst hx
  have hσ : σ = Z.descResidueField (Scheme.stalkClosedPointTo y) := by
    rw [← Spec.map_inj, ← cancel_mono (Z.fromSpecResidueField _), hy]
    exact (Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K Z y).symm
  have h : RegAt (below y) (algebraMap _ Z.functionField a) := ⟨a, rfl⟩
  have e : h.choose = a := IsFractionRing.injective (Z.presheaf.stalk (below y)) Z.functionField h.choose_spec
  rw [valAt, dif_pos h, e, hσ]
  rfl

theorem exists_finprod_valAt_eq (F : Type) [Field F] [NumberField F] (Y : Var F) (x : Y.X)
    (hx : IsClosed ({x} : Set Y.X)) (f : Y.Fn) (hf : UnitAt x f) :
    ∃ N : F, N ≠ 0 ∧ ∀ (K : Type) [Field K] [IsAlgClosed K] (φ : F →+* K),
      {y : {y : Sp K ⟶ Y.X // y ≫ Y.str = spMap φ} | below y.1 = x}.Finite ∧
      ∏ᶠ (y : {y : Sp K ⟶ Y.X // y ≫ Y.str = spMap φ}) (_ : below y.1 = x), valAt y.1 f = φ N := by
  obtain ⟨a, ha, rfl⟩ := hf
  have := isClosed_singleton_iff_isClosedImmersion.mp hx
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (Y.X.fromSpecResidueField x ≫ Y.str)
  have hfin : IsFinite (Spec.map ψ) := by
    rw [hψ]
    exact isFinite_iff_locallyOfFiniteType_of_jacobsonSpace.2 inferInstance
  letI : Algebra F (Y.X.residueField x) := ψ.hom.toAlgebra
  haveI : Module.Finite F (Y.X.residueField x) := (IsFinite.SpecMap_iff ψ).1 hfin
  have hα : (Y.X.residue x).hom a ≠ 0 := (ha.map _).ne_zero
  refine ⟨Algebra.norm F ((Y.X.residue x).hom a), Algebra.norm_ne_zero_iff.2 hα, fun K _ _ φ => ?_⟩
  letI : Algebra F K := φ.toAlgebra
  let g : (Y.X.residueField x →ₐ[F] K) → {y : Sp K ⟶ Y.X // y ≫ Y.str = spMap φ} := fun σ =>
    ⟨Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ Y.X.fromSpecResidueField x, by
      rw [Category.assoc, ← hψ, ← Spec.map_comp]
      congr 1
      ext c
      exact σ.commutes c⟩
  have hinj : Function.Injective g := fun σ τ h => by
    have h1 := congrArg Subtype.val h
    simp only [g, cancel_mono, Spec.map_inj] at h1
    exact AlgHom.coe_ringHom_injective (congrArg CommRingCat.Hom.hom h1)
  have hr : {y : {y : Sp K ⟶ Y.X // y ≫ Y.str = spMap φ} | below y.1 = x} = Set.range g := by
    ext ⟨y, hy⟩
    constructor
    · intro h
      change below y = x at h
      have h2 : Spec.map ((Y.X.residueFieldCongr h.symm).hom ≫
          Y.X.descResidueField (Scheme.stalkClosedPointTo y)) ≫ Y.X.fromSpecResidueField x = y := by
        rw [Spec.map_comp, Category.assoc, Scheme.residueFieldCongr_fromSpecResidueField]
        exact Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K Y.X y
      generalize (Y.X.residueFieldCongr h.symm).hom ≫
          Y.X.descResidueField (Scheme.stalkClosedPointTo y) = s at h2
      have h3 : ψ ≫ s = CommRingCat.ofHom φ := by
        rw [← Spec.map_inj, Spec.map_comp, hψ, ← Category.assoc, h2, hy]
      exact ⟨⟨s.hom, fun c => congrArg (fun t => t.hom c) h3⟩, Subtype.ext h2⟩
    · rintro ⟨σ, hσ⟩
      rw [← hσ]
      exact Scheme.fromSpecResidueField_apply x _
  refine ⟨hr ▸ Set.finite_range g, ?_⟩
  have key := finprod_mem_range (f := fun y : {y : Sp K ⟶ Y.X // y ≫ Y.str = spMap φ} =>
    valAt y.1 (algebraMap _ Y.X.functionField a)) hinj
  rw [← hr] at key
  refine Eq.trans key ?_
  rw [finprod_eq_prod_of_fintype]
  refine Eq.trans ?_ (Algebra.norm_eq_prod_embeddings F K ((Y.X.residue x).hom a)).symm
  exact Finset.prod_congr rfl fun σ _ => valAt_eq_of_residueField_hom _ x _ rfl a

end GlobalTheory.TrueGeo
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuativeExtensionPoint
section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions

namespace GlobalTheory.TrueGeo

theorem exists_valuationRing_point : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (M : TrueGeo.Model Y) (v : HeightOneSpectrum (𝓞 F)) (e : Ext v) (y : AlgPt Y), ∃ yt : Sp e.O ⟶ M.X, spMap e.O.subtype ≫ yt = y.1 ≫ M.j ∧ ∀ U : M.X.Opens, yt (IsLocalRing.closedPoint e.O) ∈ U → ⊤ ≤ yt ⁻¹ᵁ U ∧ y.1 (IsLocalRing.closedPoint _) ∈ M.j ⁻¹ᵁ U := by
  intro F _ _ Y M v e y
  have hP : IsProper M.p := by
    obtain ⟨N, j, hj, he⟩ := M.ar.isProjOver
    have := isProper_str (𝓞 F) N
    rw [← he]; infer_instance
  have hmem : ∀ a : 𝓞 F, ((algebraMap F (AlgebraicClosure F)).comp (algebraMap (𝓞 F) F)) a ∈ e.O := by
    intro a
    rw [e.mem_O, RingHom.comp_apply, e.w_alg]
    exact IsDedekindDomain.HeightOneSpectrum.adicAbv_coe_le_one (K := F) v (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v) a
  let φ : 𝓞 F →+* e.O := ((algebraMap F (AlgebraicClosure F)).comp (algebraMap (𝓞 F) F)).codRestrict e.O.toSubring hmem
  have hE : ValuativeCriterion.Existence M.p := by
    have h : UniversallyClosed M.p := inferInstance
    rw [UniversallyClosed.eq_valuativeCriterion] at h
    exact h.1
  have hsq : CommSq (y.1 ≫ M.j) (Spec.map (CommRingCat.ofHom (algebraMap e.O (AlgebraicClosure F)))) M.p (spMap φ) := by
    refine ⟨?_⟩
    rw [Category.assoc, M.pb.w, ← Category.assoc, y.2, ← Spec.map_comp, ← Spec.map_comp]
    rfl
  obtain ⟨⟨l⟩⟩ := hE { R := e.O, K := AlgebraicClosure F, i₁ := y.1 ≫ M.j, i₂ := spMap φ, commSq := hsq }
  have hl : spMap e.O.subtype ≫ l.l = y.1 ≫ M.j := l.fac_left
  refine ⟨l.l, hl, fun U hU => ?_⟩
  have htop : l.l ⁻¹ᵁ U = ⊤ := (IsLocalRing.closedPoint_mem_iff (R := e.O) (l.l ⁻¹ᵁ U)).1 hU
  refine ⟨htop.ge, ?_⟩
  have h2 : (y.1 ≫ M.j) ⁻¹ᵁ U = ⊤ := by
    rw [← hl, Scheme.Hom.comp_preimage, htop]; rfl
  have h3 : (IsLocalRing.closedPoint (AlgebraicClosure F) : Sp (AlgebraicClosure F)) ∈ (y.1 ≫ M.j) ⁻¹ᵁ U := by
    rw [h2]; trivial
  rw [Scheme.Hom.comp_preimage] at h3
  exact h3

end GlobalTheory.TrueGeo
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WLeOneOfIsIntegral
section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions

namespace GlobalTheory.TrueGeo

theorem Ext.w_le_one_of_isIntegral {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)} (e : Ext v)
    {x : AlgebraicClosure F} (hx : IsIntegral ℤ x) : e.w x ≤ 1 := by
  rw [← e.mem_O]
  have h : IsIntegral e.O x := hx.tower_top
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := e.O) (K := AlgebraicClosure F)).1 h
  rw [← hy]
  exact y.2

theorem finite_ext_one_lt (F : Type) [Field F] [NumberField F] (a : AlgebraicClosure F) :
    {v : HeightOneSpectrum (𝓞 F) | ∃ e : Ext v, 1 < e.w a}.Finite := by
  have hQ : IsAlgebraic ℚ a :=
    (Algebra.IsAlgebraic.trans ℚ F (AlgebraicClosure F)).isAlgebraic a
  have hZ : IsAlgebraic ℤ a := (IsFractionRing.isAlgebraic_iff ℤ ℚ _).2 hQ
  obtain ⟨d, hd, hi⟩ := hZ.exists_integral_multiple
  have hd' : (Ideal.span {(d : 𝓞 F)}) ≠ 0 := by
    simpa using hd
  refine (Ideal.finite_factors hd').subset ?_
  rintro v ⟨e, he⟩
  simp only [Set.mem_setOf_eq, Ideal.dvd_span_singleton]
  by_contra hv
  have h1 : NumberField.HeightOneSpectrum.adicAbv F v ((d : 𝓞 F) : F) = 1 :=
    (v.adicAbv_coe_eq_one_iff (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v) _).2 hv
  have h2 := e.w_le_one_of_isIntegral hi
  have h3 : e.w (d : AlgebraicClosure F) = 1 := by
    rw [← h1, ← e.w_alg]
    simp
  rw [zsmul_eq_mul, map_mul, h3, one_mul] at h2
  exact absurd he (not_lt.2 h2)

theorem finite_ext_ne_one (F : Type) [Field F] [NumberField F] (a : AlgebraicClosure F) (ha : a ≠ 0) :
    {v : HeightOneSpectrum (𝓞 F) | ∃ e : Ext v, e.w a ≠ 1}.Finite := by
  refine ((finite_ext_one_lt F a).union (finite_ext_one_lt F a⁻¹)).subset ?_
  rintro v ⟨e, he⟩
  rcases lt_or_gt_of_ne he with h | h
  · refine Or.inr ⟨e, ?_⟩
    rw [map_inv₀]
    exact (one_lt_inv₀ (e.w.pos ha)).2 h
  · exact Or.inl ⟨e, h⟩

end GlobalTheory.TrueGeo
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilFockVectorEigenOfFiniteStepEigenStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilFock_vector_eigen_of_finite_step_eigen : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), Pins R F cG → Holds R F → ∀ (t : T) (k : ℕ), k + 1 < D.R.m → ∀ κ ∈ GfC (Yc D k), ∀ κ' ∈ GfC (Yc D (k + 1)), ∀ c : ℂ, R.ωY t k (κ, κ') (R.vY t k) = c • R.vY t k → ∀ φ, R.ωY t k (κ, κ') (R.toRealDat.ptY t k φ) = c • R.toRealDat.ptY t k φ := by
  first | exact @GlobalTheory.Mem.R3.DTheta.StepLevFock.om_ptY_of_finite | exact GlobalTheory.Mem.R3.DTheta.StepLevFock.om_ptY_of_finite | (intros; apply GlobalTheory.Mem.R3.DTheta.StepLevFock.om_ptY_of_finite <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WhittakerFunctionalTorusValuationBoundStatement
section
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.whittaker_functional_torus_valuation_bound : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin n) k) V), IsSmooth ρ → ∀ l : Module.Dual ℂ V, IsFunctional ψ ρ l → ∀ x : V, ∃ r : kˣ, ∀ (t : Fin n → kˣ) (i j : Fin n), j.val = i.val + 1 → l (ρ (diagT k (Fin n) t) x) ≠ 0 → valuation k ((t i : k) / t j) ≤ valuation k (r : k) := by
  first | exact @GlobalTheory.RootUp.whittaker_torus_root_bound | exact GlobalTheory.RootUp.whittaker_torus_root_bound | (intros; apply GlobalTheory.RootUp.whittaker_torus_root_bound <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WhittakerTorusTwKerRootBoundStatement
section
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.whittaker_torus_twKer_rootBound' : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin n) k) V) (l : Module.Dual ℂ V), IsFunctional ψ ρ l → ∀ (a b : ℕ) (h : ∑ i, ![a, b] i = n) (i j : Fin n), i.val + 1 = a → j.val = a → ∀ x ∈ twKer ρ (unipRad k (stdBlocks ![a, b] h)) 1, ∃ r : kˣ, ∀ t : Fin n → kˣ, l (ρ (diagT k (Fin n) t) x) ≠ 0 → valuation k (r : k) ≤ valuation k ((t i : k) / t j) := by
  first | exact @GlobalTheory.whittaker_torus_twKer_rootBound | exact GlobalTheory.whittaker_torus_twKer_rootBound | (intros; apply GlobalTheory.whittaker_torus_twKer_rootBound <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.XEUpdSZeroLam
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section
namespace GlobalTheory.Mem.R3
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

set_option maxHeartbeats 2000000 in

theorem XE_updS_zeroLam (R : RealDat3 D A3 Ks) (F : Face3 D A3) (c : Fin D.R.m → ℝ)
    (hC : R.WeakCharacterisation F) (hP : PrimRows3 R F) (hOk : A3.fam3.Ok3 1) (hsep : A3.fam3.TypesSep3)
    (hZ : ∀ p, R.EEp3 p ≠ ⊥ → ∀ i, R.Wp3 i p ≠ ⊥ ∧ ∀ v, v ≠ A3.A.v0 → R.PartAt F i p v) (b : Bool) :
    (((R.updS R.kap (zeroLam R F c)).toCx3 F).data F.cr b).XE = ((R.toCx3 F).data F.cr b).XE := by
  have h := cx_XE_scal (R.toCx3 F) F.cr (zeroLam R F c) b fun p hp j v => by
    by_cases he : R.EEp3 p = ⊥
    · exact absurd (partPr_of_bot _ _ _ (qp_bot R F hC hP hOk hsep he b)) hp
    · exact zeroLam_of_ne R F c (hZ p he j).1 fun hv => (hZ p he j).2 v hv
  exact (by with_unfolding_all exact (h :))

set_option maxHeartbeats 2000000 in

def scalReadL (R : RealDat3 D A3 Ks) (F : Face3 D A3) (lam : type_of% R.lam3)
    (hX : ∀ b, (((R.updS R.kap lam).toCx3 F).data F.cr b).XE = ((R.toCx3 F).data F.cr b).XE) (X0 : BaseLevelRowSide D)
    (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y) : ReadL (R.updS R.kap lam) F X0 Y :=
  { Z with
    met := fun v hv x y => (Z.met v hv x y).trans (by rw [hX true]; rfl)
    met0 := fun v hv x y => (Z.met0 v hv x y).trans (by rw [hX false]; rfl) }

set_option maxHeartbeats 4000000 in

theorem read_updS (R : RealDat3 D A3 Ks) (F : Face3 D A3) (lam : type_of% R.lam3)
    (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 F.P1 F.ψ1 Zs)) (Sp : ∀ Zs, SPer (Dc Zs))
    (Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3) (err : type_of% R.err0)
    (hX : ∀ b, (((R.updS R.kap lam).toCx3 F).data F.cr b).XE = ((R.toCx3 F).data F.cr b).XE) (X0 : BaseLevelRowSide D)
    (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y) :
    ∃ (Y' : Read (A3 := A3) ((R.updS R.kap lam).withErr err).toRealDat (reFace F Dc Sp Zsc).lv2 X0) (Z' : ReadL ((R.updS R.kap lam).withErr err) (reFace F Dc Sp Zsc) X0 Y'), Y'.tup = Y.tup ∧ Y'.tupT = Y.tupT ∧ HEq Y'.jA Y.jA ∧ HEq Y'.jA0 Y.jA0 ∧ HEq Y'.eMt Y.eMt ∧ HEq Y'.PY Y.PY ∧ HEq Y'.eFT Y.eFT ∧ HEq Y'.IL Y.IL ∧ HEq Z'.jW Z.jW :=
  ⟨reFaceRead (R.updS R.kap lam) F Dc Sp Zsc err X0 Y,
    reFaceReadL (R.updS R.kap lam) F Dc Sp Zsc err X0 Y (scalReadL R F lam hX X0 Y Z),
    rfl, rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl⟩

end GlobalTheory.Mem.R3

end
end

