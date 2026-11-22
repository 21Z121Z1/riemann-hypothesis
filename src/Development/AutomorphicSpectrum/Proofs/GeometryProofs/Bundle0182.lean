import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0038
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LinearIndependentEigProj
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0058
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0038
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0034
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0177
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0075
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0178
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0156
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0172
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeRegularAtLocalPoint
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0109
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0026
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0003
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0179
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsTransition
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0014
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0054
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ModelFibresPowerFree
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeInnerProductMapIff
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

namespace TripleHodge

variable {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
  {φ : G'.left ⟶ G.left}

theorem one_left_comp (h : IsGrpPullback G' G f φ) (T : Over S') :
    (1 : T ⟶ G').left ≫ φ = (1 : Over.mk (T.hom ≫ f) ⟶ G).left :=
  congrArg (fun p => p.left) (map_one (pushHom h T))

theorem isTanAt_iff (h : IsGrpPullback G' G f φ) (z : Spec (CommRingCat.of ℂ) ⟶ S') (v' : epsAt z ⟶ G')
    (v : epsAt (z ≫ f) ⟶ G) (e : v.left = v'.left ≫ φ) : IsTanAt G' z v' ↔ IsTanAt G (z ≫ f) v := by
  have one := one_left_comp h (Over.mk z)
  have wv := Over.w v'
  constructor
  · intro hv
    unfold IsTanAt at hv ⊢
    rw [e, ← Category.assoc, hv]
    exact one
  · intro hv
    unfold IsTanAt at hv ⊢
    apply h.1.hom_ext
    · rw [Category.assoc, ← e, hv]
      exact one.symm
    · have w1 := Over.w (1 : Over.mk z ⟶ G')
      rw [Category.assoc, w1, wv]
      show Spec.map _ ≫ Spec.map _ ≫ z = z
      rw [← Category.assoc, ← Spec.map_comp]
      have e₁ : CommRingCat.ofHom (algebraMap ℂ (DualNumber ℂ)) ≫
          CommRingCat.ofHom (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom = 𝟙 _ := by
        ext x
        simp
      rw [e₁, Spec.map_id, Category.id_comp]

variable {X X' : Scheme.{0}}

theorem exists_iso_comp {Y : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} (hL : L.IsLB) (hL' : L'.IsLB)
    {w : LB.Iso L' (L.pull F)} (hw : w.IsGen) (p : Y ⟶ X') :
    ∃ w₂ : LB.Iso (L'.pull p) (L.pull (p ≫ F)), w₂.IsGen := by
  have hP : (L'.pull p).IsLB := pull_isLB hL' p
  have hr := (isGen_iff _).1 (GlobalTheory.TorsionTauCompare.isGen_refl hP)
  have hw' := (isGen_iff _).1 hw
  obtain ⟨w₂, T⟩ := exists_comp hL' w _ hw' hr hL hP
  exact ⟨w₂, (isGen_iff _).2 (T.pgen_comp hL' hw' hr)⟩

theorem exists_iso_cancel {Y : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} (hL : L.IsLB) (hL' : L'.IsLB)
    {w : LB.Iso L' (L.pull F)} (hw : w.IsGen) (p : Y ⟶ X') :
    ∃ w₂ : LB.Iso (L.pull (p ≫ F)) (L'.pull p), w₂.IsGen := by
  have hP : (L.pull (p ≫ F)).IsLB := pull_isLB hL (p ≫ F)
  have hr := (isGen_iff _).1 (GlobalTheory.TorsionTauCompare.isGen_refl hP)
  have hw' := (isGen_iff _).1 hw
  obtain ⟨w₂, T⟩ := exists_cancel hL w _ hw' hr hL' hP
  exact ⟨w₂, (isGen_iff _).2 (T.pgen_cancel hL hw' hr)⟩

end TripleHodge

theorem hodgeInnerProduct_tripleMap_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0})
    (t : SAB H X) (X' : Scheme.{0}) (t' : SAB H X') (f : X' ⟶ X) (m : SABMap t' t f)
    (z : Spec (CommRingCat.of ℂ) ⟶ X') (v' w' : epsAt z ⟶ t'.G) (v w : epsAt (z ≫ f) ⟶ t.G) (c : ℂ),
    v.left = v'.left ≫ m.φ → w.left = w'.left ≫ m.φ →
      (HodgeIP t'.G t'.PP.L z v' w' c ↔ HodgeIP t.G t.PP.L (z ≫ f) v w c) := by
  intro E _ _ _ H X t X' t' f m z v' w' v w c hv hw
  obtain ⟨i, hi, -, -⟩ := m.lin
  have tv := TripleHodge.isTanAt_iff m.cart z v' v hv
  have tw := TripleHodge.isTanAt_iff m.cart z w' w hw
  have hL := t.PP.isLB
  have hL' := t'.PP.isLB
  constructor
  · rintro ⟨-, h₁, h₂, A, _, φ, g, u, Hm, χ, a', b', a, b, p₁, p₂, p₃, p₄, p₅, p₆, rfl⟩
    obtain ⟨i₂, hi₂⟩ := TripleHodge.exists_iso_comp hL hL' hi φ
    have hP := pull_isLB hL' φ
    have hQ := pull_isLB hL (φ ≫ m.φ)
    refine ⟨hL, tv.1 h₁, tw.1 h₂, A, inferInstance, φ ≫ m.φ, g, GlobalTheory.TorsionTauCompare.transport hP hQ hi₂ u, Hm, χ,
      a', b', a, b, p₁.comp m.cart, GlobalTheory.TorsionTauCompare.isAH_transport hP hQ hi₂ u p₂, ?_, ?_, p₅, p₆, rfl⟩
    · rw [hv, ← p₃, Category.assoc]
    · rw [hw, ← p₄, Category.assoc]
  · rintro ⟨-, h₁, h₂, A, _, ψ, g, u, Hm, χ, a', b', a, b, p₁, p₂, p₃, p₄, p₅, p₆, rfl⟩
    obtain ⟨φ, rfl, hφ⟩ : ∃ φ : A.left ⟶ t'.G.left, φ ≫ m.φ = ψ ∧ φ ≫ t'.G.hom = A.hom ≫ z :=
      ⟨m.cart.1.lift ψ (A.hom ≫ z) (by rw [p₁.1.w, Category.assoc]), m.cart.1.lift_fst _ _ _, m.cart.1.lift_snd _ _ _⟩
    obtain ⟨i₂, hi₂⟩ := TripleHodge.exists_iso_cancel hL hL' hi φ
    have hP := pull_isLB hL (φ ≫ m.φ)
    have hQ := pull_isLB hL' φ
    have lift : ∀ (x : epsR ℂ ⟶ A) (y : epsAt z ⟶ t'.G) (y₀ : epsAt (z ≫ f) ⟶ t.G), y₀.left = y.left ≫ m.φ →
        x.left ≫ φ ≫ m.φ = y₀.left → x.left ≫ φ = y.left := by
      intro x y y₀ e e'
      apply m.cart.1.hom_ext
      · rw [Category.assoc, e', e]
      · rw [Category.assoc, hφ, ← Category.assoc, Over.w x, Over.w y]
        rfl
    exact ⟨hL', tv.2 h₁, tw.2 h₂, A, inferInstance, φ, g, GlobalTheory.TorsionTauCompare.transport hP hQ hi₂ u, Hm, χ,
      a', b', a, b, IsGrpPullback.cancel m.cart p₁ hφ, GlobalTheory.TorsionTauCompare.isAH_transport hP hQ hi₂ u p₂,
      lift a' v' v hv p₃, lift b' w' w hw p₄, p₅, p₆, rfl⟩

end GlobalTheory.CompanionTheory.Ar
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeLatticeValuationAgree
section
open AlgebraicGeometry CategoryTheory Limits NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat.COrder

theorem order_on_component : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) [CharZero Ω] (E : Type) [Field E] [NumberField E] (V : Type) [AddCommGroup V] [Module Ω V] [FiniteDimensional Ω V] (L : Lat ξ V) (ρ : 𝓞 E →+* Module.End Ω V) (bar : 𝓞 E ≃+* 𝓞 E) (p q : ℕ) (𝓗 : HodgeLat L ρ bar (p + q)) (σ σ' : E →+* Ω) (v : Fin p → V) (w : Fin q → V) (u : Fin (p + q) → V × Module.Dual Ω V) (α κ : Ω) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O Ω] (s : X ⟶ Spec (CommRingCat.of O)) [IsProper s] (ϖ : O), Irreducible ϖ → Function.Injective (algebraMap O Ω) → ξ ≫ s = Spec.map (CommRingCat.ofHom (algebraMap O Ω)) → IsCptGen ξ → NormalCpt ξ → ConstClosed O Ω → (∀ a : 𝓞 E, σ (a : E) ∈ (algebraMap O Ω).range) → (∀ a : 𝓞 E, σ' (a : E) = σ (bar a : 𝓞 E)) → (∀ a, bar (bar a) = a) → LinearIndependent Ω v → Submodule.span Ω (Set.range v) = HT.eigSp ρ σ → LinearIndependent Ω w → Submodule.span Ω (Set.range w) = HT.eigSp ρ σ' → IsAdapted 𝓗.ρH σ v w u → 𝓗.DegZero σ (algebraMap O Ω ϖ) → IsLineGenOn (L.inter (HT.eigSp ρ σ)) (L.inter (HT.eigSp ρ σ')) p q (α • exteriorPower.ιMulti Ω p v) (κ • exteriorPower.ιMulti Ω q w) (genFibre O ξ) → ∃ (M : ℕ) (a : ℤ), 0 < M ∧ ∀ x : Cpt ξ, OrderAt (detLat (𝓗.quot σ) u) (α / κ) (algebraMap O Ω ϖ) M a x := by
  intro X Ω _ ξ _ E _ _ V _ _ _ L ρ bar p q 𝓗 σ σ' v w u α κ O _ _ _ _ s _ ϖ hϖ hinj hs hg hn hc hσ h1 h2
    hv hvs hw hws had hdz hgen
  obtain ⟨hu, husp, -⟩ := AdaptedSpan.adapted_span X Ω ξ E V L ρ bar p q (p + q) 𝓗 σ σ' v w u h1 h2 hv hvs hw hws had
  have hO : ∀ (x : Cpt ξ) (o : O), algebraMap O Ω o ∈ regAt ξ x := fun x o =>
    (ConstReg.regular_const X Ω ξ O s hs x o).1
  have hσr : ∀ (x : Cpt ξ) (a : 𝓞 E), σ (a : E) ∈ regAt ξ x := fun x a => by
    obtain ⟨o, ho⟩ := hσ a
    exact ho ▸ hO x o
  have hinv : ∀ x ∈ genFibre O ξ, ∀ b : 𝓞 E, (σ (b : E))⁻¹ ∈ regAt ξ x := fun x hx b => by
    obtain ⟨o, ho⟩ := hσ b
    rw [← ho]
    by_cases h0 : o = 0
    · rw [h0, map_zero, inv_zero]
      exact zero_mem _
    · exact (hx o h0).2.2
  refine GlobalTheory.T.line_degree_special_fibre X Ω ξ O s ϖ hϖ hinj hs hg hn (GlobalTheory.T.isConnected_zeroSet_uniformizer X Ω ξ O s ϖ hϖ hinj hs hg hc) _ _
    (𝓗.det_isVB σ hσr hu husp) (hdz u hu husp) fun x hx => ?_
  obtain ⟨ha, hb, hco⟩ := hgen
  have hα : α ≠ 0 := left_ne_zero_of_smul ha
  have hκ : κ ≠ 0 := left_ne_zero_of_smul hb
  refine (GenAgree.generic_agree X Ω ξ E V L ρ bar p q 𝓗 σ σ' v w u x (α / κ) hg h1 h2 (fun a => ?_)
    hv hvs hw hws had).2 ⟨div_ne_zero hα hκ, ?_⟩
  · obtain ⟨y, z, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) a
    have e : ∀ c : 𝓞 E, algebraMap (𝓞 E) E c = (c : E) := fun _ => rfl
    rw [e, e, map_div₀, map_div₀, h1, h1, div_eq_mul_inv, div_eq_mul_inv]
    exact ⟨mul_mem (hσr x _) (hinv x hx _), mul_mem (hσr x _) (hinv x hx _)⟩
  · obtain ⟨a', b', ha', hb', hA, hB, e⟩ := hco x hx
    rw [one_mul] at e
    subst e
    refine ⟨a' * α, a' * κ, mul_ne_zero ha' hα, mul_ne_zero ha' hκ, by rw [hA, smul_smul], by rw [hB, smul_smul], ?_⟩
    field_simp

end GlobalTheory.CompanionTheory.Ar.Flat.COrder
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.InfNormConjugateInvariantStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inf_norm_conjugate_invariant : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (U : Set (Xo.XF c)) (τ : E →+* ℂ) (φ : FrameFn Xo c) (s : c.F →+* ℂ) (t : ℝ), IsLineFn U τ φ → HasInfNorm U τ φ s t → HasInfNorm U τ φ ((starRingEnd ℂ).comp s) t := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.hasInfNorm_conj | exact GlobalTheory.CompanionTheory.Ar.Flat.hasInfNorm_conj | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.hasInfNorm_conj <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeFrameSpecializesStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar Filter Topology Metric

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_frame_specializes : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (M : LieModel G ξ E) (C : Type) [Field C] (z : Sp C ⟶ X) (h : genPt ξ ⤳ centre z) (EC : Type) [AddCommGroup EC] [Module C EC] (N : LieModel G z EC) (g n : ℕ) (b : Fin g → E) (S : Finset (Fin g)) (c : Fin n → E) (L : Lat ξ E) (w : Fin n → EC), IsCptGen ξ → M.lat.IsFrameAt b ⟨centre z, h⟩ → L ⟨centre z, h⟩ = Submodule.span (regAt ξ ⟨centre z, h⟩) (b '' S) → L.IsFrameAt c ⟨centre z, h⟩ → (∀ i, M.ValAt z (c i) (N.pt (w i))) → LinearIndependent C w := by
  first | exact @GlobalTheory.CompanionTheory.Ar.values_frame_sublattice_linearIndependent | exact GlobalTheory.CompanionTheory.Ar.values_frame_sublattice_linearIndependent | (intros; apply GlobalTheory.CompanionTheory.Ar.values_frame_sublattice_linearIndependent <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeRegularAtLocalPointStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.RootHt GroundTheory.Heights₂.Heights

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_regular_at_local_point : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X)
    (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (R : Type) [CommRing R] [IsLocalRing R]
    (z : Sp R ⟶ X) (h : genPt ξ ⤳ centre z) (ER : Type) [AddCommGroup ER] [Module R ER] (MR : LieModel G z ER)
    (f : Module.Dual Ω Li), IsCptGen ξ → (∀ e ∈ M.lat ⟨centre z, h⟩, f e ∈ regAt ξ ⟨centre z, h⟩) →
    ∃ g : ER →ₗ[R] R, ∀ (e : Li) (x : ER) (u : R), M.ValAt z e (MR.pt x) → ValAt ξ z (f e) u → g x = u := by
  first | exact @GlobalTheory.CompanionTheory.Ar.RootHt.exists_lieFunctional | exact GlobalTheory.CompanionTheory.Ar.RootHt.exists_lieFunctional | (intros; apply GlobalTheory.CompanionTheory.Ar.RootHt.exists_lieFunctional <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieLatticeEvalFractionFieldStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_lattice_eval_fraction_field : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (M : LieModel G ξ E) (R : Type) [CommRing R] [IsLocalRing R] (z : Spec (CommRingCat.of R) ⟶ X) (C : Type) [Field C] [Algebra R C] (EC : Type) [AddCommGroup EC] [Module C EC] [Module R EC] [IsScalarTower R C EC] (MC : LieModel G (Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ z) EC), IsCptGen ξ → Smooth G.hom → genPt ξ ⤳ centre z → genPt ξ ⤳ centre (Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ z) → ∀ w : EC, w ∈ M.fibAt M.lat z MC ↔ ∃ v : epsAt z ⟶ G, IsTanAt G z v ∧ (MC.pt w).left = Spec.map (CommRingCat.ofHom (dualMap (algebraMap R C))) ≫ v.left := by
  first | exact @GlobalTheory.CompanionTheory.Ar.lieLat_fibAt_iff | exact GlobalTheory.CompanionTheory.Ar.lieLat_fibAt_iff | (intros; apply GlobalTheory.CompanionTheory.Ar.lieLat_fibAt_iff <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelActionSpecializeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_model_action_specialize : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (V : Type) [AddCommGroup V] [Module Ω V] (M : LieModel G ξ V) (F : Type) [Field F] (z : Sp F ⟶ X) (h : genPt ξ ⤳ centre z) (W : Type) [AddCommGroup W] [Module F W] (Mz : LieModel G z W) (A : Type) [CommRing A] (act : OAct A G) (ρ : A →+* Module.End Ω V) (ρz : A →+* Module.End F W) (K : Type) [Field K] (inc : K →+* Ω) (βF : K →+* F) (σ : A →+* K) (n : ℕ) (e : Fin n → A) (cf : Fin n → K) (r : ℕ) (b : Fin r → V), IsCptGen ξ → Smooth G.hom → M.IsActOf act.act ρ → Mz.IsActOf act.act ρz → (∀ k : K, ValAt ξ z (inc k) (βF k)) → ∑ k, cf k * σ (e k) = 1 → (∀ (a : A) (w : V), ρ a (∑ k, inc (cf k) • ρ (e k) w) = inc (σ a) • ∑ k, inc (cf k) • ρ (e k) w) → (M.eigLat ρ (inc.comp σ)).IsFrameAt b ⟨centre z, h⟩ → ∃ u : Fin r → W, (∀ i, M.ValAt z (b i) (Mz.pt (u i))) ∧ Submodule.span F (Set.range u) = eigSp ρz (βF.comp σ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.ValueSpan.value_span | exact GlobalTheory.CompanionTheory.Ar.ValueSpan.value_span | (intros; apply GlobalTheory.CompanionTheory.Ar.ValueSpan.value_span <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelDominantHodgeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_model_dominant_hodge : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (X' : Scheme.{0}) (t' : SAB H X') (f : X' ⟶ X) (m : SABMap t' t f) (Ω Ω' : Type) [Field Ω] [Field Ω'] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (i : Ω →+* Ω') (V V' : Type) [AddCommGroup V] [Module Ω V] [AddCommGroup V'] [Module Ω' V'] (M : LieModel t.G ξ V) (M' : LieModel t'.G ξ' V'), IsCptGen ξ → IsCptGen ξ' → GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ f i → ∃ j : V →+ V', (∀ e, (M'.pt (j e)).left ≫ m.φ = spMap (dualMap i) ≫ (M.pt e).left) ∧ (∀ (a : Ω) e, j (a • e) = i a • j e) ∧ (∀ (n : ℕ) (b : Fin n → V), LinearIndependent Ω b → LinearIndependent Ω' fun k => j (b k)) ∧ Submodule.span Ω' (Set.range j) = ⊤ ∧ M'.lat = M.lat.pull ξ' f j := by
  first | exact @GlobalTheory.CompanionTheory.Ar.LiePullSab.lie_pull_lat | exact GlobalTheory.CompanionTheory.Ar.LiePullSab.lie_pull_lat | (intros; apply GlobalTheory.CompanionTheory.Ar.LiePullSab.lie_pull_lat <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelExtendsOverDvrStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_model_extends_over_dvr : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (K : Type) [Field K] (V : Subring K) [IsDomain V] [IsDiscreteValuationRing V] [IsFractionRing V K] (y : Sp K ⟶ Xo.XF c) (T : SAB H (Sp V)) (tK : SAB H (Sp K)) (m : SABMap tK Xo.univ.t (under y)) (m' : SABMap tK T (spMap (algebraMap V K))) (U : Type) [AddCommGroup U] [Module K U] (M : LieModel Xo.univ.t.G (under y) U) (ρ : 𝓞 E →+* Module.End K U) (σ : E →+* K) (I : Type) [Fintype I] (n r : ℕ) (e : Fin n ≃ I) (uV : Fin n → (epsAt (𝟙 (Sp V)) ⟶ T.G)) (u : I → U) (v : Fin r → U), M.IsActOf Xo.univ.t.act.act ρ → (∀ a : 𝓞 E, σ (a : E) ∈ V) → (∀ k, IsTanAt T.G _ (uV k)) → (∀ w, IsTanAt T.G _ w → ∃! cc : Fin n → V, IsComb cc uV w) → (∀ k, ∃ s : Sp (DualNumber K) ⟶ tK.G.left, s ≫ m.φ = (M.pt (u (e k))).left ∧ s ≫ m'.φ = spMap (dualMap (algebraMap V K)) ≫ (uV k).left) → LinearIndependent K v → Submodule.span V (Set.range u) ⊓ (HT.eigSp ρ σ).restrictScalars V = Submodule.span V (Set.range v) → LinearIndependent K u ∧ IsIntFrame m m' (σ.comp (algebraMap (𝓞 E) E)) (fun a => M.pt (v a)) := by
  first | exact @GlobalTheory.CompanionTheory.Relay.lie_model_extends_over_dvr | exact GlobalTheory.CompanionTheory.Relay.lie_model_extends_over_dvr | (intros; apply GlobalTheory.CompanionTheory.Relay.lie_model_extends_over_dvr <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LineBundleGeneratorCorrespondence
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Ar.Nfold

theorem nfold_first_law : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X0 : Scheme.{0}) (t : SAB H X0) (n : ℕ), ∃ κ : LB.Gen (LB.LinComb t.PP.L (Sum.elim (cφG t ![fst t.G t.G ^ n, snd t.G t.G]) (cφG t ![fst t.G t.G, snd t.G t.G])) (Sum.elim (cε 2) fun I => -((n : ℤ) * cε 2 I))), κ.IsGen ∧ LB.Gen.Corr t.PP.L _ _ _ _ (LB.pullGen t.PP.L _ _ κ (lift (1 : t.G ⟶ t.G) (𝟙 t.G)).left) (LB.oneGen t.PP.L) ∧ ∀ (S : Type) [CommRing S] (x : Sp S ⟶ X0) (d : ℕ) (g : GermAt t x d) (m : ℕ), ∃ u : (Jet S (Fin 2 × Fin d) m)ˣ, (u : Jet S (Fin 2 × Fin d) m) = psJet m (pow1 g.B n) ∧ LB.Gen.Corr t.PP.L _ _ _ _ (LB.pullGen t.PP.L _ _ κ (lift (jptG t x d g.x m (0 : Fin 2)) (jptG t x d g.x m (1 : Fin 2))).left) (scaleGenG t _ _ (unitΓ u) (LB.mulGen t.PP.L _ _ _ _ (peG t x d g.x g.e m ![fun j => psIn d m ![0] (g.B.A.act (n : 𝓞 E) j), fun j => MvPolynomial.X ((1 : Fin 2), j)]) (LB.invGen t.PP.L _ _ (genPowG t _ _ (g.e m) n)))) :=
  @PositivityTheory.HtPt.Ca.nfold_law

end GlobalTheory.CompanionTheory.Ar.Nfold
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ModelFibresPowerFreeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.model_fibres_power_free : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] [IsNoetherianRing O] (β : O →+* c.F) (Y : Model Xo c β), Dense (Set.range Y.j) → Y.SplitFibres → Y.N3 → ∀ (p : ℕ), p.Prime → ∀ z : Y.X, (p : Y.X.residueField z) = 0 → FibPF Y.t z := by
  first | exact @GlobalTheory.CompanionTheory.Ar.ModelFib.model_fibPF | exact GlobalTheory.CompanionTheory.Ar.ModelFib.model_fibPF | (intros; apply GlobalTheory.CompanionTheory.Ar.ModelFib.model_fibPF <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ModuliIsReducedStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isReduced_moduli' : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l), IsReduced Xo.X := by
  first | exact @GlobalTheory.CompanionTheory.Ar.moduli_isReduced | exact GlobalTheory.CompanionTheory.Ar.moduli_isReduced | (intros; apply GlobalTheory.CompanionTheory.Ar.moduli_isReduced <;> assumption)
end

