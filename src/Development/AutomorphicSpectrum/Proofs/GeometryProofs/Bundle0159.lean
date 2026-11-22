import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RankLin
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0027
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0018
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0156
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0031
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0155
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0001
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0002
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsPeriodAtRestrict
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0009
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0023
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0015
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0072
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0083
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0078
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0084
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0086
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GagaLineGeneratorComplex
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenLatticeConstantRank
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.EigRank

theorem rt0_conj_neg_ne_zero {d : ℕ} (hd : 0 < d) {z : ℂ} (h : z ^ 2 = -(d : ℂ)) : starRingEnd ℂ z = -z :=
  _root_.UpperTheory.Reformulated.B.Ydc3.main hd h

theorem labelEmb_rt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Geo.Tor.Level H) (c : Coeff l) (τ : CMType H), labelEmb c (Sum.inl τ) H.rt = IntermediateField.inclusion c.le (baseKA l).ρ ∧ labelEmb c (Sum.inr τ) H.rt = -IntermediateField.inclusion c.le (baseKA l).ρ := by
  intro E _ _ _ H l c τ
  constructor
  · apply Subtype.ext
    exact τ.2
  · apply Subtype.ext
    show τ.1 (((H.bar H.rt : 𝓞 E)) : E) = - H.rt0
    rw [H.bar_eq, IsCMField.complexEmbedding_complexConj, τ.2]
    exact rt0_conj_neg_ne_zero H.d_prime.pos H.sqrt_neg_disc_sq

theorem structure_of_model_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (Ω : Type) [Field Ω] (y₀ : Sp Ω ⟶ Xo.XF c) (cst : c.F →+* Ω), y₀ ≫ Y.j ≫ Y.s = spMap (cst.comp (algebraMap (𝓞 c.F) c.F)) → y₀ ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) ≫ Xo.s = spMap (cst.comp (IntermediateField.inclusion c.le).toRingHom) := by
  intro E _ _ _ H D l Xo c Y Ω _ y₀ cst hy
  have : FiniteDimensional ℚ c.F := c.fin
  have : NumberField c.F := ⟨⟩
  have h1 : Y.j ≫ Y.s = pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) ≫
      spMap (algebraMap (𝓞 c.F) c.F) := by
    show (Y.jQ ≫ pullback.fst _ _) ≫ Y.s = _
    rw [Category.assoc, pullback.condition, ← Category.assoc, Y.jQ_over]
  obtain ⟨g, hg⟩ : ∃ g : c.F →+* Ω,
      y₀ ≫ pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) = spMap g :=
    ⟨(Spec.preimage (y₀ ≫ pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom))).hom, by
      simp only [spMap, CommRingCat.ofHom_hom, Spec.map_preimage]⟩
  rw [h1, ← Category.assoc, hg] at hy
  have h2 : g.comp (algebraMap (𝓞 c.F) c.F) = cst.comp (algebraMap (𝓞 c.F) c.F) := by
    have h3 : spMap (g.comp (algebraMap (𝓞 c.F) c.F)) = spMap (cst.comp (algebraMap (𝓞 c.F) c.F)) := by
      rw [← hy]
      simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have h4 := Spec.map_injective h3
    exact congrArg CommRingCat.Hom.hom h4
  have h5 : g = cst := IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 c.F)) h2
  rw [pullback.condition, ← Category.assoc, hg, h5]
  simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem lieModel_transport : ∀ (S S₁ S₂ : Scheme.{0}) (G : Over S) (G₁ : Over S₁) (G₂ : Over S₂) [GrpObj G] [GrpObj G₁] [GrpObj G₂] (f₁ : S₁ ⟶ S) (f₂ : S₂ ⟶ S) (φ₁ : G₁.left ⟶ G.left) (φ₂ : G₂.left ⟶ G.left), IsGrpPullback G₁ G f₁ φ₁ → IsGrpPullback G₂ G f₂ φ₂ → ∀ (R : Type) [CommRing R] (x₁ : Sp R ⟶ S₁) (x₂ : Sp R ⟶ S₂), x₁ ≫ f₁ = x₂ ≫ f₂ → ∀ (V : Type) [AddCommGroup V] [Module R V] (M₁ : LieModel G₁ x₁ V) (O : Type) [CommRing O] (a₁ : O → (G₁ ⟶ G₁)) (a₂ : O → (G₂ ⟶ G₂)) (b : O → (G ⟶ G)) (ρ : O →+* Module.End R V), (∀ a, (a₁ a).left ≫ φ₁ = φ₁ ≫ (b a).left) → (∀ a, (a₂ a).left ≫ φ₂ = φ₂ ≫ (b a).left) → M₁.IsActOf a₁ ρ → ∃ M₂ : LieModel G₂ x₂ V, M₂.IsActOf a₂ ρ := by
  intro S S₁ S₂ G G₁ G₂ _ _ _ f₁ f₂ φ₁ φ₂ h₁ h₂ R _ x₁ x₂ hx V _ _ M₁ O _ a₁ a₂ b ρ ha₁ ha₂ hact
  obtain ⟨N, hN⟩ := (LiePull.lieModel_pullback S S₁ G G₁ f₁ φ₁ h₁ R x₁ V).2 M₁
  have key : ∀ (g : Sp R ⟶ S), x₂ ≫ f₂ = g → ∀ N : LieModel G g V,
      (∀ a e, (N.pt (ρ a e)).left = (N.pt e).left ≫ (b a).left) →
      ∃ M₂ : LieModel G₂ x₂ V, M₂.IsActOf a₂ ρ := by
    intro g hg N hNa
    subst hg
    obtain ⟨M₂, hM₂⟩ := (LiePull.lieModel_pullback S S₂ G G₂ f₂ φ₂ h₂ R x₂ V).1 N
    refine ⟨M₂, fun a e => ?_⟩
    apply Over.OverMorphism.ext
    apply h₂.1.hom_ext
    · rw [hM₂, hNa, Over.comp_left, Category.assoc, ha₂, ← Category.assoc, hM₂]
    · rw [Over.w, Over.comp_left, Category.assoc, Over.w, Over.w]
  refine key _ hx.symm N fun a e => ?_
  rw [← hN, ← hN, hact a e, Over.comp_left, Category.assoc, ha₁, Category.assoc]

theorem pt_sum {S : Scheme.{0}} {G : Over S} [GrpObj G] {k : Type} [Field k] {t : Sp k ⟶ S} {V : Type}
    [AddCommGroup V] [Module k V] (M : LieModel G t V) : ∀ {n : ℕ} (u : Fin n → V),
    M.pt (∑ i, u i) = (List.ofFn fun i => M.pt (u i)).prod
  | 0, u => by simp [M.pt_zero]
  | n + 1, u => by
    rw [Fin.sum_univ_succ, M.add, pt_sum M (fun i => u i.succ), List.ofFn_succ, List.prod_cons]

theorem finrank_eigSp_of_lieMult : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (k : Type) [Field k] (t : Sp k ⟶ S) (O : Type) [CommRing O] (act : OAct O G) (τ : O →+* k) (n : ℕ) (V : Type) [AddCommGroup V] [Module k V] (M : LieModel G t V) (ρ : O →+* Module.End k V), M.IsActOf act.act ρ → LieMult act t τ n → Module.finrank k (eigSp ρ τ) = n := by
  intro S G _ k _ t O _ act τ n V _ _ M ρ hact hL
  obtain ⟨v, hv, huq⟩ := hL
  have mem : ∀ e, e ∈ eigSp ρ τ ↔ ∀ a, ρ a e = τ a • e := by
    intro e
    simp [eigSp, Submodule.mem_iInf, sub_eq_zero]
  have eig : ∀ e, IsLieEigen act t τ (M.pt e) ↔ e ∈ eigSp ρ τ := by
    intro e
    rw [mem]
    constructor
    · intro h a
      apply M.inj
      apply Over.OverMorphism.ext
      rw [hact a e]
      exact (h.2 a).trans (M.smul (τ a) e).symm
    · intro h
      refine ⟨M.tan e, fun a => ?_⟩
      rw [← hact a e, h a]
      exact M.smul (τ a) e
  choose e he using fun i => M.onto (v i) (hv i).1
  have heW : ∀ i, e i ∈ eigSp ρ τ := fun i => (eig _).1 (by rw [he]; exact hv i)
  have hsat : ∀ c : Fin n → k, ∃ u : Fin n → (epsPt t ⟶ G),
      (∀ i, (u i).left = spMap (epsScale (c i)) ≫ (v i).left) ∧
        M.pt (∑ i, c i • e i) = (List.ofFn u).prod := by
    intro c
    refine ⟨fun i => M.pt (c i • e i), fun i => ?_, pt_sum M _⟩
    rw [← he i]
    exact M.smul (c i) (e i)
  have hsum : ∀ c : Fin n → k, (∑ i, c i • e i) ∈ eigSp ρ τ := fun c =>
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (heW i)
  have hli : LinearIndependent k e := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have h1 := hsat g
    rw [hg] at h1
    have h2 := hsat 0
    have z : ∑ i, (0 : Fin n → k) i • e i = 0 := by simp
    rw [z] at h2
    have h0 := (huq _ ((eig 0).2 (Submodule.zero_mem _))).unique h1 h2
    exact fun i => congrFun h0 i
  have hspan : eigSp ρ τ = Submodule.span k (Set.range e) := by
    apply le_antisymm
    · intro y hy
      obtain ⟨c, ⟨u, hu, hw⟩, -⟩ := huq _ ((eig y).2 hy)
      have hu' : u = fun i => M.pt (c i • e i) := by
        funext i
        apply Over.OverMorphism.ext
        rw [hu i, ← he i]
        exact (M.smul (c i) (e i)).symm
      have : y = ∑ i, c i • e i := by
        apply M.inj
        rw [hw, hu']
        exact (pt_sum M _).symm
      rw [this]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact heW i
  rw [hspan, finrank_span_eq_card hli, Fintype.card_fin]

theorem finrank_conj {K V O : Type} [Field K] [AddCommGroup V] [Module K V] {n : ℕ} (ev : V ≃ₗ[K] (Fin n → K))
    (r : O → (V →ₗ[K] V)) (χ : O → K) :
    Module.finrank K (⨅ a, LinearMap.ker
      ((ev.toLinearMap ∘ₗ r a ∘ₗ ev.symm.toLinearMap) - χ a • LinearMap.id) : Submodule K (Fin n → K)) =
    Module.finrank K (⨅ a, LinearMap.ker (r a - χ a • LinearMap.id) : Submodule K V) := by
  have heq : (⨅ a, LinearMap.ker
      ((ev.toLinearMap ∘ₗ r a ∘ₗ ev.symm.toLinearMap) - χ a • LinearMap.id) : Submodule K (Fin n → K)) =
      (⨅ a, LinearMap.ker (r a - χ a • LinearMap.id) : Submodule K V).map (ev : V →ₗ[K] (Fin n → K)) := by
    ext c
    rw [Submodule.mem_map_equiv]
    simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.id_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, sub_eq_zero]
    refine forall_congr' fun a => ?_
    constructor
    · intro h
      apply ev.injective
      rw [h, map_smul, LinearEquiv.apply_symm_apply]
    · intro h
      rw [h, map_smul, LinearEquiv.apply_symm_apply]
  rw [heq, LinearEquiv.finrank_map_eq]

theorem finrank_eigSp_baseChange : ∀ (k k' : Type) [Field k] [Field k'] [Algebra k k'] (O : Type) [CommRing O] (V V' : Type) [AddCommGroup V] [Module k V] [AddCommGroup V'] [Module k' V'] (n : ℕ) (b : Module.Basis (Fin n) k V) (j : V →+ V'), (∀ (a : k) e, j (a • e) = algebraMap k k' a • j e) → LinearIndependent k' (fun i => j (b i)) → Submodule.span k' (Set.range fun i => j (b i)) = ⊤ → ∀ (ρ : O →+* Module.End k V) (ρ' : O →+* Module.End k' V'), (∀ a e, ρ' a (j e) = j (ρ a e)) → ∀ σ : O →+* k, Module.finrank k (eigSp ρ σ) = Module.finrank k' (eigSp ρ' ((algebraMap k k').comp σ)) := by
  intro k k' _ _ _ O _ V V' _ _ _ _ n b j hjs hli hsp ρ ρ' hc σ
  let bL : Module.Basis (Fin n) k' V' := Module.Basis.mk hli hsp.ge
  have hbL : ∀ i, bL i = j (b i) := fun i => by simp [bL]
  have hsymm : ∀ c : Fin n → k, bL.equivFun.symm (algebraMap k k' ∘ c) = j (b.equivFun.symm c) := by
    intro c
    rw [Module.Basis.equivFun_symm_apply, Module.Basis.equivFun_symm_apply, map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [hjs, hbL]; rfl
  have hfwd : ∀ e, bL.equivFun (j e) = algebraMap k k' ∘ b.equivFun e := by
    intro e
    have h := hsymm (b.equivFun e)
    rw [LinearEquiv.symm_apply_apply] at h
    rw [← h, LinearEquiv.apply_symm_apply]
  have hL : ∀ a (c : Fin n → k),
      (bL.equivFun.toLinearMap ∘ₗ ρ' a ∘ₗ bL.equivFun.symm.toLinearMap) (algebraMap k k' ∘ c) =
      algebraMap k k' ∘ (b.equivFun.toLinearMap ∘ₗ ρ a ∘ₗ b.equivFun.symm.toLinearMap) c := by
    intro a c
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [hsymm, hc, hfwd]
  have h := ReciprocityTheory.ChartRestriction.G.Chart.finrank_eig_bc _ _ hL (fun a => σ a)
  rw [finrank_conj b.equivFun (fun a => ρ a) (fun a => σ a)] at h
  have h' := finrank_conj bL.equivFun (fun a => ρ' a) (fun a => algebraMap k k' (σ a))
  exact h.trans h'

end GlobalTheory.CompanionTheory.Ar.EigRank

namespace GlobalTheory.CompanionTheory.Ar.EigRank

theorem eig_finrank_label : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (X : Scheme.{0}) (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Sp Ω ⟶ X) (f : X ⟶ Y.X) (y₀ : Sp Ω ⟶ Xo.XF c) (t : SAB H X) (m : SABMap t Y.t f) (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel t.G ξ Li) (ρ : 𝓞 E →+* Module.End Ω Li) (cst : c.F →+* Ω), ξ ≫ f = y₀ ≫ Y.j → ξ ≫ f ≫ Y.s = spMap (cst.comp (algebraMap (𝓞 c.F) c.F)) → M.IsActOf t.act.act ρ → FiniteDimensional Ω Li ∧ ∀ s, Module.finrank Ω (eigSp ρ (cst.comp (labelEmb c s))) = labelRk D s := by
  intro E _ _ _ H D l Xo c Y X Ω _ _ ξ f y₀ t m Li _ _ M ρ cst hξ hs hact
  have : Smooth t.G.hom := t.semi.smooth
  have hfin : Module.Finite Ω Li := (GlobalTheory.T.lie_model_finite_projective X t.G Ω ξ Li M).1
  refine ⟨hfin, fun s => ?_⟩
  have : Smooth Y.oF.t.G.hom := Y.oF.t.semi.smooth
  obtain ⟨M₂, hM₂⟩ := lieModel_transport Y.X X (Xo.XF c) Y.t.G t.G Y.oF.t.G f Y.j m.cm.F Y.m.cm.F m.cart Y.m.cart
    Ω ξ y₀ hξ Li M (𝓞 E) t.act.act Y.oF.t.act.act Y.t.act.act ρ m.act Y.m.act hact
  let ic : Ω →+* AlgebraicClosure Ω := algebraMap Ω (AlgebraicClosure Ω)
  let x : Sp (AlgebraicClosure Ω) ⟶ Xo.XF c := Spec.map (CommRingCat.ofHom ic) ≫ y₀
  obtain ⟨E', _, _, ⟨M₃⟩⟩ := lieModel_exists (Xo.XF c) Y.oF.t.G (AlgebraicClosure Ω) x
  obtain ⟨ρ', hρ', -⟩ := lieModel_exists_unique_act _ Y.oF.t.G (AlgebraicClosure Ω) x E' M₃ (𝓞 E)
    Y.oF.t.act.act Y.oF.t.act.hom Y.oF.t.act.one Y.oF.t.act.mul Y.oF.t.act.add
  obtain ⟨j, hj, hjs, hjb⟩ := GlobalTheory.T.lie_model_base_change_map _ Y.oF.t.G Ω (AlgebraicClosure Ω) y₀ Li E' M₂ M₃
  obtain ⟨hli, hsp⟩ := hjb inferInstance _ (Module.finBasis Ω Li)
  have hc : ∀ a e, ρ' a (j e) = j (ρ a e) := by
    intro a e
    apply M₃.inj
    apply Over.OverMorphism.ext
    rw [hρ' a (j e), Over.comp_left, hj, hj, hM₂ a e, Over.comp_left, Category.assoc]
  have hbc := finrank_eigSp_baseChange Ω (AlgebraicClosure Ω) (𝓞 E) Li E' _ (Module.finBasis Ω Li) j hjs hli hsp ρ ρ' hc
    (cst.comp (labelEmb c s))
  let β : KA l →+* AlgebraicClosure Ω :=
    ic.comp (cst.comp (IntermediateField.inclusion c.le).toRingHom)
  have hy : y₀ ≫ Y.j ≫ Y.s = spMap (cst.comp (algebraMap (𝓞 c.F) c.F)) := by
    rw [← hs, ← Category.assoc y₀, ← hξ, Category.assoc]
  have hs' : x ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) ≫ Xo.s = spMap β := by
    show (Spec.map (CommRingCat.ofHom ic) ≫ y₀) ≫ _ = _
    rw [Category.assoc, structure_of_model_point E H D l Xo c Y Ω y₀ cst hy]
    simp only [spMap, β, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have hdet := (Y.oF.geom (AlgebraicClosure Ω) x β hs').1 (ic.comp (cst.comp (labelEmb c s)))
  have hne : β (baseKA l).ρ ≠ 0 := by
    intro h0
    have h1 := congrArg β (baseKA l).ρ_sq
    rw [map_pow, h0, map_neg, map_natCast] at h1
    have h2 : ((H.d : ℕ) : AlgebraicClosure Ω) = 0 := by
      have := h1.symm
      simpa using this
    exact H.d_prime.ne_zero (Nat.cast_eq_zero.mp h2)
  rw [hbc]
  cases s with
  | inl τ =>
    have e : (ic.comp (cst.comp (labelEmb c (Sum.inl τ)))) H.rt = β (baseKA l).ρ := by
      simp only [RingHom.comp_apply, (labelEmb_rt E H l c τ).1]
      rfl
    exact finrank_eigSp_of_lieMult _ Y.oF.t.G _ x _ Y.oF.t.act _ D.p E' M₃ ρ' hρ' (hdet.1 e)
  | inr τ =>
    have e : (ic.comp (cst.comp (labelEmb c (Sum.inr τ)))) H.rt = -β (baseKA l).ρ := by
      simp only [RingHom.comp_apply, (labelEmb_rt E H l c τ).2, map_neg]
      rfl
    have e' : (ic.comp (cst.comp (labelEmb c (Sum.inr τ)))) H.rt ≠ β (baseKA l).ρ := by
      rw [e]
      intro h
      apply hne
      have h2 : (2 : AlgebraicClosure Ω) * β (baseKA l).ρ = 0 := by
        linear_combination -h
      exact (mul_eq_zero.mp h2).resolve_left two_ne_zero
    exact finrank_eigSp_of_lieMult _ Y.oF.t.G _ x _ Y.oF.t.act _ D.q E' M₃ ρ' hρ' (hdet.2 e')

end GlobalTheory.CompanionTheory.Ar.EigRank
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsHodgeTateFunctionalStatement
section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_hodge_tate_functional : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (x : Spec (CommRingCat.of R) ⟶ S) (N : ℕ) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G x N i → Smooth G.hom → ∀ (L : Type) [AddCommGroup L] [Module R L] (M : LieModel G x L) (χ : T →* Rˣ), ∃ w : Module.Dual R L, Γ.IsHT i M N χ w := by
  first | exact @GlobalTheory.CompanionTheory.Relay.exists_hodge_tate_functional | exact GlobalTheory.CompanionTheory.Relay.exists_hodge_tate_functional | (intros; apply GlobalTheory.CompanionTheory.Relay.exists_hodge_tate_functional <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsProjectiveCoordModelStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase GlobalTheory.CompanionTheory.Ar.GeoModel
open GroundTheory.Heights₂.Heights.LowerBoundFree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_projective_coord_model : ∀ (Ω : Type) [Field Ω] [CharZero Ω] (X : Scheme.{0}) (ξ : Sp Ω ⟶ X) (N : ℕ) (x : Fin (N + 1) → Ω) (e : ℕ) (Ab : Set X), (∀ q : X, genPt ξ ⤳ q) → CoordTie ℤ ξ x → SncPts ξ e {p | Char0 ξ p ∧ p.1 ∉ Ab} → ∃ (K : Type) (_ : Fintype K) (J : K → Type) (_ : ∀ k, Fintype (J k)) (y : (Σ k, J k) → Ω) (M : PModel ℤ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩)) (g : M.X ⟶ X), Nonempty K ∧ GlobalTheory.CompanionTheory.Ar.Dominates M.ξ ξ g (RingHom.id Ω) ∧ Flat.NormalCpt M.ξ ∧ SncPts M.ξ e {p | Char0 M.ξ p ∧ g p.1 ∉ Ab} := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GeoModel.NormPatch.exists_normal_model | exact GlobalTheory.CompanionTheory.Ar.GeoModel.NormPatch.exists_normal_model | (intros; apply GlobalTheory.CompanionTheory.Ar.GeoModel.NormPatch.exists_normal_model <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsSncModelOfPatches
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.SncBase.Mdl

theorem ratEval_mem {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {N : ℕ} {x : Fin (N + 1) → Ω}
    {c : Fin (N + 1)} {p : Cpt ξ} (hc : InChart ξ x c p) (g : MRing (fun _ : Unit => Fin (N + 1))) :
    ratEval x c g ∈ regAt ξ p := by
  induction g using MvPolynomial.induction_on with
  | C a => simpa using intCast_mem (regAt ξ p) a
  | add a b ha hb => simpa using (regAt ξ p).add_mem ha hb
  | mul_X a i ha =>
    simpa using (regAt ξ p).mul_mem ha (hc.2 i.2)

theorem not_unitAt_of_mem_span {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {N : ℕ}
    {x : Fin (N + 1) → Ω} {B : Set (Cpt ξ)} (hξ : IsCptGen ξ) {c : Fin (N + 1)} {p : Cpt ξ} (hp : p ∈ B)
    (hc : InChart ξ x c p) {g : MRing (fun _ : Unit => Fin (N + 1))} (hg : g ∈ Ideal.span (bdGens ξ x B)) :
    ¬ unitAt ξ p (ratEval x c g) := by
  induction hg using Submodule.span_induction with
  | mem G hG =>
    obtain ⟨d, -, h⟩ := hG
    exact h c p hp hc
  | zero => simpa [unitAt] using fun h : (0 : Ω) ≠ 0 => absurd rfl h
  | add a b _ _ ha hb =>
    have := not_unitAt_add hξ (ratEval_mem hc a) (ratEval_mem hc b) ha hb
    simpa using this
  | smul a b _ hb =>
    intro h
    have e : ratEval x c (a • b) = ratEval x c a * ratEval x c b := by simp
    rw [e] at h
    exact hb (unitAt_of_mul_right h (ratEval_mem hc a) (ratEval_mem hc b))

theorem patch_invAdj {Ω : Type} [Field Ω] [Algebra ℚ Ω] {Pt Bd : Set (Subring Ω)} {e : ℕ} {A : Subalgebra ℚ Ω}
    {z : Fin e → A} {n : ℕ} (hA : IsSncPatch Pt Bd e A z n) {g : Ω} (hg : g ∈ A) (h0 : g ≠ 0) :
    ∃ z' : Fin e → invAdj A g, IsSncPatch Pt Bd e (invAdj A g) z' n ∧ ∀ i, (z' i : Ω) = z i := by
  let z' : Fin e → invAdj A g := fun i => ⟨z i, le_invAdj A g (z i).2⟩
  have hd := GlobalTheory.T.kaehler_basis_adjoin_inverse Ω A g hg h0 e z z' (fun _ => rfl) hA.li hA.span
  refine ⟨z', ⟨?_, GlobalTheory.T.smooth_adjoin_inverse Ω A g hg h0 hA.smooth, hA.le, hd.1, hd.2, ?_⟩, fun _ => rfl⟩
  · obtain ⟨S, hS⟩ := hA.fg
    classical
    refine ⟨insert g⁻¹ S, ?_⟩
    rw [Finset.coe_insert]
    apply le_antisymm
    · refine Algebra.adjoin_mono (Set.insert_subset_insert ?_)
      rw [← hS]
      exact Algebra.subset_adjoin
    · refine Algebra.adjoin_le (Set.insert_subset (Algebra.subset_adjoin (Set.mem_insert _ _)) ?_)
      rw [← hS]
      exact Algebra.adjoin_mono (Set.subset_insert _ _)
  · intro q hq
    obtain ⟨R, hR, hloc, hbd⟩ := hA.pts (primeUnder A g q) (Ideal.comap_isPrime _ _)
    refine ⟨R, hR, isLocAt_invAdj hg h0 hq hloc, hbd.trans ?_⟩
    exact exists_congr fun i => and_congr_right fun _ => Iff.rfl

theorem chartQ_fg {Ω : Type} [Field Ω] [Algebra ℚ Ω] {N : ℕ} (x : Fin (N + 1) → Ω) (c : Fin (N + 1)) :
    (chartQ x c).FG :=
  ⟨(Set.finite_range (fun j => x j / x c)).toFinset, by simp⟩

theorem not_mem_primeUnder {Ω : Type} [Field Ω] [Algebra ℚ Ω] {A : Subalgebra ℚ Ω} {g : Ω} (hg : g ∈ A) (h0 : g ≠ 0)
    {q : Ideal (invAdj A g)} (hq : q.IsPrime) : (⟨g, hg⟩ : A) ∉ primeUnder A g q :=
  not_mem_of_isPrime hg h0 hq

variable {Ω : Type} [Field Ω] [CharZero Ω] {X : Scheme.{0}} {ξ : Sp Ω ⟶ X}

theorem exists_patch {N : ℕ} {x : Fin (N + 1) → Ω} {e : ℕ} {B : Set (Cpt ξ)} (hT : CoordTie ℤ ξ x)
    (hP : ∀ p, Char0 ξ p → ∃ (A : Subalgebra ℚ Ω) (z : Fin e → A) (n : ℕ) (q : Ideal A),
      IsSncPatch (Pts ξ) (regAt ξ '' B) e A z n ∧ q.IsPrime ∧ IsLocAt A q (regAt ξ p))
    (c : Fin (N + 1)) (p : Cpt ξ) (hp : Char0 ξ p) (hc : InChart ξ x c p) :
    ∃ h ∈ chartQ x c, unitAt ξ p h ∧ ∃ (z : Fin e → invAdj (chartQ x c) h) (n : ℕ),
      IsSncPatch (Pts ξ) (regAt ξ '' B) e (invAdj (chartQ x c) h) z n := by
  obtain ⟨A, z, n, q, hA, hq, hl⟩ := hP p hp
  obtain ⟨I, hI, hu, hIl⟩ := GlobalTheory.T.component_gives_chart_prime Ω X ξ _ x c hT p hp hc
  obtain ⟨g, h, hg, hh, he⟩ := GlobalTheory.T.localizations_equal_basic_opens Ω A (chartQ x c) q I (regAt ξ p) hA.fg (chartQ_fg x c) hq hI hl hIl
  have hg0 : (g : Ω) ≠ 0 := fun h0 => hg (by
    have : g = 0 := Subtype.ext h0
    rw [this]; exact q.zero_mem)
  obtain ⟨z', hz', -⟩ := patch_invAdj hA g.2 hg0
  refine ⟨h, h.2, (hu h).1 hh, ?_⟩
  rw [← he]
  exact ⟨z', n, hz'⟩

theorem primePoint {κ : Type} {x : κ → Ω} {c : κ} (hT : CoordTie ℤ ξ x) (hx : x c ≠ 0) {h : Ω}
    (hh : h ∈ chartQ x c) (h0 : h ≠ 0) (q : Ideal (invAdj (chartQ x c) h)) (hq : q.IsPrime) :
    ∃ p : Cpt ξ, Char0 ξ p ∧ InChart ξ x c p ∧ unitAt ξ p h ∧
      (∀ s : invAdj (chartQ x c) h, s ∉ q ↔ unitAt ξ p (s : Ω)) ∧
      IsLocAt (invAdj (chartQ x c) h) q (regAt ξ p) := by
  obtain ⟨p, hp, hc, hu, hl⟩ := GlobalTheory.T.chart_prime_gives_component Ω X ξ κ x c hT hx (primeUnder _ h q) (Ideal.comap_isPrime _ _)
  have hhu : unitAt ξ p h := (hu ⟨h, hh⟩).1 (not_mem_primeUnder hh h0 hq)
  refine ⟨p, hp, hc, hhu, ?_, isLocAt_invAdj hh h0 hq hl⟩
  intro s
  obtain ⟨k, hk⟩ := exists_mul_pow_mem hh h0 s.2
  have hreg : (s : Ω) ∈ regAt ξ p := invAdj_le hp (fun _ => chartQ_le hp hc) hhu s.2
  rw [not_congr (mem_iff_mul_pow hh h0 hq s k ⟨_, hk⟩ rfl), hu]
  exact ⟨fun u => unitAt_of_mul_left u hreg (unitAt_pow hhu k).2.1, fun u => unitAt_mul u (unitAt_pow hhu k)⟩

theorem pointPrime {κ : Type} {x : κ → Ω} {c : κ} (hT : CoordTie ℤ ξ x) {h : Ω} (hh : h ∈ chartQ x c)
    (p : Cpt ξ) (hp : Char0 ξ p) (hc : InChart ξ x c p) (hu : unitAt ξ p h) :
    ∃ q : Ideal (invAdj (chartQ x c) h), q.IsPrime ∧
      (∀ s : invAdj (chartQ x c) h, s ∉ q ↔ unitAt ξ p (s : Ω)) ∧
      IsLocAt (invAdj (chartQ x c) h) q (regAt ξ p) := by
  haveI hloc : IsLocalRing (regAt ξ p) := (regAt_isLocalRing_isFractionRing_stalk X Ω ξ hT.gen p).1
  have hmem : ∀ s : invAdj (chartQ x c) h, (s : Ω) ∈ regAt ξ p :=
    fun s => invAdj_le hp (fun _ => chartQ_le hp hc) hu s.2
  let f : invAdj (chartQ x c) h →+* regAt ξ p :=
    ((invAdj (chartQ x c) h).val : invAdj (chartQ x c) h →+* Ω).codRestrict (regAt ξ p) hmem
  have hq : (Ideal.comap f (IsLocalRing.maximalIdeal (regAt ξ p))).IsPrime := inferInstance
  have hs : ∀ s : invAdj (chartQ x c) h,
      s ∉ Ideal.comap f (IsLocalRing.maximalIdeal (regAt ξ p)) ↔ unitAt ξ p (s : Ω) := by
    intro s
    rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]
    constructor
    · intro hu'
      obtain ⟨b, hb⟩ := hu'.exists_right_inv
      have e1 : (s : Ω) * (b : Ω) = 1 := congrArg Subtype.val hb
      have h0 : (s : Ω) ≠ 0 := fun h0 => by simp [h0] at e1
      refine ⟨h0, hmem s, ?_⟩
      rw [inv_eq_of_mul_eq_one_right e1]
      exact b.2
    · rintro ⟨h0, -, hinv⟩
      exact isUnit_iff_exists_inv.2 ⟨⟨_, hinv⟩, Subtype.ext (mul_inv_cancel₀ h0)⟩
  obtain ⟨I, -, hI, hIl⟩ := GlobalTheory.T.component_gives_chart_prime Ω X ξ κ x c hT p hp hc
  have e : primeUnder (chartQ x c) h (Ideal.comap f (IsLocalRing.maximalIdeal (regAt ξ p))) = I := by
    ext a
    exact not_iff_not.1 ((hs ⟨a, le_invAdj _ h a.2⟩).trans (hI a).symm)
  exact ⟨_, hq, hs, isLocAt_invAdj hh hu.1 hq (e ▸ hIl)⟩

theorem patchClause {κ : Type} {x : κ → Ω} {e : ℕ} {B : Set (Cpt ξ)} (hT : CoordTie ℤ ξ x)
    {S : Subalgebra ℚ Ω} {z : Fin e → S} {n : ℕ} (hS : IsSncPatch (Pts ξ) (regAt ξ '' B) e S z n)
    (q : Ideal S) (hq : q.IsPrime) (p : Cpt ξ) (hl : IsLocAt S q (regAt ξ p)) :
    p ∈ B ↔ ∃ i : Fin e, (i : ℕ) < n ∧ z i ∈ q := by
  obtain ⟨R, -, hRl, hbd⟩ := hS.pts q hq
  have hR : R = regAt ξ p := Subring.ext fun a => (hRl a).trans (hl a).symm
  subst hR
  rw [← hbd]
  constructor
  · exact fun hp => ⟨p, hp, rfl⟩
  · rintro ⟨p', hp', e'⟩
    have := GlobalTheory.T.regular_ring_determines_component X Ω ξ ℤ κ x hT p' p e'
    exact this ▸ hp'

end GlobalTheory.CompanionTheory.Ar.SncBase.Mdl

namespace GlobalTheory.CompanionTheory.Ar.SncBase

open Mdl in

theorem exists_isSncModel_of_patches : ∀ (Ω : Type) [Field Ω] [CharZero Ω] (X : Scheme.{0}) (ξ : Sp Ω ⟶ X) (N : ℕ) (x : Fin (N + 1) → Ω) (e : ℕ) (B : Set (Cpt ξ)), CoordTie ℤ ξ x → (∀ p ∈ B, Char0 ξ p) → (∀ p, Char0 ξ p → ∃ (A : Subalgebra ℚ Ω) (z : Fin e → A) (n : ℕ) (q : Ideal A), IsSncPatch (Pts ξ) (regAt ξ '' B) e A z n ∧ q.IsPrime ∧ IsLocAt A q (regAt ξ p)) → ∃ bd : Ideal (MRing (fun _ : Unit => Fin (N + 1))), Cmp.IsSncModel (fun p : (Σ _ : Unit, Fin (N + 1)) => x p.2) e bd ∧ ∀ (z : Spec (CommRingCat.of ℂ) ⟶ X) w, CoordsAt ξ (fun p : (Σ _ : Unit, Fin (N + 1)) => x p.2) z w → (w ∈ mcPts bd ↔ ∃ h : genPt ξ ⤳ centre z, (⟨centre z, h⟩ : Cpt ξ) ∈ B) := by
  intro Ω _ _ X ξ N x e B hT hB hP
  have hcov := fun c p hp hc => exists_patch (B := B) hT hP c p hp hc
  have hsep : ∀ c (p : Cpt ξ), Char0 ξ p → InChart ξ x c p → p ∉ B →
      ∃ G ∈ bdGens ξ x B, unitAt ξ p (ratEval x c G) := by
    intro c p hp hc hnB
    obtain ⟨h, hh, hu, z, n, hz⟩ := hcov c p hp hc
    have hcl : ∀ q : Cpt ξ, Char0 ξ q → InChart ξ x c q → unitAt ξ q h →
        (q ∈ B ↔ ∃ i : Fin e, (i : ℕ) < n ∧ ¬ unitAt ξ q (z i : Ω)) := by
      intro q hq hcq huq
      obtain ⟨Q, hQ, hs, hl⟩ := pointPrime hT hh q hq hcq huq
      rw [patchClause hT hz Q hQ q hl]
      refine exists_congr fun i => and_congr_right fun _ => ?_
      rw [← hs (z i), not_not]
    obtain ⟨a, ha, hau, hnon⟩ := GlobalTheory.T.snc_patch_boundary_units Ω X ξ _ x c B h e n z p hT.gen hB hh hu.1 hcl hp hc hu hnB
    exact GlobalTheory.T.boundary_generator_unit Ω X ξ N x c B p a hB hp hc ha hau hnon
  refine ⟨Ideal.span (bdGens ξ x B), ?_, GlobalTheory.T.boundary_points_coords Ω X ξ N x B hT.gen hsep⟩
  refine GlobalTheory.T.snc_model_from_local_patches Ω X ξ N x e B _ hcov ?_ ?_ ?_
  · intro c hx I hI
    obtain ⟨p, a, b, d, -⟩ := GlobalTheory.T.chart_prime_gives_component Ω X ξ _ x c hT hx I hI
    exact ⟨p, a, b, d⟩
  · intro c h hx hh h0 q hq
    obtain ⟨p, hp, hc, -, hs, hl⟩ := primePoint hT hx hh h0 q hq
    exact ⟨p, hp, hc, hs, fun z n hz => patchClause hT hz q hq p hl⟩
  · intro c p hp hc
    constructor
    · intro hpB g hg
      exact not_unitAt_of_mem_span hT.gen hpB hc hg
    · intro hall
      by_contra hn
      obtain ⟨G, hG, hu⟩ := hsep c p hp hc hn
      exact hall G (Ideal.subset_span hG) hu

end GlobalTheory.CompanionTheory.Ar.SncBase
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GagaLineGeneratorComplexStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gaga_line_generator_complex : GagaSections → ∀ (X : Scheme.{0}) (s : X ⟶ Sp ℂ) (Ω : Type) [Field Ω] [Algebra ℂ Ω] (ξ : Sp Ω ⟶ X) (L : Lat ξ Ω) (W : X.Opens) (F : (Sp ℂ ⟶ X) → ℂ), IsProper s → Smooth s → ξ ≫ s = spMap (algebraMap ℂ Ω) → IsCptGen ξ → ConstClosed ℂ Ω → L.IsVB 1 ⊤ → genPt ξ ∈ W → (∀ p : Cpt ξ, p.1 ∈ W → L.IsGenAt p 1) → (∀ (x : Sp ℂ ⟶ X) (h : genPt ξ ⤳ centre x), x ≫ s = spMap (RingHom.id ℂ) → ∃ t : Ω, L.IsGenAt ⟨centre x, h⟩ t ∧ ExtendsUnitAt s (RingHom.id ℂ) ξ W F t x) → ∃ (f : Ω) (κ : ℂ), κ ≠ 0 ∧ (∀ p : Cpt ξ, L.IsGenAt p f) ∧ ∀ y : Sp ℂ ⟶ X, y ≫ s = spMap (RingHom.id ℂ) → ⊤ ≤ y ⁻¹ᵁ W → genPt ξ ⤳ centre y → ValAt ξ y f (κ * F y) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.gaga_rat_C | exact GlobalTheory.CompanionTheory.Ar.Flat.gaga_rat_C | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.gaga_rat_C <;> assumption)
end

