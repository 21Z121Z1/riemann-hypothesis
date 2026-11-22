import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0038
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0059
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.TorusUniformizationCompare
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0077
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0109
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0012
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0129
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0112
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0098
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0108
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0134
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0079
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0009
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AddJFintype
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0139
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0138

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionSectionEqOfConnected
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

namespace GlobalTheory.CompanionTheory.Ar.Flat

open GlobalTheory.HolTorsion in

theorem cubWeil_const_of_isHolTo_family : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (c : CubicalStr G L) (m N : ℕ) (B : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ X)) (x x' : ∀ b, Over.mk (y b) ⟶ G) (ζ : ℂˣ) (b₀ : Fin m → ℂ), 0 < N → IsOpen B → IsPreconnected B → b₀ ∈ B → IsHolTo B (fun b => (x b).left) → IsHolTo B (fun b => (x' b).left) → (∀ b ∈ B, x b ^ N = 1 ∧ x' b ^ N = 1 ∧ (x b).left ≫ G.hom = (x' b).left ≫ G.hom) → GlobalTheory.UU.CubWeil c N (x b₀) (x' b₀) (unitOn ζ) → ∀ b ∈ B, GlobalTheory.UU.CubWeil c N (x b) (x' b) (unitOn ζ) := by
  intro X G _ _ L c m N B y x x' ζ b₀ hN _ hB hb₀ hx hx' htor h₀ b₁ hb₁
  let o : X ⟶ G.left := (η[G] : 𝟙_ (Over X) ⟶ G).left
  have ho : o ≫ G.hom = 𝟙 X := Over.w (η[G] : 𝟙_ (Over X) ⟶ G)
  let mk : G ⟶ G := (𝟙 G) ^ N
  have hkill : ∀ (T : Over X) (u : T ⟶ G), u ^ N = 1 ↔ u.left ≫ mk.left = T.hom ≫ o := by
    intro T u
    have e₁ : u.left ≫ mk.left = (u ^ N).left := by
      rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id]
    have e₂ : T.hom ≫ o = (1 : T ⟶ G).left := by
      rw [Hom.one_def, Over.comp_left, Over.toUnit_left]
    rw [e₁, e₂]
    exact ⟨fun h => by rw [h], fun h => Over.OverMorphism.ext h⟩
  let p := pullback.fst mk.left o
  let q := pullback.snd mk.left o
  have H : IsPullback p q mk.left o := IsPullback.of_hasPullback _ _
  have hpq : p ≫ G.hom = q := by
    rw [← Over.w mk, ← Category.assoc, H.w, Category.assoc, ho, Category.comp_id]
  have hy : IsHolTo B y := isHolTo_congr (isHolTo_comp hx G.hom) fun b _ => (Over.w (x b)).symm
  obtain ⟨a, ha, hab⟩ := exists_isHolTo_lift H hx hy (fun b hb => (hkill _ _).1 (htor b hb).1) hb₀
  obtain ⟨a', ha', hab'⟩ := exists_isHolTo_lift H hx' hy (fun b hb => (hkill _ _).1 (htor b hb).2.1) hb₀
  obtain ⟨z, hz, hzb⟩ := exists_isHolTo_lift (IsPullback.of_hasPullback q q) ha ha'
    (fun b hb => (hab b hb).2.trans (hab' b hb).2.symm) hb₀
  let T : Over X := Over.mk (pullback.fst q q ≫ q)
  let u : T ⟶ G := Over.homMk (pullback.fst q q ≫ p) (by
    show (pullback.fst q q ≫ p) ≫ G.hom = pullback.fst q q ≫ q
    rw [Category.assoc, hpq])
  let v : T ⟶ G := Over.homMk (pullback.snd q q ≫ p) (by
    show (pullback.snd q q ≫ p) ≫ G.hom = pullback.fst q q ≫ q
    rw [Category.assoc, hpq, pullback.condition])
  have hu : u ^ N = 1 := (hkill T u).2 (by
    show (pullback.fst q q ≫ p) ≫ _ = (pullback.fst q q ≫ q) ≫ o
    rw [Category.assoc, H.w, Category.assoc])
  have hv : v ^ N = 1 := (hkill T v).2 (by
    show (pullback.snd q q ≫ p) ≫ _ = (pullback.fst q q ≫ q) ≫ o
    rw [Category.assoc, H.w, pullback.condition, Category.assoc])
  obtain ⟨e, he, -⟩ := GlobalTheory.UU.existsUnique_cubWeil c hu hv
  have hek : e.val ^ N = 1 := congrArg Units.val he.pow_eq_one
  have hpull : ∀ w ∈ B, GlobalTheory.UU.CubWeil c N (x w) (x' w) (Units.map (z w).appTop.hom.toMonoidHom e) := by
    intro w hw
    let h : Over.mk (y w) ⟶ T := Over.homMk (z w) (by
      show z w ≫ pullback.fst q q ≫ q = y w
      rw [← Category.assoc, (hzb w hw).1, (hab w hw).2])
    have e₁ : h ≫ u = x w := Over.OverMorphism.ext (by
      show z w ≫ pullback.fst q q ≫ p = _
      rw [← Category.assoc, (hzb w hw).1, (hab w hw).1])
    have e₂ : h ≫ v = x' w := Over.OverMorphism.ext (by
      show z w ≫ pullback.snd q q ≫ p = _
      rw [← Category.assoc, (hzb w hw).2, (hab' w hw).1])
    have := he.comp h
    rw [e₁, e₂] at this
    exact this
  have e₀ : Units.map (z b₀).appTop.hom.toMonoidHom e = unitOn ζ := (hpull b₀ hb₀).unique h₀
  have e₁ : Units.map (z b₁).appTop.hom.toMonoidHom e = Units.map (z b₀).appTop.hom.toMonoidHom e :=
    Units.ext ((val_map_appTop (z b₁) e.val).trans
      ((congrArg _ (valAt'_eq_of_pow_eq_one hz hB hN hek hb₀ hb₁)).trans (val_map_appTop (z b₀) e.val).symm))
  have := hpull b₁ hb₁
  rw [e₁, e₀] at this
  exact this

end GlobalTheory.CompanionTheory.Ar.Flat
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorusSplitPullbackGeneric
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.TorusUnif
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompanionTheory.Ar.TorusUnif

theorem torus_stratum_cocharacters_compare : ∀ (X Z' : Scheme.{0}) (G : Over X) [GrpObj G] (G' : Over Z') [GrpObj G'] (ρ : Z' ⟶ X)
    (Φ : G'.left ⟶ G.left), IsGrpPullback G' G ρ Φ → ∀ (Xc : Type) [AddCommGroup Xc] [Module.Free ℤ Xc] [Module.Finite ℤ Xc]
    (u : splitTorus Z' Xc ⟶ G') [IsMonHom u] (L k : Type) [Field L] [Field k] [Algebra L k] (x : Sp k ⟶ Z') (zL : Sp L ⟶ X),
    x ≫ ρ = spMap (algebraMap L k) ≫ zL → ∀ (GK : Over (Sp L)) [GrpObj GK] (φ : GK.left ⟶ G.left),
    IsGrpPullback GK G zL φ → ∀ τ : TorusExtension GK,
    (∀ (A : Type) [CommRing A] (g : k →+* A) (t : Over.mk (spMap g ≫ x) ⟶ splitTorus Z' Xc), t ≫ u = 1 → t = 1) →
    (∀ (Gk : Over (Sp k)) [GrpObj Gk] (ψ : Gk.left ⟶ G'.left), IsGrpPullback Gk G' x ψ → ∀ τ' : TorusExtension Gk,
      letI := τ'.grpB; ∀ (A : Type) [CommRing A] (g : k →+* A) (p : Over.mk (spMap g) ⟶ Gk),
        p ≫ τ'.q = 1 ↔ ∃ t : Over.mk (spMap g ≫ x) ⟶ splitTorus Z' Xc, (t ≫ u).left = p.left ≫ ψ) →
    letI := τ.addCommGroup
    ∃ e : τ.X ≃+ Xc, ∀ (A : Type) [CommRing A] (g : k →+* A) (b : Sp A ⟶ Z') (_ : spMap g ≫ x = b) (b' : Sp A ⟶ Sp L)
      (_ : spMap (g.comp (algebraMap L k)) = b') (t : Over.mk b ⟶ splitTorus Z' Xc) (t' : Over.mk b' ⟶ splitTorus (Sp L) τ.X),
      (∀ χ, charVal t' χ = charVal t (e χ)) → (t ≫ u).left ≫ Φ = (t' ≫ τ.i).left ≫ φ := by
  exact @PositivityTheory.Xgn.torus_uniformization_compare

end GlobalTheory.CompanionTheory.Ar.TorusUnif
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TowerI6OfReference
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Ht

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Ht.UpperTower

theorem proj_inl_mem {K₁ K₂ : Type} [Fintype K₁] [Fintype K₂] {ι₁ : K₁ → Type} {ι₂ : K₂ → Type}
    [∀ k, Fintype (ι₁ k)] [∀ k, Fintype (ι₂ k)] {Ω : Type} [Field Ω] (y₁ : (Σ k, ι₁ k) → Ω) (y₂ : (Σ k, ι₂ k) → Ω)
    {L : Type} [Field L] {z : (Σ k, joinIdx ι₁ ι₂ k) → L} (hz : z ∈ ptsOver L (mCoordIdeal (joinVec y₁ y₂))) :
    (fun p => z (joinInl ι₁ ι₂ p)) ∈ ptsOver L (mCoordIdeal y₁) := by
  refine ⟨fun k => hz.1 (Sum.inl k), fun f hf => ?_⟩
  have key : ∀ g : MRing ι₁, mConeMap (joinVec y₁ y₂) (rename (joinInl ι₁ ι₂) g) =
      rename (Sum.inl : K₁ → K₁ ⊕ K₂) (mConeMap y₁ g) := by
    intro g
    induction g using MvPolynomial.induction_on with
    | C a => simp
    | add p q hp hq => simp only [map_add, hp, hq]
    | mul_X p n hp =>
      simp only [map_mul, hp, rename_X]
      congr 1
      simp only [mConeMap, aeval_X, map_mul, rename_C, rename_X]
      rfl
  have hmem : rename (joinInl ι₁ ι₂) f ∈ mCoordIdeal (joinVec y₁ y₂) := by
    have hf' : mConeMap y₁ f = 0 := hf
    change mConeMap (joinVec y₁ y₂) (rename (joinInl ι₁ ι₂) f) = 0
    rw [key, hf', map_zero]
  have h := hz.2 _ hmem
  rw [aeval_rename] at h
  exact h

variable {Ψ : Type} [Fintype Ψ] {N : ℕ}

theorem weightAbsEntrySum_nonneg (mu : Wt Ψ N) : 0 ≤ l1 mu :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem l1_le_card_mul_norm (mu : Wt Ψ N) (h : ‖mu‖ ≤ 2) : l1 mu ≤ (Fintype.card Ψ : ℝ) * (N * 2) := by
  have h1 : ∀ τ i, |mu τ i| ≤ 2 := fun τ i =>
    ((norm_le_pi_norm (mu τ) i).trans (norm_le_pi_norm mu τ)).trans h
  calc l1 mu ≤ ∑ _τ : Ψ, ∑ _i : Fin N, (2 : ℝ) :=
        Finset.sum_le_sum fun τ _ => Finset.sum_le_sum fun i _ => h1 τ i
    _ = _ := by simp

theorem rootHt_le (R : RootModel Ψ N) (t : ℝ) (mu : Wt Ψ N) (s D : ℝ) (L : Type) [Field L] [NumberField L]
    (w : (Σ k, R.ι k) → L) (hw : ∀ j, |lineHt (R.line t j) L w| ≤ D) :
    rootHt R t mu s L w ≤ (l1 mu + |s|) * D := by
  have hD : 0 ≤ D := (abs_nonneg _).trans (hw none)
  have h1 : ∀ j, R.coef mu s j * lineHt (R.line t j) L w ≤ |R.coef mu s j| * D := fun j =>
    (le_abs_self _).trans (by rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hw j) (abs_nonneg _))
  refine (Finset.sum_le_sum fun j _ => h1 j).trans ?_
  rw [← Finset.sum_mul]
  refine mul_le_mul_of_nonneg_right ?_ hD
  rw [Fintype.sum_option, add_comm]
  refine add_le_add (le_of_eq ?_) ?_
  · simp [RootModel.coef, l1, Fintype.sum_prod_type]
  · have hk : (1 : ℝ) ≤ R.kA := by exact_mod_cast R.kA_pos
    simp only [RootModel.coef, abs_div, Nat.abs_cast]
    exact div_le_self (abs_nonneg _) hk

theorem line_smooth (R : RootModel Ψ N) (t : ℝ) : ∀ j, IsSmoothHerm (R.line t j)
  | some r => R.x_smooth t r
  | none => R.A_smooth

theorem tower_upper : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : RootTower Ψ N) (II : IntersectionSystem)
    (R : T.Comp → RootModel Ψ N), IsIntersectionSystem II → HasRef T R → T.I6 II := by
  intro Ψ _ _ N T II R hII href c₀ hc₀
  obtain ⟨C, s₀, hs₀, href⟩ := href
  obtain ⟨θ₁, hθ₁, hθ₁1, hwt⟩ := GlobalTheory.T.dominant_weight_gap_shift Ψ N T.j T.nu c₀ T.j_pos T.j_lt hc₀
  choose D hD using fun c : T.Comp =>
    GlobalTheory.T.bounded_height_points_dense (R c).K (R c).ι (R c).P _ (R c).arith _ ((R c).line 1) (line_smooth (R c) 1)
  set D' : ℝ := ∑ c, |D c| with hD'
  have hDle : ∀ c, D c ≤ D' := fun c =>
    (le_abs_self _).trans (Finset.single_le_sum (f := fun c => |D c|) (fun _ _ => abs_nonneg _) (Finset.mem_univ c))
  have hD'0 : 0 ≤ D' := Finset.sum_nonneg fun _ _ => abs_nonneg _
  set Λ : ℝ := (Fintype.card Ψ : ℝ) * (N * 2) + 1 with hΛ
  have hΛ0 : 0 ≤ Λ := by positivity
  refine ⟨min θ₁ s₀, lt_min hθ₁ hs₀, 2 * (Λ * D' + |C|) + Λ * |C|, ?_⟩
  intro B hB c lam θ s _ hlam hθ hθle hs hgap hcg
  have hθ1 : θ ≤ θ₁ := hθle.trans (min_le_left _ _)
  have hθs : θ ≤ s₀ := hθle.trans (min_le_right _ _)
  have hsθ : (s : ℝ) ≤ θ := by rw [hs]; nlinarith
  have hs0 : (0 : ℝ) < s := by rw [hs]; positivity
  obtain ⟨hdom, hnorm, -⟩ := hwt lam θ hlam hθ hθ1 hgap hcg
  rw [← hs] at hdom hnorm
  obtain ⟨i, u, hclose, harch⟩ := href B hB c
  have harch' := harch (T.lamS lam s) s hdom hnorm hs0 (hsθ.trans hθs)
  have hl : l1 (T.lamS lam s) + |(s : ℝ)| ≤ Λ := by
    rw [abs_of_pos hs0]
    exact add_le_add (l1_le_card_mul_norm _ hnorm) (by linarith)
  have hl0 : 0 ≤ l1 (T.lamS lam s) + |(s : ℝ)| := add_nonneg (weightAbsEntrySum_nonneg _) (abs_nonneg _)
  have hlog : 1 ≤ 2 * Real.log B := by
    have h2 : Real.log 2 ≤ Real.log B := Real.log_le_log (by norm_num) (by exact_mod_cast hB)
    have := Real.log_two_gt_d9
    linarith
  refine ⟨{W | (T.M B c).IsPt W ∧ T.mbarHt II B c lam s W ≤ (2 * (Λ * D' + |C|) + Λ * |C|) * Real.log B}, ?_,
    fun W hW => hW⟩
  intro f hf hfP
  obtain ⟨L, _, _, L', _, _, e, w, z, hz, hw, hQ, hze, hfz⟩ :=
    GlobalTheory.T.join_model_points_lift Ψ N (T.M B c) (R c) i
      (fun L _ w => ∀ _ : NumberField L, ∀ j, |lineHt ((R c).line 1 j) L w| ≤ D c)
      (fun g hg hgP => by
        obtain ⟨L, _, _, w, hw, hgw, hb⟩ := hD c g hg hgP
        exact ⟨L, inferInstance, inferInstance, w, hw, hgw, fun _ => hb⟩) f hf hfP
  have hz₁ : (fun p => z (joinInl (T.M B c).ι (R c).ι p)) ∈ ptsOver L' (T.M B c).P := proj_inl_mem _ _ hz
  obtain ⟨hA, hle, hmem, hht⟩ := GlobalTheory.T.number_field_point_height _ _ II hII _ _ (T.M B c).arith L' _ hz₁
  refine ⟨mCoordIdeal fun p => z (joinInl (T.M B c).ι (R c).ι p), ⟨⟨hA, hle⟩, ?_⟩, fun h => hfz ((hmem f hf).1 h)⟩
  have e1 : T.mbarHt II B c lam s (mCoordIdeal fun p => z (joinInl (T.M B c).ι (R c).ι p)) =
      rootHt (T.M B c) (scale s) (T.lamS lam s) s L' (fun p => z (joinInl (T.M B c).ι (R c).ι p)) := by
    simp only [RootTower.mbarHt, RootModel.ht, rootHt, Finset.sum_div, mul_div_assoc]
    exact Finset.sum_congr rfl fun j _ => by rw [hht _ (line_smooth _ _ j)]
  have hcl := (GlobalTheory.T.root_height_difference_bound Ψ N (T.M B c) (R c) i u _ _ _ _ _ _ hclose harch' L' z hz).2
  have hR : rootHt (R c) 1 (T.lamS lam s) s L' (fun p => z (joinInr (T.M B c).ι (R c).ι p)) ≤
      (l1 (T.lamS lam s) + |(s : ℝ)|) * D' := by
    refine rootHt_le _ _ _ _ _ _ _ fun j => ?_
    have h := GlobalTheory.T.line_height_invariant_scaling _ _ ((R c).line 1 j) L L' e w (fun _ => 1) hw.1 (fun _ => one_ne_zero)
    simp only [one_mul] at h
    rw [hze, h]
    exact (hQ inferInstance j).trans (hDle c)
  rw [e1]
  have hlog0 : 0 ≤ Real.log B := by linarith
  have b1 : (l1 (T.lamS lam s) + |(s : ℝ)|) * D' ≤ Λ * D' := mul_le_mul_of_nonneg_right hl hD'0
  have b2 : (l1 (T.lamS lam s) + |(s : ℝ)|) * (C * Real.log B) ≤ Λ * (|C| * Real.log B) :=
    (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (le_abs_self C) hlog0) hl0).trans
      (mul_le_mul_of_nonneg_right hl (mul_nonneg (abs_nonneg _) hlog0))
  have b3 : Λ * D' + |C| ≤ (Λ * D' + |C|) * (2 * Real.log B) :=
    le_mul_of_one_le_right (add_nonneg (mul_nonneg hΛ0 hD'0) (abs_nonneg _)) hlog
  have b4 := le_abs_self C
  linarith

end GlobalTheory.CompanionTheory.Ar.Ht.UpperTower
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.UnipotentEntriesFieldDegree
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagStep

namespace GlobalTheory.CompanionTheory.Ar.FlagStep.AdjoinLower

theorem adjoin_lower_eq_top : ∀ (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] [Algebra Ω₀ Ω] (S : Type) (r : S → ℕ)
    (u : ∀ σ, Matrix (Fin (r σ)) (Fin (r σ)) Ω),
    (∀ σ k, u σ k k = 1) → (∀ σ l k, l < k → u σ l k = 0) →
    Module.finrank (IntermediateField.adjoin Ω₀
      (Set.range fun q : Σ σ, Fin (r σ) × Fin (r σ) => u q.1 q.2.1 q.2.2)) Ω = 1 →
    IntermediateField.adjoin Ω₀
      (Set.range fun q : Σ σ, {lk : Fin (r σ) × Fin (r σ) // lk.2 < lk.1} => u q.1 q.2.1.1 q.2.1.2) = ⊤ := by
  intro Ω₀ Ω _ _ _ S r u hdiag hup hfin
  rw [IntermediateField.finrank_eq_one_iff_eq_top] at hfin
  rw [← hfin]
  apply le_antisymm
  · apply IntermediateField.adjoin.mono
    rintro _ ⟨⟨σ, ⟨l, k⟩, _⟩, rfl⟩
    exact ⟨⟨σ, l, k⟩, rfl⟩
  · rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨⟨σ, l, k⟩, rfl⟩
    rcases lt_trichotomy l k with h | h | h
    · simp only [hup σ l k h]
      exact zero_mem _
    · subst h
      simp only [hdiag σ l]
      exact one_mem _
    · exact IntermediateField.subset_adjoin _ _ ⟨⟨σ, ⟨l, k⟩, h⟩, rfl⟩

end GlobalTheory.CompanionTheory.Ar.FlagStep.AdjoinLower
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ValueLocallyRegularFunctionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.value_locally_regular_function : ∀ (X T : Scheme.{0}) (j : T ⟶ X) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X), IsCptGen ξ → ∀ (y₀ : Sp ℂ ⟶ T) (t : Ω) (r₀ : ℂ), ValAt ξ (y₀ ≫ j) t r₀ → ∃ W₁ : T.Opens, ⊤ ≤ y₀ ⁻¹ᵁ W₁ ∧ ∀ (V : T.Opens) (hV : IsAffineOpen V), V ≤ W₁ → ∃ g : Γ(T, V), ∀ (χ : Γ(T, V) →+* ℂ) (r : ℂ), ValAt ξ ((spMap χ ≫ hV.fromSpec) ≫ j) t r → r = χ g := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SectionNear.section_near | exact GlobalTheory.CompanionTheory.Ar.SectionNear.section_near | (intros; apply GlobalTheory.CompanionTheory.Ar.SectionNear.section_near <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.VectorsAtComplexPointStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vectors_at_complex_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (τ : E →+* ℂ) (σ : c.F →+* ℂ) (y : Sp ℂ ⟶ Xo.XF c) (v : Vecs y D.p) (w : Vecs y D.q) (v₀ : Fin D.p → (epsAt (y ≫ Y.j) ⟶ Y.t.G)) (w₀ : Fin D.q → (epsAt (y ≫ Y.j) ⟶ Y.t.G)), y ≫ pullback.snd _ _ = spMap σ → (∀ i, SameVec Y y (v i) (v₀ i)) → (∀ j, SameVec Y y (w j) (w₀ j)) → IsEigFrame Y.t.act (y ≫ Y.j) (σ.comp (tauIn c τ)) v₀ → IsEigFrame Y.t.act (y ≫ Y.j) (σ.comp (tauIn c (ComplexEmbedding.conjugate τ))) w₀ → IsFramed Set.univ τ σ y v w := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.isFramed_of_model | exact GlobalTheory.CompanionTheory.Ar.Flat.isFramed_of_model | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.isFramed_of_model <;> assumption)
end

