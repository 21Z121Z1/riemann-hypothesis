import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0012
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LieMultIffExistsFrame
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0013
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0018
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0130
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0126
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0103
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0185
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0140
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0020
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0141
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0119
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0238
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0040
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0024
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.InvariantFunctionsDescend
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0008
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
import Development.AutomorphicSpectrum.Statements.GeometryStatements.KeyBadSt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsThetaMeanSquareNorm
import Development.AutomorphicSpectrum.Statements.GeometryStatements.ZhangDimensionPushDownGrassmannianHeightBounds
import GroundTheory.HeightsAndTheta.Heights.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsBundles
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0105
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EqZeroOfSmulEqZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsTransition
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0009
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.MemRangeOfIsAlgebraicRatFun
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.HodgeIPIffHodgeFormConj
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsDerivAt0CompLinMap
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0033
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0111
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0059
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianPartLieMultShift
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.AbMult

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem lieMult_iff_family {S : Scheme.{0}} {k : Type} [Field k] {G : Over S} [GrpObj G] {O : Type} [CommRing O]
    {V : Type} [AddCommGroup V] [Module k V] {x : Sp k ⟶ S} (M : LieModel G x V) (act : OAct O G)
    (ρ : O →+* Module.End k V) (h : M.IsActOf act.act ρ) (τ : O →+* k) (n : ℕ) :
    LieMult act x τ n ↔ ∃ b : Fin n → V, LinearIndependent k b ∧ Submodule.span k (Set.range b) = eigSp ρ τ := by
  rw [Fl.Test.lieMult_iff_exists_frame]
  constructor
  · rintro ⟨v, hv⟩
    choose e he using fun i => M.onto (v i) (hv.1 i).1
    obtain rfl : v = fun i => M.pt (e i) := funext fun i => (he i).symm
    exact ⟨e, (Fl.Test.isEigFrame_iff M act ρ h τ e).1 hv⟩
  · rintro ⟨b, hb⟩
    exact ⟨fun i => M.pt (b i), (Fl.Test.isEigFrame_iff M act ρ h τ b).2 hb⟩

theorem lieMult_abPart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) (t : SAB H S) (L : Type) [Field L] [CharZero L] (z : Sp L ⟶ S) (P : AbPart t z), ∃ r : ℕ, ∀ (k : Type) [Field k] [IsAlgClosed k] (g : L →+* k) (τ : 𝓞 E →+* k) (n : ℕ), LieMult P.tK.act (spMap g) τ n → r ≤ n ∧ LieMult P.tB.act (spMap g) τ (n - r) := by
  intro E _ _ _ H S t L _ _ z P
  letI := P.τ.addCommGroup
  letI := P.τ.grpB
  haveI := P.τ.free
  haveI := P.τ.finite
  haveI := P.τ.q_hom
  haveI := P.τ.i_hom
  haveI := P.e_hom
  haveI heinv : IsMonHom P.e.inv := inferInstance
  obtain ⟨m, hm⟩ := GlobalTheory.T.torus_extension_module_structure L P.tK.G P.τ (𝓞 E) P.tK.act (fun a => by
    haveI := P.tB.act.hom a
    refine ⟨P.e.hom ≫ P.tB.act.act a ≫ P.e.inv, inferInstance, ?_⟩
    refine (cancel_mono P.e.hom).1 ?_
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using P.act a)
  letI := m
  refine ⟨Module.finrank ℤ P.τ.X / Module.finrank ℚ E, ?_⟩
  intro k _ _ g τ n hn
  haveI : CharZero k := charZero_of_injective_ringHom g.injective
  obtain ⟨V₂, _, _, ⟨M₂⟩⟩ := lieModel_exists (Sp L) P.tK.G k (spMap g)
  obtain ⟨V₃, _, _, ⟨M₃⟩⟩ := lieModel_exists (Sp L) P.tB.G k (spMap g)
  let D := GlobalTheory.Diag.diagAct (Sp L) (𝓞 E) P.τ.X
  let M₁ := Fl.Test.torusModel (spMap g) P.τ.X
  obtain ⟨ρ₁, hρ₁, -⟩ := lieModel_exists_unique_act _ _ k (spMap g) _ M₁ (𝓞 E) D.act D.hom D.one D.mul D.add
  obtain ⟨ρ₂, hρ₂, -⟩ := lieModel_exists_unique_act _ _ k (spMap g) _ M₂ (𝓞 E) P.tK.act.act P.tK.act.hom
    P.tK.act.one P.tK.act.mul P.tK.act.add
  obtain ⟨ρ₃, hρ₃, -⟩ := lieModel_exists_unique_act _ _ k (spMap g) _ M₃ (𝓞 E) P.tB.act.act P.tB.act.hom
    P.tB.act.one P.tB.act.mul P.tB.act.add
  obtain ⟨f, hf, -⟩ := lieModel_exists_unique_diff _ _ _ k (spMap g) _ _ M₁ M₂ P.τ.i
  obtain ⟨h, hh, -⟩ := lieModel_exists_unique_diff _ _ _ k (spMap g) _ _ M₂ M₃ (P.τ.q ≫ P.e.hom)
  obtain ⟨hker, hsurj⟩ := GlobalTheory.T.torus_extension_tangent_exact L P.tK.G P.τ k g
  haveI hmono : Mono P.τ.i := ⟨fun a b hab => P.τ.isKernel.hom_ext hab (toUnit_unique _ _)⟩
  have finj : Function.Injective f := fun a b hab => M₁.inj ((cancel_mono P.τ.i).1 (by
    rw [← hf, ← hf, hab]))
  have hsur : Function.Surjective h := fun y => by
    obtain ⟨v, hv, hvq⟩ := hsurj (M₃.pt y ≫ P.e.inv) ((M₃.tan y).comp_monHom P.e.inv)
    obtain ⟨a, rfl⟩ := M₂.onto v hv
    refine ⟨a, M₃.inj ?_⟩
    rw [hh, ← Category.assoc, hvq, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hex : LinearMap.range f = LinearMap.ker h := by
    ext a
    rw [LinearMap.mem_range, LinearMap.mem_ker]
    have h1 : h a = 0 ↔ M₂.pt a ≫ P.τ.q = 1 := by
      constructor
      · intro h0
        have := hh a
        rw [h0, Fl.Test.pt_zero, ← Category.assoc] at this
        refine (cancel_mono P.e.hom).1 ?_
        rw [← this, MonObj.one_comp]
      · intro h0
        refine M₃.inj ?_
        rw [hh, ← Category.assoc, h0, MonObj.one_comp, Fl.Test.pt_zero]
    rw [h1, hker _ (M₂.tan a)]
    constructor
    · rintro ⟨c, rfl⟩
      exact ⟨M₁.pt c, M₁.tan c, (hf c).symm⟩
    · rintro ⟨w, hw, hwa⟩
      obtain ⟨c, rfl⟩ := M₁.onto w hw
      exact ⟨c, M₂.inj ((hf c).trans hwa)⟩
  have eqf : ∀ a c, f (ρ₁ a c) = ρ₂ a (f c) := fun a c => M₂.inj (by
    rw [hf, hρ₂ a (f c), hρ₁ a c, hf, Category.assoc, Category.assoc]
    exact congrArg (M₁.pt c ≫ ·) (hm a))
  have eqh : ∀ a c, h (ρ₂ a c) = ρ₃ a (h c) := fun a c => M₃.inj (by
    rw [hh, hρ₃ a (h c), hρ₂ a c, hh, Category.assoc, Category.assoc, Category.assoc]
    exact congrArg (M₂.pt c ≫ ·) (P.act a))
  obtain ⟨bas⟩ := GlobalTheory.T.eigenspace_basis_exists E P.τ.X k τ
  obtain ⟨b₁, hb₁, hb₁'⟩ := (lieMult_iff_family M₁ D ρ₁ hρ₁ τ _).1
    ((GlobalTheory.Diag.lieMult_iff (spMap g) τ _).2 ⟨bas⟩)
  obtain ⟨b₂, hb₂, hb₂'⟩ := (lieMult_iff_family M₂ P.tK.act ρ₂ hρ₂ τ n).1 hn
  obtain ⟨hle, b₃, hb₃⟩ := GlobalTheory.T.eigen_decomposition_exact_sequence E k _ _ _ ρ₁ ρ₂ ρ₃ f h finj hsur hex eqf eqh τ _ n b₁ b₂ hb₁ hb₁' hb₂ hb₂'
  exact ⟨hle, (lieMult_iff_family M₃ P.tB.act ρ₃ hρ₃ τ _).2 ⟨b₃, hb₃⟩⟩

end GlobalTheory.CompanionTheory.Ar.AbMult
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CubicalTripleTrivial
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.UU

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.CubeUnit

open GlobalTheory.CubicUnit

theorem eq_one_at_rational_points : ∀ (K : Type) [Field K] (G : Over (Sp K)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → TorusExtension G → ∀ (v : Γ((G ⊗ G ⊗ G).left, ⊤)ˣ), (∀ (T : Over (Sp K)) (x y : T ⟶ G), (lift (1 : T ⟶ G) (lift x y)).left.appTop.hom v.val = 1 ∧ (lift x (lift (1 : T ⟶ G) y)).left.appTop.hom v.val = 1 ∧ (lift x (lift y (1 : T ⟶ G))).left.appTop.hom v.val = 1) → ∀ x y w : 𝟙_ (Over (Sp K)) ⟶ G, (lift x (lift y w)).left.appTop.hom v.val = 1 := by
  intro K _ G _ _ hs τ v hv x₀ y₀ w₀
  letI := τ.addCommGroup
  haveI := τ.free
  letI := τ.grpB
  haveI := τ.q_hom
  haveI := τ.i_hom
  haveI := τ.q_flat
  haveI := τ.q_surjective
  haveI := τ.q_quasiCompact
  haveI := hs.smooth
  haveI := hs.geomConnected
  haveI hGc : ConnectedSpace G.left := (GlobalTheory.GroupConn.connectedSpace_group (Sp K) G).1
  haveI hYc : ConnectedSpace (G ⊗ G).left := GlobalTheory.GroupConn.connectedSpace_tensor G G
  haveI hsn : Smooth (snd G G).left := by
    show Smooth (pullback.snd G.hom G.hom)
    infer_instance
  haveI hsm : Smooth (G ⊗ G).hom := by
    rw [← Over.w (snd G G)]
    infer_instance
  haveI hYr : IsReduced (G ⊗ G).left := GlobalTheory.isReduced_of_smooth_of_isReduced (G ⊗ G).hom
  have hf1 : ∀ (T : Over (Sp K)) (x y : T ⟶ G), ev (lift (1 : T ⟶ G) (lift x y)) v = 1 :=
    fun T x y => Units.ext (hv T x y).1
  have hf2 : ∀ (T : Over (Sp K)) (x y : T ⟶ G), ev (lift x (lift (1 : T ⟶ G) y)) v = 1 :=
    fun T x y => Units.ext (hv T x y).2.1
  let m : splitTorus (Sp K) τ.X ⊗ (G ⊗ G) ⟶ G ⊗ (G ⊗ G) :=
    lift ((fst _ _ ≫ τ.i) * (snd _ _ ≫ fst _ _)) (lift (snd _ _ ≫ snd _ _) (toUnit _ ≫ w₀))
  have hm : ∀ (Z : Over (Sp K)) (t : Z ⟶ splitTorus (Sp K) τ.X) (x y : Z ⟶ G),
      lift t (lift x y) ≫ m = lift ((t ≫ τ.i) * x) (lift y (toUnit Z ≫ w₀)) := fun Z t x y => by
    simp [m, comp_lift, MonObj.comp_mul]
  obtain ⟨χ, hχ⟩ := GlobalTheory.CompanionTheory.TorusMono.torus_unit_eq_char_mul (Sp K) τ.X (G ⊗ G) (ev m v)
  have h1 : ∀ (Z : Over (Sp K)) (t : Z ⟶ splitTorus (Sp K) τ.X) (x y : Z ⟶ G),
      ev (lift ((t ≫ τ.i) * x) (lift y (toUnit Z ≫ w₀))) v =
        chV t χ * ev (lift x (lift y (toUnit Z ≫ w₀))) v := fun Z t x y => by
    have e : ev (lift t (lift x y)) (ev m v) =
        chV t χ * ev (lift (1 : Z ⟶ splitTorus (Sp K) τ.X) (lift x y)) (ev m v) :=
      Units.ext (hχ Z t (lift x y))
    rw [ev_comp, ev_comp, hm, hm, MonObj.one_comp, _root_.one_mul] at e
    exact e
  have h2 : ∀ (Z : Over (Sp K)) (t : Z ⟶ splitTorus (Sp K) τ.X), chV t χ = 1 := fun Z t => by
    have e := h1 Z t 1 1
    rw [hf2, hf2, _root_.mul_one] at e
    exact e.symm
  have h3 : ∀ (Z : Over (Sp K)) (t : Z ⟶ splitTorus (Sp K) τ.X) (x y : Z ⟶ G),
      ev (lift ((t ≫ τ.i) * x) (lift y (toUnit Z ≫ w₀))) v =
        ev (lift x (lift y (toUnit Z ≫ w₀))) v := fun Z t x y => by
    rw [h1, h2, _root_.one_mul]
  let s : G ⟶ G ⊗ (G ⊗ G) := lift (𝟙 G) (lift (toUnit G ≫ y₀) (toUnit G ≫ w₀))
  have hs' : ∀ (Z : Over (Sp K)) (g : Z ⟶ G),
      g ≫ s = lift g (lift (toUnit Z ≫ y₀) (toUnit Z ≫ w₀)) := fun Z g => by
    simp [s, comp_lift]
  have h8 : IsWt τ.i ⊤ (ev s v).val 0 := isWt_top_iff.2 fun Z t g => by
    rw [← ev_val, ← ev_val, ev_comp, ev_comp, hs', hs', h3, chV_zero, Units.val_one, _root_.one_mul]
  obtain ⟨c, hc⟩ := (invariant_functions_descend (Sp K) G τ.B _ τ.q τ.i τ.q_hom τ.i_hom τ.q_flat
    τ.q_surjective τ.q_quasiCompact τ.isKernel ⊤).2.2 (ev s v).val fun Z t g h₁ h₂ => by
      refine (h8 Z t g h₁ h₂).trans ?_
      rw [← chV_val, chV_zero, Units.val_one, _root_.one_mul]
      rfl
  obtain ⟨d, hd⟩ := (GlobalTheory.globalFns_holds (Sp K) τ.B τ.isAbelian).2 c
  have hud : (ev s v).val = G.hom.appTop.hom d := by
    rw [← Over.w τ.q, FunDescent.comp_appTop_apply, hd]
    exact hc.symm
  have hd1 : d = 1 := by
    have e : ev (1 : 𝟙_ (Over (Sp K)) ⟶ G) (ev s v) = 1 := by
      rw [ev_comp, hs', toUnit_unique (toUnit _) (𝟙 _), Category.id_comp, Category.id_comp]
      exact hf1 _ y₀ w₀
    have e := congrArg Units.val e
    rw [ev_val, hud, ← FunDescent.comp_appTop_apply, Over.w] at e
    simpa using e
  have hu : ev s v = 1 := by
    apply Units.ext
    rw [hud, hd1, map_one, Units.val_one]
  have e : ev x₀ (ev s v) = 1 := by
    rw [hu]
    exact map_one _
  rw [ev_comp, hs', toUnit_unique (toUnit _) (𝟙 _), Category.id_comp, Category.id_comp] at e
  exact congrArg Units.val e

end GlobalTheory.CompanionTheory.Ar.CubeUnit
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsNonzeroSectionPpDataStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl GlobalTheory.CompanionTheory.Ar.Sl.KeyGen GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nonzero_section_pp_data : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (D : PPData H L), ∃ t : SecMod D.t.G.hom (LB.LinComb D.t.PP.L (K := Fin 1) (fun _ => 𝟙 _) (fun _ => ((1 : ℕ) : ℤ))), t ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg.exists_sec_ne_zero_int | exact GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg.exists_sec_ne_zero_int | (intros; apply GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg.exists_sec_ne_zero_int <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsNthRootHomomorphismStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nth_root_homomorphism : ∀ (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (n : ℕ) (A B : Out.PolAV (Sp (𝓞 K))) (f : A.A ⟶ B.A), IsMonHom f → 0 < n → (∀ x : Over.mk (spMap (σ.comp (algebraMap (𝓞 K) K))) ⟶ A.A, x ^ n = 1 → x ≫ f = 1) → ∃ f' : A.A ⟶ B.A, IsMonHom f' ∧ f' ^ n = f := by
  first | exact @GlobalTheory.CompanionTheory.Relay.exists_nth_root_homomorphism | exact GlobalTheory.CompanionTheory.Relay.exists_nth_root_homomorphism | (intros; apply GlobalTheory.CompanionTheory.Relay.exists_nth_root_homomorphism <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsPPowerLevelFromPrimesAboveP
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.SplitEx

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l}

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  rw [← Spec.map_comp]; rfl

theorem isPreimmersion_fst (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) :
    IsPreimmersion (pullback.fst Y.s (spMap (algebraMap (𝓞 c.F) c.F))) := by
  have b₁ : IsPreimmersion (spMap (algebraMap (𝓞 c.F) c.F)) :=
    IsPreimmersion.of_isLocalization (nonZeroDivisors (𝓞 c.F)) (S := c.F)
  exact MorphismProperty.of_isPullback (P := @IsPreimmersion) (IsPullback.of_hasPullback _ _).flip b₁

theorem mem_of_dense_of_isOpen {X : Type*} [TopologicalSpace X] [TopologicalSpace.NoetherianSpace X] [QuasiSober X]
    [T0Space X] {U : Set X} (hU : IsOpen U) (hd : Dense U) {x : X} (hx : ∀ z, z ⤳ x → z = x) : x ∈ U := by
  have hfin : (irreducibleComponents X).Finite := TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
  have hgen : ∀ C ∈ irreducibleComponents X, x ∈ C → C = closure {x} := by
    intro C hC hxC
    have hg := hC.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents _ hC)
    have e := hx _ (hg.specializes hxC)
    rw [← e]
    exact hg.def.symm
  let T : Set X := ⋃ C ∈ irreducibleComponents X \ {closure {x}}, C
  have hT : IsClosed T := Set.Finite.isClosed_biUnion (hfin.subset Set.diff_subset)
    fun C hC => isClosed_of_mem_irreducibleComponents C hC.1
  have hxT : x ∈ Tᶜ := by
    intro h
    obtain ⟨C, ⟨hC, hne⟩, hxC⟩ := Set.mem_iUnion₂.1 h
    exact hne (hgen C hC hxC)
  obtain ⟨w, hwT, hwU⟩ := hd.inter_open_nonempty _ hT.isOpen_compl ⟨x, hxT⟩
  have hwC : w ∈ closure {x} := by
    by_contra hn
    refine hwT (Set.mem_iUnion₂.2 ⟨irreducibleComponent w,
      ⟨irreducibleComponent_mem_irreducibleComponents w, fun e => hn ?_⟩, mem_irreducibleComponent⟩)
    rw [← (show irreducibleComponent w = closure {x} from e)]
    exact mem_irreducibleComponent
  exact (specializes_iff_mem_closure.2 hwC).mem_open hU hwU

theorem injective_j (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) : Function.Injective Y.j := by
  have := isPreimmersion_fst Y
  have := Y.jQ_open
  have : IsPreimmersion Y.j := by unfold Model.j; infer_instance
  exact Y.j.isEmbedding.injective

theorem genPt_comp {X X' : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (g : X ⟶ X') :
    genPt (ξ ≫ g) = g (genPt ξ) :=
  Scheme.Hom.comp_apply ξ g (IsLocalRing.closedPoint Ω : Spec (CommRingCat.of Ω))

theorem mem_range_j (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) {Ω : Type} [Field Ω]
    (ξ : Spec (CommRingCat.of Ω) ⟶ Y.X) (cst : c.F →+* Ω) (hmax : ∀ y, y ⤳ genPt ξ → y = genPt ξ)
    (hs : ξ ≫ Y.s = spMap (cst.comp (algebraMap (𝓞 c.F) c.F))) : genPt ξ ∈ Set.range Y.j := by
  have hpr := projProper _ _ _ Y.proj
  have sq : ξ ≫ Y.s = spMap cst ≫ spMap (algebraMap (𝓞 c.F) c.F) := by rw [hs, spMap_comp']
  let P := pullback Y.s (spMap (algebraMap (𝓞 c.F) c.F))
  let ξ₁ : Spec (CommRingCat.of Ω) ⟶ P := pullback.lift ξ (spMap cst) sq
  have hf : ξ₁ ≫ pullback.fst _ _ = ξ := pullback.lift_fst _ _ _
  let pt : Spec (CommRingCat.of Ω) := IsLocalRing.closedPoint Ω
  let x₁ : P := ξ₁ pt
  have h1 : pullback.fst Y.s (spMap (algebraMap (𝓞 c.F) c.F)) x₁ = genPt ξ := by
    have e := Scheme.Hom.comp_apply ξ₁ (pullback.fst Y.s (spMap (algebraMap (𝓞 c.F) c.F))) pt
    rw [hf] at e
    exact e.symm
  have a₁ := isPreimmersion_fst Y
  have hx₁ : ∀ z : P, z ⤳ x₁ → z = x₁ := by
    intro z hz
    apply (pullback.fst Y.s (spMap (algebraMap (𝓞 c.F) c.F))).isEmbedding.injective
    rw [h1]
    exact hmax _ (h1 ▸ hz.map (pullback.fst Y.s (spMap (algebraMap (𝓞 c.F) c.F))).continuous)
  have : LocallyOfFiniteType (pullback.snd Y.s (spMap (algebraMap (𝓞 c.F) c.F))) := inferInstance
  have : QuasiCompact (pullback.snd Y.s (spMap (algebraMap (𝓞 c.F) c.F))) := inferInstance
  have : IsLocallyNoetherian P := LocallyOfFiniteType.isLocallyNoetherian (pullback.snd Y.s (spMap (algebraMap (𝓞 c.F) c.F)))
  have : CompactSpace P := QuasiCompact.compactSpace_of_compactSpace (pullback.snd Y.s (spMap (algebraMap (𝓞 c.F) c.F)))
  have : IsNoetherian P := {}
  have := Y.jQ_open
  obtain ⟨v', hv'⟩ := mem_of_dense_of_isOpen Y.jQ.isOpenEmbedding.isOpen_range Y.jQ_dense hx₁
  exact ⟨v', by rw [Model.j, Scheme.Hom.comp_apply, hv', h1]⟩

theorem splitComps_of_fnAlgClosed (Y : Model Xo c (algebraMap (𝓞 c.F) c.F))
    (hc : Formalism.L2.Pj.FnAlgClosed Xo c) : SplitComps Y := by
  intro Ω _ ξ cst hξ hs a ha
  have hmax := CptInh.nogen ξ hξ
  obtain ⟨w₀, hw₀⟩ := mem_range_j Y ξ cst hmax hs
  have hwmax : ∀ y, y ⤳ w₀ → y = w₀ := by
    intro y hy
    have h1 : Y.j y ⤳ genPt ξ := hw₀ ▸ hy.map Y.j.continuous
    exact injective_j Y ((hmax _ h1).trans hw₀.symm)
  let Z : Formalism.L2.Pj.Comp Xo c := ⟨irreducibleComponent w₀, irreducibleComponent_mem_irreducibleComponents w₀⟩
  have hZ : Formalism.L2.Pj.genPt Z = w₀ := by
    have hC := irreducibleComponent_mem_irreducibleComponents w₀
    have hg := hC.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents _ hC)
    exact hwmax _ (hg.specializes mem_irreducibleComponent)
  have e : genPt (Formalism.L2.Pj.genSp Z ≫ Y.j) = genPt ξ := by
    refine (genPt_comp (Ω := Formalism.L2.Pj.kap Z) (Formalism.L2.Pj.genSp Z) Y.j).trans ?_
    rw [← hw₀, ← hZ]
    exact congrArg Y.j (Scheme.fromSpecResidueField_apply _ _)
  obtain ⟨i, hi⟩ := TowerOfTest.factor ξ hξ (Formalism.L2.Pj.genSp Z ≫ Y.j) e
  have hcomp : i.comp cst = algebraMap c.F (Formalism.L2.Pj.kap Z) := by
    have hsY : Y.j ≫ Y.s = pullback.snd _ _ ≫ spMap (algebraMap (𝓞 c.F) c.F) := by
      rw [Model.j, Category.assoc, pullback.condition, ← Category.assoc, Y.jQ_over]
    have h1 : Formalism.L2.Pj.genSp Z ≫ Formalism.L2.Pj.strK = spMap (algebraMap c.F (Formalism.L2.Pj.kap Z)) :=
      (Spec.map_preimage _).symm
    have h2 : spMap (algebraMap c.F (Formalism.L2.Pj.kap Z)) ≫ spMap (algebraMap (𝓞 c.F) c.F) =
        spMap i ≫ spMap (cst.comp (algebraMap (𝓞 c.F) c.F)) := by
      rw [← h1, ← hs]
      refine (Category.assoc _ _ _).trans ?_
      refine Eq.trans (congrArg (Formalism.L2.Pj.genSp Z ≫ ·) hsY.symm) ?_
      refine (Category.assoc _ _ _).symm.trans ?_
      exact (congrArg (· ≫ Y.s) hi).trans (Category.assoc _ _ _)
    have e0 : (i.comp cst).comp (algebraMap (𝓞 c.F) c.F) =
        (algebraMap c.F (Formalism.L2.Pj.kap Z)).comp (algebraMap (𝓞 c.F) c.F) := by
      apply TowerOfTest.spec_inj
      have : spMap ((i.comp cst).comp (algebraMap (𝓞 c.F) c.F)) =
          spMap i ≫ spMap (cst.comp (algebraMap (𝓞 c.F) c.F)) := by
        rw [RingHom.comp_assoc, spMap_comp']
      exact this.trans (h2.symm.trans (spMap_comp' _ _).symm)
    exact IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 c.F)) e0
  have hb : IsAlgebraic c.F (algebraMap (Formalism.L2.Pj.kap Z) (Formalism.L2.Pj.Om Z) (i a)) := by
    obtain ⟨p, hp0, hp⟩ := ha
    refine ⟨p.map (Int.castRingHom c.F), (Polynomial.map_ne_zero_iff (RingHom.injective_int _)).2 hp0, ?_⟩
    have h3 := Polynomial.hom_eval₂ p (algebraMap ℤ Ω) ((algebraMap (Formalism.L2.Pj.kap Z) (Formalism.L2.Pj.Om Z)).comp i) a
    rw [← Polynomial.aeval_def, hp, map_zero] at h3
    rw [Polynomial.aeval_def, Polynomial.eval₂_map]
    refine Eq.trans ?_ h3.symm
    exact congrArg (fun φ => Polynomial.eval₂ φ _ p) (Subsingleton.elim _ _)
  obtain ⟨k, hk⟩ := hc Z _ hb
  refine ⟨k, i.injective ?_⟩
  have h2 : algebraMap c.F (Formalism.L2.Pj.kap Z) k = i a := by
    apply (algebraMap (Formalism.L2.Pj.kap Z) (Formalism.L2.Pj.Om Z)).injective
    rw [← hk, ← IsScalarTower.algebraMap_apply]
  rw [← h2, ← hcomp]
  rfl

end GlobalTheory.CompanionTheory.Ar.SplitEx
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolUnifCompareIsogeny
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.HodgeUniq

open GlobalTheory.CompanionTheory.Ar.Flat.PerGram

variable {A A' : Over (Sp ℂ)} [GrpObj A] [GrpObj A']

theorem isDiff_comp {M : LB A.left} {M' : LB A'.left} {g g' : ℕ} (u : HolUnif A M g) (u' : HolUnif A' M' g')
    (d₂ : ∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v) (f : A' ⟶ A) (F : (Fin g' → ℂ) →ₗ[ℂ] (Fin g → ℂ))
    (hF : ∀ z, u.ex (F z) = u'.ex z ≫ f) {a' : Fin g' → ℂ} {x' : epsR ℂ ⟶ A'} (ht : IsTangent x')
    (hd : u'.IsDiff a' x') : u.IsDiff (F a') (x' ≫ f) := by
  obtain ⟨t, ⟨h₁, h₂⟩, -⟩ := d₂ (F a')
  have a1 := isDerivAt0_comp_linMap (isHolTo_ex u) F (isDerivAt0_of_isDiff u h₁ h₂)
  have a2 := GlobalTheory.FibreDeriv.isDerivAt0_comp (isDerivAt0_of_isDiff u' ht hd) f.left
  rw [show (fun z => (u.ex (F z)).left) = fun z => (u'.ex z).left ≫ f.left from
    funext fun z => by rw [hF, Over.comp_left]] at a1
  have e : t = x' ≫ f := Over.OverMorphism.ext (GlobalTheory.VerticalDeriv.isDerivAt0_unique a1 a2)
  exact e ▸ h₂

theorem tangent_of_iso (e : A' ≅ A) [IsMonHom e.hom] {x : epsR ℂ ⟶ A} {x' : epsR ℂ ⟶ A'} (hx : IsTangent x)
    (h : x' ≫ e.hom = x) : IsTangent x' := by
  have h' : x' = x ≫ e.inv := by rw [← h, Category.assoc, e.hom_inv_id, Category.comp_id]
  have h₁ : η[A'] ≫ e.hom = η[A] := IsMonHom.one_hom e.hom
  have h₂ : η[A] ≫ e.inv = η[A'] := by rw [← h₁, Category.assoc, e.hom_inv_id, Category.comp_id]
  unfold IsTangent at hx ⊢
  rw [h', Over.comp_left, ← Category.assoc, hx, ← Over.comp_left, h₂]

theorem hermForm_eq_of_pullbacks : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] (L : LB G.left) (z : Spec (CommRingCat.of ℂ) ⟶ X) (A A' : Over (Sp ℂ)) [GrpObj A] [GrpObj A'] (φ : A.left ⟶ G.left) (φ' : A'.left ⟶ G.left) (g g' : ℕ) (u : HolUnif A (L.pull φ) g) (u' : HolUnif A' (L.pull φ') g') (Hm : Matrix (Fin g) (Fin g) ℂ) (Hm' : Matrix (Fin g') (Fin g') ℂ) (χ : u.Λ → ℂ) (χ' : u'.Λ → ℂ), L.IsLB → IsAbelianScheme A → IsGrpPullback A G z φ → IsGrpPullback A' G z φ' → (∀ v, IsTangent v → ∃! w, u.IsDiff w v) → (∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v) → u.IsAH Hm χ → u'.IsAH Hm' χ' → ∀ (x y : epsR ℂ ⟶ A) (x' y' : epsR ℂ ⟶ A') (a b : Fin g → ℂ) (a' b' : Fin g' → ℂ), IsTangent x → IsTangent y → x'.left ≫ φ' = x.left ≫ φ → y'.left ≫ φ' = y.left ≫ φ → u.IsDiff a x → u.IsDiff b y → u'.IsDiff a' x' → u'.IsDiff b' y' → hermForm Hm' a' b' = hermForm Hm a b := by
  intro X G _ L z A A' _ _ φ φ' g g' u u' Hm Hm' χ χ' hL hAb hp hp' d₁ d₂ hAH hAH' x y x' y' a b a' b' hx hy hxx hyy
    da db da' db'
  obtain ⟨e, hmon, he⟩ := grpPullback_iso hp' hp
  haveI := hmon
  have hol : IsHolTo (Set.univ : Set (Fin g' → ℂ)) (fun w => (u'.ex w ≫ e.hom).left) := by
    simpa only [Over.comp_left] using GlobalTheory.HolTorsion.isHolTo_comp (isHolTo_ex u') e.hom.left
  obtain ⟨F, hF, -⟩ := GlobalTheory.existsUnique_linear_lift_of_isHolTo A hAb (L.pull φ) g g' u d₁ d₂
    (fun w => u'.ex w ≫ e.hom) (fun p q => by rw [u'.ex_add, MonObj.mul_comp]) hol
  have hΛ : ∀ l ∈ u'.Λ, F l ∈ u.Λ := fun l hl => (u.ker _).1 (by
    rw [hF, (u'.ker l).2 hl, MonObj.one_comp])
  have iso : LBIso (lbPow (L.pull φ') 1) (lbPow ((L.pull φ).pull e.hom.left) 1) :=
    GlobalTheory.lbIso_lbPow (GlobalTheory.GenSpread.lbIso_pull_pull hL e.hom.left he.symm) 1
  have hH := (GlobalTheory.appellHumbert_data_eq_of_lbIso_pow_pull A' A (L.pull φ') (L.pull φ) g' g u' u Hm' Hm χ' χ e.hom F hΛ 1
    one_pos (pull_isLB hL φ') (pull_isLB hL φ) hAH' hAH hF iso).1
  have coord : ∀ (v : epsR ℂ ⟶ A) (v' : epsR ℂ ⟶ A') (c : Fin g → ℂ) (c' : Fin g' → ℂ), IsTangent v →
      v'.left ≫ φ' = v.left ≫ φ → u.IsDiff c v → u'.IsDiff c' v' → F c' = c := fun v v' c c' hv hvv dc dc' => by
    have h : v' ≫ e.hom = v := Over.OverMorphism.ext (hp.1.hom_ext
      (by rw [Over.comp_left, Category.assoc, he, hvv]) (by rw [Over.w, Over.w]))
    have ht := tangent_of_iso e hv h
    exact (d₁ v hv).unique (h ▸ isDiff_comp u u' d₂ e.hom F hF ht dc') dc
  rw [hH, coord x x' a a' hx hxx da da', coord y y' b b' hy hyy db db']

end GlobalTheory.CompanionTheory.Ar.HodgeUniq
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolUnifPeriodMatrixLeftStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hol_unif_period_matrix_left : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] (t : SAB H (Sp R)) (g n : ℕ) (M : LieModel t.G (𝟙 (Sp R)) (Fin g → R)) (B : Set (Fin n → ℂ)) (ψ : (Fin n → ℂ) → (R →+* ℂ)) (e : Flat.FamExp t.G M B ψ) (b : Fin n → ℂ) (P : AbPart t (spMap (ψ b))) (A : Over (Sp ℂ)) (_ : GrpObj A) (φ : A.left ⟶ P.tB.G.left) (g' : ℕ) (u : HolUnif A (P.tB.PP.L.pull φ) g') (Hm : Matrix (Fin g') (Fin g') ℂ) (χ : u.Λ → ℂ), b ∈ B → IsGrpPullback A P.tB.G (𝟙 _) φ → u.IsAH Hm χ → IsPrincipal P.tB → ∃ ℓ : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ), GlobalTheory.CompanionTheory.Ar.QuotLoc.IsAbLift e b P φ u ℓ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.QuotLoc.exists_isAbLift | exact GlobalTheory.CompanionTheory.Ar.QuotLoc.exists_isAbLift | (intros; apply GlobalTheory.CompanionTheory.Ar.QuotLoc.exists_isAbLift <;> assumption)
end

