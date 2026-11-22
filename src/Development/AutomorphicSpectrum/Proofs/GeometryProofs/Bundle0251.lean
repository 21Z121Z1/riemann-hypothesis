import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0247
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0012
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsThetaMeanSquareNorm
import Development.AutomorphicSpectrum.Statements.GeometryStatements.ZhangDimensionPushDownGrassmannianHeightBounds
import GroundTheory.HeightsAndTheta.Heights.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsBundles
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsValLineLogNormAtIffEmbedding
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0077
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0245
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0091
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0080
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0059
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0083
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0242
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0165
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsDerivAt0CompLinMap
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0019
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.PFibreMahlerForms
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BoundaryChartHodgeMatrix
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCMFrame
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0212
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0179
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0145
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0114
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0203
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0200
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0028
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0206
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0063
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0223
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0248
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSheetCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.ThreeLeLevel
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0249
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianPartLieSignatureStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelian_part_lie_signature : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (L : Type) [Field L] [NumberField L] (z : Sp L ⟶ 𝔐.X) (P : AbPart 𝔐.t z), ∃ (ρ : L) (p' q' : ℕ), ρ ^ 2 = -(H.d : L) ∧ ∀ (k : Type) [Field k] [IsAlgClosed k] (g : L →+* k) (τ : 𝓞 E →+* k), (τ H.rt = g ρ → LieMult P.tB.act (spMap g) τ p') ∧ (τ H.rt ≠ g ρ → LieMult P.tB.act (spMap g) τ q') := by
  first | exact @GlobalTheory.CompanionTheory.Ar.AbPartConst.lieMult_constant_along_cmType | exact GlobalTheory.CompanionTheory.Ar.AbPartConst.lieMult_constant_along_cmType | (intros; apply GlobalTheory.CompanionTheory.Ar.AbPartConst.lieMult_constant_along_cmType <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArchimedeanFrameOfPullbackStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_frame_of_pullback : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (D : PPData H L) (σ : L →+* ℂ) (A : Over (Sp ℂ)) [GrpObj A] (φ : A.left ⟶ D.t.G.left) (g : ℕ) (u : HolUnif A (D.t.PP.L.pull φ) g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ), IsAbelianScheme A → IsGrpPullback A D.t.G (emb σ) φ → (∀ v, IsTangent v → ∃! w, u.IsDiff w v) → (∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v) → u.IsAH Hm χ → ∀ (a : D.Frame σ) (x : D.B.carrier) (c : Fin D.g → ℂ), D.IsVec a x c → D.len σ x ^ 2 = Real.pi * (a.herm c c).re := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Sl.FrameLen.len_sq_eq_pi_herm | exact GlobalTheory.CompanionTheory.Ar.Sl.FrameLen.len_sq_eq_pi_herm | (intros; apply GlobalTheory.CompanionTheory.Ar.Sl.FrameLen.len_sq_eq_pi_herm <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.BoundaryChartHodgeMatrixStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.boundary_chart_hodge_matrix : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (n a : ℕ) (C : BdryChart Xo σ n a) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo σ ty) (ρ : ℝ) (e : FamExp C.t.G C.M (ball 0 ρ) C.ψ), 0 < ρ → ρ ≤ 1 → ∃ (i : Fin FU.n) (Hf : (Fin n → ℂ) → Matrix (Fin C.g) (Fin C.g) ℂ), Module.finrank ℤ (FU.Di i).La = 2 * C.g ∧ (∀ z ∈ punct n a ρ, (Hf z).IsHermitian ∧ (∀ x : Fin C.g → ℂ, x ≠ 0 → 0 < (hermForm (Hf z) x x).re) ∧ C.IsRiem z (Hf z) ∧ ∀ (N : ℕ) (ζ : ℂˣ), 0 < N → ∀ x ∈ e.per z, ∀ x' ∈ e.per z, GlobalTheory.UU.CubWeil C.t.cub N (e.ex z ((N : ℂ)⁻¹ • x)) (e.ex z ((N : ℂ)⁻¹ • x')) (unitOn ζ) → (ζ : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * ((hermForm (Hf z) x x').im : ℂ) / N)) ∧ ∀ z₀ ∈ punct n a ρ, ∃ N : Set (Fin n → ℂ), IsOpen N ∧ z₀ ∈ N ∧ N ⊆ punct n a ρ ∧ ∃ P : (Fin n → ℂ) → ((FU.Di i).La →+ (Fin C.g → ℂ)), (∀ x, DifferentiableOn ℂ (fun z => P z x) N) ∧ ∀ z ∈ N, Function.Injective (P z) ∧ ((P z).range : Set (Fin C.g → ℂ)) = e.per z ∧ ∀ x y, (hermForm (Hf z) (P z x) (P z y)).im = (FU.Di i).EF x y := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.exists_marking | exact GlobalTheory.CompanionTheory.Ar.Flat.exists_marking | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.exists_marking <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CmPackEigenPeriodStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CM GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_pack_eigen_period : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n) (Z : ∀ b : Bool, Curve0 H (sgnRt H b)) (P : (FU.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (FU.Di i) ty P) (X : CMPack Z c FU i hP) (b : Bool) (τ : E →+* ℂ) (a : PureType.lat hP (sgnRt H b)) (v : epsAt (under X.y) ⟶ Xo.univ.t.G), X.IsCMVec b τ a v → IsDerivAt0 (fun s => (FU.ex i P s).left) ((Z b).z • tyPart ty τ (P a)) (spMap (dualMap (algebraMap X.K ℂ)) ≫ v.left) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fl.CoordPart.isDerivAt0_of_isCMVec | exact GlobalTheory.CompanionTheory.Ar.Fl.CoordPart.isDerivAt0_of_isCMVec | (intros; apply GlobalTheory.CompanionTheory.Ar.Fl.CoordPart.isDerivAt0_of_isCMVec <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CmPackProductFrameStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CM GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_pack_product_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n) (Z : ∀ b : Bool, Curve0 H (sgnRt H b)) (P : (FU.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (FU.Di i) ty P) (X : CMPack Z c FU i hP) (N : ℕ) (b : Fin g → Bool) (a : ∀ k, PureType.lat hP (sgnRt H (b k))) (V : Subring X.K) [IsLocalRing V], 0 < N → (∀ y : (FU.Di i).La, N • y ∈ Submodule.span (OK H) (Set.range fun k => (a k : (FU.Di i).La))) → (∀ s : 𝓞 X.K, (s : X.K) ∈ V) → IsUnit (N : V) → ∃ (T : SAB H (Sp V)) (m'' : SABMap X.t T (spMap (algebraMap V X.K))) (uV : Fin g → (epsAt (𝟙 (Sp V)) ⟶ T.G)), (∀ k, IsTanAt T.G _ (uV k)) ∧ (∀ w, IsTanAt T.G _ w → ∃! cc : Fin g → V, IsComb cc uV w) ∧ ∀ k u, X.IsImage (b k) (a k) u → ∃ s : Sp (DualNumber X.K) ⟶ X.t.G.left, s ≫ X.m.φ = u.left ∧ s ≫ m''.φ = spMap (dualMap (algebraMap V X.K)) ≫ (uV k).left := by
  first | exact @GlobalTheory.CompanionTheory.Relay.cm_pack_product_frame | exact GlobalTheory.CompanionTheory.Relay.cm_pack_product_frame | (intros; apply GlobalTheory.CompanionTheory.Relay.cm_pack_product_frame <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CmPackPureFrame
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CM GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.Fl

theorem mem_eigSp_iff_tyPart_eq_self {E : Type} [Field E] [NumberField E] {g : ℕ} (ty : Fin g → (E →+* ℂ)) (τ : E →+* ℂ)
    (ρ : 𝓞 E →+* Module.End ℂ (Fin g → ℂ)) (hρ : ∀ a w, ρ a w = fun k => ty k (a : E) * w k)
    (χ : 𝓞 E →+* ℂ) (hχ : ∀ a, χ a = τ (a : E)) (w : Fin g → ℂ) :
    w ∈ GlobalTheory.CompanionTheory.Ar.eigSp ρ χ ↔ tyPart ty τ w = w := by
  have hmem : w ∈ GlobalTheory.CompanionTheory.Ar.eigSp ρ χ ↔ ∀ a : 𝓞 E, ∀ k, ty k (a : E) * w k = τ (a : E) * w k := by
    simp only [GlobalTheory.CompanionTheory.Ar.eigSp, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
    refine forall_congr' fun a => ?_
    rw [hρ, hχ, funext_iff]
    rfl
  rw [hmem]
  constructor
  · intro h
    funext k
    unfold tyPart
    split_ifs with hk
    · rfl
    · have : ∃ a : 𝓞 E, ty k (a : E) ≠ τ (a : E) := by
        by_contra hc
        push Not at hc
        exact hk (IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) (RingHom.ext hc))
      obtain ⟨a, ha⟩ := this
      have h2 := h a k
      have : (ty k (a : E) - τ (a : E)) * w k = 0 := by rw [sub_mul, h2, sub_self]
      exact ((mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 ha)).symm
  · intro h a k
    by_cases hk : ty k = τ
    · rw [hk]
    · have : w k = 0 := by
        have := congrFun h k
        simp only [tyPart, hk, if_false] at this
        exact this.symm
      rw [this, mul_zero, mul_zero]

end GlobalTheory.CompanionTheory.Ar.Fl

namespace GlobalTheory.CompanionTheory.Ar.Fl.Frames

set_option maxHeartbeats 1000000 in

theorem _root_.GlobalTheory.CompanionTheory.Relay.cm_pack_pure_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n) (Z : ∀ b : Bool, Curve0 H (sgnRt H b)) (P : (FU.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (FU.Di i) ty P) (X : CMPack Z c FU i hP) (x : Fin D.p ⊕ Fin D.q → (FU.Di i).La) (hx : IsPure hP x) (τ : E →+* ℂ), IsTypeFn H D.p D.q ty → τ (H.rt : E) = H.rt0 → LinearIndependent (𝓞 E) x → (∃ v w, X.IsCMFrame τ hx v w) ∧ ∀ v w, X.IsCMFrame τ hx v w → IsFramed (Set.range X.y) τ X.β X.y v w := by
  intro E _ _ _ H D l Xo c g ty FU i Z P hP X x hx τ hty hτ hli

  have key : ∀ (b : Bool) (σ : E →+* ℂ) (n : ℕ) (T : Fin n → Fin g → ℂ) (v : Fin n → (epsAt (under X.y) ⟶ Xo.univ.t.G)),
      LinearIndependent ℂ T → (∀ w, w ∈ Submodule.span ℂ (Set.range T) ↔ tyPart ty σ w = w) →
      (∀ a, IsDerivAt0 (fun s => (FU.ex i P s).left) ((Z b).z • T a)
        (spMap (dualMap (algebraMap X.K ℂ)) ≫ (v a).left)) →
      IsEigFrame Xo.univ.t.act (under X.y) (X.β.comp (tauIn c σ)) v := by
    intro b σ n T v hT hspan hd
    obtain ⟨⟨v', hv'⟩, hiff⟩ := GlobalTheory.CompanionTheory.Relay.tangent_vectors_base_change E H _ Xo.univ.t X.K ℂ (algebraMap X.K ℂ) (under X.y) (FU.u i P)
      (X.β.comp (tauIn c σ)) n v X.pt.symm
    rw [hiff v' hv']
    obtain ⟨M, ρ, hact, hρ, hder, -⟩ := GlobalTheory.CompanionTheory.Relay.lie_model_with_cm_action E H D l Xo c g ty FU i P hP
    have hz := GlobalTheory.CompanionTheory.Ar.Fl.curve0_z_ne_zero E H _ (Z b)
    obtain ⟨-, huniq, -⟩ := GlobalTheory.isDerivAt0_ex_isTanAt E H D l Xo (algebraMap (KA l) ℂ) g ty FU i P hP
    have e : ∀ a, v' a = M.pt ((Z b).z • T a) := fun a => by
      obtain ⟨t, -, htu⟩ := huniq ((Z b).z • T a)
      have h1 : IsDerivAt0 (fun s => (FU.ex i P s).left) ((Z b).z • T a) (v' a).left := by
        rw [hv' a]; exact hd a
      exact Over.OverMorphism.ext ((htu _ h1).trans (htu _ (hder _)).symm)
    have ev : v' = fun a => M.pt ((Z b).z • T a) := funext e
    subst ev
    rw [((GlobalTheory.CompanionTheory.Ar.Fl.Bridge.comb_eig_frame _ ℂ _ _ _ M).2 (𝓞 E) Xo.univ.t.act ρ _ hact).2 n fun a => (Z b).z • T a]
    refine ⟨hT.units_smul fun _ => Units.mk0 _ hz, ?_⟩
    have hsp : Submodule.span ℂ (Set.range fun a => (Z b).z • T a) = Submodule.span ℂ (Set.range T) := by
      apply le_antisymm
      · exact Submodule.span_le.2 (by rintro _ ⟨a, rfl⟩; exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩))
      · refine Submodule.span_le.2 ?_
        rintro _ ⟨a, rfl⟩
        have : T a = ((Z b).z)⁻¹ • ((Z b).z • T a) := by rw [smul_smul, inv_mul_cancel₀ hz, one_smul]
        rw [SetLike.mem_coe, this]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
    rw [hsp]
    ext w
    rw [hspan, GlobalTheory.CompanionTheory.Ar.Fl.mem_eigSp_iff_tyPart_eq_self ty σ ρ hρ _ (fun a => rfl) w]
  have hpq : D.p + D.q = (FU.Di i).p + (FU.Di i).q := by rw [(FU.sig i).1, (FU.sig i).2]
  obtain ⟨⟨hl1, hs1⟩, hl2, hs2⟩ := GlobalTheory.CompanionTheory.Ar.Fl.tyPart_pure_family_bases E H (FU.Di i) g ty P hP D.p D.q x τ hty hpq hτ hx hli
  refine ⟨?_, fun v w hvw => ⟨X.hy, le_refl _, ?_, ?_⟩⟩
  · obtain ⟨M, ρ, lam, -, -, -, -, -, hcm⟩ := GlobalTheory.T.cm_lie_model_action E H D l Xo c g ty FU i Z P hP X
    exact ⟨fun a => M.pt (HT.eigProj ρ (X.β.comp (tauE c τ)) (lam true ⟨x (.inl a), hx.1 a⟩)),
      fun j => M.pt (HT.eigProj ρ (X.β.comp (tauE c (ComplexEmbedding.conjugate τ))) (lam false ⟨x (.inr j), hx.2 j⟩)),
      fun a => (hcm _ _ _ _).2 rfl, fun j => (hcm _ _ _ _).2 rfl⟩
  · exact key true τ D.p (fun a => tyPart ty τ (P (x (.inl a)))) v hl1 hs1
      fun a => GlobalTheory.CompanionTheory.Ar.Fl.CoordPart.isDerivAt0_of_isCMVec E H D l Xo c g ty FU i Z P hP X true τ _ (v a) (hvw.1 a)
  · exact key false (ComplexEmbedding.conjugate τ) D.q (fun j => tyPart ty (ComplexEmbedding.conjugate τ) (P (x (.inr j)))) w hl2 hs2
      fun j => GlobalTheory.CompanionTheory.Ar.Fl.CoordPart.isDerivAt0_of_isCMVec E H D l Xo c g ty FU i Z P hP X false (ComplexEmbedding.conjugate τ) _ (w j) (hvw.2 j)

end GlobalTheory.CompanionTheory.Ar.Fl.Frames
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CmPeriodAlgebraic
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open Matrix GlobalTheory GlobalTheory.CM GlobalTheory.CM.PeriodModel GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Fl.CMGiven

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem exists_desc (hU : ThetaUnifAV) (hL : Out.Laws) {D : Datum H} {l : Level H} {Xo : Moduli D l} {g : ℕ}
    {ty : Fin g → (E →+* ℂ)} (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n)
    {P : (FU.Di i).La →+ (Fin g → ℂ)} (hP : IsPeriod (FU.Di i) ty P)
    (k₀ : IntermediateField ℚ ℂ) [FiniteDimensional ℚ k₀] {ω₀ : k₀} (C₀ : Ell H k₀ ω₀)
    {ω' : ℂ} (C' : Ell H ℂ ω') {φ : C'.P.A.left ⟶ C₀.P.A.left} (c' : EllMap C' C₀ (algebraMap k₀ ℂ) φ)
    (u : HolUnif C'.P.A C'.P.L C'.P.g) (hu : PureType.IsThetaUnif u) {c : ℂ} (hc : c ≠ 0)
    (hΛ : PureType.IsQuadLattice u.Λ H.d c) {ρ : ℂ} (hρ : 2 * ω' - 1 = ρ) {ε : ℤˣ}
    (hε : 0 < ((ε : ℤ) : ℝ) * ω'.im) {h : (FU.Di i).La → (FU.Di i).La → OK H} (hh : IsKForm (FU.Di i) ε h)
    (T : PAT H (Sp k₀)) (T' : PAT H (Sp ℂ)) (n : SABMap T'.t Xo.univ.t (FU.u i P))
    (mT : SABMap T'.t T.t (spMap (algebraMap k₀ ℂ))) :
    ∃ k₁ : IntermediateField ℚ ℂ, FiniteDimensional ℚ k₁ ∧ k₀ ≤ k₁ ∧
      ∀ (K : IntermediateField ℚ ℂ) (e : k₀ ≤ K), k₁ ≤ K → ∀ (ω₂ : K) (C₂ : Ell H K ω₂)
        (φ₂ : C₂.P.A.left ⟶ C₀.P.A.left) (φ₃ : C'.P.A.left ⟶ C₂.P.A.left) (T₂ : PAT H (Sp K))
        (m₂ : SABMap T₂.t T.t (spMap (IntermediateField.inclusion e).toRingHom))
        (m₃ : SABMap T'.t T₂.t (spMap (algebraMap K ℂ))) (f : Sp K ⟶ Xo.X) (m : SABMap T₂.t Xo.univ.t f),
        EllMap C₂ C₀ (IntermediateField.inclusion e).toRingHom φ₂ → EllMap C' C₂ (algebraMap K ℂ) φ₃ →
        φ₃ ≫ φ₂ = φ → m₃.φ ≫ m₂.φ = mT.φ → m₃.φ ≫ m.φ = n.φ →
        ∃ ψ : PureType.lat hP ρ → (C₂.P.A ⟶ T₂.t.G), IsFam C₂ T₂ h _ ψ ∧
          ∀ a (z : ℂ), ((u.ex fun _ => c * z).left ≫ φ₃ ≫ (ψ a).left) ≫ m.φ = (FU.ex i P (z • P a)).left := by
  subst hρ
  obtain ⟨ψ', hψ', hex⟩ := GlobalTheory.T.exists_cmCurve_homFamily_to_fibre_at_period hU hL E H D l Xo g ty FU i P hP _ C' u c T' n ε _ hu hc hΛ hε hh
  obtain ⟨k₁, hk₁, hle, hdesc⟩ := GlobalTheory.T.cmFamily_descends_to_numberField hU hL E H k₀ _ C₀ (FU.Di i) _ T _ _ C' φ T' mT ψ' c' hψ'
  refine ⟨k₁, hk₁, hle, fun K e eK ω₂ C₂ φ₂ φ₃ T₂ m₂ m₃ f m c₂ c₃ hφ hm hn => ?_⟩
  obtain ⟨ψ₂, hψ₂, hsq⟩ := hdesc K e eK _ C₂ φ₂ φ₃ T₂ m₂ m₃ c₂ c₃ hφ hm
  refine ⟨ψ₂, hψ₂, fun a z => ?_⟩
  rw [← hex, ← hn, ← Category.assoc _ m₃.φ, Over.comp_left, Category.assoc _ _ m₃.φ]
  exact congrArg (fun q => (_ ≫ q) ≫ m.φ) (hsq a).symm

theorem exists_tower (hB : Out.PolBaseChangeSt) {M k₀ K : IntermediateField ℚ ℂ} [NumberField M] [NumberField K]
    (e₂ : M ≤ k₀) (e₅ : k₀ ≤ K) {ω : 𝓞 M} (C : Ell H (𝓞 M) ω) {ω₀ : k₀} (C₀ : Ell H k₀ ω₀)
    {φ₀ : C₀.P.A.left ⟶ C.P.A.left}
    (c₀ : EllMap C₀ C ((IntermediateField.inclusion e₂).toRingHom.comp (algebraMap (𝓞 M) M)) φ₀)
    {ω' : ℂ} (C' : Ell H ℂ ω') {φ : C'.P.A.left ⟶ C₀.P.A.left} (c' : EllMap C' C₀ (algebraMap k₀ ℂ) φ) :
    ∃ (ω₁ : 𝓞 K) (C₁ : Ell H (𝓞 K) ω₁) (φ₁ : C₁.P.A.left ⟶ C.P.A.left) (ω₂ : K) (C₂ : Ell H K ω₂)
      (φ₁₂ : C₂.P.A.left ⟶ C₁.P.A.left) (φ₂ : C₂.P.A.left ⟶ C₀.P.A.left) (φ₃ : C'.P.A.left ⟶ C₂.P.A.left),
      EllMap C₁ C (RingOfIntegers.mapRingHom (IntermediateField.inclusion (e₂.trans e₅)).toRingHom) φ₁ ∧
      EllMap C₂ C₁ (algebraMap (𝓞 K) K) φ₁₂ ∧ EllMap C₂ C₀ (IntermediateField.inclusion e₅).toRingHom φ₂ ∧
      EllMap C' C₂ (algebraMap K ℂ) φ₃ ∧ φ₃ ≫ φ₂ = φ ∧ φ₁₂ ≫ φ₁ = φ₂ ≫ φ₀ := by
  obtain ⟨C₁, φ₁, c₁⟩ := exists_ellMap hB E H _ ω C (𝓞 K)
    (RingOfIntegers.mapRingHom (IntermediateField.inclusion (e₂.trans e₅)).toRingHom)
  obtain ⟨C₂, φ₁₂, c₁₂⟩ := exists_ellMap hB E H _ _ C₁ K (algebraMap (𝓞 K) K)
  obtain ⟨φ₂, c₂, hφ₂⟩ := (Factor.ellMap_cancel_and_sabMap_cancel E H (𝓞 M) k₀ K _
    (IntermediateField.inclusion e₅).toRingHom).1 _ _ _ C C₀ C₂ φ₀ _ c₀
    ((EllComp.ellMap_comp E H _ _ C _ _ C₁ _ _ c₁).1 _ _ C₂ _ _ c₁₂)
  obtain ⟨φ₃, c₃, hφ₃⟩ := (Factor.ellMap_cancel_and_sabMap_cancel E H k₀ K ℂ _ (algebraMap K ℂ)).1
    _ _ _ C₀ C₂ C' φ₂ φ c₂ c'
  exact ⟨_, C₁, φ₁, _, C₂, φ₁₂, φ₂, φ₃, c₁, c₁₂, c₂, c₃, hφ₃, hφ₂.symm⟩

theorem sgnRt_sq (b : Bool) : sgnRt H b ^ 2 = -(H.d : ℂ) := by
  unfold sgnRt
  split_ifs <;> simp [H.sqrt_neg_disc_sq]

theorem exists_pack_given : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n) (Z : ∀ b : Bool, Curve0 H (sgnRt H b)) (P : (FU.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (FU.Di i) ty P) (n : ℕ) (k : IntermediateField ℚ ℂ), FiniteDimensional ℚ k → 0 < n → (∀ y : (FU.Di i).La, ∃ a ∈ PureType.lat hP (sgnRt H true), ∃ b ∈ PureType.lat hP (sgnRt H false), n • y = a + b) → ∃ X : CMPack Z c FU i hP, k ≤ X.K := by
  intro E _ _ _ H D l Xo c g ty FU i Z P hP n k hkf hn hy
  have := c.fin
  have hU : ThetaUnifAV := GlobalTheory.thetaUnifAV_closed
  obtain ⟨hL, hL₂⟩ := GlobalTheory.abelianSchemeLaws_all
  have hX : HomExtDvr := GlobalTheory.CM.homExtDvr_of_card_torsion GlobalTheory.UU.TorsionCount.card_torsion_points_unconditional
  have hK : Published.KernelFiniteFlatSt := GlobalTheory.kernelFiniteFlat_holds
  have hB := hL.polBaseChange
  obtain ⟨K₀, hK₀, y₀, _, hy₀, hy₀'⟩ := GlobalTheory.T.family_pure_periods_span E H D l Xo c g ty FU i P hP n hn hy
  obtain ⟨hg0, bb0, a0, hspan0⟩ := GlobalTheory.T.periods_span_pure_decomposition E H (FU.Di i) g ty P hP n hn hy

  obtain ⟨k₀, _, e₁, e₂, e₃, e₆⟩ : ∃ k₀ : IntermediateField ℚ ℂ, FiniteDimensional ℚ k₀ ∧ K₀ ≤ k₀ ∧
      (∀ b, (Z b).M ≤ k₀) ∧ k ≤ k₀ ∧ c.F ≤ k₀ :=
    ⟨K₀ ⊔ (Z true).M ⊔ (Z false).M ⊔ k ⊔ c.F, inferInstance,
      le_sup_left.trans (le_sup_left.trans (le_sup_left.trans le_sup_left)),
      fun b => by
        cases b
        · exact le_sup_right.trans (le_sup_left.trans le_sup_left)
        · exact le_sup_right.trans (le_sup_left.trans (le_sup_left.trans le_sup_left)),
      le_sup_right.trans le_sup_left, le_sup_right⟩
  choose C₀ φ₀ c₀ using fun b => exists_ellMap hB E H _ (Z b).ω (Z b).C k₀
    ((IntermediateField.inclusion (e₂ b)).toRingHom.comp (algebraMap (𝓞 (Z b).M) (Z b).M))
  choose φ c' hφ using fun b => (Factor.ellMap_cancel_and_sabMap_cancel E H (𝓞 (Z b).M) k₀ ℂ _
    (algebraMap k₀ ℂ)).1 _ _ _ (Z b).C (C₀ b) (Z b).C' (φ₀ b) (Z b).π (c₀ b) (Z b).map
  obtain ⟨T, mT, -⟩ := exists_pat_univ Xo (spMap (IntermediateField.inclusion e₁).toRingHom ≫ y₀)
  obtain ⟨T', nT, -⟩ := exists_pat_univ Xo (FU.u i P)
  obtain ⟨mT', hmT'⟩ := (Factor.ellMap_cancel_and_sabMap_cancel E H k₀ k₀ ℂ (RingHom.id _) (algebraMap k₀ ℂ)).2
    _ _ _ _ _ _ mT nT (by rw [← Category.assoc, spMap_comp_spMap]; exact hy₀')

  choose ε hε using fun b => exists_sign (H := H) (Z b).hω (sgnRt_sq b)
  choose h hh _ using fun b => GlobalTheory.T.exists_unique_cmHermitianLatticeForm E H (FU.Di i) (ε b)
  have htw : 2 * (1 - (((Z true).ω : (Z true).M) : ℂ)) - 1 = sgnRt H false := by
    have := (Z true).hω
    simp only [sgnRt, Bool.false_eq_true, if_false, if_true] at this ⊢
    linear_combination -this
  obtain ⟨ε₁, hε₁⟩ := exists_sign (H := H) htw (sgnRt_sq false)
  obtain ⟨h₁, hh₁, -⟩ := GlobalTheory.T.exists_unique_cmHermitianLatticeForm E H (FU.Di i) ε₁
  choose k₁ hk₁ hle hdesc using fun b => exists_desc hU hL FU i hP k₀ (C₀ b) (Z b).C' (c' b) (Z b).u (Z b).theta
    (Z b).c_ne (Z b).lat (Z b).hω (hε b) (hh b) T T' nT mT'
  obtain ⟨k₂, hk₂, hle₂, hdesc₂⟩ := exists_desc hU hL FU i hP k₀ (twist (C₀ true) false)
    (twist (Z true).C' false) (ellMap_twist (c' true) false) (Z true).u (Z true).theta
    (Z true).c_ne (Z true).lat htw hε₁ hh₁ T T' nT mT'

  obtain ⟨K₁, _, e₄, e₄'⟩ : ∃ K₁ : IntermediateField ℚ ℂ, FiniteDimensional ℚ K₁ ∧ (∀ b, k₁ b ≤ K₁) ∧ k₂ ≤ K₁ := by
    have := hk₁ true
    have := hk₁ false
    exact ⟨k₁ true ⊔ k₁ false ⊔ k₂, inferInstance, fun b => by
      cases b
      exacts [le_sup_right.trans le_sup_left, le_sup_left.trans le_sup_left], le_sup_right⟩
  have : NumberField K₁ := ⟨⟩
  have e₅ : k₀ ≤ K₁ := (hle true).trans (e₄ true)
  choose ω₁ C₁ φ₁ ω₂ C₂ φ₁₂ φ₂ φ₃ c₁ c₁₂ c₂ c₃ hφ₃ hφ₂ using fun b =>
    exists_tower hB (e₂ b) e₅ (Z b).C (C₀ b) (c₀ b) (Z b).C' (c' b)
  have hyy : spMap (algebraMap K₁ ℂ) ≫ spMap (IntermediateField.inclusion (e₁.trans e₅)).toRingHom ≫ y₀ = FU.u i P := by
    rw [← Category.assoc, spMap_comp_spMap]; exact hy₀'
  obtain ⟨T₂, m, hg⟩ := exists_pat_univ Xo (spMap (IntermediateField.inclusion (e₁.trans e₅)).toRingHom ≫ y₀)
  obtain ⟨m₂, hm₂⟩ := (Factor.ellMap_cancel_and_sabMap_cancel E H k₀ k₀ K₁ (RingHom.id _)
    (IntermediateField.inclusion e₅).toRingHom).2 _ _ _ _ _ _ mT m (by rw [← Category.assoc, spMap_comp_spMap]; rfl)
  obtain ⟨m₃, hm₃⟩ := (Factor.ellMap_cancel_and_sabMap_cancel E H K₁ K₁ ℂ (RingHom.id _)
    (algebraMap K₁ ℂ)).2 _ _ _ _ _ _ m₂ mT' (by rw [spMap_comp_spMap]; rfl)
  have hnT : m₃.φ ≫ m.φ = nT.φ := by rw [← hm₂, ← Category.assoc, hm₃, hmT']
  choose ψ₂ hψ₂ hex₂ using fun b => hdesc b K₁ e₅ (e₄ b) _ (C₂ b) (φ₂ b) (φ₃ b) T₂ m₂ m₃ _ m (c₂ b) (c₃ b)
    (hφ₃ b) hm₃ hnT
  obtain ⟨ψt, hψt, hext⟩ := hdesc₂ K₁ e₅ e₄' _ (twist (C₂ true) false) (φ₂ true) (φ₃ true) T₂ m₂ m₃ _ m
    (ellMap_twist (c₂ true) false) (ellMap_twist (c₃ true) false) (hφ₃ true) hm₃ hnT
  have hpt : ∀ b (z : Fin (Z b).C'.P.g → ℂ),
      (((Z b).u.ex z).left ≫ φ₃ b) ≫ (C₂ b).P.A.hom = spMap (algebraMap K₁ ℂ) := fun b z => by
    rw [Category.assoc, (c₃ b).2.1.2.1.1.w, ← Category.assoc, Over.w]
    exact Category.id_comp _

  have hΨ : ∀ b, ∃ Ψ : PureType.lat hP (sgnRt H b) → ((C₂ true).P.A ⟶ T₂.t.G), (∀ a, IsMonHom (Ψ a)) ∧
      ∀ a (z : ℂ), (((Z true).u.ex fun _ => (Z true).c * z).left ≫ φ₃ true ≫ (Ψ a).left) ≫ m.φ =
        (FU.ex i P (z • P a)).left := by
    intro b
    cases b
    · exact ⟨ψt, fun a => (hψt.1 a).1, hext⟩
    · exact ⟨ψ₂ true, fun a => ((hψ₂ true).1 a).1, hex₂ true⟩
  choose Ψ hΨm hΨe using hΨ
  have hgT : T₂.g = g := by rw [hg, hg0, (FU.sig i).1, (FU.sig i).2]
  have key : ∀ N : ℕ, N = g → ∃ (bb : Fin N → Bool) (a : ∀ j, PureType.lat hP (sgnRt H (bb j))),
      ∀ z : Fin g → ℂ, ∃ s : Fin N → ℂ, z = ∑ j, s j • P (a j) := by
    rintro N rfl
    exact ⟨bb0, a0, hspan0⟩
  obtain ⟨bb, a, hspan⟩ := key _ hgT
  obtain ⟨B, m', hBg⟩ := GlobalTheory.T.principal_triple_extends_of_curve_homomorphisms hU hL hL₂ hX hK E H (𝓞 K₁) K₁ (algebraMap K₁ ℂ) (C₁ true).P (C₂ true).P
    (φ₁₂ true) T₂ (fun j => Ψ (bb j) (a j)) (c₁₂ true).2.1 (C₁ true).dim (fun j => hΨm (bb j) (a j))
    (ontoAt_of_exp m.cart _ hyy (FU.ex i P) (FU.ex_add i P hP) (FU.ex_onto i P hP) _ hspan _ fun j z =>
      ⟨Over.homMk _ (hpt true fun _ => (Z true).c * z), by
        rw [← hΨe (bb j) (a j) z]
        simp only [Category.assoc]
        exact Category.assoc _ _ _⟩)
  choose ψ hψ hsq' using fun b => GlobalTheory.T.cmFamily_extends_over_dedekindDomain hL hX E H (𝓞 K₁) K₁ _ (C₁ b) (FU.Di i) _ B _ _ (C₂ b) (φ₁₂ b)
    T₂ m' (ψ₂ b) (c₁₂ b) (hψ₂ b)
  have hcF : c.F ≤ K₁ := e₆.trans e₅
  let yK : Sp K₁ ⟶ Xo.XF c := pullback.lift (spMap (IntermediateField.inclusion (e₁.trans e₅)).toRingHom ≫ y₀)
    (spMap (IntermediateField.inclusion hcF).toRingHom) (by
      rw [Category.assoc, hy₀, spMap_comp_spMap, spMap_comp_spMap]; rfl)
  have hyK : under yK = spMap (IntermediateField.inclusion (e₁.trans e₅)).toRingHom ≫ y₀ := pullback.lift_fst _ _ _
  obtain ⟨mK, hmK⟩ : ∃ mK : SABMap T₂.t Xo.univ.t (under yK), mK.φ = m.φ := by
    rw [hyK]; exact ⟨m, rfl⟩
  refine ⟨
    { K := K₁, hc := hcF, hM := fun b => (e₂ b).trans e₅, ω := ω₁, C := C₁, φ := φ₁
      map := c₁
      π := fun b => φ₃ b ≫ φ₁₂ b
      map' := fun b => (EllComp.ellMap_comp E H _ _ (C₁ b) _ _ (C₂ b) _ _ (c₁₂ b)).1 _ _ (Z b).C' _ _ (c₃ b)
      tri := fun b => by
        rw [Category.assoc, hφ₂, ← Category.assoc, hφ₃, hφ]
      ε := ε
      sgn := fun b => by
        have e := congrArg Complex.im (Z b).hω
        have e' : (sgnRt H b).im = 2 * (((Z b).ω : (Z b).M) : ℂ).im := by
          rw [← e]; simp
        rw [e']; nlinarith [hε b]
      h := fun b x y => h b x y
      kform := hh
      B := B
      dim := by rw [hBg, hgT]
      y := yK
      hy := pullback.lift_snd _ _ _
      pt := by rw [hyK]; exact hyy
      t := T₂.t, m := mK, m' := m', ψ := ψ, fam := hψ
      tie := fun b a z x hx hx' => ?_ }, e₃.trans e₅⟩
  rw [hmK, ← hex₂ b a z]
  congr 1
  refine m'.cart.1.hom_ext ?_ ?_
  · refine hx'.trans ?_
    simp only [Category.assoc]
    exact congrArg (fun q => _ ≫ φ₃ b ≫ q) (hsq' b a).symm
  · rw [hx, ← hpt b fun _ => (Z b).c * z]
    simp only [Category.assoc]
    exact congrArg (fun q => _ ≫ φ₃ b ≫ q) (Over.w (ψ₂ b a)).symm

end GlobalTheory.CompanionTheory.Ar.Fl.CMGiven
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComplexAbelianFibreAmpleStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complex_abelian_fibre_ample : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (D : PPData H L) (σ : L →+* ℂ), ∃ (t' : SAB H (Sp ℂ)) (_ : SABMap t' D.t (emb σ)), IsProper t'.G.hom ∧ Out.RelAmple t'.G t'.PP.L := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Sl.FibrePol.exists_fibre_pol | exact GlobalTheory.CompanionTheory.Ar.Sl.FibrePol.exists_fibre_pol | (intros; apply GlobalTheory.CompanionTheory.Ar.Sl.FibrePol.exists_fibre_pol <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CuspVolumeMiddleStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cusp_volume_middle : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (Q : Pieces Or) (U : ((Σ k, J k) → ℂ) → ℝ), Or.𝔐.IsCuspWeight Or.sm U → (∀ w ∈ Dc.Xo, ∀ w' ∈ torusSat {w}, U w' = U w) ∧ ∀ m, ∀ t ∈ Q.V m, U (Q.γ m t) = ((Q.F (Q.pc m)).R t).cuspW (Q.F (Q.pc m)).σ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.WeightSheet.cuspWeight_torus_and_sheets | exact GlobalTheory.CompanionTheory.Ar.Cusp.WeightSheet.cuspWeight_torus_and_sheets | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.WeightSheet.cuspWeight_torus_and_sheets <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsAbelianPartExtensionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_abelian_part_extension : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) (t : SAB H S) (L : Type) [Field L] [NumberField L] (z : Sp L ⟶ S), ∃ (L' : Type) (_ : Field L') (_ : NumberField L') (e : L →+* L'), Nonempty (AbPart t (spMap e ≫ z)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.abPart_exists | exact GlobalTheory.CompanionTheory.Ar.abPart_exists | (intros; apply GlobalTheory.CompanionTheory.Ar.abPart_exists <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsArchimedeanFrameStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_archimedean_frame : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (P : RigLB G) (z : Sp ℂ ⟶ S) (A : Over (Sp ℂ)) [GrpObj A] (φ : A.left ⟶ G.left) (g : ℕ) (u : HolUnif A (P.L.pull φ) g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ), IsGrpPullback A G z φ → u.IsAH Hm χ → Nonempty (ArchFrame P z g) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Sl.exists_archFrame_of_isAH | exact GlobalTheory.CompanionTheory.Ar.Sl.exists_archFrame_of_isAH | (intros; apply GlobalTheory.CompanionTheory.Ar.Sl.exists_archFrame_of_isAH <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeHermitianFormExistsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_hermitian_form_exists : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (z : Spec (CommRingCat.of ℂ) ⟶ X) (V : Type) [AddCommGroup V] [Module ℂ V] (M : LieModel t.G z V), (∃ (t' : SAB H (Sp ℂ)) (_ : SABMap t' t z), IsProper t'.G.hom ∧ Out.RelAmple t'.G t'.PP.L) → ∃ h : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ, (∀ v w c, HodgeIP t.G t.PP.L z (M.pt v) (M.pt w) c ↔ c = h v w) ∧ (∀ v w, h w v = starRingEnd ℂ (h v w)) ∧ ∀ v, v ≠ 0 → 0 < (h v v).re := by
  first | exact @GlobalTheory.CompanionTheory.Ar.exists_hodgeInnerProduct_form | exact GlobalTheory.CompanionTheory.Ar.exists_hodgeInnerProduct_form | (intros; apply GlobalTheory.CompanionTheory.Ar.exists_hodgeInnerProduct_form <;> assumption)
end

