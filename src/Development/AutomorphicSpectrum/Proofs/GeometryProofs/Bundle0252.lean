import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0248
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0249
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
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0012
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0185
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0140
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0020
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0141
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0119
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0100
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0024
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0134
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0039
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0011
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0247
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0010
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0007
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUniqueLeftBasisCoordsAdicCompletion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0057
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0129
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0117
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0099
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0190
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0173
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0078
import Development.AbelianVarietyTheory.Statements.HyperbolicHypotheses.HypothesesInhabitedHyperbolic
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsDerivAt0OfIsPullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0059
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0009
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.SmulPeriodMapMkZeroFstEqNegForm
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0020

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsUnitAnalyticFunctionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unit_analytic_function : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (τ τ' : E →+* ℂ) (σ : c.F →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty), IsTypeFn H D.p D.q ty → τ' (H.rt : E) = H.rt0 → (∀ a : 𝓞 E, σ (tauIn c τ a) = τ' (a : E)) → ∃ Φ : CFn Xo c, IsUnitAn τ σ Φ ∧ ∀ i : Fin FU.n, ∃ (e : Fin D.p ⊕ Fin D.q → (FU.Di i).La) (ρ : ℂ), ρ ≠ 0 ∧ LinearIndependent (𝓞 E) e ∧ IsFlatAn Set.univ τ τ' σ Φ FU i e ρ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.anUnit | exact GlobalTheory.CompanionTheory.Ar.Flat.anUnit | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.anUnit <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FnFactorStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_add_lattice_eq_of_isFn : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (P : RigLB G) (z : Sp ℂ ⟶ S) (g : ℕ) (a : ArchFrame P z g) (n : ℕ) (s : Out.H0 P.L n) (θ : (Fin g → ℂ) → ℂ), a.IsFn s θ → ∀ (l : a.u.Λ) (w : Fin g → ℂ), θ (w + l) = (a.χ l * Complex.exp (Real.pi * a.herm w l + Real.pi / 2 * a.herm l l)) ^ n * θ w := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Sl.Fac.fn_factor | exact GlobalTheory.CompanionTheory.Ar.Sl.Fac.fn_factor | (intros; apply GlobalTheory.CompanionTheory.Ar.Sl.Fac.fn_factor <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameCoordinatesUniqueStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frame_coordinates_unique : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (D : PPData H L) (σ : L →+* ℂ) (a : D.Frame σ), (∀ v, IsTangent v → ∃! w, a.u.IsDiff w v) → (∀ w, ∃! v, IsTangent v ∧ a.u.IsDiff w v) → ∀ x : D.B.carrier, ∃! c, D.IsVec a x c := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Sl.FrameVec.isVec_existsUnique | exact GlobalTheory.CompanionTheory.Ar.Sl.FrameVec.isVec_existsUnique | (intros; apply GlobalTheory.CompanionTheory.Ar.Sl.FrameVec.isVec_existsUnique <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolUnifPeriodMatrixMiddle
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.QuotLoc.Pair
open GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.UU

theorem cubWeil_of_lbIso (G : Over (Sp ℂ)) [GrpObj G] [IsCommMonObj G] (hs : IsSemiAbelian G) (τ : TorusExtension G)
    (L₁ L₂ : RigLB G) (c₁ : CubicalStr G L₁) (c₂ : CubicalStr G L₂) (hw : LBIso L₁.L L₂.L) (N : ℕ)
    (x y : 𝟙_ (Over (Sp ℂ)) ⟶ G) (ζ : Γ(Sp ℂ, ⊤)ˣ) (h : CubWeil c₁ N x y ζ) : CubWeil c₂ N x y ζ :=
  GlobalTheory.T.cubical_weil_pairing_iso_invariant G hs τ L₁ L₂ c₁ c₂ hw N x y ζ h

theorem cubWeil_congr {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {L : RigLB G} {c : CubicalStr G L} {N : ℕ}
    {Z : Scheme.{0}} {a b : Z ⟶ S} (hab : a = b) {x y : Over.mk a ⟶ G} {x' y' : Over.mk b ⟶ G}
    (hx : x'.left = x.left) (hy : y'.left = y.left) {ζ : Γ(Z, ⊤)ˣ} (h : CubWeil c N x y ζ) :
    CubWeil c N x' y' ζ := by
  subst hab
  obtain rfl : x' = x := Over.OverMorphism.ext hx
  obtain rfl : y' = y := Over.OverMorphism.ext hy
  exact h

theorem cubWeil_fibre {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S S' : Scheme.{0}}
    {t' : SAB H S'} {t : SAB H S} {f : S' ⟶ S} (m : SABMap t' t f) {Z : Scheme.{0}} (a : Z ⟶ S') (b : Z ⟶ S)
    (hb : b = a ≫ f) {N : ℕ} {x y : Over.mk a ⟶ t'.G} {x₀ y₀ : Over.mk b ⟶ t.G} (ex : x₀.left = x.left ≫ m.φ)
    (ey : y₀.left = y.left ≫ m.φ) (hx : x ^ N = 1) (hy : y ^ N = 1) {ζ : Γ(Z, ⊤)ˣ}
    (h : CubWeil t.cub N x₀ y₀ ζ) : CubWeil t'.cub N x y ζ := by
  obtain ⟨ξ, hξ, -⟩ := GlobalTheory.UU.existsUnique_cubWeil t'.cub hx hy
  have hw : m.cm.F ≫ t.G.hom = t'.G.hom ≫ f := m.cart.1.w
  have mul : ∀ (T : Over S') (x y : T ⟶ t'.G), Out.toBase hw (x * y) = Out.toBase hw x * Out.toBase hw y :=
    fun T x y => Over.OverMorphism.ext (m.cart.2 T x y _ _ rfl rfl).symm
  have h1 := GlobalTheory.UU.cubWeil_of_isPullCubical S S' f t.G t'.G m.cm hw mul _ _ t.cub t'.cub m.lin N (Over.mk a) x y ξ hξ
  have h2 : CubWeil t.cub N x₀ y₀ ξ := cubWeil_congr hb.symm ex ey h1
  rwa [h2.unique h] at hξ

theorem cubWeil_quot {G B : Over (Sp ℂ)} [GrpObj G] [IsCommMonObj G] [GrpObj B] [IsCommMonObj B] (hs : IsSemiAbelian G)
    (τ : TorusExtension G) (q : G ⟶ B) [IsMonHom q] (L₁ : RigLB G) (c₁ : CubicalStr G L₁) (L₂ : RigLB B)
    (c₂ : CubicalStr B L₂) (hw : LBIso L₁.L (L₂.L.pull q.left)) (N : ℕ) (x y : 𝟙_ (Over (Sp ℂ)) ⟶ G)
    (ζ : Γ(Sp ℂ, ⊤)ˣ) (h : CubWeil c₁ N x y ζ) : CubWeil c₂ N (x ≫ q) (y ≫ q) ζ := by
  obtain ⟨hL, hr, ⟨c', hc⟩, -⟩ := Out.CubePf.cubePull _ _ _ _ (CubeMap.ofHom q) L₂ c₂
  have h1 := cubWeil_of_lbIso G hs τ L₁ ((CubeMap.ofHom q).rigLB L₂ hL hr) c₁ c' hw N x y ζ h
  have hw' : (CubeMap.ofHom q).F ≫ B.hom = G.hom ≫ 𝟙 _ := by
    simp [CubeMap.ofHom]
  have e : ∀ (T : Over (Sp ℂ)) (a : T ⟶ G), Out.toBase hw' a =
      (Over.homMk (𝟙 T.left) (by simp) : Over.mk (T.hom ≫ 𝟙 _) ⟶ T) ≫ a ≫ q := fun T a =>
    Over.OverMorphism.ext (by simp [Out.toBase, CubeMap.ofHom])
  have mul : ∀ (T : Over (Sp ℂ)) (a b : T ⟶ G), Out.toBase hw' (a * b) = Out.toBase hw' a * Out.toBase hw' b := by
    intro T a b
    rw [e, e, e, MonObj.mul_comp, MonObj.comp_mul]
  have h2 := GlobalTheory.UU.cubWeil_of_isPullCubical _ _ (𝟙 _) B G (CubeMap.ofHom q) hw' mul _ _ c₂ c' hc N _ x y ζ h1
  exact cubWeil_congr (by simp) rfl rfl h2

theorem ex_nsmul {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] {g n : ℕ} {M : LieModel G (𝟙 (Sp R)) (Fin g → R)}
    {B : Set (Fin n → ℂ)} {ψ : (Fin n → ℂ) → (R →+* ℂ)} (e : Flat.FamExp G M B ψ) {b : Fin n → ℂ} (hb : b ∈ B)
    (k : ℕ) (z : Fin g → ℂ) : e.ex b (k • z) = e.ex b z ^ k := by
  have h0 : e.ex b 0 = 1 := by
    have := e.add b hb 0 0
    rw [add_zero] at this
    exact left_eq_mul.1 this
  induction k with
  | zero => rw [zero_smul, pow_zero, h0]
  | succ k ih => rw [succ_nsmul, e.add b hb, ih, pow_succ]

theorem ex_nsmul_hol {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g) (k : ℕ) (z : Fin g → ℂ) :
    u.ex (k • z) = u.ex z ^ k := by
  have h0 : u.ex 0 = 1 := (u.ker 0).2 u.Λ.zero_mem
  induction k with
  | zero => rw [zero_smul, pow_zero, h0]
  | succ k ih => rw [succ_nsmul, u.ex_add, ih, pow_succ]

theorem weil_value {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (tB : SAB H (Sp ℂ))
    (A : Over (Sp ℂ)) [GrpObj A] (φ : A.left ⟶ tB.G.left) (g : ℕ) (u : HolUnif A (tB.PP.L.pull φ) g)
    (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ) (hpb : IsGrpPullback A tB.G (𝟙 _) φ) (hAH : u.IsAH Hm χ)
    (hP : IsPrincipal tB) (N : ℕ) (ζ : ℂˣ) (a b : Fin g → ℂ) (hN : 0 < N) (ha : a ∈ u.Λ) (hb : b ∈ u.Λ)
    (x y : 𝟙_ (Over (Sp ℂ)) ⟶ tB.G) (hx : x.left = (u.ex ((N : ℂ)⁻¹ • a)).left ≫ φ)
    (hy : y.left = (u.ex ((N : ℂ)⁻¹ • b)).left ≫ φ) (h : CubWeil tB.cub N x y (unitOn ζ)) :
    (ζ : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (((a ⬝ᵥ Hm *ᵥ star b).im : ℝ) : ℂ) / N) := by
  have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have := tB.semi.smooth
  have := tB.semi.geomConnected
  have hAb : IsAbelianScheme tB.G := ⟨tB.semi.comm, tB.semi.smooth, hP.1, tB.semi.geomConnected⟩
  have hA : IsAbelianScheme A := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hAb hpb
  have : ConnectedSpace tB.G.left :=
    GeometricallyConnected.geometrically_connectedSpace (f := tB.G.hom) (𝟙 _) (𝟙 _) tB.G.hom
      (IsPullback.of_horiz_isIso ⟨by simp⟩)
  obtain ⟨d, hd⟩ := exists_dim_of_preconnected tB.G.hom (eSec tB.G (default : PrimeSpectrum ℂ))
  obtain ⟨-, ws, gs', -⟩ := tB.sym
  have hL' := pull_isLB tB.PP.isLB φ
  have hw := (isGen_iff _).1 (ReciprocityTheory.ChartRestriction.G.Geo.Tor.idIso_isGen hL')
  let Q : Out.PolAV (Sp ℂ) :=
    { A := A, isAb := hA, g := d
      smoothDim := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hpb.1 hd
      L := tB.PP.L.pull φ, isLB := hL'
      rigid := GlobalTheory.PolBaseChange.rigidified_pull hpb ⟨tB.PP.rig, tB.PP.rigGen⟩
      sym := GlobalTheory.PolBaseChange.sym_pull hpb fun _ => ⟨⊤, trivial, gen_of_iso ((isGen_iff ws).1 gs') _⟩
      ample := relAmple_pull hpb.1 tB.PP.isLB hL' hw ⊤ (isAffineOpen_top _) (fun _ => trivial) hP.2.1
      ktriv := kTriv_pull hpb tB.PP.isLB hL' hw hP.2.2 }
  haveI : IsCommMonObj A := hA.comm
  have tors : ∀ w : Fin g → ℂ, w ∈ u.Λ → u.ex ((N : ℂ)⁻¹ • w) ^ N = 1 := fun w hw => by
    rw [← ex_nsmul_hol, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_inv_cancel₀ hN0, one_smul]
    exact (u.ker w).2 hw
  obtain ⟨hL, hr, ⟨c', hc⟩, -⟩ := Out.CubePf.cubePull _ _ _ _ (cubeMapOf hpb) tB.PP tB.cub
  obtain ⟨ξ, hξ, -⟩ := existsUnique_cubWeil c' (tors a ha) (tors b hb)
  have hw' : (cubeMapOf hpb).F ≫ tB.G.hom = A.hom ≫ 𝟙 _ := hpb.1.w
  have mul : ∀ (T : Over (Sp ℂ)) (p q : T ⟶ A), Out.toBase hw' (p * q) = Out.toBase hw' p * Out.toBase hw' q :=
    fun T p q => Over.OverMorphism.ext (hpb.2 T p q _ _ rfl rfl).symm
  have h1 := cubWeil_of_isPullCubical _ _ (𝟙 _) tB.G A (cubeMapOf hpb) hw' mul _ _ tB.cub c' hc N _ _ _ ξ hξ
  have h2 : CubWeil tB.cub N x y ξ := cubWeil_congr (by simp) hx hy h1
  obtain rfl : ξ = unitOn ζ := h2.unique h
  have hW₁ : Out.WeilIs Q.A Q.L N (u.ex ((N : ℂ)⁻¹ • a)) (u.ex ((N : ℂ)⁻¹ • b)) (unitOn ζ) :=
    (cubWeil_iff_weilIs GlobalTheory.globalFns_holds hA (tors a ha) (tors b hb) _).1 hξ
  obtain ⟨Ef, hE, -, -, -, -, hWe⟩ := GlobalTheory.AHWeil.tangent_and_weil_of_isAH GlobalTheory.thetaUnifAV_all Q g u Hm χ hAH
  let c : ℂˣ := Units.mk0 (Complex.exp (-(2 * Real.pi * Complex.I) * (Ef ⟨a, ha⟩ ⟨b, hb⟩ : ℂ) / N)) (Complex.exp_ne_zero _)
  have hW₂ := hWe N ⟨a, ha⟩ ⟨b, hb⟩ c hN rfl
  have e := ((GlobalTheory.abelianSchemeLaws_all.1.weil (Sp ℂ) Q N (𝟙_ _)).1 _ _ (tors a ha) (tors b hb)).unique hW₁ hW₂
  have e' : ζ = c := Units.ext (by
    have := congrArg (fun v : Γ(Sp ℂ, ⊤)ˣ => (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom v.val) e
    simpa [unitOn] using this)
  rw [e']
  show Complex.exp _ = _
  have i := hE ⟨a, ha⟩ ⟨b, hb⟩
  congr 3
  exact_mod_cast congrArg (fun r : ℝ => (r : ℂ)) i

theorem cubWeil_eq_exp_riemann : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] (t : SAB H (Sp R)) (g n : ℕ) (M : LieModel t.G (𝟙 (Sp R)) (Fin g → R)) (B : Set (Fin n → ℂ)) (ψ : (Fin n → ℂ) → (R →+* ℂ)) (e : Flat.FamExp t.G M B ψ) (b : Fin n → ℂ) (P : AbPart t (spMap (ψ b))) (A : Over (Sp ℂ)) (_ : GrpObj A) (φ : A.left ⟶ P.tB.G.left) (g' : ℕ) (u : HolUnif A (P.tB.PP.L.pull φ) g') (Hm : Matrix (Fin g') (Fin g') ℂ) (χ : u.Λ → ℂ) (ℓ : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)), b ∈ B → IsGrpPullback A P.tB.G (𝟙 _) φ → u.IsAH Hm χ → IsPrincipal P.tB → GlobalTheory.CompanionTheory.Ar.QuotLoc.IsAbLift e b P φ u ℓ → ∀ (N : ℕ) (ζ : ℂˣ) (y y' : Fin g → ℂ), 0 < N → y ∈ e.per b → y' ∈ e.per b → CubWeil t.cub N (e.ex b ((N : ℂ)⁻¹ • y)) (e.ex b ((N : ℂ)⁻¹ • y')) (unitOn ζ) → (ζ : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (((ℓ y ⬝ᵥ Hm *ᵥ star (ℓ y')).im : ℝ) : ℂ) / N) := by
  intro E _ _ _ H R _ t g n M B ψ e b P A _ φ g' u Hm χ ℓ hb hpb hAH hP hLift N ζ y y' hN hy hy' hW
  have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  obtain ⟨ρ, hρ⟩ := GlobalTheory.AlphaPair.exists_ptEquiv P.m.cart (𝟙 (Sp ℂ)) (spMap (ψ b)) (Category.id_comp _).symm
  obtain ⟨ρ', hρ'⟩ := GlobalTheory.AlphaPair.exists_ptEquiv hpb (𝟙 (Sp ℂ)) (𝟙 (Sp ℂ)) (Category.id_comp _).symm
  letI := P.τ.grpB
  have := P.τ.q_hom
  have := P.e_hom
  have tors : ∀ w : Fin g → ℂ, w ∈ e.per b → e.ex b ((N : ℂ)⁻¹ • w) ^ N = 1 := fun w hw => by
    rw [← ex_nsmul e hb, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_inv_cancel₀ hN0, one_smul]
    exact hw
  let s : 𝟙_ (Over (Sp ℂ)) ⟶ P.tK.G := ρ.symm (e.ex b ((N : ℂ)⁻¹ • y))
  let s' : 𝟙_ (Over (Sp ℂ)) ⟶ P.tK.G := ρ.symm (e.ex b ((N : ℂ)⁻¹ • y'))
  have hs : s.left ≫ P.m.φ = (e.ex b ((N : ℂ)⁻¹ • y)).left :=
    (hρ s).symm.trans (congrArg (fun q => q.left) (ρ.apply_symm_apply _))
  have hs' : s'.left ≫ P.m.φ = (e.ex b ((N : ℂ)⁻¹ • y')).left :=
    (hρ s').symm.trans (congrArg (fun q => q.left) (ρ.apply_symm_apply _))
  have ts : s ^ N = 1 := ρ.injective (by
    show ρ (ρ.symm _ ^ N) = ρ 1
    rw [map_pow, ρ.apply_symm_apply, tors y hy, map_one])
  have ts' : s' ^ N = 1 := ρ.injective (by
    show ρ (ρ.symm _ ^ N) = ρ 1
    rw [map_pow, ρ.apply_symm_apply, tors y' hy', map_one])
  have W₁ : CubWeil P.tK.cub N s s' (unitOn ζ) :=
    cubWeil_fibre P.m (𝟙 (Sp ℂ)) (spMap (ψ b)) (Category.id_comp _).symm hs.symm hs'.symm ts ts' hW
  have W₂ := cubWeil_quot P.tK.semi P.τ (P.τ.q ≫ P.e.hom) P.tK.PP P.tK.cub P.tB.PP P.tB.cub P.pp N s s' _ W₁
  have lat : ∀ w : Fin g → ℂ, w ∈ e.per b → ℓ w ∈ u.Λ := fun w hw => by
    have h1 : (1 : 𝟙_ (Over (Sp ℂ)) ⟶ P.tK.G).left ≫ P.m.φ = (e.ex b w).left := by
      have := hρ (1 : 𝟙_ (Over (Sp ℂ)) ⟶ P.tK.G)
      rw [map_one] at this
      rw [← this]
      exact congrArg (fun q => q.left) (Eq.symm hw)
    have h2 := hLift w 1 h1
    refine (u.ker _).1 (ρ'.injective ?_)
    apply Over.OverMorphism.ext
    rw [map_one, hρ', h2, MonObj.one_comp]
  have hl : ∀ w : Fin g → ℂ, ℓ ((N : ℂ)⁻¹ • w) = (N : ℂ)⁻¹ • ℓ w := fun w => map_smul _ _ _
  exact weil_value P.tB A φ g' u Hm χ hpb hAH hP N ζ (ℓ y) (ℓ y') hN (lat y hy) (lat y' hy') _ _
    ((hl y) ▸ (hLift _ s hs).symm) ((hl y') ▸ (hLift _ s' hs').symm) W₂

end GlobalTheory.CompanionTheory.Ar.QuotLoc.Pair
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.InteriorPointLatticeData
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.FibreEx

open GlobalTheory.CompanionTheory.Ar.Cusp.FamEx GlobalTheory.CompanionTheory.Ar.Flat.PerGram

section Tangent

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ}

theorem surjective_of_add_mem {g₀ : ℕ} (Λ : Submodule ℤ (Fin g₀ → ℂ)) (hd : DiscreteTopology Λ)
    (F : (Fin g → ℂ) →ₗ[ℂ] (Fin g₀ → ℂ)) (h : ∀ y, ∃ z, y - F z ∈ Λ) : Function.Surjective F := by
  have hc : (Λ : Set (Fin g₀ → ℂ)).Countable := by
    haveI := hd
    have : Countable Λ := countable_of_Lindelof_of_discrete
    exact Set.countable_coe_iff.1 this
  intro y
  have h0 : (LinearMap.range F).mkQ y = 0 := by
    refine GlobalTheory.eq_zero_of_forall_smul_mem_countable (hc.image (LinearMap.range F).mkQ) fun s => ?_
    obtain ⟨z, hz⟩ := h (s • y)
    refine ⟨_, hz, ?_⟩
    simp only [map_sub, map_smul, Submodule.mkQ_apply]
    rw [(Submodule.Quotient.mk_eq_zero (LinearMap.range F)).2 ⟨z, rfl⟩, sub_zero]
  simpa using h0

theorem exists_isDiff {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} {t : SAB H X}
    {z : Sp ℂ ⟶ X} (t' : SAB H (Sp ℂ)) (m : SABMap t' t z) (hP : IsProper t'.G.hom)
    (hA : Out.RelAmple t'.G t'.PP.L) {φ : A.left ⟶ t.G.left} (hp : IsGrpPullback A t.G z φ) (u : HolUnif A L g)
    {x : epsR ℂ ⟶ A} (hx : IsTangent x) : ∃ w, u.IsDiff w x := by
  have hab : IsAbelianScheme t'.G := AbelianSchemeGerms.isAbelianScheme_of_proper t'.G t'.semi
  obtain ⟨g₀, hg⟩ := GlobalTheory.AbelianDim.exists_relDim ℂ t'.G hab
  obtain ⟨u₀, hc⟩ := GlobalTheory.CompanionTheory.Ar.AVExp.exists_holUnif t'.G t'.PP.L g₀ hab hA hg
  obtain ⟨ht₁, ht₂⟩ := @GlobalTheory.TangentOrigin.tangent_bijection_of_values @GlobalTheory.valAt'_rules t'.G _ _ g₀ u₀ hc
  obtain ⟨e, hmon, -⟩ := grpPullback_iso hp m.cart
  haveI := hmon
  have hol : IsHolTo (Set.univ : Set (Fin g → ℂ)) (fun w => (u.ex w ≫ e.hom).left) := by
    simpa only [Over.comp_left] using GlobalTheory.HolTorsion.isHolTo_comp (isHolTo_ex u) e.hom.left
  obtain ⟨F, hF, -⟩ := GlobalTheory.existsUnique_linear_lift_of_isHolTo t'.G hab _ g₀ g u₀ ht₁ ht₂
    (fun w => u.ex w ≫ e.hom) (fun p q => by rw [u.ex_add, MonObj.mul_comp]) hol
  have hF' : ∀ w, u₀.ex (F w) = u.ex w ≫ e.hom := hF
  have hsurj : Function.Surjective F := surjective_of_add_mem u₀.Λ u₀.discrete F fun y => by
    obtain ⟨w, hw⟩ := u.ex_onto (u₀.ex y ≫ e.inv)
    refine ⟨w, (u₀.ker _).1 ?_⟩
    have h1 : u₀.ex (F w) = u₀.ex y := by rw [hF', hw, Category.assoc, e.inv_hom_id, Category.comp_id]
    have h2 := u₀.ex_add (y - F w) (F w)
    rw [sub_add_cancel, h1] at h2
    have h3 : u₀.ex (y - F w) * u₀.ex y = 1 * u₀.ex y := by rw [← h2, _root_.one_mul]
    exact mul_right_cancel h3
  have hxe : IsTangent (x ≫ e.hom) := by
    have h₁ : η[A] ≫ e.hom = η[t'.G] := IsMonHom.one_hom e.hom
    unfold IsTangent at hx ⊢
    rw [Over.comp_left, ← Category.assoc, hx, ← Over.comp_left, h₁]
  obtain ⟨w₀, hw₀, -⟩ := ht₁ (x ≫ e.hom) hxe
  obtain ⟨w, rfl⟩ := hsurj w₀
  refine ⟨w, ?_⟩
  have a := isDerivAt0_of_isDiff u₀ hxe hw₀
  have b := GlobalTheory.FibreDeriv.isDerivAt0_comp a e.inv.left
  have hol' : IsHolTo (Set.univ : Set (Fin g₀ → ℂ)) (fun z => (u₀.ex z).left ≫ e.inv.left) :=
    GlobalTheory.HolTorsion.isHolTo_comp (isHolTo_ex u₀) e.inv.left
  have c := isDerivAt0_comp_linMap hol' F b
  have back : ∀ {T : Over (Sp ℂ)} (q : T ⟶ A), (q ≫ e.hom).left ≫ e.inv.left = q.left := fun q => by
    rw [← Over.comp_left, Category.assoc, e.hom_inv_id, Category.comp_id]
  have e1 : (fun z => (u₀.ex (F z)).left ≫ e.inv.left) = fun z => (u.ex z).left :=
    funext fun z => by rw [hF', back]
  rw [e1, back] at c
  exact fun U h f => c.2 U h f

end Tangent

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem fibreLatVec_of_fibreLat {X : Scheme.{0}} {t : SAB H X} {z : Sp ℂ ⟶ X} {g : ℕ} {Λ : Type} [AddCommGroup Λ]
    [Module (𝓞 E) Λ] {R : RiemLat E g Λ} (hz : HodgeMetric.PolarisedAt t z) (hF : FibreLat t z R) {A₀ : Type}
    (v : A₀ → (epsAt z ⟶ t.G)) (hv : ∀ i, IsTanAt t.G z (v i)) : ∃ x : A₀ → Fin g → ℂ, FibreLatVec t z R x v := by
  obtain ⟨t', m, hP, hA⟩ := hz
  obtain ⟨A, _, φ, u, χ, hp, hAH, hact, hinj, hmem, -⟩ := hF
  have key : ∀ i, ∃ (x : Fin g → ℂ) (v' : epsR ℂ ⟶ A), v'.left ≫ φ = (v i).left ∧ u.IsDiff x v' := fun i => by
    let Φ := HodgeLin.tanEquiv hp
    have hl : (Φ.symm (v i)).left ≫ φ = (v i).left := congrArg (fun q => q.left) (Φ.apply_symm_apply (v i))
    have ht : IsTangent (Φ.symm (v i)) := (HodgeLin.isTangent_iff hp _).2 (by
      change IsTanAt t.G z (Φ (Φ.symm (v i)))
      rw [Φ.apply_symm_apply]
      exact hv i)
    obtain ⟨w, hw⟩ := exists_isDiff t' m hP hA hp u ht
    exact ⟨w, _, hl, hw⟩
  choose x v' h1 h2 using key
  exact ⟨x, A, inferInstance, φ, u, χ, hp, hAH, hact, hinj, hmem, fun i => ⟨v' i, h1 i, h2 i⟩⟩

theorem hodgeInnerProduct_eq_pi_mul_riemannForm {X : Scheme.{0}} {t : SAB H X} {z : Sp ℂ ⟶ X} {g : ℕ} {Λ : Type} [AddCommGroup Λ]
    [Module (𝓞 E) Λ] {R : RiemLat E g Λ} {A₀ : Type} {x : A₀ → Fin g → ℂ} {v : A₀ → (epsAt z ⟶ t.G)}
    (h : FibreLatVec t z R x v) (tan : ∀ i, IsTanAt t.G z (v i)) (i j : A₀) :
    HodgeIP t.G t.PP.L z (v i) (v j) (Real.pi * R.ip (x i) (x j)) := by
  obtain ⟨A, _, φ, u, χ, h1, h2, -, -, -, h3⟩ := h
  obtain ⟨v', e', d'⟩ := h3 i
  obtain ⟨w', f', g'⟩ := h3 j
  exact ⟨t.PP.isLB, tan i, tan j, A, inferInstance, φ, g, u, R.Hm, χ, v', w', x i, x j, h1, h2, e', f', d', g', rfl⟩

theorem val_unique {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {R : Type} [CommRing R]
    [IsLocalRing R] {z : Spec (CommRingCat.of R) ⟶ X} (hg : IsCptGen ξ) {a : Ω} {r r' : R} (h : ValAt ξ z a r)
    (h' : ValAt ξ z a r') : r = r' := by
  obtain ⟨h1, s, hs, rfl⟩ := h
  obtain ⟨h2, s', hs', rfl⟩ := h'
  have : s = s' := hg.inj ⟨centre z, h1⟩ (hs.trans hs'.symm)
  rw [this]

theorem exists_fibreLat_rank : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H)
    (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type)
    [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y)
    (z : Sp ℂ ⟶ 𝔐.X), 1 ≤ D.p + D.q → 𝔐.Interior z →
    ∃ (κ : c.F →+* ℂ) (p : Sp ℂ ⟶ Xo.X) (g : ℕ) (Λ : Type) (_ : AddCommGroup Λ) (_ : Module (𝓞 E) Λ)
      (R : RiemLat E g Λ), IsOver 𝔐 z κ p ∧ FibreLat 𝔐.t z R ∧
        ∀ s, Module.finrank ℂ (eigSp R.B (κ.comp (labelEmb c s))) = labelRk D s := by
  intro hG E _ _ _ H D l Xo c Y S Ω _ K _ J _ y 𝔐 z hD hz
  obtain ⟨κ, p, hO⟩ := exists_isOver E H D l Xo c Y S Ω K J y 𝔐 z hz
  obtain ⟨g, ty, hty⟩ := GlobalTheory.AllClasses.exists_isTypeFn H D.p D.q
  have hN : N1c := hG.1.2.2.1
  let j : KA l →+* c.F := (IntermediateField.inclusion c.le).toRingHom
  let ρF : c.F := j (baseKA l).ρ
  have hρF : (ρF : ℂ) = H.rt0 := rfl
  have hσ : p ≫ Xo.s = spMap (κ.comp j) := by
    obtain ⟨x, -, h1, h2⟩ := hO
    rw [← h1, Category.assoc, pullback.condition, ← Category.assoc, h2, Chg.spMap_comp']
  have hsq : (κ ρF) ^ 2 = H.rt0 ^ 2 := by
    have e : ρF ^ 2 = -((H.d : ℕ) : c.F) := Subtype.ext (by
      push_cast
      rw [hρF]
      exact H.sqrt_neg_disc_sq)
    rw [← map_pow, e, H.sqrt_neg_disc_sq]
    simp
  have hconj : starRingEnd ℂ H.rt0 = -H.rt0 := conj_eq_neg_of_sq H.d_prime.pos H.sqrt_neg_disc_sq
  have hne : H.rt0 ≠ -H.rt0 := by
    intro h
    have h0 : H.rt0 = 0 := by
      have : (2 : ℂ) * H.rt0 = 0 := by linear_combination h
      simpa using this
    have h1 := H.sqrt_neg_disc_sq
    rw [h0] at h1
    have h2 : ((H.d : ℕ) : ℂ) = 0 := by simpa using h1.symm
    exact H.d_prime.pos.ne' (by exact_mod_cast h2)
  by_cases hρ : κ ρF = H.rt0
  · obtain ⟨FU⟩ := hN E H D l Xo (κ.comp j) g ty hD hρ hty
    obtain ⟨i, P, hP, hu⟩ := FU.onto p hσ
    obtain ⟨⟨R, -, hF, hr⟩, -⟩ := GlobalTheory.T.period_riemann_lattice_fibre E H D l Xo (κ.comp j) g ty FU i P hty hP
    refine ⟨κ, p, g, _, inferInstance, inferInstance, R, hO,
      GlobalTheory.T.riemann_lattice_over_point E H D l Xo c Y S Ω K J y 𝔐 z κ p g _ _ hO (hu ▸ hF), fun s => ?_⟩
    obtain ⟨τ, hτ, hτρ⟩ := exists_emb_label E H l c κ s
    have h := hτρ ρF hρF
    rw [hτ, hr τ]
    rcases s with s | s
    · have h' : τ (H.rt : E) = H.rt0 := h.trans hρ
      simp [h']
    · have h' : τ (H.rt : E) = -H.rt0 := h.trans (by simp [hρ])
      simp [h', hne.symm]
  · have hneg : κ ρF = -H.rt0 := (sq_eq_sq_iff_eq_or_eq_neg.1 hsq).resolve_left hρ
    have hρ₁ : ((starRingEnd ℂ).comp (κ.comp j)) (baseKA l).ρ = H.rt0 := by
      show starRingEnd ℂ (κ ρF) = H.rt0
      rw [hneg, map_neg, hconj, neg_neg]
    obtain ⟨FU⟩ := hN E H D l Xo ((starRingEnd ℂ).comp (κ.comp j)) g ty hD hρ₁ hty
    have hσ₁ : (spMap (starRingEnd ℂ) ≫ p) ≫ Xo.s = spMap ((starRingEnd ℂ).comp (κ.comp j)) := by
      rw [Category.assoc, hσ]
      exact (Chg.spMap_comp' _ _).symm
    obtain ⟨i, P, hP, hu⟩ := FU.onto _ hσ₁
    obtain ⟨-, R, -, hF, hr⟩ := GlobalTheory.T.period_riemann_lattice_fibre E H D l Xo _ g ty FU i P hty hP
    have hcc : spMap (starRingEnd ℂ) ≫ spMap (starRingEnd ℂ) ≫ p = p := by
      have e : (starRingEnd ℂ).comp (starRingEnd ℂ) = RingHom.id ℂ := RingHom.ext fun x => by simp
      rw [← Category.assoc, ← Chg.spMap_comp', e]
      simp [spMap]
    rw [hu, hcc] at hF
    refine ⟨κ, p, g, _, inferInstance, inferInstance, R, hO,
      GlobalTheory.T.riemann_lattice_over_point E H D l Xo c Y S Ω K J y 𝔐 z κ p g _ _ hO hF, fun s => ?_⟩
    obtain ⟨τ, hτ, hτρ⟩ := exists_emb_label E H l c κ s
    have h := hτρ ρF hρF
    rw [hτ, hr τ]
    rcases s with s | s
    · have h' : τ (H.rt : E) = -H.rt0 := h.trans hneg
      simp [h', hne.symm]
    · have h' : τ (H.rt : E) = H.rt0 := h.trans (by simp [hneg])
      simp [h']

theorem exists_riemLat_of_interior : ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (z : Sp ℂ ⟶ 𝔐.X), 1 ≤ D.p + D.q → 𝔐.Interior z → Top.Given → ∀ (A₀ : Type) (v : A₀ → (epsAt z ⟶ 𝔐.t.G)), (∀ i, IsTanAt 𝔐.t.G z (v i)) → ∃ (g : ℕ) (Λ : Type) (_ : AddCommGroup Λ) (_ : Module (𝓞 E) Λ) (R : RiemLat E g Λ) (x : A₀ → Fin g → ℂ), FibreLatVec 𝔐.t z R x v ∧ (∀ i j, HodgeIP 𝔐.t.G 𝔐.t.PP.L z (v i) (v j) (Real.pi * R.ip (x i) (x j))) ∧ ∀ σ, 𝔐.LabVal z id σ → ∀ s, Module.finrank ℂ (eigSp R.B (σ s)) = labelRk D s := by
  intro _ E _ _ _ H D l Xo c Y S Ω _ K _ J _ y 𝔐 z hD hz hG A₀ v hv
  obtain ⟨κ, p, g, Λ, i₁, i₂, R, hO, hF, hr⟩ := exists_fibreLat_rank hG E H D l Xo c Y S Ω K J y 𝔐 z hD hz
  haveI : CharZero Ω := charZero_of_injective_ringHom 𝔐.cst.injective
  have hpol := HodgeMetric.polarisedAt_of_interior E H D l Xo c Y S Ω K J y 𝔐 z hz
  obtain ⟨x, hx⟩ := fibreLatVec_of_fibreLat hpol hF v hv
  refine ⟨g, Λ, i₁, i₂, R, x, hx, fun i j => hodgeInnerProduct_eq_pi_mul_riemannForm hx hv i j, fun σ hσ s => ?_⟩
  have e : σ s = κ.comp (labelEmb c s) := RingHom.ext fun a =>
    val_unique 𝔐.tie.gen (hσ s a) (val_cst E H D l Xo c Y S Ω K J y 𝔐 z κ p hO (labelEmb c s a))
  rw [e]
  exact hr s

end GlobalTheory.CompanionTheory.Ar.Cusp.FibreEx
end
end

