import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CmPackPeriodProduct
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCMFrame
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0161
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0251
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0183
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0254
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0205
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0061
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0072
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0060
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0125
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptInteriorFlag
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeInnerProductAdjoint
import Development.AutomorphicSpectrum.Statements.GeometryStatements.KeyBadSt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsThetaMeanSquareNorm
import Development.AutomorphicSpectrum.Statements.GeometryStatements.ZhangDimensionPushDownGrassmannianHeightBounds
import GroundTheory.HeightsAndTheta.Heights.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsBundles
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0105
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0113
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0004
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0012
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PairSumFrameAtPoint

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CmPackPeriodProductStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CM GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_pack_period_product : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n) (Z : ∀ b : Bool, Curve0 H (sgnRt H b)) (P : (FU.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (FU.Di i) ty P) (X : CMPack Z c FU i hP) (b : Bool) (τ : E →+* ℂ) (n : ℕ) (a : Fin n → PureType.lat hP (sgnRt H b)) (v : Vecs X.y n) (s : X.K →+* ℂ) (y' : Sp ℂ ⟶ Xo.XF c) (v' : Vecs y' n) (r : ℝ), τ (H.rt : E) = sgnRt H b → (∀ k, X.IsCMVec b τ (a k) (v k)) → y' = spMap s ≫ X.y → (∀ k, (v' k).left = spMap (dualMap s) ≫ (v k).left) → IsLieNormSq (Z b).C.P (Z b).C.v ((s.comp (IntermediateField.inclusion (X.hM b)).toRingHom).comp (algebraMap (𝓞 (Z b).M) (Z b).M)) r → IsHodgeGram Xo.univ.t.G Xo.univ.t.PP.L (under y') v' (Matrix.of fun k k' => r * ((X.ε b : ℤ) : ℂ) * s (X.β (tauE c τ ((H.rt : E) * sesq (FU.Di i) (a k) (a k'))))) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fl.GInf.hodgeGram_cmVec | exact GlobalTheory.CompanionTheory.Ar.Fl.GInf.hodgeGram_cmVec | (intros; apply GlobalTheory.CompanionTheory.Ar.Fl.GInf.hodgeGram_cmVec <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CmPackPureFrameOpen
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CM GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.Fl.CMValue

theorem det_rows (p q : ℕ) (z₁ z₂ : ℂ) (G : Matrix (Fin q) (Fin q) ℂ) (hz : z₂ ≠ 0) (hG : G.det ≠ 0) :
    (Matrix.fromRows (Matrix.fromCols (z₁ • (1 : Matrix (Fin p) (Fin p) ℂ)) (0 : Matrix (Fin p) (Fin q) ℂ))
      (Matrix.fromCols (0 : Matrix (Fin q) (Fin p) ℂ) (z₂⁻¹ • G⁻¹))).det * (z₂ ^ q * G.det) = z₁ ^ p := by
  rw [Matrix.fromRows_fromCols_eq_fromBlocks, Matrix.det_fromBlocks_zero₂₁, Matrix.det_smul, Matrix.det_one,
    Matrix.det_smul, Matrix.det_nonsing_inv]
  simp only [Fintype.card_fin, mul_one, Ring.inverse_eq_inv', inv_pow]
  field_simp

theorem range_comp {K L : Type} [Field K] [Field L] (f : K →+* L) {Y : Scheme.{0}} (y : Sp K ⟶ Y) :
    Set.range (spMap f ≫ y) = Set.range y := by
  ext t
  constructor
  · rintro ⟨s, rfl⟩
    exact ⟨spMap f s, by simp⟩
  · rintro ⟨s, rfl⟩
    obtain ⟨s'⟩ : Nonempty (Sp L) := inferInstance
    refine ⟨s', ?_⟩
    have : spMap f s' = s := Subsingleton.elim (α := PrimeSpectrum K) _ _
    simp [this]

theorem tyPart_smul {E : Type} [Field E] {g : ℕ} (ty : Fin g → (E →+* ℂ)) (τ : E →+* ℂ) (a : ℂ) (z : Fin g → ℂ) :
    tyPart ty τ (a • z) = a • tyPart ty τ z := by
  ext k
  simp only [tyPart, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> simp

end GlobalTheory.CompanionTheory.Ar.Fl.CMValue

namespace GlobalTheory.CompanionTheory.Ar.Fl.CMValue

theorem conj_cmHostRoot_ne_self {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) :
    starRingEnd ℂ H.rt0 ≠ H.rt0 := by
  intro h
  obtain ⟨r, hr⟩ := Complex.conj_eq_iff_real.1 h
  have h1 := H.sqrt_neg_disc_sq
  rw [hr] at h1
  have h2 : r ^ 2 = -(H.d : ℝ) := by exact_mod_cast h1
  have h3 : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  nlinarith [sq_nonneg r]

end GlobalTheory.CompanionTheory.Ar.Fl.CMValue

theorem GlobalTheory.CompanionTheory.Ar.Fl.CMValue.value_on_cmFrame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n) (Z : ∀ b : Bool, Curve0 H (sgnRt H b)) (P : (FU.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (FU.Di i) ty P) (X : CMPack Z c FU i hP) (x : Fin D.p ⊕ Fin D.q → (FU.Di i).La) (hx : IsPure hP x) (U : Set (Xo.XF c)) (τ : E →+* ℂ) (φ : FrameFn Xo c) (e : Fin D.p ⊕ Fin D.q → (FU.Di i).La) (ρ : ℂ) (T : Matrix (Fin D.p ⊕ Fin D.q) (Fin D.p ⊕ Fin D.q) E) (v : Vecs X.y D.p) (w : Vecs X.y D.q), IsTypeFn H D.p D.q ty → τ (H.rt : E) = H.rt0 → (∀ P (y : Sp ℂ ⟶ Xo.XF c), IsPeriod (FU.Di i) ty P → under y = FU.u i P → y ≫ pullback.snd _ _ = spMap (algebraMap c.F ℂ) → Set.range y ⊆ U) → IsLineFn U τ φ → LinearIndependent (𝓞 E) e → IsConstMul U τ φ FU i e ρ → LinearIndependent (𝓞 E) x → IsTransition (FU.Di i) x e T → X.IsCMFrame τ hx v w → IsFramed U τ X.β X.y v w ∧ ((φ X.K X.y v w : X.K) : ℂ) * τ T.det * (Z true).z ^ D.p = ρ * (Z false).z ^ D.q * τ (gramE (FU.Di i) (x ∘ Sum.inr)).det := by
  intro E _ _ _ H D l Xo c g ty FU i Z P hP X x hx U τ φ e ρ T v w hty hτ hmem hline he hconst hxi hT hfr
  have hfr0 := (GlobalTheory.T.cm_pack_pure_frame E H D l Xo c g ty FU i Z P hP X x hx τ hty hτ hxi).2 v w hfr
  let f : X.K →+* ℂ := algebraMap X.K ℂ
  have hcomp : f.comp X.β = algebraMap c.F ℂ := by ext a; rfl
  let y' : Sp ℂ ⟶ Xo.XF c := spMap f ≫ X.y
  have hyu : under y' = spMap f ≫ under X.y := Category.assoc _ _ _
  have hy'u : under y' = FU.u i P := hyu.trans X.pt
  have hy's : y' ≫ pullback.snd _ _ = spMap (algebraMap c.F ℂ) := by
    rw [Category.assoc, X.hy, ← hcomp, spMap_comp]
  have hU : Set.range X.y ⊆ U := by
    rw [← CMValue.range_comp f X.y]
    exact hmem P y' hP hy'u hy's
  have hF : IsFramed U τ X.β X.y v w := ⟨hfr0.1, hU, hfr0.2.2⟩
  obtain ⟨⟨v', hv'⟩, hv⟩ := GlobalTheory.T.tangent_vectors_base_change E H Xo.X Xo.univ.t X.K ℂ f (under X.y) (under y')
    (X.β.comp (tauIn c τ)) D.p v hyu
  obtain ⟨⟨w', hw'⟩, hw⟩ := GlobalTheory.T.tangent_vectors_base_change E H Xo.X Xo.univ.t X.K ℂ f (under X.y) (under y')
    (X.β.comp (tauIn c (ComplexEmbedding.conjugate τ))) D.q w hyu
  have hF' : IsFramed U τ (algebraMap c.F ℂ) y' v' w' := by
    refine ⟨hy's, ?_, ?_, ?_⟩
    · rw [CMValue.range_comp f X.y]; exact hU
    · have := (hv v' hv').1 hF.2.2.1
      rwa [← RingHom.comp_assoc, hcomp] at this
    · have := (hw w' hw').1 hF.2.2.2
      rwa [← RingHom.comp_assoc, hcomp] at this
  have hz₂ : (Z false).z ≠ 0 := GlobalTheory.T.curve_z_ne_zero E H _ (Z false)
  have hcard : Fintype.card (Fin D.p ⊕ Fin D.q) = (FU.Di i).p + (FU.Di i).q := by
    simp [(FU.sig i).1, (FU.sig i).2]

  have hTdet : T.det ≠ 0 := by
    obtain ⟨T', hT', -, hT'det, -⟩ := GlobalTheory.T.exists_transition_matrix_gram E H (FU.Di i) (Fin D.p ⊕ Fin D.q) x e hcard he
    have hge := (GlobalTheory.T.gram_det_ne_zero_local_basis_cofinite E H (FU.Di i) (Fin D.p ⊕ Fin D.q) e hcard he).1
    have hmul : T * gramE (FU.Di i) e = T' * gramE (FU.Di i) e := by
      ext m n
      simp only [Matrix.mul_apply, gramE, Matrix.of_apply]
      rw [← hT m (e n), ← hT' m (e n)]
    have hTT : T = T' := by
      have hu : IsUnit (gramE (FU.Di i) e).det := isUnit_iff_ne_zero.2 hge
      rw [← Matrix.mul_nonsing_inv_cancel_right _ T hu, hmul, Matrix.mul_nonsing_inv_cancel_right _ T' hu]
    rw [hTT]
    exact hT'det hxi
  have hconst' := GlobalTheory.T.transition_matrix_period_frame E H D l Xo c g ty FU i U τ φ e x T ρ he hT hTdet hconst

  have orth : ∀ a j, sesq (FU.Di i) (x (.inl a)) (x (.inr j)) = 0 ∧ sesq (FU.Di i) (x (.inr j)) (x (.inl a)) = 0 :=
    fun a j => GlobalTheory.T.pure_type_lattices_orthogonal E H (FU.Di i) g ty P hP _ _ (hx.1 a) (hx.2 j)
  have hgram : gramE (FU.Di i) x =
      Matrix.fromBlocks (gramE (FU.Di i) (x ∘ Sum.inl)) 0 0 (gramE (FU.Di i) (x ∘ Sum.inr)) := by
    ext m n
    rcases m with a | j <;> rcases n with b | k
    · rfl
    · exact (orth a k).1
    · exact (orth b j).2
    · rfl
  have hG₀ : (gramE (FU.Di i) (x ∘ Sum.inr)).det ≠ 0 := by
    have h := (GlobalTheory.T.gram_det_ne_zero_local_basis_cofinite E H (FU.Di i) (Fin D.p ⊕ Fin D.q) x hcard hxi).1
    rw [hgram, Matrix.det_fromBlocks_zero₂₁] at h
    exact right_ne_zero_of_mul h
  let G : Matrix (Fin D.q) (Fin D.q) ℂ := τ.mapMatrix (gramE (FU.Di i) (x ∘ Sum.inr))
  have hGdet : G.det = τ (gramE (FU.Di i) (x ∘ Sum.inr)).det := (RingHom.map_det τ _).symm
  have hG : G.det ≠ 0 := by
    rw [hGdet]
    exact (map_ne_zero τ).2 hG₀
  have hGu : IsUnit G.det := isUnit_iff_ne_zero.2 hG

  have hDV : ∀ a, IsDerivAt0 (fun z => (FU.ex i P z).left)
      ((Z true).z • tyPart ty τ (P (x (.inl a)))) (v' a).left := by
    intro a
    rw [hv' a]
    exact GlobalTheory.T.cm_pack_eigen_period E H D l Xo c g ty FU i Z P hP X true τ ⟨x (.inl a), hx.1 a⟩ (v a) (hfr.1 a)
  have hDW : ∀ j, IsDerivAt0 (fun z => (FU.ex i P z).left)
      ((Z false).z • tyPart ty (ComplexEmbedding.conjugate τ) (P (x (.inr j)))) (w' j).left := by
    intro j
    rw [hw' j]
    exact GlobalTheory.T.cm_pack_eigen_period E H D l Xo c g ty FU i Z P hP X false (ComplexEmbedding.conjugate τ)
      ⟨x (.inr j), hx.2 j⟩ (w j) (hfr.2 j)
  have hvan : ∀ a, tyPart ty (ComplexEmbedding.conjugate τ) (P (x (.inl a))) = 0 := by
    intro a
    ext k
    by_cases hk : ty k = ComplexEmbedding.conjugate τ
    · have : P (x (.inl a)) k = 0 := by
        apply hx.1 a k
        rw [hk, ComplexEmbedding.conjugate_coe_eq, hτ]
        simpa [sgnRt] using CMValue.conj_cmHostRoot_ne_self H
      simp [tyPart, this]
    · simp [tyPart, hk]
  have hC : ∀ a, tyPart ty τ (∑ m, Matrix.fromCols ((Z true).z • (1 : Matrix (Fin D.p) (Fin D.p) ℂ))
      (0 : Matrix (Fin D.p) (Fin D.q) ℂ) a m • P (x m)) = (Z true).z • tyPart ty τ (P (x (.inl a))) := by
    intro a
    rw [← CMValue.tyPart_smul]
    congr 1
    simp [Fintype.sum_sum_type, Matrix.one_apply, ite_smul]
  have hB : ∀ n, tyPart ty (ComplexEmbedding.conjugate τ) (P (x n)) =
      ∑ j, Matrix.fromCols (0 : Matrix (Fin D.q) (Fin D.p) ℂ) ((Z false).z⁻¹ • (1 : Matrix (Fin D.q) (Fin D.q) ℂ)) j n •
        ((Z false).z • tyPart ty (ComplexEmbedding.conjugate τ) (P (x (.inr j)))) := by
    intro n
    rcases n with a | k
    · simp [hvan a]
    · simp [Matrix.one_apply, ite_smul, smul_smul, hz₂]
  have hFm : ∀ j n, ∑ m, Matrix.fromCols (0 : Matrix (Fin D.q) (Fin D.p) ℂ) ((Z false).z⁻¹ • G⁻¹) j m *
      τ (sesq (FU.Di i) (x m) (x n)) =
      Matrix.fromCols (0 : Matrix (Fin D.q) (Fin D.p) ℂ) ((Z false).z⁻¹ • (1 : Matrix (Fin D.q) (Fin D.q) ℂ)) j n := by
    intro j n
    rw [Fintype.sum_sum_type]
    rcases n with a | k
    · simp [(orth a _).2]
    · have h : ((Z false).z⁻¹ • G⁻¹) * G = (Z false).z⁻¹ • (1 : Matrix (Fin D.q) (Fin D.q) ℂ) := by
        rw [Matrix.smul_mul, Matrix.nonsing_inv_mul _ hGu]
      have h' := congrFun (congrFun h j) k
      rw [Matrix.mul_apply] at h'
      simpa [G, gramE, RingHom.mapMatrix_apply] using h'
  have key := hconst' P y' v' w' _ _ _ _ _ hP hy'u hF' hDV hDW hC hB hFm
  have hnat : φ ℂ y' v' w' = f (φ X.K X.y v w) := hline.nat X.K ℂ f X.β X.y v w y' v' w' hF rfl hv' hw'
  have hrows := CMValue.det_rows D.p D.q (Z true).z (Z false).z G hz₂ hG
  refine ⟨hF, ?_⟩
  have hτT : τ T.det ≠ 0 := (map_ne_zero τ).2 hTdet
  rw [hnat] at key
  change f (φ X.K X.y v w) * τ T.det * (Z true).z ^ D.p = _
  rw [← hrows, ← hGdet]
  have key' : f (φ X.K X.y v w) * (Matrix.fromRows (Matrix.fromCols ((Z true).z • (1 : Matrix (Fin D.p) (Fin D.p) ℂ))
      (0 : Matrix (Fin D.p) (Fin D.q) ℂ)) (Matrix.fromCols (0 : Matrix (Fin D.q) (Fin D.p) ℂ) ((Z false).z⁻¹ • G⁻¹))).det * τ T.det = ρ := by
    rw [key]
    field_simp
  rw [← key']
  ring
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GramMatrixChangeFrameStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gram_matrix_change_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) (r : ℕ) (b : Fin r → 𝔐.Li) (Γ Γ' : Matrix (Fin r) (Fin r) ℂ), HodgeMetric.PolarisedAt 𝔐.t z → 𝔐.M.GramAt 𝔐.t.PP.L z b Γ → 𝔐.M.GramAt 𝔐.t.PP.L z b Γ' → Γ = Γ' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HodgeMetric.gramAt_unique_of_polarisedAt | exact GlobalTheory.CompanionTheory.Ar.HodgeMetric.gramAt_unique_of_polarisedAt | (intros; apply GlobalTheory.CompanionTheory.Ar.HodgeMetric.gramAt_unique_of_polarisedAt <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GramMatrixTwoFramesStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gram_matrix_two_frames : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) (r : ℕ) (b b' : Fin r → 𝔐.Li) (Γ Γ' : Matrix (Fin r) (Fin r) ℂ) (T : Matrix (Fin r) (Fin r) Ω) (Tz : Matrix (Fin r) (Fin r) ℂ), HodgeMetric.PolarisedAt 𝔐.t z → 𝔐.M.GramAt 𝔐.t.PP.L z b Γ → 𝔐.M.GramAt 𝔐.t.PP.L z b' Γ' → (∀ q, b' q = ∑ p, T p q • b p) → (∀ p q, ValAt 𝔐.ξ z (T p q) (Tz p q)) → Γ' = Tz.conjTranspose * Γ * Tz := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HodgeMetric.gramAt_change | exact GlobalTheory.CompanionTheory.Ar.HodgeMetric.gramAt_change | (intros; apply GlobalTheory.CompanionTheory.Ar.HodgeMetric.gramAt_change <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptInteriorFlagStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_cpt_interior_flag : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (Fl : 𝔐.Flag), Function.Injective β → ∀ (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X), 𝔐.Interior z → ∀ s (i : Fin (labelRk D s)) (t : Ω), ((𝔐.V s).gr (Fl.b s) i).IsGenAt ⟨centre z, 𝔐.all _⟩ t → ∃ ν : ℝ, 0 < ν ∧ ∀ (t' : Ω) (ν' : ℝ), 𝔐.M.IsGrNorm 𝔐.t.PP.L (𝔐.V s) (Fl.b s) i z t' ν' ↔ ∃ u : ℂ, u ≠ 0 ∧ ValAt 𝔐.ξ z (t' / t) u ∧ ν' = ‖u‖ * ν := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GrNorm.exists_norm | exact GlobalTheory.CompanionTheory.Ar.GrNorm.exists_norm | (intros; apply GlobalTheory.CompanionTheory.Ar.GrNorm.exists_norm <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeGeneratedSumSpecializationFrame
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix ComplexOrder

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.PeriodIndep

section Dual

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Finset ℕ}
  {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω}

theorem disjoint_sup_biSup {α I : Type} [CompleteLattice α] [IsModularLattice α] {t : I → α} (hind : iSupIndep t)
    (a b : I) : Disjoint (t a ⊔ t b) (⨆ s ∈ {s | s ≠ a ∧ s ≠ b}, t s) := by
  by_cases hab : a = b
  · subst hab
    rw [sup_idem]
    exact hind.disjoint_biSup fun h => h.1 rfl
  · refine Disjoint.disjoint_sup_left_of_disjoint_sup_right (hind.disjoint_biSup fun h => h.2 rfl) ?_
    have h1 : t b ≤ ⨆ j, ⨆ (_ : j ≠ a), t j :=
      le_iSup₂_of_le (f := fun j (_ : j ≠ a) => t j) b (fun h => hab h.symm) le_rfl
    have h2 : (⨆ s ∈ {s | s ≠ a ∧ s ≠ b}, t s) ≤ ⨆ j, ⨆ (_ : j ≠ a), t j :=
      iSup₂_le fun s hs => le_iSup₂_of_le (f := fun j (_ : j ≠ a) => t j) s hs.1 le_rfl
    exact (hind a).mono_right (sup_le h1 h2)

theorem exists_dual_sup (𝔐 : HodgeCpt Y S y) (hind : iSupIndep 𝔐.Vgen) (q : Cpt 𝔐.ξ)
    (hV : ∀ s, 𝔐.V s q = 𝔐.dR s q) (hlat : 𝔐.M.lat q = ⨆ s, 𝔐.dR s q) (a b : CMType H ⊕ CMType H) {N : ℕ}
    (bb : Fin N → ↥(𝔐.Vgen a ⊔ 𝔐.Vgen b))
    (hfr : (Lat.comap (fun p => 𝔐.V a p ⊔ 𝔐.V b p) (𝔐.Vgen a ⊔ 𝔐.Vgen b).subtype).IsFrameAt bb q) :
    ∃ π : Fin N → Module.Dual Ω 𝔐.Li, (∀ j l, π j (bb l : 𝔐.Li) = if j = l then 1 else 0) ∧
      ∀ j, ∀ e ∈ 𝔐.M.lat q, π j e ∈ regAt 𝔐.ξ q := by
  classical
  obtain ⟨hli, hsp⟩ := hfr
  obtain ⟨W, hW, hc⟩ := (disjoint_sup_biSup hind a b).symm.exists_isCompl
  let pr : 𝔐.Li →ₗ[Ω] ↥(𝔐.Vgen a ⊔ 𝔐.Vgen b) := Submodule.linearProjOfIsCompl _ _ hc.symm
  have hker : LinearMap.ker (Fintype.linearCombination Ω bb) = ⊥ := by
    refine LinearMap.ker_eq_bot'.2 fun m hm => funext fun k => ?_
    exact Fintype.linearIndependent_iff.1 hli m (by rwa [Fintype.linearCombination_apply] at hm) k
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective _ hker
  have hgb : ∀ l, g (bb l) = Pi.single l 1 := fun l => by
    have := LinearMap.congr_fun hg (Pi.single l 1)
    simpa [Fintype.linearCombination_apply_single] using this
  have hpr : ∀ x : ↥(𝔐.Vgen a ⊔ 𝔐.Vgen b), pr (x : 𝔐.Li) = x := fun x =>
    Submodule.linearProjOfIsCompl_apply_left hc.symm x
  refine ⟨fun j => (LinearMap.proj j).comp (g.comp pr), fun j k => ?_, fun j e he => ?_⟩
  · simp only [LinearMap.comp_apply, hpr, hgb, LinearMap.proj_apply]
    simp [Pi.single_apply]
  · rw [hlat] at he
    induction he using Submodule.iSup_induction' with
    | mem s' x hx =>
      by_cases e : s' = a ∨ s' = b
      · have hxs : x ∈ 𝔐.Vgen a ⊔ 𝔐.Vgen b := by
          rcases e with rfl | rfl
          · exact Submodule.mem_sup_left hx.2
          · exact Submodule.mem_sup_right hx.2
        have hxV : x ∈ 𝔐.V a q ⊔ 𝔐.V b q := by
          rcases e with rfl | rfl
          · exact Submodule.mem_sup_left ((hV _).symm ▸ hx)
          · exact Submodule.mem_sup_right ((hV _).symm ▸ hx)
        have hm : (⟨x, hxs⟩ : ↥(𝔐.Vgen a ⊔ 𝔐.Vgen b)) ∈
            Lat.comap (fun p => 𝔐.V a p ⊔ 𝔐.V b p) (𝔐.Vgen a ⊔ 𝔐.Vgen b).subtype q := hxV
        rw [hsp] at hm
        obtain ⟨c', hc'⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hm
        have e1 : ∀ k, (c' k • bb k) = ((c' k : regAt 𝔐.ξ q) : Ω) • bb k := fun _ => rfl
        have e2 : pr x = ∑ k, ((c' k : regAt 𝔐.ξ q) : Ω) • bb k := by
          rw [show pr x = ⟨x, hxs⟩ from hpr ⟨x, hxs⟩, ← hc']
          exact Finset.sum_congr rfl fun k _ => e1 k
        simp only [LinearMap.comp_apply, e2, map_sum, map_smul, hgb, LinearMap.proj_apply]
        refine sum_mem fun k _ => ?_
        rw [smul_eq_mul]
        refine mul_mem (c' k).2 ?_
        rw [Pi.single_apply]
        split_ifs
        · exact one_mem _
        · exact zero_mem _
      · have hxW : x ∈ W := by
          push_neg at e
          exact hW (Submodule.mem_iSup_of_mem s' (Submodule.mem_iSup_of_mem e hx.2))
        have : pr x = 0 := Submodule.linearProjOfIsCompl_apply_right' hc.symm hxW
        simp [this]
    | zero => simpa using zero_mem _
    | add x y _ _ hx hy => simpa using add_mem hx hy

end Dual

theorem values_indep : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (a b : CMType H ⊕ CMType H) (N : ℕ) (bb : Fin N → ↥(𝔐.Vgen a ⊔ 𝔐.Vgen b)) (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) (h : genPt 𝔐.ξ ⤳ centre z) (Vz : Type) [AddCommGroup Vz] [Module ℂ Vz] (MR : LieModel 𝔐.t.G z Vz) (e : Fin N → Vz), (Lat.comap (fun p => 𝔐.V a p ⊔ 𝔐.V b p) (𝔐.Vgen a ⊔ 𝔐.Vgen b).subtype).IsFrameAt bb ⟨centre z, h⟩ → (∀ k, 𝔐.M.ValAt z ((bb k : ↥(𝔐.Vgen a ⊔ 𝔐.Vgen b)) : 𝔐.Li) (MR.pt (e k))) → LinearIndependent ℂ e := by
  intro E _ _ _ H D l Xo c Y S Ω _ _ K _ J _ y 𝔐 a b N bb z h Vz _ _ MR e hfr hval
  classical
  have hβ : Function.Injective (algebraMap (𝓞 c.F) c.F) := FaithfulSMul.algebraMap_injective _ _
  have hξ : IsCptGen 𝔐.ξ := 𝔐.tie.gen
  have hsm : Smooth 𝔐.t.G.hom := 𝔐.t.semi.smooth
  obtain ⟨-, -, -, -, -, -, hind, -⟩ := GlobalTheory.T.hodge_cpt_interior_generic E H D l Xo c _ _ Y S Ω K J y 𝔐 hβ
  obtain ⟨hV, -, hlat⟩ := GlobalTheory.T.hodge_cpt_away_from_primes E H D l Xo c _ _ Y S Ω K J y 𝔐 hβ ⟨centre z, h⟩
    fun r hr => GrNorm.not_inFibre hξ h hr
  obtain ⟨π, hπ, hreg⟩ := exists_dual_sup 𝔐 hind ⟨centre z, h⟩ hV hlat a b bb hfr
  have hg : ∀ j, ∃ g : Vz →ₗ[ℂ] ℂ, ∀ k, g (e k) = if j = k then 1 else 0 := fun j => by
    obtain ⟨g, hg⟩ := GlobalTheory.T.lattice_regular_at_local_point 𝔐.X 𝔐.t.G Ω 𝔐.ξ 𝔐.Li 𝔐.M ℂ z h Vz MR (π j) hξ (hreg j)
    refine ⟨g, fun k => hg (bb k : 𝔐.Li) _ _ (hval k) ?_⟩
    rw [hπ j k]
    split_ifs
    · exact RootHt.ArchB.val_one h
    · exact RootHt.ArchB.val_zero h
  choose g hg using hg
  refine Fintype.linearIndependent_iff.2 fun w hw j => ?_
  have := congrArg (g j) hw
  simpa [map_sum, hg, Finset.sum_ite_eq] using this

end GlobalTheory.CompanionTheory.Ar.PeriodIndep
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeInnerProductAdjointStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_inner_product_adjoint : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (z : Spec (CommRingCat.of ℂ) ⟶ X) (v w : epsAt z ⟶ t.G) (a : 𝓞 E) (c : ℂ), (∃ (t' : SAB H (Sp ℂ)) (_ : SABMap t' t z), IsProper t'.G.hom ∧ Out.RelAmple t'.G t'.PP.L) → IsTanAt t.G z v → IsTanAt t.G z w → (HodgeIP t.G t.PP.L z (v ≫ t.act.act a) w c ↔ HodgeIP t.G t.PP.L z v (w ≫ t.act.act (H.bar a)) c) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.hodgeInnerProduct_act_adjoint | exact GlobalTheory.CompanionTheory.Ar.hodgeInnerProduct_act_adjoint | (intros; apply GlobalTheory.CompanionTheory.Ar.hodgeInnerProduct_act_adjoint <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeMetricFrameInner
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Sl.FrameGram

theorem inner_eq_pi_herm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (D : PPData H L) (σ : L →+* ℂ) (a : D.Frame σ) (x y : D.B.carrier) (c c' : Fin D.g → ℂ), D.IsVec a x c → D.IsVec a y c' → ((D.B.metric.form σ).inner ((1 : ComplexAt σ) ⊗ₜ[𝓞 L] x) ((1 : ComplexAt σ) ⊗ₜ[𝓞 L] y) : ℂ) = Real.pi * a.herm c' c := by
  intro E _ _ _ H L _ _ D σ a x y c c' hx hy
  obtain ⟨t', m, hP, hA⟩ := GlobalTheory.T.complex_abelian_fibre_ample E H L D σ
  obtain ⟨hab, g, u, Hm, χ, hAH, d₁, d₂⟩ := FrameEx.exists_goodUnif E H _ D.t (emb σ) t' m hP hA
  have hp : IsGrpPullback t'.G D.t.G (emb σ) m.φ := m.cart
  obtain ⟨v, hlift, vA, hvA, hdiff⟩ := hx
  obtain ⟨w, hlift', wA, hwA, hdiff'⟩ := hy
  have e : spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ 𝟙 (Sp (𝓞 L)) = emb σ := Category.comp_id _
  let v₀ : epsAt (spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ 𝟙 (Sp (𝓞 L))) ⟶ D.t.G :=
    Over.homMk v.left (by simpa using Over.w v)
  let w₀ : epsAt (spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ 𝟙 (Sp (𝓞 L))) ⟶ D.t.G :=
    Over.homMk w.left (by simpa using Over.w w)
  have hl₀ : D.MB.Lifts (σ.comp (algebraMap (𝓞 L) L)) (𝟙 D.t.G.left) x v₀ := hlift
  have hl₁ : D.MB.Lifts (σ.comp (algebraMap (𝓞 L) L)) (𝟙 D.t.G.left) y w₀ := hlift'
  obtain ⟨hL, hvt, hwt, A', _, φ', g', u', Hm', χ', p, q, a', b', hp', hah', ep, eq', dp, dq, hval⟩ :=
    D.fib σ x y v₀ w₀ hl₀ hl₁
  have hp₀ : IsGrpPullback t'.G D.t.G (spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ 𝟙 (Sp (𝓞 L))) m.φ :=
    IsGrpPullback.congr hp e.symm rfl
  have hpz : IsGrpPullback A' D.t.G (emb σ) φ' := IsGrpPullback.congr hp' e rfl
  let x₁ : epsR ℂ ⟶ t'.G := (HodgeLin.tanEquiv hp₀).symm v₀
  let y₁ : epsR ℂ ⟶ t'.G := (HodgeLin.tanEquiv hp₀).symm w₀
  have hx₁ : HodgeLin.tanEquiv hp₀ x₁ = v₀ := (HodgeLin.tanEquiv hp₀).apply_symm_apply _
  have hy₁ : HodgeLin.tanEquiv hp₀ y₁ = w₀ := (HodgeLin.tanEquiv hp₀).apply_symm_apply _
  have tx₁ : IsTangent x₁ := (HodgeLin.isTangent_iff hp₀ x₁).2 (by rw [hx₁]; exact hvt)
  have ty₁ : IsTangent y₁ := (HodgeLin.isTangent_iff hp₀ y₁).2 (by rw [hy₁]; exact hwt)
  have lx₁ : x₁.left ≫ m.φ = v.left := congrArg (fun r => r.left) hx₁
  have ly₁ : y₁.left ≫ m.φ = w.left := congrArg (fun r => r.left) hy₁
  obtain ⟨cx, hcx, -⟩ := d₁ x₁ tx₁
  obtain ⟨cy, hcy, -⟩ := d₁ y₁ ty₁
  have T1 := GlobalTheory.T.hol_unif_compare_isogeny (Sp (𝓞 L)) D.t.G D.t.PP.L (emb σ) t'.G a.A m.φ a.φ g D.g u a.u Hm a.Hm χ a.χ D.t.PP.isLB
    hab hp a.cart d₁ d₂ hAH a.ah y₁ x₁ wA vA cy cx c' c ty₁ tx₁ (hwA.trans ly₁.symm) (hvA.trans lx₁.symm) hcy hcx
    hdiff' hdiff
  have T2 := GlobalTheory.T.hol_unif_compare_isogeny (Sp (𝓞 L)) D.t.G D.t.PP.L (emb σ) t'.G A' m.φ φ' g g' u u' Hm Hm' χ χ' D.t.PP.isLB
    hab hp hpz d₁ d₂ hAH hah' y₁ x₁ q p cy cx b' a' ty₁ tx₁ (eq'.trans ly₁.symm) (ep.trans lx₁.symm) hcy hcx dq dp
  have hH : a.herm c' c = hermForm Hm' b' a' := T1.trans T2.symm
  rw [hH]
  exact hval

end GlobalTheory.CompanionTheory.Ar.Sl.FrameGram
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolomorphicDiscOverNumberFieldRing
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.ConstEmbedding

theorem exists_spMap {A : Type} [CommRing A] (x : Sp ℂ ⟶ Sp A) : ∃ ψ : A →+* ℂ, spMap ψ = x :=
  ⟨(Spec.preimage x).hom, by
    show Spec.map (CommRingCat.ofHom (Spec.preimage x).hom) = x
    simp⟩

theorem exists_extend (F : Type) [Field F] [NumberField F] (ψ : 𝓞 F →+* ℂ) :
    ∃ τ : F →+* ℂ, τ.comp (algebraMap (𝓞 F) F) = ψ := by
  have hinj : Function.Injective ψ :=
    GlobalTheory.CompanionTheory.Ar.GrNorm.injective_of_algebraic (algebraMap (𝓞 F) F)
      (IsFractionRing.injective (𝓞 F) F) ψ
  refine ⟨IsFractionRing.lift hinj, RingHom.ext fun a => ?_⟩
  simp

theorem exists_embedding (F : Type) [Field F] [NumberField F] (X : Scheme.{0}) (q : X ⟶ Sp (𝓞 F)) (n : ℕ)
    (p : (Fin n → ℂ) → (Sp ℂ ⟶ X)) (hol : IsHolTo (Metric.ball 0 1) p) :
    ∃ τ : F →+* ℂ, ∀ u ∈ Metric.ball (0 : Fin n → ℂ) 1, p u ≫ q = spMap (τ.comp (algebraMap (𝓞 F) F)) := by
  choose ψ hψ using fun u => exists_spMap (p u ≫ q)
  choose κ hκ using fun u => exists_extend F (ψ u)
  have hd : ∀ a : 𝓞 F, DifferentiableOn ℂ (fun b => κ b (a : F)) (Metric.ball 0 1) := by
    intro a
    have h2 := ReciprocityTheory.ChartRestriction.G.PullbackSections.isHolTo_comp hol q
    have h3 := (h2 ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (𝓞 F))).inv a)).2
    have hset : Metric.ball (0 : Fin n → ℂ) 1 ⊆ {b ∈ Metric.ball (0 : Fin n → ℂ) 1 | ⊤ ≤ (p b ≫ q) ⁻¹ᵁ ⊤} :=
      fun b hb => ⟨hb, le_top⟩
    refine (h3.mono hset).congr fun b _ => ?_
    show κ b (a : F) = valAt' (p b ≫ q) ⊤ _
    rw [← hψ b, ← hκ b]
    exact (ReciprocityTheory.ChartRestriction.G.PullbackSections.valAt'_spMap ((κ b).comp (algebraMap (𝓞 F) F)) a).symm
  have h0 : (0 : Fin n → ℂ) ∈ Metric.ball (0 : Fin n → ℂ) 1 := Metric.mem_ball_self one_pos
  refine ⟨κ 0, fun u hu => ?_⟩
  have hc := GlobalTheory.CompanionTheory.Ar.Cusp.FamEx.embedding_const_preconnected (convex_ball (0 : Fin n → ℂ) 1).isPreconnected κ hd hu h0
  rw [← hc, hκ u, hψ u]

end GlobalTheory.CompanionTheory.Ar.ConstEmbedding
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieSignatureNumberFieldStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_signature_number_field : N1ab → PartI → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (t : SAB H (Sp L)), IsPrincipal t → (∃ (ρ : L) (p' q' : ℕ), ρ ^ 2 = -(H.d : L) ∧ ∀ (k : Type) [Field k] [IsAlgClosed k] (g : L →+* k) (τ : 𝓞 E →+* k), (τ H.rt = g ρ → LieMult t.act (spMap g) τ p') ∧ (τ H.rt ≠ g ρ → LieMult t.act (spMap g) τ q')) → ∃ (L' : Type) (_ : Field L') (_ : NumberField L') (e : L →+* L') (t' : SAB H (Sp (𝓞 L'))) (tK : SAB H (Sp L')), Nonempty (SABMap tK t' (spMap (algebraMap (𝓞 L') L'))) ∧ Nonempty (SABMap tK t (spMap e)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SabModel.exists_sab_model | exact GlobalTheory.CompanionTheory.Ar.SabModel.exists_sab_model | (intros; apply GlobalTheory.CompanionTheory.Ar.SabModel.exists_sab_model <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PairSumFrameAtPointStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pair_sum_frame_at_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (a b : CMType H ⊕ CMType H) (N : ℕ) (bb : Fin N → ↥(𝔐.Vgen a ⊔ 𝔐.Vgen b)) (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) (h : genPt 𝔐.ξ ⤳ centre z), HodgeMetric.PolarisedAt 𝔐.t z → (Lat.comap (fun p => 𝔐.V a p ⊔ 𝔐.V b p) (𝔐.Vgen a ⊔ 𝔐.Vgen b).subtype).IsFrameAt bb ⟨centre z, h⟩ → ∃ Γ : Matrix (Fin N) (Fin N) ℂ, 𝔐.M.GramAt 𝔐.t.PP.L z (fun k => ((bb k : ↥(𝔐.Vgen a ⊔ 𝔐.Vgen b)) : 𝔐.Li)) Γ ∧ Γ.PosDef := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HodgeMetric.GramEx.exists_gramAt_posDef | exact GlobalTheory.CompanionTheory.Ar.HodgeMetric.GramEx.exists_gramAt_posDef | (intros; apply GlobalTheory.CompanionTheory.Ar.HodgeMetric.GramEx.exists_gramAt_posDef <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ThetaFunctionArchimedeanFrameStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_function_archimedean_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (D : PPData H L) (σ : L →+* ℂ), Nonempty (D.Frame σ) ∧ ∀ a : D.Frame σ, (∀ (n : ℕ) (s : Out.H0 D.t.PP.L n), ∃! θ, a.IsFn s θ) ∧ (∀ (n : ℕ) (s : Out.H0 D.t.PP.L n) θ, a.IsFn s θ → a.IsTheta n θ) ∧ ∀ x : D.B.carrier, (∃! c, D.IsVec a x c) ∧ ∀ c, D.IsVec a x c → D.len σ x ^ 2 = Real.pi * (a.herm c c).re ∧ (x ≠ 0 → c ≠ 0) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Sl.frames_main | exact GlobalTheory.CompanionTheory.Ar.Sl.frames_main | (intros; apply GlobalTheory.CompanionTheory.Ar.Sl.frames_main <;> assumption)
end

