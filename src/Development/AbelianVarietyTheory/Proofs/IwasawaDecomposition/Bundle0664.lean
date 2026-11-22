import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0601
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0659
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0617
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0653
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalSystemModelMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0615
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0571
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineEigenframeNearImage
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameCover
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0647
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegersAlt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PushInvertibleModelOfIso
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0619
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsValLineLogNormAtIffEmbedding
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.UnifMetricScalar
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0009
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0020
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0141
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.HasSumPolyDerivMulProdAddMatrix
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0100
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0015
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0649
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0650
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0611
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0643
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0023
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0028
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0025
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0024
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0022
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0189
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0612
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0648
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0646
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0041
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0606

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DetNeZeroOfRealIndependentIsotropicHermitian
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem det_ne_zero_of_real_indep_isotropic : ∀ (g : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ) (E : Fin g → Fin g → ℂ), (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) → LinearIndependent ℝ E → (∀ i j, (hermForm Hm (E i) (E j)).im = 0) → (Matrix.of fun k i => E i k).det ≠ 0 := by
  intro g Hm E hpos hind him
  have hL : ∀ (a : Fin g → ℝ) (w : Fin g → ℂ), hermForm Hm (∑ i, (a i : ℂ) • E i) w
      = ∑ i, (a i : ℂ) * hermForm Hm (E i) w := by
    intro a w
    simp only [hermForm, sum_dotProduct, smul_dotProduct, smul_eq_mul]
  have hR : ∀ (b : Fin g → ℝ) (z : Fin g → ℂ), hermForm Hm z (∑ j, (b j : ℂ) • E j)
      = ∑ j, (b j : ℂ) * hermForm Hm z (E j) := by
    intro b z
    have hs : star (∑ j, (b j : ℂ) • E j) = ∑ j, (b j : ℂ) • star (E j) := by
      rw [star_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ext k
      simp
    simp only [hermForm, hs, Matrix.mulVec_sum, Matrix.mulVec_smul, dotProduct_sum, dotProduct_smul, smul_eq_mul]
  have him0 : ∀ a b : Fin g → ℝ,
      (hermForm Hm (∑ i, (a i : ℂ) • E i) (∑ j, (b j : ℂ) • E j)).im = 0 := by
    intro a b
    rw [hL]
    simp only [hR, Finset.mul_sum, Complex.im_sum]
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
    simp [Complex.mul_im, him i j]
  have hsmulL : ∀ (c : ℂ) (z w : Fin g → ℂ), hermForm Hm (c • z) w = c * hermForm Hm z w := by
    intro c z w
    simp only [hermForm, smul_dotProduct, smul_eq_mul]
  have hreal : ∀ a : Fin g → ℝ, (∑ i, (a i : ℂ) • E i) = 0 → a = 0 := by
    intro a h0
    have h1 : ∑ i, a i • E i = 0 := by
      rw [← h0]
      refine Finset.sum_congr rfl fun i _ => ?_
      ext k
      simp
    have := Fintype.linearIndependent_iff.mp hind a h1
    funext i
    exact this i
  have hC : LinearIndependent ℂ E := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have hsplit : (∑ i, (((c i).re : ℝ) : ℂ) • E i) + Complex.I • (∑ i, (((c i).im : ℝ) : ℂ) • E i) = 0 := by
      rw [← hc, Finset.smul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_smul, ← add_smul]
      congr 1
      exact (mul_comm Complex.I _ ▸ Complex.re_add_im (c i))
    set X := ∑ i, (((c i).re : ℝ) : ℂ) • E i with hX
    set Y := ∑ i, (((c i).im : ℝ) : ℂ) • E i with hY
    have hXY : X = (-Complex.I) • Y := by
      rw [neg_smul]
      exact eq_neg_of_add_eq_zero_left hsplit
    have hY0 : Y = 0 := by
      by_contra hne
      have hp := hpos Y hne
      have h2 := him0 (fun i => (c i).re) (fun i => (c i).im)
      change (hermForm Hm X Y).im = 0 at h2
      rw [hXY, hsmulL] at h2
      simp [Complex.mul_im] at h2
      linarith
    have hX0 : X = 0 := by rw [hXY, hY0, smul_zero]
    have hre := hreal (fun i => (c i).re) hX0
    have him' := hreal (fun i => (c i).im) hY0
    intro i
    apply Complex.ext
    · simpa using congrFun hre i
    · simpa using congrFun him' i
  have hcol : LinearIndependent ℂ (Matrix.of fun k i => E i k : Matrix (Fin g) (Fin g) ℂ).col := hC
  have hu := Matrix.linearIndependent_cols_iff_isUnit.mp hcol
  exact ((Matrix.isUnit_iff_isUnit_det _).mp hu).ne_zero

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EtaleChartHolomorphicCoordinateChange
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ShFam.Hor.LogCh

theorem valAt'_eq_ev {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {σ : k →+* ℂ} {U : Y.Opens}
    {x : CxPts p σ} (h : x ∈ CxPts.ptsIn p σ U) (f : Γ(Y, U)) : valAt' x.1 U f = CxPts.ev p σ U f x := by
  rw [CxPts.ev_eq h, CxPts.evHom_eq_evalPt h, TangentOrigin.valAt'_eq_evalPt _ _ h]

theorem chart_change : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (p : Y ⟶ Sp k) (n : ℕ) (σ : k →+* ℂ) (c : AlgChart p σ n) (ψ : OpenPartialHomeomorph (ReciprocityTheory.L2DbarEstimates.V n) (Fin n → ℂ)), DifferentiableOn ℂ ψ ψ.source → DifferentiableOn ℂ ψ.symm ψ.target → (∀ j, HolAlong (c.e.trans ψ).source fun x => (c.e.trans ψ) x j) ∧ IsHolTo (c.e.trans ψ).target (fun z => ((c.e.trans ψ).symm z).1) := by
  intro k _ Y p n σ c ψ hψ hψs
  refine ⟨fun j V _ _ _ B x hB hx hm => ?_, fun U' f => ⟨?_, ?_⟩⟩
  · have hs : ∀ b ∈ B, x b ∈ c.e.source ∧ c.e (x b) ∈ ψ.source := fun b hb => by
      simpa [OpenPartialHomeomorph.trans_source] using hm hb
    have hco : ∀ a, DifferentiableOn ℂ (fun b => c.e (x b) a) B := fun a => by
      refine ((hx c.U (c.x a)).2.mono fun b hb => ⟨hb, c.source_subset (hs b hb).1⟩).congr fun b hb => ?_
      rw [c.apply_eq _ (hs b hb).1, valAt'_eq_ev (c.source_subset (hs b hb).1)]
    have hce : DifferentiableOn ℂ (fun b => c.e (x b)) B := differentiableOn_euclidean.2 hco
    have h2 : DifferentiableOn ℂ (fun b => ψ (c.e (x b))) B := hψ.comp hce fun b hb => (hs b hb).2
    exact differentiableOn_pi.1 h2 j
  · exact (c.e.trans ψ).continuousOn_symm.isOpen_inter_preimage (c.e.trans ψ).open_target
      (CxPts.isOpen_ptsIn U')
  · have hm : ∀ z ∈ {z ∈ (c.e.trans ψ).target | ⊤ ≤ ((c.e.trans ψ).symm z).1 ⁻¹ᵁ U'},
        z ∈ ψ.target ∧ ψ.symm z ∈ c.e.target ∧ c.e.symm (ψ.symm z) ∈ CxPts.ptsIn p σ U' := fun z hz => by
      have h1 := hz.1
      simp only [OpenPartialHomeomorph.trans_target, Set.mem_inter_iff, Set.mem_preimage] at h1
      exact ⟨h1.1, h1.2, hz.2⟩
    have h2 : DifferentiableOn ℂ (CxPts.ev p σ U' f ∘ c.e.symm ∘ ψ.symm)
        {z ∈ (c.e.trans ψ).target | ⊤ ≤ ((c.e.trans ψ).symm z).1 ⁻¹ᵁ U'} :=
      (c.holo U' f).comp (hψs.mono fun z hz => (hm z hz).1) fun z hz => ⟨(hm z hz).2.1, (hm z hz).2.2⟩
    refine h2.congr fun z hz => ?_
    exact valAt'_eq_ev (hm z hz).2.2 f

end GlobalTheory.ShFam.Hor.LogCh
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineDomainFrameHasDR
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.HTLine
open Formalism.MainNotions.DIV.Cons (intO SCF)

namespace GlobalTheory.HTLine

attribute [local instance] Over.cartesianMonoidalCategory

theorem exists_affine_domain {X : Scheme.{0}} [GlobalTheory.IsNormalScheme X] [IsLocallyNoetherian X] (V : X.Opens) {z : X}
    (hz : z ∈ V) : ∃ (U : X.Opens) (hU : IsAffineOpen U) (_ : IsDomain Γ(X, U)),
      z ∈ U ∧ U ≤ V ∧ IsIntegrallyClosed Γ(X, U) := by
  have hC : IsOpen (irreducibleComponent z) :=
    GlobalTheory.IsNormalScheme.isOpen_of_mem_irreducibleComponents (irreducibleComponent_mem_irreducibleComponents z)
  obtain ⟨U, hU, hzU, hle⟩ := exists_isAffineOpen_mem_and_subset (X := X) (x := z)
    (U := V ⊓ ⟨irreducibleComponent z, hC⟩) ⟨hz, mem_irreducibleComponent⟩
  have hpre : IsPreirreducible (U : Set X) := (isIrreducible_irreducibleComponent (x := z)).2.open_subset U.2
    fun q hq => (hle hq).2
  have hirr : IsIrreducible (U : Set X) := ⟨⟨z, hzU⟩, hpre⟩
  have : IrreducibleSpace U.toScheme := Subtype.irreducibleSpace hirr
  have : Nonempty U := ⟨⟨z, hzU⟩⟩
  have : IsIntegral U.toScheme := GlobalTheory.IsNormalScheme.isIntegral_of_irreducibleSpace _
  have : Nonempty (Spec Γ(X, U)) := ⟨hU.isoSpec.hom ⟨z, hzU⟩⟩
  have : IsIntegral (Spec Γ(X, U)) := isIntegral_of_isOpenImmersion hU.isoSpec.inv
  have hd : IsDomain Γ(X, U) := (affine_isIntegral_iff _).1 this
  exact ⟨U, hU, hd, hzU, fun q hq => (hle hq).1,
    (GlobalTheory.IsNormalScheme.spec_iff_of_isDomain _).1 (GlobalTheory.IsNormalScheme.spec_of_isAffineOpen hU)⟩

theorem gen_mem {X : Scheme.{0}} {U V : X.Opens} (hU : IsAffineOpen U) [IsDomain Γ(X, U)] {q : X} (hq : q ∈ U)
    (hV : q ∈ V) : ⊤ ≤ (spMap (algebraMap Γ(X, U) (FractionRing Γ(X, U))) ≫ hU.fromSpec) ⁻¹ᵁ V := by
  intro q' _
  have hg : (spMap (algebraMap Γ(X, U) (FractionRing Γ(X, U))) q') ⤳ hU.primeIdealOf ⟨q, hq⟩ := by
    refine (PrimeSpectrum.le_iff_specializes _ _).1 ?_
    have e : (PrimeSpectrum.comap (algebraMap Γ(X, U) (FractionRing Γ(X, U))) q').asIdeal = ⊥ := by
      let q₀ : PrimeSpectrum (FractionRing Γ(X, U)) := q'
      have := q₀.isPrime
      change Ideal.comap _ q₀.asIdeal = ⊥
      rw [Ideal.eq_bot_of_prime q₀.asIdeal]
      exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective _ _)
    change (PrimeSpectrum.comap (algebraMap Γ(X, U) (FractionRing Γ(X, U))) q').asIdeal ≤ _
    rw [e]
    exact bot_le
  have h2 := hg.map hU.fromSpec.continuous
  rw [hU.fromSpec_primeIdealOf ⟨q, hq⟩] at h2
  exact h2.mem_open V.2 hV

theorem tan_restrict {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
    (t : SAB H X) {R S : Type} [CommRing R] [CommRing S] (ρ : R →+* S) {x : Sp R ⟶ X} {x' : Sp S ⟶ X}
    (hx : spMap ρ ≫ x = x') {n : ℕ} {v : Fin n → (Sp (DualNumber R) ⟶ t.G.left)} (h2 : ∀ i, IsTanAtG t x (v i))
    (h3 : ∀ u, IsTanAtG t x u → ∃! cf, IsCombAtG t x v cf u) :
    (∀ i, IsTanAtG t x' (spMap (dualMap ρ) ≫ v i)) ∧
      ∀ u, IsTanAtG t x' u → ∃! cf, IsCombAtG t x' (fun i => spMap (dualMap ρ) ≫ v i) cf u := by
  subst hx
  have B := GlobalTheory.T.isTanBasis_of_unique_combination E H X t R x n v h2 h3
  exact ⟨fun i => GlobalTheory.LieMet.isTan_map ρ rfl (h2 i), fun u hu => B.2 _ ρ u hu⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

theorem isLocallyNoetherian_model (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits) (Z : Mdl Y i₀) : IsLocallyNoetherian Z.X := by
  have := GlobalTheory.ProjBlowup.isDiscreteValuationRing_coeff Z.i.c hp.ne_zero hW
  have := isProper_str (Z.i.c.V W) Z.n
  have : LocallyOfFiniteType Z.s := by
    unfold Pre.s
    infer_instance
  exact LocallyOfFiniteType.isLocallyNoetherian Z.s

set_option maxHeartbeats 1600000 in

theorem intFrame_restrict (Z : Mdl Y i₀) {U₀ U : Z.X.Opens} (hU₀ : IsAffineOpen U₀) (hU : IsAffineOpen U)
    (ρ : Γ(Z.X, U₀) →+* Γ(Z.X, U)) (eρ : spMap ρ ≫ hU₀.fromSpec = hU.fromSpec) {w₀ : Vecs Dw (Y Z.i).t Γ(Z.X, U₀)}
    (hfr : IntFrame Z hU₀ w₀) : IntFrame Z hU (w₀.bc ρ) := by
  have ex : spMap ρ ≫ hU₀.fromSpec ≫ Z.π = hU.fromSpec ≫ Z.π := by rw [← Category.assoc, eρ]
  refine ⟨fun σ => ?_, fun k _ φ hr => ?_⟩
  · obtain ⟨n, v, e, h1, h2, h3⟩ := hfr.1 σ
    obtain ⟨b1, b2⟩ := tan_restrict (Y Z.i).t ρ ex h2 h3
    exact ⟨n, _, e, fun i => congrArg (spMap (dualMap ρ) ≫ ·) (h1 i), b1, b2⟩
  · have e1 : spMap (φ.comp ρ) ≫ hU₀.fromSpec = spMap φ ≫ hU.fromSpec := by
      rw [← eρ, ← Category.assoc, ModelRelProbe.spMap_comp]
    rw [Vecs.bc_bc, ← e1]
    exact hfr.2 k _ (by rwa [e1])

theorem exists_tanBasis (Z : Mdl Y i₀) {U₀ U : Z.X.Opens} (hU₀ : IsAffineOpen U₀) (hU : IsAffineOpen U)
    (ρ : Γ(Z.X, U₀) →+* Γ(Z.X, U)) (eρ : spMap ρ ≫ hU₀.fromSpec = hU.fromSpec) {w₀ : Vecs Dw (Y Z.i).t Γ(Z.X, U₀)}
    (hfr : IntFrame Z hU₀ w₀) : ∃ (g : ℕ) (e : Fin g → (Sp (DualNumber Γ(Z.X, U)) ⟶ (Y Z.i).t.G.left)),
      GlobalTheory.LineNorm.IsTanBasis (Y Z.i).t (R := Γ(Z.X, U)) (hU.fromSpec ≫ Z.π) e := by
  have ex : spMap ρ ≫ hU₀.fromSpec ≫ Z.π = hU.fromSpec ≫ Z.π := by rw [← Category.assoc, eρ]
  obtain ⟨σ⟩ : Nonempty (E →+* ℂ) := inferInstance
  obtain ⟨n, v, -, -, h2, h3⟩ := hfr.1 σ
  obtain ⟨b1, b2⟩ := tan_restrict (Y Z.i).t ρ ex h2 h3
  exact ⟨n, _, GlobalTheory.T.isTanBasis_of_unique_combination E H _ _ _ _ n _ b1 b2⟩

theorem exists_coeff_gen (Z : Mdl Y i₀) {U : Z.X.Opens} (hU : IsAffineOpen U) [IsDomain Γ(Z.X, U)] {z : Z.X} (hzU : z ∈ U) :
    ∃ (β : ↥(Z.i.c.V W) →+* Γ(Z.X, U)) (y : Sp (FractionRing Γ(Z.X, U)) ⟶ (Xo Z.i.l).XF Z.i.c), Function.Injective β ∧
      spMap (algebraMap Γ(Z.X, U) (FractionRing Γ(Z.X, U))) ≫ hU.fromSpec ≫ Z.π = y ≫ (Y Z.i).j := by
  obtain ⟨β, eβ⟩ : ∃ β : ↥(Z.i.c.V W) →+* Γ(Z.X, U), spMap β = hU.fromSpec ≫ Z.s :=
    ⟨(Spec.preimage (hU.fromSpec ≫ Z.s)).hom, Spec.map_preimage _⟩
  obtain ⟨q, hqU, hqo⟩ := Z.dense.inter_open_nonempty U U.2 ⟨z, hzU⟩
  have hqo' : q ∈ ⋃ a, ((Z.U a).1 : Set Z.X) := by rw [Z.cover]; exact hqo
  obtain ⟨a, hqa⟩ := Set.mem_iUnion.1 hqo'
  obtain ⟨φ, hφ⟩ := Pull.exists_fromSpec (Z.U a).2 _ (gen_mem hU hqU hqa)
  have hφ' : spMap φ ≫ Z.chart a = spMap (algebraMap Γ(Z.X, U) (FractionRing Γ(Z.X, U))) ≫ hU.fromSpec := hφ
  obtain ⟨y, hy⟩ := Pull.exists_open_lift Z hφ'
  refine ⟨β, y, ?_, by rw [hy, Category.assoc]⟩
  have cs := Pull.affineOpenChart_comp_structure_eq_spMap Z hφ'
  rw [Z.π_s, Category.assoc, ← eβ, ModelRelProbe.spMap_comp, ModelRelProbe.spMap_comp] at cs
  have e : (algebraMap Γ(Z.X, U) (FractionRing Γ(Z.X, U))).comp β = (φ.comp (Z.alg a)).comp (Z.i.c.V W).subtype :=
    congrArg CommRingCat.Hom.hom (Spec.map_injective (a₁ := CommRingCat.ofHom _) (a₂ := CommRingCat.ofHom _) cs)
  refine Function.Injective.of_comp (f := algebraMap Γ(Z.X, U) (FractionRing Γ(Z.X, U))) ?_
  have e' : (⇑(algebraMap Γ(Z.X, U) (FractionRing Γ(Z.X, U))) ∘ ⇑β) = ⇑((φ.comp (Z.alg a)).comp (Z.i.c.V W).subtype) :=
    congrArg DFunLike.coe e
  rw [e']
  exact (φ.comp (Z.alg a)).injective.comp (Z.i.c.V W).subtype_injective

theorem exists_small_chart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p), p.Prime → (p : ℂ) ∈ W.nonunits → ∀ (Z : Mdl Y i₀), HasDR Z → ∀ z : Z.X, ∃ (U : Z.X.Opens) (hU : IsAffineOpen U) (_ : IsDomain Γ(Z.X, U)) (w : Vecs Dw (Y Z.i).t Γ(Z.X, U)) (g : ℕ) (e : Fin g → (Sp (DualNumber Γ(Z.X, U)) ⟶ (Y Z.i).t.G.left)) (β : ↥(Z.i.c.V W) →+* Γ(Z.X, U)) (y : Sp (FractionRing Γ(Z.X, U)) ⟶ (Xo Z.i.l).XF Z.i.c), z ∈ U ∧ IsIntegrallyClosed Γ(Z.X, U) ∧ Function.Injective β ∧ IntFrame Z hU w ∧ GlobalTheory.LineNorm.IsTanBasis (Y Z.i).t (R := Γ(Z.X, U)) (hU.fromSpec ≫ Z.π) e ∧ spMap (algebraMap Γ(Z.X, U) (FractionRing Γ(Z.X, U))) ≫ hU.fromSpec ≫ Z.π = y ≫ (Y Z.i).j := by
  intro E _ _ _ H Dw Xo p W Y i₀ hp hW Z hDR z
  have hN : GlobalTheory.IsNormalScheme Z.X := Z.normal
  have := isLocallyNoetherian_model hp hW Z
  obtain ⟨U₀, hU₀, w₀, hz, hfr⟩ := hDR.2 z
  obtain ⟨U, hU, hd, hzU, hle, hic⟩ := exists_affine_domain U₀ hz
  obtain ⟨ρ, eρ⟩ : ∃ ρ : Γ(Z.X, U₀) →+* Γ(Z.X, U), spMap ρ ≫ hU₀.fromSpec = hU.fromSpec :=
    ⟨(Z.X.presheaf.map (homOfLE hle).op).hom, hU₀.map_fromSpec hU _⟩
  obtain ⟨g, e, he⟩ := exists_tanBasis Z hU₀ hU ρ eρ hfr
  obtain ⟨β, y, hβ, hy⟩ := exists_coeff_gen Z hU hzU
  exact ⟨U, hU, hd, w₀.bc ρ, g, e, β, y, hzU, hic, hβ, intFrame_restrict Z hU₀ hU ρ eρ hfr, he, hy⟩

end GlobalTheory.HTLine
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineEigenframeNearImageStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_affine_eigenframe_near_image : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (p : ℕ) (W : ValuationSubring ℂ) (Y : Model Xo c (c.V W).subtype), p.Prime → (p : ℂ) ∈ W.nonunits → IsOpen (Set.range Y.j) ∧ ∀ (x : Y.X) (U : Y.X.Opens), x ∈ U → x ∈ Set.range Y.j → ∃ (V : Y.X.affineOpens) (α : c.F →+* Γ(Y.X, V.1)) (e : Vecs Dw Y.t Γ(Y.X, V.1)) (n : ℕ) (en : Fin n ≃ Let Dw.mult), x ∈ V.1 ∧ V.1 ≤ U ∧ (V.1 : Set Y.X) ⊆ Set.range Y.j ∧ V.2.fromSpec ≫ Y.s = spMap (α.comp (c.V W).subtype) ∧ (∀ (R : Type) [CommRing R] (φ : Γ(Y.X, V.1) →+* R), IsFrame Y.t (φ.comp α) (spMap φ ≫ V.2.fromSpec) (e.bc φ)) ∧ ∀ w, IsTanAtG Y.t V.2.fromSpec w → ∃! a : Fin n → Γ(Y.X, V.1), IsCombAtG Y.t V.2.fromSpec (fun i => e (en i).1 (en i).2) a w := by
  first | exact @GlobalTheory.FlagEmb.EigSpread.exists_stable_eigFrame | exact GlobalTheory.FlagEmb.EigSpread.exists_stable_eigFrame | (intros; apply GlobalTheory.FlagEmb.EigSpread.exists_stable_eigFrame <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineEquationHolomorphicLimitStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_affine_equation_holomorphic_limit : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (Y : GlobalTheory.ProjVar.Var F) (Δ bd : Y.Dv) (g : Y.Fn), Y.Eff bd → (∀ y : Y.X, y ∉ Y.supp bd → Δ.RegularAt y g) → (∀ y ∈ Y.supp bd, ∀ V : Y.X.Opens, y ∈ V → ∃ (U : Y.X.Opens) (hU : IsAffineOpen U) (hy : y ∈ U) (t : Y.Fnˣ), U ≤ V ∧ (∀ y' ∈ U, Δ.IsEqn y' t) ∧ ∀ (a b : Γ(Y.X, U)) (ψ : ℂ → (Γ(Y.X, U) →+* ℂ)) (r : ℝ), IsHolPts ψ r → (∀ u ∈ Metric.ball (0 : ℂ) r, spMap (ψ u) ≫ (show Sp Γ(Y.X, U) ⟶ Y.X from hU.fromSpec) ≫ Y.str = spMap σ) → (∀ s, (spMap (ψ 0) ≫ (show Sp Γ(Y.X, U) ⟶ Y.X from hU.fromSpec)) s ∈ Y.supp bd) → (∀ u ∈ Metric.ball (0 : ℂ) r, u ≠ 0 → ∀ s, (spMap (ψ u) ≫ (show Sp Γ(Y.X, U) ⟶ Y.X from hU.fromSpec)) s ∉ Y.supp bd) → fnOf U (gen_mem hy) a = g * t * fnOf U (gen_mem hy) b → (∀ u ∈ Metric.ball (0 : ℂ) r, u ≠ 0 → ψ u b ≠ 0) → Tendsto (fun u => ψ u a / ψ u b) (𝓝[≠] 0) (𝓝 0)) → g ∈ Y.H0 Δ ∧ Y.vanishOn Δ g (Y.supp bd) := by
  first | exact @GlobalTheory.ShFam.BdArc.mem_H0_and_vanishOn_of_tendsto | exact GlobalTheory.ShFam.BdArc.mem_H0_and_vanishOn_of_tendsto | (intros; apply GlobalTheory.ShFam.BdArc.mem_H0_and_vanishOn_of_tendsto <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsArcFibreUniformisationThetaMultiple
section
open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries

noncomputable section

namespace GlobalTheory.ArcNormal

open GlobalTheory GlobalTheory.OrthoMetric GlobalTheory.ArchMetricCompare

theorem exists_thetaChar_mulVec_ne {g : ℕ} (τ h : Matrix (Fin g) (Fin g) ℂ) (c₁ c₂ : Fin g → ℂ) (hs : τ.IsSymm)
    (hp : (τ.map Complex.im).PosDef) (h₁ : ∀ k, c₁ k = 0 ∨ c₁ k = 1 / 2) (h₂ : ∀ k, c₂ k = 0 ∨ c₂ k = 1 / 2)
    (hh : IsUnit h.det) : ∃ z, thetaChar τ c₁ c₂ (h.mulVec z) ≠ 0 := by
  have re : ∀ c : Fin g → ℂ, (∀ k, c k = 0 ∨ c k = 1 / 2) → (fun i => (((c i).re : ℝ) : ℂ)) = c := by
    intro c hc
    funext i
    rcases hc i with e | e <;> rw [e] <;> norm_num
  have hne := GlobalTheory.CanTh.thetaChar_ne_zero hs hp (fun i => (c₁ i).re) (fun i => (c₂ i).re)
  rw [re c₁ h₁, re c₂ h₂] at hne
  obtain ⟨z₀, hz₀⟩ := Function.ne_iff.1 hne
  refine ⟨h⁻¹.mulVec z₀, ?_⟩
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hh, Matrix.one_mulVec]
  exact hz₀

theorem exists_unif_of_arc : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (V : ValuationSubring c.F) (Y : Model Xo c V.subtype) (a : ArcIn Dw l V.subtype ℂ (σ.comp V.subtype)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : GlobalTheory.ArcQ.Wit Y a χ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (Ha : HolArc Y σ a χ W Fu) (th : a.D₀.P.L.Sec) (Θ : GlobalTheory.ArcQ.ThetaDat Ha th) (M : GChart Y), Formalism.L2.PjFree.GoodEmb c σ → IsTypeFn H Dw.p Dw.q ty → PushInvertible Y.t.G Y.t.PP.L → χ ≫ Y.s = spMap (PowerSeries.C (R := ℂ)) ≫ spMap (σ.comp V.subtype) → (∀ x : Sp (PowerSeries ℂ), PowerSeries.X ∉ x.asIdeal → χ x ∈ Set.range Y.j) → ⊤ ≤ χ ⁻¹ᵁ M.U → ∃ T : ℝ, ∀ w : ℂ, T < w.im → ∀ yF : Sp ℂ ⟶ Xo.XF c, yF ≫ pullback.fst _ _ = Fu.u Ha.i (Ha.Pw w) → yF ≫ pullback.snd _ _ = spMap σ → ∀ (hz : ⊤ ≤ (yF ≫ Y.j) ⁻¹ᵁ M.U) (x : KeyIn ℂ) (φ : x.P.A.left ⟶ Y.t.G.left), GlobalTheory.ArcNormal.KeyAtVia M (yF ≫ Y.j) hz x φ → ∃ (_ : x.P.g = g) (u : HolUnif x.P.A x.P.L g) (c₀ : ℂ), u.IsRig x.rig ∧ GlobalTheory.ArcNormal.ArcFib Y σ Fu Ha.i (Ha.Pw w) x φ u ∧ u.Λ = (Ha.Pw w).range.toIntSubmodule ∧ u.IsFn x.th (fun z => c₀ * thetaChar (Θ.τ w) Θ.c₁ Θ.c₂ (Θ.h.mulVec z)) := by
  intro E _ _ _ H Dw l Xo c σ _ _ V Y a χ W g ty Fu Ha th Θ M hσ hty hP hover hgen hM
  have hh : IsUnit Θ.h.det := by
    refine Matrix.isUnit_det_of_right_inverse (B := Matrix.of fun i k => Ha.Pw 0 (Θ.bas (Pi.single (.inl k) 1)) i) ?_
    ext i k
    have e := congrFun (Θ.per 0 k).1 i
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.one_apply, Pi.single_apply, eq_comm] using e
  refine ⟨Ha.T, fun w hw yF hy₁ hy₂ hz x φ hx => ?_⟩
  have hPer := Ha.period w hw
  obtain ⟨fr, hf₁, hf₂, hf₃, -, s, hs⟩ := Θ.frame w hw
  obtain ⟨-, wx, -, hgp, hwx, -, -, -⟩ := hx
  obtain ⟨φ', hφ₁, hφ₂, hgp', hiso⟩ := GlobalTheory.T.genericFibre_group_factors_universal_cartesian E H Dw l Xo c _ _ Y yF x φ hgp ⟨wx, hwx⟩
  rw [hy₁] at hgp'
  have hL := Xo.univ.t.PP.isLB
  have hM' := pull_isLB hL (φ' ≫ Y.m0.toSABMap.φ)
  let u₁ := fibreUnif hgp' (Fu.ex Ha.i (Ha.Pw w)) (Ha.Pw w).range fr (Fu.ex_add _ _ hPer) (Fu.ex_onto _ _ hPer)
    (Fu.ex_ker _ _ hPer) hPer.2.2.1 hPer.2.2.2.1 (isHolTo_exp Fu Ha.i hPer) hf₁ hf₂ hf₃
  obtain ⟨wI, hwI⟩ := LBIso.symm hiso
  let u₂ := carry u₁ hM' x.P.isLB hwI
  have hex₁ : ∀ z, (u₂.ex z).left ≫ φ' ≫ Y.m0.toSABMap.φ = (Fu.ex Ha.i (Ha.Pw w) z).left := fun z =>
    liftPt_comp hgp' _
  obtain hθ : ∃ z, thetaChar (Θ.τ w) Θ.c₁ Θ.c₂ (Θ.h.mulVec z) ≠ 0 :=
    exists_thetaChar_mulVec_ne _ _ _ _ (Θ.pos w hw).1 (Θ.pos w hw).2 Θ.half₁ Θ.half₂ hh

  obtain ⟨c₁, hc₁⟩ := GlobalTheory.T.keySection_eq_const_mul_thetaFunction_fibre x _ Xo.univ.t.G Xo.univ.t.PP.L (Fu.u Ha.i (Ha.Pw w)) (φ' ≫ Y.m0.toSABMap.φ) g u₂ wI
    (fun z => thetaChar (Θ.τ w) Θ.c₁ Θ.c₂ (Θ.h.mulVec z)) fr s hL hgp'.1 hwI hθ
    (fun j z hj => hf₂ j z (by rwa [hex₁] at hj))
    (fun k j z hkj => by
      obtain ⟨hk, hj⟩ := (top_le_preimage_inf _ _ _).1 hkj
      exact carry_fr u₁ hM' x.P.isLB hwI k j z hk hj)
    (fun j z p hp₁ hp₂ hj => hs j z p (hp₁.trans (hex₁ z)) hp₂ (by rwa [hex₁] at hj))
  obtain ⟨u₃, lam, hlam, hex, hΛ, hR, hfr⟩ := GlobalTheory.T.exists_rescale_uniformisation_rigidification x.P.A x.P.L g u₂ x.rig x.P.isLB x.rig_gen
  have hFn : u₃.IsFn x.th fun z => c₁ / lam * thetaChar (Θ.τ w) Θ.c₁ Θ.c₂ (Θ.h.mulVec z) := by
    intro i z hi
    rw [hex] at hi ⊢
    rw [hc₁ i z hi, hfr]
    field_simp
  have hdim : g = x.P.g := by
    obtain ⟨u₀, -, -, -, -, -, hv, hw', -⟩ := thetaUnifAV_all x.P x.rig x.rig_gen
    obtain ⟨F, hF, -⟩ := existsUnique_linear_lift_of_isHolTo x.P.A x.P.isAb x.P.L x.P.g g u₀ hv hw' u₃.ex u₃.ex_add
      (fun U f => by simpa only [Set.mem_univ, true_and] using u₃.hol U f)
    exact AHWeil.dim_eq u₃ u₀ F hF
  refine ⟨hdim.symm, u₃, c₁ / lam, hR, fun z => ⟨(u₃.ex z).left ≫ φ', ?_, ?_, ?_⟩, hΛ, hFn⟩
  · rw [Category.assoc, hex]
    exact hex₁ z
  · rw [Category.assoc, ← Category.assoc φ', hφ₂, Category.assoc, ← Category.assoc (u₃.ex z).left, Over.w (u₃.ex z),
      hy₂]
    exact Category.id_comp _
  · rw [Category.assoc, hφ₁]

end GlobalTheory.ArcNormal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConstIntegralCoordsLatticeSectionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_const_integral_coords_lattice_section : ∀ (n g r : ℕ) (B : Set (Fin n → ℂ)) (K : (Fin n → ℂ) → Set (Fin g → ℂ)) (lam : (Fin n → ℂ) → Fin r → Fin g → ℂ) (ζ : (Fin n → ℂ) → Fin g → ℂ) (b₀ : Fin n → ℂ), IsPreconnected B → ContinuousOn lam B → ContinuousOn ζ B → (∀ b ∈ B, IsLatBasis (K b) (lam b)) → (∀ b ∈ B, ζ b ∈ K b) → b₀ ∈ B → ∃ m : Fin r → ℤ, ∀ b ∈ B, ζ b = ∑ j, m j • lam b j := by
  first | exact @GlobalTheory.ShFam.Hor.LogCh.exists_const_coords | exact GlobalTheory.ShFam.Hor.LogCh.exists_const_coords | (intros; apply GlobalTheory.ShFam.Hor.LogCh.exists_const_coords <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsDvrExtensionClosedPoint
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

noncomputable section

namespace GlobalTheory.TraitLift

theorem eq_of_stalkClosedPointTo' {X : Scheme.{0}} {R W V : Type} [CommRing R] [IsLocalRing R] [CommRing W]
    [IsLocalRing W] [CommRing V] [IsLocalRing V] (ξ : Sp R ⟶ X) (χ : Sp W ⟶ X) (h : ξ (closedPoint R) = χ (closedPoint W))
    (ψ : R →+* V) (f : W →+* V)
    (hc : ψ.comp (Scheme.stalkClosedPointTo ξ).hom =
      f.comp ((X.presheaf.stalkCongr (Inseparable.of_eq h)).hom ≫ Scheme.stalkClosedPointTo χ).hom) :
    spMap f ≫ χ = spMap ψ ≫ ξ := by
  have key : ∀ (x y : X) (hxy : x = y) (g : X.presheaf.stalk y ⟶ CommRingCat.of V),
      Spec.map ((X.presheaf.stalkCongr (Inseparable.of_eq hxy)).hom ≫ g) ≫ X.fromSpecStalk x =
        Spec.map g ≫ X.fromSpecStalk y := by
    intro x y hxy g
    subst hxy
    simp
  have hc' : Scheme.stalkClosedPointTo ξ ≫ CommRingCat.ofHom ψ =
      (X.presheaf.stalkCongr (Inseparable.of_eq h)).hom ≫ Scheme.stalkClosedPointTo χ ≫ CommRingCat.ofHom f := by
    ext a
    exact congrArg (fun g : _ →+* V => g a) hc
  conv_lhs => rw [← Scheme.Spec_stalkClosedPointTo_fromSpecStalk χ]
  conv_rhs => rw [← Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ]
  simp only [spMap, ← Category.assoc, ← Spec.map_comp]
  rw [hc', key _ _ h]

theorem exists_lift : ∀ (X : Scheme.{0}) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (ξ : Sp R ⟶ X), IsCN R → IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom → ((residue R).comp (Scheme.stalkClosedPointTo ξ).hom).FormallyUnramified → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], CDvr W → ∀ ϖ : W, Irreducible ϖ → ∀ (χ : Sp W ⟶ X), χ (closedPoint W) = ξ (closedPoint R) → ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsLocalRing V) (f : W →+* V) (ψ : R →+* V), CDvr V ∧ Function.Injective f ∧ IsLocalHom f ∧ IsLocalHom ψ ∧ Irreducible (f ϖ) ∧ spMap f ≫ χ = spMap ψ ≫ ξ := by
  intro X R _ _ _ ξ hR hξ hur W _ _ _ hW ϖ hϖ χ hχ
  obtain ⟨-, -, hRc, -⟩ := hR
  haveI := hRc
  have hpt : ξ (closedPoint R) = χ (closedPoint W) := hχ.symm
  let φ : X.presheaf.stalk (ξ (closedPoint R)) →+* R := (Scheme.stalkClosedPointTo ξ).hom
  let α : X.presheaf.stalk (ξ (closedPoint R)) →+* W :=
    ((X.presheaf.stalkCongr (Inseparable.of_eq hpt)).hom ≫ Scheme.stalkClosedPointTo χ).hom
  haveI : IsLocalHom α := by
    simp only [α, CommRingCat.hom_comp]
    infer_instance
  haveI : IsLocalHom φ := Scheme.isLocalHom_stalkClosedPointTo' ξ
  obtain ⟨hflat, hmax, hfin⟩ := hξ
  have hfin' : (ResidueField.map φ).Finite := by
    rw [← ResidueField.map_comp_residue] at hfin
    exact RingHom.Finite.of_comp_finite hfin
  have hur' : (ResidueField.map φ).FormallyUnramified := by
    rw [← ResidueField.map_comp_residue] at hur
    exact RingHom.FormallyUnramified.of_comp hur
  obtain ⟨θ, q, hqm, hqθ, hqd, hgen, hind⟩ := GlobalTheory.T.exists_primitive_element_unramified φ hfin hur
  obtain ⟨M, _, u, v, huv, hvf, hvu⟩ := GlobalTheory.T.exists_common_unramified_extension (ResidueField.map φ) (ResidueField.map α) hfin' hur'
  obtain ⟨V, _, _, _, f, τ, hV, hfinj, hfloc, hirr, hτ⟩ := GlobalTheory.T.exists_dvr_residue_lift_irreducible W hW v hvf hvu
  haveI := hV.2.1
  let σ : ResidueField R →+* ResidueField V := τ.comp u
  have hσ : ∀ a, σ (residue R (φ a)) = residue V ((f.comp α) a) := by
    intro a
    have h1 := congrArg (fun g => g (residue _ a)) huv
    simp only [RingHom.comp_apply, ResidueField.map_residue] at h1
    simp only [σ, RingHom.comp_apply, h1, hτ]
  obtain ⟨η, hη, -⟩ := GlobalTheory.T.exists_hensel_root_residue φ (f.comp α) σ hσ θ q hqm hqθ hqd
  have hgp := GlobalTheory.T.polynomial_approx_pow_maximal φ hmax θ hgen
  have hip := GlobalTheory.T.polynomial_approx_uniqueness φ hflat hmax θ q hqm hqθ hgp hind
  obtain ⟨ψ, hψ, hψl⟩ := GlobalTheory.T.hensel_roots_compatible φ (f.comp α) inferInstance θ η q hqm hqθ hη hgp hip
  exact ⟨V, inferInstance, inferInstance, inferInstance, f, ψ, hV, hfinj, hfloc, hψl, hirr ϖ hϖ,
    eq_of_stalkClosedPointTo' ξ χ hpt ψ f hψ⟩

end GlobalTheory.TraitLift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsExponentialChartRescaleFrameChangeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_exponentialChart_rescale_frameChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (n g : ℕ) (e0 : OpenPartialHomeomorph (CxPts (genStr Z) σ) (Fin n → ℂ)) (ex : ExpMaps Z σ g) (ρ : ℝ) (A : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ), 0 < ρ → Metric.ball 0 ρ ⊆ e0.target → (∀ j, HolAlong e0.source fun x => e0 x j) → IsHolTo e0.target (fun z => (e0.symm z).1) → IsHolTo (Metric.ball 0 ρ ×ˢ Set.univ) (fun zw : (Fin n → ℂ) × (Fin g → ℂ) => (ex (e0.symm zw.1) zw.2).left) → (∀ x ∈ e0.source, ‖e0 x‖ < ρ → IsExpAt Z.t (x.1 ≫ genι Z) (ex x)) → DifferentiableOn ℂ A (Metric.ball 0 ρ) → (∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ, IsUnit (A z).det) → ∃ (e : OpenPartialHomeomorph (CxPts (genStr Z) σ) (Fin n → ℂ)) (ex' : ExpMaps Z σ g), IsExpChart e ex' ∧ e.source = e0.source ∩ {x | ‖e0 x‖ < ρ} ∧ (∀ x ∈ e.source, e x = ρ⁻¹ • e0 x) ∧ ∀ x ∈ e.source, ∀ w, ex' x w = ex x (A (e0 x) *ᵥ w) := by
  first | exact @GlobalTheory.ShFam.Hor.LogCh.exists_isExpChart_rescale | exact GlobalTheory.ShFam.Hor.LogCh.exists_isExpChart_rescale | (intros; apply GlobalTheory.ShFam.Hor.LogCh.exists_isExpChart_rescale <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteExtensionSplittingTorsionStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.LineNorm MonObj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_extension_splitting_torsion : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) [IsLocallyNoetherian X] (t : SAB H X) (A : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] [CharZero A] (x : Sp A ⟶ X) (q : ℕ), q ≠ 0 → ∃ (A' : Type) (_ : CommRing A') (_ : IsDomain A') (_ : Algebra A A'), Module.Finite A A' ∧ Function.Injective (algebraMap A A') ∧ IsIntegrallyClosed A' ∧ (∃ ζ : A', IsPrimitiveRoot ζ q) ∧ SplitTors t (spMap (algebraMap A A') ≫ x) q := by
  first | exact @GlobalTheory.TorsSplitField.splitTors_finite_extension | exact GlobalTheory.TorsSplitField.splitTors_finite_extension | (intros; apply GlobalTheory.TorsSplitField.splitTors_finite_extension <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFramedComplexPointOfEigenFrameOffBoundaryStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.GradedNorm GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open GlobalTheory.ArcQ
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_framedComplexPoint_of_eigenFrame_off_boundary : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (y : CxPts (genStr Z) σ), ¬ LiesIn y (genBd Z) → ∀ f : EigFrame Z σ (y.1 ≫ genι Z), ∃ q : FrPt Xo c (CAt σ), cxPt Z q = y ∧ ∀ τ k, ∃ w : Sp (DualNumber ℂ) ⟶ Z.oF.t.G.left, w ≫ Z.m0.toSABMap.φ = q.u τ k ∧ w ≫ Z.m.φ = f.v τ k := by
  first | exact @GlobalTheory.ShFam.exists_frPt_cxPt_of_eigFrame | exact GlobalTheory.ShFam.exists_frPt_cxPt_of_eigFrame | (intros; apply GlobalTheory.ShFam.exists_frPt_cxPt_of_eigFrame <;> assumption)
end

