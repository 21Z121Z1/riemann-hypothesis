import Mathlib
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MemRangeOfForallHeightEqOneOfIsReflexive
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0573
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0096
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.CstDvdOfCstMulEqZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0568
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FinrankFixedSubmoduleComplexification
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0572
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsComplexArcDatumCmFibre
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArithmeticCMKnownTheoremsProof
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0047
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0570
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyTorusExtensionOfIsAlgClosed
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AllTorsMap
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.GeneratorValues

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DivisibilityOnClosedFibreSpreads
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.LN GlobalTheory.TorRef GlobalTheory.IntegralCombination
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Spread

theorem gs_fromSpecStalk (X : Scheme.{0}) (x : X) (U : X.Opens) (hx : x ∈ U) (c : Γ(X, U))
    (q : PrimeSpectrum (X.presheaf.stalk x)) :
    gs (X.fromSpecStalk x) q U c =
      @algebraMap (X.presheaf.stalk x) ((Spec.structureSheaf (X.presheaf.stalk x)).presheaf.stalk q) _ _
        (StructureSheaf.stalkAlgebra _ q) (gs (𝟙 X) x U c) := by
  have hq : X.fromSpecStalk x q ∈ U := by
    have : X.fromSpecStalk x q ⤳ x := (Scheme.range_fromSpecStalk (x := x)).le ⟨q, rfl⟩
    exact this.mem_open U.2 hx
  rw [gs_eq _ _ _ hq, gs_eq _ _ _ hx]
  rw [Scheme.fromSpecStalk_app hx]
  simp only [CommRingCat.comp_apply, Scheme.ΓSpecIso_inv]
  erw [TopCat.Presheaf.germ_res_apply]
  rfl

variable {V : Type} [CommRing V]

theorem stalkMap_cst {Y Z : Scheme.{0}} (g : Z ⟶ Y) (p : Y ⟶ Sp V) (z : Z) (v : V) :
    (g.stalkMap z).hom (cst p (g z) v) = cst (g ≫ p) z v := by
  have h : g z ∈ p ⁻¹ᵁ (⊤ : (Sp V).Opens) := trivial
  rw [cst, cst, ← gs_pull g p z ⊤ trivial, gs_stalkMap g z (p ⁻¹ᵁ ⊤) h, gs_pull (𝟙 Y) p (g z) ⊤ trivial,
    Category.id_comp]

theorem isUnit_cst_iff {Z : Scheme.{0}} (p : Z ⟶ Sp V) (z : Z) (v : V) :
    IsUnit (cst p z v) ↔ v ∉ (p z).asIdeal := by
  rw [cst, gs_stalkMap p z ⊤ trivial, isUnit_map_iff]
  let P : PrimeSpectrum V := p z
  have e : gs (𝟙 (Sp V)) (p z) ⊤ ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom v) =
      algebraMap V ((Spec.structureSheaf V).presheaf.stalk P) v := by
    rw [gs_eq _ _ (⊤ : (Sp V).Opens) (show (𝟙 (Sp V) : Sp V ⟶ Sp V) (p z) ∈ (⊤ : (Sp V).Opens) from trivial)]
    rfl
  rw [e]
  exact IsLocalization.AtPrime.isUnit_to_map_iff ((Spec.structureSheaf V).presheaf.stalk P) P.asIdeal v

theorem isNormalScheme_sp (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] :
    IsNormalScheme (Sp R) := by
  refine (isNormalScheme_iff _).2 fun P => ?_
  let P' : PrimeSpectrum R := P
  change IsDomain ((Spec.structureSheaf R).presheaf.stalk P') ∧
    IsIntegrallyClosed ((Spec.structureSheaf R).presheaf.stalk P')
  have hle := P'.asIdeal.primeCompl_le_nonZeroDivisors
  exact ⟨IsLocalization.isDomain_of_le_nonZeroDivisors ((Spec.structureSheaf R).presheaf.stalk P') hle,
    isIntegrallyClosed_of_isLocalization _ _ hle⟩

end GlobalTheory.Spread

namespace GlobalTheory.Spread

variable {V : Type} [CommRing V]

theorem cst_fromSpecStalk (X : Scheme.{0}) (x : X) (p : X ⟶ Sp V) (q : PrimeSpectrum (X.presheaf.stalk x))
    (v : V) :
    cst (X.fromSpecStalk x ≫ p) q v =
      @algebraMap (X.presheaf.stalk x) ((Spec.structureSheaf (X.presheaf.stalk x)).presheaf.stalk q) _ _
        (StructureSheaf.stalkAlgebra _ q) (cst p x v) := by
  unfold cst
  refine (gs_pull (X.fromSpecStalk x) p q ⊤ trivial _).symm.trans
    ((gs_fromSpecStalk X x (p ⁻¹ᵁ ⊤) trivial _ q).trans ?_)
  congr 1

theorem exists_closedFibre_of_generic (R : Type) [CommRing R] [IsLocalRing R] (G : Over (Sp R))
    [GrpObj G] [GeometricallyIntegral G.hom] (y : G.left)
    (hy : ∀ w : G.left, w ⤳ y → G.hom w = G.hom y → w = y) :
    ∃ z : G.left, G.hom z = closedPoint R ∧ y ⤳ z := by
  set P := G.hom y
  have hI : IsIntegral (G.hom.fiber P) :=
    GeometricallyIntegral.geometrically_isIntegral (f := G.hom) ((Sp R).fromSpecResidueField P)
      (pullback.fst _ _) (pullback.snd _ _) (IsPullback.of_hasPullback _ _)
  let η := G.hom.fiberι P (genericPoint (G.hom.fiber P))
  have hη : ∀ w : G.left, G.hom w = P → η ⤳ w := by
    intro w hw
    obtain ⟨w', rfl⟩ : w ∈ Set.range (G.hom.fiberι P) := by rw [Scheme.Hom.range_fiberι]; exact hw
    exact (genericPoint_specializes w').map (G.hom.fiberι P).continuous
  have hηP : G.hom η = P := by
    have : η ∈ Set.range (G.hom.fiberι P) := ⟨_, rfl⟩
    rw [Scheme.Hom.range_fiberι] at this
    exact this
  have hηy : η = y := hy η (hη y rfl) hηP
  let e := (MonObj.one : 𝟙_ (Over (Sp R)) ⟶ G).left
  have he : ∀ u, G.hom (e u) = u := fun u => by
    change (e ≫ G.hom) u = u
    rw [Over.w]
    rfl
  refine ⟨e (closedPoint R), he _, ?_⟩
  rw [← hηy]
  exact (hη (e P) (he P)).trans ((IsLocalRing.specializes_closedPoint P).map e.continuous)

end GlobalTheory.Spread

namespace GlobalTheory.Spread

theorem dvd_of_dvd_near_closedFibre : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsNoetherianRing R → IsIntegrallyClosed R →
    ∀ (G : Over (Sp R)) [GrpObj G], IsSemiAbelian G → ∀ (r : R), r ≠ 0 → ∀ (W : G.left.Opens) (a : Γ(G.left, W))
    (x : G.left), x ∈ W → (∀ y ∈ W, (∃ z : G.left, G.hom z = closedPoint R ∧ y ⤳ z) → cst G.hom y r ∣ gs (𝟙 G.left) y W a) →
    cst G.hom x r ∣ gs (𝟙 G.left) x W a := by
  intro R _ _ _ hN hIC G _ hG r hr W a x hxW H
  have : Smooth G.hom := hG.smooth
  have : GeometricallyConnected G.hom := hG.geomConnected
  have : GeometricallyIntegral G.hom := GlobalTheory.geometricallyIntegral_of_smooth G.hom
  have : IsNormalScheme (Sp R) := isNormalScheme_sp R
  have : IsNormalScheme G.left := GlobalTheory.isNormalScheme_of_smooth G.hom
  have : IsLocallyNoetherian G.left := LocallyOfFiniteType.isLocallyNoetherian G.hom
  obtain ⟨_, _⟩ := (isNormalScheme_iff G.left).1 ‹_› x
  have ha : cst G.hom x r ≠ 0 := by
    intro h0
    have hreg := cst_regular G.hom x hr
    rw [h0] at hreg
    exact one_ne_zero (hreg (by simp : (0 : G.left.presheaf.stalk x) * 1 = 0 * 0))
  refine GlobalTheory.dvd_of_forall_height_eq_one ha fun q _ hq1 haq => ?_
  let f := G.left.fromSpecStalk x
  let Q : PrimeSpectrum (G.left.presheaf.stalk x) := ⟨q, inferInstance⟩
  have hmem : ∀ Q' : PrimeSpectrum (G.left.presheaf.stalk x),
      r ∈ (G.hom (f Q')).asIdeal ↔ cst G.hom x r ∈ Q'.asIdeal := by
    intro Q'
    letI := StructureSheaf.stalkAlgebra (G.left.presheaf.stalk x) Q'
    have e1 := isUnit_cst_iff (f ≫ G.hom) Q' r
    rw [cst_fromSpecStalk] at e1
    have e2 := IsLocalization.AtPrime.isUnit_to_map_iff
      ((Spec.structureSheaf (G.left.presheaf.stalk x)).presheaf.stalk Q') Q'.asIdeal (cst G.hom x r)
    have e := e1.symm.trans e2
    constructor
    · intro h
      by_contra h'
      exact (e.2 h') h
    · intro h
      by_contra h'
      exact (e.1 h') h
  have hyx : f Q ⤳ x := (Scheme.range_fromSpecStalk (x := x)).le ⟨Q, rfl⟩
  have hyW : f Q ∈ W := hyx.mem_open W.2 hxW
  have key : ∃ z : G.left, G.hom z = closedPoint R ∧ f Q ⤳ z := by
    apply exists_closedFibre_of_generic R G (f Q)
    intro w hwy hw
    obtain ⟨Q'', rfl⟩ : w ∈ Set.range f := by
      rw [Scheme.range_fromSpecStalk]; exact hwy.trans hyx
    let Q' : PrimeSpectrum (G.left.presheaf.stalk x) := Q''
    have hsp : Q' ⤳ Q := (f.isEmbedding.isInducing.specializes_iff).1 hwy
    have hle : Q'.asIdeal ≤ q := (PrimeSpectrum.le_iff_specializes Q' Q).2 hsp
    have haQ' : cst G.hom x r ∈ Q'.asIdeal := (hmem Q').1 (by change r ∈ (G.hom (f Q'')).asIdeal; rw [hw]; exact (hmem Q).2 haq)
    have hQ : Q'' = Q := by
      by_contra hne
      have hlt : Q'.asIdeal < q := lt_of_le_of_ne hle (fun h => hne (PrimeSpectrum.ext h))
      have h1 := Ideal.height_strict_mono_of_isPrime hlt
      rw [hq1, ENat.lt_one_iff_eq_zero, Ideal.height_eq_zero_iff_eq_bot] at h1
      rw [h1] at haQ'
      exact ha haQ'
    rw [hQ]
  obtain ⟨t, ht⟩ := H (f Q) hyW key
  have hd := map_dvd (f.stalkMap Q).hom ⟨t, ht⟩
  replace hd : cst (f ≫ G.hom) Q r ∣ gs f Q W a := by
    have e1 := stalkMap_cst f G.hom Q r
    have e2 := gs_stalkMap f Q W hyW a
    rw [← e1, e2]
    exact hd
  rw [cst_fromSpecStalk, gs_fromSpecStalk _ x W hxW] at hd
  letI := StructureSheaf.stalkAlgebra (G.left.presheaf.stalk x) Q
  haveI : IsLocalization Q.asIdeal.primeCompl
      ((Spec.structureSheaf (G.left.presheaf.stalk x)).presheaf.stalk Q) :=
    StructureSheaf.IsLocalization.to_stalk _ Q
  obtain ⟨w, hw⟩ := hd
  obtain ⟨⟨c, s⟩, rfl⟩ := IsLocalization.mk'_surjective (S := (Spec.structureSheaf (G.left.presheaf.stalk x)).presheaf.stalk Q)
    Q.asIdeal.primeCompl w
  dsimp only at hw
  have e : algebraMap (G.left.presheaf.stalk x) ((Spec.structureSheaf (G.left.presheaf.stalk x)).presheaf.stalk Q)
      (gs (𝟙 G.left) x W a * s) =
      algebraMap (G.left.presheaf.stalk x) ((Spec.structureSheaf (G.left.presheaf.stalk x)).presheaf.stalk Q)
      (cst G.hom x r * c) := by
    rw [map_mul, hw]
    erw [mul_assoc, IsLocalization.mk'_spec]
    rw [map_mul]
  obtain ⟨u, hu⟩ := (IsLocalization.eq_iff_exists Q.asIdeal.primeCompl _).1 e
  refine ⟨u * s, Q.asIdeal.primeCompl.mul_mem u.2 s.2, ⟨u * c, ?_⟩⟩
  linear_combination hu

end GlobalTheory.Spread
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBaseFieldMultipleOfNthRootComplexification
section
open scoped TensorProduct

namespace GlobalTheory.KeyFourth

theorem exists_eq_smul_of_pow_eq_pow {R : Type*} [CommRing R] [IsDomain R] [Algebra ℂ R]
    {n : ℕ} (hn : 0 < n) {x y : R} (h : x ^ n = y ^ n) : ∃ z : ℂ, x = z • y := by
  have : NeZero n := ⟨hn.ne'⟩
  have h0 := Complex.isPrimitiveRoot_exp n hn.ne'
  have h1 := h0.map_of_injective (algebraMap ℂ R).injective
  have h2 := h1.pow_sub_pow_eq_prod_sub_mul x y hn
  rw [h, sub_self] at h2
  obtain ⟨ζ, hζ, hz⟩ := Finset.prod_eq_zero_iff.1 h2.symm
  rw [Polynomial.mem_nthRootsFinset hn] at hζ
  obtain ⟨i, -, hi⟩ := h1.eq_pow_of_pow_eq_one hζ
  refine ⟨Complex.exp (2 * Real.pi * Complex.I / n) ^ i, ?_⟩
  rw [Algebra.smul_def, map_pow, hi]
  exact sub_eq_zero.1 hz

theorem exists_eq_smul_pow_of_pow_eq_tmul :
    ∀ (K : Type) [Field K] [Algebra K ℂ] (A : Type) [CommRing A] [Algebra K A]
      [IsDomain (ℂ ⊗[K] A)] (n : ℕ) (w : ℂ ⊗[K] A) (C : ℂ) (u : A), 0 < n → C ≠ 0 → u ≠ 0 →
      w ^ n = C ⊗ₜ[K] u → ∃ (a : K) (b : A), a ≠ 0 ∧ u = a • b ^ n := by
  intro K _ _ A _ _ _ n w C u hn hC hu hw
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one K (one_ne_zero : (1 : ℂ) ≠ 0)
  let T : ℂ ⊗[K] A →ₗ[K] A := (TensorProduct.lid K A).toLinearMap ∘ₗ LinearMap.rTensor A f
  have hT : ∀ (c : ℂ) (a : A), T (c ⊗ₜ a) = f c • a := fun c a => by simp [T]
  have hne : ∀ (c : ℂ) (a : A), c ≠ 0 → a ≠ 0 → c ⊗ₜ[K] a ≠ 0 := by
    intro c a hc ha h
    have h1 : (1 : ℂ) ⊗ₜ[K] a = 0 := by
      have := congrArg (fun t : ℂ ⊗[K] A => c⁻¹ • t) h
      simpa [TensorProduct.smul_tmul', hc] using this
    have h2 := hT 1 a
    rw [h1, map_zero, hf, one_smul] at h2
    exact ha h2.symm
  have hw0 : w ≠ 0 := by
    rintro rfl
    rw [zero_pow hn.ne'] at hw
    exact hne C u hC hu hw.symm
  have hst : ∀ σ : ℂ ≃ₐ[K] ℂ, ∀ x ∈ Submodule.span ℂ {w},
      σ.toLinearMap.rTensor A x ∈ Submodule.span ℂ {w} := by
    intro σ x hx
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hx
    let S : ℂ ⊗[K] A →ₐ[K] ℂ ⊗[K] A := Algebra.TensorProduct.map σ.toAlgHom (AlgHom.id K A)
    have hS : ∀ t, σ.toLinearMap.rTensor A t = S t := by
      intro t
      induction t with
      | zero => simp
      | tmul b v => simp [S]
      | add x y hx hy => simp only [map_add, hx, hy]
    obtain ⟨μ, hμ⟩ := IsAlgClosed.exists_pow_nat_eq (σ C / C) hn
    have h1 : (S w) ^ n = (μ • w) ^ n := by
      rw [← map_pow, smul_pow, hw, hμ, TensorProduct.smul_tmul', smul_eq_mul,
        div_mul_cancel₀ _ hC]
      simp [S]
    obtain ⟨z, hz⟩ := exists_eq_smul_of_pow_eq_pow hn h1
    have h2 : c • w = (c ⊗ₜ[K] (1 : A)) * w := by
      rw [Algebra.smul_def]; rfl
    have h3 : S (c ⊗ₜ[K] (1 : A)) * S w = σ c • S w := by
      rw [Algebra.smul_def]
      simp [S]
    rw [hS, h2, map_mul, h3, hz, smul_smul, smul_smul]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self w)
  obtain ⟨N, hN, -⟩ := (GlobalTheory.GaloisDescent.complex_stable_iff_exists_baseChange _).1 hst
  have hN0 : N ≠ ⊥ := by
    rintro rfl
    rw [Submodule.baseChange_bot, eq_comm, Submodule.span_singleton_eq_bot] at hN
    exact hw0 hN
  obtain ⟨b, hbN, hb0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hN0
  have hb : (1 : ℂ) ⊗ₜ[K] b ∈ Submodule.span ℂ {w} :=
    hN ▸ Submodule.tmul_mem_baseChange_of_mem 1 hbN
  obtain ⟨l, hl⟩ := Submodule.mem_span_singleton.1 hb
  have hpow : (1 : ℂ) ⊗ₜ[K] (b ^ n) = (l ^ n * C) ⊗ₜ[K] u := by
    have := congrArg (· ^ n) hl
    simp only [smul_pow, hw, Algebra.TensorProduct.tmul_pow, one_pow, TensorProduct.smul_tmul',
      smul_eq_mul] at this
    exact this.symm
  have hbn : b ^ n ≠ 0 := by
    intro h
    have h1 : ((1 : ℂ) ⊗ₜ[K] b) ^ n = 0 := by
      rw [Algebra.TensorProduct.tmul_pow, h, TensorProduct.tmul_zero]
    exact hne 1 b one_ne_zero hb0 (pow_eq_zero_iff hn.ne' |>.1 h1)
  have h4 := congrArg T hpow
  rw [hT, hT, hf, one_smul] at h4
  have h5 : f (l ^ n * C) ≠ 0 := by
    intro h
    rw [h, zero_smul] at h4
    exact hbn h4
  exact ⟨(f (l ^ n * C))⁻¹, b, inv_ne_zero h5, by rw [h4, smul_smul, inv_mul_cancel₀ h5, one_smul]⟩

end GlobalTheory.KeyFourth
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsComplexArcOfAnalyticModelOnFlowOrbit
section
noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory GlobalTheory.ArcQ GlobalTheory.ArcCM GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.CuspFrom
open scoped LaurentSeries
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

namespace GlobalTheory.CuspFrom

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D D' : Datum H} {k : Type} [Field k]
  {Q : Type} [Group Q] {act : 𝓞 E → Q → Q} {e : ℕ → Q → Q → kˣ → Prop}

theorem tateIso_similar_zeta
    (he : ∀ n x y c c', e n x y c → e n x y c' → c = c') (I : TateIso D k Q act e) (I' : TateIso D' k Q act e) :
    ∃ (f : ℕ → D.La →ₗ[𝓞 E] D'.La) (ν : ℕ → ℤ),
      (∀ n m : ℕ, 0 < n → 0 < m → ∀ a, ∃ e, f (n * m) a = f n a + n • e) ∧
      (∀ n : ℕ, 0 < n → (∀ a, (∃ e, f n a = n • e) ↔ ∃ e, a = n • e) ∧ ∀ a', ∃ a e, a' = f n a + n • e) ∧
      (∀ n : ℕ, 0 < n → IsCoprime (ν n) (n : ℤ)) ∧
      (∀ n m : ℕ, 0 < n → 0 < m → (n : ℤ) ∣ ν (n * m) - ν n) ∧
      (∀ n : ℕ, 0 < n → ∀ a a', (n : ℤ) ∣ D'.EF (f n a) (f n a') - ν n * D.EF a a') ∧
      (∀ n : ℕ, 0 < n → ∀ a, I.ev n a = I'.ev n (f n a)) ∧
      ∀ n : ℕ, 0 < n → I.ζ n = I'.ζ n ^ ν n := by
  have h1 : ∀ n : ℕ, ∃ f : D.La →ₗ[𝓞 E] D'.La, 0 < n → ∀ a, I.ev n a = I'.ev n (f a) := by
    intro n
    rcases Nat.eq_zero_or_pos n with h | h
    · exact ⟨0, fun h' => absurd h h'.ne'⟩
    · obtain ⟨f, hf⟩ := tateIso_exists_lift_of_two_data I I' h
      exact ⟨f, fun _ => hf⟩
  have h2 : ∀ n : ℕ, ∃ ν : ℕ, 0 < n → I.ζ n = I'.ζ n ^ ν := by
    intro n
    rcases Nat.eq_zero_or_pos n with h | hn
    · exact ⟨1, fun h' => absurd h h'.ne'⟩
    · haveI : NeZero n := ⟨hn.ne'⟩
      obtain ⟨i, -, hi⟩ := (I'.ζ_prim n hn).eq_pow_of_mem_rootsOfUnity
        ((mem_rootsOfUnity _ _).2 (I.ζ_prim n hn).pow_eq_one)
      exact ⟨i, fun _ => hi.symm⟩
  choose f hf using h1
  choose ν hν using h2
  refine ⟨f, fun n => ν n, ?_, ?_, ?_, ?_, ?_, hf, fun n hn => ?_⟩
  · intro n m hn hm a
    rw [← tateIso_ev_eq_iff_add I' hn, ← hf n hn, ← I'.tower n m hn hm, ← hf (n * m) (Nat.mul_pos hn hm),
      I.tower n m hn hm]
  · intro n hn
    refine ⟨fun a => ?_, fun a' => ?_⟩
    · rw [← I'.ker n hn, ← I.ker n hn, hf n hn]
    · obtain ⟨a, ha⟩ := (I.onto n hn _).1 (tateIso_ev_pow I' hn a')
      rw [hf n hn] at ha
      exact ⟨a, (tateIso_ev_eq_iff_add I' hn _ _).1 ha.symm⟩
  · intro n hn
    have h := I.ζ_prim n hn
    rw [hν n hn] at h
    exact Nat.isCoprime_iff_coprime.2 (((I'.ζ_prim n hn).pow_iff_coprime hn _).1 h)
  · intro n m hn hm
    have h : I'.ζ n ^ ν (n * m) = I'.ζ n ^ ν n := by
      rw [← hν n hn, ← I.ζ_pow n m hn hm, hν (n * m) (Nat.mul_pos hn hm), ← I'.ζ_pow n m hn hm, ← pow_mul,
        ← pow_mul, mul_comm m]
    rw [← (I'.ζ_prim n hn).zpow_eq_one_iff_dvd, zpow_sub, zpow_natCast, zpow_natCast, h, mul_inv_cancel]
  · intro n hn a b
    have e1 := I'.isom n hn (f n a) (f n b)
    have e2 := I.isom n hn a b
    rw [hf n hn a, hf n hn b] at e2
    have h := he n _ _ _ _ e1 e2
    rw [hν n hn, ← zpow_natCast, ← zpow_mul] at h
    rw [← (I'.ζ_prim n hn).zpow_eq_one_iff_dvd, zpow_sub, h, mul_inv_cancel]
  · rw [zpow_natCast]
    exact hν n hn

end

theorem familyUnif_lattice_similar_zeta (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H)
    (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (U : FamilyUnif Xo σ ty)
    (i : Fin U.n) (P : (U.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (U.Di i) ty P) :
    ∃ (f : ℕ → D.La →ₗ[𝓞 E] (U.Di i).La) (ν : ℕ → ℤ),
      (∀ n m : ℕ, 0 < n → 0 < m → ∀ a, ∃ e, f (n * m) a = f n a + n • e) ∧
      (∀ n : ℕ, 0 < n → (∀ a, (∃ e, f n a = n • e) ↔ ∃ e, a = n • e) ∧ ∀ a', ∃ a e, a' = f n a + n • e) ∧
      (∀ n : ℕ, 0 < n → ∀ a a', (n : ℤ) ∣ (U.Di i).EF (f n a) (f n a') - ν n * D.EF a a') ∧
      (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), ∃ e, f l.M a = U.t i a + l.M • e) ∧
      (∀ a, ∃ e, f l.A a = U.t i a + l.A • e) ∧
      σ (baseKA l).ζ = Complex.exp (-(2 * Real.pi * Complex.I) * (ν l.A : ℂ) / l.A) := by
  obtain ⟨-, I, hζ, hA, hM⟩ := Xo.univ.geom ℂ (U.u i P) σ (U.over_σ i P hP)
  obtain ⟨f, ν, h1, h2, -, -, h5, h6, h7⟩ := tateIso_similar_zeta
    (fun n x y c c' => weilIs_unique_fieldPoint _ _ _ Xo.univ.t.PP.isLB ℂ _ n x y c c') I (familyUnifTateIso U hP)
  have hM0 : 0 < l.M := lt_of_lt_of_le (by norm_num) l.three_le
  refine ⟨f, ν, h1, h2, h5, fun a ha => ?_, fun a => ?_, ?_⟩
  · rw [← tateIso_ev_eq_iff_add (familyUnifTateIso U hP) hM0, ← h6 _ hM0, ← hM a ha]
    exact U.ex_eta i P hP a ha
  · rw [← tateIso_ev_eq_iff_add (familyUnifTateIso U hP) l.A_pos, ← h6 _ l.A_pos, ← hA a]
    exact U.ex_etaA i P hP a
  · rw [← hζ, h7 _ l.A_pos]
    exact expNegUnit_zpow_val _ _

theorem exists_arcIn_input : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r) (Uw : UnfWit U) (k : U.Comp) (ξ' : Fin r → E) (x : Frame (U.X k).Ψ r) (B : GlobalTheory.CM.PAT H (Sp ℂ)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → letI := H.starRing; ∀ (A : AnArc (𝓞 E)) (gam : (Uw.F.Di (Uw.ik k)).La ≃ₗ[𝓞 E] A.La) (ξ : Module.Dual ℤ A.X) (DB : Datum H) (tyB : Fin A.gB → (E →+* ℂ)) (eB : DB.La ≃+ A.abelian₂) (ex : (Fin A.gB → ℂ) → (Over.mk (spMap (RingHom.id ℂ)) ⟶ B.t.G)), OnOrbit Uw k ξ' x A gam ξ → Module.finrank (𝓞 E) A.X = 1 → (∀ y y', (2 * l.M' : ℤ) ∣ A.be y y') → PrimAn H A → AbDat H A DB tyB eB → DB.p = Dw.p - 1 → DB.q = Dw.q - 1 → 1 ≤ Dw.p → 1 ≤ Dw.q → GlobalTheory.CM.IsExp B (RingHom.id ℂ) DB tyB (A.abelian₂.subtype.toAddMonoidHom.comp eB.toAddMonoidHom) ex → ∃ (aC : ArcIn Dw l (RingHom.id c.F) ℂ σ) (Λ : GtAn₀ aC) (hA : Λ.A = A), (∀ v, Λ.Lifts (aC.eta v) (cast (congrArg AnArc.La hA.symm) (gam (Uw.F.t (Uw.ik k) v)))) ∧ ∀ v, Λ.Lifts (aC.etaA v) (cast (congrArg AnArc.La hA.symm) (gam (Uw.F.t (Uw.ik k) v))) := by
  intro E _ _ _ H Dw l Xo c _ _ σ r U Uw k ξ' x B hσ _
  let _ := H.starRing
  intro A gam ξ DB tyB eB ex ⟨hgam, _, T₀, hT₀⟩ hrk hbe ⟨hχ, hψ⟩ ⟨hF, hty, _, hEF, _⟩ hp hq hp1 hq1
    ⟨_, hol, add, onto, ker, lin, weil⟩
  have hK := GlobalTheory.ArcCM.known_holds
  obtain ⟨T, m, hg⟩ := GlobalTheory.CM.PAT.exists_pullback E H _ _ (spMap (RingHom.id ℂ)) B
  obtain ⟨-, hiso⟩ := GlobalTheory.CM.PAT.exists_of_sabMap E H _ _ _ B _ m
  obtain ⟨w₀, hw₀, -⟩ := m.lin
  obtain ⟨sym, hsym, hsym'⟩ := (GlobalTheory.isSymmetric_iff_exists_gen _ _ T.t.PP).1 T.t.sym
  have := T.t.act.hom H.w0
  obtain ⟨w, hw, hw'⟩ := CxFibre.exists_primGen T.t.PP (T.t.act.act H.w0) T.t.prim
  let oa : T.pol.OAct (𝓞 E) := ⟨T.t.act.toRingAct, fun a =>
    (GlobalTheory.RosLam.rosatiAdj_iff_lamEq hK.laws.globalFns _ T.pol _ _ (T.t.act.hom a) (T.t.act.hom _)).2 (by
      change GlobalTheory.CM.LamEq _ _ _ _ _ (T.t.act.act (H.bar a))
      simpa [GlobalTheory.CM.LamEq] using T.t.adj a)⟩
  obtain ⟨u, χ, hgP, lam, hAH, hrig, hθ, hex⟩ := CxFibre.exists_holUnif_of_exp hK.theta B.t.PP.isLB
    (spMap (RingHom.id ℂ)) T.pol T.t.PP.rig
    T.t.PP.rigGen m.φ m.cart ⟨w₀, hw₀⟩ A.abelian₂ A.discrete A.full A.Hm A.Hm_herm A.Hm_pos (fun a b => A.Ef a b) A.Ef_eq
    ex hol add onto
    (fun z => (ker z).trans ⟨fun ⟨a, ha⟩ => ha ▸ (eB a).2, fun hz => ⟨eB.symm ⟨z, hz⟩, by simp⟩⟩)
    (fun n a b c hn hc => by
      obtain ⟨a, rfl⟩ := eB.surjective a
      obtain ⟨b, rfl⟩ := eB.surjective b
      exact weil n a b c hn (by rw [hEF]; exact hc))
  have hact : ∀ (a : 𝓞 E) z, u.ex (fun i => tyB i (a : E) * z i) = u.ex z ≫ T.t.act.act a := fun a z =>
    Over.OverMorphism.ext (m.cart.1.hom_ext (by
      rw [hex, lin, Over.comp_left, Over.comp_left, Category.assoc, m.act, ← Category.assoc, hex])
      (by rw [Over.w, Over.w]))
  have hact' : ∀ (a : 𝓞 E) z, u.ex (A.F a z) = u.ex z ≫ T.t.act.act a := fun a z => by
    rw [← hact]; exact congrArg u.ex (funext (hF a z))
  obtain rfl : χ = fun b : u.Λ => A.chi ⟨b, lam.le b.2⟩ := funext fun a => by
    rw [CxFibre.chi_eq T.t.PP.isLB _ w hw u A.Hm χ hAH (A.F H.w0) (hact' _) a
      ⟨_, lam.ge (A.F_mem H.w0 a (lam.le a.2))⟩ rfl, hχ]
    have h₁ := A.Ef_eq_im (A.FLam H.w0 ⟨a, lam.le a.2⟩) ⟨a, lam.le a.2⟩
    rw [← A.H_conj, Complex.conj_im] at h₁
    have h₂ : (hermForm A.Hm a (A.F H.w0 a)).im = -(A.Ef (A.FLam H.w0 ⟨a, lam.le a.2⟩) ⟨a, lam.le a.2⟩ : ℤ) := by
      rw [h₁, neg_neg]; rfl
    generalize A.Ef (A.FLam H.w0 ⟨a, lam.le a.2⟩) ⟨a, lam.le a.2⟩ = n at h₂
    rw [h₂, ← Complex.exp_neg_pi_mul_I, ← Complex.exp_int_mul]
    congr 1
    push_cast
    ring
  obtain ⟨s, hs, -⟩ := hT₀ ((T₀ + 1 : ℝ) * Complex.I) (by simp)
  obtain ⟨f, ν, f₁, f₂, f₃, f₄, f₅, f₆⟩ :=
    familyUnif_lattice_similar_zeta E H Dw l Xo _ _ _ Uw.F (Uw.ik k) _ (Uw.period k ⟨_, hs⟩)
  obtain ⟨a, Λ, hA, -, -, -, -, -, -, heta, hetaA⟩ := GlobalTheory.ArcOfModel.exists_arcIn hK.laws hK.laws2 Dw l
    (RingHom.id c.F) σ T.pol T.t.PP.rig T.t.PP.rigGen T.t.cub sym hsym hsym' oa ⟨w, hw, hw'⟩ A u lam hAH hrig
    (fun j _ => hθ j) hact' hψ (Module.nontrivial_of_finrank_pos (R := 𝓞 E) (hrk ▸ one_pos)) hbe _ gam hgam
    (Uw.F.t (Uw.ik k)) f ν f₁ (fun n hn v => ((f₂ n hn).1 v).1) (fun n hn => (f₂ n hn).2)
    f₃ f₄ f₅
    (fun z hz => (congrArg σ (Subtype.ext hz)).trans f₆)
    (fun ρ hρ τ => by
      obtain ⟨τ₀, rfl⟩ := GlobalTheory.PeriodPoint.exists_embedding (RingHom.id ℂ) τ
      have hρ' : σ ρ = H.rt0 := by
        rw [← hσ]
        exact congrArg σ (Subtype.ext hρ)
      refine ⟨_, CxFibre.lieMult_card hK.theta T.pol hgP u _ tyB hact τ₀, ?_⟩
      rw [hrk, hρ']
      split_ifs with h
      · rw [(hty τ₀).1 h]; omega
      · rw [(hty τ₀).2 h]; omega)
  refine ⟨a, Λ.toGtAn₀, hA, fun v q hq => ?_, fun v q hq => ?_⟩
  · rw [(TorusExt.existsUnique_qkExt a.bimult (algebraMap (FractionRing ℂ) ℂ) (RingHom.comp_id _) _).unique hq (heta v)]
    exact qk_equiv_refl a.bimult _
  · rw [(TorusExt.existsUnique_qkExt a.bimult (algebraMap (FractionRing ℂ) ℂ) (RingHom.comp_id _) _).unique hq (hetaA v)]
    exact qk_equiv_refl a.bimult _

end GlobalTheory.CuspFrom
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFramedPointOverOfLieEigenspaceFrame
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.FlagBundle

namespace GlobalTheory.ShFam

theorem exists_frPt_ptF_over_of_eigFrame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (L : Type) [Field L] (φ : c.F →+* L) (z : Sp L ⟶ Xo.XF c) (x : Sp L ⟶ Z.X) (g : EigFrame Z φ x), z ≫ pullback.snd _ _ = spMap φ → z ≫ Z.jQ ≫ genι Z = x → letI := φ.toAlgebra; ∃ y : FrPt Xo c L, GlobalTheory.AllWt.ptF y = z ∧ ∀ τ i, ∃ w : Sp (DualNumber L) ⟶ Z.oF.t.G.left, w ≫ Z.oF.t.G.hom = spMap (algebraMap L (DualNumber L)) ≫ z ∧ w ≫ Z.m0.toSABMap.φ = y.u τ i ∧ w ≫ Z.m.φ = g.v τ i := by
  intro E _ _ _ H Dw l Xo c O _ β Z L _ φ z x g hs hx
  letI := φ.toAlgebra
  obtain ⟨y, w, hy, hw⟩ := OpenReg.exists_frPt_of_eigFrame (Z := Z) z hs hx g
  refine ⟨y, pullback.hom_ext ?_ ?_, fun τ i => ⟨w τ i, hw τ i⟩⟩
  · exact (pullback.lift_fst _ _ _).trans hy
  · exact (pullback.lift_snd _ _ _).trans hs.symm

end GlobalTheory.ShFam
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsInertiaMovesTameRootStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_inertia_moves_tame_root : ∀ (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W] [CharZero W]
    (F : Type) [Field F] [Algebra (FractionRing W) F] [IsAlgClosure (FractionRing W) F] (ϖ : W), Irreducible ϖ →
    ∀ k : ℕ, IsUnit (k : W) → ∃ (O : ValuationSubring F) (φ : W →+* O) (σ : F →ₐ[FractionRing W] F) (π : F),
      IsLocalHom φ ∧ (∀ w, (φ w : F) = algebraMap (FractionRing W) F (algebraMap W (FractionRing W) w)) ∧
      (∀ x ∈ O, O.valuation (σ x - x) < 1) ∧ π ^ k = algebraMap (FractionRing W) F (algebraMap W (FractionRing W) ϖ) ∧
      IsPrimitiveRoot (σ π / π) k := by
  first | exact @GlobalTheory.InertiaTameRoot.exists_inertia_moves_root | exact GlobalTheory.InertiaTameRoot.exists_inertia_moves_root | (intros; apply GlobalTheory.InertiaTameRoot.exists_inertia_moves_root <;> assumption)
end

