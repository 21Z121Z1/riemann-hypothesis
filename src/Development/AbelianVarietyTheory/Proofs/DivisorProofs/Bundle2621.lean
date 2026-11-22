import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2373
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2502
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0045
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0048
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0056
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0069
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0054
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0078
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0035
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsFieldsSeparately
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0046
import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2345
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0609
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2501
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2362
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineEigenframeNearImage
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBlockMetricDiagForm
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2513
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibOfIsGenerated
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0311
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0075
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2212
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2243
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0079
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2504
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZbLeftWhiskerRight

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramePolynomialCoeffIntegralAlmostAllPrimes
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LamT (CMPt)
open GlobalTheory.Frames GlobalTheory.LamT

namespace GlobalTheory.CoeffInt

theorem coeff_valuation_le_one_almost_all : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (z : CMPt Xo c) (f : ℕ) (La : ℝ), z.Good f La →
    ∀ (e : Formalism.L2.Pj.Ix Dw → ℤ) (k : (E →+* ℂ) → ℕ), e none = 0 →
    ∃ S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 z.K)), ∀ p ∉ S,
      ∀ F ∈ GlobalTheory.AllWt.secZ Xo c e, (∀ v, ∀ w ∈ valSet Xo c (algCls Xo c) v, 0 ≤ w F) →
      ∀ G : MvPolynomial (Formalism.L2.LamCM.FrVar Dw.mult) z.K, (∀ (y' : FrPt Xo c z.K) (Y : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) z.K) (s : z.Kˣ),
          (∀ b, (Y b).det ≠ 0) → GlobalTheory.Frames.FrChg (fun b => (Y b).transpose) (s : z.K) z.y y' →
          (∏ b, (Y b).det ^ k b) * evR Xo c F y' = Formalism.L2.LamCM.evalFr G Y) →
        ∀ μ, p.valuation z.K (MvPolynomial.coeff μ G) ≤ 1 := by
  intro E _ _ _ H Dw l Xo c _ z f La hz e k he
  classical
  obtain ⟨S₁, hS₁⟩ := GlobalTheory.T.cmPoint_eigenbasis_change_det_integral_almost_all_primes E H Dw l Xo c z f La hz
  have hfin : (⋃ j, {p : IsDedekindDomain.HeightOneSpectrum (𝓞 z.K) |
      FractionalIdeal.count z.K p (z.ℓ j).I ≠ 0}).Finite :=
    Set.finite_iUnion fun j => Filter.eventually_cofinite.1 (FractionalIdeal.finite_factors (z.ℓ j).I)
  refine ⟨S₁ ∪ hfin.toFinset, fun p hp F hF hv G hG μ => ?_⟩
  simp only [Finset.mem_union, not_or, Set.Finite.mem_toFinset, Set.mem_iUnion, Set.mem_setOf_eq, not_exists,
    not_not] at hp
  obtain ⟨hp1, hp2⟩ := hp
  have hgen : ∀ j, Formalism.L2.LamCM.IsLocGen p (1 : z.K) (z.ℓ j).I := fun j =>
    ⟨one_ne_zero, by rw [FractionalIdeal.spanSingleton_one, FractionalIdeal.count_one, hp2 j]⟩
  obtain ⟨T, iK, hT, hiK⟩ := GlobalTheory.T.exists_completeDVR_completion_integral_iff z.K p
  obtain ⟨M⟩ := (GlobalTheory.T.exists_cmPoint_localModel_over_dvr E H Dw l Xo c z T iK).1 fun a => (hiK _).2 (p.valuation_le_one a)
  let io : c.F →+* T.Fr := iK.comp (algebraMap c.F z.K)
  letI := io.toAlgebra
  let φ : z.K →ₐ[c.F] T.Fr := { iK with commutes' := fun _ => rfl }
  obtain ⟨yT, hyT⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c _ _ φ z.y
  have hyx : yT.x = spMap iK ≫ z.x := by rw [hyT.1, hz.2.2.2.1]
  obtain ⟨g, hg, hgL⟩ := (GlobalTheory.T.exists_integralEigenbasis_of_frame_at_localModel E H Dw l Xo c T io M.G.t M.t'.t _ M.m1 M.m2 yT hyx).1
  obtain ⟨s, hsS⟩ := GlobalTheory.T.exists_unit_integral_generator_principal_local_model E H Dw l Xo c T io M.G M.t'.t _ M.m1 M.m2 yT hyx
  obtain ⟨y', hy', -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c T.Fr yT g s hg
  have hL := hgL _ _ hy'
  have hS := hsS _ _ hy'
  have hinv : ∀ b j i, (g b)⁻¹ j i ∈ Set.range (algebraMap T.V T.Fr) := fun b j i => by
    have := GlobalTheory.T.lieLetter_integral_in_integral_eigenbasis E H Dw l Xo c z f La hz p T iK M hiK φ yT y' g s rfl hyT hy' hg hL b j i 1 (hgen _)
    rwa [map_one, _root_.one_mul] at this
  have hR : ∀ x : T.Fr, x ∈ Set.range (algebraMap T.V T.Fr) ↔ x ∈ (algebraMap T.V T.Fr).range :=
    fun x => (RingHom.mem_range).symm
  have hdetinv : ∀ b, ((g b).det)⁻¹ ∈ (algebraMap T.V T.Fr).range := fun b => by
    choose N hN using hinv b
    have e1 : (g b)⁻¹ = (Matrix.of N).map (algebraMap T.V T.Fr) := by
      ext j i; exact (hN j i).symm
    have e2 : ((g b).det)⁻¹ = ((g b)⁻¹).det := by
      rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
    rw [e2, e1]
    exact ⟨(Matrix.of N).det, by rw [RingHom.map_det]; rfl⟩
  have hall := (hR _).1 (hS₁ p hp1 T iK hT hiK M φ yT y' g s rfl hyT hy' hg hL)
  have hdet : ∀ b, (g b).det ∈ (algebraMap T.V T.Fr).range := fun b => by
    have hne : (∏ b' ∈ Finset.univ.erase b, (g b').det) ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun b' _ => (hg b').ne_zero
    have e3 : (g b).det = (∏ b', (g b').det) * ∏ b' ∈ Finset.univ.erase b, ((g b').det)⁻¹ := by
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ b), Finset.prod_inv_distrib, _root_.mul_assoc,
        mul_inv_cancel₀ hne, _root_.mul_one]
    rw [e3]
    exact Subring.mul_mem _ hall (Subring.prod_mem _ fun b' _ => hdetinv b')
  have hτ : (∏ b, (g b).det ^ k b) ∈ (algebraMap T.V T.Fr).range :=
    Subring.prod_mem _ fun b _ => Subring.pow_mem _ (hdet b) _
  obtain ⟨w, hw⟩ := GlobalTheory.T.framePolynomial_coeff_bounded_by_determinants E H Dw l Xo c z f La hz e k he p T iK hT hiK M φ yT y' g s rfl hyT hy' s.ne_zero hg hL
    hS (fun _ _ => 1) (fun b j i => by rw [_root_.one_mul]; exact hinv b j i) F hF hv G
    (fun y' Y hY hch => hG y' Y 1 hY (by rw [Units.val_one]; exact hch)) μ
  simp only [one_pow, Finset.prod_const_one, _root_.mul_one] at hw
  refine (hiK _).1 ((hR _).2 ?_)
  rw [hw]
  exact Subring.mul_mem _ hτ (RingHom.mem_range_self _ _)

end GlobalTheory.CoeffInt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameVectorIsCombinationEigenbasisFlagSpacePoint
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole

namespace GlobalTheory.LogPole

attribute [local instance] Over.cartesianMonoidalCategory Over.braidedCategory

theorem frameVector_isCombination_tangentBasis_flagCover_point {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)}
    (X : GlobalTheory.FlagMod.FlagCover Y) (U : Y.X.affineOpens) {n : ℕ}
    (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (v : Fin n → (Sp (DualNumber Γ(Y.X, U.1)) ⟶ Y.t.G.left))
    (h1 : ∀ i, IsTanAtG Y.t (LogKS.chart U) (v i))
    (h2 : ∀ w', IsTanAtG Y.t (LogKS.chart U) w' →
      ∃! cf : Fin n → Γ(Y.X, U.1), IsCombAtG Y.t (LogKS.chart U) v cf w')
    (h3 : ∀ (a : 𝓞 E) (τ : E →+* ℂ) (i : Fin (Dw.mult τ)), IsCombAtG Y.t (LogKS.chart U) v
      (Pi.single (e ⟨τ, i⟩) (algX Y.s U.1 (embK c τ a))) (v (e ⟨τ, i⟩) ≫ (Y.t.act.act a).left))
    (k : X.F.J) (S : Type) [CommRing S] (z' : Sp S ⟶ X.YY) (x : Sp S ⟶ Y.X) (hU : ⊤ ≤ x ⁻¹ᵁ U.1)
    (hk : ⊤ ≤ z' ⁻¹ᵁ X.F.U k) (hx : z' ≫ X.π = x) :
    ∃ C : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) S, ∀ (σ : E →+* ℂ) (i : Fin (Dw.mult σ)),
      IsCombAtG Y.t x (fun j => spMap (dualMap (ev x U.1 hU)) ≫ v (e ⟨σ, j⟩)) (C σ i)
        (tv (X.F.vecAt k z' hk hx σ i)).left := by
  classical
  subst hx
  have hxψ : spMap (ev (z' ≫ X.π) U.1 hU) ≫ LogKS.chart U = z' ≫ X.π := GlobalTheory.FlagMod.spMap_ev _ U.2 hU
  obtain ⟨b1, b2⟩ := GlobalTheory.LocM.FrameBase.tanBasis_baseChange Y.t (ev (z' ≫ X.π) U.1 hU) (LogKS.chart U) n v h1 h2
  rw [hxψ] at b1 b2

  set ψ := ev (z' ≫ X.π) U.1 hU with hψ
  let φ : c.F →+* S := (ev ((z' ≫ X.π) ≫ Y.s) ⊤ le_top).comp (toΓ c.F)
  have hφ : z' ≫ X.π ≫ Y.s = spMap φ := by
    rw [GlobalTheory.FlagMod.spMap_ev_top, Category.assoc]
  have hφψ : ∀ r : c.F, ψ (algX Y.s U.1 r) = φ r := fun r =>
    GlobalTheory.FlagMod.ev_appLE (z' ≫ X.π) Y.s (by simp) hU le_top (toΓ c.F r)
  let V : Fin n → ReciprocityTheory.ChartRestriction.G.PullbackSections.TanM (z' ≫ X.π) Y.t.G := fun m => GlobalTheory.LieMet.tanOf (b1 m)
  have hb : ∀ W, ∃! a : Fin n → S, ∑ i, a i • V i = W := fun W => by
    obtain ⟨a, ha, hu⟩ := b2 _ (GlobalTheory.LieMet.isTan_tv W)
    exact ⟨a, ((GlobalTheory.LieMet.isComb_iff V a W).1 ha).symm,
      fun a' ha' => hu a' ((GlobalTheory.LieMet.isComb_iff V a' W).2 ha'.symm)⟩
  have hV : ∀ (τ : E →+* ℂ) (j : Fin (Dw.mult τ)) (a : 𝓞 E),
      ReciprocityTheory.ChartRestriction.G.PullbackSections.actR Y.t.act a (V (e ⟨τ, j⟩)) = φ (embK c τ a) • V (e ⟨τ, j⟩) := by
    intro τ j a
    have h := (GlobalTheory.TanBaseChange.tan_comb_baseChange E H Y.X Y.t _ S ψ (LogKS.chart U) _ hxψ).2 n v _ _ (h3 a τ j)
    have e1 : (fun i => ψ ((Pi.single (e ⟨τ, j⟩) (algX Y.s U.1 (embK c τ a)) : Fin n → Γ(Y.X, U.1)) i)) =
        fun i => (Pi.single (e ⟨τ, j⟩) (φ (embK c τ a)) : Fin n → S) i := by
      funext i
      by_cases hi : i = e ⟨τ, j⟩
      · subst hi; simp [hφψ]
      · simp [Pi.single_apply, hi]
    rw [e1] at h
    have e2 : spMap (dualMap ψ) ≫ v (e ⟨τ, j⟩) ≫ (Y.t.act.act a).left =
        (tv (ReciprocityTheory.ChartRestriction.G.PullbackSections.actR Y.t.act a (V (e ⟨τ, j⟩)))).left := by
      rw [← Category.assoc]; rfl
    rw [e2] at h
    rw [(GlobalTheory.LieMet.isComb_iff V _ _).1 h]
    simp [Pi.single_apply]
  letI : Algebra c.F S := φ.toAlgebra
  have hs := GlobalTheory.FlagEmb.EigSpread.splits (E := E) c
  have hu : ∀ z : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)),
      ReciprocityTheory.ChartRestriction.G.PullbackSections.IsEigV (ReciprocityTheory.ChartRestriction.G.PullbackSections.actR Y.t.act) (embK c z.1) (V (e z)) :=
    fun z a => hV z.1 z.2 a
  have hb' : ∀ w, ∃! a : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) → S, ∑ z, a z • V (e z) = w := fun w => by
    obtain ⟨a, ha, hu⟩ := hb w
    refine ⟨fun z => a (e z), ?_, fun a' ha' => ?_⟩
    · rw [← ha]; exact Equiv.sum_comp e (fun i => a i • V i)
    · have h' : ∑ i, a' (e.symm i) • V i = w := by
        rw [← ha', ← Equiv.sum_comp e.symm (fun z => a' z • V (e z))]; simp
      have := hu _ h'
      funext z
      have := congrFun this (e z)
      simpa using this
  have key : ∀ σ i, ∃ cf : Fin (Dw.mult σ) → S, ∑ j, cf j • V (e ⟨σ, j⟩) = X.F.vecAt k z' hk rfl σ i :=
    fun σ i => (GlobalTheory.FlagEmb.EigSpread.block_basis hs (fun z => V (e z)) hu hb' σ _
      (fun a => GlobalTheory.VarFlag.actR_vecAt X φ z' k hk hφ σ i a)).exists
  choose C hC using key
  refine ⟨fun σ => Matrix.of fun i j => C σ i j, fun σ i => ?_⟩
  exact (GlobalTheory.LieMet.isComb_iff (fun j => V (e ⟨σ, j⟩)) (C σ i) _).2 (hC σ i).symm

theorem isCombAtG_block : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c) (U : TF.Y.X.affineOpens) (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)), IsEigBasis TF U e v → ∀ (k : TF.X.F.J) (S : Type) [CommRing S] (z : Sp S ⟶ Y₀ TF.X Z) (hU : ⊤ ≤ (z ≫ toBase TF Z) ⁻¹ᵁ U.1) (hk : ⊤ ≤ (z ≫ inc₀ TF.X Z) ⁻¹ᵁ TF.X.F.U k) (hx : (z ≫ inc₀ TF.X Z) ≫ TF.X.π = z ≫ toBase TF Z), ∃ C : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) S, ∀ (σ : E →+* ℂ) (i : Fin (Dw.mult σ)), IsCombAtG TF.Y.t (z ≫ toBase TF Z) (fun j => spMap (dualMap (ev (z ≫ toBase TF Z) U.1 hU)) ≫ v (e ⟨σ, j⟩)) (C σ i) (tv (TF.X.F.vecAt k (z ≫ inc₀ TF.X Z) hk hx σ i)).left := by
  intro E _ _ _ H Dw l Xo c TF Z U n e v hv k S _ z hU hk hx
  exact frameVector_isCombination_tangentBasis_flagCover_point TF.X U e v hv.1 hv.2.1 hv.2.2 k S (z ≫ inc₀ TF.X Z) (z ≫ toBase TF Z) hU hk hx

end GlobalTheory.LogPole
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FubiniStudyCoordinateCombinationsNoCommonZero
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.TrueGeo

namespace GlobalTheory.FubiniStudyFrame

theorem exists_ne_zero_of_rel {K V : Type} [Field K] [AddCommGroup V] [Module K V] {n N : ℕ}
    (σ : K →+* ℂ) (u : Fin n → V) (b : Module.Basis (Fin N) K V) (c : Matrix (Fin n) (Fin N) K)
    (A : Matrix (Fin N) (Fin N) ℂ) (w : Fin n → ℂ) (hw : w ≠ 0)
    (hrel : ∀ lam : Fin n → K, ∑ k, lam k • u k = 0 → ∑ k, σ (lam k) * w k = 0)
    (hb : ∀ j, b j = ∑ k, c k j • u k) (hA : A.det ≠ 0) :
    ∃ a, ∑ k, (c.map σ * A) k a * w k ≠ 0 := by
  classical
  have hx : Matrix.vecMul w (c.map σ) ≠ 0 := by
    intro hx
    apply hw
    funext l
    set r := b.repr (u l)
    have hl : ∑ k, ((Pi.single l (1 : K) : Fin n → K) k - ∑ j, c k j * r j) • u k = 0 := by
      have e : ∑ k, (∑ j, c k j * r j) • u k = u l := by
        calc ∑ k, (∑ j, c k j * r j) • u k = ∑ j, r j • ∑ k, c k j • u k := by
              simp only [Finset.sum_smul, Finset.smul_sum, smul_smul]
              rw [Finset.sum_comm]
              exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [mul_comm]
          _ = ∑ j, r j • b j := by simp only [hb]
          _ = u l := b.sum_repr (u l)
      simp only [sub_smul, Finset.sum_sub_distrib, e, Pi.single_apply, ite_smul, one_smul,
        zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true, sub_self]
    have h2 := hrel _ hl
    have h3 : ∀ j, ∑ k, w k * σ (c k j) = 0 := fun j => by
      have := congrFun hx j
      simpa [Matrix.vecMul, dotProduct] using this
    have h4 : ∑ k, σ ((Pi.single l (1 : K) : Fin n → K) k - ∑ j, c k j * r j) * w k =
        w l - ∑ j, σ (r j) * ∑ k, w k * σ (c k j) := by
      simp only [map_sub, map_sum, map_mul, sub_mul, Finset.sum_sub_distrib, Finset.mul_sum,
        Finset.sum_mul]
      congr 1
      · rw [Finset.sum_eq_single l]
        · simp
        · intro k _ hk; simp [Pi.single_apply, hk]
        · simp
      · rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    rw [h4] at h2
    simpa [h3] using h2
  by_contra hne
  push_neg at hne
  have h0 : Matrix.vecMul (Matrix.vecMul w (c.map σ)) A = 0 := by
    rw [Matrix.vecMul_vecMul]
    funext a
    have := hne a
    simp only [Matrix.vecMul, dotProduct, Pi.zero_apply]
    rw [← this]
    exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  exact hA (Matrix.exists_vecMul_eq_zero_iff.1 ⟨_, hx, h0⟩)

theorem rel_field_of_rel_int {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {n : ℕ} (τ : 𝓞 K →+* ℂ) (u : Fin n → V)
    (w : Fin n → ℂ)
    (H : ∀ lam : Fin n → 𝓞 K, ∑ k, lam k • u k = 0 → ∑ k, τ (lam k) * w k = 0)
    (lam : Fin n → K) (h : ∑ k, lam k • u k = 0) :
    ∑ k, OfLattice.extEmb τ (lam k) * w k = 0 := by
  classical
  set σ := OfLattice.extEmb τ
  obtain ⟨⟨d, hd⟩, hint⟩ := IsLocalization.exist_integer_multiples_of_finset
    (nonZeroDivisors (𝓞 K)) (Finset.univ.image lam)
  have hk : ∀ k, IsLocalization.IsInteger (𝓞 K) (d • lam k) := fun k =>
    hint _ (Finset.mem_image_of_mem _ (Finset.mem_univ k))
  choose lam' hlam' using hk
  have hσ : ∀ x : 𝓞 K, σ (algebraMap (𝓞 K) K x) = τ x := fun x =>
    RingHom.congr_fun (OfLattice.extEmb_comp τ) x
  have h1 : ∑ k, lam' k • u k = 0 := by
    have : ∀ k, lam' k • u k = d • (lam k • u k) := fun k => by
      rw [← algebraMap_smul K (lam' k) (u k), hlam' k, Algebra.smul_def, mul_smul,
        algebraMap_smul]
    simp only [this, ← Finset.smul_sum, h, smul_zero]
  have h2 := H lam' h1
  have h3 : ∀ k, τ (lam' k) = σ (algebraMap (𝓞 K) K d) * σ (lam k) := fun k => by
    rw [← hσ, hlam' k, Algebra.smul_def, map_mul]
  simp only [h3, mul_assoc, ← Finset.mul_sum] at h2
  have hd0 : σ (algebraMap (𝓞 K) K d) ≠ 0 := by
    rw [map_ne_zero, ne_eq, ← map_zero (algebraMap (𝓞 K) K),
      (IsFractionRing.injective (𝓞 K) K).eq_iff]
    exact nonZeroDivisors.ne_zero hd
  exact (mul_eq_zero.1 h2).resolve_left hd0

end GlobalTheory.FubiniStudyFrame

open GlobalTheory.FubiniStudyFrame in

theorem GlobalTheory.FubiniStudyFrame.noCommonZero_comb : ∀ (K V : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (m N : ℕ) (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp (𝓞 K)) (g : X ⟶ PSpace (𝓞 K) m) (u : Fin (m + 1) → V) (b : Module.Basis (Fin N) K V) (c : Matrix (Fin (m + 1)) (Fin N) K) (A : (K →+* ℂ) → Matrix (Fin N) (Fin N) ℂ),
    g ≫ PSpace.str (𝓞 K) m = p →
    (∀ lam : Fin (m + 1) → 𝓞 K, ∑ k, lam k • u k = 0 → ∑ k, algX p ⊤ (lam k) • GlobalTheory.Cartier.secPull (ProjSpace.coord (𝓞 K) m k) g = 0) →
    (∀ j, b j = ∑ k, c k j • u k) → (∀ σ, (A σ).det ≠ 0) →
    ∀ τ : 𝓞 K →+* ℂ, Weight.NoCommonZero fun a => ∑ k, (c.map (OfLattice.extEmb τ) * A (OfLattice.extEmb τ)) k a • secVal p τ (GlobalTheory.Cartier.secPull (ProjSpace.coord (𝓞 K) m k) g) := by
  intro K V _ _ _ _ _ _ m N X _ p g u b c A _hg hrel hb hA τ i y hy
  classical
  set s := fun k => GlobalTheory.Cartier.secPull (ProjSpace.coord (𝓞 K) m k) g with hs
  set w : Fin (m + 1) → ℂ := fun k => secVal p τ (s k) i y with hw_def
  have hsup := ProjSpace.iSup_nonzeroLocus_secPull (ProjSpace.iSup_nonzeroLocus_coord (𝓞 K) m) g
  have hw : w ≠ 0 := by
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1
      (show y.1 (IsLocalRing.closedPoint ℂ) ∈ ⨆ k, nonzeroLocus (s k) by rw [hsup]; trivial)
    intro h0
    exact (secVal_ne_zero_iff (s k) hy).2 (mem_ptsIn.2 hk) (congrFun h0 k)
  have H : ∀ lam : Fin (m + 1) → 𝓞 K, ∑ k, lam k • u k = 0 → ∑ k, τ (lam k) * w k = 0 := by
    intro lam h
    have e := congrArg (fun t => secVal p τ t i y) (hrel lam h)
    simpa [map_sum, secVal_smul, Finset.sum_apply, hw_def] using e
  obtain ⟨a, ha⟩ := exists_ne_zero_of_rel (OfLattice.extEmb τ) u b c (A (OfLattice.extEmb τ)) w hw
    (rel_field_of_rel_int τ u w H) hb (hA _)
  refine ⟨a, ?_⟩
  simpa [Finset.sum_apply, hw_def] using ha
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionFieldMapBijectiveOfIsIsoRestrictStatement
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.functionFieldMap_bijective_of_isIso_restrict' : ∀ (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (s : Y ⟶ X) [IsDominant s] (U : X.Opens), (U : Set X).Nonempty → IsIso (s ∣_ U) → Function.Bijective (functionFieldMap s) := by
  first | exact @GlobalTheory.Discrepancy.functionFieldMap_bijective_of_isIso_restrict | exact GlobalTheory.Discrepancy.functionFieldMap_bijective_of_isIso_restrict | (intros; apply GlobalTheory.Discrepancy.functionFieldMap_bijective_of_isIso_restrict <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GalMap
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum

def GalMap {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {I : Ideal R'} {ρ : R →+* R'}
    {D : DegPre R} {D' : DegData R' I} (hD : IsPullDeg ρ D D'.toPre) {A' : PolAV (Sp (FractionRing R'))} {G' : Over (Sp R')}
    [GrpObj G'] [IsCommMonObj G'] (U' : Unif I D' A' G') (σ : Gal ρ) (a : G'.left ⟶ G'.left) : Prop :=
  IsGrpPullback G' G' (spMap (Gal.hom σ)) a ∧
    ∃ (h : IsPullDeg (Gal.hom σ) D'.toPre D'.toPre) (bc : G' ≅ (Over.pullback (specOf (Gal.hom σ))).obj G'),
      bc.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ)) = a ∧ IsPullUnif (Gal.hom σ) h bc U' U' ∧ PullOver hD h

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisQuotientAffineOpenSpecInvariants
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem quot_affine_spec_invariants : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] [Algebra R R'], Base R → FinExt (algebraMap R R') → IsGal (algebraMap R R') → ∀ (G' : Over (Sp R')) (act : Gal (algebraMap R R') → (G'.left ⟶ G'.left)), (∀ σ, act σ ≫ G'.hom = G'.hom ≫ spMap (Gal.hom σ)) → act 1 = 𝟙 _ → (∀ σ τ, act (σ * τ) = act σ ≫ act τ) → ∀ (H : G'.left.Opens) (hH : ∀ σ, act σ ⁻¹ᵁ H = H) (X : Over (Sp R)) (π : H.toScheme ⟶ X.left), π ≫ X.hom = H.ι ≫ G'.hom ≫ spMap (algebraMap R R') → IsAffineHom π → (∀ σ, (act σ).resLE H H (hH σ).ge ≫ π = π) → (∀ x y : H.toScheme, π x = π y → ∃ σ, act σ (H.ι x) = H.ι y) → (∀ V : X.left.Opens, Function.Injective (π.app V).hom ∧ ∀ f : Γ(H.toScheme, π ⁻¹ᵁ V), (∀ σ (h : π ⁻¹ᵁ V ≤ ((act σ).resLE H H (hH σ).ge) ⁻¹ᵁ (π ⁻¹ᵁ V)), (((act σ).resLE H H (hH σ).ge).appLE _ _ h).hom f = f) → f ∈ Set.range (π.app V).hom) → ∀ V : X.left.Opens, IsAffineOpen V → ∃ (C' : Type) (_ : CommRing C') (_ : Algebra R C') (_ : Algebra R' C') (_ : IsScalarTower R R' C') (actC : Gal (algebraMap R R') →* (C' ≃ₐ[R] C')) (C : Subalgebra R C') (j : Sp C' ⟶ H.toScheme) (l : Sp C ⟶ X.left), IsOpenImmersion j ∧ IsOpenImmersion l ∧ Set.range l = (V : Set X.left) ∧ IsPullback j (spMap (algebraMap C C')) π l ∧ j ≫ H.ι ≫ G'.hom = spMap (algebraMap R' C') ∧ l ≫ X.hom = spMap (algebraMap R C) ∧ (∀ σ, spMap (actC σ : C' →+* C') ≫ j ≫ H.ι = j ≫ H.ι ≫ act σ) ∧ (∀ σ r, actC σ (algebraMap R' C' r) = algebraMap R' C' (σ.1 r)) ∧ ∀ x, x ∈ C ↔ ∀ σ, actC σ x = x := by
  intro R _ _ _ R' _ _ _ _ _ _ _ G' act hact h1 hmul H hH X π hπ hAff hinv _ hsec V hV
  haveI := hAff
  have hU : IsAffineOpen (π ⁻¹ᵁ V) := hV.preimage π
  let r : Gal (algebraMap R R') → (H.toScheme ⟶ H.toScheme) := fun σ => (act σ).resLE H H (hH σ).ge
  have hrπ : ∀ σ, r σ ≫ π = π := hinv
  have hr : ∀ σ, π ⁻¹ᵁ V ≤ (r σ) ⁻¹ᵁ (π ⁻¹ᵁ V) := fun σ x hx => by
    show x ∈ (r σ ≫ π) ⁻¹ᵁ V
    rw [hrπ σ]; exact hx
  have hrι : ∀ σ, r σ ≫ H.ι = H.ι ≫ act σ := fun σ => Scheme.Hom.resLE_comp_ι _ _
  let a : Gal (algebraMap R R') → (Γ(H.toScheme, π ⁻¹ᵁ V) ⟶ Γ(H.toScheme, π ⁻¹ᵁ V)) :=
    fun σ => (r σ).appLE (π ⁻¹ᵁ V) (π ⁻¹ᵁ V) (hr σ)
  have key0 : ∀ σ, Spec.map (a σ) ≫ hU.fromSpec = hU.fromSpec ≫ r σ := fun σ =>
    IsAffineOpen.SpecMap_appLE_fromSpec (r σ) hU hU (hr σ)
  have key : ∀ σ, Spec.map (a σ) ≫ hU.fromSpec ≫ H.ι = hU.fromSpec ≫ H.ι ≫ act σ := fun σ => by
    rw [← Category.assoc, key0, Category.assoc, hrι]
  have key_assoc : ∀ σ {Z : Scheme.{0}} (g : G'.left ⟶ Z),
      Spec.map (a σ) ≫ hU.fromSpec ≫ H.ι ≫ g = hU.fromSpec ≫ H.ι ≫ act σ ≫ g := fun σ Z g => by
    simpa only [Category.assoc] using congrArg (· ≫ g) (key σ)
  have a_one : a 1 = 𝟙 _ := by
    rw [← Spec.map_inj, ← cancel_mono (hU.fromSpec ≫ H.ι), key, h1, Spec.map_id]
    simp
  have a_mul : ∀ σ τ, a (σ * τ) = a τ ≫ a σ := fun σ τ => by
    rw [← Spec.map_inj, ← cancel_mono (hU.fromSpec ≫ H.ι), key, hmul, Spec.map_comp]
    simp only [Category.assoc, key, key_assoc]
  have a_one' : ∀ x, (a 1).hom x = x := fun x => by rw [a_one]; rfl
  have a_mul' : ∀ σ τ x, (a (σ * τ)).hom x = (a σ).hom ((a τ).hom x) := fun σ τ x => by
    rw [a_mul]; rfl
  obtain ⟨φ', hφ'⟩ : ∃ φ' : CommRingCat.of R' ⟶ Γ(H.toScheme, π ⁻¹ᵁ V),
      Spec.map φ' = hU.fromSpec ≫ H.ι ≫ G'.hom := ⟨Spec.preimage _, Spec.map_preimage _⟩
  have semi : ∀ σ, φ' ≫ a σ = CommRingCat.ofHom (Gal.hom σ) ≫ φ' := fun σ => by
    rw [← Spec.map_inj, Spec.map_comp, Spec.map_comp, hφ', key_assoc, hact]
    simp only [Category.assoc]
  have semi' : ∀ σ y, (a σ).hom (φ'.hom y) = φ'.hom (σ.1 y) := fun σ y =>
    congrArg (fun f => f.hom y) (semi σ)
  letI alg' : Algebra R' Γ(H.toScheme, π ⁻¹ᵁ V) := φ'.hom.toAlgebra
  letI algR : Algebra R Γ(H.toScheme, π ⁻¹ᵁ V) := (φ'.hom.comp (algebraMap R R')).toAlgebra
  haveI tow : IsScalarTower R R' Γ(H.toScheme, π ⁻¹ᵁ V) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have fixR : ∀ σ r, (a σ).hom (algebraMap R Γ(H.toScheme, π ⁻¹ᵁ V) r) = algebraMap R Γ(H.toScheme, π ⁻¹ᵁ V) r :=
    fun σ r => by
      show (a σ).hom (φ'.hom (algebraMap R R' r)) = φ'.hom (algebraMap R R' r)
      rw [semi' σ]
      exact congrArg φ'.hom ((show ∀ r, σ.1 (algebraMap R R' r) = algebraMap R R' r from σ.2) r)
  let ah : Gal (algebraMap R R') → (Γ(H.toScheme, π ⁻¹ᵁ V) →ₐ[R] Γ(H.toScheme, π ⁻¹ᵁ V)) :=
    fun σ => { (a σ).hom with commutes' := fixR σ }
  have inv1 : ∀ σ x, (a σ).hom ((a σ⁻¹).hom x) = x := fun σ x => by
    rw [← a_mul', mul_inv_cancel, a_one']
  have inv2 : ∀ σ x, (a σ⁻¹).hom ((a σ).hom x) = x := fun σ x => by
    rw [← a_mul', inv_mul_cancel, a_one']
  let actE : Gal (algebraMap R R') → (Γ(H.toScheme, π ⁻¹ᵁ V) ≃ₐ[R] Γ(H.toScheme, π ⁻¹ᵁ V)) := fun σ =>
    AlgEquiv.ofAlgHom (ah σ) (ah σ⁻¹) (AlgHom.ext fun x => inv1 σ x) (AlgHom.ext fun x => inv2 σ x)
  let actC : Gal (algebraMap R R') →* (Γ(H.toScheme, π ⁻¹ᵁ V) ≃ₐ[R] Γ(H.toScheme, π ⁻¹ᵁ V)) :=
    { toFun := actE
      map_one' := AlgEquiv.ext fun x => a_one' x
      map_mul' := fun σ τ => AlgEquiv.ext fun x => a_mul' σ τ x }
  have actC_apply : ∀ σ x, actC σ x = (a σ).hom x := fun _ _ => rfl
  let C : Subalgebra R Γ(H.toScheme, π ⁻¹ᵁ V) :=
    ⨅ σ, AlgHom.equalizer (actC σ : Γ(H.toScheme, π ⁻¹ᵁ V) →ₐ[R] Γ(H.toScheme, π ⁻¹ᵁ V)) (AlgHom.id R _)
  have memC : ∀ x, x ∈ C ↔ ∀ σ, actC σ x = x := fun x =>
    Algebra.mem_iInf.trans (forall_congr' fun σ => Iff.rfl)
  have happ : Spec.map (π.app V) ≫ hV.fromSpec = hU.fromSpec ≫ π := by
    rw [Scheme.Hom.app_eq_appLE]; exact IsAffineOpen.SpecMap_appLE_fromSpec π hV hU le_rfl
  have hmem : ∀ g, (π.app V).hom g ∈ C := by
    intro g; rw [memC]; intro σ
    have e : π.app V ≫ a σ = π.app V := by
      rw [← Spec.map_inj, ← cancel_mono hV.fromSpec, Spec.map_comp]
      simp only [Category.assoc]
      rw [happ, ← Category.assoc, key0, Category.assoc, hrπ]
    exact congrArg (fun f => f.hom g) e
  let ψ : Γ(X.left, V) →+* C := (π.app V).hom.codRestrict C hmem
  have hbij : Function.Bijective ψ := by
    refine ⟨fun x y h => (hsec V).1 (congrArg Subtype.val h), fun ⟨y, hy⟩ => ?_⟩
    obtain ⟨x, hx⟩ := (hsec V).2 y (fun σ _ => (memC y).1 hy σ)
    exact ⟨x, Subtype.ext hx⟩
  let eψ := RingEquiv.ofBijective ψ hbij
  let l : Sp C ⟶ X.left := Spec.map eψ.toCommRingCatIso.hom ≫ hV.fromSpec
  have hlr : l.opensRange = V := by
    rw [Scheme.Hom.opensRange_comp_of_isIso, IsAffineOpen.opensRange_fromSpec]
  have sq : hU.fromSpec ≫ π = spMap (algebraMap C Γ(H.toScheme, π ⁻¹ᵁ V)) ≫ l := by
    rw [← happ]
    show _ = _ ≫ Spec.map eψ.toCommRingCatIso.hom ≫ hV.fromSpec
    rw [← Category.assoc, ← Spec.map_comp]
    rfl
  have hj : hU.fromSpec ≫ H.ι ≫ G'.hom = spMap (algebraMap R' Γ(H.toScheme, π ⁻¹ᵁ V)) := by
    rw [← hφ']; rfl
  have hl : l ≫ X.hom = spMap (algebraMap R C) := by
    obtain ⟨m, hm⟩ : ∃ m : CommRingCat.of R ⟶ CommRingCat.of C, Spec.map m = l ≫ X.hom :=
      ⟨Spec.preimage _, Spec.map_preimage _⟩
    rw [← hm]
    have e : m ≫ CommRingCat.ofHom (algebraMap C Γ(H.toScheme, π ⁻¹ᵁ V)) =
        CommRingCat.ofHom (algebraMap R Γ(H.toScheme, π ⁻¹ᵁ V)) := by
      rw [← Spec.map_inj, Spec.map_comp, hm, ← Category.assoc, ← sq, Category.assoc, hπ]
      have h2 := congrArg (· ≫ spMap (algebraMap R R')) hj
      simp only [Category.assoc] at h2
      rw [h2, ← Spec.map_comp]
      rfl
    congr 1
    ext r
    exact congrArg (fun f => f.hom r) e
  refine ⟨Γ(H.toScheme, π ⁻¹ᵁ V), inferInstance, algR, alg', tow, actC, C, hU.fromSpec, l, inferInstance,
    inferInstance, ?_, ?_, hj, hl, ?_, ?_, memC⟩
  · exact congrArg (fun U : X.left.Opens => (U : Set X.left)) hlr
  · refine (IsOpenImmersion.isPullback _ _ _ _ sq ?_).flip
    rw [hlr, IsAffineOpen.opensRange_fromSpec]
  · intro σ
    exact key σ
  · intro σ y
    exact semi' σ y

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlobalUnitTripleFibreProductInvariantSetGroupCooStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open GlobalTheory.LBDescent GlobalTheory.DescNorm
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.globalUnit_tripleFibreProduct_invariant_setGroupCoordZero : ∀ (K : Type) [Field K] (A A' B : Over (Sp K)) [GrpObj B] (q : A ⟶ A'), IsAbelianScheme B → ∀ (D : Γ(Triple (q ▷ B).left, ⊤)ˣ) (w : Triple (q ▷ B).left), gm (rhoW q) w ⊤ D = gm (𝟙 _) w ⊤ D := by
  first | exact @GlobalTheory.DescNorm.RigidW.gm_rhoW_eq_gm_id_of_abelian | exact GlobalTheory.DescNorm.RigidW.gm_rhoW_eq_gm_id_of_abelian | (intros; apply GlobalTheory.DescNorm.RigidW.gm_rhoW_eq_gm_id_of_abelian <;> assumption)
end

