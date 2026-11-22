import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0228
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3174
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0522
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0554
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTangentPresentationPrime
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0659
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2825
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2820
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3124
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3180
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3164
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0083
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2982
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2978
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3105
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2979
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3023
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3123
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3165
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0075
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2410
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2377
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3134
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0180
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0638
import Development.AbelianVarietyTheory.Definitions.Divisors.OfFactorE
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2821
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3150
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3146
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3132
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3129
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1038
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1387
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2039
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1838
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1960
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3168
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3166
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDivPlace
import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2950
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0799
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3143

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertTwistedLatticeJetsModularFamily
section
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)

namespace GlobalTheory.HilbFam

theorem isFam_hfun_twist : EisExp → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], 2 ≤ Module.finrank ℚ F → ∀ (s N : ℕ) (L : Lat F), 1 ≤ s → 0 < N → HasLevel N L → ∀ (ι : Type) (act : ι → SL(2, ℤ) → ι) (α : ι → Matrix (Fin 2) (Fin 2) (ZMod N)) (Ch : ι → ℍ → ℂ) (κ : Emb F → ℕ), (∀ i γ, α (act i γ) = α i * (γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod N)) → (∀ i (γ : SL(2, ℤ)) (τ : ℍ), Ch i (γ • τ) = (((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * (τ : ℂ) + (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1) : ℂ) ^ 2 * Ch (act i γ) τ - ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℂ) * ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * (τ : ℂ) + (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1) / (2 * Real.pi * Complex.I)) → IsFam act (wt (2 * s) κ : ℕ) (fun i ↦ hfun (2 * s) (twist N L (α i)) κ (Ch i)) := by
  intro hE F _ _ _ hF s N L hs hN hL ι act α Ch κ hα hC
  rw [GlobalTheory.T.isSLTwoPermutedModularFamily_iff_values]
  intro i γ τ
  have htw : twist N L (α (act i γ)) = mulMat (twist N L (α i)) (γ : Matrix (Fin 2) (Fin 2) ℤ) := by
    rw [hα]; exact GlobalTheory.T.hilbertLatticeTwistByMatrixModN_mul_SL2Z F N L (α i) γ hL.2
  have h := GlobalTheory.T.quasiPeriod_normalised_jet_modular_transform hE F hF s N (twist N L (α i)) hs hN (GlobalTheory.T.hilbertLatticeTwist_hasLevel F N L (α i) hL) κ γ (Ch i)
    (Ch (act i γ)) τ ⟨_, GlobalTheory.T.hilbertLatticeTwist_hasLevel F N L (α (act i γ)) hL, htw⟩ (hC i γ τ)
  rw [zpow_natCast]
  beta_reduce
  rw [h, htw]

end GlobalTheory.HilbFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateLocalOfKernelAtPoint
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
open GlobalTheory.FlatModel
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

namespace GlobalTheory.FlatModel

theorem charZero_of_pt {R : Type} [CommRing R] [IsDomain R] (F : IntermediateField ℚ ℂ)
    (f : Sp (FractionRing R) ⟶ Sp F) : CharZero R := by
  letI : Algebra F (FractionRing R) := (Spec.preimage f).hom.toAlgebra
  haveI : CharZero (FractionRing R) := charZero_of_injective_algebraMap (algebraMap F (FractionRing R)).injective
  exact (algebraMap R (FractionRing R)).charZero_iff (IsFractionRing.injective R (FractionRing R)) |>.2 inferInstance

theorem htLocSt_of_hodgeTateKernel (hK : GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel.HodgeTateKernelAtPoint) : HTLocSt := by
  intro E _ _ _ H Dw l' Xo' c' W Y p _ n _ hstar hpW hA R _ _ _ ξ hgen g e he N a 𝔭 h𝔭
  have hp : p.Prime := Fact.out
  obtain ⟨y, hy⟩ := GlobalTheory.T.generic_point_lift_to_field E H Dw l' Xo' c' W Y p hp hpW R ξ hgen
  haveI : IsLocallyNoetherian Y.X := GlobalTheory.T.integral_model_locally_noetherian E H Dw l' Xo' c' W Y p hp hpW
  haveI : CharZero R := charZero_of_pt c'.F (y ≫ pullback.snd _ _)
  have hS : SplitTors Y.t ξ (p ^ n) :=
    GlobalTheory.T.splitTors_of_generic_level E H Dw l' Xo' c' _ _ Y R ξ y hy (p ^ n) (hA ▸ dvd_rfl)
  have hq : p ^ n ≠ 0 := pow_ne_zero _ hp.ne_zero
  have hF := GlobalTheory.HTMap.ex_full hq hS
  choose κ hκ hW using fun m => GlobalTheory.T.integrally_closed_point_extension E H Dw l' Xo' c' W Y p n hstar hpW hA R ξ y hy (a m)
  choose h' hh' using fun m => GlobalTheory.HTMap.ex_dlog hF (hκ m) he.1
  refine ⟨1, fun m k => algebraMap R _ (-(h' m k)), fun h1 => h𝔭.ne_top ((Ideal.eq_top_iff_one _).2 h1), ?_⟩
  intro φ yy P π ψ hPt m tt hlev k x hx
  let x0 : R →+* 𝓞_ℂ_[p] := φ.comp (algebraMap R _)
  obtain ⟨P', hP'⟩ := hF ((IsLocalRing.maximalIdeal 𝓞_ℂ_[p]).comap x0) inferInstance
  obtain ⟨b, hb⟩ := P'.ex_gl (hκ m)
  obtain ⟨c, hc⟩ := GlobalTheory.HTMap.ex_char hP' hb
  have hd := hh' m 𝓞_ℂ_[p] x0 P' b hP' hb c hc
  have htan : ∀ i, IsTanAtG Y.t (spMap x0 ≫ ξ) (spMap (dualMap x0) ≫ e i) := (isTanBasis_bc he x0).1
  have hD : ∀ (k : Fin g) (β : P'.B →+* DualNumber (𝓞_ℂ_[p] ⧸ Ideal.span {(p : 𝓞_ℂ_[p]) ^ n})),
      P'.At ((algebraMap 𝓞_ℂ_[p] (DualNumber (𝓞_ℂ_[p] ⧸ Ideal.span {(p : 𝓞_ℂ_[p]) ^ n}))).comp x0)
        (spMap (dualMap (Ideal.Quotient.mk (Ideal.span {(p : 𝓞_ℂ_[p]) ^ n}))) ≫ spMap (dualMap x0) ≫ e k) β →
      (β b).snd = Ideal.Quotient.mk (Ideal.span {(p : 𝓞_ℂ_[p]) ^ n}) (x0 (h' m k)) := by
    intro k β hβ
    let w := GlobalTheory.HTMap.mkPt (G := Y.t.G) _ (hβ.over.trans (GlobalTheory.HTMap.spc_assoc _ _ _).symm)
    have h2 := hd _ _ (GlobalTheory.HTMap.comb_single htan k) w rfl
    rw [hc _ w β hβ] at h2
    rw [h2]
    simp [Pi.single_apply]
  have key := GlobalTheory.T.tangent_basis_frame_map E H Dw l' Xo' c' W Y p n R ξ g e he P' (κ m) b hb x0 hP' yy P π ψ hPt
    (hK p ℂ_[p] Valued.v 𝓞_ℂ_[p] (𝓞 E) P).1 tt (hW m P' b hb x0 yy P π ψ hPt tt hlev) (fun k => x0 (h' m k)) hD
    k x hx
  have e1 : φ (algebraMap R _ (-(h' m k))) - (P.al₀ tt).1 x = -(x0 (h' m k) + (P.al₀ tt).1 x) := by
    simp only [x0, RingHom.comp_apply, map_neg]; ring
  rw [e1]
  exact neg_mem key

end GlobalTheory.FlatModel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolAtlasIsFormDelDbarSmoothStatement
section
open GlobalTheory GlobalTheory.CxForm GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff ComplexConjugate Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holAtlas_isForm_del_dbar_smooth : ∀ (M : Type) [TopologicalSpace M] (n : ℕ) (A : HolAtlas M n) (α : A.Fld), A.IsForm α →
    A.IsForm (A.del α) ∧ A.IsForm (A.dbar α) := by
  first | exact @GlobalTheory.CxForm.isForm_del_dbar | exact GlobalTheory.CxForm.isForm_del_dbar | (intros; apply GlobalTheory.CxForm.isForm_del_dbar <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolAtlasIsFormPullbackHolomorphicStatement
section
open GlobalTheory GlobalTheory.CxForm GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff ComplexConjugate Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holAtlas_isForm_pullback_holomorphic : ∀ (M M' : Type) [TopologicalSpace M] [TopologicalSpace M'] (n n' : ℕ) (A : HolAtlas M n) (A' : HolAtlas M' n')
    (f : M' → M) (α : A.Fld), A.IsHolo A' f → A.IsForm α → A'.IsForm (A.pullback A' f α) := by
  first | exact @GlobalTheory.PullbackForm.isForm_pullback | exact GlobalTheory.PullbackForm.isForm_pullback | (intros; apply GlobalTheory.PullbackForm.isForm_pullback <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealSheafAlongLocalSpecMonomialOfConeCombinatioStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idealSheafAlongLocalSpec_monomial_of_cone_combination : ∀ {o : Type} [CommRing o] {ζ : o} {g n : ℕ} (F : SFam g n ζ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (φ : InvFun ℤ)
    (J : Z.IdealSheafData) (d : ℕ), ValOn F i φ J d →
    ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (m : ℕ) (ga δ : Fin m → LinearMap.BilinForm ℤ X)
      (M : ℕ), IsCone id φ ga → (∀ k, δ k = (M : ℤ) • ga k) → ∀ b : Fin m → ℕ, (∀ k, (b k : ℝ) = d * φ.evalZ (δ k)) →
    ∀ (T : Trait F) (W : Type) [CommRing W] [IsLocalRing W] (σ : W →+* T.V) (c : Fin m → ℕ) (e' : T.D.toPre.X ≃+ X)
      (x : Sp W ⟶ Z) (s : Fin m → W), Function.Bijective σ → jK T.V ≫ spMap σ ≫ x = T.y ≫ i →
      (∀ k, Associated (σ (s k)) (T.ϖ ^ c k)) → (∀ a b, T.β a b = ∑ k, (c k : ℤ) * δ k (e' a) (e' b)) →
      idlAlong J x = Ideal.span {∏ k, s k ^ b k} := by
  first | exact @GlobalTheory.Poinc.Arith.idlAlong_monomial | exact GlobalTheory.Poinc.Arith.idlAlong_monomial | (intros; apply GlobalTheory.Poinc.Arith.idlAlong_monomial <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealSheafAlongLocalSpecNormalisedBlowupPrincipaStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idealSheafAlongLocalSpec_normalisedBlowup_principal : ∀ {S Z : Scheme.{0}} (π : S ⟶ Z) (J : Z.IdealSheafData), IsNormBl π J → ∀ (R : Type) [CommRing R] [IsLocalRing R]
    (ξ : Sp R ⟶ S), ∃ g₀ : R, idlAlong (J.comap π) ξ = Ideal.span {g₀} := by
  first | exact @GlobalTheory.NormBlPrincipal.idlAlong_comap_principal | exact GlobalTheory.NormBlPrincipal.idlAlong_comap_principal | (intros; apply GlobalTheory.NormBlPrincipal.idlAlong_comap_principal <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentImageNDividedPointGaloisConjEquiv
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.GalFixQ

theorem eImage_equiv_conj : ∀ {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (iw : W →+* R) {I : Type} [Fintype I] (s : I → R) (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (n : ℕ), IsCN R → 1 ≤ n → IsUnit (n : R) → ∀ ζ : R, IsPrimitiveRoot ζ n → ∀ (Q : Data R) (e : Q.X ≃+ (Fin T.r → ℤ)), DataFrom T iw s ε n Q e → TorsRat Q.B n → ∀ (D' : DegData R (maximalIdeal R)) (F : PFactor Q D'.toPre) (A' : PolAV (Sp (FractionRing R))) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'] (U' : Unif (maximalIdeal R) D' A' G') (oA : A'.OAct F.O) (oG : RingAct G' F.O), IsSemiAbelian G' → U'.toUnifPre.OLinear F.O F.o oA oG → ∀ (σ : AlgebraicClosure (FractionRing R) ≃ₐ[FractionRing R] AlgebraicClosure (FractionRing R)) (p₀ p p' : QkPt D'.toPre (AlgebraicClosure (FractionRing R)) n), p.y = F.e • p₀.y → GtPtAct F.o F.e p₀.g p.g → QkExt σ.toAlgHom.toRingHom p p' → QkPt.Equiv D'.toPre (AlgebraicClosure (FractionRing R)) p p' := by
  intro o W _ _ _ T R _ _ _ iw I _ s ε n hCN hn hnu ζ hζ Q e hDF hTR D' F A' G' _ _ U' oA oG hSA hOL σ p₀ p p' hy hg hext
  have hB := D'.tau_bimult
  obtain ⟨b, hb⟩ := GlobalTheory.T.idempotent_image_base_point_rational_fractionField T R iw s ε n hCN hn hnu ζ hζ Q e hDF hTR D' F p₀ p hy hg
  have hc := GlobalTheory.T.divisionPoint_characters_galoisFixed_of_rational_basePoint T R iw s ε n hCN hn hnu ζ hζ Q e hDF hTR D' F σ p₀ p hy hg ⟨b, hb⟩
  have hσ : σ.toAlgHom.toRingHom.comp (algebraMap (FractionRing R) (AlgebraicClosure (FractionRing R))) =
      algebraMap _ _ := σ.toAlgHom.comp_algebraMap
  have hpp : QkExt σ.toAlgHom.toRingHom p p := by
    refine ⟨rfl, ?_, hc⟩
    rw [hb, ← Category.assoc]
    congr 1
    rw [spMap, spMap, ← Spec.map_comp]
    congr 1
    ext x
    exact (RingHom.congr_fun hσ x).symm
  have e1 := (GlobalTheory.TorusExt.qkExt_iff hB _ hσ p p').1 hext
  have e2 := (GlobalTheory.TorusExt.qkExt_iff hB _ hσ p p).1 hpp
  rw [e1, ← e2]
  exact qk_equiv_refl hB p

end GlobalTheory.Mum.GalFixQ
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InductiveHeightFormulaRhsTransportIso
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.MixHt
open GlobalTheory.TrueGeo.SmallSec GlobalTheory.FrameGlue.Pull GlobalTheory.MultPull GlobalTheory.Points

variable {k : Type} [CommRing k]

theorem isEmpty_cxPts_of_map {X Y : Scheme.{0}} {p : X ⟶ Sp k} {q : Y ⟶ Sp k} (g : Y ⟶ X) (hg : g ≫ p = q)
    (h : ∀ σ : k →+* ℂ, IsEmpty (CxPts p σ)) (σ : k →+* ℂ) : IsEmpty (CxPts q σ) :=

  isEmpty_iff.2 fun y => isEmpty_iff.1 (h σ) (PtsOver.map g hg (spMap σ) y)

theorem mixArch_pull_iso {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k)
    (hp : IsAmb p) (hq : IsAmb q) (g : Y ⟶ X) (hg : g ≫ p = q) (hη : g (genericPoint Y) = genericPoint X) [IsIso g]
    (e : ℕ) (hX : topologicalKrullDim X = (e + 1 : ℕ)) (L : Fin e → HermLB p) (M : HermLB p)
    (r : M.B.ι → X.functionFieldˣ) (hr : IsRatSec M.B r) :
    mixArch (fun a => (L a).pull g hg) (M.pull g hg)
      (MultPull.isRatSec_pull_map g (hη ▸ specializes_rfl : g (genericPoint Y) ⤳ genericPoint X) hr) =
      mixArch L M hr := by
  have hY : topologicalKrullDim Y = (e + 1 : ℕ) :=
    (IsHomeomorph.topologicalKrullDim_eq _ (Scheme.homeoOfIso (asIso g)).isHomeomorph).trans hX
  have hg' : inv g ≫ q = p := by rw [← hg, IsIso.inv_hom_id_assoc]
  by_cases hp0 : ∀ σ : k →+* ℂ, IsEmpty (CxPts p σ)
  · rw [(GlobalTheory.T.mixedArch_restricted_eq_zero_of_no_complexPoints k X p hp0 e L M).1 r hr]
    exact (GlobalTheory.T.mixedArch_restricted_eq_zero_of_no_complexPoints k Y q (isEmpty_cxPts_of_map g hg hp0) e _ _).1 _ _
  by_cases hq0 : ∀ σ : k →+* ℂ, IsEmpty (CxPts q σ)
  · exact absurd (isEmpty_cxPts_of_map (inv g) hg' hq0) hp0
  obtain ⟨e₁, he₁, hXa⟩ := (GlobalTheory.T.projArithAmbient_vertical_or_arithmeticVariety k X p hp (e + 1) hX).resolve_left fun ⟨_, _, _, h⟩ => hp0 h
  obtain ⟨e₂, he₂, hYa⟩ := (GlobalTheory.T.projArithAmbient_vertical_or_arithmeticVariety k Y q hq (e + 1) hY).resolve_left fun ⟨_, _, _, h⟩ => hq0 h
  obtain rfl : e₁ = e := by omega
  obtain rfl : e₂ = e₁ := by omega
  unfold mixArch
  congr 2
  funext n
  have h₁ : (comb (fun a => (L a).pull g hg) n).archInt (M.pull g hg) e₂
      (MultPull.isRatSec_pull_map g (hη ▸ specializes_rfl : g (genericPoint Y) ⤳ genericPoint X) hr) =
      ((comb L n).pull g hg).archInt (M.pull g hg) e₂
      (MultPull.isRatSec_pull_map g (hη ▸ specializes_rfl : g (genericPoint Y) ⤳ genericPoint X) hr) := by
    simp only [HermLB.archInt, (isometric_comb_pull L n g hg).chernInt_eq]
  rw [h₁, GlobalTheory.T.archimedeanIntegral_pull_mul_degree k X Y p q e₂ hXa hYa g hg hη (by rw [Published.residueDegree_of_isClosedImmersion]; exact one_ne_zero),
    Published.residueDegree_of_isClosedImmersion, Nat.cast_one, one_mul]

theorem mult_pull_iso {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    {p : X ⟶ Sp k} {q : Y ⟶ Sp k} (g : Y ⟶ X) (hg : g ≫ p = q) (hη : g (genericPoint Y) ⤳ genericPoint X) [IsIso g]
    (M : HermLB p) {r : M.B.ι → X.functionFieldˣ} (hr : IsRatSec M.B r) (y : Y) :
    ((M.pull g hg).div (MultPull.isRatSec_pull_map g hη hr)).mult y = (M.div hr).mult (g y) := by
  change (divOfRatSec (LB.isLB_pull M.isLB g) (MultPull.isRatSec_pull_map g hη hr)).mult y =
    (divOfRatSec M.isLB hr).mult (g y)
  obtain ⟨c, hc⟩ := exists_chart (LB.isLB_pull M.isLB g) y
  have hc' : g y ∈ M.B.U (c PUnit.unit) := Set.mem_iInter.1 hc PUnit.unit
  rw [((presents_divOfRatSec _ _).isEqn c y hc).mult_eq,
    ((presents_divOfRatSec M.isLB hr).isEqn _ _ hc').mult_eq]
  exact ord_fnMap g hη y _

theorem transport : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k), IsAmb p → IsAmb q → ∀ (g : Y ⟶ X) (hg : g ≫ p = q) (hη : g (genericPoint Y) = genericPoint X), IsIso g → ∀ e : ℕ, topologicalKrullDim X = (e + 1 : ℕ) → ∀ (h : X → ℝ) (L : Fin e → HermLB p) (M : HermLB p) (r : M.B.ι → X.functionFieldˣ) (hr : IsRatSec M.B r), recVal (fun w => h (g w)) (fun a => (L a).pull g hg) (M.pull g hg) (MultPull.isRatSec_pull_map g (hη ▸ specializes_rfl : g (genericPoint Y) ⤳ genericPoint X) hr) = recVal h L M hr := by
  intro k _ X Y _ _ _ _ p q hp hq g hg hη _ e hX h L M r hr
  unfold recVal
  rw [mixArch_pull_iso p q hp hq g hg hη e hX L M r hr]
  congr 1
  refine (finsum_congr fun z => ?_).trans
    (finsum_comp_equiv (Scheme.homeoOfIso (asIso g)).toEquiv (f := fun x => ((M.div hr).mult x : ℝ) * h x))
  exact congrArg (fun n : ℤ => (n : ℝ) * h (g z)) (mult_pull_iso g hg _ M hr z)

end GlobalTheory.MixHt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceLatticeStabiliserFixesVacuum
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

namespace GlobalTheory.InertSph

theorem vac_fixed : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    IsTriple B G X om om' →
    ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ k ∈ GlobalTheory.InertSph.KAt σ G.W v, Acts (evFin F v) (om (1, k)) (G.M.vac v) (G.M.vac v) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v w hin hvT k hk
  obtain ⟨hSB, hne, θ, hθ, hfix⟩ := hT.geo.hM.vac v
  obtain ⟨φ₁, hφ₁, hact⟩ := GlobalTheory.T.weilRepresentationLocality_unitaryGroupW_pairVW F E σ B a a' G X om om' hT v k hk.1 _ hSB
  have hfix₁ := GlobalTheory.T.weilOperator_latticeStabiliser_right_preserves_vacuumType F E σ B a a' G X om om' hT v k hk θ hθ _ hSB φ₁ hφ₁ hfix hact
  obtain ⟨c, rfl⟩ := GlobalTheory.T.heisenbergSelfDualLattice_fixedFunctions_line F E σ B a a' G X om om' hT v (hT.base.inert v w hin).2.2
    (GlobalTheory.T.tensorLattice_inertPlace_selfDual F E σ B a a' G X om om' hT v w hin) θ hθ _ hSB hne hfix φ₁ hφ₁ hfix₁
  have hc := GlobalTheory.T.latticeStabilizer_vacuum_eigenvalue_eq_one_inertPlace F E σ B a a' G X om om' hT v w hin hvT k hk c hact
  rw [hc, one_smul] at hact
  exact hact

end GlobalTheory.InertSph
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntDvdOfEqNatMulIntegralAdeleAwayFromPStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.int_dvd_of_eq_nat_mul_integralAdeleAwayFromP : ∀ (p : ℕ) [Fact p.Prime] (n : ℕ), 0 < n → n.Coprime p → ∀ (c : ℤ) (a : AfP p), IsIntAf a → algebraMap ℚ (AfP p) (c : ℚ) = (n : AfP p) * a → (n : ℤ) ∣ c := by
  first | (exact @GlobalTheory.LKGeo.IntDvd.int_dvd_of_eq_mul_isIntAf) | (exact GlobalTheory.LKGeo.IntDvd.int_dvd_of_eq_mul_isIntAf) | (intros; apply GlobalTheory.LKGeo.IntDvd.int_dvd_of_eq_mul_isIntAf <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableLogNormSectionMixedChernFormsStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integrable_logNormSection_mixedChernForms : ∀ (F : Type) [Field F] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp F) (σ : F →+* ℂ) (D : ℕ), IsProjOver p → SmoothOfRelativeDimension D p → ∀ (L : Fin D → MLine p σ) (M : MLine p σ) (s : M.B.Sec), genericPoint X ∈ nonzeroLocus s → Intg L (M.logSec s) := by
  first | exact @GlobalTheory.MixLogSec.intg_logSec | exact GlobalTheory.MixLogSec.intg_logSec | (intros; apply GlobalTheory.MixLogSec.intg_logSec <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedLocusPullbackLineBundlesIsomorphicStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isClosed_locus_pullback_lineBundles_isomorphic : ∀ (Rg : Type) [CommRing Rg] (A B : Over (Sp Rg)) [GrpObj A] [GrpObj B] (L : LB A.left) (M : LB B.left) (eA : LB.Gen (L.pull (eSec A))) (eB : LB.Gen (M.pull (eSec B))) (Z₁ : Scheme.{0}) [IsLocallyNoetherian Z₁] (t₁ : Z₁ ⟶ Sp Rg) (A₁ B₁ : Over Z₁) [GrpObj A₁] [GrpObj B₁] (φA₁ : A₁.left ⟶ A.left) (φB₁ : B₁.left ⟶ B.left) (Φ₁ : A₁ ⟶ B₁), IsAbelianScheme A → IsAbelianScheme B → L.IsLB → M.IsLB → eA.IsGen → eB.IsGen → RelAmple A L → IsGrpPullback A₁ A t₁ φA₁ → IsGrpPullback B₁ B t₁ φB₁ → IsMonHom Φ₁ → ∃ (Z : Scheme.{0}) (i : Z ⟶ Z₁), IsClosedImmersion i ∧ ∀ (T : Scheme.{0}) (u : T ⟶ Z₁) (A' B' : Over T) [GrpObj A'] [GrpObj B'] (ψA : A'.left ⟶ A₁.left) (ψB : B'.left ⟶ B₁.left) (Φ' : A' ⟶ B'), IsGrpPullback A' A₁ u ψA → IsGrpPullback B' B₁ u ψB → Φ'.left ≫ ψB = ψA ≫ Φ₁.left → (LBIso (L.pull (ψA ≫ φA₁)) ((M.pull (ψB ≫ φB₁)).pull Φ'.left) ↔ ∃ w : T ⟶ Z, w ≫ i = u) := by
  first | (exact @GlobalTheory.HomFixTrivLocus.isoLocus_closed) | (exact GlobalTheory.HomFixTrivLocus.isoLocus_closed) | (intros; apply GlobalTheory.HomFixTrivLocus.isoLocus_closed  <;> assumption)
end

