import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.SameObj
import Development.AbelianVarietyTheory.Statements.ThetaLevelCharacters.MemThetaLevelCharDimZero
import Development.AbelianVarietyTheory.Definitions.KeyFormula.LevBasis
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.KeyFormulaPowOfKeyFormula
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0037
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0024
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0038
import Development.AbelianVarietyTheory.Definitions.KeyFormula.Bundle0001
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.ExistsIsAddFundamentalDomain
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.ExistsUniqueEqConstMulOriginSec
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsStandardSmoothOfRelativeDimensionAwayJacobian
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0007
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0002
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0003
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0019
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.IsLocalModelOfIntegral
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsUnitThetaKeyRuleSmoothBase
import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRootOfKeyFormula
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsKeyPBPair
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0039
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0028
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0030
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRuleOneOfKeyFormula
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0017
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0016

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.DetNeZeroOfNormalAt
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyKa
open GlobalTheory.KeyEq

noncomputable section
namespace GlobalTheory.KeyEq

theorem det_ne_zero_of_normalAt (hU : ThetaUnifAV) (x : KeyIn ℂ) {τ M : Matrix (Fin x.P.g) (Fin x.P.g) ℂ}
    {a b : Fin x.P.g → ℂ} {c : ℂ} (h : NormalAt x τ M a b c) : M.det ≠ 0 := by
  obtain ⟨u, -, -, -, -, -, h₆⟩ := h
  obtain ⟨u₀, -, -, -, -, -, -, hd, -⟩ := hU x.P x.rig x.rig_gen
  have := x.P.isAb.comm
  obtain ⟨hex, htan, -⟩ := LieComb.lieComb_algebra ℂ x.P.A x.P.g x.v x.basis.1
  intro h0
  obtain ⟨d, hd0, hdM⟩ := Matrix.exists_vecMul_eq_zero_iff.2 h0
  have key : ∀ (e : Fin x.P.g → ℂ) (w), Matrix.vecMul e M = 0 → IsLieComb e x.v w → u₀.IsDiff 0 w := by
    intro e w he hw
    have h1 := UnifDifferential.isDiff_of_isLieComb _ _ _ _ u _ x.v e w x.basis.1 h₆ hw
    have e1 : ∑ j, e j • (2 * Real.pi * Complex.I : ℂ)⁻¹ • M j =
        (2 * Real.pi * Complex.I : ℂ)⁻¹ • Matrix.vecMul e M := by
      rw [Matrix.vecMul_eq_sum, Finset.smul_sum]
      exact Finset.sum_congr rfl fun j _ => smul_comm _ _ _
    rw [e1, he, smul_zero] at h1
    intro U hU' f
    rw [h1 U hU' f, map_zero, map_zero]
  obtain ⟨w, hw⟩ := (hex d).exists
  obtain ⟨w', hw'⟩ := (hex 0).exists
  have hww : w = w' := (hd 0).unique ⟨htan _ _ hw, key _ _ hdM hw⟩
    ⟨htan _ _ hw', key _ _ (Matrix.zero_vecMul M) hw'⟩
  subst hww
  exact hd0 ((x.basis.2 w (htan _ _ hw)).unique hw hw')

end GlobalTheory.KeyEq
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsKeyDataBaseChangeSectionsMatricesStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_keyData_baseChange_sections_matrices : Out.Laws → ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] (R' : Type) [CommRing R'] (f : O →+* R') (x : KeyIn O) (n l : ℕ) (s : Fin x.P.g → RR x n) (b : ∀ j, Fin ((l - j * n) ^ x.P.g) → RR x (l - j * n)) (m), x.P.g * n < l → (∀ j ≤ x.P.g, IsBasis x (b j)) → IsMul x l s b m → ∃ (x' : KeyIn R') (φ : x'.P.A.left ⟶ x.P.A.left) (w : LB.Iso x'.P.L (x.P.L.pull φ)) (hg : x'.P.g = x.P.g) (s' : Fin x'.P.g → RR x' n) (b' : ∀ j, Fin ((l - j * n) ^ x'.P.g) → RR x' (l - j * n)) (m' : _), KeyVia x' x f φ w ∧ (∀ i, SecVia x' x φ w (s' i) (s (i.cast hg))) ∧ (∀ j k, SecVia x' x φ w (b' j k) (b j (k.cast (congrArg (fun r => (l - j * n) ^ r) hg)))) ∧ (∀ j ≤ x'.P.g, IsBasis x' (b' j)) ∧ IsMul x' l s' b' m' ∧ (∀ i j j' k k', m' i j j' k k' = f (m (i.cast hg) j j' (k.cast (congrArg (fun r => (l - j * n) ^ r) hg)) (k'.cast (congrArg (fun r => (l - j' * n) ^ r) hg)))) ∧ (Finite (Sp R') → FinZ x s → FinZ x' s') := by
  first | exact @GlobalTheory.KeyBaseChangeData.exists_baseChange_data | exact GlobalTheory.KeyBaseChangeData.exists_baseChange_data | (intros; apply GlobalTheory.KeyBaseChangeData.exists_baseChange_data <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsKeyInIsoElliptic
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.KeyPow

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.WeierstrassCurve

theorem exists_mem_coordOpen_two {R : Type} [CommRing R] (W : WeierstrassCurve R) (s : Sp R) :
    ∃ x : scheme W, toSpec W x = s ∧ x ∈ coordOpen W 2 := by
  have : Module.Finite (Polynomial R) W.toAffine.CoordinateRing :=
    .of_basis (WeierstrassCurve.Affine.CoordinateRing.basis W.toAffine)
  have : FaithfulSMul (Polynomial R) W.toAffine.CoordinateRing :=
    ⟨fun {p q} h => by
      have e := congrArg (fun a => (WeierstrassCurve.Affine.CoordinateRing.basis W.toAffine).repr a 0)
        (h (WeierstrassCurve.Affine.CoordinateRing.basis W.toAffine 0))
      simp only [map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul] at e
      exact (mul_one p).symm.trans (e.trans (mul_one q))⟩
  obtain ⟨y, hy⟩ := Algebra.IsIntegral.comap_surjective (Polynomial R) W.toAffine.CoordinateRing
    (PrimeSpectrum.comap (Polynomial.evalRingHom 0) s)
  refine ⟨chartZ W y, ?_, (opensRange_chartZ W).le ⟨y, rfl⟩⟩
  refine (Scheme.Hom.comp_apply (chartZ W) (toSpec W) y).symm.trans ?_
  rw [chartZ_toSpec]
  change PrimeSpectrum.comap (algebraMap R W.toAffine.CoordinateRing) y = s
  rw [IsScalarTower.algebraMap_eq R (Polynomial R), PrimeSpectrum.comap_comp_apply, hy]
  have e : (Polynomial.evalRingHom (0 : R)).comp (algebraMap R (Polynomial R)) = RingHom.id R := by
    ext; simp
  exact congrArg (fun f => PrimeSpectrum.comap f s) e

theorem exists_keyIn_iso_elliptic (R : Type) [CommRing R] (W : WeierstrassCurve R) [W.IsElliptic] :
    ∃ (x : KeyIn R) (e : x.P.A ≅ schemeOver W), x.P.g = 1 ∧ eSec x.P.A ≫ e.hom.left = zero W ∧
      Out.nonzeroLocus x.th = e.hom.left ⁻¹ᵁ coordOpen W 2 := by
  obtain ⟨G, hc, h0, -⟩ := GlobalTheory.T.exists_commGrpObj_weierstrassScheme R W W.isUnit_Δ
  obtain ⟨hr, hs, ha, hk⟩ := originLB_polarisation R W hc h0
  let P : Out.PolAV (Sp R) :=
    { A := schemeOver W
      isAb := isAbelianScheme_schemeOver R W W.isUnit_Δ hc
      g := 1
      smoothDim := smoothOfRelativeDimension_toSpec W
      L := originLB W
      isLB := originLB_isLB W
      rigid := hr
      sym := hs
      ample := ha
      ktriv := hk }
  obtain ⟨rig, hrig⟩ := P.rigid
  obtain ⟨v, -, hv⟩ := WeierstrassLie.isLieBasis_eps R W h0
  refine ⟨⟨P, le_rfl, rig, hrig, originSec W, fun s => ?_, ![v], hv⟩, Iso.refl _, rfl,
    (Category.comp_id _).trans h0, nonzeroLocus_originSec W⟩
  obtain ⟨x, hx, hx'⟩ := exists_mem_coordOpen_two W s
  exact ⟨x, hx, (nonzeroLocus_originSec W).ge hx'⟩

theorem exists_keyIn_elliptic (R : Type) [CommRing R] [IsLocalRing R] (W : WeierstrassCurve R) [W.IsElliptic] :
    ∃ x : KeyIn R, x.P.g = 1 :=
  let ⟨x, _, h, _⟩ := exists_keyIn_iso_elliptic R W
  ⟨x, h⟩

end GlobalTheory.KeyPow
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsKeyInNormalAt
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa

namespace GlobalTheory.KeyOfPeriod

theorem exists_keyIn_normalAt :
    ThetaUnifAV → GlobalTheory.TorusAlgebraic → ∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ), 1 ≤ g → τ.IsSymm → (τ.map Complex.im).PosDef → charHalf g a b → ∃ (x : KeyIn ℂ) (h : x.P.g = g), NormalAt x (τ.submatrix (Fin.cast h) (Fin.cast h)) 1 (fun i => a (i.cast h)) (fun i => b (i.cast h)) 1 := by
  intro _ H g τ a b hg hs hp hab
  obtain ⟨P, u, th, e, hΛ, ⟨h₁, h₂⟩, hth, -⟩ := H g τ a b hs hp hab.1 hab.2
  subst e
  obtain ⟨rig, hr, hR⟩ := Test.exists_isRig u
  choose v hv using fun i : Fin P.g => (h₂ (Pi.single i (2 * Real.pi * Complex.I)⁻¹)).exists
  have hb := Test.isLieBasis_of_isDiff P u h₁ h₂ (inv_ne_zero Complex.two_pi_I_ne_zero) v
    (fun i => (hv i).1) fun i => (hv i).2
  obtain ⟨z, hz⟩ := Function.ne_iff.1 (TorusAlg.thetaChar_level hs hp hab.1 hab.2).1
  obtain ⟨i, hi⟩ := exists_chart P.isLB ((u.ex z).left (default : PrimeSpectrum ℂ))
  have hi' := (top_le_preimage_iff_mem _ _).2 hi
  have hne : th.f i ≠ 0 := fun h => by
    have := hth i z hi'
    rw [h, valAt'_zero] at this
    exact mul_ne_zero hz (u.fr_ne i z hi') this.symm
  exact ⟨⟨P, hg, rig, hr, th, exists_mem_nonzeroLocus P th ⟨i, hne⟩, v, hb⟩, rfl,
    (normalAt_one_iff _ _ _ _).2 ⟨u, hs, hp, hΛ, hR, hth, fun i => (hv i).2⟩⟩

end GlobalTheory.KeyOfPeriod
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsUnitThetaKeyRuleSmoothBaseStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unit_thetaKeyRule_smooth_base : ThetaUnifAV → Out.PolBaseChangeSt → ∀ N : ℕ → ℕ, KeyRule N 1 charHalf → ∀ (k S : Type) [Field k] [CharZero k] [CommRing S] [IsDomain S] [Algebra k S] [Algebra.Smooth k S] (y : KeyIn S), ∃ κ : Sˣ, ∀ (s : S →+* ℂ) (x : KeyIn ℂ) (t : ℂ), KeyPB x y s → (∃ (τ M : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (a b : Fin x.P.g → ℂ) (c : ℂ), charHalf _ a b ∧ c ≠ 0 ∧ NormalAt x τ M a b c ∧ t = M.det ^ 4 / c ^ 8) → t ^ N y.P.g = s κ := by
  first | exact @GlobalTheory.KeySmoothBase.exists_unit_of_smooth | exact GlobalTheory.KeySmoothBase.exists_unit_of_smooth | (intros; apply GlobalTheory.KeySmoothBase.exists_unit_of_smooth <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.FamHomogOfHomog
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.KeyFamHomog

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.KeyCl

theorem famHomog_of_homog : ∀ (N : ℕ → ℕ) (κ : Rule), Homog N κ → FamHomog N κ := by
  intro N κ hH S _ _ _ P hg rig hr th hth v hv th' hth' v' hv' a M u u' ha hM hu hu'
  obtain ⟨Q, hg₁, rig₁, hr₁, th₁, hth₁, v₁, hv₁, th₁', hth₁', v₁', hv₁', M₁, h₁, h₂, ha₁, hN, hd⟩ :=
    KeyGalDesc.exists_keyPB_pair (algebraMap S (FractionRing S)) P hg rig hr th hth v hv th' hth' v' hv' a M ha hM
  have e := hH _ Q hg₁ rig₁ hr₁ th₁ hth₁ v₁ hv₁ th₁' hth₁' v₁' hv₁' _ M₁ ha₁ hN
  have hgQ : Q.g = P.g := KeyGalDesc.g_eq h₁
  rw [hu _ _ _ h₁, hu' _ _ _ h₂, hd] at e
  have hn : N Q.g = N P.g := congrArg N hgQ
  rw [hn] at e
  apply IsFractionRing.injective S (FractionRing S)
  simpa only [map_mul, map_pow] using e

end GlobalTheory.KeyFamHomog
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.GenericSectionsMeetTransversallyStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_sections_meet_transversally : Out.Laws → ∀ (k K : Type) [Field k] [Field K] [IsAlgClosed K] [Algebra k K] (x : KeyIn k) (x' : KeyIn K) φ w (n : ℕ) (b : Fin (n ^ x.P.g) → RR x n) (b' : Fin (n ^ x.P.g) → RR x' n) (T : Fin x'.P.g × Fin (n ^ x.P.g) → K) (s : Fin x'.P.g → RR x' n), 4 ≤ n → KeyVia x' x (algebraMap k K) φ w → IsBasis x b → (∀ j, SecVia x' x φ w (b' j) (b j)) → AlgebraicIndependent k T → (∀ i, Coords x' b' (fun j => T (i, j)) (s i).f) → ∃ (d : ℕ) (z : Fin d → Pt x') (ch : Fin d → x'.P.L.ι), EtZ x' s z ch := by
  first | exact @GlobalTheory.KeyKa.GenericZeros.exists_etZ_of_algebraicIndependent | exact GlobalTheory.KeyKa.GenericZeros.exists_etZ_of_algebraicIndependent | (intros; apply GlobalTheory.KeyKa.GenericZeros.exists_etZ_of_algebraicIndependent <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IsProjOverDescendsToSubring
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa

namespace GlobalTheory

theorem locallyOfFinitePresentation_pspace_str (R : Type) [CommRing R] (N : ℕ) :
    LocallyOfFinitePresentation (PSpace.str R N) := by
  have hloc : IsZariskiLocalAtSource @LocallyOfFinitePresentation :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @LocallyOfFinitePresentation)
  refine IsZariskiLocalAtSource.of_openCover (ProjSpace.chartCover R N) fun (i : Fin (N + 1)) => ?_
  change LocallyOfFinitePresentation (ProjSpace.chartι R N i ≫ PSpace.str R N)
  rw [ProjSpace.chartι_str]
  change LocallyOfFinitePresentation
    (Spec.map (CommRingCat.ofHom (MvPolynomial.C : R →+* MvPolynomial {j // j ≠ i} R)))
  rw [LocallyOfFinitePresentation.SpecMap_iff, CommRingCat.hom_ofHom, ← MvPolynomial.algebraMap_eq,
    RingHom.finitePresentation_algebraMap]
  infer_instance

theorem isProjOver_descends_to_subring :
    ∀ (S : Type) [CommRing S] (R₀ : Subring S) (X X₀ : Scheme.{0}) (f : X ⟶ Sp S) (f₀ : X₀ ⟶ Sp R₀) (π : X ⟶ X₀) [QuasiCompact f₀] [QuasiSeparated f₀] [LocallyOfFiniteType f₀], IsPullback π f f₀ (spMap R₀.subtype) → IsProjOver f → ∃ F : Finset S, ∀ (R₁ : Subring S) (h : R₀ ≤ R₁), (F : Set S) ⊆ R₁ → ∀ (X₁ : Scheme.{0}) (f₁ : X₁ ⟶ Sp R₁) (π₁ : X₁ ⟶ X₀), IsPullback π₁ f₁ f₀ (spMap (Subring.inclusion h)) → IsProjOver f₁ := by
  intro S _ R₀ X X₀ f f₀ π _ _ _ hX hP
  classical
  have hsub : ∀ {A B : Subring S} (hAB : A ≤ B), B.subtype.comp (Subring.inclusion hAB) = A.subtype :=
    fun _ => RingHom.ext fun _ => rfl
  have hincl : ∀ {A B C : Subring S} (hAB : A ≤ B) (hBC : B ≤ C) (hAC : A ≤ C),
      (Subring.inclusion hBC).comp (Subring.inclusion hAB) = Subring.inclusion hAC :=
    fun _ _ _ => RingHom.ext fun _ => rfl
  have hsp : ∀ {A B : Subring S} (hAB : A ≤ B),
      spMap B.subtype ≫ spMap (Subring.inclusion hAB) = spMap A.subtype := by
    intro A B hAB
    rw [← spMap_comp, hsub]
  have hsp2 : ∀ {A B C : Subring S} (hAB : A ≤ B) (hBC : B ≤ C) (hAC : A ≤ C),
      spMap (Subring.inclusion hBC) ≫ spMap (Subring.inclusion hAB) = spMap (Subring.inclusion hAC) := by
    intro A B C hAB hBC hAC
    rw [← spMap_comp, hincl]
  obtain ⟨L, -, M, s, hv⟩ := (ProjSpace.isProjBy_iff_isProjOver f).2 hP
  obtain ⟨hs, hci⟩ := (ProjSpace.veryAmpleBy_iff f s).1 hv
  set i := ProjSpace.toProj f s hs with hi
  have hif : i ≫ PSpace.str S M = f := ProjSpace.toProj_str f s hs
  have : LocallyOfFinitePresentation (PSpace.str R₀ M) := locallyOfFinitePresentation_pspace_str R₀ M
  have hφ : (i ≫ ProjSpace.baseChange M R₀.subtype) ≫ PSpace.str R₀ M = π ≫ f₀ := by
    rw [Category.assoc, ProjSpace.baseChange_str, ← Category.assoc, hif, hX.w]
  obtain ⟨F₁, hF₁⟩ := morphism_descends_to_subring S R₀ X X₀ (PSpace R₀ M) f f₀ (PSpace.str R₀ M) π
    (i ≫ ProjSpace.baseChange M R₀.subtype) hX hφ
  set R₀' : Subring S := R₀ ⊔ Subring.closure (F₁ : Set S) with hR₀'
  have h₀ : R₀ ≤ R₀' := le_sup_left
  have hF₁' : (F₁ : Set S) ⊆ R₀' := fun x hx =>
    (le_sup_right : Subring.closure (F₁ : Set S) ≤ R₀') (Subring.subset_closure hx)
  obtain ⟨X₀', π₀', f₀', hX₀'⟩ : ∃ (X₀' : Scheme.{0}) (π₀' : X₀' ⟶ X₀) (f₀' : X₀' ⟶ Sp R₀'),
      IsPullback π₀' f₀' f₀ (spMap (Subring.inclusion h₀)) :=
    ⟨_, _, _, IsPullback.of_hasPullback _ _⟩
  obtain ⟨j, hjπ, hjf⟩ : ∃ j : X ⟶ X₀', j ≫ π₀' = π ∧ j ≫ f₀' = f ≫ spMap R₀'.subtype :=
    ⟨hX₀'.lift π (f ≫ spMap R₀'.subtype) (by rw [Category.assoc, hsp h₀, hX.w]),
      hX₀'.lift_fst _ _ _, hX₀'.lift_snd _ _ _⟩
  obtain ⟨ψ, hjψ, hψq⟩ := hF₁ R₀' h₀ hF₁' X₀' f₀' π₀' j hX₀' hjπ hjf
  have hbc₀ := ProjSpace.isPullback_baseChange M (Subring.inclusion h₀)
  obtain ⟨g₀, hg₀b, hg₀q⟩ : ∃ g₀ : X₀' ⟶ PSpace R₀' M,
      g₀ ≫ ProjSpace.baseChange M (Subring.inclusion h₀) = ψ ∧ g₀ ≫ PSpace.str R₀' M = f₀' :=
    ⟨hbc₀.lift ψ f₀' (by rw [hψq, hX₀'.w]), hbc₀.lift_fst _ _ _, hbc₀.lift_snd _ _ _⟩
  have : IsProper (PSpace.str R₀' M) := isProper_str R₀' M
  have : QuasiCompact f₀' := MorphismProperty.of_isPullback (P := @QuasiCompact) hX₀' inferInstance
  have : QuasiSeparated f₀' := MorphismProperty.of_isPullback (P := @QuasiSeparated) hX₀' inferInstance
  have : LocallyOfFiniteType f₀' :=
    MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) hX₀' inferInstance
  have : LocallyOfFiniteType (g₀ ≫ PSpace.str R₀' M) := by rw [hg₀q]; infer_instance
  have : QuasiSeparated (g₀ ≫ PSpace.str R₀' M) := by rw [hg₀q]; infer_instance
  have : QuasiCompact (g₀ ≫ PSpace.str R₀' M) := by rw [hg₀q]; infer_instance
  have : LocallyOfFiniteType g₀ := locallyOfFiniteType_of_comp g₀ (PSpace.str R₀' M)
  have : QuasiSeparated g₀ := QuasiSeparated.of_comp g₀ (PSpace.str R₀' M)
  have : QuasiCompact g₀ := QuasiCompact.of_comp g₀ (PSpace.str R₀' M)
  have hY := ProjSpace.isPullback_baseChange M R₀'.subtype
  have hbc : ProjSpace.baseChange M R₀'.subtype ≫ ProjSpace.baseChange M (Subring.inclusion h₀) =
      ProjSpace.baseChange M R₀.subtype := by
    rw [← ProjSpace.baseChange_comp, hsub]
  have hleft : IsPullback j f f₀' (spMap R₀'.subtype) := by
    refine IsPullback.of_right ?_ hjf hX₀'
    rw [hjπ, hsp h₀]
    exact hX
  have hsq : IsPullback j i g₀ (ProjSpace.baseChange M R₀'.subtype) := by
    refine IsPullback.of_bot ?_ ?_ hY
    · rw [hif, hg₀q]
      exact hleft
    · apply hbc₀.hom_ext
      · rw [Category.assoc, hg₀b, hjψ, Category.assoc, hbc]
      · rw [Category.assoc, hg₀q, hjf, Category.assoc, ProjSpace.baseChange_str, ← Category.assoc, hif]
  obtain ⟨F₂, hF₂⟩ := GlobalTheory.T.isClosedImmersion_descends_to_subring' S R₀' X₀' (PSpace R₀' M) X (PSpace S M) g₀ (PSpace.str R₀' M)
    i j (ProjSpace.baseChange M R₀'.subtype) (PSpace.str S M) hY hsq hci
  refine ⟨F₁ ∪ F₂, fun R₁ h hF X₁ f₁ π₁ hX₁ => ?_⟩
  have h' : R₀' ≤ R₁ := sup_le h (Subring.closure_le.2 fun x hx =>
    hF (Finset.mem_coe.2 (Finset.mem_union_left _ (Finset.mem_coe.1 hx))))
  have hF₂' : (F₂ : Set S) ⊆ R₁ := fun x hx =>
    hF (Finset.mem_coe.2 (Finset.mem_union_right _ (Finset.mem_coe.1 hx)))
  obtain ⟨πX₁, hπ₁, hf₁⟩ : ∃ πX₁ : X₁ ⟶ X₀',
      πX₁ ≫ π₀' = π₁ ∧ πX₁ ≫ f₀' = f₁ ≫ spMap (Subring.inclusion h') :=
    ⟨hX₀'.lift π₁ (f₁ ≫ spMap (Subring.inclusion h')) (by rw [Category.assoc, hsp2 h₀ h' h, hX₁.w]),
      hX₀'.lift_fst _ _ _, hX₀'.lift_snd _ _ _⟩
  have hleft₁ : IsPullback πX₁ f₁ f₀' (spMap (Subring.inclusion h')) := by
    refine IsPullback.of_right ?_ hf₁ hX₀'
    rw [hπ₁, hsp2 h₀ h' h]
    exact hX₁
  have hY₁ := ProjSpace.isPullback_baseChange M (Subring.inclusion h')
  obtain ⟨g₁, hg₁b, hg₁q⟩ : ∃ g₁ : X₁ ⟶ PSpace R₁ M,
      g₁ ≫ ProjSpace.baseChange M (Subring.inclusion h') = πX₁ ≫ g₀ ∧ g₁ ≫ PSpace.str R₁ M = f₁ :=
    ⟨hY₁.lift (πX₁ ≫ g₀) f₁ (by rw [Category.assoc, hg₀q, hf₁]), hY₁.lift_fst _ _ _,
      hY₁.lift_snd _ _ _⟩
  have hsq₁ : IsPullback πX₁ g₁ g₀ (ProjSpace.baseChange M (Subring.inclusion h')) := by
    refine IsPullback.of_bot ?_ hg₁b.symm hY₁
    rw [hg₁q, hg₀q]
    exact hleft₁
  have := hF₂ R₁ h' hF₂' X₁ (PSpace R₁ M) g₁ πX₁ (ProjSpace.baseChange M (Subring.inclusion h'))
    (PSpace.str R₁ M) hY₁ hsq₁
  rw [← hg₁q]
  exact ProjSpace.isProjOver_comp_of_isClosedImmersion g₁ (ProjSpace.isProjOver_pspace_str R₁ M)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IsValueOfGeneric
section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.KeyCl GlobalTheory.KeyPow GlobalTheory.KeySmoothBase

noncomputable section
namespace GlobalTheory.KeySpec

theorem valueAt_of_point {κ : Rule} (hF : Funct κ) {S k : Type} [CommRing S] [Field k] [CharZero k] {y : KeyIn S} {u : S}
    (r : S →+* k) {xk : KeyIn k} (hk : KeyPB xk y r) (h : (κ k xk : k) = r u) : ValueAt κ y u (RingHom.ker r) := by
  intro K _ _ f x hf hx
  haveI := RingHom.ker_isPrime r
  haveI : CharZero (S ⧸ RingHom.ker r) := (RingHom.kerLift r).charZero
  obtain ⟨y', hy⟩ := exists_keyPB_ring y (Ideal.Quotient.mk (RingHom.ker r))
  let F := FractionRing (S ⧸ RingHom.ker r)
  obtain ⟨xF, hxF⟩ := exists_keyPB_ring y' (algebraMap _ F)
  have hr := RingHom.kerLift_injective r
  have er : (RingHom.kerLift r).comp (Ideal.Quotient.mk (RingHom.ker r)) = r :=
    RingHom.ext fun a => RingHom.kerLift_mk r a
  have e : (IsFractionRing.lift (K := F) hr).comp (algebraMap _ F) = RingHom.kerLift r :=
    RingHom.ext fun a => IsFractionRing.lift_algebraMap hr a
  have h1 := hF F k (IsFractionRing.lift hr) xF xk
    (GlobalTheory.KeyCancel.keyPB_cancel _ _ _ y' xF xk _ _ hxF
      (e.symm ▸ GlobalTheory.KeyCancel.keyPB_cancel _ _ _ y y' xk _ _ hy (er.symm ▸ hk)))
  have h2 : (κ F xF : F) = algebraMap _ F (Ideal.Quotient.mk (RingHom.ker r) u) := by
    apply (IsFractionRing.lift (K := F) hr).injective
    rw [← h1, h, IsFractionRing.lift_algebraMap, RingHom.kerLift_mk]
  have hz : ∀ a ∈ RingHom.ker r, f a = 0 := fun a ha => (show a ∈ RingHom.ker f from hf ▸ ha)
  let g := Ideal.Quotient.lift (RingHom.ker r) f hz
  have eg : g.comp (Ideal.Quotient.mk _) = f := RingHom.ext fun a => Ideal.Quotient.lift_mk (RingHom.ker r) f hz
  have hg : RingHom.ker g = ⊥ := by
    refine le_antisymm (fun a ha => ?_) bot_le
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    have : a ∈ RingHom.ker f := ha
    exact Ideal.Quotient.eq_zero_iff_mem.2 (hf ▸ this)
  exact valueAt_bot hF hxF h2 K g x hg (GlobalTheory.KeyCancel.keyPB_cancel _ _ _ y y' x _ _ hy (eg.symm ▸ hx))

theorem isValue_of_generic : ∀ κ : Rule, Funct κ → UnitSp κ → ∀ (S : Type) [CommRing S] [IsDomain S] [IsNoetherianRing S] [CharZero S] (y : KeyIn S) (u : S), (∀ (K : Type) [Field K] [CharZero K] (f : S →+* K) (x : KeyIn K), Function.Injective f → KeyPB x y f → (κ K x : K) = f u) → IsValue κ y u := by
  intro κ hF hU S _ _ _ _ y u h K _ _ f x hx
  have h0 : ValueAt κ y u ⊥ := fun K _ _ f x hf hx => h K f x ((RingHom.injective_iff_ker_eq_bot f).2 hf) hx
  by_cases hp : RingHom.ker f = ⊥
  · exact h0 K f x hp hx
  haveI := RingHom.ker_isPrime f
  obtain ⟨O, _, _, _, _, φ, hφ, hm⟩ :=
    GlobalTheory.exists_complete_discreteValuationRing_of_prime_lt (⊥ : Ideal S) (RingHom.ker f) (bot_lt_iff_ne_bot.2 hp)
  haveI : CharZero O := charZero_of_injective_ringHom ((RingHom.injective_iff_ker_eq_bot φ).2 hφ)
  obtain ⟨yO, hy⟩ := exists_keyPB_ring y φ
  obtain ⟨u', hu'⟩ := exists_unit_dvr hF hU O yO
  have e : φ u = u' := (h0.map_bot φ hφ hy).unique (hu' ⊥)
  have hk : RingHom.ker ((IsLocalRing.residue O).comp φ) = RingHom.ker f := by
    rw [← RingHom.comap_ker, IsLocalRing.ker_residue, hm]
  haveI : CharZero (IsLocalRing.ResidueField O) := charZero_of_inj_zero fun n hn => by
    have : (n : S) ∈ RingHom.ker ((IsLocalRing.residue O).comp φ) := by
      rw [RingHom.mem_ker, map_natCast, hn]
    rw [hk, RingHom.mem_ker, map_natCast] at this
    exact_mod_cast this
  obtain ⟨xk, hxk⟩ := exists_keyPB_ring yO (IsLocalRing.residue O)
  refine valueAt_of_point hF ((IsLocalRing.residue O).comp φ) (GlobalTheory.keyPB_trans _ _ _ y yO xk _ _ hy hxk) ?_ K f x hk.symm hx
  rw [hu' _ _ _ xk rfl hxk, RingHom.comp_apply, e]

end GlobalTheory.KeySpec
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KeyFormulaPowOfKeyRuleCharZero
section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.KeyPow

theorem keyFormulaPow_of_keyRule :
    ThetaUnifAV → ∀ N : ℕ → ℕ, (∀ g, 1 ≤ N g) → GlobalTheory.KeyPow.KeyRule N 1 GlobalTheory.KeyPow.charHalf → GlobalTheory.KeyFormulaPow := by
  rintro hT N hN ⟨κ, hH, hF, hU, hK⟩
  refine ⟨N, hN, κ, fun K _ _ P hg rig hr th hth v hv th' hth' v' hv' a M =>
      hH K P hg rig hr th hth v hv th' hth' v' hv' a M hg,
    fun K K' _ _ _ _ f x x' => hF K K' f x x' x.g_pos,
    fun R K _ _ _ _ _ _ _ x xK => hU R K x xK x.g_pos,
    fun x u τ a b h₁ h₂ ha hb h₃ h₄ h₅ h₆ =>
      hK x τ a b x.g_pos ⟨ha, hb⟩ ((normalAt_one_iff x τ a b).2 ⟨u, h₁, h₂, h₃, h₄, h₅, h₆⟩), ?_⟩
  intro x u Hm W χ θ Fd nth nη h₁ h₂ h₃ h₄ h₅ h₆ h₇
  obtain ⟨u', τ, M, a, b, c, k₁, k₂, ha, hb, k₃, k₄, hc, k₅, hM, k₆, hn⟩ :=
    keyIn_normal_form_and_archimedean_constant hT x u Hm W χ θ Fd nth nη h₁ h₂ h₃ h₄ h₅ h₆ h₇
  have hv := value_at_normalForm N 1 (κ ℂ) x.P.g a b x.g_pos (hH ℂ)
    (fun y h τ' hy => hK y τ' _ _ y.g_pos ⟨fun i => ha _, fun i => hb _⟩ hy) x rfl τ M c hc hM
    ⟨u', k₁, k₂, k₃, k₄, k₅, k₆⟩
  rw [hv, norm_pow, pow_mul nth, pow_mul nη, ← mul_pow, ← mul_pow, hn, ← pow_mul]

theorem keyFormulaPow_of_keyRule_double (hT : ThetaUnifAV) (N : ℕ → ℕ) (hN : ∀ g, 1 ≤ N g)
    (h : KeyRule (fun g => 2 * N (2 * g)) 1 charHalf) : GlobalTheory.KeyFormulaPow :=
  keyFormulaPow_of_keyRule hT _ (fun g => by have := hN (2 * g); omega) h

theorem keyFormulaPow_of_keyRule_charZero :
    ThetaUnifAV → ReciprocityTheory.ChartRestriction.G.Key.Chi.InversionStatement →
      ∀ N : ℕ → ℕ, (∀ g, 1 ≤ N g) → GlobalTheory.KeyPow.KeyRule N 2 GlobalTheory.KeyPow.charZero' → GlobalTheory.KeyFormulaPow :=
  fun hT hI N hN h => keyFormulaPow_of_keyRule_double hT N hN (keyRule_charHalf_of_charZero hI N h)

end GlobalTheory.KeyPow
end

