import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1712
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1848
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1853
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1790
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1791
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0533
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOfBalanced
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardLatticeDoubleCosetClassesStabilisers
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0352
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteAdeleBaseChangeEquiv
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0304
import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1833
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0540
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1857
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1829
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0082
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsFormalGroupJetsChart
import Formalism.LocalToGlobal.CharacterGerms.Bundle0046
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1858
import Development.AbelianVarietyTheory.Definitions.Divisors.PointShiftSt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1038
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1387
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1397
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1425
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceLocalFieldDataExists
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1793
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1859
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1738

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFormalPathEqScalingValuationRingPath
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Nef

private theorem top_le_comp_preimage {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) {U : Z.Opens} (h : ⊤ ≤ g ⁻¹ᵁ U) :
    ⊤ ≤ (f ≫ g) ⁻¹ᵁ U := by
  rw [Scheme.Hom.comp_preimage, top_le_iff.1 h, Scheme.Hom.preimage_top]

private theorem top_le_of_comp {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) {U : Z.Opens} (h : ⊤ ≤ (f ≫ g) ⁻¹ᵁ U) :
    ⊤ ≤ f ⁻¹ᵁ (g ⁻¹ᵁ U) := by
  rwa [Scheme.Hom.comp_preimage] at h

private theorem top_le_preimage_inf {X Y : Scheme.{0}} (f : X ⟶ Y) {A B : Y.Opens} (hA : ⊤ ≤ f ⁻¹ᵁ A)
    (hB : ⊤ ≤ f ⁻¹ᵁ B) : ⊤ ≤ f ⁻¹ᵁ (A ⊓ B) :=
  fun y _ => ⟨hA trivial, hB trivial⟩

private theorem evAt_congr {R : Type} [CommRing R] {X : Scheme.{0}} {ξ ξ' : Sp R ⟶ X} (e : ξ = ξ') {U : X.Opens}
    (h : ⊤ ≤ ξ ⁻¹ᵁ U) (h' : ⊤ ≤ ξ' ⁻¹ᵁ U) : evAt ξ h = evAt ξ' h' := by
  subst e; rfl

private def resO {k K E : Type} [Field k] [Field K] [Algebra k K] [Field E] [Algebra k E] [Algebra K E]
    {ρ : Place k E → Place k K} (hρ : IsRes ρ) (p : Place k E) : (ρ p).O →+* p.O :=
  ((algebraMap K E).comp (ρ p).O.subtype).codRestrict p.O fun y =>
    (Valuation.mem_valuationSubring_iff _ _).2 ((hρ p y).2 ((Valuation.mem_valuationSubring_iff _ _).1 y.2))

private def constO {k E : Type} [Field k] [Field E] [Algebra k E] (p : Place k E) : k →+* p.O :=
  (algebraMap k E).codRestrict p.O fun c => by
    rw [Valuation.mem_valuationSubring_iff]
    by_cases hc : c = 0
    · simp [hc]
    · exact (p.2.2 c hc).le

theorem genPath_scaling : ∀ (k K E : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field K] [Algebra k K] [Field E] [Algebra k E] [Algebra K E] [IsScalarTower k K E] [FiniteDimensional K E] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)] (x : Sp K ⟶ C), IsGenOver k x →
  ∀ (G : Over C) [GrpObj G], IsSemiAbelian G → ∀ (W : C.Modules) (r : ℕ) (i : W ⟶ Lie G) (V₀ : C.Opens) (s : Fin r → Γ(W, V₀)) (ρ : Place k E → Place k K), IsRes ρ → ∀ (p : Place k E) (g : Matrix (Fin r) (Fin r) K), LocFrame x s (ρ p) g → ∀ (w : Fin r → E) (u : E), u ≠ 0 → p.1 u = nrm p ((g.map (algebraMap K E)).mulVec w) → ∀ ξ, IsPath G 2 (spMap (algebraMap K E) ≫ x) ξ → HasTan G (spMap (algebraMap K E) ≫ x) ξ (fun j => i.app V₀ (s j)) w → ∃ (b : Sp p.O ⟶ C) (ζ : Sp (PowerSeries p.O) ⟶ G.left), spMap p.O.subtype ≫ b = spMap (algebraMap K E) ≫ x ∧ IsPath G 2 b ζ ∧ ξ = spMap (sc p u) ≫ ζ := by
  intro k K E _ _ _ _ _ _ _ _ _ _ C _ x _ G _ hG W r i V₀ s ρ hρ p g hg w u hu hpu ξ hξ hξt
  have hsm : Smooth G.hom := hG.smooth
  have hqs : QuasiSeparated G.hom := by haveI := hG.separated; infer_instance
  haveI : CharZero E := charZero_of_injective_algebraMap (algebraMap k E).injective
  obtain ⟨b₀, V, t, Vf, h₀, h₁, hxf, M, hb₀, hb₀V, -, hst, rfl⟩ := hg
  set xE := spMap (algebraMap K E) ≫ x with hxE
  let α := resO hρ p
  let φ : p.O →+* E := p.O.subtype
  let b : Sp p.O ⟶ C := spMap α ≫ b₀
  have hbx : spMap φ ≫ b = xE := by
    rw [hxE, ← hb₀]
    simp only [b, ← Category.assoc, spMap, ← Spec.map_comp]
    rfl
  letI : Algebra ℚ p.O := ((constO p).comp (algebraMap ℚ k)).toAlgebra
  have hbV : ⊤ ≤ b ⁻¹ᵁ V := top_le_comp_preimage _ _ hb₀V
  let y : Fin r → E := ((M.map (evAt x hxf)).map (algebraMap K E)).mulVec w
  let eE : Fin r → E := fun j => u⁻¹ * y j
  have heO : ∀ j, eE j ∈ p.O := by
    intro j
    rw [Valuation.mem_valuationSubring_iff]
    have hle : p.1 (y j) ≤ p.1 u := by
      rw [hpu, nrm]; exact Finset.le_sup (f := fun i => p.1 (y i)) (Finset.mem_univ j)
    have hu0 : p.1 u ≠ 0 := (Valuation.ne_zero_iff _).2 hu
    calc p.1 (eE j) = (p.1 u)⁻¹ * p.1 (y j) := by simp only [eE, map_mul, map_inv₀]
      _ ≤ (p.1 u)⁻¹ * p.1 u := by gcongr
      _ = 1 := inv_mul_cancel₀ hu0
  let e : Fin r → p.O := fun j => ⟨eE j, heO j⟩
  obtain ⟨ζ, hζ, hζt⟩ := GlobalTheory.T.exists_formalSquaringPath_with_tangentVector C G p.O hsm hqs b r V (fun j => i.app V (t j)) e hbV
  obtain ⟨U₀, hU₀a, hζU₀, -⟩ := Opens.isBasis_iff_nbhd.1 G.left.isBasis_affineOpens
    (Opens.mem_top (ζ (IsLocalRing.closedPoint (PowerSeries p.O))))
  have hζU : ⊤ ≤ ζ ⁻¹ᵁ U₀ := (GlobalTheory.T.evalSectionAtRingPoint_spMap_comp_restrict_stalk.2.2.2.1 (PowerSeries p.O) G.left ζ U₀).2 hζU₀
  have hξ'U : ⊤ ≤ (spMap (sc p u) ≫ ζ) ⁻¹ᵁ U₀ := top_le_comp_preimage _ _ hζU
  have hξ'path : IsPath G 2 xE (spMap (sc p u) ≫ ζ) := by
    have := (GlobalTheory.T.formalSquaringPaths_baseChange_and_hom.1 C G p.O E φ 2 u b ζ hζ).1
    rw [map_ofNat, hbx] at this
    exact this

  have hxEf : ⊤ ≤ xE ⁻¹ᵁ Vf := top_le_comp_preimage _ _ hxf
  have hxE0 : ⊤ ≤ xE ⁻¹ᵁ V₀ := hxEf.trans (Scheme.Hom.preimage_mono xE h₀)
  have hxEu : ⊤ ≤ xE ⁻¹ᵁ (unitSec G ⁻¹ᵁ U₀) := by
    apply top_le_of_comp
    rw [← hξ'path.zero]; exact top_le_comp_preimage _ _ hξ'U
  have hbu : ⊤ ≤ b ⁻¹ᵁ (unitSec G ⁻¹ᵁ U₀) := by
    apply top_le_of_comp
    rw [← hζ.zero]; exact top_le_comp_preimage _ _ hζU
  have hxs : ⊤ ≤ xE ⁻¹ᵁ (Vf ⊓ unitSec G ⁻¹ᵁ U₀) := top_le_preimage_inf _ hxEf hxEu
  have hb'' : ⊤ ≤ b ⁻¹ᵁ (V ⊓ unitSec G ⁻¹ᵁ U₀) := top_le_preimage_inf _ hbV hbu
  have hxE'' : ⊤ ≤ xE ⁻¹ᵁ (V ⊓ unitSec G ⁻¹ᵁ U₀) := by rw [← hbx]; exact top_le_comp_preimage _ _ hb''
  have hsub : Vf ⊓ unitSec G ⁻¹ᵁ U₀ ≤ V ⊓ unitSec G ⁻¹ᵁ U₀ := inf_le_inf_right _ h₁
  have key : ∀ f : Γ(G.left, U₀), PowerSeries.coeff 1 (evAt (spMap (sc p u) ≫ ζ) hξ'U f) =
      ∑ j, w j * evAt xE hxs (dualApp (i.app V₀ (s j)) (inf_le_left.trans h₀) (dUnit G inf_le_right f)) := by
    intro f
    have h1 := (GlobalTheory.T.formalSquaringPaths_baseChange_and_hom.1 C G p.O E φ 2 u b ζ hζ).2 r V (fun j => i.app V (t j)) e hbV U₀ hζU hζt hξ'U
      (V ⊓ unitSec G ⁻¹ᵁ U₀) inf_le_left inf_le_right hb'' f
    have hD : ∀ τ : Γ(Lie G, V), φ (evAt b hb'' (dualApp τ inf_le_left (dUnit G inf_le_right f))) =
        evAt xE hxs (dualApp τ (hsub.trans inf_le_left) (dUnit G (hsub.trans inf_le_right) f)) := by
      intro τ
      rw [← GlobalTheory.T.evalSectionAtRingPoint_spMap_comp_restrict_stalk.1 p.O E C φ b _ hb'' (top_le_comp_preimage _ _ hb''), evAt_congr hbx _ hxE'',
        ← GlobalTheory.T.evalSectionAtRingPoint_spMap_comp_restrict_stalk.2.2.1 E C xE _ _ hsub hxE'' hxs]
      congr 1
      have := dualApp_resM τ (inf_le_left : V ⊓ unitSec G ⁻¹ᵁ U₀ ≤ V) hsub (dUnit G inf_le_right f)
      rw [resM_dUnit] at this
      exact this.symm
    have hR : ∀ j, evAt xE hxs (dualApp (i.app V₀ (s j)) (inf_le_left.trans h₀) (dUnit G inf_le_right f)) =
        ∑ l, algebraMap K E (evAt x hxf (M l j)) * evAt xE hxs (dualApp (i.app V (t l))
          (hsub.trans inf_le_left) (dUnit G (hsub.trans inf_le_right) f)) := by
      intro j
      have e1 : dualApp (i.app V₀ (s j)) (inf_le_left.trans h₀) =
          dualApp (resM _ h₀ (i.app V₀ (s j))) (inf_le_left : Vf ⊓ unitSec G ⁻¹ᵁ U₀ ≤ Vf) :=
        (dualApp_res _ _ _).symm
      have e2 : resM _ h₀ (i.app V₀ (s j)) = ∑ l, M l j • resM _ h₁ (i.app V (t l)) := by
        rw [← GlobalTheory.Twist.app_resM, hst, map_sum]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [Scheme.Modules.Hom.app_smul, GlobalTheory.Twist.app_resM]
      rw [e1, e2, dualApp_sum, LinearMap.sum_apply, map_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [dualApp_smul, LinearMap.smul_apply, smul_eq_mul, map_mul, dualApp_res]
      congr 1
      exact (GlobalTheory.T.evalSectionAtRingPoint_spMap_comp_restrict_stalk.2.2.1 E C xE Vf _ inf_le_left hxEf hxs (M l j)).trans
        (GlobalTheory.T.evalSectionAtRingPoint_spMap_comp_restrict_stalk.1 K E C (algebraMap K E) x Vf hxf hxEf (M l j))
    have he' : ∀ l, u * φ (e l) = ∑ j, algebraMap K E (evAt x hxf (M l j)) * w j := by
      intro l
      show u * (u⁻¹ * y l) = _
      rw [← _root_.mul_assoc, mul_inv_cancel₀ hu, _root_.one_mul]
      simp [y, Matrix.mulVec, dotProduct]
    refine Eq.trans h1 ?_
    simp only [hD, hR, he', Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
    ring
  have htan' : HasTan G xE (spMap (sc p u) ≫ ζ) (fun j => i.app V₀ (s j)) w :=
    GlobalTheory.T.hasTangent_of_single_affineChart C G E 2 xE _ hξ'path r V₀ _ w U₀ hU₀a hξ'U _ (inf_le_left.trans h₀) inf_le_right hxs key
  have hunit : ∀ j, 2 ≤ j → IsUnit ((2 : E) ^ j - 2) := by
    intro j hj
    refine isUnit_iff_ne_zero.2 fun h0 => ?_
    have h4 : 4 ≤ 2 ^ j := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj
    have hc : ((2 ^ j - 2 : ℕ) : E) = 0 := by
      rw [Nat.cast_sub (by omega : 2 ≤ 2 ^ j)]; push_cast; exact h0
    rw [Nat.cast_eq_zero] at hc
    omega
  have heq : ξ = spMap (sc p u) ≫ ζ := by
    refine GlobalTheory.T.formalSquaringPath_unique_of_agree_low_degrees C G E hqs 2 2 (by norm_num) hunit xE ξ _ hξ hξ'path ?_
    intro U h h' f j hj0 hj2
    obtain rfl : j = 1 := by omega
    have hb3 : ⊤ ≤ xE ⁻¹ᵁ (V₀ ⊓ unitSec G ⁻¹ᵁ U) := by
      refine top_le_preimage_inf _ hxE0 ?_
      apply top_le_of_comp
      rw [← hξ.zero]; exact top_le_comp_preimage _ _ h
    rw [hξt U h _ inf_le_left inf_le_right hb3 f, htan' U h' _ inf_le_left inf_le_right hb3 f]
  exact ⟨b, ζ, hbx, hζ, heq⟩

end GlobalTheory.Nef
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSignatureOfGramEqOne
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SquareComm
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BotDict

open GlobalTheory.ChainFr GlobalTheory.SquareComm

variable {D : D7}

theorem gramAt_eq_one {V : HSp D} (h : V.gram = 1) (τ : D.what₂.Tau) : gramAt D V τ = 1 := by
  unfold gramAt
  rw [h]
  exact Matrix.map_one _ (map_zero _) (map_one _)

def stdFr (V : HSp D) (h : V.gram = 1) : Fr V where
  ε _ _ := true
  fr _ := 1
  fr_unit _ := isUnit_one
  fr_gram τ := by
    rw [gramAt_eq_one h τ]
    simp [Formalism.REAL.Jm]

theorem cart_stdFr (V : HSp D) (h : V.gram = 1) (τ : D.what₂.Tau) : (stdFr V h).cart τ = 1 := by
  simp [Fr.cart, stdFr, Formalism.REAL.Jm]

theorem onb_stdFr (V : HSp D) (h : V.gram = 1) (τ : D.what₂.Tau) : (stdFr V h).onb τ = 1 := by
  simp [Fr.onb, stdFr]

theorem cart_frSgn_true_stdFr (V : HSp D) (h : V.gram = 1) (τ : D.what₂.Tau) : (frSgn true (stdFr V h)).cart τ = -1 := by
  simp only [Fr.cart, frSgn, stdFr, Formalism.REAL.Jm]
  ext a b
  by_cases hab : a = b
  · subst hab; simp
  · simp [Matrix.one_apply, hab]

theorem cart_frSgn_false_stdFr (V : HSp D) (h : V.gram = 1) (τ : D.what₂.Tau) : (frSgn false (stdFr V h)).cart τ = 1 := by
  simp [Fr.cart, frSgn, stdFr, Formalism.REAL.Jm]

theorem hasSignature_of_gram_eq_one {V : HSp D} (h : V.gram = 1) (τ : D.what₂.Tau) :
    Formalism.UG.HasSignature (gramAt D V τ) V.rank 0 := by
  refine ⟨(Equiv.sumEmpty (Fin V.rank) (Fin 0)).symm, 1, ?_⟩
  rw [gramAt_eq_one h τ]
  ext (a | a) (b | b)
  · simp [Formalism.UG.Jpq, Formalism.UG.cT, Matrix.one_apply]
  · exact b.elim0
  · exact a.elim0
  · exact a.elim0

end GlobalTheory.BotDict

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharacterFiniteIdeleValueEq
section
open NumberField IsDedekindDomain
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 lamOf Th La Iop Qbar lamC)
open Formalism.MainNotions.StandardLatticesGL3 (TT stdL pt oddE0 Wd La0 Crv inc OhE IntU)
open GlobalTheory.NormSum (Pair intG)
open GlobalTheory.FunObj.SqNum (hatId CongOne skewLat unitBlock cosetVec)
open GlobalTheory.NormExact (Reads Setup IsFinIdl HasFinPart finPt)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (InId IsUnitDet unitChar stdFst)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdRead

noncomputable section

open scoped TensorProduct

namespace GlobalTheory.FinIdlRead

open GlobalTheory.Mem.Col2.SplitChar

theorem toFinE_eq_adEquiv (D : D7) (y : Formalism.MainNotions.StandardLatticesGL3.AE D) : GlobalTheory.BotFormula.toFinE D y = adEquiv D y := by
  let f : Formalism.MainNotions.StandardLatticesGL3.AE D →+* Formalism.MainNotions.StandardLatticesGL3.AE D := (adEquiv D).symm.toRingHom.comp (GlobalTheory.BotFormula.toFinE D).toRingHom
  have hf : ∀ z, adEquiv D (f z) = GlobalTheory.BotFormula.toFinE D z := fun z => (adEquiv D).apply_symm_apply _
  have hι : ∀ (x : D.host.E) (a : FiniteAdeleRing (𝓞 ℚ) ℚ), (GlobalTheory.BotFormula.toFinE D).toRingHom (x ⊗ₜ[ℚ] a) =
      algebraMap D.host.E _ x * GlobalTheory.AdeleBaseChange.adMap ℚ D.host.E a := GlobalTheory.BotClassDict.toFinE_tmul
  have hinc : ∀ a : D.host.E, f (inc D a) = inc D a := fun a => by
    apply (adEquiv D).injective
    rw [hf, adEquiv_inc]
    have h1 : GlobalTheory.BotFormula.toFinE D (inc D a) = algebraMap D.host.E _ a * GlobalTheory.AdeleBaseChange.adMap ℚ D.host.E 1 :=
      GlobalTheory.BotClassDict.toFinE_tmul a 1
    rw [h1, map_one, mul_one]
  have hint : ∀ r ∈ OhE D, f r ∈ OhE D := fun r hr => by
    rw [mem_OhE_iff, hf]
    exact GlobalTheory.AdeleBaseChange.map_mem_int (F := ℚ) (E := D.host.E) hι hr
  have h0 : f y - y = 0 := by
    refine GlobalTheory.AdeleBaseChange.eq_zero_of_divisible (F := ℚ) (E := D.host.E) (f y - y) fun N hN => ?_
    obtain ⟨a, r, hr, e⟩ := exists_approx y hN
    refine ⟨f r - r, sub_mem (hint r hr) hr, ?_⟩
    rw [nsmul_eq_mul]
    change f y - y = (N : Formalism.MainNotions.StandardLatticesGL3.AE D) * (f r - r)
    rw [e, map_add, map_mul, map_natCast, hinc]
    ring
  rw [← hf, sub_eq_zero.1 h0]

theorem finAdEquiv_one_tmul (D : D7) (x : D.host.E) :
    GlobalTheory.LFun.finAdEquiv D.host.F D.host.E ((1 : Af D.host.F) ⊗ₜ[D.host.F] x) =
      algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E) x := by
  show GlobalTheory.LFun.toFinAd D.host.F D.host.E ((1 : Af D.host.F) ⊗ₜ[D.host.F] x) = _
  rw [GlobalTheory.LFun.toFinAd_tmul, map_one, one_mul]

theorem mem_intAE_iff_finAdEquiv (D : D7) (y : Af D.host.F ⊗[D.host.F] D.host.E) :
    y ∈ intAE D ↔ ∀ P : HeightOneSpectrum (𝓞 D.host.E), Valued.v (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E y P) ≤ 1 := by
  let c := (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).toRingEquiv
  let ι : Formalism.L2.DIV.AfE D.host.F D.host.E →+* FiniteAdeleRing (𝓞 D.host.E) D.host.E :=
    (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E).toRingHom.comp c.symm.toRingHom
  have hι : ∀ x a, ι (x ⊗ₜ[D.host.F] a) = algebraMap D.host.E _ x * GlobalTheory.AdeleBaseChange.adMap D.host.F D.host.E a :=
    fun x a => (GlobalTheory.LFun.toFinAd_tmul a x).trans (mul_comm _ _)
  have e : ι (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E y) = GlobalTheory.LFun.finAdEquiv D.host.F D.host.E y := by
    change GlobalTheory.LFun.finAdEquiv D.host.F D.host.E (c.symm (c y)) = _
    rw [c.symm_apply_apply]
  rw [GlobalTheory.HostAdeleIso.mem_intAE_iff_comm]
  constructor
  · intro hy
    have := GlobalTheory.AdeleBaseChange.map_mem_int hι hy
    rw [e] at this
    exact this
  · intro hy
    refine GlobalTheory.AdeleBaseChange.mem_int_of_map hι ?_
    rw [e]
    exact hy

theorem chr_finIdl : ∀ {D : D7} (ν : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E), ChrEq ν χ → ∀ x y, IsFinIdl x y →
    ((ν x : Circle) : ℂ) = ((χ.1 (GlobalTheory.Mem.Col2.SplitChar.finIdl D y) : ℂˣ) : ℂ) := by
  intro D ν χ h x y hxy
  obtain ⟨Φ, -, hΦ', h1, h2, h3⟩ := GlobalTheory.DetRootRead.exists_adele_equiv_fin D (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E)
    (finAdEquiv_one_tmul D) (mem_intAE_iff_finAdEquiv D)
  rw [GlobalTheory.DetRootRead.read_of_equiv D ν χ h Φ hΦ' h1 h2 x]
  obtain ⟨s, hs, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  have split : ∀ z w : AE D, infPart D z = infPart D w → finPart D z = finPart D w → z = w := fun z w hi hf =>
    s.injective (Prod.ext ((hs z).1.trans (hi.trans (hs w).1.symm)) ((hs z).2.trans (hf.trans (hs w).2.symm)))
  have hfst : (Φ (x : AE D)).1 = 1 := by
    let w : AE D := Φ.symm (1, (Φ (x : AE D)).2)
    have hw : Φ w = (1, (Φ (x : AE D)).2) := Φ.apply_symm_apply _
    have hwi : infPart D w = 1 := (h3 w).1 (by rw [hw])
    have hwf : finPart D w = finPart D (x : AE D) := by
      apply (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E).injective
      rw [← (h3 w).2, ← (h3 (x : AE D)).2, hw]
    have : w = (x : AE D) := split _ _ (hwi.trans hxy.1.symm) hwf
    rw [← this, hw]
  have he : Units.map Φ.toRingHom.toMonoidHom x = GlobalTheory.Mem.Col2.SplitChar.finIdl D y := by
    refine Units.ext (Prod.ext ?_ ?_)
    · exact hfst
    · change (Φ (x : AE D)).2 = adEquiv D (y : Formalism.MainNotions.StandardLatticesGL3.AE D)
      rw [(h3 _).2, hxy.2, toFinE_eq_adEquiv]
  rw [he]

end GlobalTheory.FinIdlRead
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergFinitePointReadsClassicalTranslation
section
open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.NormExact

theorem heisO_finPt_reads : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) {a d : ℕ} (hS : S.rank = a) (hT : T.rank = d)
  (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (r : D.host.E), Setup ψ θ S T cc δ r →
  ∀ G f, Reads ψ θ hS hT cc δ r G f → ∀ z : Matrix (Fin d) (Fin a) D.host.E,
    Reads ψ θ hS hT cc δ r (U D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z) G) (heisO ψ S T (finPt hS hT r z) f) := by
  intro D ψ θ S T a d hS hT cc δ r hs G f hf z
  subst hS hT
  have hc := hs.crv
  have hr := hs.scale
  have hr0 : r ≠ 0 := IsScale.ne_zero hc.1.1 hr
  rw [reads_iff hc hr] at hf ⊢
  refine ⟨GlobalTheory.TwistFactorCompare.isTheta_heisO hs.std hf.1 _, fun w hw => ?_⟩
  set X : VC D S.rank T.rank := fun τ i j => embT D τ (r⁻¹ * z i j) with hXdef
  have hX : (fun τ a b => -(((GlobalTheory.FockPos.frAt (1 : GL (Fin T.rank) D.host.E) τ)⁻¹ *
      Matrix.of (GlobalTheory.VacUnique.infRat S T (Matrix.of fun i j => -(r⁻¹ * z i j)) τ) *
      GlobalTheory.FockPos.frAt (1 : GL (Fin S.rank) D.host.E) τ) a b)) = X := by
    funext τ a b
    have e : ∀ n, GlobalTheory.FockPos.frAt (D := D) (1 : GL (Fin n) D.host.E) τ = 1 := fun n =>
      Matrix.map_one _ (map_zero _) (map_one _)
    simp only [e, inv_one, Matrix.one_mul, Matrix.mul_one]
    show -(embT D τ (-(r⁻¹ * z a b))) = embT D τ (r⁻¹ * z a b)
    rw [map_neg, neg_neg]
  have h := GlobalTheory.MovedTrans.heisO_finRat_real ψ θ S T 1 1 (by simp [Formalism.UG.cT_one, hs.gS])
    (by simp [Formalism.UG.cT_one, hs.gT]) hs.std hs.inf f hf.1 (fun Z => G fun τ i j => δ * embT D τ r * Z τ i j) hf.2
    (Matrix.of fun i j => -(r⁻¹ * z i j)) _ hX.symm w hw
  have e1 : finPt (rfl : S.rank = S.rank) (rfl : T.rank = T.rank) r z =
      GlobalTheory.VacUnique.finRat S T (Matrix.of fun i j => -(r⁻¹ * z i j)) := rfl
  have hpt : pt D (tor0 D cc δ) δ z = fun τ i j => δ * embT D τ r * X τ i j := by
    funext τ i j
    show δ * embT D τ (z i j) = δ * embT D τ r * embT D τ (r⁻¹ * z i j)
    rw [mul_assoc, ← map_mul, ← mul_assoc, mul_inv_cancel₀ hr0, one_mul]
  rw [e1, h, hpt]
  simp only [U]
  rw [Hf_scale hc hr, Hf_scale hc hr]
  have hY : ((fun τ i j => δ * embT D τ r * GlobalTheory.FockPos.zCo θ 1 1 w τ i j) + fun τ i j => δ * embT D τ r * X τ i j) =
      fun τ i j => δ * embT D τ r * (GlobalTheory.FockPos.zCo θ 1 1 w + X) τ i j := by
    funext τ i j
    simp only [Pi.add_apply]
    ring
  rw [hY]

end GlobalTheory.NormExact
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealExtendConjMulEqAbsNormStatement
section
open NumberField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idealExtend_conj_mul_eq_absNorm : ∀ (D : Formalism.BasicNotions.D7) (cc : Ideal (𝓞 D.host.K)), (∀ α ∈ GlobalTheory.VacRead.cE D cc, ∀ β ∈ GlobalTheory.VacRead.cE D cc, ∃ o : 𝓞 D.host.E, D.host.conj α * β = (Ideal.absNorm cc : D.host.E) * (o : D.host.E)) ∧ (Ideal.absNorm cc : D.host.E) ∈ Submodule.span (𝓞 D.host.E) {t | ∃ α ∈ GlobalTheory.VacRead.cE D cc, ∃ β ∈ GlobalTheory.VacRead.cE D cc, t = D.host.conj α * β} := by
  first | exact @GlobalTheory.VacRead.conj_mul_cE_absNorm | exact GlobalTheory.VacRead.conj_mul_cE_absNorm | (intros; apply GlobalTheory.VacRead.conj_mul_cE_absNorm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsRestBis
section
open NumberField IsLocalRing Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF

attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory

namespace GlobalTheory.IntegralChartCover

theorem cover : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (lv : Level H) (Xo : Moduli Dw lv) (c : Coeff lv) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C3 : IntChart T io y), ∃ (T' : CDVR) (φ : T.V →+* T'.V) (t' : SAB H (Sp T'.V)), Function.Injective φ ∧ φ.Finite ∧ UpFBr.GeoJ T'.V t'.G (𝓞 E) (fun a => t'.act.act a) (chD C3.ch) (fun i => MvPowerSeries.map φ (C3.FT i)) (fun a i => MvPowerSeries.map φ (C3.actT a i)) := by
  intro E _ _ _ H Dw lv Xo c inst hstar T io y C3
  obtain rfl : inst = H.starRing := GlobalTheory.PowGerm.starRing_ext_of_star inst H.starRing hstar
  letI := H.starRing
  letI := io.toAlgebra
  obtain ⟨T', φ, t', m, hi, hf, ⟨P⟩⟩ := GlobalTheory.ChartCharacters.exists_finite_ext_pelUnif Xo T C3.I.G C3.I.t' C3.I.m2 _ C3.I.m1
  obtain ⟨F', x', act', hF, hA, hx, ha⟩ := GlobalTheory.integralChart_baseChange E H Dw lv Xo c T io y C3 T' φ t' m
  exact ⟨T', φ, t', hi, hf, P.D, P.A, P.U.toUnifPre, F', x', _, t'.act.toRingAct, P.oD, P.oA, act', hF, funext hA, fun _ => rfl, hx, P.lin, ha⟩

end GlobalTheory.IntegralChartCover
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndexIdealRankOneTensorImageEqMapStatement
section
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.indexIdeal_rankOne_tensor_image_eq_map : ∀ (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] (τ : 𝓞 E →+* 𝓞 K) (τE : E →+* K),
    (∀ x : 𝓞 E, τE x = ((τ x : 𝓞 K) : K)) → ∀ (p m n : ℕ) (ell : Submodule (𝓞 K) (Fin m → K))
    (M : Fin p → ((Fin m → K) →ₗ[K] (Fin n → K))) (Λ : Submodule (𝓞 E) (Fin p → E)),
    ell.FG → ReciprocityTheory.GeometryOfNumbersTheory.latRank K ell = 1 → (∀ a, Function.Injective (M a)) →
    iSupIndep (fun a => Submodule.span K ((ell.map ((M a).restrictScalars (𝓞 K)) : Submodule (𝓞 K) (Fin n → K)) : Set (Fin n → K))) →
    Λ.FG → (∀ x : Fin p → 𝓞 E, (fun a => (x a : E)) ∈ Λ) →
    GlobalTheory.FlatCM.idx K p (Submodule.span (𝓞 K) {w | ∃ c ∈ Λ, ∃ e ∈ ell, w = ∑ a, τE (c a) • M a e})
                 (⨆ a, ell.map ((M a).restrictScalars (𝓞 K))) =
      (GlobalTheory.FlatCM.idx E p Λ (Submodule.span (𝓞 E) (Set.range fun a => (Pi.single a (1 : E) : Fin p → E)))).map τ := by
  first | exact @GlobalTheory.IdxTensor.idx_image_eq_map | exact GlobalTheory.IdxTensor.idx_image_eq_map | (intros; apply GlobalTheory.IdxTensor.idx_image_eq_map <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertCompletionToAdelesPropertiesStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertCompletionToAdeles_properties : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {v : Pl F}
    {w : HeightOneSpectrum (𝓞 E)} (hw : Formalism.UG.IsInertAt F E v w),
  Function.Injective (GlobalTheory.InertBigCell.iotaW hw) ∧
  (∀ x y, GlobalTheory.InertBigCell.iotaW hw (x * y) = GlobalTheory.InertBigCell.iotaW hw x * GlobalTheory.InertBigCell.iotaW hw y) ∧
  GlobalTheory.InertBigCell.iotaW hw 1 = algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1) ∧
  (∀ z : AE F E, At (evFin F v) z ↔ ∃ x, GlobalTheory.InertBigCell.iotaW hw x = z) ∧
  (∀ x, GlobalTheory.InertBigCell.iotaW hw (GlobalTheory.InertBigCell.conjW σ hw x) = cA σ (GlobalTheory.InertBigCell.iotaW hw x)) ∧
  (∀ x, GlobalTheory.InertBigCell.iotaW hw (2⁻¹ * x) = ⅟(2 : AF F) • GlobalTheory.InertBigCell.iotaW hw x) ∧
  (∀ e : E, GlobalTheory.InertBigCell.iotaW hw (algebraMap E (w.adicCompletion E) e) =
    algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1) * inclR (F := F) (AF F) e) := by
  first | exact @GlobalTheory.InertBigCell.iotaW_adelic_place | exact GlobalTheory.InertBigCell.iotaW_adelic_place | (intros; apply GlobalTheory.InertBigCell.iotaW_adelic_place <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralAdelicPureTensorEqProductLocalStatement
section
open scoped Matrix GlobalTheory.VacAny
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RatWeilOp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_adelic_pureTensor_eq_product_local : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] [MeasurableSpace (κ → AF F)] [BorelSpace (κ → AF F)]
    [MeasurableSpace (κ → mixedEmbedding.mixedSpace F)] [BorelSpace (κ → mixedEmbedding.mixedSpace F)]
    [∀ v : Pl F, MeasurableSpace (κ → Fv F v)] [∀ v : Pl F, BorelSpace (κ → Fv F v)]
    (μ : Measure (κ → AF F)) [μ.IsAddHaarMeasure] (μi : Measure (κ → mixedEmbedding.mixedSpace F)) [μi.IsAddHaarMeasure]
    (μv : ∀ v : Pl F, Measure (κ → Fv F v)) [∀ v, (μv v).IsAddHaarMeasure],
    (∀ v, μv v {x | ∀ i, x i ∈ v.adicCompletionIntegers F} = 1) → ∃ c : ℂ, c ≠ 0 ∧
      ∀ (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ), Continuous f → Integrable f μi → IsFam φ →
        Integrable (fun x : κ → AF F => f (fun i => evI F (x i)) * ∏ᶠ v, φ v fun i => evFin F v (x i)) μ ∧
        ∫ x, f (fun i => evI F (x i)) * ∏ᶠ v, φ v (fun i => evFin F v (x i)) ∂μ = c * (∫ x, f x ∂μi) * ∏ᶠ v, ∫ x, φ v x ∂(μv v) := by
  first | exact @GlobalTheory.AdelicHaarPure.integral_pure_haar | exact GlobalTheory.AdelicHaarPure.integral_pure_haar | (intros; apply GlobalTheory.AdelicHaarPure.integral_pure_haar <;> assumption)
end

