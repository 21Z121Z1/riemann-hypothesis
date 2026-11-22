import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0362
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1712
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1791
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1714
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1806
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1765
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1777
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1453
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0201
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0331
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.CentralInvolutionRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsINeZeroKind
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrientedHermitianFormQuadSumEqTrace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1728
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHasLocalSmall
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentMulCutSubOneEntry
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstStandardPairMemberHasThetaFunction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1792
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotRelZero
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1674
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1702
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1794
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0035

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalSquaringPathUniqueOfAgreeLowDegrees
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

namespace GlobalTheory.Nef

theorem exists_spMap_fromSpecStalk {A : Type} [CommRing A] [IsLocalRing A] {X : Scheme.{0}} (f : Sp A ⟶ X) (x : X)
    (hx : f (IsLocalRing.closedPoint (CommRingCat.of A)) = x) :
    ∃ g0 : X.presheaf.stalk x →+* A, spMap g0 ≫ X.fromSpecStalk x = f := by
  subst hx
  exact ⟨(Scheme.stalkClosedPointTo f).hom, Scheme.Spec_stalkClosedPointTo_fromSpecStalk f⟩

theorem ringHom_eq_of_fromSpecStalk {X : Scheme.{0}} (x : X) {B : Type} [CommRing B]
    (f f' : X.presheaf.stalk x →+* B) (h : spMap f ≫ X.fromSpecStalk x = spMap f' ≫ X.fromSpecStalk x) : f = f' := by
  have h' : spMap f = spMap f' := (cancel_mono (X.fromSpecStalk x)).mp h
  have := Spec.map_injective h'
  exact congrArg CommRingCat.Hom.hom this

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  rw [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

theorem spMap_constantCoeff_closedPoint (R : Type) [CommRing R] [IsLocalRing R] : (spMap (PowerSeries.constantCoeff (R := R))) (IsLocalRing.closedPoint (CommRingCat.of R)) = IsLocalRing.closedPoint (CommRingCat.of (PowerSeries R)) := by
  haveI : IsLocalHom (CommRingCat.Hom.hom (CommRingCat.ofHom (PowerSeries.constantCoeff (R := R)))) :=
    ⟨fun _ h => PowerSeries.isUnit_iff_constantCoeff.mpr h⟩
  exact Spec_closedPoint

end GlobalTheory.Nef

namespace GlobalTheory.Nef

theorem path_unique : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (R : Type) [CommRing R], ∀ [IsLocalRing R], QuasiSeparated G.hom → ∀ (c : R) (n : ℕ), 0 < n → (∀ j, n ≤ j → IsUnit (c ^ j - 2)) → ∀ (b : Sp R ⟶ S) (ξ ξ' : Sp (PowerSeries R) ⟶ G.left), IsPath G c b ξ → IsPath G c b ξ' → (∀ (U : G.left.Opens) (h : ⊤ ≤ ξ ⁻¹ᵁ U) (h' : ⊤ ≤ ξ' ⁻¹ᵁ U) (f : Γ(G.left, U)) (j : ℕ), 0 < j → j < n → PowerSeries.coeff j (evAt ξ h f) = PowerSeries.coeff j (evAt ξ' h' f)) → ξ = ξ' := by
  intro S G _ R _ _ hqs c n hn hc b ξ ξ' hξ hξ' hlow
  set s : S := b (IsLocalRing.closedPoint (CommRingCat.of R)) with hs
  set x : G.left := unitSec G s with hx
  have hpt : ∀ q0 : Sp (PowerSeries R) ⟶ G.left, IsPath G c b q0 →
      q0 (IsLocalRing.closedPoint (CommRingCat.of (PowerSeries R))) = x := by
    intro q0 hq0
    have e := congrArg (fun q : Sp R ⟶ G.left => q (IsLocalRing.closedPoint (CommRingCat.of R))) hq0.zero
    change q0 (spMap PowerSeries.constantCoeff (IsLocalRing.closedPoint (CommRingCat.of R))) = unitSec G s at e
    rw [spMap_constantCoeff_closedPoint] at e
    exact e
  obtain ⟨π, ε, m, hSD, h1, h2, h3⟩ := GlobalTheory.T.exists_groupSchemeUnitStalkData S G s
  have hm := GlobalTheory.T.groupSchemeSquaring_cotangent_eq_two S G hqs s π ε m hSD
  obtain ⟨β, hβ⟩ := exists_spMap_fromSpecStalk b s rfl
  obtain ⟨g, hg⟩ := exists_spMap_fromSpecStalk ξ x (hpt ξ hξ)
  obtain ⟨g', hg'⟩ := exists_spMap_fromSpecStalk ξ' x (hpt ξ' hξ')
  have E1 : ∀ (k : G.left.presheaf.stalk x →+* PowerSeries R), IsPath G c b (spMap k ≫ G.left.fromSpecStalk x) →
      k.comp π = PowerSeries.C.comp β := by
    intro k hk
    apply ringHom_eq_of_fromSpecStalk s
    rw [spMap_comp' π k, spMap_comp' β PowerSeries.C, Category.assoc, Category.assoc, hβ, hSD.str, ← Category.assoc, hk.base]
  have E2 : ∀ (k : G.left.presheaf.stalk x →+* PowerSeries R), IsPath G c b (spMap k ≫ G.left.fromSpecStalk x) →
      PowerSeries.constantCoeff.comp k = β.comp ε := by
    intro k hk
    apply ringHom_eq_of_fromSpecStalk x
    rw [spMap_comp' k PowerSeries.constantCoeff, spMap_comp' ε β, Category.assoc, Category.assoc, hSD.unit, ← Category.assoc (spMap β), hβ, hk.zero]
  have E3 : ∀ (k : G.left.presheaf.stalk x →+* PowerSeries R), IsPath G c b (spMap k ≫ G.left.fromSpecStalk x) →
      (PowerSeries.rescale c).comp k = k.comp m := by
    intro k hk
    apply ringHom_eq_of_fromSpecStalk x
    rw [spMap_comp' k (PowerSeries.rescale c), spMap_comp' m k, Category.assoc, Category.assoc, hSD.sq, hk.scale, Category.assoc]
  subst hg hg'
  have hlow' : ∀ j < n, ∀ f, PowerSeries.coeff j (g f) = PowerSeries.coeff j (g' f) := by
    intro j hj f
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · have a := RingHom.congr_fun (E2 g hξ) f
      have a' := RingHom.congr_fun (E2 g' hξ') f
      simp only [RingHom.comp_apply] at a a'
      rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_zero_eq_constantCoeff_apply, a, a']
    · obtain ⟨U, hxU, f0, rfl⟩ := TopCat.Presheaf.germ_exist _ f
      obtain ⟨hh, hev⟩ := (GlobalTheory.T.evalSectionAtRingPoint_spMap_comp_restrict_stalk).2.2.2.2.2.2 (PowerSeries R) G.left x g U hxU
      obtain ⟨hh', hev'⟩ := (GlobalTheory.T.evalSectionAtRingPoint_spMap_comp_restrict_stalk).2.2.2.2.2.2 (PowerSeries R) G.left x g' U hxU
      have := hlow U hh hh' f0 j hj0 hj
      rw [hev, hev'] at this
      exact this
  have := ringHom_powerSeries_eq_of_rescale _ _ R π ε m β c n h1 h2 h3 hm hn hc g g' (E1 g hξ) (E1 g' hξ')
    (E2 g hξ) (E2 g' hξ') (E3 g hξ) (E3 g' hξ') hlow'
  rw [this]

end GlobalTheory.Nef
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussMulUnitary
section
open scoped Matrix NNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.VacKInf.LeviFix

variable {D : D7}

theorem compAt_mul' (θ : InfFam D) (τ : D.what₂.Tau) {k m n : ℕ} (x : Mx D k m) (y : Mx D m n) :
    compAt θ τ (HMul.hMul x y : Mx D k n) = compAt θ τ x * compAt θ τ y :=
  Matrix.map_mul (f := (θ τ).comp (infPart D))

theorem compAt_adj' {θ : InfFam D} (hθ : IsInfFam θ) (τ : D.what₂.Tau) {m n : ℕ} (x : Mx D m n) :
    compAt θ τ (adj x) = (compAt θ τ x)ᴴ := by
  ext i j
  simp only [compAt, adj, Matrix.map_apply, Matrix.transpose_apply, Matrix.conjTranspose_apply]
  rw [GlobalTheory.FockCompare.comp_cA hθ τ]
  rfl

end GlobalTheory.VacKInf.LeviFix

namespace GlobalTheory.VacKInf

end GlobalTheory.VacKInf
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussMulUnram
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (gauss unifAt PsiUnr)

noncomputable section

namespace GlobalTheory.GaussUnr

open ValuativeRel GlobalTheory.SplitFlip GlobalTheory.GaussNonvanish

theorem gauss_mul_unram : ∀ {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) {v : HeightOneSpectrum (𝓞 F)}
    (ν₀ ξ : (Fv F v)ˣ →* ℂˣ), (∀ x : (Fv F v)ˣ, (x : Fv F v) ∈ v.adicCompletionIntegers F →
      ((x⁻¹ : (Fv F v)ˣ) : Fv F v) ∈ v.adicCompletionIntegers F → ξ x = 1) →
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.condExp (ν₀ * ξ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.condExp ν₀ ∧
      ∃ y : (Fv F v)ˣ, gauss ψ (ν₀ * ξ) = (((ξ y)⁻¹ : ℂˣ) : ℂ) * gauss ψ ν₀ := by
  intro F _ _ ψ v ν₀ ξ hξ
  have hϖ : IsUnif (unifAt v) := (GlobalTheory.SplitFlip.exists_isUnif (k := Fv F v)).choose_spec
  have hunit : ∀ x : (Fv F v)ˣ, valuation (Fv F v) (x : Fv F v) = 1 → ξ x = 1 := fun x hx => by
    apply hξ x
    · exact (val_le_one_iff v _).1 hx.le
    · apply (val_le_one_iff v _).1
      rw [Units.val_inv_eq_inv_val, map_inv₀, hx, inv_one]
  have hce : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.condExp (ν₀ * ξ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.condExp ν₀ := by
    unfold GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.condExp
    congr 1
    ext c
    simp only [Set.mem_setOf_eq, CondLE]
    refine forall₂_congr fun x hx => ?_
    rw [MonoidHom.mul_apply, hunit x hx.1, mul_one]
  refine ⟨hce, ?_⟩
  unfold gauss
  rw [hce]
  generalize GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.condExp ν₀ = c
  rcases Nat.eq_zero_or_pos c with h0 | hc1
  · subst h0
    have hsu : ∀ a b : (Res (Fv F v) 0)ˣ, a = b := fun a b =>
      Units.ext ((Ideal.Quotient.subsingleton_iff.2 (by simp)).elim _ _)
    classical
    rw [Fintype.sum_eq_single 1 (fun y hy => (hy (hsu y 1)).elim), Fintype.sum_eq_single 1 (fun y hy => (hy (hsu y 1)).elim)]
    by_cases h : ((Quotient.out (1 : (Res (Fv F v) 0)ˣ).1 : (ValuativeRel.valuation (Fv F v)).integer) : Fv F v) = 0
    · refine ⟨1, ?_⟩
      rw [dif_pos h, dif_pos h, mul_zero]
    · refine ⟨Units.mk0 _ h, ?_⟩
      rw [dif_neg h, dif_neg h, MonoidHom.mul_apply, mul_inv, Units.val_mul, mul_comm (((ν₀ _)⁻¹ : ℂˣ) : ℂ),
        mul_assoc]
  · refine ⟨1, ?_⟩
    rw [map_one, inv_one, Units.val_one, one_mul]
    refine Finset.sum_congr rfl fun y _ => ?_
    by_cases h : ((Quotient.out y.1 : (ValuativeRel.valuation (Fv F v)).integer) : Fv F v) = 0
    · rw [dif_pos h, dif_pos h]
    · rw [dif_neg h, dif_neg h, MonoidHom.mul_apply, hunit _ (val_rep_unit hϖ hc1 y), mul_one]

end GlobalTheory.GaussUnr
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenPtSubset
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.VacAny
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU GlobalTheory.WeilM
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At latAtV realAd evI)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.BigDat

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {i j : ℕ}

variable (G i j) in

abbrev Pt : Type := Matrix (Fin (spW G i j).rank) (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (AE D)

variable (G i j) in

abbrev Ix : Type := Fin (spW G i j).rank × Fin ((spW G i j).rank + (spW₁ G i j).rank)

variable (G i j) in

abbrev HomV : Type := WO (negSp (spW G i j)) (spV G i j)

variable (G i j) in

abbrev HomW : Type := WO (spV₁ G i j) (spW G i j)

abbrev mapV (e : Num G i j) (u : Pt G i j) : HomV G i j := mulG (negSp (spW G i j)) (colV e u)ᵀ

abbrev mapW (e : Num G i j) (u : Pt G i j) : HomW G i j := adjV₁ e u

theorem mulG_eq (S : HSp D) {n : ℕ} (y : Matrix (Fin n) (Fin S.rank) (AE D)) :
    mulG S y = HMul.hMul y (S.gram.map (incA D)) := rfl

def divG (S : HSp D) {n : ℕ} (x : Matrix (Fin n) (Fin S.rank) (AE D)) : Matrix (Fin n) (Fin S.rank) (AE D) :=
  HMul.hMul x ((S.gram⁻¹).map (incA D))

theorem divG_mulG (S : HSp D) {n : ℕ} (x : Matrix (Fin n) (Fin S.rank) (AE D)) : divG S (mulG S x) = x := by
  rw [divG, mulG_eq, Matrix.mul_assoc, mul_eq_one_comm.1 (GlobalTheory.RouteCoords.inv_mul_gram S), Matrix.mul_one]

theorem mulG_divG (S : HSp D) {n : ℕ} (x : Matrix (Fin n) (Fin S.rank) (AE D)) : mulG S (divG S x) = x := by
  rw [divG, mulG_eq, Matrix.mul_assoc, GlobalTheory.RouteCoords.inv_mul_gram S, Matrix.mul_one]

theorem mulG_add (S : HSp D) {n : ℕ} (x y : Matrix (Fin n) (Fin S.rank) (AE D)) : mulG S (x + y) = mulG S x + mulG S y :=
  Matrix.add_mul _ _ _

theorem mulG_smul (S : HSp D) {n : ℕ} (c : AF D.host.F) (x : Matrix (Fin n) (Fin S.rank) (AE D)) :
    mulG S (c • x) = c • mulG S x := Matrix.smul_mul _ _ _

def ofMaps (e : Num G i j) (x : HomV G i j × HomW G i j) : Pt G i j :=
  (fromCols (divG (negSp (spW G i j)) x.1)ᵀ ((divG (spV₁ G i j) (-x.2)).map (cA D))).submatrix id e.symm

theorem mapV_ofMaps (e : Num G i j) (x : HomV G i j × HomW G i j) : mapV e (ofMaps e x) = x.1 := by
  have h1 : (colV e (ofMaps e x))ᵀ = divG (negSp (spW G i j)) x.1 := Matrix.ext fun a b => by
    simp only [colV, ofMaps, transpose_apply, submatrix_apply, id, Equiv.symm_apply_apply, fromCols_apply_inl]
  exact (congrArg (mulG (negSp (spW G i j))) h1).trans (mulG_divG _ _)

theorem mapW_ofMaps (e : Num G i j) (x : HomV G i j × HomW G i j) : mapW e (ofMaps e x) = x.2 := by
  have h2 : ((ofMaps e x).submatrix id fun k => e (.inr k)).map (cA D) = divG (spV₁ G i j) (-x.2) := Matrix.ext fun a b => by
    simp only [ofMaps, submatrix_apply, id, Equiv.symm_apply_apply, fromCols_apply_inr, map_apply,
      GlobalTheory.DualPairCheck.cA_cA]
  exact (congrArg (fun y => -mulG (spV₁ G i j) y) h2).trans ((congrArg Neg.neg (mulG_divG _ _)).trans (neg_neg _))

theorem ofMaps_maps (e : Num G i j) (u : Pt G i j) : ofMaps e (mapV e u, mapW e u) = u := by
  have h1 : divG (negSp (spW G i j)) (mapV e u) = (colV e u)ᵀ := divG_mulG _ _
  have h2 : divG (spV₁ G i j) (-mapW e u) = (u.submatrix id fun k => e (.inr k)).map (cA D) :=
    (congrArg (divG (spV₁ G i j)) (neg_neg _)).trans (divG_mulG _ _)
  ext a b
  obtain ⟨k | k, rfl⟩ := e.surjective b
  · simp only [ofMaps, submatrix_apply, id, Equiv.symm_apply_apply, fromCols_apply_inl, transpose_apply]
    exact congrFun (congrFun h1 k) a
  · simp only [ofMaps, submatrix_apply, id, Equiv.symm_apply_apply, fromCols_apply_inr, map_apply]
    exact (congrArg (cA D) (congrFun (congrFun h2 a) k)).trans (GlobalTheory.DualPairCheck.cA_cA _)

theorem mapV_add (e : Num G i j) (u u' : Pt G i j) : mapV e (u + u') = mapV e u + mapV e u' :=
  mulG_add (negSp (spW G i j)) (colV e u)ᵀ (colV e u')ᵀ

theorem mapW_add (e : Num G i j) (u u' : Pt G i j) : mapW e (u + u') = mapW e u + mapW e u' := by
  have h : ((u + u').submatrix id fun k => e (.inr k)).map (cA D) =
      (u.submatrix id fun k => e (.inr k)).map (cA D) + (u'.submatrix id fun k => e (.inr k)).map (cA D) :=
    Matrix.ext fun a b => map_add (cA D) _ _
  exact (congrArg (fun y => -mulG (spV₁ G i j) y) h).trans ((congrArg Neg.neg (mulG_add _ _ _)).trans (neg_add _ _))

theorem mapV_smul (e : Num G i j) (c : AF D.host.F) (u : Pt G i j) : mapV e (c • u) = c • mapV e u :=
  mulG_smul (negSp (spW G i j)) c (colV e u)ᵀ

theorem mapW_smul (e : Num G i j) (c : AF D.host.F) (u : Pt G i j) : mapW e (c • u) = c • mapW e u := by
  have h : ((c • u).submatrix id fun k => e (.inr k)).map (cA D) = c • (u.submatrix id fun k => e (.inr k)).map (cA D) :=
    Matrix.ext fun a b => map_smul (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) c _
  exact (congrArg (fun y => -mulG (spV₁ G i j) y) h).trans ((congrArg Neg.neg (mulG_smul _ _ _)).trans (smul_neg _ _).symm)

def maps (e : Num G i j) : Pt G i j ≃ₗ[AF D.host.F] HomV G i j × HomW G i j where
  toFun u := (mapV e u, mapW e u)
  invFun := ofMaps e
  map_add' u u' := Prod.ext (mapV_add e u u') (mapW_add e u u')
  map_smul' c u := Prod.ext (mapV_smul e c u) (mapW_smul e c u)
  left_inv := ofMaps_maps e
  right_inv x := Prod.ext (mapV_ofMaps e x) (mapW_ofMaps e x)

theorem maps_apply (e : Num G i j) (u : Pt G i j) : maps e u = (mapV e u, mapW e u) := rfl

abbrev sympPt (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (u u' : Pt G i j) : AF D.host.F :=
  symp (R := AF D.host.F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (-1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.V.J)
    (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.W.J) u u'

set_option maxHeartbeats 1000000 in

theorem symp_eq (e : Num G i j) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (hW : Γ.V.J = (1 : D.host.E) • (spW G i j).gram)
    (hWW : Γ.W.J = skewGram (spV G i j) (spV₁ G i j) e) (x x' : Pt G i j) :
    sympPt Γ x x' = symplO _ _ (mapV e x) (mapV e x') + symplO _ _ (mapW e x) (mapW e x') := by
  have hJW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.W.J =
      incA D D.host.xi0 • GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e ((spV G i j).gram.map (incA D))ᵀ ((spV₁ G i j).gram.map (incA D))ᵀ := by
    have k : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM Γ.W.J = incA D D.host.xi0 •
        GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM (spV G i j).gramᵀ) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM (spV₁ G i j).gramᵀ) := by
      rw [hWW, skewGram, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM_smul]
      congr 1
      exact GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk_map _ _ _ (map_zero _)
    exact k
  have hJV : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.V.J = (spW G i j).gram.map (incA D) := by
    rw [hW, one_smul]; rfl
  have hN : (negSp (spW G i j)).gram.map (incA D) = -(spW G i j).gram.map (incA D) := by
    rw [negSp_gram]; exact Matrix.map_neg _ (map_neg _) _
  have hA : hTens (R := AF D.host.F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.V.J)
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.W.J) x x' = _ :=
    GlobalTheory.RouteCoords.quadruple_sum_eq_trace_transpose_mul (cA D : AE D → AE D) _ _ _ _
  have hB1 : hO _ _ (mapV e x) (mapV e x') = _ :=
    GlobalTheory.RouteCoords.orientedHermitianForm_quadSum_eq_trace (cA D : AE D → AE D) (((negSp (spW G i j)).gram⁻¹).map (incA D))
      ((spV G i j).gram.map (incA D)) _ _
  have hB2 : hO _ _ (mapW e x) (mapW e x') = _ :=
    GlobalTheory.RouteCoords.orientedHermitianForm_quadSum_eq_trace (cA D : AE D → AE D) (((spV₁ G i j).gram⁻¹).map (incA D))
      ((spW G i j).gram.map (incA D)) _ _
  have h1 := GlobalTheory.RouteCoords.trace_first (cA D) ((negSp (spW G i j)).gram.map (incA D))
    (((negSp (spW G i j)).gram⁻¹).map (incA D)) ((spV G i j).gram.map (incA D)) (GlobalTheory.RouteCoords.gram_conj_transpose _)
    (GlobalTheory.RouteCoords.inv_mul_gram _) (colV e x) (colV e x')
  have h2 := GlobalTheory.RouteCoords.trace_second (cA D) GlobalTheory.DualPairCheck.cA_cA (incA D D.host.xi0) GlobalTheory.RouteCoords.adeleConj_incl_skewElement_eq_neg
    ((spW G i j).gram.map (incA D)) ((spV₁ G i j).gram.map (incA D)) (((spV₁ G i j).gram⁻¹).map (incA D))
    (GlobalTheory.RouteCoords.gram_conj_transpose _) (GlobalTheory.RouteCoords.gram_conj_transpose _) (GlobalTheory.RouteCoords.inv_mul_gram _)
    (x.submatrix id fun k => e (.inr k)) (x'.submatrix id fun k => e (.inr k))
  rw [Matrix.neg_mul, Matrix.neg_mul, Matrix.neg_mul, trace_neg, mul_neg, map_neg, neg_eq_iff_eq_neg] at h2
  unfold sympPt symp symplO
  rw [hA, hB1, hB2]
  conv_rhs => arg 2; rw [← GlobalTheory.DualPairCheck.trace_cA]
  rw [← map_add]
  congr 1
  erw [h2, h1]
  rw [hN, hJW, hJV, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul,
    GlobalTheory.RouteCoords.mul_blk_mul_transpose, transpose_neg, Matrix.mul_neg, trace_smul, trace_neg, Matrix.add_mul, trace_add,
    submatrix_map, submatrix_map, smul_eq_mul]
  unfold colV
  ring

def box (e : Num G i j) (f₁ : HomV G i j → ℂ) (f₂ : HomW G i j → ℂ) (u : Pt G i j) : ℂ := f₁ (mapV e u) * f₂ (mapW e u)

def heisPt (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (ψ : AddChar (AF D.host.F) ℂ) (u₀ : Pt G i j) (f : Pt G i j → ℂ) (u : Pt G i j) : ℂ :=
  ψ (⅟(2 : AF D.host.F) * sympPt Γ u u₀) * f (u + u₀)

theorem invOf_two : ⅟(2 : AF D.host.F) = algebraMap D.host.F (AF D.host.F) (1 / 2) := by
  refine invOf_eq_right_inv ?_
  rw [← map_ofNat (algebraMap D.host.F (AF D.host.F)) 2, ← map_mul, mul_one_div_cancel two_ne_zero, map_one]

theorem heisPt_box (e : Num G i j) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (hW : Γ.V.J = (1 : D.host.E) • (spW G i j).gram)
    (hWW : Γ.W.J = skewGram (spV G i j) (spV₁ G i j) e) (ψ : AddChar (AF D.host.F) ℂ) (u₀ : Pt G i j)
    (f₁ : HomV G i j → ℂ) (f₂ : HomW G i j → ℂ) :
    heisPt Γ ψ u₀ (box e f₁ f₂) = box e (heisO ψ _ _ (mapV e u₀) f₁) (heisO ψ _ _ (mapW e u₀) f₂) := by
  funext u
  unfold heisPt box heisO symplOH
  rw [symp_eq e Γ hW hWW, mul_add, AddChar.map_add_eq_mul, mapV_add, mapW_add, invOf_two]
  ring

abbrev thetaPt (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (ψ : AddChar (AF D.host.F) ℂ) (Φ : (Ix G i j → AF D.host.F) → ℂ)
    (u : Pt G i j) : ℂ := thetaSum D.host.F (Γ.M.co.rho ψ u Φ)

theorem rho_rho {R W κ : Type} [CommRing R] [Invertible (2 : R)] [AddCommGroup W] [Module R W] {B : W → W → R} [Fintype κ]
    (co : Darboux B κ) (ψ : AddChar R ℂ) (u u₀ : W) (Φ : (κ → R) → ℂ) :
    co.rho ψ u (co.rho ψ u₀ Φ) = ψ (⅟(2 : R) * B u u₀) • co.rho ψ (u + u₀) Φ := by
  funext x
  simp only [Darboux.rho, schr, co.form, map_add, Prod.fst_add, Prod.snd_add, Pi.smul_apply, smul_eq_mul]
  rw [← mul_assoc, ← mul_assoc, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, add_assoc x]
  congr 2
  simp only [add_dotProduct, dotProduct_add]
  linear_combination (-((co.e u).1 ⬝ᵥ (co.e u₀).2)) * invOf_two_add_invOf_two (R := R)

theorem thetaPt_rho (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (ψ : AddChar (AF D.host.F) ℂ) (Φ : (Ix G i j → AF D.host.F) → ℂ)
    (u₀ : Pt G i j) : thetaPt Γ ψ (Γ.M.co.rho ψ u₀ Φ) = heisPt Γ ψ u₀ (thetaPt Γ ψ Φ) :=
  funext fun u => (congrArg (thetaSum D.host.F) (rho_rho Γ.M.co ψ u u₀ Φ)).trans tsum_mul_left

variable (G i j) in

abbrev latV : AddSubgroup (HomV G i j) :=
  latO (negSp (spW G i j)) (spV G i j) (G.Λ (.grid (i + 1) (j + 1)) : Set _) (G.Λ (.grid i (j + 1)) : Set _) fun _ => True

variable (G i j) in

abbrev latW : AddSubgroup (HomW G i j) :=
  latO (spV₁ G i j) (spW G i j) (G.Λ (.grid (i + 1) j) : Set _) (G.Λ (.grid (i + 1) (j + 1)) : Set _) fun _ => True

def latPt (e : Num G i j) (v : Pl D.host.F) : AddSubgroup (Pt G i j) where
  carrier := {u | At (evFin D.host.F v) u ∧ mapV e u ∈ latV G i j ∧ mapW e u ∈ latW G i j}
  zero_mem' := ⟨fun u _ => smul_zero u, by
    rw [show mapV e 0 = 0 from congrArg Prod.fst (map_zero (maps e))]; exact zero_mem _, by
    rw [show mapW e 0 = 0 from congrArg Prod.snd (map_zero (maps e))]; exact zero_mem _⟩
  add_mem' := fun {a b} ha hb => ⟨fun u hu => by rw [smul_add, ha.1 u hu, hb.1 u hu, add_zero],
    by rw [mapV_add]; exact add_mem ha.2.1 hb.2.1, by rw [mapW_add]; exact add_mem ha.2.2 hb.2.2⟩
  neg_mem' := fun {a} ha => ⟨fun u hu => by rw [smul_neg, ha.1 u hu, neg_zero], by
    rw [show mapV e (-a) = -mapV e a from congrArg Prod.fst (map_neg (maps e) a)]; exact neg_mem ha.2.1, by
    rw [show mapW e (-a) = -mapW e a from congrArg Prod.snd (map_neg (maps e) a)]; exact neg_mem ha.2.2⟩

def genPt (e : Num G i j) (v : Pl D.host.F) : Set (Pt G i j) :=
  {γ | (∃ γ' ∈ latPt e v, γ = 2 • γ') ∨ γ ∈ latPt e v ∧ ∃ ε, IsSplitIdem D ε ∧ γ ∈ mixHalf e ε}

theorem genPt_subset (e : Num G i j) (v : Pl D.host.F) : genPt e v ⊆ latPt e v := by
  rintro _ (⟨γ, h, rfl⟩ | h)
  exacts [nsmul_mem h 2, h.1]

def boxGraph (e : Num G i j) (ε : AE D) (T₁ : (HomV G i j → ℂ) →ₗ[ℂ] (HomV G i j → ℂ))
    (T₂ : (HomW G i j → ℂ) →ₗ[ℂ] (HomW G i j → ℂ)) : Submodule ℂ ((Pt G i j → ℂ) × (Pt G i j → ℂ)) :=
  Submodule.span ℂ {p | ∃ φ₁ φ₂, IsSBHalf ε (latV G i j) φ₁ ∧ IsSBHalf ε (latW G i j) φ₂ ∧
    p = (box e φ₁ φ₂, box e (T₁ φ₁) (T₂ φ₂))}

end GlobalTheory.BigDat

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridSquareCharQuotientFiniteUnitIdeleRootOfUnityStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gridSquareCharQuotient_finiteUnitIdele_rootOfUnity : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData Lc sc} (μ₀ : T), Lc.Is μ₀ →
    CharsIn G D.what₂.embLL → ∀ (i j : Fin D.R.m) (t : T) (x : (AE D)ˣ), Formalism.L2.Pj.FinUnit x →
    ∃ ζ : D.what₂.LL, (∃ n : ℕ, 0 < n ∧ ζ ^ n = 1) ∧
      D.what₂.embLL ζ = (((Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2) /
        (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2))) x : Circle) : ℂ) := by
  first | exact @GlobalTheory.SquareCharUnit.nu_finUnit_root | exact GlobalTheory.SquareCharUnit.nu_finUnit_root | (intros; apply GlobalTheory.SquareCharUnit.nu_finUnit_root <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridSquareSkewSumSpaceIsSkewHermitianSelfDualStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gridSquare_skewSumSpace_isSkewHermitianSelfDual : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (_hL : L.Is μ₀) (W : G.Weil)
    (i j : Fin D.R.m) (e : Num G i j) (B : Base D.host.F D.host.E) (τf : InfinitePlace D.host.F → D.what₂.Tau),
    (∀ w x, (B.emb w).1 x = conj (tauE D (τf w) x)) →
    ∃ (Λ : Submodule (𝓞 D.host.E) (Fin ((spW G i j).rank + (spW₁ G i j).rank) → D.host.E))
      (bas : ∀ v : HeightOneSpectrum (𝓞 D.host.F), GL (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (Fv D.host.F v)),
      Spc.IsSkew D.sp.cm.sig B
        (Spc.mk (skewGram (spV G i j) (spV₁ G i j) e) Λ (fun w => (blk e (W.cart (.grid (i : ℕ) ((j : ℕ) + 1)) (τf w)) (W.cart (.grid ((i : ℕ) + 1) (j : ℕ)) (τf w))).map conj) bas)
        ((spW G i j).rank + (spW₁ G i j).rank - ((D.R.m - j - 1) / 2 + (D.R.m - j) / 2))
        ((D.R.m - j - 1) / 2 + (D.R.m - j) / 2) := by
  first | exact @GlobalTheory.SkewLat.bigSpace_isSkew | exact GlobalTheory.SkewLat.bigSpace_isSkew | (intros; apply GlobalTheory.SkewLat.bigSpace_isSkew <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndefiniteScaleThetaSumStatement
section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.indefinite_scale_theta_sum : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (K : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (Rc : Formalism.L2.RecT ex) (P : RowSideFamily ex) (Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)) (Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)) (Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3) (S : Formalism.L2.SG.SpectralTiesReal.STiesR Rc) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (Q : RealT Rc P Dcf Spf Zscf S Ks), RealPins Q → Q.FramesEx := by
  first | exact @GlobalTheory.FramesAtReal.framesEx_of_realisation | exact GlobalTheory.FramesAtReal.framesEx_of_realisation | (intros; apply GlobalTheory.FramesAtReal.framesEx_of_realisation <;> assumption)
end

