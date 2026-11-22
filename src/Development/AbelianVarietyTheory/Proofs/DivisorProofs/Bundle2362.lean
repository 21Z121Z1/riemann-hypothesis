import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2284
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2290
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1607
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0485
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1671
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2250
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0653
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0644
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2302
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2248
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentHaarRealSUOfMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannianHaarIndependentOfOrthonormalFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1951
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0065
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0126
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.MuCardLeTwo
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2306
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2303
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2259
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantsJetsChangeSectionBasis
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2189
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2240

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentCombinationPreservedByBaseChange
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TanBaseChange

open MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

theorem spMap_comp_spMap' {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R' →+* R'')
    (g : R →+* R') : spMap f ≫ spMap g = spMap (f.comp g) := by
  unfold spMap
  rw [← Spec.map_comp]
  rfl

theorem dualMap_comp_algebraMap {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) :
    (Formalism.L2.Pj.dualMap ψ).comp (algebraMap S (DualNumber S)) = (algebraMap T (DualNumber T)).comp ψ := by
  ext s <;> simp [Formalism.L2.Pj.dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem fstHom_comp_dualMap {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) :
    (TrivSqZeroExt.fstHom T T T).toRingHom.comp (Formalism.L2.Pj.dualMap ψ) =
      ψ.comp (TrivSqZeroExt.fstHom S S S).toRingHom := by
  ext s <;> simp [Formalism.L2.Pj.dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem dualMap_comp_epsMul' {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) (a : S) :
    (Formalism.L2.Pj.dualMap ψ).comp (epsMul a) = (epsMul (ψ a)).comp (Formalism.L2.Pj.dualMap ψ) := by
  ext s <;> simp [Formalism.L2.Pj.dualMap, epsMul, TrivSqZeroExt.algebraMap_eq_inl]

theorem list_prod_comp' {X0 : Scheme.{0}} {G : Over X0} [MonObj G] {T T' : Over X0} (f : T' ⟶ T)
    (L : List (T ⟶ G)) : (L.map (f ≫ ·)).prod = f ≫ L.prod := by
  induction L with
  | nil => simp [Hom.one_def]
  | cons a L ih => simp only [List.map_cons, List.prod_cons, ih, Hom.mul_def, comp_lift_assoc]

theorem tan_comb_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (S S' : Type) [CommRing S] [CommRing S'] (φ : S →+* S') (x : Sp S ⟶ X) (x' : Sp S' ⟶ X), spMap φ ≫ x = x' → (∀ v : Sp (DualNumber S) ⟶ t.G.left, IsTanAtG t x v → IsTanAtG t x' (spMap (dualMap φ) ≫ v)) ∧ ∀ (m : ℕ) (v : Fin m → (Sp (DualNumber S) ⟶ t.G.left)) (cf : Fin m → S) (w : Sp (DualNumber S) ⟶ t.G.left), IsCombAtG t x v cf w → IsCombAtG t x' (fun i => spMap (dualMap φ) ≫ v i) (fun i => φ (cf i)) (spMap (dualMap φ) ≫ w) := by
  intro E _ _ _ H X t S S' _ _ φ x x' hx
  subst hx
  refine ⟨fun v hv => ?_, fun m v cf w h => ?_⟩
  · obtain ⟨h1, h2⟩ := hv
    refine ⟨?_, ?_⟩
    · rw [Category.assoc, h1, ← Category.assoc, spMap_comp_spMap', dualMap_comp_algebraMap, ← spMap_comp_spMap',
        Category.assoc]
    · rw [← Category.assoc, spMap_comp_spMap', fstHom_comp_dualMap, ← spMap_comp_spMap', Category.assoc, h2]
      have e : (Over.homMk (spMap φ) rfl : Over.mk (spMap φ ≫ x) ⟶ Over.mk x) ≫ (1 : Over.mk x ⟶ t.G) = 1 := by
        simp [Hom.one_def]
      rw [← e, Over.comp_left]
      rfl
  · obtain ⟨u, hu, hp⟩ := h
    let q : tEpsG (spMap φ ≫ x) ⟶ tEpsG x := Over.homMk (spMap (Formalism.L2.Pj.dualMap φ)) (by
      show spMap (Formalism.L2.Pj.dualMap φ) ≫ spMap (algebraMap S (DualNumber S)) ≫ x =
        spMap (algebraMap S' (DualNumber S')) ≫ spMap φ ≫ x
      rw [← Category.assoc, ← Category.assoc, spMap_comp_spMap', spMap_comp_spMap', dualMap_comp_algebraMap])
    refine ⟨fun i => q ≫ u i, fun i => ?_, ?_⟩
    · show spMap (Formalism.L2.Pj.dualMap φ) ≫ (u i).left = _
      rw [hu i, ← Category.assoc, spMap_comp_spMap', dualMap_comp_epsMul', ← spMap_comp_spMap', Category.assoc]
    · have e : List.ofFn (fun i => q ≫ u i) = (List.ofFn u).map (q ≫ ·) := by
        rw [List.map_ofFn]
        rfl
      rw [e, list_prod_comp', Over.comp_left, hp]
      rfl

end GlobalTheory.TanBaseChange
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentDerivativeLinearInKodairaSpencerMatrixOfI
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
open scoped Classical

namespace GlobalTheory.LogPole

theorem exists_snd_ev_eq_sum_of_ksIso : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} (TF : TorFlag Xo c) (K : Type) [Field K] [Algebra c.F K] (P₀ : FrPt Xo c K), KSIso (psiSet H) P₀ → ∀ (U : TF.Y.X.Opens), ⊤ ≤ (frX P₀ ≫ TF.Y.j) ⁻¹ᵁ U → ∃ δ : HIx Dw (psiSet H) → Γ(TF.Y.X, U) → K, ∀ (y' : Sp (DualNumber K) ⟶ Xo.XF c) (hy : ⊤ ≤ (y' ≫ TF.Y.j) ⁻¹ᵁ U), y' ≫ pullback.snd _ _ = spMap (algebraMap c.F (DualNumber K)) → spMap (FlagTan.red c K).toRingHom ≫ y' = frX P₀ → ∀ (M : HIx Dw (psiSet H) → K), FlagTan.IsKS (psiSet H) P₀ (y' ≫ pullback.fst _ _) M → ∀ r, (ev (y' ≫ TF.Y.j) U hy r).snd = ∑ k, M k * δ k r := by
  intro E _ _ _ H Dw l Xo c TF K _ _ P₀ hKS U hU
  obtain ⟨X, hX, hP, hk⟩ := hKS
  let S := TrivSqZeroExt K (HIx Dw (psiSet H) → K)
  obtain ⟨XF, h1, h2⟩ : ∃ XF : Sp S ⟶ Xo.XF c, XF ≫ pullback.fst _ _ = X ∧
      XF ≫ pullback.snd _ _ = spMap (algebraMap c.F S) :=
    ⟨pullback.lift X (spMap (algebraMap c.F S)) (hX.trans (GlobalTheory.DualEval.spMap_comp_ring _ _)),
      pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have hred : ∀ M : HIx Dw (psiSet H) → K, spMap (FlagTan.red c K).toRingHom ≫
      spMap (FlagTan.dir c M).toRingHom ≫ XF = frX P₀ := fun M => by
    have e : (FlagTan.red c K).toRingHom.comp (FlagTan.dir c M).toRingHom =
        (TrivSqZeroExt.fstHom c.F K (HIx Dw (psiSet H) → K)).toRingHom :=
      RingHom.ext fun a => FlagTan.fst_dir (c := c) M a
    rw [← Category.assoc, ← GlobalTheory.DualEval.spMap_comp_ring, e]
    refine GlobalTheory.FlagMod.eq_frX P₀ (by rw [Category.assoc, h1, hP]) ?_
    rw [Category.assoc, h2, ← GlobalTheory.DualEval.spMap_comp_ring]
    exact congrArg spMap (TrivSqZeroExt.fstHom c.F K (HIx Dw (psiSet H) → K)).comp_algebraMap
  have hmem : ∀ M : HIx Dw (psiSet H) → K,
      ⊤ ≤ (spMap (FlagTan.dir c M).toRingHom ≫ XF ≫ TF.Y.j) ⁻¹ᵁ U := fun M =>
    le_preimage_of_dualNumber (FlagTan.red c K).toRingHom _ _ (by
      rw [← Category.assoc (spMap (FlagTan.dir c M).toRingHom), ← Category.assoc, hred]
      exact hU)
  refine ⟨fun k r => (ev _ U (hmem (Pi.single k 1)) r).snd, fun y' hy hs hr M hM r => ?_⟩
  have ht : FlagTan.IsTanX P₀ (y' ≫ pullback.fst _ _) := by
    refine ⟨?_, by rw [← Category.assoc, hr, GlobalTheory.FlagMod.frX_fst]⟩
    rw [Category.assoc, pullback.condition, ← Category.assoc, hs]
    exact (GlobalTheory.DualEval.spMap_comp_ring _ _).symm
  have e : y' = spMap (FlagTan.dir c M).toRingHom ≫ XF := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, h1]
      exact ((hk _ ht).2 M).1 hM
    · rw [Category.assoc, h2, hs, ← GlobalTheory.DualEval.spMap_comp_ring]
      exact congrArg spMap (FlagTan.dir c M).comp_algebraMap.symm
  subst e
  exact GlobalTheory.DualEval.evalPt_snd_sum (XF ≫ TF.Y.j) (TrivSqZeroExt.fstHom c.F K (HIx Dw (psiSet H) → K)).toRingHom
    (fun k => (FlagTan.dir c (Pi.single k (1 : K))).toRingHom) (FlagTan.dir c M).toRingHom M
    (fun k s => FlagTan.fst_dir (c := c) _ s) (fun s => FlagTan.fst_dir (c := c) _ s)
    (fun s => by
      refine (FlagTan.snd_dir (c := c) M s).trans (Finset.sum_congr rfl fun k _ => ?_)
      rw [mul_comm]
      refine congrArg (M k * ·) ((FlagTan.snd_dir (c := c) (Pi.single k (1 : K)) s).trans ?_).symm
      simp [Pi.single_apply]) U r (hmem M) fun k => hmem _

end GlobalTheory.LogPole
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentFrameBaseChange
section
set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

namespace GlobalTheory.FlatModel.LiftBC

theorem isCombAtG_unique {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}}
    (t : SAB H X) {S : Type} [CommRing S] {x : Sp S ⟶ X} {m : ℕ} {v : Fin m → (Sp (DualNumber S) ⟶ t.G.left)}
    {a : Fin m → S} {w₁ w₂ : Sp (DualNumber S) ⟶ t.G.left} (h₁ : IsCombAtG t x v a w₁) (h₂ : IsCombAtG t x v a w₂) :
    w₁ = w₂ := by
  obtain ⟨u₁, hu₁, hw₁⟩ := h₁
  obtain ⟨u₂, hu₂, hw₂⟩ := h₂
  have hu : u₁ = u₂ := funext fun i => Over.OverMorphism.ext ((hu₁ i).trans (hu₂ i).symm)
  rw [← hw₁, ← hw₂, hu]

theorem eq_bc_of_isCombAtG : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l' : Level H}
    {Xo' : Moduli Dw l'} {c' : Coeff l'} {W : ValuationSubring ℂ} (Y : Model Xo' c' (c'.V W).subtype) {L k : Type}
    [CommRing L] [CommRing k] (φ : L →+* k) (yL : Sp L ⟶ Xo'.XF c') {g : ℕ}
    (e : Fin g → (Sp (DualNumber L) ⟶ Y.t.G.left)) (cf : Fin g → L) (w : Sp (DualNumber L) ⟶ Y.oF.t.G.left)
    (w' : Sp (DualNumber k) ⟶ Y.oF.t.G.left),
    IsCombAtG Y.t (yL ≫ Y.j) e cf (w ≫ Y.m.φ) →
    IsCombAtG Y.t (spMap φ ≫ yL ≫ Y.j) (bcV Y.t φ e) (fun b => φ (cf b)) (w' ≫ Y.m.φ) →
    w' = spMap (dualMap φ) ≫ w := by
  intro E _ _ _ H Dw l' Xo' c' W Y L k _ _ φ yL g e cf w w' h₁ h₂
  have h₁' := GlobalTheory.LocM.Cht.FlagBase.isCombAtG_bc Y.t φ h₁
  have hφ : w' ≫ Y.m.φ = (spMap (dualMap φ) ≫ w) ≫ Y.m.φ := by
    rw [Category.assoc]
    exact isCombAtG_unique Y.t h₂ h₁'
  haveI : IsOpenImmersion Y.j := GlobalTheory.TriplesAlong.isOpenImmersion_j W Y
  have hc := Y.m.cart.1
  have hb : w' ≫ Y.oF.t.G.hom = (spMap (dualMap φ) ≫ w) ≫ Y.oF.t.G.hom := by
    rw [← cancel_mono Y.j]
    simp only [Category.assoc]
    have hw := hc.w
    change Y.m.φ ≫ Y.t.G.hom = Y.oF.t.G.hom ≫ Y.j at hw
    rw [← hw, ← Category.assoc, hφ, Category.assoc, Category.assoc]
  exact hc.hom_ext hφ hb

end GlobalTheory.FlatModel.LiftBC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentNormalizedHaarLeTwoMulLieHaarStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tangentNormalizedHaar_le_two_mul_lieHaar : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (hG : G.det ≠ 0) (lam : Measure (realLie Ψ G)) [lam.IsAddHaarMeasure], ∃ δ : ℝ, 0 < δ ∧ ∀ s : Set (realLie Ψ G), MeasurableSet s → s ⊆ Metric.ball 0 δ → tangentHaar (realSU Ψ G) (lam.map Subtype.val) (GlobalTheory.SUVol.DensOne.chartExp Ψ G hG '' s) ≤ 2 * lam s := by
  first | exact @GlobalTheory.CovTop.VolUp.UpDens.tangentHaar_le_two_mul_lam | exact GlobalTheory.CovTop.VolUp.UpDens.tangentHaar_le_two_mul_lam | (intros; apply GlobalTheory.CovTop.VolUp.UpDens.tangentHaar_le_two_mul_lam <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentTransportEquivariantCartesianPreservesCom
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.EqvTrans

theorem epsMul_comp_algebraMap {R : Type} [CommRing R] (c : R) :
    spMap (epsMul c) ≫ spMap (algebraMap R (DualNumber R)) = spMap (algebraMap R (DualNumber R)) := by
  simp only [spMap, ← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext (RingHom.ext fun a => by ext <;> simp [epsMul, TrivSqZeroExt.algebraMap_eq_inl])

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
  {X Y : Scheme.{0}} {t : SAB H Y} {p : X ⟶ Y} {G' : Over X} [GrpObj G'] {ψ : G'.left ⟶ t.G.left}

theorem trv_epsMul (hψ : IsPullback ψ G'.hom t.G.hom p) (g : G'.left ⟶ G'.left) {R : Type} [CommRing R]
    (q : Sp R ⟶ X) (c : R) {v : Sp (DualNumber R) ⟶ t.G.left}
    (hv : v ≫ t.G.hom = spMap (algebraMap R (DualNumber R)) ≫ q ≫ p) :
    trv hψ g q (spMap (epsMul c) ≫ v) = spMap (epsMul c) ≫ trv hψ g q v := by
  obtain ⟨w, hw, hw'⟩ := exists_lift hψ q hv
  rw [trv_eq hψ g q w hw hw', trv_eq hψ g q (spMap (epsMul c) ≫ w) (by rw [Category.assoc, hw])
    (by rw [Category.assoc, hw', ← Category.assoc, epsMul_comp_algebraMap])]
  simp only [Category.assoc]

end GlobalTheory.EqvTrans

open MonObj GlobalTheory.EqvTrans in

theorem GlobalTheory.EqvTrans.trv_comb : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X Y : Scheme.{0}} (t : SAB H Y) (p : X ⟶ Y) (G' : Over X) [GrpObj G'] (ψ : G'.left ⟶ t.G.left) (b : X ⟶ X) (g : G'.left ⟶ G'.left) (hG : IsGrpPullback G' t.G p ψ), IsGrpPullback G' G' b g → ∀ {R : Type} [CommRing R] (q : Sp R ⟶ X) {n : ℕ} (v : Fin n → (Sp (DualNumber R) ⟶ t.G.left)) (a : Fin n → R) (w : Sp (DualNumber R) ⟶ t.G.left), (∀ i, IsTanAtG t (q ≫ p) (v i)) → IsTanAtG t (q ≫ p) w → IsCombAtG t (q ≫ p) v a w → IsCombAtG t ((q ≫ b) ≫ p) (fun i => GlobalTheory.EqvTrans.trv hG.1 g q (v i)) a (GlobalTheory.EqvTrans.trv hG.1 g q w) := by
  intro E _ _ _ H X Y t p G' _ ψ b g hG hg R _ q n v a w hv _ hc
  obtain ⟨u, hu, hw⟩ := hc

  let T : Over X := Over.mk (spMap (algebraMap R (DualNumber R)) ≫ q)
  let e1 : Over.mk (T.hom ≫ p) ⟶ tEpsG (q ≫ p) := Over.homMk (𝟙 _) (by simp [T])
  let T' : Over X := Over.mk (T.hom ≫ b)
  let e2 : Over.mk (T'.hom ≫ p) ⟶ tEpsG ((q ≫ b) ≫ p) := Over.homMk (𝟙 _) (by simp [T, T'])
  have hov : ∀ x : tEpsG (q ≫ p) ⟶ t.G,
      x.left ≫ t.G.hom = spMap (algebraMap R (DualNumber R)) ≫ q ≫ p := fun x => by
    simpa using Over.w x

  let L : (tEpsG (q ≫ p) ⟶ t.G) → (T ⟶ G') := fun x =>
    Over.homMk (hG.1.lift x.left T.hom (by rw [hov x]; simp [T])) (hG.1.lift_snd _ _ _)
  have hL : ∀ x, (L x).left ≫ ψ = x.left := fun x => hG.1.lift_fst _ _ _
  have hLw : ∀ x, (L x).left ≫ G'.hom = spMap (algebraMap R (DualNumber R)) ≫ q := fun x => Over.w (L x)
  have hgw : g ≫ G'.hom = G'.hom ≫ b := hg.1.w

  let Φ : (tEpsG (q ≫ p) ⟶ t.G) → (tEpsG ((q ≫ b) ≫ p) ⟶ t.G) := fun x =>
    Over.homMk (trv hG.1 g q x.left) (by
      have := trv_over hG.1 g hgw q (hov x)
      simpa using this)
  have hΦ : ∀ x, (Φ x).left = (L x).left ≫ g ≫ ψ := fun x => trv_eq hG.1 g q (L x).left (hL x) (hLw x)

  let M : (tEpsG (q ≫ p) ⟶ t.G) → (T' ⟶ G') := fun x =>
    Over.homMk ((L x).left ≫ g) (by
      show ((L x).left ≫ g) ≫ G'.hom = T.hom ≫ b
      rw [Category.assoc, hgw, ← Category.assoc, Over.w])
  have hmul : ∀ x y, Φ (x * y) = Φ x * Φ y := fun x y => by
    have h1 : ((e1 ≫ x) * (e1 ≫ y)).left = (L x * L y).left ≫ ψ :=
      hG.2 T (L x) (L y) (e1 ≫ x) (e1 ≫ y) (by simp [e1, hL]) (by simp [e1, hL])
    rw [← MonObj.comp_mul] at h1
    have h1' : (L x * L y).left ≫ ψ = (x * y).left := by rw [← h1]; simp [e1]
    have h2 : (M x * M y).left = (L x * L y).left ≫ g :=
      hg.2 T (L x) (L y) (M x) (M y) rfl rfl
    have h3 : ((e2 ≫ Φ x) * (e2 ≫ Φ y)).left = (M x * M y).left ≫ ψ :=
      hG.2 T' (M x) (M y) (e2 ≫ Φ x) (e2 ≫ Φ y) (by simp [e2, hΦ, M]) (by simp [e2, hΦ, M])
    rw [← MonObj.comp_mul, h2] at h3
    apply Over.OverMorphism.ext
    have h4 : (Φ (x * y)).left = (L x * L y).left ≫ g ≫ ψ :=
      trv_eq hG.1 g q (L x * L y).left h1' (Over.w (L x * L y))
    rw [h4, ← Category.assoc, ← h3]
    simp [e2]
  let Φm : (tEpsG (q ≫ p) ⟶ t.G) →* (tEpsG ((q ≫ b) ≫ p) ⟶ t.G) := MonoidHom.mk' Φ hmul
  refine ⟨fun i => Φ (u i), fun i => ?_, ?_⟩
  · show trv hG.1 g q (u i).left = _
    rw [hu i, trv_epsMul hG.1 g q (a i) (hv i).1]
  · have : (List.ofFn fun i => Φ (u i)) = (List.ofFn u).map Φm := by
      rw [List.map_ofFn]; rfl
    rw [this, ← map_list_prod]
    show trv hG.1 g q _ = _
    rw [hw]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TestPointGenericFibreStatement
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.test_point_generic_fibre : ∀ (F : Type) [Field F] [NumberField F] (V : ValuationSubring F) [IsDiscreteValuationRing V] (p : ℕ) [Fact p.Prime], (p : F) ∈ V.nonunits → ∀ (X : Scheme.{0}) (s : X ⟶ Sp V) (Xw : X.Opens), Xw ≤ X.basicOpen (p : Γ(X, ⊤)) → ∀ yb : Sp 𝓞_ℂ_[p] ⟶ X, IsTest p Xw yb → ∃ φ : V →+* 𝓞_ℂ_[p], Function.Injective φ ∧ IsLocalHom φ ∧ yb ≫ s = Spec.map (CommRingCat.ofHom φ) ∧ ∃ y : Spec (.of ℂ_[p]) ⟶ GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.genericFibre s, y ≫ GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.genericι s = Spec.map (CommRingCat.ofHom (algebraMap 𝓞_ℂ_[p] ℂ_[p])) ≫ yb := by
  first | exact @GlobalTheory.FlatModel.isTest_base_generic | exact GlobalTheory.FlatModel.isTest_base_generic | (intros; apply GlobalTheory.FlatModel.isTest_base_generic <;> assumption)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TestPointLiftProperStatement
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
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.test_point_lift_proper : ∀ (p : ℕ) [Fact p.Prime] (X X' : Scheme.{0}) (π : X' ⟶ X), IsProper π → ∀ (Xw O : X.Opens), Xw ≤ O →
    IsIso (π ∣_ O) → ∀ yb : Sp 𝓞_ℂ_[p] ⟶ X, IsTest p Xw yb → ∃ yb', IsTest p (π ⁻¹ᵁ Xw) yb' ∧ yb' ≫ π = yb := by
  first | exact @GlobalTheory.FlatModel.isTest_lift | exact GlobalTheory.FlatModel.isTest_lift | (intros; apply GlobalTheory.FlatModel.isTest_lift <;> assumption)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantsJetsChangeSectionBasisStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaConstants_jets_change_section_basis : ∀ (K : Type) [Field K] (P : PolAV (Sp K)) (hp rig hr th hth v hv th' hth' v' hv') (a : K) (M : Matrix (Fin P.g) (Fin P.g) K), (∀ i, LB.Sec.f th' i = constFn P.A.hom _ a * LB.Sec.f th i) → (∀ i, IsLieComb (M i) v (v' i)) → ∀ (m : ℕ), Odd m → (m : K) ≠ 0 → ∀ (I : Type) (pt : I → (baseOver (Sp K) ⟶ P.A)) (ϑ ϑ' : I → K) (J J' : I → Fin P.g → K), ThJet ⟨P, hp, rig, hr, th, hth, v, hv⟩ rfl m pt ϑ J → ThJet ⟨P, hp, rig, hr, th', hth', v', hv'⟩ rfl m pt ϑ' J' → (∀ i, ϑ' i = a * ϑ i) ∧ ∃ c : Fin P.g → K, ∀ i j, J' i j = a * ∑ l, M j l * J i l + c j * ϑ i := by
  first | exact @GlobalTheory.MBLow.JetUniq.thJet_change | exact GlobalTheory.MBLow.JetUniq.thJet_change | (intros; apply GlobalTheory.MBLow.JetUniq.thJet_change <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaModelChangeStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_model_change : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.ThK.ModelChange := by
  first | exact @GlobalTheory.ModelChg.modelChange | exact GlobalTheory.ModelChg.modelChange | (intros; apply GlobalTheory.ModelChg.modelChange <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToSiegAmple
section
noncomputable section

namespace GlobalTheory.UPel.HT

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {S : Scheme.{0}}

def Obj.toSieg {b : Base D R} {N : ℕ} {t : S ⟶ Sp R} (o : Obj b N t) {h M : ℕ} {B : Type} [CommRing B] {ζ : B}
    {t₁ : S ⟶ Sp B} {lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S) ⟶ o.A)} (hl : IsSympLev o.P h M ζ t₁ lev) :
    SiegPre h M ζ t₁ where
  A := o.A
  ab := o.ab
  P := o.P
  isLB := o.isLB
  rig₁ := o.rig₁
  rig₂ := o.rig₂
  symm := o.symm
  lev := lev
  lev_add := hl.1
  lev_tors := hl.2.1
  geom := hl.2.2

@[simp] theorem Obj.toSieg_A {b : Base D R} {N : ℕ} {t : S ⟶ Sp R} (o : Obj b N t) {h M : ℕ} {B : Type} [CommRing B]
    {ζ : B} {t₁ : S ⟶ Sp B} {lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S) ⟶ o.A)} (hl : IsSympLev o.P h M ζ t₁ lev) :
    (o.toSieg hl).A = o.A := rfl

theorem Obj.toSieg_ample {b : Base D R} {N : ℕ} {t : S ⟶ Sp R} (o : Obj b N t) {h M : ℕ} {B : Type} [CommRing B]
    {ζ : B} {t₁ : S ⟶ Sp B} {lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S) ⟶ o.A)} (hl : IsSympLev o.P h M ζ t₁ lev) :
    Out.RelAmple (o.toSieg hl).A (o.toSieg hl).diag := o.ample

end GlobalTheory.UPel.HT
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopFormDerivationDetPairingChangeMatrix
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

namespace GlobalTheory.LogKSDiv

theorem topPair_change_matrix : ∀ {k A : Type} [CommRing k] [CommRing A] (α : k →+* A) {n : ℕ}
    (D D' : Fin n → (letI := α.toAlgebra; Derivation k A A)) (L : Matrix (Fin n) (Fin n) A),
    (letI := α.toAlgebra; ∀ j, D j = ∑ i, L i j • D' i) →
    ∀ η, GlobalTheory.LogKSDiv.topPair α D η = L.det * GlobalTheory.LogKSDiv.topPair α D' η := by
  intro k A _ _ α n D D' L hD η
  letI := α.toAlgebra
  have key : (Matrix.detRowAlternating.compLinearMap
      (LinearMap.pi fun j => (KaehlerDifferential.linearMapEquivDerivation k A).symm (D j)) :
        (Ω[A⁄k]) [⋀^Fin n]→ₗ[A] A) =
      L.det • Matrix.detRowAlternating.compLinearMap
      (LinearMap.pi fun j => (KaehlerDifferential.linearMapEquivDerivation k A).symm (D' j)) := by
    ext v
    simp only [AlternatingMap.compLinearMap_apply, AlternatingMap.smul_apply, smul_eq_mul]
    change Matrix.det (Matrix.of fun i j =>
        (KaehlerDifferential.linearMapEquivDerivation k A).symm (D j) (v i)) =
      L.det * Matrix.det (Matrix.of fun i j =>
        (KaehlerDifferential.linearMapEquivDerivation k A).symm (D' j) (v i))
    rw [mul_comm, ← Matrix.det_mul]
    congr 1
    ext i j
    simp only [Matrix.of_apply, Matrix.mul_apply, hD j, map_sum, map_smul,
      LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun l _ => ?_
    ring
  show (exteriorPower.alternatingMapLinearEquiv _ : _ →ₗ[A] A) η = L.det * (exteriorPower.alternatingMapLinearEquiv _ : _ →ₗ[A] A) η
  rw [key, map_smul, LinearMap.smul_apply, smul_eq_mul]

end GlobalTheory.LogKSDiv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopFormOrderRationalPullbackOfEssentiallyEtaleStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.topFormOrder_rationalPullback_of_essentiallyEtale : ∀ (M W : Scheme.{0}) [IsIntegral M] [IsIntegral W] (p : W ⟶ Sp ℂ) (f : M ⟶ W) [IsDominant f] (n : ℕ) [LocallyOfFiniteType p], topologicalKrullDim W = n → ∀ (E : DivOver p) (E' : DivOver (f ≫ p)) (h : ∀ x ∈ E.ring, functionFieldMap f x ∈ E'.ring), ((functionFieldMap f).restrict E.ring E'.ring h).FormallyEtale → (∀ g : W.functionFieldˣ, E'.ord (Units.map (functionFieldMap f).toMonoidHom g) = E.ord g) → ∀ η : RatForms p n, η ≠ 0 → E'.formOrd (GlobalTheory.EtaleKlt.ratPull p f n η) = E.formOrd η := by
  first | exact @GlobalTheory.EtaleKlt.formOrd_ratPull | exact GlobalTheory.EtaleKlt.formOrd_ratPull | (intros; apply GlobalTheory.EtaleKlt.formOrd_ratPull <;> assumption)
end

