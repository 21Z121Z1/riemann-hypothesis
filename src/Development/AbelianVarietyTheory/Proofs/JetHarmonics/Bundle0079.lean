import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsAdicColimitOfFactor
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueIsPointOfDualNumber
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.GtActIffEqGtSmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0012
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.JetLemmaStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.Bundle0001
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0001
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0004
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0074
import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.RealPlaceAnalysis.Bundle0003
import Formalism.RealPlaceAnalysis.Bundle0002
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0073
import Formalism.HermitianCurvature.Bundle0005
import Formalism.RealPlaceAnalysis.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0001
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0075
import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsAdicColimitSpecOfIsLocalRing
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.FormalPoint

namespace GlobalTheory.AdicColimit

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry in

theorem _root_.GlobalTheory.AdicColimit.isAdicColimit_spec_of_isLocalRing (R : Type) [CommRing R] (I : Ideal R) (A : Type) [CommRing A]
    [IsLocalRing A] (φ : R →+* A) (hA : IsAdicComplete (I.map φ) A) :
    _root_.GlobalTheory.AdicColimit.IsAdicColimit I (Over.mk (Spec.map (CommRingCat.ofHom φ))) := by
  have hthick : ∀ e : ℕ, _root_.ReciprocityTheory.ChartRestriction.G.Out.thickTrans R I e ≫ _root_.ReciprocityTheory.ChartRestriction.G.Out.thick R I (e + 1) = _root_.ReciprocityTheory.ChartRestriction.G.Out.thick R I e := by
    intro e
    unfold _root_.ReciprocityTheory.ChartRestriction.G.Out.thickTrans _root_.ReciprocityTheory.ChartRestriction.G.Out.thick
    rw [← Spec.map_comp]
    rfl
  have hPV : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap φ = Spec.map (CommRingCat.ofHom φ) := rfl
  have hC : ∀ e, _root_.GlobalTheory.AdicColimit.thickι I e (Over.mk (Spec.map (CommRingCat.ofHom φ))) =
      pullback.fst (Spec.map (CommRingCat.ofHom φ)) (_root_.ReciprocityTheory.ChartRestriction.G.Out.thick R I e) := fun e => rfl
  have hD_fst : ∀ e, _root_.ReciprocityTheory.ChartRestriction.G.Out.thickMap R I e (Over.mk (Spec.map (CommRingCat.ofHom φ))) ≫
      pullback.fst (Spec.map (CommRingCat.ofHom φ)) (_root_.ReciprocityTheory.ChartRestriction.G.Out.thick R I (e + 1)) =
      pullback.fst (Spec.map (CommRingCat.ofHom φ)) (_root_.ReciprocityTheory.ChartRestriction.G.Out.thick R I e) := by
    intro e; exact pullback.lift_fst _ _ _
  have hD_snd : ∀ e, _root_.ReciprocityTheory.ChartRestriction.G.Out.thickMap R I e (Over.mk (Spec.map (CommRingCat.ofHom φ))) ≫
      pullback.snd (Spec.map (CommRingCat.ofHom φ)) (_root_.ReciprocityTheory.ChartRestriction.G.Out.thick R I (e + 1)) =
      pullback.snd (Spec.map (CommRingCat.ofHom φ)) (_root_.ReciprocityTheory.ChartRestriction.G.Out.thick R I e) ≫ _root_.ReciprocityTheory.ChartRestriction.G.Out.thickTrans R I e := by
    intro e; exact pullback.lift_snd _ _ _
  have hcond : ∀ e, pullback.fst (Spec.map (CommRingCat.ofHom φ)) (_root_.ReciprocityTheory.ChartRestriction.G.Out.thick R I e) ≫
      Spec.map (CommRingCat.ofHom φ) =
      pullback.snd (Spec.map (CommRingCat.ofHom φ)) (_root_.ReciprocityTheory.ChartRestriction.G.Out.thick R I e) ≫ _root_.ReciprocityTheory.ChartRestriction.G.Out.thick R I e :=
    fun e => pullback.condition
  have hq : ∀ e, _root_.GlobalTheory.FormalPoint.levelMap I φ e ≫ _root_.ReciprocityTheory.ChartRestriction.G.Out.thick R I e =
      _root_.GlobalTheory.adicLevelι (I.map φ) (e + 1) ≫ Spec.map (CommRingCat.ofHom φ) := fun e => by
    rw [_root_.GlobalTheory.FormalPoint.levelMap_thick, hPV]
  obtain ⟨s, hs_fst, hs_snd⟩ : ∃ s : ∀ e : ℕ, Spec (CommRingCat.of (A ⧸ I.map φ ^ (e + 1))) ⟶
      pullback (Spec.map (CommRingCat.ofHom φ)) (_root_.ReciprocityTheory.ChartRestriction.G.Out.thick R I e),
      (∀ e, s e ≫ pullback.fst _ _ = _root_.GlobalTheory.adicLevelι (I.map φ) (e + 1)) ∧
      (∀ e, s e ≫ pullback.snd _ _ = _root_.GlobalTheory.FormalPoint.levelMap I φ e) :=
    ⟨fun e => pullback.lift _ _ (hq e).symm, fun e => pullback.lift_fst _ _ _,
      fun e => pullback.lift_snd _ _ _⟩
  have hsec : ∀ e, ∃ l, l ≫ s e = 𝟙 _ := by
    intro e
    obtain ⟨l, hl⟩ := _root_.GlobalTheory.FormalPoint.exists_factor_level I φ
      (pullback.fst (Spec.map (CommRingCat.ofHom φ)) (_root_.ReciprocityTheory.ChartRestriction.G.Out.thick R I e))
      (pullback.snd _ _) (by rw [hPV]; exact hcond e)
    refine ⟨l, ?_⟩
    apply pullback.hom_ext
    · rw [Category.assoc, hs_fst, Category.id_comp, hl]
    · rw [← cancel_mono (_root_.ReciprocityTheory.ChartRestriction.G.Out.thick R I e), Category.assoc, Category.assoc, ← Category.assoc (s e), hs_snd, hq,
        ← Category.assoc, hl, Category.id_comp, hcond]
  intro X f hf
  have hfam : _root_.GlobalTheory.IsAdicFamily (I.map φ) (fun e => s e ≫ f e) := by
    intro n
    have hmap : _root_.GlobalTheory.adicLevelMap (I.map φ) (by omega : n + 1 ≤ n + 1 + 1) ≫ s (n + 1) =
        s n ≫ _root_.ReciprocityTheory.ChartRestriction.G.Out.thickMap R I n (Over.mk (Spec.map (CommRingCat.ofHom φ))) := by
      apply pullback.hom_ext
      · rw [Category.assoc, hs_fst, _root_.GlobalTheory.adicLevelMap_ι, Category.assoc, hD_fst, hs_fst]
      · rw [← cancel_mono (_root_.ReciprocityTheory.ChartRestriction.G.Out.thick R I (n + 1))]
        simp only [Category.assoc]
        rw [← Category.assoc (s (n + 1)), hs_snd, hq, _root_.GlobalTheory.adicLevelMap_ι_assoc, ← Category.assoc (_root_.ReciprocityTheory.ChartRestriction.G.Out.thickMap R I n (Over.mk (Spec.map (CommRingCat.ofHom φ)))), hD_snd,
          Category.assoc, hthick, ← Category.assoc, hs_snd, hq]
    show _root_.GlobalTheory.adicLevelMap (I.map φ) _ ≫ s (n + 1) ≫ f (n + 1) = s n ≫ f n
    rw [← Category.assoc, hmap, Category.assoc, hf]
  haveI := hA
  obtain ⟨g, hg, hgu⟩ := _root_.GlobalTheory.existsUnique_of_isAdicFamily hfam
  have key : ∀ y : Spec (CommRingCat.of A) ⟶ X,
      (∀ e, _root_.GlobalTheory.AdicColimit.thickι I e (Over.mk (Spec.map (CommRingCat.ofHom φ))) ≫ y = f e) ↔
      (∀ n, _root_.GlobalTheory.adicLevelι (I.map φ) (n + 1) ≫ y = s n ≫ f n) := by
    intro y
    constructor
    · intro hy n
      rw [← hs_fst, Category.assoc, ← hC, hy]
    · intro hy e
      obtain ⟨l, hl⟩ := hsec e
      have h1 : _root_.GlobalTheory.AdicColimit.thickι I e (Over.mk (Spec.map (CommRingCat.ofHom φ))) =
          l ≫ _root_.GlobalTheory.adicLevelι (I.map φ) (e + 1) := by
        rw [← hs_fst, ← Category.assoc, hl, Category.id_comp, hC]
      rw [h1, Category.assoc, hy, ← Category.assoc, hl]
      exact Category.id_comp _
  exact ⟨g, (key g).2 hg, fun y hy => hgu y ((key y).1 hy)⟩

end GlobalTheory.AdicColimit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsSmulPtSmulPt
section
noncomputable section

namespace GlobalTheory.TorusModel

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.TorusExt GlobalTheory.FormalPoint

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {T T' : Over (Spec (CommRingCat.of R))}

abbrev cv (g : GtPt D T) (χ : D.X) (y : T.left) (J : (T.left ⟶ D.P.A.left) → D.P.L.ι) :
    (T.left.presheaf.stalk y)ˣ := val (g.s χ) (𝟙 T.left) y J

theorem pt_ext {g g' : GtPt D T} (hb : g.b = g'.b)
    (h : ∀ χ y J, Good D.P.L y J → cv g χ y J = cv g' χ y J) : g = g' := by
  obtain ⟨b, s, hs, _, _⟩ := g
  obtain ⟨b', s', hs', _, _⟩ := g'
  obtain rfl : b = b' := hb
  obtain rfl : s = s' := funext fun χ => TorusCoord.gen_eq_of_corr D.P.isLB (hs χ) (hs' χ)
    (corr_of_val D.P.isLB (h χ))
  rfl

theorem prod_pt (b : T ⟶ D.P.A) (χ : D.X) {U : Type} [CommGroup U] (h : (T.left ⟶ D.P.A.left) → U) :
    ∏ i, h (DegPre.gtφT D T b χ i) ^ DegPre.gtε i =
      (h (cP D _ χ * b).left)⁻¹ * h (cP D _ χ).left * h b.left * (h (1 : T ⟶ D.P.A).left)⁻¹ := by
  simp [DegPre.gtφT, DegPre.gtε, Fin.prod_univ_four]
  rfl

theorem val_cubAtT {y : T.left} {J} (hJ : Good D.P.L y J) (x x' w : T ⟶ D.P.A) :
    val (DegPre.cubAtT D T x x' w) (𝟙 _) y J = th D y J x x' w := by
  have := val_cub D.cub (𝟙 T) hJ x x' w
  rwa [Category.id_comp, Category.id_comp, Category.id_comp] at this

theorem cv_zero (g : GtPt D T) {y J} (hJ : Good D.P.L y J) : cv g 0 y J = 1 :=
  (val_corr hJ g.s_zero _).trans (val_one _)

theorem cv_add (g : GtPt D T) {y J} (hJ : Good D.P.L y J) (χ χ' : D.X) :
    cv g (χ + χ') y J * th D y J (cP D _ χ) (cP D _ χ') g.b = cv g χ y J * cv g χ' y J :=
  ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_cubAtT hJ _ _ _))).symm.trans
    ((val_corr hJ (g.mult χ χ') _).trans (val_mul hJ _ _ _))

theorem exists_pt (b : T ⟶ D.P.A) {K : Type} [Fintype K] {φ : D.X → K → (T.left ⟶ D.P.A.left)}
    {ε : K → ℤ} (v : ∀ χ, LB.Gen (LB.LinComb D.P.L (φ χ) ε)) (hv : ∀ χ, (v χ).IsGen)
    (hF : ∀ χ, FormEq (φ χ) ε (DegPre.gtφT D T b χ) DegPre.gtε)
    (h₀ : ∀ y J, Good D.P.L y J → val (v 0) (𝟙 _) y J = 1)
    (hm : ∀ χ χ' y J, Good D.P.L y J → val (v (χ + χ')) (𝟙 _) y J * th D y J (cP D _ χ) (cP D _ χ') b =
      val (v χ) (𝟙 _) y J * val (v χ') (𝟙 _) y J) :
    ∃ g : GtPt D T, g.b = b ∧ ∀ χ (Z : Scheme.{0}) (r : Z ⟶ T.left) y J, Good D.P.L y J →
      val (g.s χ) r y J = val (v χ) r y J := by
  choose s hs vs using fun χ => exists_gen D.P.isLB (hF χ) (v χ) (hv χ)
  refine ⟨⟨b, s, hs, corr_of_val D.P.isLB fun y J hJ => ?_, fun χ χ' => corr_of_val D.P.isLB fun y J hJ => ?_⟩, rfl,
    fun χ Z r y J hJ => vs χ _ _ y J hJ⟩
  · exact (vs 0 _ _ y J hJ).trans ((h₀ y J hJ).trans (val_one _).symm)
  · exact (val_mul hJ _ _ _).trans ((congrArg₂ (· * ·) (vs _ _ _ y J hJ) (val_cubAtT hJ _ _ _)).trans
      ((hm χ χ' y J hJ).trans
      ((congrArg₂ (· * ·) (vs _ _ _ y J hJ) (vs _ _ _ y J hJ)).symm.trans (val_mul hJ _ _ _).symm)))

theorem isAdd_iff (g g' g'' : GtPt D T) : g.IsAdd g' g'' ↔ g''.b = g.b * g'.b ∧ ∀ χ y J, Good D.P.L y J →
    cv g'' χ y J * th D y J (cP D _ χ) g.b g'.b = cv g χ y J * cv g' χ y J :=
  and_congr Iff.rfl (forall_congr' fun _ => ⟨fun h _ _ hJ =>
    ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_cubAtT hJ _ _ _))).symm.trans
      ((val_corr hJ h _).trans (val_mul hJ _ _ _)),
    fun h => corr_of_val D.P.isLB fun y J hJ => ((val_mul hJ _ _ _).trans
      (congrArg₂ (· * ·) rfl (val_cubAtT hJ _ _ _))).trans ((h y J hJ).trans (val_mul hJ _ _ _).symm)⟩)

theorem isAdd_unique {g g' h h' : GtPt D T} (e : g.IsAdd g' h) (e' : g.IsAdd g' h') : h = h' := by
  rw [isAdd_iff] at e e'
  exact pt_ext (e.1.trans e'.1.symm) fun χ y J hJ => mul_right_cancel ((e.2 χ y J hJ).trans (e'.2 χ y J hJ).symm)

theorem isPull_iff (k : T' ⟶ T) (g : GtPt D T) (g' : GtPt D T') : GtPt.IsPull k.left g g' ↔
    g'.b = k ≫ g.b ∧ ∀ χ y J, Good D.P.L y J → cv g' χ y J = val (g.s χ) k.left y J :=
  and_congr ⟨fun h => Over.OverMorphism.ext h, fun h => congrArg (·.left) h⟩ (forall_congr' fun _ =>
    ⟨fun h _ _ hJ => (val_corr hJ h _).trans ((val_pull hJ _ _ _).trans (by rw [Category.id_comp])),
      fun h => corr_of_val D.P.isLB fun y J hJ => (h y J hJ).trans
        ((val_pull hJ _ _ _).trans (by rw [Category.id_comp])).symm⟩)

theorem isPull_unique {k : T' ⟶ T} {g : GtPt D T} {h h' : GtPt D T'} (e : GtPt.IsPull k.left g h)
    (e' : GtPt.IsPull k.left g h') : h = h' := by
  rw [isPull_iff] at e e'
  exact pt_ext (e.1.trans e'.1.symm) fun χ y J hJ => (e.2 χ y J hJ).trans (e'.2 χ y J hJ).symm

variable {O : Type} [CommRing O] [StarRing O] [Module O D.X] (hG : GlobalFnsSt) (oa : D.OAct O)

theorem val_smul (a : O) (g : GtPt D T)
    (u : LB.Gen (LB.LinComb D.P.L (rosatiφ D.P.A (oa.onB.act (star a)) (oa.onB.act a)) rosatiε)) (χ : D.X)
    (k : T' ⟶ T) {y J} (hJ : Good D.P.L y J) : val (LB.mulGen D.P.L _ _ _ _ (g.s (star a • χ))
        (LB.pullGen D.P.L _ _ u (lift (cP D _ χ) g.b).left)) k.left y J =
      val (g.s (star a • χ)) k.left y J * val₂ u y J (cP D _ χ) (k ≫ g.b) :=
  (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl ((val_pull_pair u k hJ _ _).trans (by rw [comp_cP])))

theorem val_smul' (a : O) (g : GtPt D T)
    (u : LB.Gen (LB.LinComb D.P.L (rosatiφ D.P.A (oa.onB.act (star a)) (oa.onB.act a)) rosatiε)) (χ : D.X)
    {y J} (hJ : Good D.P.L y J) : val (LB.mulGen D.P.L _ _ _ _ (g.s (star a • χ))
        (LB.pullGen D.P.L _ _ u (lift (cP D _ χ) g.b).left)) (𝟙 T.left) y J =
      cv g (star a • χ) y J * val₂ u y J (cP D _ χ) g.b := by
  simpa using val_smul oa a g u χ (𝟙 T) hJ

theorem isSmulPt_iff (a : O) (g g' : GtPt D T) :
    IsSmulPt oa a g g' ↔ g'.b = g.b ≫ oa.onB.act a ∧ ∀ χ y J, Good D.P.L y J →
      cv g' χ y J = cv g (star a • χ) y J * val₂ (rosGen hG oa a) y J (cP D _ χ) g.b := by
  refine and_congr Iff.rfl ⟨fun h χ y J hJ => ?_, fun h u hu u₀ χ => corr_of_val D.P.isLB fun y J hJ => ?_⟩
  · exact (val_corr hJ (h _ (rosGen_isRos hG oa a).1 (rosGen_isRos hG oa a).2 χ) _).symm.trans
      (val_smul' oa a g _ χ hJ)
  · exact (val_smul' oa a g u χ hJ).trans ((congrArg₂ (· * ·) rfl
      (IsRos.unique hG D.P.isAb D.P.isLB ⟨hu, u₀⟩ (rosGen_isRos hG oa a) hJ _ _)).trans (h χ y J hJ).symm)

include hG in
theorem exists_isSmulPt (a : O) (g : GtPt D T) : ∃ g', IsSmulPt oa a g g' := by
  have := oa.onB.hom (star a)
  have vv := fun χ y J (hJ : Good D.P.L y J) => val_smul' oa a g (rosGen hG oa a) χ hJ
  obtain ⟨g', hb, hv⟩ := exists_pt (g.b ≫ oa.onB.act a) (fun χ => LB.mulGen D.P.L _ _ _ _ (g.s (star a • χ))
      (LB.pullGen D.P.L _ _ (rosGen hG oa a) (lift (cP D _ χ) g.b).left))
    (fun χ => mulGen_isGen _ _ _ _ _ _ _ (g.isGen _) (pullGen_isGen _ _ _ _ (rosGen_isRos hG oa a).1 _))
    (fun χ U _ h => by
      refine (prod_sum₂ (K := Fin 4) (K' := Fin 6) (U := U) _ (prod_pt g.b (star a • χ) h)
        (prod_ros _ _ (cP D _ χ) g.b h)).trans ?_
      rw [prod_pt, cPoint_smul oa]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel) (fun y J hJ => by
      have C : IsCub (th D (T := T) y J) := isCub_cubV D.cub hJ
      have e := (rosGen_add hG oa a hJ 1 1 g.b).1
      rw [_root_.mul_one, MonObj.one_comp, C.face, C.face, _root_.mul_one, _root_.one_mul] at e
      refine (vv 0 y J hJ).trans ?_
      rw [smul_zero, cPoint_zero, mul_eq_left.1 e.symm, _root_.mul_one, cv_zero g hJ]) (fun χ χ' y J hJ => by
      have e₁ := congrArg Additive.ofMul (rosGen_add hG oa a hJ (cP D _ χ) (cP D _ χ') g.b).1
      have e := cv_add g hJ (star a • χ) (star a • χ')
      rw [cPoint_smul oa, cPoint_smul oa] at e
      have e₂ := congrArg Additive.ofMul e
      refine (congrArg₂ (· * ·) (vv _ y J hJ) rfl).trans (Eq.trans ?_ (congrArg₂ (· * ·) (vv _ y J hJ) (vv _ y J hJ)).symm)
      rw [smul_add, cPoint_add]
      apply Additive.ofMul.injective
      simp only [ofMul_mul] at e₁ e₂ ⊢
      linear_combination (norm := abel) e₁ + e₂)
  exact ⟨g', (isSmulPt_iff hG oa _ _ _).2 ⟨hb, fun χ y J hJ => (hv χ _ _ y J hJ).trans (vv χ y J hJ)⟩⟩

def smulPt (a : O) (g : GtPt D T) : GtPt D T := (exists_isSmulPt hG oa a g).choose

theorem isSmulPt_smulPt (a : O) (g : GtPt D T) : IsSmulPt oa a g (smulPt hG oa a g) :=
  (exists_isSmulPt hG oa a g).choose_spec

theorem smulPt_b (a : O) (g : GtPt D T) : (smulPt hG oa a g).b = g.b ≫ oa.onB.act a :=
  ((isSmulPt_iff hG oa a g _).1 (isSmulPt_smulPt hG oa a g)).1

theorem smulPt_val (a : O) (g : GtPt D T) (χ : D.X) {y J} (hJ : Good D.P.L y J) :
    cv (smulPt hG oa a g) χ y J = cv g (star a • χ) y J * val₂ (rosGen hG oa a) y J (cP D _ χ) g.b :=
  ((isSmulPt_iff hG oa a g _).1 (isSmulPt_smulPt hG oa a g)).2 χ y J hJ

theorem smulPt_pull (a : O) (k : T' ⟶ T) {g : GtPt D T} {g' : GtPt D T'} (h : GtPt.IsPull k.left g g') :
    GtPt.IsPull k.left (smulPt hG oa a g) (smulPt hG oa a g') := by
  obtain ⟨b, v⟩ := (isPull_iff _ _ _).1 h
  refine (isPull_iff _ _ _).2 ⟨by rw [smulPt_b, smulPt_b, b, Category.assoc], fun χ y J hJ => ?_⟩
  rw [smulPt_val hG oa a _ χ hJ, v _ y J hJ, b]
  exact (val_smul oa a g _ χ k hJ).symm.trans (val_corr hJ ((isSmulPt_smulPt hG oa a g).2 _
    (rosGen_isRos hG oa a).1 (rosGen_isRos hG oa a).2 χ) _)

theorem smulPt_add (a : O) {g g' g'' : GtPt D T} (h : g.IsAdd g' g'') :
    (smulPt hG oa a g).IsAdd (smulPt hG oa a g') (smulPt hG oa a g'') := by
  have := oa.onB.hom a
  obtain ⟨b, v⟩ := (isAdd_iff _ _ _).1 h
  refine (isAdd_iff _ _ _).2 ⟨?_, fun χ y J hJ => ?_⟩
  · rw [smulPt_b, smulPt_b, smulPt_b, b, MonObj.mul_comp]
  · have e₁ := congrArg Additive.ofMul (rosGen_add hG oa a hJ g.b g'.b (cP D _ χ)).2
    have e := v (star a • χ) y J hJ
    rw [cPoint_smul oa] at e
    have e₂ := congrArg Additive.ofMul e
    rw [smulPt_val hG oa a _ χ hJ, smulPt_val hG oa a _ χ hJ, smulPt_val hG oa a _ χ hJ, smulPt_b, smulPt_b, b]
    apply Additive.ofMul.injective
    simp only [ofMul_mul] at e₁ e₂ ⊢
    linear_combination (norm := abel) e₁ + e₂

theorem one_smulPt (g : GtPt D T) : smulPt hG oa 1 g = g :=
  pt_ext (by rw [smulPt_b, oa.onB.map_one, Category.comp_id]) fun χ y J hJ => by
    rw [smulPt_val hG oa _ _ χ hJ, IsRos.val_id hG D.P.isAb D.P.isLB (by rw [star_one, oa.onB.map_one])
      oa.onB.map_one (rosGen_isRos hG oa 1) hJ, star_one, one_smul, _root_.mul_one]

theorem mul_smulPt (a a' : O) (g : GtPt D T) : smulPt hG oa (a * a') g = smulPt hG oa a (smulPt hG oa a' g) := by
  have := oa.onB.hom a'
  have := oa.onB.hom (star a)
  refine pt_ext (by rw [smulPt_b, smulPt_b, smulPt_b, oa.onB.map_mul, Category.assoc]) fun χ y J hJ => ?_
  rw [smulPt_val hG oa _ _ χ hJ, smulPt_val hG oa _ _ χ hJ, smulPt_val hG oa _ _ _ hJ,
    IsRos.val_comp hG D.P.isAb D.P.isLB (by rw [star_mul, oa.onB.map_mul]) (oa.onB.map_mul a a')
      (rosGen_isRos hG oa (a * a')) (rosGen_isRos hG oa a) (rosGen_isRos hG oa a') hJ,
    smulPt_b, cPoint_smul oa, star_mul, mul_smul, _root_.mul_assoc]

theorem add_smulPt (a a' : O) (g : GtPt D T) :
    (smulPt hG oa a g).IsAdd (smulPt hG oa a' g) (smulPt hG oa (a + a') g) := by
  have := oa.onB.hom a
  have := oa.onB.hom (star a)
  refine (isAdd_iff _ _ _).2 ⟨?_, fun χ y J hJ => ?_⟩
  · rw [smulPt_b, smulPt_b, smulPt_b, oa.onB.map_add]; exact MonObj.comp_mul _ _ _
  · have e₁ := congrArg Additive.ofMul (IsRos.val_sum hG D.P.isAb D.cub
      (by rw [star_add]; exact oa.onB.map_add _ _) (oa.onB.map_add a a')
      (rosGen_isRos hG oa (a + a')) (rosGen_isRos hG oa a) (rosGen_isRos hG oa a') hJ (cP D _ χ) g.b)
    have e := cv_add g hJ (star a • χ) (star a' • χ)
    rw [cPoint_smul oa, cPoint_smul oa, ← add_smul, ← star_add] at e
    have e₂ := congrArg Additive.ofMul e
    rw [smulPt_val hG oa _ _ χ hJ, smulPt_val hG oa _ _ χ hJ, smulPt_val hG oa _ _ χ hJ, smulPt_b, smulPt_b]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, th] at e₁ e₂ ⊢
    linear_combination (norm := abel) e₁ + e₂

def Represents {H : Over (Spec (CommRingCat.of R))} [GrpObj H] (Φ : ∀ T, (T ⟶ H) ≃ GtPt D T) : Prop :=
  (∀ (T' T : Over (Spec (CommRingCat.of R))) (k : T' ⟶ T) (x : T ⟶ H),
    GtPt.IsPull k.left (Φ T x) (Φ T' (k ≫ x))) ∧
  ∀ (T : Over (Spec (CommRingCat.of R))) (x x' : T ⟶ H), GtPt.IsAdd (Φ T x) (Φ T x') (Φ T (x * x'))

include hG in

theorem exists_ringAct {H : Over (Spec (CommRingCat.of R))} [GrpObj H] [IsCommMonObj H]
    {Φ : ∀ T, (T ⟶ H) ≃ GtPt D T} (h : Represents Φ) :
    ∃ ρ : RingAct H O, ∀ (a : O) (T) (x : T ⟶ H), IsSmulPt oa a (Φ T x) (Φ T (x ≫ ρ.act a)) := by
  let act : O → (H ⟶ H) := fun a => (Φ H).symm (smulPt hG oa a (Φ H (𝟙 H)))
  have key : ∀ (a : O) {T} (x : T ⟶ H), Φ T (x ≫ act a) = smulPt hG oa a (Φ T x) := fun a T x => by
    have e₁ := h.1 T H x (act a)
    have e₂ := smulPt_pull hG oa a x (h.1 T H x (𝟙 H))
    rw [Category.comp_id] at e₂
    rw [Equiv.apply_symm_apply] at e₁
    exact isPull_unique e₁ e₂
  have mul : ∀ (a : O) {T} (x x' : T ⟶ H), (x * x') ≫ act a = (x ≫ act a) * (x' ≫ act a) := fun a T x x' => by
    have e₁ := h.2 T (x ≫ act a) (x' ≫ act a)
    rw [key, key] at e₁
    exact (Φ T).injective ((key a _).trans (isAdd_unique (smulPt_add hG oa a (h.2 T x x')) e₁))
  refine ⟨⟨act, fun a => ⟨?_, ?_⟩, ?_, fun a b => ?_, fun a b => ?_⟩, fun a T x => ?_⟩
  · have e := mul a (1 : 𝟙_ _ ⟶ H) 1
    rw [_root_.mul_one] at e
    have e' := mul_eq_left.1 e.symm
    simpa [Hom.one_def] using e'
  · have e := mul a (fst H H) (snd H H)
    rw [Hom.mul_def, Hom.mul_def, lift_fst_snd, Category.id_comp] at e
    rw [e]
    congr 1
  · exact (Φ H).injective (by rw [← Category.id_comp (act 1), key, one_smulPt])
  · exact (Φ H).injective (by
      rw [← Category.id_comp (act (a * b)), key, mul_smulPt, key, ← Category.id_comp (act b), key])
  · have e₁ := h.2 H (act a) (act b)
    have k := fun a => (congrArg (Φ H) (Category.id_comp (act a))).symm.trans (key a (𝟙 H))
    rw [k, k] at e₁
    exact (Φ H).injective ((k _).trans (isAdd_unique (add_smulPt hG oa a b _) e₁))
  · rw [key]
    exact isSmulPt_smulPt hG oa a _

end GlobalTheory.TorusModel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.KerJetAugEqSpanTorusUnionQuotient
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace JetGenerators

theorem exists_tangent {k A : Type} [Field k] [CommRing A] [Algebra k A] (aug : A →ₐ[k] k)
    {I : Ideal A} {n : ℕ} (hJ : (RingHom.ker aug) ^ (n + 1) = ⊥) (hI : I ≤ RingHom.ker aug)
    (hne : ¬ RingHom.ker aug ≤ I) :
    ∃ φ : A →ₐ[k] DualNumber k, (TrivSqZeroExt.fstHom k k k).comp φ = aug ∧ (∀ a ∈ I, φ a = 0) ∧
      ∃ a ∈ RingHom.ker aug, φ a ≠ 0 := by
  first
  | exact @_root_.GlobalTheory.NotLeSqSup.main
  | exact _root_.GlobalTheory.NotLeSqSup.main
  | (apply _root_.GlobalTheory.NotLeSqSup.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.NotLeSqSup.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NotLeSqSup.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NotLeSqSup.main ..)

theorem spMap_jetAug {k : Type} [CommRing k] {G : Over (Spec (CommRingCat.of k))} [GrpObj G] {d : ℕ}
    {x : ∀ m : ℕ, Chart.sp (R₀ := k) (Chart.JetR k (Fin d) m) ⟶ G} (hx : Chart.IsUnivChart G d x)
    (n : ℕ) {A : Type} [CommRing A] [Algebra k A] :
    Chart.spMap ((Algebra.ofId k A).comp (Chart.jetAug k (Fin d) n)) ≫ x n = 1 := by
  have : (Algebra.ofId k A).comp (Chart.jetAug k (Fin d) n) =
      ((Algebra.ofId k A).comp (Chart.jetAug k (Fin d) 0)).comp (Chart.jetZeroR k (Fin d) n) := by
    apply Chart.jet_ext
    intro j
    rfl
  rw [this, ← Chart.spMap_comp, Category.assoc, hx.2.1 n, MonObj.comp_one]

theorem eq_one_of_basis {S : Scheme.{0}} {X : Type} [AddCommGroup X] {κ : Type}
    (b : Module.Basis κ ℤ X) {Z : Over S} (y : Z ⟶ splitTorus S X)
    (h : ∀ j, y.left.appTop.hom (charUnit S X (b j)).val = 1) : y = 1 := by
  obtain ⟨e, he⟩ := exists_splitTorus_points_mulEquiv S X Z
  apply e.injective
  rw [map_one]
  have h1 : (MonoidHom.toAdditiveRight (e y)).toIntLinearMap = 0 := by
    apply b.ext
    intro j
    change Additive.ofMul (e y (Multiplicative.ofAdd (b j))) = Additive.ofMul 1
    congr 1
    exact Units.ext ((he y (b j)).trans (h j))
  refine MonoidHom.ext fun χ => ?_
  exact congrArg Additive.toMul (LinearMap.congr_fun h1 χ.toAdd)

end JetGenerators

theorem ker_jetAug_eq_span_torus_union_quotient :
    ∀ (k : Type) [Field k] (X : Type) [AddCommGroup X] (r : ℕ) (b : Module.Basis (Fin r) ℤ X) (G B : Over (Spec (CommRingCat.of k))) [GrpObj G] [GrpObj B] (q : G ⟶ B) (i : splitTorus (Spec (CommRingCat.of k)) X ⟶ G), IsMonHom q → IsMonHom i → IsPullback i (toUnit _) q η[B] → ∀ (d g n : ℕ) (x : ∀ m : ℕ, Chart.sp (R₀ := k) (Chart.JetR k (Fin d) m) ⟶ G) (xB : ∀ m : ℕ, Chart.sp (R₀ := k) (Chart.JetR k (Fin g) m) ⟶ B), Chart.IsUnivChart G d x → Chart.IsUnivChart B g xB → ∀ (ψ : (Chart.JetR k (Fin g) n) →ₐ[k] (Chart.JetR k (Fin d) n)), x n ≫ q = Chart.spMap ψ ≫ xB n → ∀ T : Fin r → (Chart.JetR k (Fin d) n), (∀ j, Chart.jetAug k (Fin d) n (T j) = 0) → (∀ (φ : (Chart.JetR k (Fin d) n) →ₐ[k] DualNumber k) (y : Chart.sp (R₀ := k) (DualNumber k) ⟶ splitTorus (Spec (CommRingCat.of k)) X), Chart.spMap φ ≫ x n = y ≫ i → ∀ j, (Scheme.ΓSpecIso (CommRingCat.of (DualNumber k))).inv.hom (1 + φ (T j)) = y.left.appTop.hom (charUnit (Spec (CommRingCat.of k)) X (b j)).val) → RingHom.ker (Chart.jetAug k (Fin d) n) = Ideal.span (Set.range T ∪ Set.range fun l => ψ (Chart.zR n l)) := by
  intro k _ X _ r b G B _ _ q i hq hi hpb d g n x xB hx hxB ψ hψ T hT hchar
  have hI : Ideal.span (Set.range T ∪ Set.range fun l => ψ (Chart.zR n l)) ≤
      RingHom.ker (Chart.jetAug k (Fin d) n) := by
    rw [Ideal.span_le]
    rintro _ (⟨j, rfl⟩ | ⟨l, rfl⟩)
    · exact hT j
    · have hz : IsNilpotent (Chart.zR (R := k) n l) := ⟨n + 1, by
        have := Ideal.pow_mem_pow (Chart.zR_mem_ker (R := k) n l) (n + 1)
        rwa [Chart.ker_jetAug_pow, Ideal.mem_bot] at this⟩
      exact ((hz.map ψ).map (Chart.jetAug k (Fin d) n)).eq_zero
  refine le_antisymm ?_ hI
  by_contra hne
  obtain ⟨φ, hφ1, hφ2, a, haJ, ha⟩ :=
    JetGenerators.exists_tangent _ (Chart.ker_jetAug_pow (R := k) (Fin d) n) hI hne
  have hn : n ≠ 0 := by
    rintro rfl
    have : RingHom.ker (Chart.jetAug k (Fin d) 0) = ⊥ :=
      (pow_one _).symm.trans (Chart.ker_jetAug_pow (R := k) (Fin d) 0)
    exact hne (this ▸ bot_le)
  have hφψ : φ.comp ψ = (Algebra.ofId k (DualNumber k)).comp (Chart.jetAug k (Fin g) n) := by
    apply Chart.jet_ext
    intro l
    rw [AlgHom.comp_apply, AlgHom.comp_apply, Chart.jetAug_zR, map_zero]
    exact hφ2 _ (Ideal.subset_span (Or.inr ⟨l, rfl⟩))
  have hq1 : (Chart.spMap φ ≫ x n) ≫ q = toUnit _ ≫ η[B] := by
    rw [Category.assoc, hψ, ← Category.assoc, Chart.spMap_comp, hφψ, JetGenerators.spMap_jetAug hxB]
    rfl
  have hy := (hpb.lift_fst _ _ hq1).symm
  have hy1 : hpb.lift _ _ hq1 = 1 := by
    apply JetGenerators.eq_one_of_basis b
    intro j
    rw [← hchar φ _ hy j, hφ2 _ (Ideal.subset_span (Or.inl ⟨j, rfl⟩)), add_zero, map_one]
  rw [hy1, MonObj.one_comp] at hy
  have hker : (RingHom.ker (TrivSqZeroExt.fstHom k k k)) ^ (n + 1) = ⊥ := by
    rw [← le_bot_iff]
    refine (Ideal.pow_le_pow_right (show 2 ≤ n + 1 by omega)).trans ?_
    rw [pow_two, Ideal.mul_le]
    intro u hu v hv
    have hu' : u.fst = 0 := hu
    have hv' : v.fst = 0 := hv
    rw [Ideal.mem_bot]
    ext <;> simp [hu', hv']
  have huniq := (hx.2.2 (DualNumber k) (TrivSqZeroExt.fstHom k k k) n hker 1
    (MonObj.comp_one _)).unique (y₁ := φ)
    (y₂ := (Algebra.ofId k (DualNumber k)).comp (Chart.jetAug k (Fin d) n)) ⟨hφ1, hy.symm⟩
    ⟨by ext1 z; simp, (JetGenerators.spMap_jetAug hx n).symm⟩
  apply ha
  have h0 : Chart.jetAug k (Fin d) n a = 0 := haJ
  rw [huniq, AlgHom.comp_apply, h0, map_zero]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.RightOperatorDualMemOfInfiniteStatement
section
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rightOperatorDual_mem_of_infinite : ∀ (P : M.Par) (A : Type) [Ring A] [StarRing A] [Algebra ℂ A] (d : Q.NFData P A) (K : Submodule ℂ A) (S : Set ℂ), S.Infinite → (∀ y ∈ S, rhv d y ∈ K) → ∀ y : ℂ, rhv d y ∈ K := by
  first | exact @GlobalTheory.RhvPoly.rhv_mem_of_infinite | exact GlobalTheory.RhvPoly.rhv_mem_of_infinite | (intros; apply GlobalTheory.RhvPoly.rhv_mem_of_infinite <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.SmoothVectorsDiscreteSeriesGlModuleStatement
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smoothVectors_discreteSeries_glModule : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDS ε mu → ∀ Q : Mx k r, IsUnit Q → ∃ E : (Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ R.smSub), R.IsE Q E ∧ Formalism.REAL.GlRel E := by
  first | exact @GlobalTheory.smooth_gl_module | exact GlobalTheory.smooth_gl_module | (intros; apply GlobalTheory.smooth_gl_module <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.StarProjectionSplitCasimirRaisingLastStatement
section
open Formalism.REAL Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.starProjection_splitCasimir_raising_last : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (n : ℕ) (E : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V) (Et : Fin (n + 1) → Fin (n + 1) → Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V))) (Om : Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V))) (β : ℂ) (L : Fin (n + 1) → ℤ) (l : Fin (n + 1)), Hyp E β L → (∀ a b x y, inner ℂ (E a b x) y = inner ℂ x (E b a y)) → (∀ a b y c, Et a b y c = E a b (y c) + if c = a then y b else 0) → (∀ y b, Om y b = ∑ c, E c b (y c)) → ∀ (M : Fin n → ℤ) (v : V), v ∈ CapSp (subA E) (shf β M) → (Module.End.eigenspace Om (β + L l + 0)).starProjection (PiLp.single 2 (Fin.last n) v) (Fin.last n) = (GlobalTheory.WigSh.wP L M l : ℂ) • v := by
  first | exact @GlobalTheory.starProjection_splitCasimirStd_last | exact GlobalTheory.starProjection_splitCasimirStd_last | (intros; apply GlobalTheory.starProjection_splitCasimirStd_last <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.TruncationFramesLocalSeriesStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.truncation_frames_local_series : LinkEpsSt := by
  first | exact @GlobalTheory.LinkEps.linkEps | exact GlobalTheory.LinkEps.linkEps | (intros; apply GlobalTheory.LinkEps.linkEps <;> assumption)
end

