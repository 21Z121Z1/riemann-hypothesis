import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2770
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2621
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0034
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0141
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsNsmulIffEq
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0088
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationEndomorphismsToCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThickenedPointToTorusExtensionGenerator
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2738
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCocycleUnit
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusCoordinateValueEqOfMapsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torusCoordinate_value_eq_of_maps : ∀ {R' : Type} [CommRing R'] [IsDomain R'] {I' : Ideal R'} {D' : DegPre R'} {e : ℕ} {G' : Over (Spec (CommRingCat.of R'))} [GrpObj G'] [IsCommMonObj G'] (g : GtCoord I' D' e G') (F : D'.P.A.left ⟶ D'.P.A.left) (w : LB.Iso D'.P.L (D'.P.L.pull F)) (f f' : (thickObj R' I' e G').left ⟶ (thickObj R' I' e G').left) (x : D'.X) (hψ : ∀ k : Fin 4, D'.Oφ g.pG x k ≫ F = f ≫ D'.Oφ g.pG x k) (hψ' : ∀ k : Fin 4, D'.Oφ g.pG x k ≫ F = f' ≫ D'.Oφ g.pG x k), LB.Gen.Maps (LB.linCombIso w _ Oinvε) (g.t x) (GeneratorPullback.pullAlong D'.P.L F f _ Oinvε _ hψ (g.t x)) → LB.Gen.Maps (LB.linCombIso w _ Oinvε) (g.t x) (GeneratorPullback.pullAlong D'.P.L F f' _ Oinvε _ hψ' (g.t x)) → ∀ (z : (thickObj R' I' e G').left) (J : ((thickObj R' I' e G').left ⟶ D'.P.A.left) → D'.P.L.ι), Good D'.P.L z J → val (g.t x) f z J = val (g.t x) f' z J := by
  first | exact @GlobalTheory.Mum.gtCoord_val_eq_of_maps | exact GlobalTheory.Mum.gtCoord_val_eq_of_maps | (intros; apply GlobalTheory.Mum.gtCoord_val_eq_of_maps <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusCoordinatesCompareNormalisedGenerators
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

namespace GlobalTheory.Mum.Two

open CoordCompare TorusCoord in

theorem exists_level_ratio {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D₁ D₂ : DegPre R} {e : ℕ}
    {G₁ G₂ : Over (Sp R)} [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂]
    (g₁ : GtCoord I D₁ e G₁) (g₂ : GtCoord I D₂ e G₂) (a : thickObj R I e G₁ ⟶ thickObj R I e G₂) [IsMonHom a]
    (b : D₁.P.A ⟶ D₂.P.A) (h : D₂.X → D₁.X)
    (t : splitTorus (Sp (R ⧸ I ^ (e + 1))) D₁.X ⟶ splitTorus (Sp (R ⧸ I ^ (e + 1))) D₂.X)
    (ht : TorusHomOf h t) (hi : g₁.i ≫ a = t ≫ g₂.i) (hq : a ≫ g₂.q = g₁.q ≫ (Over.pullback (thick R I e)).map b)
    (χ : D₂.X) :
    ∃ u : LB.Gen (LB.LinComb (JN D₁ D₂) (Y := (thickObj R I e D₁.P.A).left)
      (fun k => pullback.fst D₁.P.A.hom (thick R I e) ≫
        Sum.elim (fun k => D₁.Oφ (𝟙 _) (h χ) k ≫ coprod.inl) (fun k => D₂.Oφ b χ k ≫ coprod.inr) k)
      (Sum.elim Oε Oinvε)), u.IsGen ∧
      ∀ (Z : Scheme.{0}) (x : Z ⟶ (thickObj R I e G₁).left) (z : Z) (J), Good (JN D₁ D₂) z J →
        val (g₂.t χ) (x ≫ a.left) z (rr J) = val (g₁.t (h χ)) x z (rl J) * val u (x ≫ g₁.q.left) z J := by
  have := g₁.q_flat
  have := g₁.q_surj
  have := g₁.q_affine
  have p₁ := isPart_inl D₁.P.L D₂.P.L
  have p₂ := isPart_inr D₁.P.L D₂.P.L
  have hp : (Over.map (thick R I e)).map a ≫ g₂.pG = g₁.pG ≫ b := by
    refine Over.OverMorphism.ext ?_
    have h1 : a.left ≫ g₂.q.left = g₁.q.left ≫ ((Over.pullback (thick R I e)).map b).left :=
      congrArg (fun q => q.left) hq
    have h2 : ((Over.pullback (thick R I e)).map b).left ≫ pullback.fst D₂.P.A.hom (thick R I e) =
        pullback.fst D₁.P.A.hom (thick R I e) ≫ b.left := pullback.lift_fst _ _ _
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) h1).trans ((Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) h2).trans (Category.assoc _ _ _).symm)))
  have e₁ : ∀ k, a.left ≫ D₂.Oφ g₂.pG χ k =
      g₁.q.left ≫ pullback.fst D₁.P.A.hom (thick R I e) ≫ D₂.Oφ b χ k := fun k =>
    (WeightPf.Oφ_comp ((Over.map (thick R I e)).map a) g₂.pG χ k).trans
      ((congrArg (D₂.Oφ · χ k) hp).trans
        ((WeightPf.Oφ_comp g₁.pG b χ k).symm.trans (Category.assoc _ _ _)))
  have e₂ : ∀ k, D₁.Oφ g₁.pG (h χ) k =
      g₁.q.left ≫ pullback.fst D₁.P.A.hom (thick R I e) ≫ D₁.Oφ (𝟙 _) (h χ) k := fun k =>
    (congrArg (D₁.Oφ · (h χ) k) (Category.comp_id g₁.pG).symm).trans
      ((WeightPf.Oφ_comp g₁.pG (𝟙 _) (h χ) k).symm.trans (Category.assoc _ _ _))
  obtain ⟨u, hu, hu'⟩ := exists_gen (jn_isLB D₁ D₂)
    (φ' := fun k => g₁.q.left ≫ pullback.fst D₁.P.A.hom (thick R I e) ≫
      Sum.elim (fun k => D₁.Oφ (𝟙 _) (h χ) k ≫ coprod.inl) (fun k => D₂.Oφ b χ k ≫ coprod.inr) k)
    (ε' := Sum.elim Oε Oinvε)
    (fun U _ f => by
      refine (Fintype.prod_sum_type _).trans (Eq.trans ?_ (Fintype.prod_sum_type _).symm)
      refine congrArg₂ (· * ·) (Finset.prod_congr rfl fun k _ => ?_) (Finset.prod_congr rfl fun k _ => ?_)
      · refine congrArg₂ (· ^ ·) (congrArg f ?_) (show -Oinvε k = Oε k by fin_cases k <;> rfl)
        exact (congrArg (· ≫ coprod.inl) (e₂ k)).trans
          ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (Category.assoc _ _ _)))
      · refine congrArg (fun ψ => f ψ ^ Oinvε k) ?_
        exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ coprod.inr) (e₁ k)).trans
          ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (Category.assoc _ _ _)))))
    (LB.mulGen (JN D₁ D₂) _ _ _ _ (LB.invGen (JN D₁ D₂) _ _ (p₁.gen (g₁.t (h χ))))
      (LB.pullGen (JN D₁ D₂) _ _ (p₂.gen (g₂.t χ)) a.left))
    (mulGen_isGen _ _ _ _ _ _ _ (invGen_isGen _ _ _ _ (p₁.gen_isGen (g₁.t_gen _)))
      (pullGen_isGen _ _ _ _ (p₂.gen_isGen (g₂.t_gen χ)) _))
  have hv : ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G₁).left) (z : Z) (J), Good (JN D₁ D₂) z J →
      val u r z J = (val (g₁.t (h χ)) r z (rl J))⁻¹ * val (g₂.t χ) (r ≫ a.left) z (rr J) := fun Z r z J hJ =>
    (hu' Z r z J hJ).trans ((Geo.Tor.val_mul hJ _ _ _).trans
      (congrArg₂ (· * ·) ((Geo.Tor.val_inv _ _).trans (congrArg (·⁻¹) (p₁.val_gen _ _ z hJ)))
        ((Geo.Tor.val_pull hJ _ _ _).trans (p₂.val_gen _ _ z hJ))))
  obtain ⟨v, hv₁, hv₂⟩ := exists_gen_of_val_eq (jn_isLB D₁ D₂) _ _ g₁.q.left u hu (fun Z r r' z J hJ hr => by
    rw [hv Z r z J hJ, hv Z r' z J hJ]
    have hw : r ≫ (thickObj R I e G₁).hom = r' ≫ (thickObj R I e G₁).hom := by
      rw [← Over.w g₁.q, reassoc_of% hr]
    let Z' : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) := Over.mk (r' ≫ (thickObj R I e G₁).hom)
    let c : Z' ⟶ thickObj R I e G₁ := Over.homMk r hw
    let c' : Z' ⟶ thickObj R I e G₁ := Over.homMk r' rfl
    obtain ⟨τ, hτ⟩ := exists_torus g₁ c c' (Over.OverMorphism.ext hr)
    have hτa : c ≫ a = ((τ ≫ t) ≫ g₂.i) * (c' ≫ a) := by
      rw [hτ, MonObj.mul_comp, Category.assoc, hi, Category.assoc]
    have v₁ := val_torus g₁ (h χ) (Z := Z') (p₁.good hJ) τ c'
    have v₂ := val_torus g₂ χ (Z := Z') (p₂.good hJ) (τ ≫ t) (c' ≫ a)
    rw [← hτ] at v₁
    rw [← hτa] at v₂
    have v₀ : gm (τ ≫ t).left z ⊤ (charUnit _ D₂.X χ) = gm τ.left z ⊤ (charUnit _ D₁.X (h χ)) :=
      (gm_pull τ.left t.left z ⊤ trivial _).symm.trans
        ((gm_res τ.left z (V := ⊤) (U := t.left ⁻¹ᵁ ⊤) (fun _ _ => trivial) trivial _).symm.trans (congrArg _ (ht χ)))
    refine (congrArg₂ (fun s s' => s⁻¹ * s') v₁ v₂).trans ?_
    rw [v₀, mul_inv, _root_.mul_mul_mul_comm, inv_mul_cancel, _root_.one_mul]
    rfl)
  refine ⟨v, hv₁, fun Z x z J hJ => ?_⟩
  rw [hv₂ Z x z J hJ, hv Z x z J hJ, mul_inv_cancel_left]

theorem prod_unit_hom {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) {B : Over (Sp R)} [GrpObj B] (p : B ⟶ D.P.A)
    [IsMonHom p] (χ : D.X) {U : Type} [CommGroup U] (h : (Spec (CommRingCat.of R) ⟶ D.P.A.left) → U) :
    ∏ k, h (eSec B ≫ D.Oφ p χ k) ^ Oinvε k = 1 := by
  have e0 : ∀ k, eSec B ≫ D.Oφ p χ k = eSec D.P.A ≫ D.Oφ (𝟙 _) χ k := fun k =>
    (WeightPf.Oφ_comp η[B] p χ k).trans ((congrArg (D.Oφ · χ k)
      ((IsMonHom.one_hom p).trans (Category.comp_id _).symm)).trans (WeightPf.Oφ_comp η[D.P.A] (𝟙 _) χ k).symm)
  simp only [e0]
  exact (EndData.prod_unit D (𝟙 _) χ h).2

open EndData in

theorem coord_of_lin : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I → ∀ (D₁ D₂ : DegData R I) (A₁ A₂ : PolAV (Sp (FractionRing R))) (G₁ G₂ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂] (U₁ : UnifPre I D₁ A₁ G₁) (U₂ : UnifPre I D₂ A₂ G₂) (a : G₁ ⟶ G₂) (b : D₁.toPre.P.A ⟶ D₂.toPre.P.A) (h : D₂.toPre.X →+ D₁.toPre.X), Lin U₁ U₂ a b h → Coord U₁ U₂ a b h := by
  intro R _ _ I hR D₁ D₂ A₁ A₂ G₁ G₂ _ _ _ _ U₁ U₂ a b h ⟨ha, hb, hq, hh⟩ χ
  have hC := hR.2.2.2
  have hB := jn_isLB D₁.toPre D₂.toPre
  have p₁ := isPart_inl D₁.toPre.P.L D₂.toPre.P.L
  have p₂ := isPart_inr D₁.toPre.P.L D₂.toPre.P.L
  choose t ht hi using hh
  choose v hv vv using fun e => exists_level_ratio (U₁.gt e) (U₂.gt e) ((Over.pullback (thick R I e)).map a) b h (t e)
    (ht e) (hi e) (hq e) χ
  have down₁ : ∀ χ e (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G₁).left) (z : Z) (J), Good D₁.toPre.P.L z J →
      val ((U₁.gt (e + 1)).t χ) (r ≫ thickMap R I e G₁) z J = val ((U₁.gt e).t χ) r z J :=
    fun χ e Z r z J hJ => (val_pull hJ _ _ _).symm.trans (val_corr hJ (U₁.gt_t e χ) r)
  have down₂ : ∀ χ e (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G₂).left) (z : Z) (J), Good D₂.toPre.P.L z J →
      val ((U₂.gt (e + 1)).t χ) (r ≫ thickMap R I e G₂) z J = val ((U₂.gt e).t χ) r z J :=
    fun χ e Z r z J hJ => (val_pull hJ _ _ _).symm.trans (val_corr hJ (U₂.gt_t e χ) r)
  obtain ⟨u, hu, uv⟩ := T.exists_generator_of_compatible_thickening_generators R I hC D₁.toPre.P.A D₁.toPre.P.isAb.smooth
    (AbProj.isProjBy_of_isPullback D₁.toPre.P (IsPullback.id_horiz _)) _ (JN D₁.toPre D₂.toPre) _ _ _ _ hB
    (fun _ _ => rfl) v hv (fun e z J hJ => by
      have := (U₁.gt e).q_flat
      have := (U₁.gt e).q_surj
      refine val_eq_of_flat hB _ _ _ _ (fun k => ?_) (U₁.gt e).q.left (fun x J hJ => ?_) z J hJ
      · rw [← Category.assoc, trans_fst, Category.id_comp]
      · have k₁ := vv (e + 1) _ (𝟙 _ ≫ thickMap R I e G₁) x J hJ
        have k₀ := vv e _ (𝟙 _) x J hJ
        rw [down₁ _ _ _ _ _ _ (p₁.good hJ), Category.assoc, trans_map, ← Category.assoc,
          down₂ _ _ _ _ _ _ (p₂.good hJ), k₀, Category.id_comp, Category.id_comp, UnifCompare.trans_comp_q] at k₁
        rw [Category.comp_id]
        exact (mul_left_cancel k₁).symm)
  refine ⟨u, ⟨hu, fun Z r z J hJ => ?_⟩, fun e Z x z J hJ => ?_⟩
  · refine (val_pull hJ _ _ _).symm.trans ((val_corr hJ (t' := LB.oneGen _)
      (corr_of_val hB fun y J hJ => Eq.trans ?_ (val_one _).symm) r).trans (val_one _))
    refine val_eq_one I hB (fun V _ k => ?_) _ (pullGen_isGen _ _ _ _ hu _) (fun e z J hJ => ?_) y J hJ
    · refine (Fintype.prod_sum_type _).trans ((congrArg₂ (· * ·)
        (Eq.trans ?_ (prod_unit D₁.toPre (𝟙 _) (h χ) (fun ψ => k (ψ ≫ coprod.inl))).1)
        (Eq.trans ?_ (prod_unit_hom D₂.toPre b χ (fun ψ => k (ψ ≫ coprod.inr))))).trans
        ((_root_.mul_one _).trans (Fintype.prod_empty _).symm))
      · exact Finset.prod_congr rfl fun j _ => congrArg (fun ψ => k ψ ^ Oε j) (Category.assoc _ _ _).symm
      · exact Finset.prod_congr rfl fun j _ => congrArg (fun ψ => k ψ ^ Oinvε j) (Category.assoc _ _ _).symm
    · have := (U₁.gt e).q_hom
      have k := vv e _ (1 : 𝟙_ (Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) ⟶ thickObj R I e G₁).left z J hJ
      rw [← Over.comp_left, ← Over.comp_left, MonObj.one_comp, MonObj.one_comp, TorusCoord.val_unit _ _ (p₂.good hJ),
        TorusCoord.val_unit _ _ (p₁.good hJ), _root_.one_mul, ← uv e _ _ z J hJ] at k
      have o : (1 : 𝟙_ (Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) ⟶ thickObj R I e D₁.toPre.P.A) =
        η[thickObj R I e D₁.toPre.P.A] := by simp [Hom.one_def]
      rw [o] at k
      exact (val_pull hJ _ _ _).trans ((congrArg (fun p => val u p z J)
        (UnitValue.eSec_pullback_fst (thick R I e) D₁.toPre.P.A).symm).trans k.symm)
  · refine (vv e Z x z J hJ).trans (congrArg (_ * ·) ((uv e Z _ z J hJ).symm.trans ?_))
    exact congrArg (fun p => val u p z J) (Category.assoc _ _ _)

end GlobalTheory.Mum.Two
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionPointActionPeriodValueFractionFiel
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

noncomputable section

namespace GlobalTheory.Mum.Two

theorem act_val_frac : ∀ (R : Type) [CommRing R] [IsDomain R] (D₀ D' : DegPre R) (pr : D'.P.A ⟶ D₀.P.A) (h : D₀.X →+ D'.X) (F : Type) [Field F] [Algebra (FractionRing R) F] (y : D'.X) (y₀ : D₀.X) (g : GtPtF D' F) (g' : GtPtF D₀ F), GtPtF.IsIota y g → GtPtF.IsIota y₀ g' → Act D' D₀ pr h g g' → ∀ (χ : D₀.X) (u : LB.Gen (CmpLB D' D₀ pr (h χ) χ)), Nrm u → ∀ (z : (TK R).left) (J : ((TK R).left ⟶ (D'.P.A.left ⨿ D₀.P.A.left : Scheme.{0})) → (JN D' D₀).ι), Good (JN D' D₀) z J → val (D₀.tau y₀ χ) (𝟙 _) z (rr J) = val (D'.tau y (h χ)) (𝟙 _) z (rl J) * val u (ptK (D'.c y)) z J := by
  intro R _ _ D₀ D' pr h F _ _ y y₀ g g' hg hg' ha χ u hu z J hJ
  have hsurj : Surjective (jFK (R := R) F) := GlobalTheory.Balanced.surjective_spMap _
  have hflat : Flat (jFK (R := R) F) := (inferInstance : Flat (spMap (algebraMap (FractionRing R) F)))
  have hb : g.b.left = jFK (R := R) F ≫ ptK (D'.c y) := by
    rw [hg.1]
    have e : toUnit (TF (R := R) F) = (Over.homMk (jFK (R := R) F) rfl : TF (R := R) F ⟶ TK R) ≫ toUnit (TK R) :=
      toUnit_unique _ _
    show (toUnit (TF (R := R) F) ≫ D'.c y).left = _
    rw [e, Category.assoc, Over.comp_left]
    rfl

  have step1 : ∀ (z' : (TF (R := R) F).left) (J' : _), Good (JN D' D₀) z' J' →
      val (D₀.tau y₀ χ) (jFK (R := R) F) z' (rr J') =
        val (D'.tau y (h χ)) (jFK (R := R) F) z' (rl J') * val u (jFK (R := R) F ≫ ptK (D'.c y)) z' J' := by
    intro z' J' hJ'
    have g₀ := (isPart_inr D'.P.L D₀.P.L).good hJ'
    have g₁ := (isPart_inl D'.P.L D₀.P.L).good hJ'
    have e := ha.2 χ u hu z' J' hJ'
    rw [val_corr g₀ (hg'.2 χ), val_corr g₁ (hg.2 (h χ)), val_pull g₀, val_pull g₁, hb] at e
    simp only [Category.id_comp] at e
    exact e

  have p₀ := isPart_inr D'.P.L D₀.P.L
  have p₁ := isPart_inl D'.P.L D₀.P.L
  let t₀ := p₀.gen (D₀.tau y₀ χ)
  let t₂ := LB.mulGen (JN D' D₀) _ _ _ _ (p₁.gen (D'.tau y (h χ))) (LB.pullGen (JN D' D₀) _ _ u (ptK (D'.c y)))
  have key := GlobalTheory.Balanced.val_descend (jn_isLB D' D₀) t₀ t₂ (jFK (R := R) F) (fun z' J' hJ' => by
    rw [p₀.val_gen _ _ _ hJ', val_mul hJ', p₁.val_gen _ _ _ hJ', val_pull hJ']
    exact step1 z' J' hJ') z J hJ
  rw [p₀.val_gen _ _ _ hJ, val_mul hJ, p₁.val_gen _ _ _ hJ, val_pull hJ, Category.id_comp] at key
  exact key

end GlobalTheory.Mum.Two

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionPointActionPullbackData
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

namespace GlobalTheory.Mum.Two.ActPull

open GlobalTheory.ArcPull GlobalTheory.PullLinear
open GlobalTheory.PsiEvenPull (proj)

section Join

variable {X X' Y Y' : Scheme.{0}}

theorem isGen_part {N : LB X} {N' : LB X'} {M : LB Y} {M' : LB Y'} {e : Y ⟶ X} {e' : Y' ⟶ X'} {π : N.ι → M.ι}
    {π' : N'.ι → M'.ι} (h : IsPart N M e π) (h' : IsPart N' M' e' π') {Φ : X' ⟶ X} {Ψ : Y' ⟶ Y}
    (sq : e' ≫ Φ = Ψ ≫ e) (w : LB.Iso N' (N.pull Φ)) {v : LB.Iso M' (M.pull Ψ)} (hv : v.IsGen)
    (H : ∀ (x : Y') p q, Ψ x ∈ M.U (π p) → x ∈ M'.U (π' q) → gw w (𝟙 _ ≫ e') x p q = gw v (𝟙 _) x (π p) (π' q))
    (a b : (LB.div (N.pull Φ) N').ι) (x : Y')
    (hx : e' x ∈ (LB.div (N.pull Φ) N').U a ⊓ (LB.div (N.pull Φ) N').U b) :
    gm e' x _ (res (inf_le_left : (LB.div (N.pull Φ) N').U a ⊓ (LB.div (N.pull Φ) N').U b ≤ _) (w.s a)) =
      gm e' x _ ((LB.div (N.pull Φ) N').g a b *
        res (inf_le_right : (LB.div (N.pull Φ) N').U a ⊓ (LB.div (N.pull Φ) N').U b ≤ _) (w.s b)) := by
  obtain ⟨J, k⟩ := a
  obtain ⟨J', k'⟩ := b
  have pt : Φ (e' x) = e (Ψ x) := congrArg (fun q : Y' ⟶ X => q x) sq
  have hj := mem_pull.1 hx.1.1
  have hj' := mem_pull.1 hx.2.1
  have mj := (h.mem _ _).1 (pt ▸ hj)
  have mj' := (h.mem _ _).1 (pt ▸ hj')
  have mk := (h'.mem _ _).1 hx.1.2
  have mk' := (h'.mem _ _).1 hx.2.2
  have e₀ := (isGen_iff v).1 hv _ (𝟙 _) x _ _ _ _ mj mj' mk mk'
  rw [← H x _ _ mj mk, ← H x _ _ mj' mk', ← h.g _ (𝟙 _ ≫ Ψ) x _ _ mj mj', ← h'.g _ (𝟙 _) x _ _ mk mk',
    Category.id_comp, Category.id_comp, ← sq, ← gm_div_g e' x _ _ k k' hj hj' hx.1.2 hx.2.2] at e₀
  exact (gm_res _ x _ hx _).trans (e₀.trans ((map_mul _ _ _).trans (congrArg _ (gm_res _ x _ hx _))).symm)

variable {X₁ X₂ X₁' X₂' : Scheme.{0}} {M₁ : LB X₁} {M₂ : LB X₂} {M₁' : LB X₁'} {M₂' : LB X₂'} {Φ₁ : X₁' ⟶ X₁}
  {Φ₂ : X₂' ⟶ X₂}

theorem exists_join_iso {w₁ : LB.Iso M₁' (M₁.pull Φ₁)} {w₂ : LB.Iso M₂' (M₂.pull Φ₂)} (h₁ : w₁.IsGen) (h₂ : w₂.IsGen) :
    ∃ w : LB.Iso (join M₁' M₂') ((join M₁ M₂).pull (coprod.map Φ₁ Φ₂)), w.IsGen ∧
      ∀ (Z : Scheme.{0}) (z : Z) J J', Good (join M₁ M₂) z J → Good (join M₁' M₂') z J' →
        (∀ ψ, om w z J J' (ψ ≫ coprod.inl) = om w₁ z (rl J) (rl J') ψ) ∧
        ∀ ψ, om w z J J' (ψ ≫ coprod.inr) = om w₂ z (rr J) (rr J') ψ := by
  have s₁ : coprod.inl ≫ coprod.map Φ₁ Φ₂ = Φ₁ ≫ coprod.inl := coprod.inl_map _ _
  have s₂ : coprod.inr ≫ coprod.map Φ₁ Φ₂ = Φ₂ ≫ coprod.inr := coprod.inr_map _ _
  have p₁ : ∀ x, coprod.map Φ₁ Φ₂ ((coprod.inl : X₁' ⟶ _) x) = (coprod.inl : X₁ ⟶ _) (Φ₁ x) :=
    fun x => congrArg (fun q : X₁' ⟶ X₁ ⨿ X₂ => q x) s₁
  have p₂ : ∀ x, coprod.map Φ₁ Φ₂ ((coprod.inr : X₂' ⟶ _) x) = (coprod.inr : X₂ ⟶ _) (Φ₂ x) :=
    fun x => congrArg (fun q : X₂' ⟶ X₁ ⨿ X₂ => q x) s₂
  choose a ha₁ ha₂ using fun i : (LB.div ((join M₁ M₂).pull (coprod.map Φ₁ Φ₂)) (join M₁' M₂')).ι =>
    exists_glue ((LB.div ((join M₁ M₂).pull (coprod.map Φ₁ Φ₂)) (join M₁' M₂')).U i)
      ((M₁.pull Φ₁).U (fun _ => (i.1 PUnit.unit).1) ⊓ M₁'.U i.2.1)
      ((M₂.pull Φ₂).U (fun _ => (i.1 PUnit.unit).2) ⊓ M₂'.U i.2.2)
      (fun x hx => ⟨mem_pull.2 ((mem_jU_inl _ _ _).1 (p₁ x ▸ mem_pull.1 hx.1)), (mem_jU_inl _ _ _).1 hx.2⟩)
      (fun x hx => ⟨mem_pull.2 ((mem_jU_inr _ _ _).1 (p₂ x ▸ mem_pull.1 hx.1)), (mem_jU_inr _ _ _).1 hx.2⟩)
      (w₁.s (fun _ => (i.1 PUnit.unit).1, i.2.1)) (w₂.s (fun _ => (i.1 PUnit.unit).2, i.2.2))
  let w : LB.Iso (join M₁' M₂') ((join M₁ M₂).pull (coprod.map Φ₁ Φ₂)) := ⟨a⟩
  have v₁ : ∀ (Z : Scheme.{0}) (ψ : Z ⟶ X₁') (z : Z) (p : (join M₁ M₂).ι) (q : (join M₁' M₂').ι),
      Φ₁ (ψ z) ∈ M₁.U p.1 → ψ z ∈ M₁'.U q.1 → gw w (ψ ≫ coprod.inl) z p q = gw w₁ ψ z p.1 q.1 :=
    fun Z ψ z p q hp hq => ha₁ (fun _ => p, q) Z ψ z
      ⟨mem_pull.2 ((p₁ (ψ z)).symm ▸ (mem_jU_inl _ _ _).2 hp), (mem_jU_inl _ _ _).2 hq⟩
  have v₂ : ∀ (Z : Scheme.{0}) (ψ : Z ⟶ X₂') (z : Z) (p : (join M₁ M₂).ι) (q : (join M₁' M₂').ι),
      Φ₂ (ψ z) ∈ M₂.U p.2 → ψ z ∈ M₂'.U q.2 → gw w (ψ ≫ coprod.inr) z p q = gw w₂ ψ z p.2 q.2 :=
    fun Z ψ z p q hp hq => ha₂ (fun _ => p, q) Z ψ z
      ⟨mem_pull.2 ((p₂ (ψ z)).symm ▸ (mem_jU_inr _ _ _).2 hp), (mem_jU_inr _ _ _).2 hq⟩
  refine ⟨w, fun i j => unit_ext_coprod
    (isGen_part (isPart_inl M₁ M₂) (isPart_inl M₁' M₂') s₁ w h₁ (fun x => v₁ _ (𝟙 _) x) i j)
    (isGen_part (isPart_inr M₁ M₂) (isPart_inr M₁' M₂') s₂ w h₂ (fun x => v₂ _ (𝟙 _) x) i j),
    fun Z z J J' hJ hJ' => ⟨fun ψ => ?_, fun ψ => ?_⟩⟩
  · have e : (ψ ≫ coprod.inl) ≫ coprod.map Φ₁ Φ₂ = (ψ ≫ Φ₁) ≫ coprod.inl := by
      rw [Category.assoc, s₁, Category.assoc]
    rw [om, e]
    exact v₁ Z ψ z _ _ ((isPart_inl M₁ M₂).good hJ (ψ ≫ Φ₁)) ((isPart_inl M₁' M₂').good hJ' ψ)
  · have e : (ψ ≫ coprod.inr) ≫ coprod.map Φ₁ Φ₂ = (ψ ≫ Φ₂) ≫ coprod.inr := by
      rw [Category.assoc, s₂, Category.assoc]
    rw [om, e]
    exact v₂ Z ψ z _ _ ((isPart_inr M₁ M₂).good hJ (ψ ≫ Φ₂)) ((isPart_inr M₁' M₂').good hJ' ψ)

end Join

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']

theorem nrm_unique {D₁ D₂ : DegPre R} {a : D₁.P.A ⟶ D₂.P.A} {x : D₁.X} {y : D₂.X} {u u' : LB.Gen (CmpLB D₁ D₂ a x y)}
    (hu : Nrm u) (hu' : Nrm u') (Z : Scheme.{0}) (r : Z ⟶ D₁.P.A.left) (z : Z) (J) (hJ : Good (JN D₁ D₂) z J) :
    val u r z J = val u' r z J :=
  gen_unique (jn_isLB D₁ D₂) D₁.P.A.hom (eSec D₁.P.A) (Over.w η[D₁.P.A]) (GlobalTheory.globalFns_holds _ _ D₁.P.isAb).2 hu.1 hu'.1
    (fun y J hJ => by
      have e := (hu.2 _ (𝟙 _) y J hJ).trans (hu'.2 _ (𝟙 _) y J hJ).symm
      rwa [Category.id_comp] at e) Z r z J hJ

theorem act_iff_of_nrm {D₁ D₂ : DegPre R} {a : D₁.P.A ⟶ D₂.P.A} {h : D₂.X →+ D₁.X}
    (u : ∀ χ, LB.Gen (CmpLB D₁ D₂ a (h χ) χ)) (hu : ∀ χ, Nrm (u χ)) {F : Type} [Field F] [Algebra (FractionRing R) F]
    (g : GtPtF D₁ F) (g' : GtPtF D₂ F) : Act D₁ D₂ a h g g' ↔ g'.b = g.b ≫ a ∧ ∀ χ z J, Good (JN D₁ D₂) z J →
      val (g'.s χ) (𝟙 _) z (rr J) = val (g.s (h χ)) (𝟙 _) z (rl J) * val (u χ) g.b.left z J :=
  and_congr_right fun _ => forall_congr' fun χ => ⟨fun H => H _ (hu χ), fun H _ hv z J hJ =>
    (H z J hJ).trans (congrArg _ (nrm_unique (hu χ) hv _ _ z J hJ))⟩

theorem prod_Oε (D : DegPre R) {T : Over (Spec (CommRingCat.of R))} (p : T ⟶ D.P.A) (x : D.X) {U : Type} [CommGroup U]
    (h : (T.left ⟶ D.P.A.left) → U) : ∏ k, h (D.Oφ p x k) ^ Oε k = (∏ k, h (D.Oφ p x k) ^ Oinvε k)⁻¹ := by
  rw [OLinEnd.prod_Oφ, OLinEnd.prod_Oφ_inv D p]
  simp only [mul_inv, inv_inv]

variable {φ : R →+* R'} {D₁ D₂ : DegPre R} {D₁' D₂' : DegPre R'} (hD₁ : IsPullDeg φ D₁ D₁') (hD₂ : IsPullDeg φ D₂ D₂')

theorem exists_u {a : D₁.P.A ⟶ D₂.P.A} {a' : D₁'.P.A ⟶ D₂'.P.A} [IsMonHom a']
    (ha : a'.left ≫ proj hD₂ = proj hD₁ ≫ a.left) {x : D₁.X} (x' : D₁'.X) (y' : D₂'.X) (hx : hD₁.xe x' = x)
    (u : LB.Gen (CmpLB D₁ D₂ a x (hD₂.xe y'))) (hu : Nrm u) :
    ∃ u' : LB.Gen (CmpLB D₁' D₂' a' x' y'), Nrm u' ∧
      ∀ (T : Over (Spec (CommRingCat.of R'))) (p : T ⟶ D₁'.P.A) (Z : Scheme.{0}) (r : Z ⟶ T.left) (z : Z) J J',
        Good (JN D₁ D₂) z J → Good (JN D₁' D₂') z J' → val u ((r ≫ p.left) ≫ proj hD₁) z J =
          (∏ k, om hD₁.w z (rl J) (rl J') (r ≫ D₁'.Oφ p x' k) ^ Oinvε k)⁻¹ *
            (∏ k, om hD₂.w z (rr J) (rr J') (r ≫ D₂'.Oφ (p ≫ a') y' k) ^ Oinvε k) * val u' (r ≫ p.left) z J' := by
  subst hx
  obtain ⟨w, hw, vw⟩ := exists_join_iso hD₁.w_gen hD₂.w_gen
  obtain ⟨u', hu', vu⟩ := exists_down_om hw (jn_isLB D₁ D₂) (jn_isLB D₁' D₂')
    (φ' := Sum.elim (fun k => D₁'.Oφ (𝟙 _) x' k ≫ coprod.inl) (fun k => D₂'.Oφ a' y' k ≫ coprod.inr)) (proj hD₁) (by
      rintro (k | k)
      · refine (Category.assoc _ _ _).trans (Eq.trans ?_ (Category.assoc _ _ _))
        rw [coprod.inl_map, ← Category.assoc]
        exact congrArg (· ≫ _)
          (TorusCoordPull.Oφ_pull hD₁ (𝟙 _) (𝟙 _) _ ((Category.id_comp _).trans (Category.comp_id _).symm) x' k)
      · refine (Category.assoc _ _ _).trans (Eq.trans ?_ (Category.assoc _ _ _))
        rw [coprod.inr_map, ← Category.assoc]
        exact congrArg (· ≫ _) (TorusCoordPull.Oφ_pull hD₂ a a' _ ha y' k)) u hu.1
  have key : ∀ (T : Over (Spec (CommRingCat.of R'))) (p : T ⟶ D₁'.P.A) (Z : Scheme.{0}) (r : Z ⟶ T.left) (z : Z) J J',
      Good (JN D₁ D₂) z J → Good (JN D₁' D₂') z J' → val u ((r ≫ p.left) ≫ proj hD₁) z J =
        (∏ k, om hD₁.w z (rl J) (rl J') (r ≫ D₁'.Oφ p x' k) ^ Oinvε k)⁻¹ *
          (∏ k, om hD₂.w z (rr J) (rr J') (r ≫ D₂'.Oφ (p ≫ a') y' k) ^ Oinvε k) * val u' (r ≫ p.left) z J' :=
    fun T p Z r z J J' hJ hJ' => by
    refine (vu Z (r ≫ p.left) z J J' hJ hJ').trans (congrArg₂ (· * ·) ?_ rfl)
    obtain ⟨o₁, o₂⟩ := vw Z z J J' hJ hJ'
    rw [Fintype.prod_sum_type, ← prod_Oε D₁' p x' (fun q => om hD₁.w z (rl J) (rl J') (r ≫ q))]
    refine congrArg₂ (· * ·) (Finset.prod_congr rfl fun k _ => congrArg (· ^ Oε k) ?_)
      (Finset.prod_congr rfl fun k _ => congrArg (· ^ Oinvε k) ?_)
    · refine Eq.trans (congrArg _ ?_) (o₁ _)
      rw [Sum.elim_inl, ← Category.assoc, Category.assoc r, WeightPf.Oφ_comp, Category.comp_id]
    · refine Eq.trans (congrArg _ ?_) (o₂ _)
      rw [Sum.elim_inr, ← Category.assoc, Category.assoc r, WeightPf.Oφ_comp]
  refine ⟨u', ⟨hu', fun Z r z J' hJ' => ?_⟩, key⟩
  obtain ⟨J, hJ⟩ := DegPull.exists_good' (jn_isLB D₁ D₂) z
  have o₁ : (1 : 𝟙_ (Over (Sp R')) ⟶ D₁'.P.A).left = eSec D₁'.P.A := Category.id_comp _
  have z₀ : ∀ (D : DegPre R') (T : Over (Spec (CommRingCat.of R'))) (χ : D.X) {U : Type} [CommGroup U]
      (f : (T.left ⟶ D.P.A.left) → U), ∏ k, f (D.Oφ (1 : T ⟶ D.P.A) χ k) ^ Oinvε k = 1 := fun D T χ U _ f => by
    rw [OLinEnd.prod_Oφ_inv, _root_.mul_one]; simp
  have e := key (𝟙_ (Over (Sp R'))) 1 Z r z J J' hJ hJ'
  rw [MonObj.one_comp, o₁] at e
  have e₁ : val u ((r ≫ eSec D₁'.P.A) ≫ proj hD₁) z J = 1 := by
    rw [Category.assoc, hD₁.he, ← Category.assoc]
    exact hu.2 Z _ z J hJ
  have e₂ := e₁.symm.trans (e.trans (congrArg₂ (· * ·) (congrArg₂ (fun a b => a⁻¹ * b)
    (z₀ D₁' (𝟙_ (Over (Sp R'))) x' (fun q => om hD₁.w z (rl J) (rl J') (r ≫ q)))
    (z₀ D₂' (𝟙_ (Over (Sp R'))) y' (fun q => om hD₂.w z (rr J) (rr J') (r ≫ q)))) rfl))
  rw [inv_mul_cancel, _root_.one_mul] at e₂
  exact e₂.symm

theorem main : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (φ : R →+* R') (D₁ D₂ : DegPre R) (D₁' D₂' : DegPre R') (hD₁ : IsPullDeg φ D₁ D₁') (hD₂ : IsPullDeg φ D₂ D₂') (b : D₁.P.A ⟶ D₂.P.A) (h : D₂.X →+ D₁.X) (b' : D₁'.P.A ⟶ D₂'.P.A) (h' : D₂'.X →+ D₁'.X), IsMonHom b → IsMonHom b' → b' ≫ hD₂.e.hom = hD₁.e.hom ≫ (Over.pullback (specOf φ)).map b → (∀ χ, hD₁.xe (h' χ) = h (hD₂.xe χ)) → (∀ χ, ∃ u : LB.Gen (CmpLB D₁ D₂ b (h χ) χ), Nrm u) → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing R') F] (g₁ : GtPtF D₁ F) (g₂ : GtPtF D₂ F) (g₁' : GtPtF D₁' F) (g₂' : GtPtF D₂' F), IsPullGtF φ hD₁ F g₁ g₁' → IsPullGtF φ hD₂ F g₂ g₂' → (Act D₁ D₂ b h g₁ g₂ ↔ Act D₁' D₂' b' h' g₁' g₂') := by
  intro R R' _ _ _ _ φ D₁ D₂ D₁' D₂' hD₁ hD₂ a h a' h' _ _ hb hx hu F _ _ _ g₁ g₂ g₁' g₂' h₁ h₂
  have ha : a'.left ≫ proj hD₂ = proj hD₁ ≫ a.left := by
    rw [← Category.assoc, ← Over.comp_left, hb, Over.comp_left, Category.assoc, map_left_fst, Category.assoc]
  choose u hu using hu
  choose u' hu' vu using fun χ => exists_u hD₁ hD₂ ha (h' χ) χ (hx χ) (u (hD₂.xe χ)) (hu _)
  rw [act_iff_of_nrm u hu, act_iff_of_nrm u' hu']
  have hb : (g₁'.b ≫ a').left ≫ proj hD₂ = (g₁.b ≫ a).left := by
    rw [Over.comp_left, Over.comp_left, Category.assoc, ha, ← Category.assoc]
    exact congrArg (· ≫ _) h₁.1
  have hiff : g₂.b = g₁.b ≫ a ↔ g₂'.b = g₁'.b ≫ a' :=
    ⟨fun H => ext_of_iso_pullback _ hD₂.e (h₂.1.trans ((congrArg (·.left) H).trans hb.symm)),
      fun H => Over.OverMorphism.ext (h₂.1.symm.trans ((congrArg (·.left ≫ proj hD₂) H).trans hb))⟩
  rw [hiff]
  refine and_congr_right fun H => ?_
  have key : ∀ χ (y : Sp F) J J', Good (JN D₁ D₂) y J → Good (JN D₁' D₂') y J' →
      (vS (g₂.s (hD₂.xe χ)) y (rr J) = vS (g₁.s (h (hD₂.xe χ))) y (rl J) * val (Z := Sp F) (u (hD₂.xe χ)) g₁.b.left y J ↔
        vS (g₂'.s χ) y (rr J') = vS (g₁'.s (h' χ)) y (rl J') * val (Z := Sp F) (u' χ) g₁'.b.left y J') := by
    intro χ y J J' hJ hJ'
    have e₁ : vS (g₁.s (hD₁.xe (h' χ))) y (rl J) =
        (∏ k, om hD₁.w y (rl J) (rl J') (𝟙 (Sp F) ≫ D₁'.Oφ g₁'.b (h' χ) k) ^ Oinvε k) * vS (g₁'.s (h' χ)) y (rl J') :=
      (pullGt_val hD₁ h₁ (h' χ) (𝟙 _) ((isPart_inl _ _).good hJ) ((isPart_inl _ _).good hJ')).trans (congrArg₂ (· * ·)
        (OLinEnd.prod_Oφ_inv D₁' g₁'.b (h' χ) (fun q => om hD₁.w y (rl J) (rl J') (𝟙 (Sp F) ≫ q))).symm rfl)
    have e₂ : vS (g₂.s (hD₂.xe χ)) y (rr J) =
        (∏ k, om hD₂.w y (rr J) (rr J') (𝟙 (Sp F) ≫ D₂'.Oφ (g₁'.b ≫ a') χ k) ^ Oinvε k) * vS (g₂'.s χ) y (rr J') := by
      rw [← H]
      exact (pullGt_val hD₂ h₂ χ (𝟙 _) ((isPart_inr _ _).good hJ) ((isPart_inr _ _).good hJ')).trans (congrArg₂ (· * ·)
        (OLinEnd.prod_Oφ_inv D₂' g₂'.b χ (fun q => om hD₂.w y (rr J) (rr J') (𝟙 (Sp F) ≫ q))).symm rfl)
    have e₃ : val (Z := Sp F) (u (hD₂.xe χ)) g₁.b.left y J =
        (∏ k, om hD₁.w y (rl J) (rl J') (𝟙 (Sp F) ≫ D₁'.Oφ g₁'.b (h' χ) k) ^ Oinvε k)⁻¹ *
          (∏ k, om hD₂.w y (rr J) (rr J') (𝟙 (Sp F) ≫ D₂'.Oφ (g₁'.b ≫ a') χ k) ^ Oinvε k) *
          val (Z := Sp F) (u' χ) g₁'.b.left y J' :=
      (congrArg (fun q => val (Z := Sp F) (u (hD₂.xe χ)) q y J)
        ((congrArg (· ≫ proj hD₁) (Category.id_comp _)).trans h₁.1).symm).trans
        ((vu χ _ g₁'.b (Sp F) (𝟙 _) y J J' hJ hJ').trans (congrArg₂ (· * ·) rfl
          (congrArg (fun q => val (Z := Sp F) (u' χ) q y J') (Category.id_comp _))))
    rw [hx] at e₁
    rw [e₁, e₂, e₃]
    exact EndBaseChange.cancel_iff _ _ _ _ _
  constructor
  · intro H χ y J' hJ'
    obtain ⟨J, hJ⟩ := DegPull.exists_good' (jn_isLB D₁ D₂) (Z := Sp F) y
    exact (key χ y J J' hJ hJ').1 (H _ y J hJ)
  · intro H χ y J hJ
    obtain ⟨χ, rfl⟩ := hD₂.xe.surjective χ
    obtain ⟨J', hJ'⟩ := DegPull.exists_good' (jn_isLB D₁' D₂') (Z := Sp F) y
    exact (key χ y J J' hJ hJ').2 (H _ y J' hJ')

end GlobalTheory.Mum.Two.ActPull
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionPointOfThickeningEqTransport
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

open GlobalTheory.TorusCoordPull in

theorem isPullPt_of_carries : ∀ {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {ρ : R →+* R'} {D : DegPre R} {I : Ideal R'} {E : DegData R' I} (hE : IsPullDeg ρ D E.toPre) {A' : PolAV (Sp (FractionRing R'))} {G' : Over (Sp R')} [GrpObj G'] [IsCommMonObj G'] (U : UnifPre I E A' G') (Y : Ext D) {e : ℕ} {φ : (thickObj R' I e G').left ⟶ Y.H.left}, GlobalTheory.FormalModel.Carries hE (U.gt e) (Y.Φ Y.H (𝟙 Y.H)) φ → ∀ (Z : Scheme.{0}) (g : Z ⟶ (thickObj R' I e G').left), ∃ ξ' : GtPt E.toPre (Over.mk (g ≫ (thickObj R' I e G').hom ≫ thick R' I e)), GlobalTheory.TorusCoord.IsPointOf (U.gt e) g ξ' ∧ IsPullPt hE (𝟙 Z) (Y.Φ (Over.mk ((g ≫ φ) ≫ Y.H.hom)) (Over.homMk (g ≫ φ) rfl)) ξ' := by
  intro R R' _ _ _ _ ρ D I E hE A' G' _ _ U Y e φ h Z g
  obtain ⟨ξ', hξ⟩ := GlobalTheory.TorusCoord.exists_isPointOf (U.gt e)
    (T := Over.mk (g ≫ (thickObj R' I e G').hom ≫ thick R' I e)) g rfl
  have hp := Y.rep.1 (Over.mk ((g ≫ φ) ≫ Y.H.hom)) Y.H (Over.homMk (g ≫ φ) rfl) (𝟙 Y.H)
  rw [Category.comp_id] at hp
  set Yξ := Y.Φ (Over.mk ((g ≫ φ) ≫ Y.H.hom)) (Over.homMk (g ≫ φ) rfl) with hYξ
  have hb : ξ'.b.left ≫ hE.e.hom.left ≫ pullback.fst D.P.A.hom (specOf ρ) = 𝟙 Z ≫ Yξ.b.left := by
    rw [hξ.1, Category.assoc, h.1, hp.1, Category.id_comp]
    rfl
  refine ⟨ξ', hξ, hb, fun χ => ?_⟩
  have hψ : ∀ κ : Fin 4, DegPre.gtφT E.toPre _ ξ'.b χ κ ≫ hE.e.hom.left ≫ pullback.fst D.P.A.hom (specOf ρ) =
      𝟙 Z ≫ DegPre.gtφT D _ Yξ.b (hE.xe χ) κ := fun κ => by
    rw [GlobalTheory.TorusCoord.gtφT_eq, GlobalTheory.TorusCoord.gtφT_eq]
    exact Oφ_pull hE Yξ.b ξ'.b (𝟙 Z) hb χ κ
  refine ⟨hψ, maps_of_good ((isGen_iff hE.w).1 hE.w_gen) D.P.isLB E.toPre.P.isLB (ξ'.s χ) (ξ'.isGen χ) _
    (Yξ.isGen _) hψ fun z J J' hJ hJ' => ?_⟩
  have o := (GlobalTheory.TorusCoord.comp_eq_of_left ξ'.b (U.gt e).pG (𝟙 Z) g (by rw [Category.id_comp]; exact hξ.1)).1 χ
  have r1 : val (Yξ.s (hE.xe χ)) (𝟙 Z) z J = val ((Y.Φ Y.H (𝟙 Y.H)).s (hE.xe χ)) (g ≫ φ) z J :=
    (val_corr hJ (hp.2 _) (𝟙 _)).trans ((val_pull hJ _ _ _).trans
      (congrArg (fun r => val ((Y.Φ Y.H (𝟙 Y.H)).s (hE.xe χ)) r z J) (Category.id_comp _)))
  have r3 : val (ξ'.s χ) (𝟙 Z) z J' = val ((U.gt e).t χ) g z J' :=
    (val_corr hJ' (hξ.2 χ) (𝟙 _)).trans ((val_pull hJ' _ _ _).trans
      (congrArg (fun r => val ((U.gt e).t χ) r z J') (Category.id_comp _)))
  refine r1.trans ((h.2 χ Z g z J J' hJ hJ').trans (congrArg₂ (· * ·) (Finset.prod_congr rfl fun k _ => ?_) r3.symm))
  have ok := o k
  rw [Category.id_comp] at ok
  rw [← ok]
  rfl

end GlobalTheory.Mum
end
end

