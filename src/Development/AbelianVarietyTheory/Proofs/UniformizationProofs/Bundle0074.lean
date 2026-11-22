import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0060
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0061
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0012
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0013
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0011
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0010
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigIsoCongr
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0065
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0035
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifBaseChangeSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0009
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.BoxLeOfComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0015
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0016
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0016
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0064
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0066

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IntegralWitness
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
namespace GlobalTheory.UU.IntWit

theorem gs_zero {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) : gs f y U 0 = 0 := by
  unfold gs
  split_ifs
  · simp only [map_zero]
  · rfl

theorem sval_eq_zero {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (s : LB.Sec (LB.LinComb L φ ε)) (h : ∀ j, s.f j = 0) (r : Z ⟶ Y) (z : Z) (J) : sval s r z J = 0 :=
  (congrArg (gs r z _) (h _)).trans (gs_zero r z _)

theorem eq_zero_of_sval {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)}
    {ε : K → ℤ} (s : LB.Sec (LB.LinComb L φ ε)) (h : ∀ y J, Good L y J → sval s (𝟙 Y) y J = 0) (j : K → L.ι) :
    s.f j = 0 := by
  refine fn_ext (V := LB.wchart L φ j) fun y hy => ?_
  obtain ⟨J, hJ, e⟩ := sval_trans hL s y j hy
  rw [h y J hJ, mul_zero] at e
  exact e.trans (gs_zero _ _ _).symm

theorem integral_witness : AllPre fun {V} _ _ _ {D} {_} {_} _ _ U => ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (k : ℕ) (β : D.X), U.FE F k → U.Supp F k β → ∃ (σ : U.SecGT (𝟙_ _) k) (f : ∀ α, SecBT D (𝟙_ _) k α) (s : Raw D F k), U.ExpT (𝟙_ _) k σ f ∧ PullB D F (toUnit _) k f s ∧ DegPre.FamFE D F k s ∧ (∃ j, (s β).f j ≠ 0) ∧ ∃ j, (f β).f j ≠ 0 := by
  intro V _ _ _ hV D A G _ _ U F _ _ k β hFE hS
  obtain ⟨t, s, ⟨n, c, σ, f, hE, -, hB⟩, j₀, hj₀⟩ := hS
  obtain ⟨hG, hP⟩ := GlobalTheory.UU.PullSec.pullEx V hV D A G U F (𝟙_ _) (toUnit _) k
  choose s' hs' using fun i => (hP (f i)).exists
  have hex : ∃ i, ∃ j, (s' i β).f j ≠ 0 := by
    by_contra hn
    push Not at hn
    refine hj₀ (eq_zero_of_sval D.P.isLB (s β) (fun y J hJ => ?_) j₀)
    have w : (toUnit (TF (R := V) F) ▷ D.P.A).left ≫ (snd (𝟙_ _) D.P.A).left = (snd _ D.P.A).left :=
      congrArg CommaMorphism.left (whiskerRight_snd (toUnit (TF (R := V) F)) D.P.A)
    refine (hB β _ (𝟙 _) (toUnit (TF (R := V) F) ▷ D.P.A).left (w.trans (Category.id_comp _).symm) y J hJ).trans ?_
    refine Finset.sum_eq_zero fun i _ => ?_
    exact (congrArg (_ * ·) ((hs' i β y J hJ).symm.trans (sval_eq_zero _ (hn i) _ _ _))).trans (mul_zero _)
  obtain ⟨i, j, hj⟩ := hex
  obtain ⟨t', ht'⟩ := (hG (σ i)).exists
  refine ⟨σ i, f i, s' i, hE i, hs' i,
    hFE t' (s' i) (IntExp.expF_of_expT V _ D A G U F k (σ i) (f i) t' (s' i) (hE i) ht' (hs' i)), ⟨j, hj⟩, ?_⟩
  by_contra hn
  push Not at hn
  exact hj (eq_zero_of_sval D.P.isLB (s' i β)
    (fun y J hJ => (hs' i β y J hJ).trans (sval_eq_zero _ hn _ _ _)) j)

end GlobalTheory.UU.IntWit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsSemiAbelianOfIsPowGrp
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SemiPow

theorem nonempty_torusExtension {K : Type} [Field K] {G' G : Over (Spec (CommRingCat.of K))} [GrpObj G'] [GrpObj G]
    {j : ℕ} (p : IsPowGrp G' G j) (E : TorusExtension G) : Nonempty (TorusExtension G') := by
  letI := E.addCommGroup
  haveI := E.free
  haveI := E.finite
  letI := E.grpB
  obtain ⟨pT, -⟩ := GlobalTheory.exists_isPowGrp_splitTorus (Spec (CommRingCat.of K)) E.X (Fin j → E.X) j (AddEquiv.refl _)
  obtain ⟨q', hq, hq1, hq2, hq3, hq4, -⟩ :=
    GlobalTheory.PowMap.main _ G' G (powObj E.B j) E.B j p (powIsPowGrp E.B j) E.q
  obtain ⟨i', hi, hi1, -⟩ := GlobalTheory.PowMap.main _ _ _ G' G j pT p E.i
  exact ⟨{ X := Fin j → E.X
           B := powObj E.B j
           isAbelian := (GlobalTheory.PowGrp.powers _ _ _ j (powIsPowGrp E.B j)).2.2.2.1 E.isAbelian
           q := q'
           q_hom := hq1 E.q_hom
           q_flat := hq2 E.q_flat
           q_surjective := hq3 E.q_surjective
           q_quasiCompact := hq4 E.q_quasiCompact
           i := i'
           i_hom := hi1 E.i_hom
           isKernel := GlobalTheory.PowKernel.main _ _ _ _ _ _ _ j pT p (powIsPowGrp E.B j) E.i E.q i' q' hi hq
             E.isKernel }⟩

theorem isSemiAbelian_of_isPowGrp : ∀ (S : Scheme.{0}) (G G' : Over S) [GrpObj G] [GrpObj G'] (j : ℕ) (_ : IsPowGrp G' G j), IsSemiAbelian G → IsSemiAbelian G' := by
  intro S G G' _ _ j p hG
  obtain ⟨h1, h2, -, -, h5⟩ := GlobalTheory.PowGrp.powers S G' G j p
  have hq := GlobalTheory.PowGrp.quasiCompact_geomConnected_pow S G' G j p
  refine ⟨h5 hG, h1 hG.smooth, h2 hG.separated, hq.1 hG.quasiCompact, hq.2 hG.smooth hG.geomConnected,
    fun Ω _ _ f => ?_⟩
  obtain ⟨p', -⟩ := GlobalTheory.isPowGrp_baseChange S _ f G' G j p
  obtain ⟨E⟩ := hG.fibres Ω f
  exact nonempty_torusExtension p' E

end GlobalTheory.SemiPow
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsZeroOfRed
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section

namespace GlobalTheory.UU.RedAdd

open GlobalTheory.FormalPoint GlobalTheory.TorusCoord ReciprocityTheory.ChartRestriction.G.DVR

section Level

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : PreU I D A G)
  {T : Over (Spec (CommRingCat.of R))}

theorem red_iff_over (x : T ⟶ G) (g : GtPt D T) :
    U.Red x g ↔ ∀ (e : ℕ) (Z : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))))
      (r : (Over.map (thick R I e)).obj Z ⟶ T) (a : Z ⟶ thickObj R I e G),
      (Over.map (thick R I e)).map a ≫ fstG I e G = r ≫ x → im (U.gt e) a = r ≫ g.b ∧
        ∀ χ z J, Good D.P.L z J →
          val ((U.gt e).t χ) ((Over.map (thick R I e)).map a).left z J = val (g.s χ) r.left z J := by
  constructor
  · intro h e Z r a ha
    obtain ⟨h₁, h₂⟩ := h e _ r.left ((Over.map (thick R I e)).map a).left (congrArg (fun q => q.left) ha)
    exact ⟨Over.OverMorphism.ext h₁, h₂⟩
  · intro h e Z r y hy
    have w : r ≫ T.hom = (y ≫ (thickObj R I e G).hom) ≫ thick R I e := by
      rw [← Over.w x, ← Category.assoc, ← hy, Category.assoc, Over.w (fstG I e G), Category.assoc]; rfl
    obtain ⟨h₁, h₂⟩ := h e (Over.mk (y ≫ (thickObj R I e G).hom)) (Over.homMk r w) (Over.homMk y rfl)
      (Over.OverMorphism.ext hy)
    exact ⟨congrArg (fun q => q.left) h₁, h₂⟩

theorem map_one_fstG {e : ℕ} {Z : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} :
    (Over.map (thick R I e)).map (1 : Z ⟶ thickObj R I e G) ≫ fstG I e G = 1 := by
  have := map_mul_fstG (1 : Z ⟶ thickObj R I e G) 1
  rw [_root_.mul_one] at this
  exact mul_eq_left.1 this.symm

theorem red_one {g : GtPt D T} (h : g.IsZero) : U.Red 1 g := by
  rw [red_iff_over]
  intro e Z r a ha
  obtain rfl : a = 1 := eq_of_map_fstG (by rw [ha, map_one_fstG, MonObj.comp_one])
  refine ⟨by rw [im_one, h.1]; exact (MonObj.comp_one r).symm, fun χ z J hJ => ?_⟩
  have t₁ := val_unit (U.gt e) χ (Z := Z) (z := z) hJ
  exact t₁.trans ((val_corr hJ (h.2 χ) r.left).trans (val_one _)).symm

variable {U} in

theorem red_mul (hG : GlobalFnsSt) {g g' g'' : GtPt D T} {x x' : T ⟶ G} (hx : U.Red x g)
    (hx' : U.Red x' g') (h : g.IsAdd g' g'') : U.Red (x * x') g'' := by
  rw [red_iff_over] at hx hx' ⊢
  intro e Z r y hy
  obtain ⟨a, ha⟩ := exists_lift_fstG (r ≫ x)
  obtain ⟨b, hb⟩ := exists_lift_fstG (r ≫ x')
  obtain rfl : y = a * b := eq_of_map_fstG (by rw [hy, map_mul_fstG, ha, hb, MonObj.comp_mul])
  obtain ⟨a₁, a₂⟩ := hx e Z r a ha
  obtain ⟨b₁, b₂⟩ := hx' e Z r b hb
  refine ⟨by rw [im_mul, a₁, b₁, h.1]; exact (MonObj.comp_mul _ _ _).symm, fun χ z J hJ => ?_⟩
  have e₁ : val ((U.gt e).t χ) ((Over.map (thick R I e)).map (a * b)).left z J *
      th D z J (cP D _ χ) (im (U.gt e) a) (im (U.gt e) b) =
      val ((U.gt e).t χ) ((Over.map (thick R I e)).map a).left z J *
        val ((U.gt e).t χ) ((Over.map (thick R I e)).map b).left z J :=
    val_t_mul_points (U.gt e) hG χ a b z J hJ
  have e₂ : val (g''.s χ) r.left z J * th D z J (r ≫ cP D T χ) (r ≫ g.b) (r ≫ g'.b) =
      val (g.s χ) r.left z J * val (g'.s χ) r.left z J :=
    ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_cub D.cub r hJ _ _ _))).symm.trans
      ((val_corr hJ (h.2 χ) r.left).trans (val_mul hJ _ _ _))
  rw [a₁, b₁, a₂ χ z J hJ, b₂ χ z J hJ] at e₁
  rw [comp_cP] at e₂
  exact mul_right_cancel (e₁.trans e₂.symm)

end Level

section Complete

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {S : Type} [CommRing S] {φ : R →+* S} {D : DegPre R}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] {U : PreU I D A G}

variable (I φ) in

abbrev lev (e : ℕ) : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) := Over.mk (levelMap I φ e)

variable (I φ) in

def levι (e : ℕ) : (Over.map (thick R I e)).obj (lev I φ e) ⟶ Over.mk (spMap φ) :=
  Over.homMk (thick S (I.map φ) e) (levelMap_thick I φ e).symm

variable [IsLocalRing S] [IsHausdorff (I.map φ) S]

omit [IsDomain R] in

theorem pt_ext {B : Over (Spec (CommRingCat.of R))} {b b' : Over.mk (spMap φ) ⟶ B}
    (h : ∀ e, levι I φ e ≫ b = levι I φ e ≫ b') : b = b' :=
  Over.OverMorphism.ext (hom_ext_of_isHausdorff (I.map φ) fun e => congrArg (·.left) (h e))

variable [IsNoetherianRing S]

theorem isAdd_of_red (hG : GlobalFnsSt) {x x' : Over.mk (spMap φ) ⟶ G} {g g' g'' : GtPt D (Over.mk (spMap φ))}
    (h : U.Red x g) (h' : U.Red x' g') (h'' : U.Red (x * x') g'') : GtPt.IsAdd g g' g'' := by
  rw [red_iff_over] at h h' h''
  choose a ha using fun e => exists_lift_fstG (levι I φ e ≫ x)
  choose a' ha' using fun e => exists_lift_fstG (levι I φ e ≫ x')
  have k := fun e => h e _ _ _ (ha e)
  have k' := fun e => h' e _ _ _ (ha' e)
  have k'' := fun e => h'' e _ (levι I φ e) (a e * a' e) (by rw [map_mul_fstG, ha, ha', MonObj.comp_mul])
  have hb : g''.b = g.b * g'.b := pt_ext (I := I) fun e => by
    rw [MonObj.comp_mul, ← (k e).1, ← (k' e).1, ← (k'' e).1, im_mul]
  refine ⟨hb, fun χ => CoordAdd.corr_of_thick (ne_top_of_isHausdorff (I.map φ)) D.P.isLB (fun U _ h => ?_)
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (g''.isGen χ) (DVR.pullGen_isGen _ _ _ _ D.cub.isGen _))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (g.isGen χ) (g'.isGen χ)) fun e z J hJ => ?_⟩
  · refine (Fintype.prod_sum_type _).trans (Eq.trans ?_ (Fintype.prod_sum_type _).symm)
    refine (congrArg₂ (· * ·) (CoordAdd.prod_gtφT g''.b χ h) (prod_cub (DegPre.cT D _ χ) g.b g'.b h)).trans
      (Eq.trans ?_ (congrArg₂ (· * ·) (CoordAdd.prod_gtφT g.b χ h) (CoordAdd.prod_gtφT g'.b χ h)).symm)
    rw [hb, _root_.mul_assoc (DegPre.cT D _ χ)]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  · have e₁ : val ((U.gt e).t χ) ((Over.map (thick R I e)).map (a e * a' e)).left z J *
        th D (T := (Over.map (thick R I e)).obj (lev I φ e)) z J (cP D _ χ) (im (U.gt e) (a e)) (im (U.gt e) (a' e)) =
        val ((U.gt e).t χ) ((Over.map (thick R I e)).map (a e)).left z J *
          val ((U.gt e).t χ) ((Over.map (thick R I e)).map (a' e)).left z J :=
      val_t_mul_points (U.gt e) hG χ (a e) (a' e) z J hJ
    rw [(k e).1, (k' e).1, (k e).2 χ z J hJ, (k' e).2 χ z J hJ, (k'' e).2 χ z J hJ,
      ← comp_cP D (levι I φ e)] at e₁
    exact ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_cub D.cub (levι I φ e) hJ _ _ _))).trans
      (e₁.trans (val_mul hJ _ _ _).symm)

theorem isZero_of_red {g : GtPt D (Over.mk (spMap φ))} (h : U.Red 1 g) : g.IsZero := by
  rw [red_iff_over] at h
  have k := fun e => h e _ (levι I φ e) 1 (by rw [map_one_fstG, MonObj.comp_one])
  have hb : g.b = 1 := pt_ext (I := I) fun e => by rw [MonObj.comp_one, ← (k e).1, im_one]
  refine ⟨hb, fun χ => CoordAdd.corr_of_thick (ne_top_of_isHausdorff (I.map φ)) D.P.isLB (fun U _ h => ?_)
    (g.isGen χ) (fun i j => (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans
      (_root_.mul_one _)).symm) fun e z J hJ => ?_⟩
  · refine (CoordAdd.prod_gtφT g.b χ h).trans (Eq.trans ?_ (Fintype.prod_empty _).symm)
    rw [hb, _root_.mul_one, inv_mul_cancel, _root_.one_mul, mul_inv_cancel]
  · exact ((k e).2 χ z J hJ).symm.trans
      ((val_unit (U.gt e) χ (Z := lev I φ e) (z := z) hJ).trans (val_one _).symm)

end Complete

theorem main : GlobalFnsSt → (AllPre fun {V} _ _ _ {D} {_} {G} _ _ U => ∀ (W : Type) [CommRing W] [IsLocalRing W] [Algebra V W], FinExt V W → ∀ (x x' x'' : TA V W ⟶ G) (g g' g'' : GtPt D (TA V W)), U.Red x g → U.Red x' g' → U.Red x'' g'' → (x'' = x * x' ↔ GtPt.IsAdd g g' g'') ∧ (x = 1 ↔ g.IsZero)) := by
  intro hG V _ _ _ hV D A G _ _ U W _ _ _ hW x x' x'' g g' g'' h h' h''
  have := hV.1
  have := hW.1
  have := hW.2.2.2.2
  have : IsNoetherianRing W := IsNoetherianRing.of_finite V W
  refine ⟨⟨fun e => ?_, fun e => ?_⟩, ⟨fun e => ?_, fun e => ?_⟩⟩
  · exact isAdd_of_red (φ := algebraMap V W) hG h h' (e ▸ h'')
  · exact RedOnto.red_unique (φ := algebraMap V W) h'' (red_mul hG h h' e)
  · exact isZero_of_red (φ := algebraMap V W) (e ▸ h)
  · exact RedOnto.red_unique (φ := algebraMap V W) h (red_one U e)

end GlobalTheory.UU.RedAdd

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PsiInOfIsPowDeg
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory

namespace PsiInPow

open PsiInPull

variable {R : Type} [CommRing R] [IsDomain R]

theorem psiIn_of_gs (D : DegPre R) (χ : D.X) (J : Ideal R)
    (H : ∀ (q : D.P.L.ι) (V : (Spec (CommRingCat.of R)).Opens), IsAffineOpen V →
      V ≤ (D.c χ).left ⁻¹ᵁ D.P.L.U q → ∀ z : Spec (CommRingCat.of (FractionRing R)), jK R z ∈ V →
      ∃ r ∈ J.map (DegPre.toOpen V), gs (jK R) z V r =
        (gm (𝟙 _) z (LB.wchart D.P.L (fun _ : PUnit => D.xK χ) (fun _ => q)) ((D.psi χ).s (fun _ => q))).val) :
    D.PsiIn χ J := by
  intro j' V hV hle h'
  obtain ⟨q, rfl⟩ : ∃ q, j' = fun _ => q := ⟨j' PUnit.unit, rfl⟩
  have hss : Subsingleton (Spec (CommRingCat.of (FractionRing R))) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum (FractionRing R)))
  by_cases hne : ∃ z, jK R z ∈ V
  swap
  · exact ⟨0, Ideal.zero_mem _, fn_ext fun z hz => (hne ⟨z, hz⟩).elim⟩
  obtain ⟨z, hz⟩ := hne
  obtain ⟨r', hr', e'⟩ := H q V hV hle z hz
  refine ⟨r', hr', fn_ext fun y hy => ?_⟩
  obtain rfl : y = z := Subsingleton.elim (α := Spec (CommRingCat.of (FractionRing R))) y z
  exact (gs_pull (𝟙 _) (jK R) y V hz r').trans (e'.trans
    ((gs_res (𝟙 _) y h' hy _).trans (gs_unit _ _ _ (h' hy) _)).symm)

theorem gs_of_psiIn (D : DegPre R) (χ : D.X) (J : Ideal R) (H : D.PsiIn χ J)
    (q : D.P.L.ι) (V : (Spec (CommRingCat.of R)).Opens) (hV : IsAffineOpen V)
    (hle : V ≤ (D.c χ).left ⁻¹ᵁ D.P.L.U q) (z : Spec (CommRingCat.of (FractionRing R))) (hz : jK R z ∈ V) :
    ∃ r ∈ J.map (DegPre.toOpen V), gs (jK R) z V r =
      (gm (𝟙 _) z (LB.wchart D.P.L (fun _ : PUnit => D.xK χ) (fun _ => q)) ((D.psi χ).s (fun _ => q))).val := by
  have h : jK R ⁻¹ᵁ V ≤ (LB.LinComb D.P.L (K := PUnit) (fun _ => D.xK χ) (fun _ => -1)).U (fun _ => q) :=
    fun y hy => mem_wchart _ _ _ _ (hle hy)
  obtain ⟨r, hrJ, hr⟩ := H (fun _ => q) V hV hle h
  refine ⟨r, hrJ, ?_⟩
  exact (gs_pull (𝟙 _) (jK R) z V hz r).symm.trans ((congrArg (gs (𝟙 _) z _) hr).trans
    ((gs_res (𝟙 _) z h hz _).trans (gs_unit _ _ _ (h hz) _)))

theorem val_psi_zero (D : DegPre R) (hB : D.TauBimult) {y : (TK R).left} {J} (hJ : Good D.P.L y J) :
    val (D.psi 0) (𝟙 _) y J = (val D.rigK (𝟙 _) y J)⁻¹ := by
  have C : IsCub (cubV D.cub (T := TK R) y J) := isCub_cubV D.cub hJ
  have t := tauK_mul hJ hB 0 0 0
  have z0 : val (D.tau (0 + 0) 0) (𝟙 _) y J = val (D.tau 0 0) (𝟙 _) y J :=
    congrArg (fun a => val (D.tau a 0) (𝟙 _) y J) (add_zero 0)
  rw [z0, cPoint_zero, C.face, _root_.mul_one] at t
  have t0 : val (D.tau 0 0) (𝟙 _) y J = 1 := mul_eq_left.1 t.symm
  have e : val (D.tau 0 0) (𝟙 _) y J = val (D.psi (0 + 0)) (𝟙 _) y J * (val (D.psi 0) (𝟙 _) y J)⁻¹ *
      (val (D.psi 0) (𝟙 _) y J)⁻¹ * (val D.rigK (𝟙 _) y J)⁻¹ :=
    (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
      (congrArg₂ (· * ·) rfl (val_inv _ _))) (val_inv _ _))) (val_inv _ _))
  rw [t0, add_zero, mul_inv_cancel, _root_.one_mul] at e
  exact (inv_mul_eq_one.1 e.symm)

end PsiInPow

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PsiScalarsRelationsUpToBaseUnitsStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
theorem _root_.GlobalTheory.T.psiScalars_relations_up_to_baseUnits : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (D : DegPre V) (ga : ∀ χ : D.X, LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1))) (a : D.X → (FractionRing V)ˣ), PsiScal D ga a → (D.TauBimult → ∀ x y z, ∃ u : Vˣ, (a (x + y + z) * a x * a y * a z).val = algebraMap V (FractionRing V) u.val * (a (x + y) * a (x + z) * a (y + z)).val) ∧ (D.PsiEven → ∀ x, ∃ u : Vˣ, (a (-x)).val = algebraMap V (FractionRing V) u.val * (a x).val) := by
  first | exact @GlobalTheory.PsiScalUnit.main | exact GlobalTheory.PsiScalUnit.main | (intros; apply GlobalTheory.PsiScalUnit.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PullbackSectionFamilyNeZeroIffStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pullbackSectionFamily_ne_zero_iff : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ) (f : ∀ α, SecBT D (𝟙_ _) k α) (s : Raw D F k), PullB D F (toUnit _) k f s → ∀ α, ((∃ j, (s α).f j ≠ 0) ↔ ∃ j, (f α).f j ≠ 0) := by
  first | exact @GlobalTheory.pullB_ne_zero_iff | exact GlobalTheory.pullB_ne_zero_iff | (intros; apply GlobalTheory.pullB_ne_zero_iff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SvalLincomb
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
namespace GlobalTheory.UU.ExpLinC

theorem gs_sum' {Y Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (U : Y.Opens) (hm : r z ∈ U) {K : Type} (S : Finset K)
    (a : K → Γ(Y, U)) : gs r z U (∑ i ∈ S, a i) = ∑ i ∈ S, gs r z U (a i) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    have h := gs_add r z U hm 0 0
    rw [add_zero] at h
    simpa using h
  | insert i S hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, gs_add r z U hm, ih]

theorem sval_lincomb {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ} {n : ℕ}
    {t : Fin n → LB.Sec (LB.LinComb L φ ε)} {t' : LB.Sec (LB.LinComb L φ ε)} (a : Fin n → Γ(Y, ⊤))
    (h : ∀ j, t'.f j = ∑ i, (Y.presheaf.map (homOfLE le_top).op).hom (a i) * (t i).f j)
    (r : Z ⟶ Y) (z : Z) {J} (hJ : Good L z J) :
    sval t' r z J = ∑ i, gs r z ⊤ (a i) * sval (t i) r z J := by
  have hm := hJ.mem φ r
  refine (congrArg (gs r z _) (h _)).trans ?_
  refine (gs_sum' _ _ _ hm _ _).trans (Finset.sum_congr rfl fun i _ => ?_)
  exact (gs_mul _ _ _ hm _ _).trans (congrArg (· * _) (gs_res r z le_top hm (a i)))

theorem expF_lincomb : (AllPre fun {V} _ _ _ {D} {A} {_} _ _ U => ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (k n : ℕ) (c : Fin n → F) (t : Fin n → LB.Sec (LPow A.A A.L (k : ℤ) (TFK (R := V) F))) (s : Fin n → Raw D F k) (t' : LB.Sec (LPow A.A A.L (k : ℤ) (TFK (R := V) F))) (s' : Raw D F k), (∀ i, U.ExpF F k (t i) (s i)) → (∀ j, t'.f j = ∑ i, liftFun A.A _ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (c i)) * (t i).f j) → (∀ α j, (s' α).f j = ∑ i, DegPre.constBF D F (c i) _ * (s i α).f j) → U.ExpF F k t' s') := by
  intro V _ _ _ _ D A G _ _ U F _ _ k n c t s t' s' H ht hs
  choose m a σ f h1 h2 h3 using H
  let e : Fin (Fintype.card (Σ i, Fin (m i))) ≃ (Σ i, Fin (m i)) := (Fintype.equivFin _).symm
  refine ⟨_, fun p => c (e p).1 * a (e p).1 (e p).2, fun p => σ (e p).1 (e p).2, fun p => f (e p).1 (e p).2,
    fun p => h1 _ _, fun Z rA y rG e1 e2 z JA JG hA hG => ?_, fun α Z rF rB e0 z J hJ => ?_⟩
  · rw [e.sum_comp (fun q => gs rA z ⊤ (scal (fst (TFK (R := V) F) A.A).left (c q.1 * a q.1 q.2)) *
      sval (σ q.1 q.2) rG z JG), Fintype.sum_sigma,
      sval_lincomb (L := A.L) (φ := fun _ : Fin 1 => (snd (TFK (R := V) F) A.A).left) (ε := fun _ => (k : ℤ))
        (fun i => scal (fst (TFK (R := V) F) A.A).left (c i)) ht rA z hA, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [ExpLin.gs_scal_mul, _root_.mul_assoc]
    rw [← Finset.mul_sum, ← h2 i Z rA y rG e1 e2 z JA JG hA hG]
    ring
  · rw [e.sum_comp (fun q => gs rF z ⊤ (scal (fst (TF (R := V) F) D.P.A).left (c q.1 * a q.1 q.2)) *
      sval (f q.1 q.2 α) rB z J), Fintype.sum_sigma]
    refine (sval_lincomb (fun i => scal (fst (TF (R := V) F) D.P.A).left (c i)) (hs α) rF z hJ).trans ?_
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [ExpLin.gs_scal_mul, _root_.mul_assoc]
    rw [← Finset.mul_sum, ← h3 i α Z rF rB e0 z J hJ]

end GlobalTheory.UU.ExpLinC
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TauBimultPsiEvenOverExtensionFieldStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
theorem _root_.GlobalTheory.T.tau_bimult_psi_even_over_extension_field : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F], ((∀ (z : (TF (R := R) F).left) J, Good D.P.L z J → ∀ a b m : D.X, val (Z := (TF (R := R) F).left) (D.psi (a + b + m)) (jFK (R := R) F) z J * val (Z := (TF (R := R) F).left) (D.psi (a)) (jFK (R := R) F) z J * val (Z := (TF (R := R) F).left) (D.psi (b)) (jFK (R := R) F) z J * val (Z := (TF (R := R) F).left) (D.psi (m)) (jFK (R := R) F) z J * rigV D z J * cubV D.cub z J (cT D _ a) (cT D _ b) (cT D _ m) = val (Z := (TF (R := R) F).left) (D.psi (a + b)) (jFK (R := R) F) z J * val (Z := (TF (R := R) F).left) (D.psi (a + m)) (jFK (R := R) F) z J * val (Z := (TF (R := R) F).left) (D.psi (b + m)) (jFK (R := R) F) z J) ↔ D.TauBimult) ∧ ((∀ (z : (TF (R := R) F).left) J, Good D.P.L z J → ∀ m : D.X, val (Z := (TF (R := R) F).left) (D.psi (-m)) (jFK (R := R) F) z J * val D.sym (cT D (TF (R := R) F) m).left z J = val (Z := (TF (R := R) F).left) (D.psi (m)) (jFK (R := R) F) z J) ↔ D.PsiEven) := by
  first | exact @GlobalTheory.TauValues.main | exact GlobalTheory.TauValues.main | (intros; apply GlobalTheory.TauValues.main <;> assumption)
end

