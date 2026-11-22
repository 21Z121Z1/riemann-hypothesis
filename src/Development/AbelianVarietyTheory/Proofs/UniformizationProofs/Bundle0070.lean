import Mathlib
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0057
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0012
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0012
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0011
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Uniformization.SmulOneSecEqZeroIff
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPowEqOfBaseChange
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0060
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0029
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0066
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0051
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0061
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0016
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0059
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigIsoCongr
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExactTermAfterTorsionStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
theorem _root_.GlobalTheory.T.exists_nsmul_add_decomp_with_coef_valuation : LL → TwistBCSpanStatement → TWM.VRatioGtStatement → TWStatement → UUStatement → AllDV fun {V} _ _ _ {ϖ} hϖ D Q {F} _ _ {v} hv => ∀ ϑ : Fam D.toPre F 1, Prim D Q v ϑ → ∀ (n : ℕ), 2 ≤ n → IsUnit (n : V) → ∀ (g : GtPtF D.toPre F) (χ : D.toPre.X), ∃ (h o g₂ : GtPtF D.toPre F), o.IsZero ∧ GtPtF.IsNsmul n h o ∧ g.IsAdd h g₂ ∧ ∀ (w : Frm D.toPre F 1 g₂.b) l ω, w.IsGen → GtV hϖ hv g₂ l → GenV hϖ hv w ω → v (coef ϑ g₂ w χ) = (((Q χ : ℚ) + l χ + ω : ℚ) : WithTop ℚ) := by
  first | exact @GlobalTheory.UT.ExactTerm.exact_term_after_torsion | exact GlobalTheory.UT.ExactTerm.exact_term_after_torsion | (intros; apply GlobalTheory.UT.ExactTerm.exact_term_after_torsion <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsConj
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.UU.Weight

open GlobalTheory.TorusExt

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]

abbrev CompMod (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ) (α : D.X) : Type :=
  SecMod (fst (TF (R := R) F) D.P.A).left (LB.LinComb D.P.L (DegPre.famφ D F α) (DegPre.famε k))

theorem gs_scal {K : Type} [CommRing K] {Y Z : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of K)) (r : Z ⟶ Y) (z : Z)
    (c : K) : gs r z ⊤ (scal p c) = gs (r ≫ p) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom c) :=
  gs_pull r p z ⊤ trivial _

theorem phiRaw_val (hG : GlobalFnsSt) {k : ℕ} {g : GtPtF D F} (hg : GtTors D k g)
    {w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F g.b) (DegPre.lineε k))} (hw : w.IsGen) {s s' : Raw D F k}
    (h : PhiRaw D F k 0 g w s s') (α : D.X) (y : (DegPre.BF D F).left) (J) (hJ : Good D.P.L y J) :
    sval (s' α) (𝟙 _) y J = sval (s α) (DegPre.trPt D F g.b).left y J * (uVal D F k α g.b (𝟙 _) y J *
      val (LB.mulGen D.P.L _ _ _ _ (g.s α) w) (fst (TF (R := R) F) D.P.A).left y J).val := by
  obtain ⟨u, hu, hc⟩ := (gen_u D F hG k α (α + 0) g.b (by rw [add_zero, hg.base_pow, _root_.mul_one]) _
    (mulGen_isGen _ _ _ _ _ _ _ (g.isGen α) hw) (fun U _ h => by
    refine (Fintype.prod_sum_type _).trans ?_
    rw [Fin.prod_univ_four, Fin.prod_univ_two]
    show h (cP D _ α * g.b).left ^ (-1 : ℤ) * h (cP D _ α).left ^ (1 : ℤ) * h g.b.left ^ (1 : ℤ) *
      h (1 : TF (R := R) F ⟶ D.P.A).left ^ (-1 : ℤ) *
      (h (1 : TF (R := R) F ⟶ D.P.A).left ^ (k : ℤ) * h g.b.left ^ (-(k : ℤ))) = _
    simp only [zpow_neg, zpow_one, zpow_natCast]
    ac_rfl)).1
  have e := (secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ u).1 (h α u hu hc) _ (𝟙 _) y J hJ
  have e' := hg.val_phi hG w hw α u hu hc _ (𝟙 _) y J hJ
  rw [Category.id_comp, Over.id_left] at e'
  rw [Category.id_comp] at e
  exact (congrArg (fun β => sval (s' β) (𝟙 _) y J) (add_zero α)).symm.trans
    (e.trans (congrArg (fun q => _ * Units.val q) e'))

theorem phiRaw_smul (hG : GlobalFnsSt) {k : ℕ} {g : GtPtF D F} (hg : GtTors D k g)
    {w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F g.b) (DegPre.lineε k))} (hw : w.IsGen)
    {s s' t t' : ∀ α, CompMod D F k α} (h : PhiRaw D F k 0 g w (fun α => (s α).sec) fun α => (s' α).sec)
    (h' : PhiRaw D F k 0 g w (fun α => (t α).sec) fun α => (t' α).sec) (α : D.X) (c : F) (e : s α = c • t α) :
    s' α = c • t' α := by
  refine SecMod.ext_coord (sec_ext_val D.P.isLB fun y J hJ => ?_)
  have a := phiRaw_val hG hg hw h α y J hJ
  have b := phiRaw_val hG hg hw h' α y J hJ
  have t₁ : (DegPre.trPt D F g.b).left ≫ (fst (TF (R := R) F) D.P.A).left = 𝟙 _ ≫ (fst (TF (R := R) F) D.P.A).left :=
    (congrArg (fun q => q.left) (tr_fst D F g.b)).trans (Category.id_comp _).symm
  rw [SecMod.value_smul hJ, a, b, e, SecMod.value_smul hJ, gs_scal, gs_scal, _root_.mul_assoc]
  exact congrArg (fun q => gs q y ⊤ _ * _) t₁

theorem phiRaw_torus (hG : GlobalFnsSt) {k : ℕ} (τ : Multiplicative D.X →* Fˣ) {g : GtPtF D F}
    (hτ : g = torusPt D F (Additive.ofMul τ)) (hg : GtTors D k g)
    {w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F g.b) (DegPre.lineε k))} (hw : w.IsGen) :
    ∃ c : Fˣ, ∀ s s' : ∀ α, CompMod D F k α, PhiRaw D F k 0 g w (fun α => (s α).sec) (fun α => (s' α).sec) →
      ∀ α, s' α = ((c * τ (Multiplicative.ofAdd α) : Fˣ) : F) • s α := by
  have hb : g.b = 1 := hτ ▸ torusPt_b _
  obtain ⟨y₀, J₀, hJ₀⟩ := exists_good_chart D F
  obtain ⟨c, hc⟩ := (stalkUnits (F := F) y₀).surjective (val w (𝟙 _) y₀ J₀)
  have vv : ∀ (u : Fˣ) {Z : Scheme.{0}} (r : Z ⟶ (TF (R := R) F).left) (z : Z) J, Good D.P.L z J →
      val (GlobalTheory.UU.scaleGen (unitOn u) (LB.oneGen D.P.L (Y := (TF (R := R) F).left))) r z J = gm r z ⊤ (unitOn u) :=
    fun u Z r z J hJ => (GlobalTheory.UU.val_scaleGen _ _ _ hJ).trans ((congrArg₂ (· * ·) rfl (val_one _)).trans (_root_.mul_one _))
  have hwv : ∀ y J, Good D.P.L y J → val w (𝟙 _) y J = stalkUnits (F := F) y c := fun y J hJ => by
    obtain rfl := pt_eq y₀ y
    refine (val_eq_of_val_eq (φ' := PEmpty.elim) (ε' := PEmpty.elim) (fun U _ h => ?_) hw
      (GlobalTheory.UU.scaleGen_isGen (unitOn c) oneGen_isGen) hJ₀ hJ (hc.symm.trans ((vv c _ _ _ hJ₀).trans (gm_unitOn _ c)).symm)).trans
      ((vv c _ _ _ hJ).trans (gm_unitOn _ c))
    rw [Fin.prod_univ_two, Fintype.prod_empty]
    show h (1 : TF (R := R) F ⟶ D.P.A).left ^ (k : ℤ) * h g.b.left ^ (-(k : ℤ)) = 1
    rw [hb, zpow_neg, mul_inv_cancel]
  refine ⟨c, fun s s' h α => SecMod.ext_coord (sec_ext_val D.P.isLB fun y J hJ => ?_)⟩
  have cr : LB.Gen.Corr D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ (g.s α) w)
      (GlobalTheory.UU.scaleGen (unitOn (c * τ (Multiplicative.ofAdd α))) (LB.oneGen D.P.L (Y := (TF (R := R) F).left))) :=
    corr_of_val D.P.isLB fun y J hJ => by
      have e : charVal g α y J = stalkUnits (F := F) y (τ (Multiplicative.ofAdd α)) := hτ ▸ torusPt_val τ α hJ
      refine ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) e (hwv y J hJ))).trans
        (Eq.trans ?_ ((vv _ _ _ _ hJ).trans (gm_unitOn _ _)).symm)
      exact (mul_comm _ _).trans (map_mul (stalkUnits (F := F) y) _ _).symm
  have C : IsCub (th D (T := DegPre.BF D F) y J) := isCub_cubV D.cub hJ
  have u₁ : uVal D F k α g.b (𝟙 _) y J = 1 := by
    rw [uVal_id, hb, MonObj.comp_one, C.face₃, inv_one, _root_.mul_one]
    exact Finset.prod_eq_one fun _ _ => C.face₂ _ _
  have t₁ : DegPre.trPt D F g.b = 𝟙 _ := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [tr_fst, Category.id_comp]
    · rw [tr_pr, hb, MonObj.comp_one, _root_.mul_one, Category.id_comp]
  have a := phiRaw_val hG hg hw h α y J hJ
  rw [u₁, _root_.one_mul, t₁, Over.id_left, (val_corr hJ cr _).trans (vv _ _ _ _ hJ)] at a
  rw [SecMod.value_smul hJ, gs_scal, Category.id_comp, mul_comm]
  exact a.trans (congrArg _ (gs_unit _ y ⊤ trivial _).symm)

theorem exists_conj {K K' E M : Type} [CommRing K] [CommRing K'] [AddCommGroup E] [Module K E] [AddCommGroup M]
    [Module K' M] (σ : K ≃+* K') (j : E ≃+ M) (hj : ∀ (c : K) v, j (c • v) = σ c • j v) (Φ : M ≃ₗ[K'] M) :
    ∃ Ψ : E ≃ₗ[K] E, ∀ v, j (Ψ v) = Φ (j v) :=
  ⟨{ j.trans (Φ.toAddEquiv.trans j.symm) with
      map_smul' := fun c v => j.injective (by
        show j (j.symm (Φ (j (c • v)))) = j (c • j.symm (Φ (j v)))
        rw [hj, hj, map_smul, j.apply_symm_apply, j.apply_symm_apply]) }, fun _ => j.apply_symm_apply _⟩

abbrev TorsPt {S : Scheme.{0}} (P : PolAV S) (T : Over S) (N : ℕ) : Subgroup (T ⟶ P.A) :=
  (powMonoidHom N : (T ⟶ P.A) →* (T ⟶ P.A)).ker

theorem exists_projective_rep (hL : Laws) (hL₂ : Laws2) {S : Scheme.{0}} [IsLocallyNoetherian S] (P : PolAV S)
    {F : Type} [Field F] [IsAlgClosed F] (p : Spec (CommRingCat.of F) ⟶ S) {N : ℕ} (hN : (N : F) ≠ 0) :
    ∃ (Φ : TorsPt P (Over.mk p) N → (SecMod (F := F) (fst (Over.mk p) P.A).left (LPow P.A P.L N (Over.mk p)) ≃ₗ[F]
        SecMod (F := F) (fst (Over.mk p) P.A).left (LPow P.A P.L N (Over.mk p))))
      (e : TorsPt P (Over.mk p) N → TorsPt P (Over.mk p) N → Fˣ),
      Module.finrank F (SecMod (F := F) (fst (Over.mk p) P.A).left (LPow P.A P.L N (Over.mk p))) = N ^ P.g ∧
      (∀ a, ∃ θ : ThetaGrp P.A P.L N (Over.mk p), θ.pt = a.1 ∧ ∀ v, IsActOf P.A P.L N θ v.sec (Φ a v).sec) ∧
      (∀ a b, ∃ c : Fˣ, ∀ v, Φ (a * b) v = (c : F) • Φ a (Φ b v)) ∧
      (∀ a b v, Φ a (Φ b v) = (e a b : F) • Φ b (Φ a v)) ∧ ∀ a, (∀ b, e a b = 1) → a = 1 := by
  obtain ⟨Φ, e, h₁, h₂, h₃, h₄, h₅⟩ := GlobalTheory.ThetaRep.exists_projective_rep hL hL₂ S P F p N hN
  let σ : F ≃+* Γ((Over.mk p).left, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of F)).symm.commRingCatIsoToRingEquiv
  let j : SecMod (F := F) (fst (Over.mk p) P.A).left (LPow P.A P.L N (Over.mk p)) ≃+ SecM P.A P.L N (Over.mk p) :=
    { toFun := fun v => SecM.ofSec P.A v.sec
      invFun := fun v => SecMod.mk _ (SecM.toSec P.A v)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl }
  have hj : ∀ (c : F) v, j (c • v) = σ c • j v := fun _ _ => rfl
  let u : Γ((Over.mk p).left, ⊤)ˣ ≃* Fˣ := Units.mapEquiv σ.symm.toMulEquiv
  have hu : ∀ r, σ (u r : F) = r.val := fun r => σ.apply_symm_apply _
  have hd := (congrArg Cardinal.toNat (rank_eq_of_equiv_equiv σ j σ.bijective hj)).trans h₁
  choose Ψ hΨ using fun a : TorsPt P (Over.mk p) N => exists_conj σ j hj (Φ a)
  refine ⟨Ψ, fun a b => u (e a b), hd, fun a => ?_, fun a b => ?_, fun a b v => ?_,
    fun a h => Subtype.ext (h₅ a fun b => u.injective ((h b).trans (map_one u).symm))⟩
  · obtain ⟨θ, h, h'⟩ := h₂ a
    refine ⟨θ, h, fun v => ?_⟩
    have := h' (j v)
    rw [← hΨ] at this
    exact this
  · obtain ⟨r, hr⟩ := h₃ a b (a * b : TorsPt P (Over.mk p) N) rfl
    refine ⟨u r, fun v => j.injective ?_⟩
    rw [hj, hΨ, hΨ, hΨ, hu]
    exact hr (j v)
  · apply j.injective
    beta_reduce
    rw [hj, hΨ, hΨ, hΨ, hΨ]
    exact ((h₄ a b).2 (j v)).trans (congrArg (fun c => c • Φ b (Φ a (j v))) (hu (e a b)).symm)

end GlobalTheory.UU.Weight
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCubicalBundleOfSymmetricSemiAbelian
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.UU

theorem exists_cp_of_isSymmetric :
    Laws → ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (gen : (Over.pullback (jK R)).obj G ≅ A.A), IsMonHom gen.hom → ∀ (L : RigLB G) (c : CubicalStr G L), L.IsSymmetric → ∃ P : CP G, P.L = L ∧ HEq P.c c := by
  intro hL R _ _ _ A G _ _ hS gen _ L c hsym
  obtain ⟨s, hs, hr⟩ := GlobalTheory.SymmetricBundle.gen_of_isSymmetric L hsym
  have := hS.smooth
  have : Flat (G3 G).hom := by
    show Flat (pullback.fst G.hom (pullback.fst G.hom G.hom ≫ G.hom) ≫ G.hom)
    infer_instance
  exact ⟨⟨L, c, s, hs, hr, GlobalTheory.ValueForm.sym_cub_of_baseChange (jK R) (GlobalTheory.ValueForm.app_generic_injective _)
    (GlobalTheory.ValueForm.surjective_cube_baseChange hL.globalFns _ A.isAb gen) c s hs hr⟩, rfl, HEq.rfl⟩

end GlobalTheory.UU
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsGenOfIso
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section
namespace GlobalTheory.UU.Transl

section General
variable {X X' W Y Y₂ : Scheme.{0}} {L : LB X} {L' : LB X'} {K : Type} [Fintype K]

theorem exists_gen_of_iso (hL : L.IsLB) (hL' : L'.IsLB) {F : W ⟶ X} {F' : W ⟶ X'}
    (w : LB.Iso (L'.pull F') (L.pull F)) (hw : w.IsGen) (y : K → (Y ⟶ W)) (h : Y ⟶ Y₂) {φ : K → (Y₂ ⟶ X)}
    {φ' : K → (Y ⟶ X')} {ε : K → ℤ} (ha : ∀ k, y k ≫ F' = φ' k) (hb : ∀ k, y k ≫ F = h ≫ φ k)
    (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) :
    ∃ a : LB.Gen (LB.LinComb L' φ' ε), a.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J) (J'), Good L z J →
      Good L' z J' → val t (r ≫ h) z J =
        (∏ k, gw w (r ≫ y k) z (J ((r ≫ y k) ≫ F)) (fun _ => J' ((r ≫ y k) ≫ F')) ^ ε k) * val a r z J' := by
  obtain rfl : (fun k => y k ≫ F') = φ' := funext ha
  obtain ⟨a, ga, H⟩ := CubTransport.exists_pmaps ((isGen_iff w).1 hw) hL (pull_isLB hL' F') (φ' := y) h hb t ht
  have le : ∀ j : K → L'.ι, LB.wchart L' (fun k => y k ≫ F') j ≤ LB.wchart (L'.pull F') y (fun k _ => j k) :=
    fun j p hp => Set.mem_iInter.2 fun k => mem_pull.2 (Set.mem_iInter.1 hp k)
  refine ⟨⟨fun j => res (le j) (a.s fun k _ => j k)⟩, isGen_of_gm _ fun p j j' hj hj' => ?_,
    fun Z r z J J' hJ hJ' => ?_⟩
  · refine (gm_res _ p (le j) hj _).trans ((gen_trans ga (𝟙 Y) p (le j hj) (le j' hj')).trans
      (congrArg₂ (· * ·) (Finset.prod_congr rfl fun k _ => congrArg (· ^ ε k) ?_) (gm_res _ p (le j') hj' _).symm))
    refine (gm_pull_g L' F' (𝟙 Y ≫ y k) p _ _ (Set.mem_iInter.1 (le j hj) k) (Set.mem_iInter.1 (le j' hj') k)).trans ?_
    rw [Category.assoc]
  · have g' : Good (L'.pull F') z (fun ψ _ => J' (ψ ≫ F')) := fun ψ => mem_pull.2 (hJ' (ψ ≫ F'))
    refine (CubTransport.val_pmaps hb H r hJ g').trans (congrArg (_ * ·) ?_)
    rw [val_of _ r z J' (fun k => J' ((r ≫ y k) ≫ F')) (fun k => by rw [Category.assoc])]
    exact (gm_res r z (le _) (Set.mem_iInter.2 fun k => hJ' ((r ≫ y k) ≫ F')) _).symm

theorem exists_unit_base {S₀ : Scheme.{0}} (p : Y ⟶ S₀) (e : S₀ ⟶ Y) (he : e ≫ p = 𝟙 _)
    (hp : Function.Surjective p.appTop.hom) (a : Γ(Y, ⊤)ˣ) :
    ∃ c : Γ(S₀, ⊤)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z), gm r z ⊤ a = gm (r ≫ p) z ⊤ c := by
  obtain ⟨c, hc⟩ := hp a.val
  have e₁ : e.appTop.hom a.val = c := by
    rw [← hc, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, he]; simp
  refine ⟨Units.map e.appTop.hom.toMonoidHom a, fun Z r z => ?_⟩
  refine Eq.trans (congrArg (gm r z ⊤) (Units.ext ?_)) (gm_pull r p z ⊤ trivial _)
  exact hc.symm.trans (congrArg p.appTop.hom e₁.symm)

theorem surj_fst (hG : GlobalFnsSt) {S : Scheme.{0}} {A : Over S} [GrpObj A] (hA : IsAbelianScheme A) (T : Over S) :
    Function.Surjective (fst T A).left.appTop.hom := by
  have e : (fst T A).left = (β_ T A).hom.left ≫ (snd A T).left := by
    rw [← Over.comp_left, braiding_hom_snd]
  rw [e]
  have : IsIso (β_ T A).hom.left := inferInstanceAs (IsIso ((Over.forget _).map (β_ T A).hom))
  have : IsIso (β_ T A).hom.left.appTop := inferInstanceAs (IsIso ((β_ T A).hom.left.app ⊤))
  exact surj_comp (ConcreteCategory.bijective_of_isIso (β_ T A).hom.left.appTop).2 (surj_snd hG hA T)

def comb {M : LB Y} (a : Γ(Y, ⊤)) (s t : LB.Sec M) : LB.Sec M where
  f j := (Y.presheaf.map (homOfLE le_top).op).hom a * s.f j + t.f j
  compat i j := by
    have e : ∀ {V : Y.Opens} (h : M.U i ⊓ M.U j ≤ V), (Y.presheaf.map (homOfLE h).op).hom
        ((Y.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op).hom a) = (Y.presheaf.map (homOfLE le_top).op).hom a :=
      fun h => by rw [← CommRingCat.comp_apply, ← Functor.map_comp]; rfl
    rw [map_add, map_add, map_mul, map_mul, e, e, s.compat i j, t.compat i j]
    ring

def zeroSec (M : LB Y) : LB.Sec M where
  f _ := 0
  compat i j := by rw [map_zero, map_zero, mul_zero]

theorem sval_zeroSec {φ : K → (Y ⟶ X)} {ε : K → ℤ} {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (J) :
    sval (zeroSec (LB.LinComb L φ ε)) r z J = 0 := by
  unfold sval gs
  split_ifs
  · exact (congrArg _ (map_zero _)).trans (map_zero _)
  · rfl

theorem gs_scal {R : Type} [CommRing R] {Z : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of R)) (r : Z ⟶ Y) (z : Z)
    (c : R) : gs r z ⊤ (scal p c) = gs (r ≫ p) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c) :=
  gs_pull r p z ⊤ trivial _

end General

theorem cubN_twist {A B C U : Type} [CommGroup A] [CommGroup B] [CommGroup C] [CommGroup U] (β : A →* B) (κ : A →* C)
    (W : A → U) {θ : B → B → B → U} {θ' : C → C → C → U}
    (h : ∀ a b c, θ (β a) (β b) (β c) * W (a * b) * W (a * c) * W (b * c) * W 1 =
      W (a * b * c) * W a * W b * W c * θ' (κ a) (κ b) (κ c)) {N : ℕ} {m : A} (hm : m ^ N = 1) (y : A) :
    cubN θ N 1 (β m) (β y) * W (m * y) ^ N * W 1 ^ N = W y ^ N * W m ^ N * cubN θ' N 1 (κ m) (κ y) := by
  have key : ∀ n : ℕ, cubN θ n 1 (β m) (β y) * W (m ^ n) * W y * W (m * y) ^ n * W 1 ^ n =
      W (m ^ n * y) * W 1 * W y ^ n * W m ^ n * cubN θ' n 1 (κ m) (κ y) := by
    intro n
    induction n with
    | zero => simp [cubN, mul_comm]
    | succ n ih =>
      have c := h (m ^ n) m y
      simp only [cubN, Finset.prod_range_succ, _root_.one_mul, map_pow, ← pow_succ m] at ih c ⊢
      simp only [pow_succ (W _)]
      apply Additive.ofMul.injective
      have ih' := congrArg Additive.ofMul ih
      have c' := congrArg Additive.ofMul c
      simp only [ofMul_mul] at ih' c' ⊢
      linear_combination (norm := abel) ih' + c'
  have k := key N
  rw [hm, _root_.one_mul y] at k
  apply Additive.ofMul.injective
  have k' := congrArg Additive.ofMul k
  simp only [ofMul_mul] at k' ⊢
  linear_combination (norm := abel) k'

section Theta
variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {L : RigLB G} (c : CubicalStr G L)

theorem exists_thetaGen {T : Over S} (x : T ⟶ G) {N : ℕ} (hx : x ^ N = 1)
    (f : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(1 : T ⟶ G).left, x.left] ![(N : ℤ), -(N : ℤ)])) (hf : f.IsGen) :
    ∃ t : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(snd T G).left, ((fst T G ≫ x) * snd T G).left] ![(N : ℤ), -(N : ℤ)]),
      t.IsGen ∧ ∀ (T' : Over S) (τ : T' ⟶ T) (y : T' ⟶ G) (z : T'.left) (J), Good L.L z J →
        val t (lift τ y).left z J = cubN (cubV c z J) N 1 (τ ≫ x) y * val f τ.left z J := by
  obtain ⟨n, hn, vn⟩ := exists_cubN c 1 (fst T G ≫ x) (snd T G) N
  have hm : (fst T G ≫ x) ^ N = 1 := by rw [← MonObj.comp_pow, hx, MonObj.comp_one]
  obtain ⟨t, ht, vt⟩ := exists_gen L.isLB (φ' := ![(snd T G).left, ((fst T G ≫ x) * snd T G).left])
    (ε' := ![(N : ℤ), -(N : ℤ)]) (fun U _ h => by
      have q : (fst T G).left ≫ (1 : T ⟶ G).left = (1 : T ⊗ G ⟶ G).left :=
        congrArg (fun q : T ⊗ G ⟶ G => q.left) (MonObj.comp_one (M := G) (fst T G))
      have p : ∏ k : Fin 2, h ((fst T G).left ≫ ![(1 : T ⟶ G).left, x.left] k) ^ (![(N : ℤ), -(N : ℤ)] k) =
          h (1 : T ⊗ G ⟶ G).left ^ (N : ℤ) * h (fst T G ≫ x).left ^ (-(N : ℤ)) := by
        rw [Fin.prod_univ_two, ← q]; rfl
      refine (DVR.prod_sum₂ (K := Fin 8) (K' := Fin 2) (U := U) _ rfl p).trans ?_
      rw [hm]
      apply Additive.ofMul.injective
      simp [Fin.prod_univ_succ, ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
      module)
    (LB.mulGen L.L _ _ _ _ n (LB.pullGen L.L _ _ f (fst T G).left))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ hn (DVR.pullGen_isGen _ _ _ _ hf _))
  refine ⟨t, ht, fun T' τ y z J hJ => ?_⟩
  refine (vt _ _ z J hJ).trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((vn T' _ z J hJ).trans ?_)
    ((val_pull hJ _ _ _).trans ?_)))
  · rw [MonObj.comp_one, lift_fst_assoc, lift_snd]
  · rw [← Over.comp_left, lift_fst]

end Theta

section ThetaSec
variable {S : Scheme.{0}} {G : Over S} [GrpObj G] {L : LB G.left}

theorem exists_translSec (hL : L.IsLB) {T : Over S} (x : T ⟶ G) {N : ℤ}
    (t : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T G).left, ((fst T G ≫ x) * snd T G).left] ![N, -N]))
    (ht : t.IsGen) (σ : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => (snd (𝟙_ _) G).left) (fun _ => N))) :
    ∃ σ' : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => (snd T G).left) (fun _ => N)),
      ∀ (T' : Over S) (τ : T' ⟶ T) (y : T' ⟶ G) (z : T'.left) (J), Good L z J →
        sval σ' (lift τ y).left z J =
          sval σ (lift (toUnit T') ((τ ≫ x) * y)).left z J * (val t (lift τ y).left z J).val := by
  obtain ⟨σ', v⟩ := exists_sec hL (φ' := fun _ : Fin 1 => (snd T G).left) (ε' := fun _ => N) (fun U _ h => by
      have q : (lift (toUnit (T ⊗ G)) ((fst T G ≫ x) * snd T G)).left ≫ (snd (𝟙_ _) G).left =
          ((fst T G ≫ x) * snd T G).left := by rw [← Over.comp_left, lift_snd]
      refine (DVR.prod_sum₂ (K := Fin 1) (K' := Fin 2) (U := U) _ (Fin.prod_univ_one _) (Fin.prod_univ_two _)).trans ?_
      rw [Fin.prod_univ_one]
      show h (_ ≫ _) ^ N * (h (snd T G).left ^ N * h ((fst T G ≫ x) * snd T G).left ^ (-N)) = _
      rw [q, zpow_neg, mul_left_comm, mul_inv_cancel, _root_.mul_one])
    (pullMulSec σ (lift (toUnit (T ⊗ G)) ((fst T G ≫ x) * snd T G)).left t ht)
  refine ⟨σ', fun T' τ y z J hJ => (v _ _ z J hJ).trans ((sval_pullMulSec _ _ _ _ _ z hJ).trans ?_)⟩
  rw [← Over.comp_left, comp_lift, MonObj.comp_mul, lift_fst_assoc, lift_snd, toUnit_unique (_ ≫ _) (toUnit T')]

end ThetaSec

section Base
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R}
open ReciprocityTheory.ChartRestriction.G.DVR

theorem prod_famT {T T' : Over (Spec (CommRingCat.of R))} (ρ : T' ⟶ T ⊗ D.P.A) (α : D.X) (k : ℕ) {U : Type}
    [CommGroup U] (h : (T'.left ⟶ D.P.A.left) → U) : ∏ i, h (ρ.left ≫ famφT D T α i) ^ DegPre.famε k i =
      h (ρ ≫ snd _ _).left ^ ((k : ℤ) - 1) * h (cP D T' α * (ρ ≫ snd _ _)).left * (h (cP D T' α).left)⁻¹ *
        h (1 : T' ⟶ D.P.A).left := by
  have e₁ : ρ.left ≫ famφT D T α 1 = (cP D T' α * (ρ ≫ snd _ _)).left :=
    congrArg (fun q => q.left) ((MonObj.comp_mul ρ (snd _ _) (cP D _ α)).trans (by rw [comp_cP, mul_comm]))
  have e₂ : ρ.left ≫ famφT D T α 2 = (cP D T' α).left := congrArg (fun q => q.left) (comp_cP D ρ α)
  have e₃ : ρ.left ≫ famφT D T α 3 = (1 : T' ⟶ D.P.A).left :=
    congrArg (fun q : T' ⟶ D.P.A => q.left) (MonObj.comp_one (M := D.P.A) ρ)
  rw [Fin.prod_univ_four, e₁, e₂, e₃]
  show _ ^ ((k : ℤ) - 1) * _ ^ (1 : ℤ) * _ ^ (-1 : ℤ) * _ ^ (1 : ℤ) = _
  rw [zpow_one, zpow_one, zpow_neg_one]; rfl

def fac {T T' : Over (Spec (CommRingCat.of R))} (g : GtPt D T) (N : ℕ)
    (w : LB.Gen (LB.LinComb D.P.L (K := Fin 2) ![(1 : T ⟶ D.P.A).left, g.b.left] ![(N : ℤ), -(N : ℤ)])) (α : D.X)
    (τ : T' ⟶ T) (y : T' ⟶ D.P.A) (z : T'.left) (J : (T'.left ⟶ D.P.A.left) → D.P.L.ι) :
    (T'.left.presheaf.stalk z)ˣ :=
  cubN (th D z J) N 1 (τ ≫ g.b) y * val w τ.left z J * val (g.s α) τ.left z J *
    (th D z J (cP D T' α) (τ ≫ g.b) y)⁻¹

theorem exists_translFam {T : Over (Spec (CommRingCat.of R))} (g : GtPt D T) {N : ℕ} (hb : g.b ^ N = 1)
    (w : LB.Gen (LB.LinComb D.P.L (K := Fin 2) ![(1 : T ⟶ D.P.A).left, g.b.left] ![(N : ℤ), -(N : ℤ)]))
    (hw : w.IsGen) (α : D.X) (f : SecBT D (𝟙_ _) N α) :
    ∃ f' : SecBT D T N α, ∀ (T' : Over (Spec (CommRingCat.of R))) (τ : T' ⟶ T) (y : T' ⟶ D.P.A) (z : T'.left) (J),
      Good D.P.L z J → sval f' (lift τ y).left z J =
        sval f (lift (toUnit T') ((τ ≫ g.b) * y)).left z J * (fac g N w α τ y z J).val := by
  obtain ⟨t, ht, vt⟩ := exists_thetaGen D.cub g.b hb w hw
  let a : T ⊗ D.P.A ⟶ D.P.A := cP D _ α
  let m : T ⊗ D.P.A ⟶ D.P.A := fst _ _ ≫ g.b
  let x : T ⊗ D.P.A ⟶ D.P.A := snd _ _
  let u := LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ t (LB.pullGen D.P.L _ _ (g.s α) (fst T D.P.A).left))
    (LB.invGen D.P.L _ _ (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (lift a (lift m x)).left))
  have hu : u.IsGen := mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ ht (pullGen_isGen _ _ _ _ (g.isGen α) _))
    (invGen_isGen _ _ _ _ (pullGen_isGen _ _ _ _ D.cub.isGen _))
  obtain ⟨f', v⟩ := exists_sec D.P.isLB (φ' := famφT D T α) (ε' := DegPre.famε N) (fun U _ h => by
      have p₁ := prod_cub a m x h
      have p₂ := FormalPoint.prod_gtφT (fst T D.P.A) g.b α h
      have p₃ := prod_famT (𝟙 (T ⊗ D.P.A)) α N h
      have p₄ := prod_famT (lift (toUnit (T ⊗ D.P.A)) (m * x)) α N h
      have p₅ : ∏ k : Fin 2, h (![x.left, (m * x).left] k) ^ (![(N : ℤ), -(N : ℤ)] k) =
          h x.left ^ (N : ℤ) * h (m * x).left ^ (-(N : ℤ)) := Fin.prod_univ_two _
      simp only [Over.id_left, Category.id_comp] at p₃
      rw [lift_snd, ← _root_.mul_assoc (cP D _ α)] at p₄
      refine Eq.trans (prod_sum₂ (K := Fin 4) (K' := (Fin 2 ⊕ Fin 4) ⊕ thK) (U := U) _ p₄
        (prod_sum₂ (K := Fin 2 ⊕ Fin 4) (K' := thK) (U := U) _
          (prod_sum₂ (K := Fin 2) (K' := Fin 4) (U := U) _ p₅ p₂) (prod_neg _ _ p₁))) (Eq.trans ?_ p₃.symm)
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, a, m, x]
      module)
    (pullMulSec f (lift (toUnit (T ⊗ D.P.A)) (m * x)).left u hu)
  refine ⟨f', fun T' τ y z J hJ => (v _ _ z J hJ).trans ((sval_pullMulSec _ _ _ _ _ z hJ).trans ?_)⟩
  have e : val u (lift τ y).left z J = fac g N w α τ y z J := by
    refine (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
      (vt T' τ y z J hJ) ((val_pull hJ _ _ _).trans ?_))) ((val_inv _ _).trans (congrArg (·⁻¹)
      ((val_cub D.cub (lift τ y) hJ _ _ _).trans ?_))))
    · rw [← Over.comp_left, lift_fst]
    · rw [comp_cP, lift_fst_assoc, lift_snd]
  rw [e, ← Over.comp_left, comp_lift, MonObj.comp_mul, lift_fst_assoc, lift_snd, toUnit_unique (_ ≫ _) (toUnit T')]

end Base

end GlobalTheory.UU.Transl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIntegralFamiliesSpanGenerateValuationRingsStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.exists_integral_families_span_generate_valuationRings : PolBaseChangeSt → GlobalFnsSt → DVR.TwistBaseChangeStatement → ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (I : Ideal R), AdmBase R I → ∀ (φ : R →+* R') (D : DegData R I) (D' : DegPre R') (hD : IsPullDeg φ D.toPre D') (k : ℕ), 1 ≤ k → ∃ (n : ℕ) (F₀ : Fin n → Fam D.toPre (FractionRing R) k) (f : Fin n → ∀ α, D.toPre.SecB k α) (F₁ : Fin n → Fam D' (FractionRing R') k) (f' : Fin n → ∀ α, D'.SecB k α), (∀ i, (∀ α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing R) α) (DegPre.famε k) ((F₀ i).s α) (D.toPre.famφB α) (DegPre.famε k) (f i α) (DegPre.prB D.toPre (FractionRing R)).left 1) ∧ (∀ α, GeneratorPullback.SecScal D'.P.L (DegPre.famφ D' (FractionRing R') α) (DegPre.famε k) ((F₁ i).s α) (D'.famφB α) (DegPre.famε k) (f' i α) (DegPre.prB D' (FractionRing R')).left 1) ∧ (∀ x : D'.X, (∀ (Z : Scheme.{0}) (r : Z ⟶ D'.P.A.left) (z : Z) (p : Fin 4 → D.toPre.P.L.ι) (q : Fin 4 → D'.P.L.ι), (∀ κ, ((hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf φ))) ((D'.famφB x) κ (r z)) ∈ D.toPre.P.L.U (p κ)) → (∀ κ, (D'.famφB x) κ (r z) ∈ D'.P.L.U (q κ)) → Geo.Tor.gs (r ≫ (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf φ))) z (LB.wchart D.toPre.P.L (D.toPre.famφB (hD.xe x)) p) ((f i (hD.xe x)).f p) = (∏ κ, Geo.Tor.gw hD.w (r ≫ (D'.famφB x) κ) z (p κ) (q κ) ^ (DegPre.famε k) κ).val * Geo.Tor.gs r z (LB.wchart D'.P.L (D'.famφB x) q) ((f' i x).f q)))) ∧ Submodule.span (FractionRing R') (Set.range F₁) = ⊤ ∧ (∀ (S : Type) [CommRing S] [IsDomain S] [ValuationRing S] (σ : R →+* S) (F : Type) [Field F] [Algebra (FractionRing R) F] (ιF : S →+* F), Function.Injective ιF → ∀ (ρ : TF (R := R) F ⟶ (Over.mk (specOf σ))), ρ.left = specOf ιF → ∀ (F' : Type) [Field F'] [Algebra (FractionRing R') F'] (π : S →+* F'), IsLocalHom π → (∀ r : R, π (σ r) = algebraMap (FractionRing R') F' (algebraMap R' (FractionRing R') (φ r))) → ∀ s : Fam D.toPre F k, (∃ g : ∀ α, LB.Sec (LB.LinComb D.toPre.P.L (fun i => (snd (Over.mk (specOf σ)) D.toPre.P.A).left ≫ D.toPre.famφB α i) (DegPre.famε k)), (∀ α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε k) (s.s α) (fun i => (snd (Over.mk (specOf σ)) D.toPre.P.A).left ≫ D.toPre.famφB α i) (DegPre.famε k) (g α) (ρ ▷ D.toPre.P.A).left 1)) → ∃ c : Fin n → S, ∀ α, GeneratorPullback.SecLin D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε k) (s.s α) (D.toPre.famφB α) (DegPre.famε k) (fun i => f i α) (DegPre.prB D.toPre F).left (fun i => scal (fst (TF (R := R) F) D.toPre.P.A).left (ιF (c i)))) := by
  first | exact @GlobalTheory.FamGen.exists_span_generate | exact GlobalTheory.FamGen.exists_span_generate | (intros; apply GlobalTheory.FamGen.exists_span_generate <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpFOfPull
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory

theorem expF_of_pull : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (I : Ideal R) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : PreU I D A G) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ) (σ : U.SecGT (𝟙_ _) k) (f : ∀ α, SecBT D (𝟙_ _) k α) (t : LB.Sec (LPow A.A A.L (k : ℤ) (TFK (R := R) F))) (s : Raw D F k), U.ExpT (𝟙_ _) k σ f → U.PullG F (toUnit _) k σ t → PullB D F (toUnit _) k f s → U.ExpF F k t s :=
  fun R _ _ D I A G _ _ U F _ _ k σ f t s hE hG hB =>
    GlobalTheory.UU.IntExp.expF_of_expT R I D A G U F k σ f t s hE hG hB

end GlobalTheory
end

