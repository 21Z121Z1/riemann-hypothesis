import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullUUnitsCompatGeneric
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0013
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0067
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0005
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0024
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0013
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationEndomorphismsToCompleteDvr
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0012
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0060
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0063
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaOperatorPointZeroOfPowerEigen
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section

namespace GlobalTheory.ThetaEigen

theorem gs_pow {X Z : Scheme.{0}} (r : Z ⟶ X) (z : Z) (U : X.Opens) (h : r z ∈ U) (a : Γ(X, U)) (n : ℕ) :
    gs r z U (a ^ n) = gs r z U a ^ n := by simp only [gs_eq r z U h, map_pow]

theorem sval_pow {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) (pr : Y ⟶ X) (a b : ℤ) (l : ℕ)
    (th : LB.Sec (LB.LinComb L (fun _ : Fin 1 => pr) (fun _ => a)))
    (t : LB.Sec (LB.LinComb L (fun _ : Fin 1 => pr) (fun _ => b)))
    (hp : ∀ y J, Good L y J → sval t (𝟙 Y) y J = sval th (𝟙 Y) y J ^ l)
    {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (J) (hJ : Good L z J) : sval t r z J = sval th r z J ^ l := by
  have key : ∀ j : L.ι, (t.f (fun _ => j) : Γ(Y, LB.wchart L (fun _ : Fin 1 => pr) (fun _ => j))) =
      (show Γ(Y, LB.wchart L (fun _ : Fin 1 => pr) (fun _ => j)) from th.f (fun _ => j)) ^ l := fun j =>
    fn_ext (V := LB.wchart L (fun _ : Fin 1 => pr) (fun _ => j)) fun y hy => by
      obtain ⟨I, hI, e⟩ := exists_good L hL y (K := PUnit) (fun _ => 𝟙 Y ≫ pr) (fun _ => j) (fun _ _ _ => rfl)
        (fun _ => Set.mem_iInter.1 hy 0)
      have := hp y I hI
      rw [sval_of t _ y I (fun _ => j) (fun _ => e PUnit.unit),
        sval_of th _ y I (fun _ => j) (fun _ => e PUnit.unit)] at this
      exact this.trans (gs_pow _ y _ hy _ l).symm
  exact (congrArg (gs r z _) (key _)).trans (gs_pow r z _ (hJ.mem (fun _ : Fin 1 => pr) r) _ l)

theorem exists_gen_of_eigen {X Y : Scheme.{0}} [IsIntegral Y] (hN : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
    {L : LB X} (hL : L.IsLB) (pr m : Y ⟶ X) (τ : Y ⟶ Y) (hm : τ ≫ pr = m) (l : ℕ) (hl : 1 ≤ l)
    (th : LB.Sec (LB.LinComb L (fun _ : Fin 1 => pr) (fun _ => ((1 : ℕ) : ℤ))))
    (t : LB.Sec (LB.LinComb L (fun _ : Fin 1 => pr) (fun _ => (l : ℤ)))) (h0 : ∃ j, th.f j ≠ 0)
    (hp : ∀ y J, Good L y J → sval t (𝟙 Y) y J = sval th (𝟙 Y) y J ^ l) (c : Γ(Y, ⊤)ˣ)
    (α : LB.Gen (LB.LinComb L (K := Fin 2) ![pr, m] ![(l : ℤ), -(l : ℤ)])) (hα : α.IsGen)
    (H : ∀ y J, Good L y J →
      gs (𝟙 Y) y ⊤ c.val * sval t (𝟙 Y) y J = (val α (𝟙 Y) y J).val * sval t (𝟙 Y ≫ τ) y J) :
    ∃ r : LB.Gen (LB.LinComb L (K := Fin 2) ![m, pr] ![1, -1]), r.IsGen := by
  obtain ⟨s₁, h₁⟩ := exists_sec hL (K' := PUnit) (φ' := fun _ => m) (ε' := fun _ => 1)
    (fun U _ h => by simp only [Fin.prod_univ_one, Fintype.prod_unique, hm, Nat.cast_one])
    (DVR.pullSec L _ _ th τ)
  obtain ⟨s₂, h₂⟩ := exists_sec hL (K' := PUnit) (φ' := fun _ => pr) (ε' := fun _ => 1)
    (fun U _ h => by simp only [Fin.prod_univ_one, Fintype.prod_unique, Nat.cast_one]) th
  obtain ⟨u, hu, h₃⟩ := exists_gen hL (K' := Fin 2) (φ' := ![m, pr]) (ε' := ![(l : ℤ), -(l : ℤ)])
    (fun U _ h => by
      simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, zpow_neg, inv_inv]
      exact _root_.mul_comm _ _)
    (DVR.scaleGen c (LB.invGen L _ _ α)) (DVR.scaleGen_isGen _ _ (DVR.invGen_isGen _ _ _ _ hα))
  have h₄ : ∀ y J, Good L y J → val u (𝟙 Y) y J = gm (𝟙 Y) y ⊤ c * (val α (𝟙 Y) y J)⁻¹ := fun y J hJ =>
    (h₃ _ _ y J hJ).trans ((map_mul _ _ _).trans (congrArg₂ (· * ·)
      (gm_res _ y le_top (hJ.mem ![pr, m] (𝟙 Y)) c) (val_inv α (𝟙 Y))))
  obtain ⟨r, hr, -⟩ := RootUnit.exists_gen_of_pow X Y hN L hL m pr l hl s₁ s₂ u hu
    (by
      obtain ⟨y⟩ : Nonempty Y := inferInstance
      choose J hJ using fun χ : Y ⟶ X => exists_chart hL (χ y)
      have hJ' : Good L y J := hJ
      refine ⟨fun _ => J (𝟙 Y ≫ pr), fun e => ?_⟩
      refine RootUnit.sec_gs_ne_zero th h0 y _ (hJ'.mem (fun _ : Fin 1 => pr) (𝟙 Y)) ?_
      refine (h₂ _ _ y J hJ').symm.trans ((congrArg (gs (𝟙 Y) y _) e).trans ?_)
      exact (RootUnit.gs_id y _ (hJ'.mem (fun _ : PUnit => pr) (𝟙 Y)) _).trans (map_zero _))
    (fun y J hJ => by
      have e₁ := (h₁ _ (𝟙 Y) y J hJ).trans (DVR.SectionScalarValuation.sval_pullSec _ _ th τ _ y hJ)
      have e₂ := h₂ _ (𝟙 Y) y J hJ
      have e := H y J hJ
      rw [hp y J hJ, sval_pow hL pr _ _ l th t hp _ y J hJ, gs_unit _ y ⊤ (by trivial)] at e
      refine (congrArg (· ^ l) e₁).trans (Eq.trans ?_ (congrArg₂ (fun a b => Units.val a * b ^ l) (h₄ y J hJ) e₂).symm)
      change _ = Units.val (_ * _) * _
      rw [Units.val_mul, mul_right_comm, e, mul_right_comm, Units.mul_inv, _root_.one_mul])
  exact ⟨r, hr⟩

theorem main : ∀ (S : Scheme.{0}) (P : PolAV S) (F : Type) [Field F] (p : Spec (CommRingCat.of F) ⟶ S) (l : ℕ), 1 ≤ l → ∀ (th : EA P p 1) (t : EA P p l) (θ : ThetaGrp P.A P.L (l : ℤ) (Over.mk p)) (c : Fˣ), th ≠ 0 → (∀ z J, Good P.L z J → sval (L := P.L) (φ := fun _ : Fin 1 => (snd (Over.mk p) P.A).left) (ε := fun _ => ((l : ℕ) : ℤ)) t.sec (𝟙 _) z J = sval (L := P.L) (φ := fun _ : Fin 1 => (snd (Over.mk p) P.A).left) (ε := fun _ => ((1 : ℕ) : ℤ)) th.sec (𝟙 _) z J ^ l) → IsActOf P.A P.L (l : ℤ) θ t.sec (c.val • t).sec → θ.pt = 1 := by
  intro S P F _ p l hl th t θ c h0 hp hθ
  haveI := P.isAb.smooth
  haveI := P.isAb.geomConnected
  haveI : IsIntegral (Over.mk p).left := inferInstanceAs (IsIntegral (Spec (CommRingCat.of F)))
  haveI := isIntegral_tensor_left_of_smooth_grpObj S P.A (Over.mk p)
  have hs : Smooth (fst (Over.mk p) P.A).left :=
    inferInstanceAs (Smooth (pullback.fst p P.A.hom))
  have hN := (isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field F _ _ hs).2.1
  let φ : F →+* Γ((Over.mk p ⊗ P.A).left, ⊤) :=
    (fst (Over.mk p) P.A).left.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom
  obtain ⟨r, hr⟩ := exists_gen_of_eigen (fun y => (hN y).2) P.isLB (snd (Over.mk p) P.A).left
    (translPt P.A θ.pt).left (translT P.A θ.pt).left (by rw [← Over.comp_left, translT, lift_snd]) l hl th.sec t.sec
    (not_forall.1 fun h => h0 ((SecMod.eq_zero_iff th).2 h)) hp (Units.map φ.toMonoidHom c) θ.φ θ.isGen
    (fun y J hJ => (SecMod.sval_smul hJ (𝟙 _) c.val t).symm.trans (ThetaLin.sval_of_isTwistPull P.A hθ (𝟙 _) y hJ))
  exact P.ktriv F p θ.pt fun _ => ⟨⊤, trivial, exists_isGen_pull (translDiff P.A P.L θ.pt) r hr _⟩

end GlobalTheory.ThetaEigen

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationEndomorphismsToCompleteDvrStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisation_endomorphisms_to_complete_dvr : LL → AllU fun {R} _ _ {I} {D} {A} {G} _ _ U => ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (φ : R →+* V), IsAdicComplete (maximalIdeal V) V → Function.Injective φ → I.map φ ≤ maximalIdeal V → ∃ (D' : DegData V (maximalIdeal V)) (hD : IsPullDeg φ D.toPre D'.toPre) (A' : PolAV (Spec (CommRingCat.of (FractionRing V)))) (U' : Unif (maximalIdeal V) D' A' ((Over.pullback (specOf φ)).obj G)), IsSemiAbelian ((Over.pullback (specOf φ)).obj G) ∧ IsPullUnif φ hD (Iso.refl _) U U' ∧ (∀ (F : Type) [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing V) F], (∀ r : R, algebraMap (FractionRing R) F (algebraMap R _ r) = algebraMap (FractionRing V) F (algebraMap V _ (φ r))) → (∀ g, ∃! g', IsPullGtF φ hD F g g') ∧ (∀ g', ∃! g, IsPullGtF φ hD F g g') ∧ (∀ g g' y, IsPullGtF φ hD F g g' → (GtPtF.IsIota (hD.xe y) g ↔ GtPtF.IsIota y g')) ∧ ∀ k g g' h h', IsPullGtF φ hD F g g' → IsPullGtF φ hD F h h' → (GtPtF.IsNsmul k g h ↔ GtPtF.IsNsmul k g' h')) ∧ ∀ E : EndU U.toUnifPre, ∃ E' : EndU U'.toUnifPre, E'.aG = (Over.pullback (specOf φ)).map E.aG ∧ (∀ χ, hD.xe (E'.h χ) = E.h (hD.xe χ)) ∧ ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing V) F], (∀ r : R, algebraMap (FractionRing R) F (algebraMap R _ r) = algebraMap (FractionRing V) F (algebraMap V _ (φ r))) → ∀ g₁ g₂ g₁' g₂', IsPullGtF φ hD F g₁ g₁' → IsPullGtF φ hD F g₂ g₂' → (E.Act g₁ g₂ ↔ E'.Act g₁' g₂') := by
  first | exact @GlobalTheory.UT.EndBaseChange.main | exact GlobalTheory.UT.EndBaseChange.main | (intros; apply GlobalTheory.UT.EndBaseChange.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValueExpansionOfChartExpansion
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.UU

theorem sval_of_secScal {X Y Y' Z : Scheme.{0}} {L : LB X} {K₁ K₂ : Type} [Fintype K₁] [Fintype K₂]
    {φ₁ : K₁ → (Y' ⟶ X)} {ε₁ : K₁ → ℤ} {s₁ : LB.Sec (LB.LinComb L φ₁ ε₁)}
    {φ₂ : K₂ → (Y ⟶ X)} {ε₂ : K₂ → ℤ} {s₂ : LB.Sec (LB.LinComb L φ₂ ε₂)} {h : Y' ⟶ Y} {c : Γ(Y', ⊤)}
    (H : GeneratorPullback.SecScal L φ₁ ε₁ s₁ φ₂ ε₂ s₂ h c) (r : Z ⟶ Y') (z : Z) {J : (Z ⟶ X) → L.ι}
    (hJ : Good L z J) : sval s₂ (r ≫ h) z J = gs r z ⊤ c * sval s₁ r z J := by
  have e := H (fun k => J (r ≫ φ₁ k)) (fun k => J (r ≫ h ≫ φ₂ k)) (by
    rintro (a | a) (b | b) e <;> exact congrArg (fun q => J (r ≫ q)) e)
  have hm : r z ∈ LB.wchart L φ₁ (fun k => J (r ≫ φ₁ k)) ⊓
      LB.wchart L (fun k => h ≫ φ₂ k) (fun k => J (r ≫ h ≫ φ₂ k)) :=
    ⟨hJ.mem φ₁ r, hJ.mem (fun k => h ≫ φ₂ k) r⟩
  have le : LB.wchart L (fun k => h ≫ φ₂ k) (fun k => J (r ≫ h ≫ φ₂ k)) ≤
      h ⁻¹ᵁ LB.wchart L φ₂ (fun k => J (r ≫ h ≫ φ₂ k)) :=
    fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k
  rw [sval_of s₂ (r ≫ h) z J (fun k => J (r ≫ h ≫ φ₂ k)) (fun k => by rw [Category.assoc])]
  have e2 := congrArg (gs r z _) e
  exact ((gs_res r z _ hm _).trans (gs_pull r h z _ (le hm.2) _)).symm.trans (e2.trans ((gs_mul r z _ hm _ _).trans
    (congrArg₂ (· * ·) (gs_res r z le_top hm _) (gs_res r z _ hm _))))

theorem scal_specMap {A C : Type} [CommRing A] [CommRing C] (φ : A →+* C) {Y : Scheme.{0}}
    (p : Y ⟶ Spec (CommRingCat.of C)) (a : A) :
    scal (p ≫ Spec.map (CommRingCat.ofHom φ)) a = scal p (φ a) := by
  have e := congrArg (fun q => q.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))
  exact congrArg p.appTop.hom e.symm

theorem gs_scal_inv_mul {R : Type} [CommRing R] [IsDomain R] {Y₁ Y₂ Z : Scheme.{0}}
    (p₁ : Y₁ ⟶ Spec (CommRingCat.of (FractionRing R))) (p₂ : Y₂ ⟶ Spec (CommRingCat.of R))
    (r₁ : Z ⟶ Y₁) (r₂ : Z ⟶ Y₂) (h : r₂ ≫ p₂ = ((r₁ ≫ p₁) ≫ jFK (R := R) (FractionRing R)) ≫ jK R) (z : Z)
    {a : R} (ha : a ≠ 0) :
    gs r₁ z ⊤ (scal p₁ (algebraMap R (FractionRing R) a)⁻¹) * gs r₂ z ⊤ (scal p₂ a) = 1 := by
  have k : ∀ {S : Type} [CommRing S] {Y : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of S)) (r : Z ⟶ Y) (c : S),
      gs r z ⊤ (scal p c) = gs (𝟙 _) z ⊤ (scal (r ≫ p) c) := by
    intro S _ Y p r c
    calc gs r z ⊤ (scal p c) = gs (𝟙 _ ≫ r) z ⊤ (scal p c) := by rw [Category.id_comp]
      _ = gs (𝟙 _) z (r ⁻¹ᵁ ⊤) ((r.app ⊤).hom (scal p c)) := (gs_pull (𝟙 _) r z ⊤ (by trivial) _).symm
      _ = gs (𝟙 _) z ⊤ (scal (r ≫ p) c) := rfl
  have e : scal (((r₁ ≫ p₁) ≫ jFK (R := R) (FractionRing R)) ≫ jK R) a =
      scal (r₁ ≫ p₁) (algebraMap R (FractionRing R) a) :=
    (scal_specMap _ _ a).trans (scal_specMap _ _ _)
  have ha' : algebraMap R (FractionRing R) a ≠ 0 := fun h0 =>
    ha (IsFractionRing.injective R (FractionRing R) (h0.trans (map_zero _).symm))
  rw [k p₁, k p₂, h, e, ← gs_mul _ z ⊤ trivial, scal, scal, ← map_mul, ← map_mul, inv_mul_cancel₀ ha', map_one, map_one,
    gs_eq _ z ⊤ trivial, map_one, map_one]

theorem expF_of_expands : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : PreU I D.toPre A G) (U' : UnifPre I D A G), Match U U' → ∀ (k : ℕ) (σ : U'.SecK k) (σ₀) (t) (s : Fam D.toPre (FractionRing R) k), HEq σ σ₀ → U.SameK (k := k) σ₀ t → U'.Expands k σ s → U.ExpF (FractionRing R) k t s.s := by
  intro R _ _ I D A G _ _ U U' hM k σ σ₀ t s hσ hK hE
  obtain ⟨r, hr, τ, f, hτ, hf, hE⟩ := hE
  have hL := hM.LG
  have hX := fun τ₀ τ' f' h₁ h₂ h₃ => expT_of_expandsAt R I D A G U U' hM k τ τ₀ τ' f f' h₁ h₂ h₃ hE
  clear hE hM
  cases U'
  dsimp only at hL
  subst hL
  cases hσ
  obtain ⟨e₁, -, e₃, -⟩ := GlobalTheory.UnitSec.same_exists R D.toPre G U.P.L.L U.P.L.isLB k
  obtain ⟨τ', hτ'⟩ := e₁ τ
  obtain ⟨f', hf'⟩ := e₃ f
  refine ⟨1, fun _ => (algebraMap R (FractionRing R) r)⁻¹, fun _ => τ', fun _ => f',
    fun _ => hX τ τ' f' HEq.rfl hτ' hf', ?_, ?_⟩
  · intro Z rA y rG h₁ h₂ z JA JG hJA hJG
    refine (hK Z rA y h₁ z JA JG hJA hJG).trans ?_
    rw [Fin.sum_univ_one, hτ' Z rG z JG hJG, h₂]
    refine Eq.trans ?_ (congrArg (_ * ·) (sval_of_secScal hτ y z hJG)).symm
    rw [← _root_.mul_assoc]
    refine (_root_.one_mul _).symm.trans (congrArg (· * _) (gs_scal_inv_mul _ _ rA y ?_ z hr).symm)
    have w₁ := Over.w (fst (TFK (R := R) (FractionRing R)) A.A)
    have w₂ := Over.w (snd (TFK (R := R) (FractionRing R)) A.A)
    have w₃ := Over.w U.gen.hom
    have w₄ : (rA ≫ (fst (TFK (R := R) (FractionRing R)) A.A).left) ≫ jFK (R := R) (FractionRing R) =
        y ≫ pullback.snd G.hom (jK R) :=
      (Category.assoc _ _ _).trans ((congrArg (rA ≫ ·) (w₁.trans w₂.symm)).trans ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ A.A.hom) h₁).trans ((Category.assoc _ _ _).trans (congrArg (y ≫ ·) w₃)))))
    exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ jK R) w₄.symm)
  · intro α Z rF rB h₁ z J hJ
    rw [Fin.sum_univ_one, hf' α Z rB z J hJ, h₁]
    refine Eq.trans ?_ (congrArg (_ * ·) (sval_of_secScal (hf α) rF z hJ)).symm
    rw [← _root_.mul_assoc]
    refine (_root_.one_mul _).symm.trans (congrArg (· * _) (gs_scal_inv_mul _ _ rF rF ?_ z hr).symm)
    have w₁ := Over.w (fst (TF (R := R) (FractionRing R)) D.toPre.P.A)
    exact (congrArg (rF ≫ ·) w₁.symm).trans ((Category.assoc _ _ _).symm.trans (Category.assoc _ _ _).symm)

end GlobalTheory.UU
end

