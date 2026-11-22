import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0159
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LocGenOfTrivial
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0055
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0120
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0141
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0138
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0160
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0019
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0130
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGenericIsoOfUniformisationsIsoData
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0111
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsAbelianSchemeAway
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0132
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0133

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AbelianPartsIsoLabelsOfThetaPointAndValuesStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianPartsIsoLabels_of_thetaPoint_and_values : Laws → ThetaPtDeterminesSt → BrUthSt → UrCSt := by
  first | exact @GlobalTheory.Ex.AbPartIso.main | exact GlobalTheory.Ex.AbPartIso.main | (intros; apply GlobalTheory.Ex.AbPartIso.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ArcDataDescendsFromCompleteDVRStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arcData_descends_from_completeDVR : Laws → Laws2 → Laws3 → Laws4 → Laws5 → Laws6 → HomExtSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (W₀ : ValuationSubring ℂ) (Y : Model Xo c (c.V W₀).subtype) (O' : Type) [CommRing O'] [IsDomain O'] [CharZero O'] (b : c.V W₀ →+* O') (a : ArcIn D l (c.V W₀).subtype O' b) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CharZero R] (I : Ideal R) (f : O' →+* R) (u : R), AdmBase R I → I ≠ ⊤ → Function.Injective f → ∀ (χ : Sp R ⟶ Y.X) (y : Sp (FractionRing R) ⟶ Xo.XF c), y ≫ Y.j = jK R ≫ χ → ∀ (t : SAB H (Sp R)) (m : SABMap t Y.t χ) (P : PELUnif I t), P.TorsionIso → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDvr V → ∀ g : R →+* V, Function.Injective g → I.map g ≤ IsLocalRing.maximalIdeal V → ¬ IsUnit (g u) → (∀ x, x ≠ 0 → IsUnit (g (f x))) → Y.HasArcData a (IsLocalRing.maximalIdeal V) (g.comp f) (g u) (spMap g ≫ χ) → Y.HasArcData a I f u χ := by
  first | exact @GlobalTheory.ArcDataDescent.hasArcData_descends | exact GlobalTheory.ArcDataDescent.hasArcData_descends | (intros; apply GlobalTheory.ArcDataDescent.hasArcData_descends <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ClosedPointMemRange
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
open GlobalTheory.AbLaw

noncomputable section
namespace GlobalTheory.TowerAlg

theorem closedPoint_mem_range {R : Type} [CommRing R] [IsLocalRing R] {I : Ideal R} (hI : I ≠ ⊤) (e : ℕ) :
    IsLocalRing.closedPoint R ∈ Set.range (thick R I e) := by
  have h := range_comap_of_surjective _ _ (Ideal.Quotient.mk_surjective (I := I ^ (e + 1)))
  refine h.ge ?_
  rw [Ideal.mk_ker]
  exact (Ideal.pow_le_self (Nat.succ_ne_zero e)).trans (IsLocalRing.le_maximalIdeal hI)

theorem triv_of_forall_thick (hG : GlobalFnsSt) (hS : SecAlgSt) {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V]
    {I : Ideal V} (hI : I ≠ ⊤) (hV : IsAdicComplete I V) (B : Over (Spec (CommRingCat.of V))) [GrpObj B]
    (hB : IsAbelianScheme B) (hp : IsProjBy B.hom) (N : LB B.left) (hN : N.IsLB)
    (ht : ∀ e, Triv (N.pull (fstG I e B).left)) : Triv N := by
  let o : Spec (CommRingCat.of V) ⟶ B.left := (η[B]).left
  have ho : o ≫ B.hom = 𝟙 _ := Over.w η[B]
  obtain ⟨c, hc⟩ := DVR.exists_gen_of_local N hN (K := PUnit) (fun _ => o) (fun _ => 1)
  have pb : ∀ e, IsPullback (fstG I e B).left (thickObj V I e B).hom B.hom (thick V I e) :=
    fun e => IsPullback.of_hasPullback B.hom (thick V I e)
  choose t tg tv using fun e => AbTriv.exists_normalised hN ho c hc (pb e) (ht e)
  have tm : ∀ e, thickMap V I e B ≫ (fstG I (e + 1) B).left = (fstG I e B).left := fun e =>
    (pullback.lift_fst _ _ _).trans (Category.comp_id _)
  have compat : ∀ e z J, Good N z J → val (t (e + 1)) (thickMap V I e B) z J = val (t e) (𝟙 _) z J := by
    intro e z J hJ
    let a := (pb e).lift (thick V I e ≫ o) (𝟙 _) (by rw [Category.assoc, ho, Category.comp_id, Category.id_comp])
    have a₁ : a ≫ (fstG I e B).left = thick V I e ≫ o := (pb e).lift_fst _ _ _
    have key := gen_unique' hN (fun U _ k => by simp only [tm e]) (thickObj V I e B).hom a ((pb e).lift_snd _ _ _)
      (hG _ _ (TLinPf.isAb_pullback (thick V I e) B hB)).2 (tg e)
      (DVR.pullGen_isGen _ _ _ _ (tg (e + 1)) (thickMap V I e B))
      (fun y J hJ => (tv e _ a _ y J hJ a₁).trans ((val_pull hJ _ _ _).trans
        (tv (e + 1) _ _ _ y J hJ (by rw [Category.assoc, tm e, a₁]))).symm) _ (𝟙 _) z J hJ
    rw [val_pull hJ, Category.id_comp] at key
    exact key.symm
  obtain ⟨s, hs, -⟩ := hS V I hV B hB.smooth hp N hN (fun e => genSec (t e) (tg e))
    (fun e z J hJ => (sval_genSec _ _ _ z hJ).trans
      ((congrArg Units.val (compat e z J hJ)).trans (sval_genSec _ _ _ z hJ).symm))
  have := hB.proper
  have top : nonzeroLocus s = ⊤ := AbTriv.eq_top_of_closed_fibre B.hom _ fun x hx => by
    have hm : x ∈ Set.range (pullback.fst B.hom (thick V I 0)) := by
      rw [Scheme.Pullback.range_fst, Set.mem_preimage, hx]
      exact closedPoint_mem_range hI 0
    obtain ⟨z, rfl⟩ := hm
    choose J hJ using fun ψ : ((Over.map (thick V I 0)).obj (thickObj V I 0 B)).left ⟶ B.left =>
      exists_chart hN (ψ z)
    refine (TwistZero.mem_nonzeroLocus_iff s (fstG I 0 B).left z hJ).2 ?_
    rw [hs 0 z J hJ, sval_genSec _ _ _ z hJ]
    exact Units.isUnit _
  refine AbTriv.triv_of_pull_id (TwistZero.triv_of_sec hN s fun y J hJ => ?_)
  exact (TwistZero.mem_nonzeroLocus_iff s (𝟙 _) y hJ).1 (by rw [top]; trivial)

theorem triv_pull_of_gen {X X' Y Y' Z : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} (hL : L.IsLB) (hL' : L'.IsLB)
    (hw : LBIso L' (L.pull F)) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {φ' : K → (Y' ⟶ X')} {ε : K → ℤ}
    (a : LB.Gen (LB.LinComb L' φ' ε)) (ha : a.IsGen) (r : Z ⟶ Y') (π : Z ⟶ Y)
    (hc : ∀ k, (r ≫ φ' k) ≫ F = π ≫ φ k) : Triv ((LB.LinComb L φ ε).pull π) := by
  obtain ⟨w, hw⟩ := hw
  obtain ⟨t, ht, -⟩ := exists_up ((isGen_iff w).1 hw) hL hL' _ (DVR.pullGen_isGen _ _ _ _ ha r)
  refine (KerPow.pull_iff φ ε π).2 ?_
  rw [← (funext hc : (fun k => (r ≫ φ' k) ≫ F) = fun k => π ≫ φ k)]
  exact ⟨t, ht⟩

section Level
variable {S S' Z : Scheme.{0}} {B : Over S} {B' : Over S'} [GrpObj B] [IsCommMonObj B] [GrpObj B'] [IsCommMonObj B']
  {f : S' ⟶ S} {F : B'.left ⟶ B.left}

omit [IsCommMonObj B] [IsCommMonObj B'] in

theorem toBase_mul (h : IsGrpPullback B' B f F) (T : Over S') (x y : T ⟶ B') :
    toBase h.1.w (x * y) = toBase h.1.w x * toBase h.1.w y :=
  Over.OverMorphism.ext (h.2 T x y _ _ rfl rfl).symm

theorem triv_theta (h : IsGrpPullback B' B f F) (M' : CP B') {L : LB B.left} (hL : L.IsLB)
    (hw : LBIso M'.L.L (L.pull F)) (π : Z ⟶ (G3 B).left) (z : Z ⟶ S') (hz : π ≫ (G3 B).hom = z ≫ f) :
    Triv ((Theta B L).pull π) := by
  let ρ : Over.mk ((Over.mk z).hom ≫ f) ⟶ G3 B := Over.homMk π hz
  let x : Fin 3 → (Over.mk z ⟶ B') := fun i =>
    Over.homMk (h.1.lift (ρ ≫ x3 B i).left z (Over.w (ρ ≫ x3 B i))) (h.1.lift_snd _ _ _)
  let β := toBaseHom (toBase_mul h) (Over.mk z)
  have hx : ∀ i, β (x i) = ρ ≫ x3 B i := fun i => Over.OverMorphism.ext (h.1.lift_fst _ _ _)
  let r : Over.mk z ⟶ G3 B' := lift (x 0) (lift (x 1) (x 2))
  have hr : ∀ i, r ≫ x3 B' i = x i := fun i => by fin_cases i <;> simp [r, x3]
  refine triv_pull_of_gen hL M'.L.isLB hw (φ := thφ B (x3 B)) (φ' := thφ B' (x3 B')) (ε := thε) M'.c.t M'.c.isGen
    r.left π fun I => ?_
  have e : β (r ≫ psum B' (x3 B') I.down) = ρ ≫ psum B (x3 B) I.down :=
    (psum_hom (β.comp (preHom r)) (x3 B') I.down).trans ((congrArg (fun q => psum B q I.down) (funext fun i =>
      (congrArg β (hr i)).trans (hx i))).trans (psum_hom (preHom ρ) (x3 B) I.down).symm)
  exact congrArg (fun q => q.left) e

theorem triv_sym (h : IsGrpPullback B' B f F) (M' : CP B') {L : LB B.left} (hL : L.IsLB)
    (hw : LBIso M'.L.L (L.pull F)) (π : Z ⟶ B.left) (z : Z ⟶ S') (hz : π ≫ B.hom = z ≫ f) :
    Triv ((LB.LinComb L (K := Fin 2) ![(ι[B]).left, 𝟙 B.left] ![1, -1]).pull π) := by
  let x : Over.mk z ⟶ B' := Over.homMk (h.1.lift π z hz) (h.1.lift_snd _ _ _)
  have hx : x.left ≫ F = π := h.1.lift_fst _ _ _
  refine triv_pull_of_gen hL M'.L.isLB hw M'.sym M'.sym_gen x.left π fun k => ?_
  fin_cases k
  · exact (inv_left_comp (toBase_mul h) x).trans (congrArg (· ≫ _) hx)
  · exact ((congrArg (· ≫ F) (Category.comp_id _)).trans hx).trans (Category.comp_id _).symm

end Level

section Pack
variable (hG : GlobalFnsSt) (hS : SecAlgSt) {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {I : Ideal R}
  (hI : I ≠ ⊤) (hc : IsAdicComplete I R) {Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))}
  [∀ e, GrpObj (Y e)] [∀ e, IsCommMonObj (Y e)] (N : ∀ e, CP (Y e)) {B : Over (Spec (CommRingCat.of R))} [GrpObj B]
  [IsCommMonObj B] (hB : IsAbelianScheme B) (hp : IsProjBy B.hom) {b : ∀ e, (Y e).left ⟶ B.left}
  (hg : ∀ e, IsGrpPullback (Y e) B (thick R I e) (b e)) {M : LB B.left} (hM : M.IsLB)
  (hiso : ∀ e, LBIso (N e).L.L (M.pull (b e)))
include hG hS hI hc hB hp hg hM hiso

theorem triv_theta_alg : Triv (Theta B M) :=
  triv_of_forall_thick hG hS hI hc (G3 B)
    (AbelianSchemeGerms.isAbelianScheme_tensor _ _ hB (AbelianSchemeGerms.isAbelianScheme_tensor _ _ hB hB))
    (isProjBy_tensor R _ _ hp (isProjBy_tensor R _ _ hp hp)) (Theta B M) (LB.isLB_linComb hM _ _) fun e =>
      triv_theta (hg e) (N e) hM (hiso e) (fstG I e (G3 B)).left (pullback.snd (G3 B).hom (thick R I e))
        (pullback.condition (f := (G3 B).hom) (g := thick R I e))

theorem triv_sym_alg : Triv (LB.LinComb M (K := Fin 2) ![(ι[B]).left, 𝟙 B.left] ![1, -1]) :=
  triv_of_forall_thick hG hS hI hc B hB hp _ (LB.isLB_linComb hM _ _) fun e =>
    triv_sym (hg e) (N e) hM (hiso e) (fstG I e B).left (pullback.snd B.hom (thick R I e))
      (pullback.condition (f := B.hom) (g := thick R I e))

theorem exists_cp_alg (hY : ∀ e, IsAbelianScheme (Y e)) :
    ∃ Q : CP B, Q.L.L = M ∧ ∀ e, IsCPPullback (N e) Q (thick R I e) (b e) := by
  obtain ⟨r, hr⟩ := DVR.exists_gen_of_local M hM (K := PUnit) (fun _ => eSec B) (fun _ => 1)
  obtain ⟨Q, hQ⟩ := AbPackage.exists_cp hG hB ⟨M, r, hM, hr⟩ (triv_theta_alg hG hS hI hc N hB hp hg hM hiso)
    (triv_sym_alg hG hS hI hc N hB hp hg hM hiso)
  have e₀ : Q.L.L = M := congrArg (fun q => q.L) hQ
  refine ⟨Q, e₀, fun e => ⟨hg e, ?_⟩⟩
  obtain ⟨w, hw⟩ : LBIso (N e).L.L (Q.L.L.pull (b e)) := by rw [e₀]; exact hiso e
  exact AbPackage.exists_isCPMap_of_iso hG (hY e) Q (N e) (toBase_mul (hg e)) w hw

end Pack

end GlobalTheory.TowerAlg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ClosureTestsExistAndReductionIndependent
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH.CoreTests

theorem image_iff {T H B G B' F P : Scheme.{0}} (h : H ⟶ B) (s : T ⟶ B) (g : G ⟶ B') (s' : T ⟶ B')
    (r : F ⟶ G) (q : F ⟶ T) (cart : IsPullback r q g s') (u : H ⟶ P) (v : G ⟶ P)
    (e : pullback h s ≅ F) (e₁ : e.hom ≫ q = pullback.snd _ _) (e₂ : e.hom ≫ r ≫ v = pullback.fst _ _ ≫ u)
    (x : T ⟶ P) :
    (∃ c : T ⟶ H, c ≫ h = s ∧ c ≫ u = x) ↔ ∃ c' : T ⟶ G, c' ≫ g = s' ∧ c' ≫ v = x := by
  constructor
  · rintro ⟨c, hc, rfl⟩
    refine ⟨pullback.lift c (𝟙 T) (by simpa using hc) ≫ e.hom ≫ r, ?_, ?_⟩
    · simp only [Category.assoc]
      rw [cart.w, reassoc_of% e₁, pullback.lift_snd_assoc, Category.id_comp]
    · simp only [Category.assoc]
      rw [e₂, pullback.lift_fst_assoc]
  · rintro ⟨c, hc, rfl⟩
    refine ⟨cart.lift c (𝟙 T) (by simpa using hc) ≫ e.inv ≫ pullback.fst _ _, ?_, ?_⟩
    · simp only [Category.assoc]
      rw [pullback.condition, ← reassoc_of% e₁, e.inv_hom_id_assoc, cart.lift_snd_assoc, Category.id_comp]
    · simp only [Category.assoc]
      rw [← e₂, e.inv_hom_id_assoc, cart.lift_fst_assoc]

theorem exists_test (hL : GlobalTheory.UT.LL) (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω]
    (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J)
    (hB : BaseFacts S M U₀ EE) (Q : Clos ρ M U₀ EE) (ex : Q.Ext) (hS : S.Big) (hG : ρ.HasGeo)
    (p : ℕ) [Fact p.Prime] (y : Sp (GlobalTheory.ZJ.OO p) ⟶ ex.core.Z) (hy : ex.core.Cl y) :
    ∃ τ : ex.core.Test y, ∀ x : Sp (GlobalTheory.ZJ.kb p) ⟶ Q.P.left, x ≫ Q.P.hom = GlobalTheory.ZJ.rPt p ≫ y →
      ((∃ c : Sp (GlobalTheory.ZJ.kb p) ⟶ τ.H.left, c ≫ τ.H.hom = GlobalTheory.ZJ.rPt p ≫ spMap τ.j ∧ c ≫ τ.f ≫ Q.G.ι = x) ↔
        (⊤ ≤ x ⁻¹ᵁ Q.G ∧ Q.InFib x)) := by
  obtain ⟨y₀, t, c, ⟨tm⟩⟩ := (GlobalTheory.T.exists_geometricTest_map_classicalPoint hL o Ω S ρ M U₀ EE hB Q hS hG).1 p y hy
  obtain ⟨τ, e, e₁, e₂⟩ := GlobalTheory.T.exists_uniformisationTest_of_geometricTest hL o Ω S ρ M U₀ EE hB Q ex p y y₀ t c tm hS
  refine ⟨τ, fun x hx => ?_⟩
  exact (image_iff _ _ _ _ _ _ t.mod.cart.1 _ _ e e₁ e₂ x).trans
    (GlobalTheory.T.specialFibre_image_test_independent hL o Ω S ρ M U₀ EE hB Q p y y₀ t c tm hS x hx)

end GlobalTheory.ZH.CoreTests

theorem GlobalTheory.ZH.Clos.Ext.hasTests_and_indep : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), BaseFacts S M U₀ EE → ∀ (Q : Clos ρ M U₀ EE) (ex : Q.Ext), S.Big → ρ.HasGeo → ex.core.HasTests ∧ ex.core.Indep := by
  intro hL o Ω _ _ _ _ S ρ M U₀ EE hB Q ex hS hG
  have key := GlobalTheory.ZH.CoreTests.exists_test hL o Ω S ρ M U₀ EE hB Q ex hS hG
  have hT : ex.core.HasTests := fun p _ y hy => ⟨(key p y hy).choose⟩
  refine ⟨hT, GlobalTheory.T.indep_of_nested_special_fibre_images _ hT fun p _ y y' hy hy' hr => ?_⟩
  obtain ⟨τ, hτ⟩ := key p y hy
  obtain ⟨τ', hτ'⟩ := key p y' hy'
  refine ⟨τ, τ', fun c hc => ?_⟩
  have hx : (c ≫ τ.f ≫ Q.G.ι) ≫ Q.P.hom = GlobalTheory.ZJ.rPt p ≫ y := by
    have h : c ≫ τ.f ≫ ex.core.GG.hom = GlobalTheory.ZJ.rPt p ≫ y := by
      rw [τ.f_over, reassoc_of% hc, τ.fac]
    simp only [Category.assoc]
    exact h
  obtain ⟨c', hc', hf⟩ := (hτ' _ (hx.trans hr)).2 ((hτ _ hx).1 ⟨c, hc, rfl⟩)
  refine ⟨c', hc', ?_⟩
  have : Mono ex.core.G.ι := inferInstance
  rw [← cancel_mono ex.core.G.ι, Category.assoc, Category.assoc]
  exact hf
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsCompareUniformisationDataPullbackStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_compare_uniformisationData_pullback : Laws → Laws2 → Ega → ∀ (R V : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing V] [IsDomain V] [IsLocalRing V] (I : Ideal R) (I' : Ideal V), AdmBase R I → AdmBase V I' → I' ≠ ⊤ → ∀ φ : R →+* V, I.map φ ≤ I' → ∀ (D : DegPre R) (D' : DegPre V) (A : PolAV (Sp (FractionRing R))) (A' : PolAV (Sp (FractionRing V))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (G' : Over (Spec (CommRingCat.of V))) [GrpObj G'] [IsCommMonObj G'] (U : PreU I D A G) (U' : PreU I' D' A' G') (F : G'.left ⟶ G.left) (pb : IsGrpPullback G' G (spMap φ) F) (wL : LB.Iso U'.P.L.L (U.P.L.L.pull F)), IsCPMap U'.P U.P (spMap φ) F pb.1.w wL → ∃ C : Cmp φ U U' F, C.wL = wL := by
  first | exact @GlobalTheory.LN.PreCompare.exists_cmp | exact GlobalTheory.LN.PreCompare.exists_cmp | (intros; apply GlobalTheory.LN.PreCompare.exists_cmp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGeneratorThetaConstantsOverAlgClosedExtensStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.ThetaPtMove GlobalTheory.ConstFam
open GlobalTheory.Ex.OneGen GlobalTheory.UT

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_generator_thetaConstants_over_algClosedExtensions : Laws → Laws2 → ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen → ∀ (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (x₀ : Sp K ⟶ S) (P : PolAV (Sp K)) (φ : P.A.left ⟶ G.left), IsGrpPullback P.A G x₀ φ → LBIso P.L (L.pull φ) → ∀ (m : ℕ), Odd m → ∀ (Ix : Type) (x : Ix → (baseOver (Sp K) ⟶ P.A)) (v : Ix → K), (∀ y, y ^ (m ^ 2) = 1 ↔ ∃ i, x i = y) → IsThetaPt P m x (fun i => fnOf (v i)) → ∃ th : LB.Sec (LPow G L ((1 : ℕ) : ℤ) (Over.mk x₀)), IsGenSec G L ((1 : ℕ) : ℤ) th ∧ ∀ (F : Type) [Field F] [IsAlgClosed F] (e : K →+* F) (x' : Sp F ⟶ S) (h : spMap e ≫ x₀ = x') (a : F) (th' : LB.Sec (LPow G L ((1 : ℕ) : ℤ) (Over.mk x'))), SecM.ofSec G th' = @id Γ((Over.mk x').left, ⊤) (fnOf a) • SecM.ofSec G (VVRank.pullS G _ (Over.homMk (spMap e) h : Over.mk x' ⟶ Over.mk x₀) th) → (∀ i, ∃ z, ThG G L ρ m th' z (fnOf (a * e (v i)))) ∧ ∀ z (c : F), ThG G L ρ m th' z (fnOf c) → ∃ i, c = a * e (v i) := by
  first | exact @GlobalTheory.Ex.OneGen.exists_gen_thG_generic | exact GlobalTheory.Ex.OneGen.exists_gen_thG_generic | (intros; apply GlobalTheory.Ex.OneGen.exists_gen_thG_generic <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGenericIsoOfUniformisationsIsoDataStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_generic_iso_of_uniformisations_isoData : Laws → Laws2 → ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I → I ≠ ⊤ → ∀ (D D' : DegData R I) (A A' : PolAV (Sp (FractionRing R))) (G G' : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ (U : Unif I D A G) (U' : Unif I D' A' G') (hD : IsPullDeg (RingHom.id R) D.toPre D'.toPre), ∃ ψ : A'.A ≅ A.A, IsMonHom ψ.hom ∧ LBIso A'.L (A.L.pull ψ.hom.left) ∧ (∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ), 1 ≤ k → ∀ (p : QkPt D.toPre F k) (p' : QkPt D'.toPre F k) (x' : TFK (R := R) F ⟶ A'.A), p'.y = hD.xe.symm p.y → IsPullGtF (RingHom.id R) hD F p.g p'.g → (QkToAkU U'.toUnifPre F k p' x' ↔ QkToAkU U.toUnifPre F k p (x' ≫ ψ.hom))) ∧ ∀ (O : Type) [CommRing O] [StarRing O] [Module O D.toPre.X] [Module O D'.toPre.X] (o : D.OAct O) (o' : D'.OAct O) (oA : A.OAct O) (oA' : A'.OAct O) (oG : RingAct G O) (oG' : RingAct G' O), U.OLinear O o oA oG → U'.OLinear O o' oA' oG' → (∀ (x : O) y, hD.xe (x • y) = x • hD.xe y) → (∀ x, o'.onB.act x ≫ hD.e.hom = hD.e.hom ≫ (Over.pullback (specOf (RingHom.id R))).map (o.onB.act x)) → ∀ x, oA'.act x ≫ ψ.hom = ψ.hom ≫ oA.act x := by
  first | exact @GlobalTheory.exists_generic_iso_of_unif | exact GlobalTheory.exists_generic_iso_of_unif | (intros; apply GlobalTheory.exists_generic_iso_of_unif <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGeometricallyConnectedAwayOfGenericFibreStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_geometricallyConnected_away_of_genericFibre : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K] [IsFractionRing R K] (X X₀ : Scheme.{0}) (f : X ⟶ Sp R) (f₀ : X₀ ⟶ Sp K) (φ : X₀ ⟶ X), IsPullback φ f₀ f (spMap (algebraMap R K)) → Smooth f → GlobalTheory.AbLaw.IsProjBy f → GeometricallyConnected f₀ → ∃ a : R, a ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (g : R →+* R'), IsUnit (g a) → ∀ (X' : Scheme.{0}) (π : X' ⟶ X) (f' : X' ⟶ Sp R'), IsPullback π f' f (spMap g) → GeometricallyConnected f' := by
  first | exact @GlobalTheory.GenSpread.exists_geometricallyConnected | exact GlobalTheory.GenSpread.exists_geometricallyConnected | (intros; apply GlobalTheory.GenSpread.exists_geometricallyConnected <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGroupLawSmoothProperModelOfGeneric
section
noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GenSpread

open SpreadAb (grpObj_of_dominant isPullback_square)

theorem exists_grpObj : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K] [IsFractionRing R K] (X : Scheme.{0}) (f : X ⟶ Sp R) (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A] (φ : A.left ⟶ X), IsPullback φ A.hom f (spMap (algebraMap R K)) → Smooth f → IsProper f → ∃ a : R, a ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (g : R →+* R'), IsUnit (g a) → ∀ (ψ : R' →+* K), Function.Injective ψ → ψ.comp g = algebraMap R K → ∀ (G' : Over (Sp R')) (π : G'.left ⟶ X) (φ' : A.left ⟶ G'.left), IsPullback π G'.hom f (spMap g) → φ' ≫ π = φ → φ' ≫ G'.hom = A.hom ≫ spMap ψ → ∃ _ : GrpObj G', IsCommMonObj G' ∧ IsGrpPullback A G' (spMap ψ) φ' := by
  intro R K _ _ _ _ _ _ X f A _ _ φ h _ _
  obtain ⟨a₁, ha₁, H₁⟩ := exists_hom (pullback.fst f f ≫ f) f (isPullback_square h) ((μ[A]).left ≫ φ) (by
    rw [(isPullback_square h).w, Category.assoc, h.w, Over.w_assoc]
    rfl)
  obtain ⟨a₂, ha₂, H₂⟩ := exists_hom f f h ((ι[A]).left ≫ φ) (by rw [Category.assoc, h.w, Over.w_assoc])
  obtain ⟨a₃, ha₃, H₃⟩ := exists_hom (𝟙 _) f (IsPullback.id_vert (spMap (algebraMap R K)))
    ((η[A]).left ≫ φ) (by rw [Category.assoc, h.w, Over.w_assoc]; simp)
  refine ⟨a₁ * a₂ * a₃, mul_ne_zero (mul_ne_zero ha₁ ha₂) ha₃,
    fun R' _ g hg ψ hψ hψg G π φ' hG hφ₁ hφ₂ => ?_⟩
  rw [map_mul, map_mul, IsUnit.mul_iff, IsUnit.mul_iff] at hg
  obtain ⟨⟨u₁, u₂⟩, u₃⟩ := hg
  have hc : spMap ψ ≫ spMap g = spMap (algebraMap R K) := by
    rw [← hψg, ← Spec.map_comp]; rfl
  have hφ : IsPullback φ' A.hom G.hom (spMap ψ) := IsPullback.of_right (by rwa [hφ₁, hc]) hφ₂ hG
  have := ExtUnique.isSchemeTheoreticallyDominant_spec_of_injective (CommRingCat.ofHom ψ) hψ
  have : Flat G.hom := MorphismProperty.of_isPullback (P := @Flat) hG inferInstance
  have : IsSeparated G.hom := MorphismProperty.of_isPullback (P := @IsSeparated) hG inferInstance
  obtain ⟨m, hm₁, hm₂⟩ := H₁ R' g u₁ _ _ _ (isPullback_square hG).w
  obtain ⟨i, hi₁, hi₂⟩ := H₂ R' g u₂ _ _ _ hG.w
  obtain ⟨e, he₁, he₂⟩ := H₃ R' g u₃ _ (spMap g) (𝟙 _) (by simp)
  have L : ∀ (Y : Over (Sp R')) (u : Y.left ⟶ X), u ≫ f = Y.hom ≫ spMap g → ∃ v : Y ⟶ G, v.left ≫ π = u :=
    fun Y u w => ⟨Over.homMk (hG.lift u Y.hom w) (hG.lift_snd _ _ _), hG.lift_fst _ _ _⟩
  obtain ⟨m', hm'⟩ := L (G ⊗ G) m (hm₁.trans (isPullback_square hG).w)
  obtain ⟨i', hi'⟩ := L G i (hi₁.trans hG.w)
  obtain ⟨e', he'⟩ := L (𝟙_ _) e (he₁.trans ((Category.comp_id _).trans (Category.id_comp _).symm))
  exact grpObj_of_dominant (spMap ψ) G A φ' hφ m' i' e'
    (fun φ₂ ⟨k₁, k₂⟩ => by
      apply hG.hom_ext
      · rw [Category.assoc, Category.assoc, hφ₁, hm']
        refine hm₂ φ₂ (pullback.hom_ext ?_ ?_)
        · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, ← hφ₁]
          exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ π) k₁).trans (Category.assoc _ _ _))
        · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, ← hφ₁]
          exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ π) k₂).trans (Category.assoc _ _ _))
      · rw [Category.assoc, Category.assoc, Over.w, hφ₂, Over.w_assoc, ← Over.w (fst G G), reassoc_of% k₁, hφ₂,
          Over.w_assoc])
    (by
      apply hG.hom_ext
      · rw [Category.assoc, Category.assoc, hφ₁, hi']
        exact hi₂ φ' hφ₁
      · rw [Category.assoc, Category.assoc, Over.w, hφ₂, Over.w_assoc])
    (by
      apply hG.hom_ext
      · rw [Category.assoc, Category.assoc, hφ₁, he']
        exact he₂ _ hc
      · rw [Category.assoc, Category.assoc, Over.w, hφ₂, Over.w_assoc]
        exact (Category.comp_id _).trans (Category.id_comp _).symm)

end GlobalTheory.GenSpread
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLinearUniformisationBaseChangeAdmissibleStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Trait
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_linearUniformisation_baseChange_admissible : Laws → Laws3 → Laws4 → Laws5 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (I : Ideal R) (I' : Ideal R'), AdmBase R I → AdmBase R' I' → ∀ g : R →+* R', Function.Injective g → I.map g ≤ I' → ∀ (t : SAB H (Sp R)) (P : PELUnif I t), ∃ (t' : SAB H (Sp R')) (_ : SABMap t' t (spMap g)) (P' : PELUnif I' t') (ψ : P'.D.toPre.P.A.left ⟶ P.D.toPre.P.A.left), IsGrpPullback P'.D.toPre.P.A P.D.toPre.P.A (spMap g) ψ := by
  first | exact @GlobalTheory.Ex.Trait.exists_pelUnif_baseChange | exact GlobalTheory.Ex.Trait.exists_pelUnif_baseChange | (intros; apply GlobalTheory.Ex.Trait.exists_pelUnif_baseChange <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSectionsBasisBaseChangeH1VanishingStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_sections_basis_baseChange_h1Vanishing : ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of A)), Flat f → IsProjBy f → ∀ M : LB X, M.IsLB → ∀ (K : Type) [Field K] (g₀ : A →+* K), Function.Surjective g₀ → ∀ (X₀ : Scheme.{0}) (π : X₀ ⟶ X) (f₀ : X₀ ⟶ Spec (CommRingCat.of K)), IsPullback π f₀ f (Spec.map (CommRingCat.ofHom g₀)) → ∀ (M₀ : LB X₀) (w₀ : LB.Iso M₀ (M.pull π)), M₀.IsLB → w₀.IsGen → FirstCohomologyVanishes M₀ → ∃ (n : ℕ) (τ : Fin n → LB.Sec M), ∀ (A' : Type) [CommRing A'] (g : A →+* A') (X' : Scheme.{0}) (β : X' ⟶ X) (f' : X' ⟶ Spec (CommRingCat.of A')), IsPullback β f' f (Spec.map (CommRingCat.ofHom g)) → ∀ (M' : LB X') (w : LB.Iso M' (M.pull β)) (τ' : Fin n → LB.Sec M'), M'.IsLB → w.IsGen → (∀ i, (∀ z (k : (M).ι) (k' : (M').ι), (β) z ∈ (M).U k → z ∈ (M').U k' → gs (β) z _ ((τ i).f k) = (Geo.Tor.gw (w) (𝟙 _) z k k').val * gs (𝟙 _) z _ ((τ' i).f k'))) → ∀ s' : LB.Sec M', ∃! c : Fin n → A', ∀ k : M'.ι, s'.f k = ∑ i, cst f' (M'.U k) (c i) * (τ' i).f k := by
  first | exact @GlobalTheory.SecBasis.exists_basis | exact GlobalTheory.SecBasis.exists_basis | (intros; apply GlobalTheory.SecBasis.exists_basis <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTorsionIsometryTwistByRootsOfDataIsoStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Relabel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_torsionIsometry_twistByRoots_of_dataIso : BrGtSt → BrWpSt → AllD fun {E} _ _ _ {H} D => letI := H.starRing; ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Algebra (FractionRing R') F] (A : ArcF D R F) (D' : DegPre R') [Module (𝓞 E) D'.X] (oa' : D'.OAct (𝓞 E)), D'.PsiEven → D'.TauBimult → ∀ (N' : NumD F) (ν' : NumOf D' F N') (k : ℕ) (β : A.N.Form k) (u : Fˣ) (r : ℕ → Fˣ) (J : NumD.Iso (A.N.twist β u) N'), Roots u r → ActCompat A.ν A.oa ν' oa' β u r J → ∃ I' : TateIsoQ D D' oa' F, I'.ζ = A.I.ζ ∧ ∀ j, 0 < j → ∀ x, ∃ q', TwJ β u (r j) J (A.q j x) q' ∧ ν'.QPt (I'.ev j x) q' := by
  first | exact @GlobalTheory.Relabel.exists_tateIsoQ_twJ | exact GlobalTheory.Relabel.exists_tateIsoQ_twJ | (intros; apply GlobalTheory.Relabel.exists_tateIsoQ_twJ <;> assumption)
end

