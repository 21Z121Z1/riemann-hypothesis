import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0028
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnivIdentity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2580
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2621
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2506
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationEndomorphismsToCompleteDvr
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0142
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0141
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0027
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2634
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0015
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0099
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2676

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationEndomorphismCarriesPeriodPointBala
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.UT

noncomputable section

namespace GlobalTheory.Mum.KeepsIota

variable {R : Type} [CommRing R] [IsDomain R]

theorem exists_v (hG : GlobalFnsSt) (D : DegPre R) (f g : D.P.A ⟶ D.P.A) [IsMonHom f] [IsMonHom g]
    (k : D.X → D.X) (hk : ∀ χ, D.c (k χ) = D.c χ ≫ f)
    (u : LB.Gen (LB.LinComb D.P.L (rosatiφ D.P.A f g) rosatiε)) (hu : u.IsGen)
    (u₀ : LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (zero2 D.P.A)) (LB.oneGen D.P.L)) (χ : D.X) :
    ∃ v : LB.Gen (LB.LinComb D.P.L (Sum.elim (D.Oφ (𝟙 _) (k χ)) (D.Oφ g χ)) (Sum.elim Oε Oinvε)),
      Normd v ∧ ∀ (T : Over (Spec (CommRingCat.of R))) (x : T ⟶ D.P.A) (Z : Scheme.{0}) (r : Z ⟶ T.left) (z : Z) (J),
        Good D.P.L z J → val v (r ≫ x.left) z J = val u (r ≫ (lift (cP D T χ) x).left) z J := by
  have cf : ∀ T, cP D T (k χ) = cP D T χ ≫ f := fun T => by
    rw [cP, hk, ← Category.assoc]; rfl
  obtain ⟨v, hv, vv⟩ := exists_gen D.P.isLB
    (φ' := Sum.elim (D.Oφ (𝟙 _) (k χ)) (D.Oφ g χ)) (ε' := Sum.elim Oε Oinvε)
    (fun U _ h => by
      refine (prod_ros _ _ (cP D _ χ) (𝟙 D.P.A) h).trans (Eq.symm ?_)
      refine (prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _ (GlobalTheory.UT.OLinEnd.prod_Oφ D (𝟙 _) (k χ) h)
        (GlobalTheory.UT.OLinEnd.prod_Oφ_inv D g χ h)).trans ?_
      rw [cf, Category.id_comp]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel)
    (LB.pullGen D.P.L _ _ u (lift (cP D D.P.A χ) (𝟙 D.P.A)).left) (pullGen_isGen _ _ _ _ hu _)
  have key : ∀ (T : Over (Spec (CommRingCat.of R))) (x : T ⟶ D.P.A) (Z : Scheme.{0}) (r : Z ⟶ T.left) (z : Z) (J),
      Good D.P.L z J → val v (r ≫ x.left) z J = val u (r ≫ (lift (cP D T χ) x).left) z J := fun T x Z r z J hJ => by
    rw [vv Z _ z J hJ, val_pull hJ, Category.assoc, ← Over.comp_left, comp_lift, comp_cP, Category.comp_id]
  refine ⟨v, ⟨hv, corr_of_val D.P.isLB fun y J hJ => ?_⟩, key⟩
  have C : IsCub (cubV D.cub (T := 𝟙_ (Over (Spec (CommRingCat.of R)))) y J) := isCub_cubV D.cub hJ
  have e := (ros_add D.cub hG D.P.isAb _ _ u hu u₀ (T := 𝟙_ (Over (Spec (CommRingCat.of R)))) hJ 1 1 (cP D _ χ)).2
  rw [_root_.mul_one, MonObj.one_comp, C.face₃, C.face₃, _root_.mul_one, _root_.one_mul] at e
  have e' : val₂ u (T := 𝟙_ (Over (Spec (CommRingCat.of R)))) y J (cP D _ χ) 1 = 1 := mul_eq_left.1 e.symm
  have k' := key (𝟙_ (Over (Spec (CommRingCat.of R)))) 1 _ (𝟙 _) y J hJ
  have o : (1 : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D.P.A).left = eSec D.P.A := by
    rw [Hom.one_def, toUnit_unit, Category.id_comp]; rfl
  rw [o] at k'
  refine (val_pull hJ _ _ _).trans (k'.trans (Eq.trans ?_ (val_one _).symm))
  rw [Category.id_comp]
  exact e'

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ E : EndU U.toUnifPre, E.aB = a → E.h = h' → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (y : D.toPre.X) (g g' : GtPtF D.toPre F), GtPtF.IsIota y g → E.Act g g' → GtPtF.IsIota (h y) g' := by
  intro R _ _ _ _ D A G _ _ _ U a a' h h' hd E hEa hEh F _ _ _ y g g' hg hact
  subst hEa hEh
  have hG : GlobalFnsSt := GlobalTheory.SemiRigid.globalFns
  have hs := (endData_symm_and_ofOAct R D.toPre).1 _ _ _ _ hd
  obtain ⟨ha, ha', -, hc, hc', -⟩ := hd
  obtain ⟨-, -, hr', -, -, hbal'⟩ := hs
  obtain ⟨u, hu, u₀⟩ := exists_ros hG D.toPre.P.isAb D.toPre.P.isLB _ _ hr'
  obtain ⟨gb, gv⟩ := (isIota_iff _ _).1 hg
  refine (isIota_iff _ _).2 ⟨?_, fun χ z J hJ => ?_⟩
  · rw [hact.1, gb, cP, cP, hc, ← Category.assoc]
  · obtain ⟨v, hv, vv⟩ := exists_v hG D.toPre a' E.aB E.h hc' u hu u₀ χ
    have k1 : val (E.u χ) g.b.left z J = val u (lift (cP D.toPre _ χ) g.b).left z J := by
      have := vv _ g.b _ (𝟙 _) z J hJ
      rw [Category.id_comp, Category.id_comp] at this
      exact (GlobalTheory.UT.SymFrame.normd_unique hG (E.u_norm χ) hv _ z J hJ).trans this
    rw [hact.2 χ z J hJ, gv _ z J hJ, k1, gb]
    let κ : TF (R := R) F ⟶ TK R := Over.homMk (𝟙 _ ≫ jFK (R := R) F) (by rw [Category.id_comp]; rfl)
    have e := (val_mul hJ _ _ _).symm.trans (val_corr hJ (hbal' u hu u₀ χ y) κ.left)
    have e' : val (LB.pullGen D.toPre.P.L _ _ u (D.toPre.pt2 χ y)) κ.left z J =
        val u (lift (cP D.toPre _ χ) (cP D.toPre _ y)).left z J := by
      rw [val_pull hJ, ← comp_cP D.toPre κ, ← comp_cP D.toPre κ y, ← comp_lift]; rfl
    rw [← e']
    exact (congrArg₂ (· * ·) (tau_symm (𝟙 (TF (R := R) F)) hJ _ _) rfl).trans
      (e.trans (tau_symm (𝟙 (TF (R := R) F)) hJ _ _))

end GlobalTheory.Mum.KeepsIota

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedGroupGaloisMapMul
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.GalMul

open GlobalTheory.ArcPull GlobalTheory.ArcQ GlobalTheory.PsiEvenPull

theorem exists_isPullDeg_of_val {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']
    {i : R →+* R'} (hi : Function.Injective i) (D : DegPre R) (D' : DegPre R')
    {W : (Sp R).Opens} (ψW : PsiOn D W) (s : (TK R).left ⟶ W.toScheme) (hs : s ≫ W.ι = jK R)
    {Φ : D'.P.A.left ⟶ D.P.A.left} (gp : IsGrpPullback D'.P.A D.P.A (spMap i) Φ)
    (w : LB.Iso D'.P.L (D.P.L.pull Φ)) (hw : PGen w)
    (hr : PMaps w (K := PUnit) (fun _ => eSec D'.P.A) (fun _ => eSec D.P.A) (fun _ => 1) D'.rig D.rig (spMap i))
    (xe : D'.X ≃+ D.X) (hc : ∀ x, (D'.c x).left ≫ Φ = spMap i ≫ (D.c (xe x)).left)
    (hψ : ∀ (x : D'.X) (z : (TK R').left) J J', Good D.P.L z J → Good D'.P.L z J' →
      val (D.psi (xe x)) (genMap hi) z J = (om w z J J' (D'.xK x))⁻¹ * val (D'.psi x) (𝟙 _) z J') :
    ∃ hD : IsPullDeg i D D', proj hD = Φ ∧ hD.xe = xe ∧ HEq hD.w w := by
  obtain ⟨e, e_hom, he⟩ := grpPullback_iso gp (isGrpPullback_pullback D.P.A (specOf i))
  subst he
  have hE : eSec D'.P.A ≫ e.hom.left ≫ pullback.fst D.P.A.hom (specOf i) = specOf i ≫ eSec D.P.A :=
    (cubeMapOf gp).e_comm
  obtain ⟨g, sq⟩ : ∃ g : (TK R').left ⟶ (TW W).left, g ≫ W.ι = genMap hi ≫ jK R :=
    ⟨genMap hi ≫ s, (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) hs)⟩
  have hg : g ≫ W.ι = jK R' ≫ specOf i := sq.trans ((fracMap_sq hi).symm.trans (Category.id_comp _))
  obtain ⟨lam, l₁, l₂⟩ : ∃ lam : (TK R').left ⟶ (jK R ⁻¹ᵁ W).toScheme, lam ≫ (jK R ⁻¹ᵁ W).ι = genMap hi ∧
      lam ≫ (jK R ∣_ W) = g :=
    ⟨(isPullback_morphismRestrict (jK R) W).lift _ _ sq,
      (isPullback_morphismRestrict (jK R) W).lift_snd _ _ _,
      (isPullback_morphismRestrict (jK R) W).lift_fst _ _ _⟩
  have hx : ∀ x, g ≫ (toUnit (TW W) ≫ D.c (xe x)).left =
      D'.xK x ≫ e.hom.left ≫ pullback.fst D.P.A.hom (specOf i) := fun x => by
    show g ≫ W.ι ≫ (D.c (xe x)).left = (jK R' ≫ (D'.c x).left) ≫ _
    rw [Category.assoc, hc, ← Category.assoc, hg, Category.assoc]
  choose b hb vb using fun x => exists_gen D.P.isLB (K' := PUnit)
    (φ' := fun _ => D'.xK x ≫ e.hom.left ≫ pullback.fst D.P.A.hom (specOf i)) (ε' := fun _ => -1)
    (fun U _ h => Finset.prod_congr rfl fun _ _ => congrArg (fun q => h q ^ (-1 : ℤ)) (hx x))
    (LB.pullGen D.P.L _ _ (ψW.psi (xe x)) g) (DVR.pullGen_isGen _ _ _ _ (ψW.psi_gen _) g)
  choose psi hpsi vpsi using fun x => DegPull.exists_down_val hw D.P.isLB D'.P.isLB (K := PUnit)
    (φ' := fun _ => D'.xK x) (ε := fun _ => -1) (fun _ => rfl) (b x) (hb x)
  have eψ : ∀ x, psi x = D'.psi x := fun x => TorusExt.gen_ext_val D'.P.isLB (hpsi x) (D'.psi_gen x) fun y J' hJ' => by
    obtain ⟨J, hJ⟩ := DegPull.exists_good' D.P.isLB y
    have v := vpsi x _ (𝟙 _) y _ _ (hJ.mem _ (𝟙 _)) (hJ'.mem _ (𝟙 _))
    have u := (val_pull hJ _ _ _).symm.trans ((val_corr hJ (ψW.psi_eq (xe x)) lam).trans (val_pull hJ _ _ _))
    rw [l₁, l₂, hψ x y J J' hJ hJ'] at u
    have v₁ : val (b x) (𝟙 _) y J = val (ψW.psi (xe x)) g y J :=
      (vb x _ _ y J hJ).trans ((val_pull hJ _ _ _).trans (by rw [Category.id_comp]))
    have v₂ : val (b x) (𝟙 _) y J = (om w y J J' (D'.xK x))⁻¹ * val (psi x) (𝟙 _) y J' := by
      refine v.trans (congrArg₂ (· * ·) ?_ rfl)
      rw [pw, Fintype.prod_unique, zpow_neg_one]
      simp only [om, Category.id_comp]
    exact mul_left_cancel (v₂.symm.trans (v₁.trans u))
  refine ⟨⟨e, e_hom, w, (isGen_iff w).2 hw, hE, ?_, xe, hc, W, ψW, g, hg, fun x => ⟨b x, fun jN jL => ?_,
      corr_of_val D.P.isLB fun y J hJ => vb x _ _ y J hJ⟩⟩, rfl, rfl, HEq.rfl⟩
  · exact (maps_iff w _ (fun _ => eSec D.P.A) _ D'.rig D.rig (specOf i) _
      (rigPull_le (G' := D'.P.A) (G := D.P.A) _ (specOf i) hE D.P.L) (fun _ => rfl)).2 hr
  · rw [← eψ]
    refine unit_ext fun y hy => ?_
    have v := vpsi x _ (𝟙 _) y jN (fun _ => jL) (GeneratorPullback.mapsAt_le_b _ _ _ _ jN jL hy) (GeneratorPullback.mapsAt_le_a _ _ _ _ jN jL hy)
    refine (gm_res _ y _ hy _).trans (v.trans (Eq.symm ((map_mul _ _ _).trans (congrArg₂ (· * ·) ?_
      (gm_res _ y _ hy _)))))
    rw [pw, Fintype.prod_unique]
    exact (map_zpow _ _ _).trans (congrArg (· ^ (-1 : ℤ)) (gm_pull (𝟙 _) _ y _ hy _))

theorem exists_isPullDeg_comp {R R' R'' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] [CommRing R'']
    [IsDomain R''] {i : R →+* R'} {j : R' →+* R''} (hi : Function.Injective i) (hj : Function.Injective j)
    {D : DegPre R} {D' : DegPre R'} {D'' : DegPre R''} (p : IsPullDeg i D D') (q : IsPullDeg j D' D'') :
    ∃ (r : IsPullDeg (j.comp i) D D'') (w : LB.Iso D''.P.L (D.P.L.pull (proj q ≫ proj p))),
      proj r = proj q ≫ proj p ∧ r.xe = q.xe.trans p.xe ∧ HEq r.w w ∧ Tri p.w q.w w := by
  have hji : Function.Injective (j.comp i) := hj.comp hi
  have sc : spMap j ≫ spMap i = spMap (j.comp i) := (spMap_comp i j).symm
  have gp : IsGrpPullback D''.P.A D.P.A (spMap (j.comp i)) (proj q ≫ proj p) :=
    ((pull_grp q).comp (pull_grp p)).congr sc rfl
  have g₁ := (isGen_iff _).1 p.w_gen
  have g₂ := (isGen_iff _).1 q.w_gen
  obtain ⟨w, T⟩ := Geo.Tor.exists_comp D'.P.isLB p.w q.w g₁ g₂ D.P.isLB D''.P.isLB
  have hr := T.pmaps_comp D'.P.isLB (fun _ => q.he) (FieldPull.pmaps_rig p) (FieldPull.pmaps_rig q)
  rw [sc] at hr
  have hc : ∀ x, (D''.c x).left ≫ proj q ≫ proj p = spMap (j.comp i) ≫ (D.c ((q.xe.trans p.xe) x)).left := fun x =>
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ proj p) (q.c_pr x)).trans ((Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) (p.c_pr _)).trans ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) sc)))))
  obtain ⟨s, hs⟩ := GlobalTheory.PullDegComp.exists_generic_lift hi p
  obtain ⟨r, r₁, r₂, r₃⟩ := exists_isPullDeg_of_val hji D D'' p.psiW s hs gp w (T.pgen_comp D'.P.isLB g₁ g₂) hr
    (q.xe.trans p.xe) hc (fun x z J J'' hJ hJ'' => by
      obtain ⟨J', hJ'⟩ := DegPull.exists_good' D'.P.isLB z
      have sj : jK R'' ≫ spMap j = genMap hj ≫ jK R' := (Category.id_comp _).symm.trans (fracMap_sq hj)
      have s' : genMap hj ≫ jK R' ≫ spMap i = genMap hji ≫ jK R :=
        (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) sj.symm).trans ((Category.assoc _ _ _).trans
          ((congrArg (_ ≫ ·) sc).trans ((Category.id_comp _).symm.trans (fracMap_sq hji)))))
      have v₁ := psi_val p _ _ s' hJ hJ' (q.xe x)
      have v₂ := psi_val q _ _ (fracMap_sq hj) hJ' hJ'' x
      have hx : D''.xK x ≫ proj q = genMap hj ≫ D'.xK (q.xe x) := by
        show (jK R'' ≫ (D''.c x).left) ≫ proj q = genMap hj ≫ jK R' ≫ (D'.c (q.xe x)).left
        rw [Category.assoc, q.c_pr, ← Category.assoc, ← Category.assoc, ← sj]
      have t : om w z J J'' (D''.xK x) = om p.w z J J' (D''.xK x ≫ proj q) * om q.w z J' J'' (D''.xK x) :=
        (congrArg (fun u => Geo.Tor.gw w (D''.xK x) z (J u) (J'' (D''.xK x)))
          (Category.assoc (D''.xK x) (proj q) (proj p)).symm).trans
          (T _ _ z _ _ _ (hJ ((D''.xK x ≫ proj q) ≫ proj p)) (hJ' (D''.xK x ≫ proj q)) (hJ'' _))
      rw [v₂, Category.id_comp, ← hx, ← _root_.mul_assoc, ← mul_inv, ← t] at v₁
      exact v₁)
  exact ⟨r, w, r₁, r₂, r₃, T⟩

def Sq {X X' G G' Y Y' : Scheme.{0}} {M : LB X} {M' : LB X'} {L : LB G} {L' : LB G'}
    {F : X' ⟶ X} {B : G' ⟶ G} {p : Y ⟶ X} {p' : Y' ⟶ X'} {f : Y ⟶ G} {f' : Y' ⟶ G'} (h : Y' ⟶ Y)
    (wM : LB.Iso M' (M.pull F)) (wL : LB.Iso L' (L.pull B))
    (w : LB.Iso (L.pull f) (M.pull p)) (w' : LB.Iso (L'.pull f') (M'.pull p')) : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (jM : M.ι) (jM' : M'.ι) (jL : L.ι) (jL' : L'.ι),
    F (p' (r z)) ∈ M.U jM → p' (r z) ∈ M'.U jM' → B (f' (r z)) ∈ L.U jL → f' (r z) ∈ L'.U jL' →
    Geo.Tor.gw wM (r ≫ p') z jM jM' * Geo.Tor.gw w' r z jM' (fun _ => jL') =
      Geo.Tor.gw w (r ≫ h) z jM (fun _ => jL) * Geo.Tor.gw wL (r ≫ f') z jL jL'

theorem Sq.comp {X X' X'' G G' G'' Y Y' Y'' : Scheme.{0}} {M : LB X} {M' : LB X'} {M'' : LB X''} {L : LB G} {L' : LB G'}
    {L'' : LB G''} {F : X' ⟶ X} {F' : X'' ⟶ X'} {B : G' ⟶ G} {B' : G'' ⟶ G'} {p : Y ⟶ X} {p' : Y' ⟶ X'} {p'' : Y'' ⟶ X''}
    {f : Y ⟶ G} {f' : Y' ⟶ G'} {f'' : Y'' ⟶ G''} {h : Y' ⟶ Y} {h' : Y'' ⟶ Y'}
    {wM : LB.Iso M' (M.pull F)} {wM' : LB.Iso M'' (M'.pull F')} {wM'' : LB.Iso M'' (M.pull (F' ≫ F))}
    {wL : LB.Iso L' (L.pull B)} {wL' : LB.Iso L'' (L'.pull B')} {wL'' : LB.Iso L'' (L.pull (B' ≫ B))}
    {w : LB.Iso (L.pull f) (M.pull p)} {w' : LB.Iso (L'.pull f') (M'.pull p')} {w'' : LB.Iso (L''.pull f'') (M''.pull p'')}
    (hM : M'.IsLB) (hL : L'.IsLB) (TM : Tri wM wM' wM'') (TL : Tri wL wL' wL'')
    (hf : h' ≫ f' = f'' ≫ B') (hp : p'' ≫ F' = h' ≫ p') (H : Sq h wM wL w w') (H' : Sq h' wM' wL' w' w'') :
    Sq (h' ≫ h) wM'' wL'' w w'' := by
  intro Z r z jM jM'' jL jL'' h₁ h₂ h₃ h₄
  have ef : f' (h' (r z)) = B' (f'' (r z)) := congrArg (fun g => g (r z)) hf
  have ep : p' (h' (r z)) = F' (p'' (r z)) := congrArg (fun g => g (r z)) hp.symm
  obtain ⟨jM', m⟩ := exists_chart hM (F' (p'' (r z)))
  obtain ⟨jL', l⟩ := exists_chart hL (B' (f'' (r z)))
  have a := H Z (r ≫ h') z jM jM' jL jL' (by show F (p' (h' (r z))) ∈ _; rw [ep]; exact h₁)
    (by show p' (h' (r z)) ∈ _; rw [ep]; exact m) (by show B (f' (h' (r z))) ∈ _; rw [ef]; exact h₃)
    (by show f' (h' (r z)) ∈ _; rw [ef]; exact l)
  have b := H' Z r z jM' jM'' jL' jL'' m h₂ l h₄
  have c := TM Z (r ≫ p'') z jM jM' jM'' h₁ m h₂
  have d := TL Z (r ≫ f'') z jL jL' jL'' h₃ l h₄
  rw [Category.assoc, hp, ← Category.assoc] at c
  rw [Category.assoc, ← hf, ← Category.assoc] at d
  rw [c, d, _root_.mul_assoc, b, ← _root_.mul_assoc, a, _root_.mul_assoc, Category.assoc]

theorem isPullUnif_comp {R R' R'' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] [CommRing R'']
    [IsDomain R''] {I : Ideal R} {I' : Ideal R'} {I'' : Ideal R''} {i : R →+* R'} {j : R' →+* R''}
    {D : DegData R I} {D' : DegData R' I'} {D'' : DegData R'' I''} {p : IsPullDeg i D.toPre D'.toPre}
    {q : IsPullDeg j D'.toPre D''.toPre} {r : IsPullDeg (j.comp i) D.toPre D''.toPre}
    {w : LB.Iso D''.toPre.P.L (D.toPre.P.L.pull (proj q ≫ proj p))} (r₁ : proj r = proj q ≫ proj p)
    (r₂ : r.xe = q.xe.trans p.xe) (r₃ : HEq r.w w) (T : Tri p.w q.w w)
    {A : PolAV (Sp (FractionRing R))} {A' : PolAV (Sp (FractionRing R'))} {A'' : PolAV (Sp (FractionRing R''))}
    {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] {G' : Over (Sp R')} [GrpObj G'] [IsCommMonObj G']
    {G'' : Over (Sp R'')} [GrpObj G''] [IsCommMonObj G'']
    {b₁ : G' ≅ (Over.pullback (specOf i)).obj G} {b₂ : G'' ≅ (Over.pullback (specOf j)).obj G'}
    {b : G'' ≅ (Over.pullback (specOf (j.comp i))).obj G}
    (hb : b.hom.left ≫ pullback.fst G.hom (specOf (j.comp i)) =
      (b₂.hom.left ≫ pullback.fst G'.hom (specOf j)) ≫ (b₁.hom.left ≫ pullback.fst G.hom (specOf i)))
    {U : Unif I D A G} {U' : Unif I' D' A' G'} {U'' : Unif I'' D'' A'' G''}
    (H₁ : IsPullUnif i p b₁ U U') (H₂ : IsPullUnif j q b₂ U' U'') : IsPullUnif (j.comp i) r b U U'' := by
  have sc : specOf j ≫ specOf i = specOf (j.comp i) := (spMap_comp i j).symm
  obtain ⟨w₁, g₁, e₁, m₁, K₁⟩ := (isPullUnif_iff_stalks _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).1 H₁
  obtain ⟨w₂, g₂, e₂, m₂, K₂⟩ := (isPullUnif_iff_stalks _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).1 H₂
  replace g₁ := (isGen_iff _).1 g₁
  replace g₂ := (isGen_iff _).1 g₂
  replace m₁ := (maps_iff w₁ _ (fun _ => eSec G) _ U'.LG.rig U.LG.rig (specOf i) _
    (rigPull_le (G' := G') (G := G) _ (specOf i) e₁ U.LG.L) (fun _ => rfl)).1 m₁
  replace m₂ := (maps_iff w₂ _ (fun _ => eSec G') _ U''.LG.rig U'.LG.rig (specOf j) _
    (rigPull_le (G' := G'') (G := G') _ (specOf j) e₂ U'.LG.L) (fun _ => rfl)).1 m₂
  obtain ⟨wL, TL⟩ := Geo.Tor.exists_comp U'.LG.isLB w₁ w₂ g₁ g₂ U.LG.isLB U''.LG.isLB
  have key : ∀ (Φ : D''.toPre.P.A.left ⟶ D.toPre.P.A.left) (u : LB.Iso D''.toPre.P.L (D.toPre.P.L.pull Φ))
      (xe : D''.toPre.X ≃+ D.toPre.X) (B : G''.left ⟶ G.left), Φ = proj q ≫ proj p → HEq u w → xe = q.xe.trans p.xe →
      B = (b₂.hom.left ≫ pullback.fst G'.hom (specOf j)) ≫ (b₁.hom.left ≫ pullback.fst G.hom (specOf i)) →
      ∃ wL : LB.Iso U''.LG.L (U.LG.L.pull B), wL.IsGen ∧ ∃ he : eSec G'' ≫ B = specOf (j.comp i) ≫ eSec G,
        LB.Gen.Maps (LB.linCombIso wL (K := PUnit) (fun _ => eSec G'') (fun _ => 1)) U''.LG.rig
          (rigPullOf B (specOf (j.comp i)) he U.LG.L U.LG.rig) ∧
        ∀ e : ℕ, ∃ h : (thickObj R'' I'' e G'').left ⟶ (thickObj R I e G).left,
          h ≫ (fstG I e G).left = (fstG I'' e G'').left ≫ B ∧
          ((U''.gt e).pG.left ≫ Φ = h ≫ (U.gt e).pG.left ∧ ∀ x : D''.toPre.X,
            (∀ κ : Fin 4, D''.toPre.Oφ (U''.gt e).pG x κ ≫ Φ = h ≫ D.toPre.Oφ (U.gt e).pG (xe x) κ) ∧
            PMaps u (D''.toPre.Oφ (U''.gt e).pG x) (D.toPre.Oφ (U.gt e).pG (xe x)) Oinvε ((U''.gt e).t x)
              ((U.gt e).t (xe x)) h) ∧ Sq h u wL (U.w e) (U''.w e) := by
    rintro _ u _ _ rfl hu rfl rfl
    obtain rfl := eq_of_heq hu
    have he : eSec G'' ≫ (b₂.hom.left ≫ pullback.fst G'.hom (specOf j)) ≫ (b₁.hom.left ≫ pullback.fst G.hom (specOf i)) =
        specOf (j.comp i) ≫ eSec G :=
      (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) e₂).trans ((Category.assoc _ _ _).trans
        ((congrArg (_ ≫ ·) e₁).trans ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) sc)))))
    have hr := TL.pmaps_comp U'.LG.isLB (fun _ => e₂) m₁ m₂
    rw [sc] at hr
    refine ⟨wL, (isGen_iff _).2 (TL.pgen_comp U'.LG.isLB g₁ g₂), he,
      (maps_iff wL _ (fun _ => eSec G) _ U''.LG.rig U.LG.rig (specOf (j.comp i)) _
        (rigPull_le (G' := G'') (G := G) _ (specOf (j.comp i)) he U.LG.L) (fun _ => rfl)).2 hr, fun e => ?_⟩
    obtain ⟨h₁, f₁, ⟨p₁, t₁⟩, s₁⟩ := K₁ e
    obtain ⟨h₂, f₂, ⟨p₂, t₂⟩, s₂⟩ := K₂ e
    refine ⟨h₂ ≫ h₁, ?_, ⟨?_, fun x => ⟨fun κ => ?_, ?_⟩⟩, Sq.comp D'.toPre.P.isLB U'.LG.isLB T TL f₂ p₂ s₁ s₂⟩
    · exact (Category.assoc _ _ _).trans ((congrArg (h₂ ≫ ·) f₁).trans ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ _) f₂).trans (Category.assoc _ _ _))))
    · exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) p₂).trans ((Category.assoc _ _ _).trans
        ((congrArg (h₂ ≫ ·) p₁).trans (Category.assoc _ _ _).symm)))
    · exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) ((t₂ x).1 κ)).trans ((Category.assoc _ _ _).trans
        ((congrArg (h₂ ≫ ·) ((t₁ (q.xe x)).1 κ)).trans (Category.assoc _ _ _).symm)))
    · exact T.pmaps_comp D'.toPre.P.isLB (t₂ x).1 (t₁ (q.xe x)).2 (t₂ x).2
  exact (isPullUnif_iff_stalks _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).2 (key _ r.w r.xe _ r₁ r₃ r₂ hb)

end GlobalTheory.Mum.GalMul

namespace GlobalTheory.Mum

theorem galMap_mul : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → ∀ (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R') D' A' G') (σ τ : Gal ρ) (a b : G'.left ⟶ G'.left), GalMap hD U' σ a → GalMap hD U' τ b → GalMap hD U' (σ * τ) (a ≫ b) := by
  intro R _ _ _ _ R' _ _ _ ρ _ D D' hD A' G' _ _ _ U' σ τ a b ⟨ga, q, b₂, ha, H₂, x₂, c₂⟩ ⟨gb, p, b₁, hb, H₁, x₁, c₁⟩
  have gp : IsGrpPullback G' G' (spMap ((Gal.hom σ).comp (Gal.hom τ))) (a ≫ b) :=
    (ga.comp gb).congr (spMap_comp _ _).symm rfl
  obtain ⟨r, w, r₁, r₂, r₃, T⟩ := GalMul.exists_isPullDeg_comp (i := Gal.hom τ) (j := Gal.hom σ) τ.1.injective σ.1.injective p q
  obtain ⟨bc, -, hbc⟩ := grpPullback_iso gp (isGrpPullback_pullback G' (specOf ((Gal.hom σ).comp (Gal.hom τ))))
  refine ⟨gp, r, bc, hbc, GalMul.isPullUnif_comp r₁ r₂ r₃ T (hbc.trans (by rw [ha, hb])) H₁ H₂, fun x => ?_, ?_⟩
  · exact (congrArg (fun e => e x) r₂).trans ((x₁ _).trans (x₂ x))
  · rintro _ _ rfl rfl
    exact (congrArg (· ≫ _) r₁).trans ((Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) (c₁ _ _ rfl rfl)).trans (c₂ _ _ rfl rfl)))

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformiserOrderEqOfAssociatedStalkImage
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open GlobalTheory
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.UPoinc

theorem uOrdEq_stalkHom_of_associated : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] (M : RatModel o' Ω) (x : M.Z) (T : UTrait Xo c) (ξ : Sp T.V ⟶ M.Z), ξ (IsLocalRing.closedPoint T.V) ⤳ x → ∀ (R : Type) [CommRing R] (j : M.Z.presheaf.stalk x →+* R) (V' : Type) [CommRing V'] [IsDomain V'] [IsDiscreteValuationRing V'] (h : T.V →+* V') (g' : R →+* V'), Function.Injective h → Irreducible (h T.ϖ) → spMap g' ≫ (spMap j ≫ M.Z.fromSpecStalk x) = spMap h ≫ ξ → ∀ (a : M.Z.presheaf.stalk x) (k : ℕ), Associated (g' (j a)) (h T.ϖ ^ k) → UOrdEq M T ξ (M.stalkHom x a) k := by
  intro E _ _ _ H Dw l Xo c o' Ω _ _ _ M x T ξ hx R _ j V' _ _ _ h g' hinj hirr hcomm a k ha
  haveI : IsDiscreteValuationRing T.V := T.cdvr.1
  let v : M.Z.presheaf.stalk x ⟶ CommRingCat.of T.V :=
    M.Z.presheaf.stalkSpecializes hx ≫ Scheme.stalkClosedPointTo (R := CommRingCat.of T.V) ξ
  have hv : Spec.map v ≫ M.Z.fromSpecStalk x = ξ := by
    rw [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk,
      Scheme.Spec_stalkClosedPointTo_fromSpecStalk]
  have e1 : Spec.map (CommRingCat.ofHom j ≫ CommRingCat.ofHom g') = Spec.map (v ≫ CommRingCat.ofHom h) := by
    rw [← cancel_mono (M.Z.fromSpecStalk x), Spec.map_comp, Spec.map_comp, Category.assoc, Category.assoc, hv]
    exact hcomm
  have e2 : g' (j a) = h (v.hom a) := congrArg (fun φ => φ.hom a) (Spec.map_injective e1)
  have e3 : M.val (jK T.V ≫ ξ) (M.stalkHom x a) = algebraMap T.V (FractionRing T.V) (v.hom a) := by
    refine (RatModel.val_spMap_comp (algebraMap T.V (FractionRing T.V)) ξ hx (M.stalkEquiv x a)).trans ?_
    rw [RatModel.valLoc, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      RingEquiv.symm_apply_apply]
  rw [e2] at ha
  have h0 : v.hom a ≠ 0 := fun h0 => by
    rw [h0, map_zero] at ha
    exact pow_ne_zero k hirr.ne_zero (associated_zero_iff_eq_zero _ |>.1 ha.symm)
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible h0 T.irr
  have h1 : Associated (h T.ϖ ^ n) (h T.ϖ ^ k) := by
    refine Associated.trans ?_ ha
    rw [hu, map_mul, map_pow]
    exact (associated_unit_mul_left _ _ (u.isUnit.map h)).symm
  have hn : n = k := le_antisymm ((pow_dvd_pow_iff hirr.ne_zero hirr.not_isUnit).1 h1.dvd)
    ((pow_dvd_pow_iff hirr.ne_zero hirr.not_isUnit).1 h1.symm.dvd)
  exact ⟨u, by rw [e3, hu, hn, mul_comm]⟩

end GlobalTheory.UPoinc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformizationBaseChangeCompleteDvr
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

open GlobalTheory.ArcPull GlobalTheory.PullLinear in

theorem isPullDeg_of_trait_unif : ∀ (R₀ : Type) [CommRing R₀] [IsDomain R₀] [IsLocalRing R₀], AdmBase R₀ (maximalIdeal R₀) → ∀ (D₀ : DegData R₀ (maximalIdeal R₀)) (A₀ : PolAV (Sp (FractionRing R₀))) (G₀ : Over (Sp R₀)) [GrpObj G₀] [IsCommMonObj G₀], IsSemiAbelian G₀ → ∀ (U₀ : Unif (maximalIdeal R₀) D₀ A₀ G₀) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ (φ : R₀ →+* W), Function.Injective φ → IsLocalHom φ → ∀ (GW : Over (Sp W)) [GrpObj GW] [IsCommMonObj GW] (β : GW.left ⟶ G₀.left) (DW : DegData W (maximalIdeal W)) (AW : PolAV (Sp (FractionRing W))) (UW : Unif (maximalIdeal W) DW AW GW), IsGrpPullback GW G₀ (spMap φ) β → LBIso UW.LG.L (U₀.LG.L.pull β) → Nonempty (IsPullDeg φ D₀.toPre DW.toPre) := by
  intro R₀ _ _ _ hR D₀ A₀ G₀ _ _ hG U₀ W _ _ _ hW φ hφ hloc GW _ _ β DW AW UW hβ hLβ
  obtain ⟨hL1, -, -, h4, h5⟩ := GlobalTheory.firstFiveLaws
  have := hW.1
  have hW' : AdmBase W (maximalIdeal W) := ⟨inferInstance, inferInstance, inferInstance, hW.2.1⟩
  obtain ⟨bc, mbc, hbc⟩ := grpPullback_iso hβ (isGrpPullback_pullback G₀ (spMap φ))
  have hbc' : bc.hom.left ≫ pullback.fst G₀.hom (specOf φ) = β := hbc
  have hGW : IsSemiAbelian GW := by
    have := mbc
    exact GlobalTheory.isSemiAbelian_of_grpIso bc (IsSemiAbelian.pullback (spMap φ) G₀ hG)

  have sq : spMap (GlobalTheory.ArcPull.fracMap hφ) ≫ jK R₀ = jK W ≫ spMap φ :=
    (GlobalTheory.ArcPull.fracMap_sq hφ).symm.trans (Category.id_comp _)
  obtain ⟨A', gA, pA, dA, mA, tA⟩ := hL1.polBaseChange _ _ (spMap (GlobalTheory.ArcPull.fracMap hφ)) A₀
  have gpA : IsGrpPullback A'.A A₀.A (spMap (GlobalTheory.ArcPull.fracMap hφ)) gA := ⟨pA, fun T x y x₀ y₀ hx hy => by
    have e₁ : x₀ = Out.toBase pA.w x := Over.OverMorphism.ext hx
    have e₂ : y₀ = Out.toBase pA.w y := Over.OverMorphism.ext hy
    rw [e₁, e₂, ← mA]; rfl⟩
  have gpG := GlobalTheory.ThetaBaseChange.grp_generic U₀.toUnifPre
  have gp' : IsGrpPullback ((Over.pullback (jK W)).obj GW) G₀ (spMap (GlobalTheory.ArcPull.fracMap hφ) ≫ jK R₀)
      (pullback.fst GW.hom (jK W) ≫ β) :=
    ((isGrpPullback_pullback GW (jK W)).comp hβ).congr sq.symm rfl
  obtain ⟨eA, mE, heA⟩ := grpPullback_iso gp' (gpA.comp gpG)
  have hgi : U₀.gen.inv.left ≫ U₀.gen.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
  have wA : LBIso (A'.L.pull eA.hom.left) (U₀.LG.L.pull (pullback.fst GW.hom (jK W) ≫
      bc.hom.left ≫ pullback.fst G₀.hom (specOf φ))) := by
    refine LBIso.trans (pull_isLB A'.isLB _) (pull_isLB (pull_isLB A₀.isLB gA) eA.hom.left)
      (pull_isLB U₀.LG.isLB _)
      ((LBIso.symm tA).chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull A'.L _ _ rfl) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull (A₀.L.pull gA) _ _ rfl)) ?_
    refine LBIso.chartPull (h := eA.hom.left ≫ gA ≫ U₀.gen.inv.left)
      (chartPullLinComb A₀.L gA (fun _ => eA.hom.left) (fun _ => U₀.gen.hom.left) _ _ fun _ => ?_)
      (chartPullSame U₀.LG.L _ (fun _ => pullback.fst G₀.hom (jK R₀)) _ _ fun _ => ?_) U₀.ext
    · rw [Category.assoc, Category.assoc, hgi, Category.comp_id]
    · rw [hbc', ← heA]; simp only [Category.assoc]

  have he : eSec GW ≫ bc.hom.left ≫ pullback.fst G₀.hom (specOf φ) = specOf φ ≫ eSec G₀ := by
    rw [hbc']; exact (cubeMapOf hβ).e_comm
  obtain ⟨wL, hwL, hm⟩ := GlobalTheory.Unif.RigidifyIso.exists_rigidified_iso _ _ (specOf φ) G₀ GW
    (bc.hom.left ≫ pullback.fst G₀.hom (specOf φ)) he U₀.LG UW.LG (by rw [hbc']; exact hLβ)

  obtain ⟨Wo, hWo, hψ⟩ := h5.psiOnExists R₀ _ hR D₀
  have hgen : (specOf φ).base (genericPoint (Spec (CommRingCat.of W))) ∈ Wo := by
    have : (specOf φ).base (genericPoint (Spec (CommRingCat.of W))) = genericPoint (Spec (CommRingCat.of R₀)) := by
      rw [genericPoint_eq_bot_of_affine, genericPoint_eq_bot_of_affine]
      exact PrimeSpectrum.ext (Ideal.comap_bot_of_injective φ hφ)
    rw [this]; exact hWo

  obtain ⟨D₁, hD₁, U₁, hLG, -, -⟩ := h4.unifBaseChange R₀ W _ _ hR hW' φ (map_maximalIdeal_le φ) D₀ A₀ G₀ hG U₀
    Wo hψ hgen GW bc mbc A' dA eA mE wA UW.LG wL he hwL hm
  obtain ⟨-, w₀, -, g₀, -, m₀, -⟩ := exists_iso_pair_of_eq hLG
  obtain ⟨hDid, -⟩ := GlobalTheory.sixthLaws_and_unifUniq.2 W _ hW' D₁ DW A' AW GW hGW U₁ UW w₀ g₀ m₀
  have h := GlobalTheory.Mum.isPullDeg_unique_and_comp.2 R₀ W W φ (RingHom.id W) hφ Function.injective_id D₀.toPre D₁.toPre
    DW.toPre ⟨hD₁⟩ ⟨hDid⟩
  rwa [RingHom.id_comp] at h

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryActionBaseChangeSubalgebra
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.ZH GlobalTheory.UPoinc GlobalTheory.UCovSep
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UCovSep

theorem uAct_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (R R' : Subalgebra o Ω) (h : R ≤ R') (P : PolAV (Sp R)) (P' : PolAV (Sp R')) (φ : P'.A.left ⟶ P.A.left), IsGrpPullback P'.A P.A (spMap (Subalgebra.inclusion h).toRingHom) φ → LBIso P'.L (P.L.pull φ) → ∀ (act : 𝓞 E → (P.A ⟶ P.A)) (u : Sp (ratHull R) ⟶ Xo.XF c), (∀ a, IsMonHom (act a)) → GlobalTheory.UCovSep.UAct Xo c P act (toRat R) u → ∃ act' : 𝓞 E → (P'.A ⟶ P'.A), (∀ a, IsMonHom (act' a)) ∧ (∀ a, (act' a).left ≫ φ = φ ≫ (act a).left) ∧ GlobalTheory.UCovSep.UAct Xo c P' act' (toRat R') (spMap (Subalgebra.inclusion (ratHull_mono h)).toRingHom ≫ u) := by
  intro E _ _ _ H Dw l Xo c o Ω _ _ _ R R' h P P' φ hφ hL act u hact hU

  have inj : ∀ {T : Over (Sp R')} {x y : T ⟶ P'.A}, pushPt hφ.1.w x = pushPt hφ.1.w y → x = y := fun {T x y} e =>
    Over.OverMorphism.ext (hφ.1.hom_ext (congrArg (fun q => q.left) e) (by rw [Over.w, Over.w]))
  let act' : 𝓞 E → (P'.A ⟶ P'.A) := fun a => Over.homMk (hφ.1.lift (φ ≫ (act a).left) P'.A.hom
    (by rw [Category.assoc, Over.w, hφ.1.w])) (hφ.1.lift_snd _ _ _)
  have ha : ∀ a, (act' a).left ≫ φ = φ ≫ (act a).left := fun a => hφ.1.lift_fst _ _ _
  have pa : ∀ {T : Over (Sp R')} (x : T ⟶ P'.A) a, pushPt hφ.1.w (x ≫ act' a) = pushPt hφ.1.w x ≫ act a := fun x a =>
    Over.OverMorphism.ext (by
      show (x.left ≫ _) ≫ _ = (x.left ≫ _) ≫ _
      rw [Category.assoc, ha, Category.assoc])
  have pm : ∀ {T : Over (Sp R')} (x y : T ⟶ P'.A), pushPt hφ.1.w (x * y) = pushPt hφ.1.w x * pushPt hφ.1.w y :=
    fun x y => map_mul (pushHom hφ _) x y
  have hact' : ∀ a, IsMonHom (act' a) := fun a => isMonHom_of_mul _ fun T x y => inj (by
    have := hact a
    rw [pa, pm, pm, pa, pa, MonObj.mul_comp])
  refine ⟨act', hact', ha, ?_⟩

  obtain ⟨G, _, α, β, hα, hβ, hLG, hf⟩ := hU
  set g := (Subalgebra.inclusion (ratHull_mono h)).toRingHom with hg
  have hG := isGrpPullback_pullback G (spMap g)
  have e : spMap g ≫ spMap (toRat R) = spMap (toRat R') ≫ spMap (Subalgebra.inclusion h).toRingHom := by
    rw [← Spec.map_comp, ← Spec.map_comp]; rfl
  have hα₀ : IsGrpPullback ((Over.pullback (spMap g)).obj G) P.A
      (spMap (toRat R') ≫ spMap (Subalgebra.inclusion h).toRingHom) (pullback.fst _ _ ≫ α) := (hG.comp hα).congr e rfl
  have w : (pullback.fst G.hom (spMap g) ≫ α) ≫ P.A.hom =
      (((Over.pullback (spMap g)).obj G).hom ≫ spMap (toRat R')) ≫ spMap (Subalgebra.inclusion h).toRingHom := by
    rw [Category.assoc]; exact hα₀.1.w
  have e₁ := hφ.1.lift_fst _ _ w
  have hα' := hφ.cancel (hα₀.congr rfl e₁.symm) (hφ.1.lift_snd _ _ w)
  have hβ' := (hG.comp hβ).congr (Category.assoc _ _ _).symm rfl
  refine ⟨_, _, hφ.1.lift _ _ w, pullback.fst _ _ ≫ β, hα', hβ', ?_, fun a => ?_⟩
  · exact LBIso.trans (pull_isLB P'.isLB _) (pull_isLB P.isLB _) (pull_isLB Xo.univ.t.PP.isLB _)
      (GenSpread.lbIso_pull_of_lbIso hL _ e₁.symm) (GenSpread.lbIso_pull_comp _ rfl rfl hLG)
  · obtain ⟨f, hfα, hfβ⟩ := hf a
    have hfl : ((Over.pullback (spMap g)).map f).left ≫ pullback.fst G.hom (spMap g) = pullback.fst G.hom (spMap g) ≫ f.left :=
      pullback.lift_fst _ _ _
    refine ⟨(Over.pullback (spMap g)).map f, ?_, ?_⟩
    · apply hφ.1.hom_ext
      · rw [Category.assoc, e₁, Category.assoc, ha, ← Category.assoc (hφ.1.lift _ _ w), e₁,
          ← Category.assoc _ (pullback.fst _ _), hfl, Category.assoc, hfα, Category.assoc]
      · rw [Category.assoc, hφ.1.lift_snd, Category.assoc, Over.w, hφ.1.lift_snd, ← Category.assoc, Over.w]
    · rw [← Category.assoc, hfl, Category.assoc, hfβ, Category.assoc]

end GlobalTheory.UCovSep
end
end

