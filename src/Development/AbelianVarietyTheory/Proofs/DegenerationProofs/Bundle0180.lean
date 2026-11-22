import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigIsoCongr
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0041
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0039
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsNormalisedGen
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0066
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0059
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SurjectiveCubeOfGeneric
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0061
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0162
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0137
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnifOfCmp
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0176
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.KTrivOfKTrivNonemptyOpenNormalCharZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0177
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0178
import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0089
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0175

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniformisationCompleteLocalDomainPrime
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN

noncomputable section
namespace GlobalTheory.PrimeUnif

theorem exists_cdvr (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [CharZero R] (I : Ideal R) [I.IsPrime] :
    ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsLocalRing V) (φ : R →+* V), CDvr V ∧ Function.Injective φ ∧
      (IsLocalRing.maximalIdeal V).comap φ = I := by
  rcases eq_or_ne I ⊥ with rfl | hI
  · let K := FractionRing R
    let φ : R →+* PowerSeries K := (PowerSeries.C (R := K)).comp (algebraMap R K)
    have hφ : Function.Injective φ := PowerSeries.C_injective.comp (IsFractionRing.injective R K)
    refine ⟨PowerSeries K, inferInstance, inferInstance, inferInstance, φ,
      ⟨inferInstance, ?_, charZero_of_injective_ringHom hφ⟩, hφ, ?_⟩
    · rw [PowerSeries.maximalIdeal_eq_span_X]; infer_instance
    · refine eq_bot_iff.2 fun r hr => ?_
      rw [Ideal.mem_comap, PowerSeries.maximalIdeal_eq_span_X, Ideal.mem_span_singleton,
        PowerSeries.X_dvd_iff] at hr
      have : algebraMap R K r = 0 := by simpa [φ] using hr
      exact (Ideal.mem_bot).2 (IsFractionRing.injective R K (this.trans (map_zero _).symm))
  · obtain ⟨V, _, _, hV, hc, φ, h1, h2⟩ := exists_complete_discreteValuationRing_of_prime_lt ⊥ I (bot_lt_iff_ne_bot.2 hI)
    have hφ : Function.Injective φ := (RingHom.injective_iff_ker_eq_bot φ).2 h1
    exact ⟨V, inferInstance, inferInstance, inferInstance, φ, ⟨hV, hc, charZero_of_injective_ringHom hφ⟩, hφ, h2⟩

theorem isCPMap_of_eq (hG : GlobalFnsSt) {V : Type} [CommRing V] [IsDomain V] {A : PolAV (Sp (FractionRing V))}
    {G' : Over (Sp V)} [GrpObj G'] [IsCommMonObj G'] [Smooth G'.hom] (gen : (Over.pullback (jK V)).obj G' ≅ A.A)
    {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {P : CP G} {f : Sp V ⟶ S} {F : G'.left ⟶ G.left}
    {hw : F ≫ G.hom = G'.hom ≫ f} (P₁ P₂ : CP G') (e : P₂.L = P₁.L) {w} (h : IsCPMap P₁ P f F hw w) :
    ∃ w', IsCPMap P₂ P f F hw w' := by
  obtain ⟨L, c, s, hs, hr, hc⟩ := P₂
  obtain rfl : L = P₁.L := e
  let P₂ : CP G' := ⟨P₁.L, c, s, hs, hr, hc⟩
  have : Flat (G3 G').hom := by
    show Flat (pullback.fst G'.hom (pullback.fst G'.hom G'.hom ≫ G'.hom) ≫ G'.hom)
    infer_instance
  have h1 : Function.Surjective (pullback.snd G'.hom (jK V)).appTop.hom := by
    have hw : gen.hom.left ≫ A.A.hom = pullback.snd G'.hom (jK V) := Over.w gen.hom
    have : IsIso gen.hom.left := ((Over.forget _).mapIso gen).isIso_hom
    have : IsIso gen.hom.left.appTop := inferInstanceAs (IsIso (gen.hom.left.app ⊤))
    rw [← hw]
    exact surj_comp (ConcreteCategory.bijective_of_isIso gen.hom.left.appTop).2 (hG _ _ A.isAb).2
  let o : Over.mk (jK V) ⟶ G' := 1
  let o₃ : Over.mk (jK V) ⟶ G3 G' := lift o (lift o o)
  have es : ∀ (Z : Scheme.{0}) (r : Z ⟶ G'.left) (z : Z) (J), Good P₁.L.L z J → val P₁.sym r z J = val s r z J :=
    ValueForm.gen_unique_of_injective P₁.L.isLB (fun _ _ _ => rfl) (pullback.fst G'.hom (jK V))
      (ValueForm.app_generic_injective _) (pullback.snd _ _)
      (pullback.lift o.left (𝟙 _) ((Over.w o).trans (Category.id_comp _).symm)) (pullback.lift_snd _ _ _) h1
      P₁.sym_gen hs fun y J hJ => by
        rw [pullback.lift_fst]
        exact (P₁.val_sym_one hJ).trans (P₂.val_sym_one hJ).symm
  have ec : ∀ (T : Over (Sp V)) (z : T.left) (J), Good P₁.L.L z J → ∀ x y u : T ⟶ G',
      cubV P₁.c z J x y u = cubV c z J x y u := fun T z J hJ x y u =>
    ValueForm.gen_unique_of_injective P₁.L.isLB (φ := thφ G' (x3 G')) (ε := thε) (φ' := thφ G' (x3 G')) (ε' := thε)
      (fun _ _ _ => rfl) (pullback.fst (G3 G').hom (jK V))
      (ValueForm.app_generic_injective _) (pullback.snd _ _)
      (pullback.lift o₃.left (𝟙 _) ((Over.w o₃).trans (Category.id_comp _).symm)) (pullback.lift_snd _ _ _)
      (ValueForm.surjective_cube_baseChange hG _ A.isAb gen) P₁.c.isGen c.isGen
      (fun y J hJ => by
        rw [pullback.lift_fst]
        exact ((isCub_cubV P₁.c (T := Over.mk (jK V)) hJ).face 1 1).trans
          ((isCub_cubV c (T := Over.mk (jK V)) hJ).face 1 1).symm) _ _ z J hJ
  refine ⟨w, h.mul, h.gen, fun T z J' J hJ' hJ W hW => ?_⟩
  obtain ⟨a₁, a₂, a₃⟩ := h.vals T z J' J hJ' hJ W hW
  exact ⟨a₁, fun x => (a₂ x).trans (congrArg (W x⁻¹ * ·) (es _ x.left z J' hJ')),
    fun x y u => (a₃ x y u).trans (congrArg (W (x * y * u) * W x * W y * W u * ·) (ec T z J' hJ' x y u))⟩

section Psi
variable {R V : Type} [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] {I : Ideal R} {I' : Ideal V}
  {D : DegPre R} {D' : DegPre V} {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {A' : PolAV (Spec (CommRingCat.of (FractionRing V)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] {G' : Over (Spec (CommRingCat.of V))} [GrpObj G']
  [IsCommMonObj G']
  (psi : ∀ χ : D.X, LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => ptK (D.c χ)) (fun _ => -1)))
  (h : ∀ χ, (psi χ).IsGen)

def gtWithPsi {e : ℕ} (g : GtCoord I D e G) : GtCoord I (withPsi D psi h) e G :=
  ⟨g.q, g.q_hom, g.q_flat, g.q_surj, g.q_affine, g.i, g.i_hom, g.isKernel, g.t, g.t_gen, g.t_mul, g.t_unit, g.t_weight⟩

def preWithPsi (U : PreU I D A G) : PreU I (withPsi D psi h) A G :=
  ⟨U.semi, U.gen, U.gen_hom, U.P, U.wA, U.wA_gen, fun e => gtWithPsi psi h (U.gt e), U.gt_q, U.gt_t, U.w, U.w_gen,
    U.w_vals, U.w_compat⟩

def cmpWithPsi {φ : R →+* V} {U : PreU I D A G} {U' : PreU I' D' A' G'} {F : G'.left ⟶ G.left} (C : Cmp φ U U' F) :
    Cmp φ (preWithPsi psi h U) U' F :=
  ⟨C.pb, C.wL, C.wL_map, C.β, C.pbB, C.v, C.v_gen, C.xe, C.c_pr, C.lev, C.map_le⟩

theorem exists_move {φ : R →+* V} {U : PreU I D A G} {U' : PreU I' D' A' G'} {F : G'.left ⟶ G.left} (C : Cmp φ U U' F)
    (hD : IsPullDeg φ (withPsi D psi h) D') (D₂ : DegPre R) (e : D₂ = withPsi D psi h)
    (h₁ : hD.e.hom.left ≫ pullback.fst _ _ = C.β) (h₂ : HEq hD.w C.v) (h₃ : hD.xe = C.xe) :
    ∃ (U₂ : PreU I D₂ A G) (C₂ : Cmp φ U₂ U' F) (hD₂ : IsPullDeg φ D₂ D'), U₂.P = U.P ∧ U₂.gen = U.gen ∧
      hD₂.e.hom.left ≫ pullback.fst _ _ = C₂.β ∧ HEq hD₂.w C₂.v ∧ hD₂.xe = C₂.xe := by
  subst e
  exact ⟨preWithPsi psi h U, cmpWithPsi psi h C, hD, rfl, rfl, h₁, h₂, h₃⟩

end Psi

set_option maxHeartbeats 1600000 in

theorem exists_setting (hL : Laws) (hL2 : Laws2) (hL3 : Laws3) {R : Type} [CommRing R] [IsDomain R] {I : Ideal R}
    {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (P : CP G) (hS : IsSemiAbelian G)
    (hW : HypW G P.L.L) (hsp : SplitOver G I) (A : PolAV (Sp (FractionRing R)))
    (gen : (Over.pullback (jK R)).obj G ≅ A.A) [IsMonHom gen.hom]
    (hA : LBIso (A.L.pull gen.hom.left) (P.L.L.pull (pullback.fst G.hom (jK R))))
    {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] (hV : CDvr V) (g : R →+* V) (hg : Function.Injective g)
    (hI : I ≤ (IsLocalRing.maximalIdeal V).comap g) :
    ∃ (A' : PolAV (Sp (FractionRing V))) (s : HidaSetting V A' ((Over.pullback (spMap g)).obj G)) (w : _),
      IsCPMap s.P P (spMap g) (pullback.fst G.hom (spMap g)) pullback.condition w := by
  let G' : Over (Sp V) := (Over.pullback (spMap g)).obj G
  have pb : IsGrpPullback G' G (spMap g) (pullback.fst G.hom (spMap g)) := isGrpPullback_pullback G _
  have hS' : IsSemiAbelian G' := IsSemiAbelian.pullback _ G hS
  obtain ⟨P', w, hP', hw⟩ := exists_cp_pull _ _ (spMap g) G G' _ pullback.condition (toBase_mul_pullback G _) P
  have hW' : HypW G' P'.L.L :=
    SymBaseChange.hypS_baseChange _ _ G G' _ _ _ _ P.L.isLB P'.L.isLB pb ⟨w, hw.gen⟩ hW

  let gam : FractionRing R →+* FractionRing V :=
    IsFractionRing.lift (g := (algebraMap V (FractionRing V)).comp g) ((IsFractionRing.injective V _).comp hg)
  have hgam : ∀ r, gam (algebraMap R _ r) = algebraMap V _ (g r) := fun r => IsFractionRing.lift_algebraMap _ r
  have sq : spMap gam ≫ jK R = jK V ≫ spMap g :=
    (spMap_comp _ gam).symm.trans ((congrArg spMap (RingHom.ext hgam)).trans (spMap_comp g _))
  obtain ⟨A', gA, pA, -, mA, tA⟩ := hL.polBaseChange _ _ (spMap gam) A
  have gpA : IsGrpPullback A'.A A.A (spMap gam) gA := ⟨pA, fun T x y x₀ y₀ hx hy => by
    have e₁ : x₀ = toBase pA.w x := Over.OverMorphism.ext hx
    have e₂ : y₀ = toBase pA.w y := Over.OverMorphism.ext hy
    rw [e₁, e₂, ← mA]; rfl⟩
  have gpG : IsGrpPullback A.A G (jK R) (gen.inv.left ≫ pullback.fst G.hom (jK R)) := by
    have : IsMonHom gen.symm.hom := by show IsMonHom gen.inv; infer_instance
    exact ((isGrpPullback_of_iso gen.symm).comp (isGrpPullback_pullback G (jK R))).congr (Category.id_comp _) rfl
  have gp' : IsGrpPullback ((Over.pullback (jK V)).obj G') G (spMap gam ≫ jK R)
      (pullback.fst G'.hom (jK V) ≫ pullback.fst G.hom (spMap g)) :=
    ((isGrpPullback_pullback G' (jK V)).comp pb).congr sq.symm rfl
  obtain ⟨eA, mE, heA⟩ := grpPullback_iso gp' (gpA.comp gpG)
  have hgi : gen.inv.left ≫ gen.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
  have wA : LBIso (A'.L.pull eA.hom.left) (P'.L.L.pull (pullback.fst G'.hom (jK V))) := by
    rw [hP']
    refine LBIso.trans (pull_isLB A'.isLB _) (pull_isLB (pull_isLB A.isLB gA) eA.hom.left)
      (pull_isLB (pull_isLB P.L.isLB _) _)
      ((LBIso.symm tA).chartPull (Geo.Tor.chartPullPull A'.L _ _ rfl) (Geo.Tor.chartPullPull (A.L.pull gA) _ _ rfl)) ?_
    refine LBIso.chartPull (h := eA.hom.left ≫ gA ≫ gen.inv.left)
      (Geo.Tor.chartPullLinComb A.L gA (fun _ => eA.hom.left) (fun _ => gen.hom.left) _ _ fun _ => ?_)
      (Geo.Tor.chartPullLinComb P.L.L _ _ (fun _ => pullback.fst G.hom (jK R)) _ _ fun _ => ?_) hA
    · rw [Category.assoc, Category.assoc, hgi, Category.comp_id]
    · rw [← heA]; simp only [Category.assoc]
  obtain ⟨wA, hwA⟩ := wA
  have hpr : IsProper (pullback.snd G'.hom (jK V)) := by
    have hw : eA.hom.left ≫ A'.A.hom = pullback.snd G'.hom (jK V) := Over.w eA.hom
    have : IsIso eA.hom.left := ((Over.forget _).mapIso eA).isIso_hom
    have := A'.isAb.proper
    rw [← hw]; infer_instance

  let m := IsLocalRing.maximalIdeal V
  obtain ⟨E₀, hE₀⟩ := hsp
  let k : R ⧸ I →+* V ⧸ m ^ (0 + 1) := Ideal.Quotient.lift I ((Ideal.Quotient.mk _).comp g) fun a ha =>
    Ideal.Quotient.eq_zero_iff_mem.2 (by rw [zero_add, pow_one]; exact hI ha)
  obtain ⟨E₁, -, -, -, -, hE₁⟩ := hL3.gtBaseChange _ _ (spMap k) E₀ _ hE₀
  have hc : spMap k ≫ spMap (Ideal.Quotient.mk I) = thick V m 0 ≫ spMap g :=
    (spMap_comp _ k).symm.trans (spMap_comp g (Ideal.Quotient.mk _))
  obtain ⟨e, he, -⟩ := grpPullback_iso (((isGrpPullback_pullback _ (spMap k)).comp
    (isGrpPullback_pullback G (spMap (Ideal.Quotient.mk I)))).congr hc rfl)
    ((isGrpPullback_pullback G' (thick V m 0)).comp pb)
  have := E₁.free
  have := E₁.finite
  obtain ⟨Dat⟩ := isGt_of_iso e hE₁
  obtain ⟨Q₀, -⟩ := exists_tq_of_gtDatum _ E₁ _ Dat
  obtain ⟨P₀, v, hP₀⟩ := exists_isLevelCP m 0 P'
  have hm : (m ^ (0 + 1)).IsMaximal := by rw [zero_add, pow_one]; infer_instance
  have hS₀ : IsSemiAbelian (thickObj V m 0 G') := IsSemiAbelian.pullback _ G' hS'
  have hb : Nonempty (BiTriv P₀.c Q₀.i) := by
    letI : Field (V ⧸ m ^ (0 + 1)) := Ideal.Quotient.field _
    exact @BiextTriv.main (V ⧸ m ^ (0 + 1)) _ E₁.X _ _ _ (thickObj V m 0 G') _ _ hS₀.smooth hS₀.geomConnected
      P₀.L P₀.c Q₀.i Q₀.i_hom
  obtain ⟨w₀, -, hw₀, -, -, hp, -⟩ := hW'
  have hev := EvenTriv.exists_even_cubTriv hL hL2 V G' hS' hpr P' w₀ hw₀ hp _ _ E₁.X Q₀ P₀ _ _
    (IsPullback.of_hasPullback G'.hom (thick V m 0)) v hP₀ hb
  exact ⟨A', ⟨hV, hS', eA, mE, P', wA, hwA, E₁.X, Q₀, P₀, ⟨v, hP₀⟩, hev⟩, w, hw⟩

theorem exists_unif : Laws → Laws2 → Laws3 → Ega → USt → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), admitted R I → IsPrincipalIdealRing (R ⧸ I) → ∀ (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (P : CP G), IsSemiAbelian G → HypW G P.L.L → SplitOver G I → ThetaNZ G P.L.L → ∀ (A : PolAV (Sp (FractionRing R))) (gen : (Over.pullback (jK R)).obj G ≅ A.A), IsMonHom gen.hom → LBIso (A.L.pull gen.hom.left) (P.L.L.pull (pullback.fst G.hom (jK R))) → ∃ (D : DegData R I) (U : Unif I D A G), U.LG = P.L ∧ U.gen = gen := by
  intro hL hL2 hL3 hE hU R _ _ _ I hR hpi G _ _ P hS hW hsp hθ A gen hgen hA
  have := hR.1.1
  have := hR.2.2.1
  have hI := hR.2.2.2.1
  obtain ⟨V, _, _, _, φ, hV, hφ, hc⟩ := exists_cdvr R I
  have := hV.1
  have hB : AdmBase V (IsLocalRing.maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hV.2.1⟩
  have hle : I.map φ ≤ IsLocalRing.maximalIdeal V := Ideal.map_le_iff_le_comap.2 hc.ge
  obtain ⟨A', s, w, hw⟩ := exists_setting hL hL2 hL3 P hS hW hsp A gen hA hV φ hφ hc.ge
  obtain ⟨D', U₀, hLG, -, -⟩ := hU V A' _ s
  obtain ⟨U', hU'⟩ := (GlobalTheory.LN.PreForm.under_exists_and_expands hL hL2 V _ D' A' _ s.semi).1 U₀.toUnifPre
  obtain ⟨D, U, rfl, rfl⟩ := GlobalTheory.T.exists_uniformization_data_complete_local_prime hL hL2 hL3 hE hU R I hR hpi G P hS hW hsp A gen hgen hA
  have := s.semi.smooth
  obtain ⟨w', hw'⟩ := isCPMap_of_eq hL.globalFns s.gen s.P U'.P (hU'.2.1.trans hLG) hw
  obtain ⟨C, -⟩ := GlobalTheory.T.exists_compare_uniformisationData_pullback hL hL2 hE R V I _ hR.1 hB (IsLocalRing.maximalIdeal.isMaximal V).ne_top φ hle D _ A A'
    G _ U U' _ (isGrpPullback_pullback G _) w' hw'
  obtain ⟨psi, h, Dd, hD, e, h₁, h₂, h₃⟩ := GlobalTheory.T.exists_degData_psi_of_section_nonzero_fibres hL hL2 hE R I hR V hV φ hφ hc D D' A A' G _ U U' U₀ _ C hU' hθ
  obtain ⟨U₂, C₂, hD₂, eP, eg, k₁, k₂, k₃⟩ := exists_move psi h C hD Dd.toPre e h₁ h₂ h₃
  obtain ⟨U₁, -, hU₁, -⟩ := GlobalTheory.UnifDescent.exists_unif_of_cmp hL hL2 hE R V I _ hR.1 hB hI.ne_top φ hφ hle Dd D' A A' G _ U₂ U' U₀ _ C₂ hD₂
    hU' k₁ k₂ k₃
  exact ⟨Dd, U₁, hU₁.2.1.symm.trans (congrArg CP.L eP), hU₁.1.symm.trans eg⟩

end GlobalTheory.PrimeUnif
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.KTrivOfKTrivNonemptyOpenNormalCharZeroStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kTriv_of_kTriv_nonemptyOpen_normal_charZero : Out.Laws → ∀ (S : Scheme.{0}) [IsIntegral S] [IsLocallyNoetherian S], IsNormalScheme S → (∀ n : ℕ, n ≠ 0 → (n : Γ(S, ⊤)) ≠ 0) → ∀ (U : S.Opens), (U : Set S).Nonempty → ∀ (G : Over S) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (_ : CubicalStr G L), IsAbelianScheme G → Out.RelAmple G L.L → Out.KTriv ((Over.pullback U.ι).obj G) (L.L.pull (pullback.fst G.hom U.ι)) → Out.KTriv G L.L := by
  first | exact @GlobalTheory.KTrivSpread.kTriv_of_open_normal | exact GlobalTheory.KTrivSpread.kTriv_of_open_normal | (intros; apply GlobalTheory.KTrivSpread.kTriv_of_open_normal <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PotentialSemiAbelianReductionOfRetractStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.potentialSemiAbelianReduction_of_retract : ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K] (B Q : Over (Sp K)) [GrpObj B] [GrpObj Q] (i : B ⟶ Q) (r : Q ⟶ B), IsMonHom i → IsMonHom r → i ≫ r = 𝟙 B → PotModel V K Q (fun _ _ _ G _ => IsSemiAbelian G) → PotModel V K B (fun _ _ _ G _ => IsSemiAbelian G) := by
  first | exact @GlobalTheory.SS.potModel_semiAbelian_of_retract | exact GlobalTheory.SS.potModel_semiAbelian_of_retract | (intros; apply GlobalTheory.SS.potModel_semiAbelian_of_retract <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaParameterOfThetaParameterMulDegreeStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaParameter_of_thetaParameter_mul_degree : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab) (N k : ℕ) (a : u.PtC) (g : GtPtF u.D.toPre (PadicAlgCl p)), 4 ≤ N → 1 ≤ k → u.ParAt (N * k) a g → u.ParAt N a g := by
  first | exact @GlobalTheory.ParameterRoot.parAt_of_parAt_mul | exact GlobalTheory.ParameterRoot.parAt_of_parAt_mul | (intros; apply GlobalTheory.ParameterRoot.parAt_of_parAt_mul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaSystemBaseSectionValueChart
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ZH.PowSec
open GlobalTheory.Points

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} {ρ : S.Real} {M : RatModel o Ω}
  {U₀ : M.Z.Opens} (Q : ZHPre ρ M U₀)

def GV (c : S.J → Ω) (a : Q.L.L.ι) (K : Type) [Field K] (x : Sp K ⟶ Q.G.left) (v : K) : Prop :=
  ∀ (β : Ω →+* K) (g : Sp K ⟶ pullback ρ.P.A.hom Q.u₀) (r : Sp K ⟶ (baseOver (Sp S.R) ⊗ ρ.P.A).left)
    (jP : ρ.P.L.ι), g ≫ Q.φ = x → g ≫ pullback.snd _ _ ≫ U₀.ι = spMap β ≫ M.pt →
    r ≫ (snd (baseOver (Sp S.R)) ρ.P.A).left = g ≫ pullback.fst _ _ →
    ⊤ ≤ (g ≫ pullback.fst ρ.P.A.hom Q.u₀) ⁻¹ᵁ ρ.P.L.U jP →
    ∑ i, β (c i) * valF r _ ((ρ.s i).f (fun _ => jP)) =
      valF g _ (Q.w.s (fun _ => jP, fun _ => a)).val ^ (S.N : ℤ) * v

variable {K : Type} [Field K] {c : S.J → Ω} {a a' : Q.L.L.ι}

theorem le_w {g : Sp K ⟶ pullback ρ.P.A.hom Q.u₀} {jP : ρ.P.L.ι}
    (h : ⊤ ≤ (g ≫ pullback.fst ρ.P.A.hom Q.u₀) ⁻¹ᵁ ρ.P.L.U jP) (h' : ⊤ ≤ (g ≫ Q.φ) ⁻¹ᵁ Q.L.L.U a) :
    ⊤ ≤ g ⁻¹ᵁ (LB.div (ρ.P.L.pull (pullback.fst ρ.P.A.hom Q.u₀)) (Q.L.L.pull Q.φ)).U (fun _ => jP, fun _ => a) :=
  le_inf' (le_wchart _ _ _ fun _ => h) (le_wchart _ _ _ fun _ => h')

theorem val_w {g : Sp K ⟶ pullback ρ.P.A.hom Q.u₀} {jP jP' : ρ.P.L.ι}
    (h : ⊤ ≤ (g ≫ pullback.fst ρ.P.A.hom Q.u₀) ⁻¹ᵁ ρ.P.L.U jP) (h' : ⊤ ≤ (g ≫ Q.φ) ⁻¹ᵁ Q.L.L.U a)
    (k : ⊤ ≤ (g ≫ pullback.fst ρ.P.A.hom Q.u₀) ⁻¹ᵁ ρ.P.L.U jP') (k' : ⊤ ≤ (g ≫ Q.φ) ⁻¹ᵁ Q.L.L.U a') :
    valF g _ (Q.w.s (fun _ => jP, fun _ => a)).val =
      valF (g ≫ pullback.fst ρ.P.A.hom Q.u₀) _ (ρ.P.L.g jP jP').val * (valF (g ≫ Q.φ) _ (Q.L.L.g a a').val)⁻¹ *
        valF g _ (Q.w.s (fun _ => jP', fun _ => a')).val := by
  refine (val_gen Q.w_gen g (le_w Q h h') (le_w Q k k')).trans (congrArg (· * _) ?_)
  refine (val_div_g _ _ _ _ g (le_w Q h h') (le_w Q k k')).trans ?_
  exact congrArg₂ (fun x y => x * y⁻¹) ((val_linComb_g (I := PUnit) _ _ 1 _ _ g h k).trans (zpow_one _))
    ((val_linComb_g (I := PUnit) _ _ 1 _ _ g h' k').trans (zpow_one _))

omit Q in
theorem thetaSystem_baseSection_value_chart {r : Sp K ⟶ (baseOver (Sp S.R) ⊗ ρ.P.A).left} {jP jP' : ρ.P.L.ι}
    (h : ⊤ ≤ (r ≫ (snd (baseOver (Sp S.R)) ρ.P.A).left) ⁻¹ᵁ ρ.P.L.U jP)
    (k : ⊤ ≤ (r ≫ (snd (baseOver (Sp S.R)) ρ.P.A).left) ⁻¹ᵁ ρ.P.L.U jP') (i : S.J) :
    valF r _ ((ρ.s i).f (fun _ => jP)) =
      valF (r ≫ (snd (baseOver (Sp S.R)) ρ.P.A).left) _ (ρ.P.L.g jP jP').val ^ (S.N : ℤ) *
        valF r _ ((ρ.s i).f (fun _ => jP')) :=
  (val_sec (ρ.s i) r (j := fun _ => jP) (k := fun _ => jP') (le_wchart _ _ _ fun _ => h)
    (le_wchart _ _ _ fun _ => k)).trans (congrArg (· * _) (val_linComb_g (I := Fin 1) _ _ _ _ _ r h k))

theorem exists_data (hU : (U₀ : Set M.Z).Nonempty) {Y : Scheme.{0}} (x : Y ⟶ Q.G.left) (κ : Y ⟶ Sp Ω)
    (h : x ≫ Q.G.hom = κ ≫ M.pt) : ∃ (g : Y ⟶ pullback ρ.P.A.hom Q.u₀) (r : Y ⟶ (baseOver (Sp S.R) ⊗ ρ.P.A).left),
      g ≫ Q.φ = x ∧ g ≫ pullback.snd _ _ ≫ U₀.ι = κ ≫ M.pt ∧
      r ≫ (snd (baseOver (Sp S.R)) ρ.P.A).left = g ≫ pullback.fst _ _ := by
  have hr : Set.range (κ ≫ M.pt) ⊆ Set.range U₀.ι := by
    rintro _ ⟨w, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact M.top_le_preimage_pt hU (x := κ w) trivial
  let y : Y ⟶ U₀.toScheme := IsOpenImmersion.lift U₀.ι (κ ≫ M.pt) hr
  have hy : y ≫ U₀.ι = κ ≫ M.pt := IsOpenImmersion.lift_fac _ _ _
  let g : Y ⟶ pullback ρ.P.A.hom Q.u₀ := Q.cart.1.lift x y (h.trans hy.symm)
  have hg2 : g ≫ pullback.snd _ _ = y := Q.cart.1.lift_snd x y _
  refine ⟨g, pullback.lift ((g ≫ pullback.fst _ _) ≫ ρ.P.A.hom) (g ≫ pullback.fst _ _)
    (Category.comp_id _), Q.cart.1.lift_fst x y _, ?_, pullback.lift_snd _ _ _⟩
  rw [← Category.assoc, hg2, hy]

theorem exists_data' (hU : (U₀ : Set M.Z).Nonempty) (x : Sp K ⟶ Q.G.left) (β : Ω →+* K)
    (h : x ≫ Q.G.hom = spMap β ≫ M.pt) : ∃ (g : Sp K ⟶ pullback ρ.P.A.hom Q.u₀)
      (r : Sp K ⟶ (baseOver (Sp S.R) ⊗ ρ.P.A).left) (jP : ρ.P.L.ι),
      g ≫ Q.φ = x ∧ g ≫ pullback.snd _ _ ≫ U₀.ι = spMap β ≫ M.pt ∧
      r ≫ (snd (baseOver (Sp S.R)) ρ.P.A).left = g ≫ pullback.fst _ _ ∧
      ⊤ ≤ (g ≫ pullback.fst ρ.P.A.hom Q.u₀) ⁻¹ᵁ ρ.P.L.U jP := by
  obtain ⟨g, r, h1, h2, h3⟩ := exists_data Q hU x _ h
  obtain ⟨jP, hj⟩ := exists_le_preimage_of_iSup_eq_top (g ≫ pullback.fst ρ.P.A.hom Q.u₀) ρ.P.isLB.cover
  exact ⟨g, r, jP, h1, h2, h3, hj⟩

variable {Q} {x : Sp K ⟶ Q.G.left} {v v' : K}

theorem GV.unique (hU : (U₀ : Set M.Z).Nonempty) {β : Ω →+* K} (h : x ≫ Q.G.hom = spMap β ≫ M.pt)
    (ha : ⊤ ≤ x ⁻¹ᵁ Q.L.L.U a) (H : GV Q c a K x v) (H' : GV Q c a K x v') : v = v' := by
  obtain ⟨g, r, jP, rfl, h2, h3, hj⟩ := exists_data' Q hU x β h
  exact mul_left_cancel₀ (zpow_ne_zero _ (val_unit_ne g (le_w Q hj ha) _))
    ((H β g r jP rfl h2 h3 hj).symm.trans (H' β g r jP rfl h2 h3 hj))

theorem GV.chart (ha : ⊤ ≤ x ⁻¹ᵁ Q.L.L.U a) (ha' : ⊤ ≤ x ⁻¹ᵁ Q.L.L.U a') (H : GV Q c a K x v) :
    GV Q c a' K x (valF x _ (Q.L.L.g a' a).val ^ (S.N : ℤ) * v) := by
  rintro β g r jP rfl h2 h3 hj
  have h0 := zpow_ne_zero (S.N : ℤ) (val_unit_ne _ (le_inf' ha' ha) (Q.L.L.g a' a))
  rw [H β g r jP rfl h2 h3 hj, val_w Q hj ha' hj ha, val_g_self ρ.P.isLB _ hj, _root_.one_mul, mul_zpow, inv_zpow]
  field_simp

theorem GV.of_one {β : Ω →+* K} {g : Sp K ⟶ pullback ρ.P.A.hom Q.u₀}
    {r : Sp K ⟶ (baseOver (Sp S.R) ⊗ ρ.P.A).left} {jP : ρ.P.L.ι} (ha : ⊤ ≤ x ⁻¹ᵁ Q.L.L.U a) (h1 : g ≫ Q.φ = x)
    (h2 : g ≫ pullback.snd _ _ ≫ U₀.ι = spMap β ≫ M.pt)
    (h3 : r ≫ (snd (baseOver (Sp S.R)) ρ.P.A).left = g ≫ pullback.fst _ _)
    (hj : ⊤ ≤ (g ≫ pullback.fst ρ.P.A.hom Q.u₀) ⁻¹ᵁ ρ.P.L.U jP)
    (H : ∑ i, β (c i) * valF r _ ((ρ.s i).f (fun _ => jP)) =
      valF g _ (Q.w.s (fun _ => jP, fun _ => a)).val ^ (S.N : ℤ) * v) : GV Q c a K x v := by
  intro β' g' r' jP' k1 k2 k3 kj
  have : Mono Q.φ := (MorphismProperty.monomorphisms _).of_isPullback Q.cart.1.flip
    (inferInstanceAs (Mono U₀.ι))
  have := EndoExtend.isPreimmersion_pt M
  have : Mono (snd (baseOver (Sp S.R)) ρ.P.A).left := inferInstanceAs (Mono (pullback.snd (𝟙 _) ρ.P.A.hom))
  obtain rfl : g' = g := (cancel_mono Q.φ).1 (k1.trans h1.symm)
  obtain rfl : r' = r := (cancel_mono _).1 (k3.trans h3.symm)
  obtain rfl : β' = β := congrArg (·.hom) (Spec.map_injective ((cancel_mono M.pt).1 (k2.symm.trans h2)))
  subst h1
  rw [val_w Q kj ha hj ha, val_g_self Q.L.isLB _ ha, inv_one, _root_.mul_one, mul_zpow, _root_.mul_assoc, ← H,
    Finset.mul_sum, ← h3]
  rw [← h3] at kj hj
  exact Finset.sum_congr rfl fun i _ => by rw [thetaSystem_baseSection_value_chart kj hj, mul_left_comm]

section Ratio

theorem exists_pt {X : Scheme.{0}} (y : X) : ∃ (F : Type) (_ : Field F) (g : Sp F ⟶ X), ∀ w, g w = y :=
  ⟨X.residueField y, inferInstance, X.fromSpecResidueField _, fun _ => Scheme.fromSpecResidueField_apply _ _⟩

theorem exists_ne {P : Scheme.{0}} {O : LB P} {I : Type} {τ : I → O.Sec} (hτ : ⨆ i, nonzeroLocus (τ i) = ⊤)
    (h : Sp K ⟶ P) {k : O.ι} (hk : ⊤ ≤ h ⁻¹ᵁ O.U k) : ∃ i, valF h _ ((τ i).f k) ≠ 0 := by
  obtain ⟨i, hi⟩ := exists_le_preimage_of_iSup_eq_top h hτ
  obtain ⟨k', hk'⟩ := TopologicalSpace.Opens.mem_iSup.1 ((le_preimage_iff h _).1 hi)
  have h1 := (le_preimage_iff h _).2 hk'
  have h2 := le_preimage_mono h (P.basicOpen_le _) h1
  refine ⟨i, ?_⟩
  rw [val_sec (τ i) h hk h2]
  exact mul_ne_zero (val_unit_ne h (le_inf' hk h2) _) ((le_preimage_basicOpen_iff h h2 _).1 h1).ne_zero

theorem exists_mem_basicOpen {P : Scheme.{0}} {O : LB P} {I : Type} {τ : I → O.Sec}
    (hτ : ⨆ i, nonzeroLocus (τ i) = ⊤) (y : P) {k : O.ι} (hk : y ∈ O.U k) : ∃ i, y ∈ P.basicOpen ((τ i).f k) := by
  obtain ⟨F, _, g, hg⟩ := exists_pt y
  have h1 : ⊤ ≤ g ⁻¹ᵁ O.U k := fun w _ => show g w ∈ O.U k from Set.mem_of_eq_of_mem (hg w) hk
  obtain ⟨i, hi⟩ := exists_ne hτ g h1
  exact ⟨i, Set.mem_of_eq_of_mem (hg (IsLocalRing.closedPoint F)).symm
    ((le_preimage_basicOpen_iff g h1 _).2 hi.isUnit trivial)⟩

variable (Q) {P : Scheme.{0}} (ν : P ⟶ Q.G.left) {O : LB P} (τ : S.J → O.Sec) (b : S.J → S.J → Ω)

def Ratio (a : Q.L.L.ι) (k : O.ι) (K : Type) [Field K] (h : Sp K ⟶ P) (v : K) : Prop :=
  v ≠ 0 ∧ ∀ i, GV Q (b i) a K (h ≫ ν) (v * valF h _ ((τ i).f k))

variable {Q ν τ b} {k k' : O.ι} {h : Sp K ⟶ P}

theorem Ratio.unique (hU : (U₀ : Set M.Z).Nonempty) (hτ : ⨆ i, nonzeroLocus (τ i) = ⊤) {β : Ω →+* K}
    (e : (h ≫ ν) ≫ Q.G.hom = spMap β ≫ M.pt) (ha : ⊤ ≤ (h ≫ ν) ⁻¹ᵁ Q.L.L.U a) (hk : ⊤ ≤ h ⁻¹ᵁ O.U k)
    (H : Ratio Q ν τ b a k K h v) (H' : Ratio Q ν τ b a k K h v') : v = v' := by
  obtain ⟨i, hi⟩ := exists_ne hτ h hk
  exact mul_right_cancel₀ hi ((H.2 i).unique hU e ha (H'.2 i))

theorem Ratio.chart (ha : ⊤ ≤ (h ≫ ν) ⁻¹ᵁ Q.L.L.U a) (hk : ⊤ ≤ h ⁻¹ᵁ O.U k)
    (ha' : ⊤ ≤ (h ≫ ν) ⁻¹ᵁ Q.L.L.U a') (hk' : ⊤ ≤ h ⁻¹ᵁ O.U k') (H : Ratio Q ν τ b a k K h v) :
    Ratio Q ν τ b a' k' K h
      (valF (h ≫ ν) _ (Q.L.L.g a' a).val ^ (S.N : ℤ) * (valF h _ (O.g k' k).val)⁻¹ * v) := by
  have h1 := val_unit_ne _ (le_inf' hk' hk) (O.g k' k)
  refine ⟨mul_ne_zero (mul_ne_zero (zpow_ne_zero _ (val_unit_ne _ (le_inf' ha' ha) _)) (inv_ne_zero h1)) H.1,
    fun i => ?_⟩
  convert (H.2 i).chart ha ha' using 1
  rw [val_sec (τ i) h hk' hk]
  field_simp

theorem exists_unit (hU : (U₀ : Set M.Z).Nonempty) (hτ : ⨆ i, nonzeroLocus (τ i) = ⊤)
    (hp : ∀ (K : Type) [Field K] (β : Ω →+* K) (h : Sp K ⟶ P), (h ≫ ν) ≫ Q.G.hom = spMap β ≫ M.pt →
      ⊤ ≤ (h ≫ ν) ⁻¹ᵁ Q.L.L.U a → ⊤ ≤ h ⁻¹ᵁ O.U k → ∃ v, Ratio Q ν τ b a k K h v)
    {Y : Scheme.{0}} [IsIntegral Y] (J : Y ⟶ P) (κ : Y ⟶ Sp Ω) (hJ : (J ≫ ν) ≫ Q.G.hom = κ ≫ M.pt)
    (V : Y.Opens) (hV : V ≤ (J ≫ ν) ⁻¹ᵁ Q.L.L.U a) (hV' : V ≤ J ⁻¹ᵁ O.U k) :
    ∃ t : Γ(Y, V)ˣ, ∀ (K : Type) [Field K] (h : Sp K ⟶ Y), ⊤ ≤ h ⁻¹ᵁ V →
      Ratio Q ν τ b a k K (h ≫ J) (valF h V t.val) := by
  have hβ : ∀ {K : Type} [Field K] (h : Sp K ⟶ Y), spMap (Spec.preimage (h ≫ κ)).hom = h ≫ κ := fun h =>
    Spec.map_preimage _
  have he : ∀ {K : Type} [Field K] (h : Sp K ⟶ Y),
      ((h ≫ J) ≫ ν) ≫ Q.G.hom = spMap (Spec.preimage (h ≫ κ)).hom ≫ M.pt := fun h => by
    rw [hβ, Category.assoc h κ, ← hJ]; simp only [Category.assoc]
  have ha : ∀ {K : Type} [Field K] (h : Sp K ⟶ Y), ⊤ ≤ h ⁻¹ᵁ V → ⊤ ≤ ((h ≫ J) ≫ ν) ⁻¹ᵁ Q.L.L.U a :=
    fun h hh => le_preimage_mono h hV hh
  have hk : ∀ {K : Type} [Field K] (h : Sp K ⟶ Y), ⊤ ≤ h ⁻¹ᵁ V → ⊤ ≤ (h ≫ J) ⁻¹ᵁ O.U k :=
    fun h hh => le_preimage_mono h hV' hh
  obtain ⟨F, _, ξ, hξ⟩ := exists_generic Y
  obtain ⟨g, r, g1, g2, g3⟩ := exists_data Q hU _ κ hJ
  obtain ⟨f, hf⟩ := exists_glue V (fun K _ h v => Ratio Q ν τ b a k K (h ≫ J) v) ξ hξ
    (fun hh v v' H H' => H.unique hU hτ (he ξ) (ha ξ hh) (hk ξ hh) H') (fun y hy => by
      obtain ⟨jP, hj⟩ := exists_chart ρ.P.isLB ((g ≫ pullback.fst ρ.P.A.hom Q.u₀) y)
      obtain ⟨i, hi⟩ := exists_mem_basicOpen hτ (J y) (hV' hy)
      have m1 : r y ∈ (LPow ρ.P.A ρ.P.L S.N (baseOver (Sp S.R))).U (fun _ => jP) :=
        Set.mem_iInter.2 fun _ => by rw [← g3] at hj; exact hj
      have m2 : g y ∈ (pullback ρ.P.A.hom Q.u₀).basicOpen (Q.w.s (fun _ => jP, fun _ => a)).val := by
        rw [Scheme.basicOpen_of_isUnit _ (Units.isUnit _)]
        have := hV hy
        rw [← g1] at this
        exact ⟨Set.mem_iInter.2 fun _ => hj, Set.mem_iInter.2 fun _ => this⟩
      obtain ⟨W, f, hW, hf⟩ := ((Reg.sum Finset.univ fun l => (Reg.val κ (U := ⊤)
        ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (b i l)) trivial).mul (Reg.val r ((ρ.s l).f _) m1)).mul
        ((Reg.inv g _ m2).pow S.N)).mul (Reg.inv J _ hi)
      refine ⟨W ⊓ ((g ≫ pullback.fst ρ.P.A.hom Q.u₀) ⁻¹ᵁ ρ.P.L.U jP ⊓ J ⁻¹ᵁ P.basicOpen ((τ i).f k)),
        resG Y inf_le_left f, ⟨hW, hj, hi⟩, fun K _ h h1 h2 => ?_⟩
      obtain ⟨v, hv⟩ := hp K _ _ (he h) (ha h h2) (hk h h2)
      have n1 : ⊤ ≤ ((h ≫ g) ≫ pullback.fst ρ.P.A.hom Q.u₀) ⁻¹ᵁ ρ.P.L.U jP :=
        le_preimage_mono h (inf_le_right.trans inf_le_left) h1
      have n2 : ⊤ ≤ (h ≫ J) ⁻¹ᵁ P.basicOpen ((τ i).f k) := le_preimage_mono h (inf_le_right.trans inf_le_right) h1
      have n3 : (h ≫ g) ≫ Q.φ = (h ≫ J) ≫ ν := by rw [Category.assoc, g1, Category.assoc]
      have e := hv.2 i _ (h ≫ g) (h ≫ r) jP n3 (by rw [Category.assoc, g2, hβ, Category.assoc])
        (by rw [Category.assoc, g3, Category.assoc]) n1
      have z1 : valF (h ≫ J) _ ((τ i).f k) ≠ 0 := ((le_preimage_basicOpen_iff _ (hk h h2) _).1 n2).ne_zero
      have z2 := val_unit_ne (h ≫ g) (le_w Q n1 (n3 ▸ ha h h2)) (Q.w.s (fun _ => jP, fun _ => a))
      convert hv using 1
      refine (valR_res h _ h1 _).trans ((hf K h (le_preimage_mono h inf_le_left h1)).trans ?_)
      rw [zpow_natCast] at e
      have key : ∀ (A w t : K), w ≠ 0 → t ≠ 0 → A = w ^ S.N * (v * t) → A * (w⁻¹) ^ S.N * t⁻¹ = v := by
        rintro _ w t h1 h2 rfl
        rw [inv_pow]
        field_simp
      refine key _ _ _ z2 z1 (Eq.trans (Finset.sum_congr rfl fun l _ => ?_) e)
      rw [preimage_apply (h ≫ κ) (b i l)]
      rfl)
  exact ⟨(isUnit_of_val f fun K _ h hh => (hf K h hh).1).unit, hf⟩

end Ratio

end GlobalTheory.ZH.PowSec
end

