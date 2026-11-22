import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0672
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0046
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PsiCoordExistsUniqueUpToUnitLocal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0567
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTrivialisationsCorrespond
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0009
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.GenCalc
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0027
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.GeneratorValues
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEqAddOfRedVEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0655
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0673
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0677
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PsiCoordinatesFourthPowerAssociated
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.SiegLoc GlobalTheory.LN GlobalTheory
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PsiFourthCoord

open ReciprocityTheory.ChartRestriction.G.DVR

variable {R : Type} [CommRing R] [IsDomain R]

def cstHom {Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of R)) (z : Z) : R →+* Z.presheaf.stalk z :=
  (Z.presheaf.germ (q ⁻¹ᵁ ⊤) z trivial).hom.comp ((q.app ⊤).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)

theorem cst_eq_cstHom {Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of R)) (z : Z) (a : R) :
    cst q z a = cstHom q z a :=
  gs_eq q z ⊤ trivial _

theorem cst_inj {Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of (FractionRing R))) (z : Z) {a b : R}
    (h : cst (p ≫ jK R) z a = cst (p ≫ jK R) z b) : a = b := by
  by_contra hne
  have hu := IntegralExpansionLocal.isUnit_cst_of_ne_zero p z (sub_ne_zero.2 hne)
  rw [cst_eq_cstHom, map_sub, ← cst_eq_cstHom, ← cst_eq_cstHom, h, sub_self] at hu
  exact not_isUnit_zero hu

theorem gm_top {Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of R)) (z : Z) {V : (Spec (CommRingCat.of R)).Opens}
    (hV : ⊤ ≤ V) (g : Γ(Spec (CommRingCat.of R), V)ˣ) : ∃ u : Rˣ, (gm q z V g).val = cst q z (u : R) := by
  refine ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom.toMonoidHom (res hV g), ?_⟩
  rw [← gm_res q z hV trivial g, ← gs_unit q z ⊤ trivial]
  simp only [cst, Units.coe_map, MonoidHom.coe_coe]
  congr 1
  change _ = ((Scheme.ΓSpecIso (CommRingCat.of R)).hom ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).inv).hom _
  rw [Iso.hom_inv_id]
  rfl

theorem gm_of_top {Z X : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of R)) (z : Z) (x : Spec (CommRingCat.of R) ⟶ X)
    {f : Z ⟶ X} (hf : f = q ≫ x) {V : X.Opens} (hV : ⊤ ≤ x ⁻¹ᵁ V) (g : Γ(X, V)ˣ) :
    ∃ u : Rˣ, (gm f z V g).val = cst q z (u : R) := by
  subst hf
  rw [← gm_pull q x z V (hV trivial) g]
  exact gm_top q z hV _

end GlobalTheory.PsiFourthCoord

namespace GlobalTheory.PsiFourthCoord

open ReciprocityTheory.ChartRestriction.G.DVR

variable {R : Type} [CommRing R] [IsDomain R]

theorem val_psi_of_coord (D : DegPre R) (χ : D.X) {r : R} {j : PUnit → D.P.L.ι}
    (h : jK R ⁻¹ᵁ ⊤ ≤ (LB.LinComb D.P.L (K := PUnit) (fun _ => D.xK χ) (fun _ => -1)).U j)
    (e : ((jK R).app ⊤).hom (DegPre.toOpen (R := R) ⊤ r) =
      ((TK R).left.presheaf.map (homOfLE h).op).hom ((D.psi χ).s j).val)
    {Z : Scheme.{0}} (p : Z ⟶ (TK R).left) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι)
    (hJ : J (p ≫ D.xK χ) = j PUnit.unit) : (val (D.psi χ) p z J).val = cst (p ≫ jK R) z r := by
  have m₁ : p z ∈ LB.wchart D.P.L (K := PUnit) (fun _ => D.xK χ) j := h trivial
  have hto : ∀ a, DegPre.toOpen (R := R) ⊤ a = (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a := fun a => by
    simp [DegPre.toOpen]
  rw [val_of (D.psi χ) p z J j (fun _ => hJ)]
  refine (gs_unit p z _ m₁ _).symm.trans ((gs_res p z h trivial _).symm.trans ?_)
  refine (congrArg (gs p z _) e.symm).trans ((gs_pull p (jK R) z ⊤ trivial _).trans ?_)
  rw [hto]; rfl

theorem val_famMult_two {D : DegPre R} (hB : D.TauBimult) {F : Type} [Field F] [Algebra (FractionRing R) F]
    {T : Over (Spec (CommRingCat.of R))} (σ : T ⟶ TF (R := R) F) {z : T.left}
    {J : (T.left ⟶ D.P.A.left) → D.P.L.ι} (hJ : Good D.P.L z J) (χ : D.X) :
    val (DegPre.famMult D F 2 χ 0) σ.left z J =
      val (D.psi χ) (σ.left ≫ jFK (R := R) F) z J ^ 2 * val D.rigK (σ.left ≫ jFK (R := R) F) z J ^ 2 := by
  have C : IsCub (th D z J) := isCub_cubV D.cub hJ
  have t0 := tau_mul σ hJ hB 0 0 χ
  rw [add_zero, cPoint_zero, C.face, _root_.mul_one] at t0
  have τ0 : val (D.tau 0 χ) (σ.left ≫ jFK (R := R) F) z J = 1 := mul_eq_left.1 t0.symm
  rw [val_famMult σ hJ, UUA.val_powGen', UUA.val_powGen', tau_symm σ hJ, τ0, _root_.one_mul]

theorem val_rigK_of_top (D : DegPre R) {Z : Scheme.{0}} (p : Z ⟶ (TK R).left) (z : Z)
    (J : (Z ⟶ D.P.A.left) → D.P.L.ι) (hJ : Good D.P.L z J)
    (h : ⊤ ≤ (eSec D.P.A) ⁻¹ᵁ D.P.L.U (J ((p ≫ jK R) ≫ eSec D.P.A))) :
    ∃ u : Rˣ, (val D.rigK p z J).val = cst (p ≫ jK R) z u := by
  have e1 : p ≫ (toUnit (TK R)).left = p ≫ jK R := by
    congr 1
  rw [DegPre.rigK, val_pull hJ, e1]
  rw [val_of D.rig (p ≫ jK R) z J (fun _ => J ((p ≫ jK R) ≫ eSec D.P.A)) (fun _ => rfl)]
  exact gm_top _ z (fun y _ => Set.mem_iInter.2 fun _ => h trivial) _

theorem exists_good_pts (P : PolAV (Spec (CommRingCat.of R))) (F : Type) [Field F] [Algebra (FractionRing R) F]
    {Z : Scheme.{0}} (t : Z ⟶ Spec (CommRingCat.of R)) (a : Spec (CommRingCat.of F) ⟶ Z) (ha : a ≫ t = DegPre.jFR F)
    (z : Z) (pk : (Spec (CommRingCat.of R) ⟶ P.A.left) → P.L.ι)
    (hpk : ∀ q, q ≫ P.A.hom = 𝟙 _ → ⊤ ≤ q ⁻¹ᵁ P.L.U (pk q)) :
    ∃ J, Good P.L z J ∧ ∀ q, q ≫ P.A.hom = 𝟙 _ → J (t ≫ q) = pk q := by
  obtain ⟨J, hJ, e⟩ := exists_good P.L P.isLB z (K := {q : Spec (CommRingCat.of R) ⟶ P.A.left // q ≫ P.A.hom = 𝟙 _})
    (fun q => t ≫ q.1) (fun q => pk q.1) (fun a' b' h => by
      have : a'.1 = b'.1 := GC.vpt_ext F P a'.2 b'.2 (by rw [← ha, Category.assoc, Category.assoc, h])
      rw [this]) (fun q => hpk q.1 q.2 trivial)
  exact ⟨J, hJ, fun q hq => e ⟨q, hq⟩⟩

end GlobalTheory.PsiFourthCoord

open GlobalTheory.PsiFourthCoord ReciprocityTheory.ChartRestriction.G.DVR in

theorem GlobalTheory.psi_coord_fourth_associated : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D D' : DegData R (maximalIdeal R)) (Φ : D'.toPre.P.A ≅ D.toPre.P.A) (w : LB.Iso (LB.LinComb D'.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D'.toPre.P.A.left) (fun _ => 2)) ((LB.LinComb D.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D.toPre.P.A.left) (fun _ => 2)).pull Φ.hom.left)), w.IsGen → ∀ (nu : D.toPre.X) (mu : D'.toPre.X) (z : (DegPre.BF D.toPre (FractionRing R)).left), (∀ (J : ((DegPre.BF D.toPre (FractionRing R)).left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : ((DegPre.BF D.toPre (FractionRing R)).left ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Geo.Tor.Good D.toPre.P.L z J → Geo.Tor.Good D'.toPre.P.L z J' → val (DegPre.famMult D'.toPre (FractionRing R) 2 (mu) 0) (fst (TF (R := R) (FractionRing R)) D.toPre.P.A).left z J' ^ 2 = (ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q) (ReciprocityTheory.ChartRestriction.G.DVR.cP D'.toPre (DegPre.BF D.toPre (FractionRing R)) (mu)).left * (ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q) (1 : (DegPre.BF D.toPre (FractionRing R)) ⟶ D'.toPre.P.A).left)⁻¹) ^ 2 * val (DegPre.famMult D.toPre (FractionRing R) 2 (nu) 0) (fst (TF (R := R) (FractionRing R)) D.toPre.P.A).left z J ^ 2) → ∀ (r r' : R), PsiCoord D.toPre nu r → PsiCoord D'.toPre mu r' → Associated (r ^ 4) (r' ^ 4) := by
  intro R _ _ _ D D' Φ w _ nu mu z H r r' hr hr'
  classical
  set π := (fst (TF (R := R) (FractionRing R)) D.toPre.P.A).left ≫ jFK (R := R) (FractionRing R) with hπdef
  have hπ : π ≫ jK R = (DegPre.BF D.toPre (FractionRing R)).hom :=
    (Category.assoc _ _ _).trans (Over.w (fst (TF (R := R) (FractionRing R)) D.toPre.P.A))
  have za : (DegPre.zF D.toPre (FractionRing R)).left ≫ (π ≫ jK R) = DegPre.jFR (FractionRing R) := by
    rw [hπ]; exact Over.w (DegPre.zF D.toPre (FractionRing R))
  obtain ⟨j, hj, h, e⟩ := hr
  obtain ⟨j', hj', h', e'⟩ := hr'
  choose pk hpk using fun q : Spec (CommRingCat.of R) ⟶ D.toPre.P.A.left => GC.exists_chart_top D.toPre.P.L D.toPre.P.isLB q
  choose pk' hpk' using fun q : Spec (CommRingCat.of R) ⟶ D'.toPre.P.A.left =>
    GC.exists_chart_top D'.toPre.P.L D'.toPre.P.isLB q
  let pkD : (Spec (CommRingCat.of R) ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι := fun q =>
    if q = (D.toPre.c nu).left then j PUnit.unit else pk q
  let pkD' : (Spec (CommRingCat.of R) ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι := fun q =>
    if q = (D'.toPre.c mu).left then j' PUnit.unit else pk' q
  have hpkD : ∀ q, q ≫ D.toPre.P.A.hom = 𝟙 _ → ⊤ ≤ q ⁻¹ᵁ D.toPre.P.L.U (pkD q) := fun q _ => by
    by_cases hq : q = (D.toPre.c nu).left
    · subst hq; simp only [pkD, if_pos rfl]; exact hj
    · simp only [pkD, if_neg hq]; exact (hpk q).ge
  have hpkD' : ∀ q, q ≫ D'.toPre.P.A.hom = 𝟙 _ → ⊤ ≤ q ⁻¹ᵁ D'.toPre.P.L.U (pkD' q) := fun q _ => by
    by_cases hq : q = (D'.toPre.c mu).left
    · subst hq; simp only [pkD', if_pos rfl]; exact hj'
    · simp only [pkD', if_neg hq]; exact (hpk' q).ge
  obtain ⟨J, hJ, eJ⟩ := exists_good_pts D.toPre.P (FractionRing R) (π ≫ jK R) _ za z pkD hpkD
  obtain ⟨J', hJ', eJ'⟩ := exists_good_pts D'.toPre.P (FractionRing R) (π ≫ jK R) _ za z pkD' hpkD'
  have HH := H J J' hJ hJ'
  have pc : ∀ {X : Over (Spec (CommRingCat.of R))} (x : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ X),
      x.left ≫ X.hom = 𝟙 _ := fun x => Over.w x
  have hc : (D.toPre.c nu).left ≫ D.toPre.P.A.hom = 𝟙 _ := pc _
  have hc' : (D'.toPre.c mu).left ≫ D'.toPre.P.A.hom = 𝟙 _ := pc _
  have he : eSec D.toPre.P.A ≫ D.toPre.P.A.hom = 𝟙 _ := pc η[D.toPre.P.A]
  have he' : eSec D'.toPre.P.A ≫ D'.toPre.P.A.hom = 𝟙 _ := pc η[D'.toPre.P.A]
  have hcΦ : ((D'.toPre.c mu).left ≫ Φ.hom.left) ≫ D.toPre.P.A.hom = 𝟙 _ := by
    rw [Category.assoc, Over.w Φ.hom]; exact hc'
  have heΦ : (eSec D'.toPre.P.A ≫ Φ.hom.left) ≫ D.toPre.P.A.hom = 𝟙 _ := by
    rw [Category.assoc, Over.w Φ.hom]; exact he'
  have V1 := val_psi_of_coord D.toPre nu h e π z J (by
    rw [show π ≫ D.toPre.xK nu = (π ≫ jK R) ≫ (D.toPre.c nu).left from (Category.assoc _ _ _).symm, eJ _ hc]
    simp only [pkD, if_pos rfl])
  have V1' := val_psi_of_coord D'.toPre mu h' e' π z J' (by
    rw [show π ≫ D'.toPre.xK mu = (π ≫ jK R) ≫ (D'.toPre.c mu).left from (Category.assoc _ _ _).symm, eJ' _ hc']
    simp only [pkD', if_pos rfl])
  obtain ⟨a, V2⟩ := val_rigK_of_top D.toPre π z J hJ (by rw [eJ _ he]; exact hpkD _ he)
  obtain ⟨a', V2'⟩ := val_rigK_of_top D'.toPre π z J' hJ' (by rw [eJ' _ he']; exact hpkD' _ he')
  have hψ : (ReciprocityTheory.ChartRestriction.G.DVR.cP D'.toPre (DegPre.BF D.toPre (FractionRing R)) mu).left =
      (π ≫ jK R) ≫ (D'.toPre.c mu).left := by
    rw [hπ, cP, Over.comp_left]; rfl
  have hψ1 : (1 : DegPre.BF D.toPre (FractionRing R) ⟶ D'.toPre.P.A).left = (π ≫ jK R) ≫ eSec D'.toPre.P.A := by
    rw [hπ]; rfl
  have O1 : ∃ b : Rˣ, (ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q)
      (ReciprocityTheory.ChartRestriction.G.DVR.cP D'.toPre (DegPre.BF D.toPre (FractionRing R)) mu).left).val = cst (π ≫ jK R) z b := by
    have k1 : J ((ReciprocityTheory.ChartRestriction.G.DVR.cP D'.toPre (DegPre.BF D.toPre (FractionRing R)) mu).left ≫ Φ.hom.left) =
        pkD ((D'.toPre.c mu).left ≫ Φ.hom.left) := by rw [hψ, Category.assoc]; exact eJ _ hcΦ
    have k2 : J' (ReciprocityTheory.ChartRestriction.G.DVR.cP D'.toPre (DegPre.BF D.toPre (FractionRing R)) mu).left =
        pkD' (D'.toPre.c mu).left := by rw [hψ]; exact eJ' _ hc'
    unfold ExpTrans.om Geo.Tor.gw
    refine gm_of_top (π ≫ jK R) z (D'.toPre.c mu).left hψ (fun y _ => ?_) _
    refine ⟨Set.mem_iInter.2 fun _ => Set.mem_iInter.2 fun _ => ?_, Set.mem_iInter.2 fun _ => ?_⟩
    · have m := hpkD _ hcΦ (show y ∈ (⊤ : (Spec (CommRingCat.of R)).Opens) from trivial)
      rw [← k1] at m
      exact m
    · have m := hpkD' _ hc' (show y ∈ (⊤ : (Spec (CommRingCat.of R)).Opens) from trivial)
      rw [← k2] at m
      exact m
  have O2 : ∃ b : Rˣ, (ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q)
      (1 : DegPre.BF D.toPre (FractionRing R) ⟶ D'.toPre.P.A).left).val = cst (π ≫ jK R) z b := by
    have k1 : J ((1 : DegPre.BF D.toPre (FractionRing R) ⟶ D'.toPre.P.A).left ≫ Φ.hom.left) =
        pkD (eSec D'.toPre.P.A ≫ Φ.hom.left) := by rw [hψ1, Category.assoc]; exact eJ _ heΦ
    have k2 : J' (1 : DegPre.BF D.toPre (FractionRing R) ⟶ D'.toPre.P.A).left = pkD' (eSec D'.toPre.P.A) := by
      rw [hψ1]; exact eJ' _ he'
    unfold ExpTrans.om Geo.Tor.gw
    refine gm_of_top (π ≫ jK R) z (eSec D'.toPre.P.A) hψ1 (fun y _ => ?_) _
    refine ⟨Set.mem_iInter.2 fun _ => Set.mem_iInter.2 fun _ => ?_, Set.mem_iInter.2 fun _ => ?_⟩
    · have m := hpkD _ heΦ (show y ∈ (⊤ : (Spec (CommRingCat.of R)).Opens) from trivial)
      rw [← k1] at m
      exact m
    · have m := hpkD' _ he' (show y ∈ (⊤ : (Spec (CommRingCat.of R)).Opens) from trivial)
      rw [← k2] at m
      exact m
  obtain ⟨b, O1⟩ := O1
  obtain ⟨b', O2⟩ := O2
  rw [val_famMult_two D'.tau_bimult _ hJ', val_famMult_two D.tau_bimult _ hJ] at HH
  set Ωc := ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q)
    (ReciprocityTheory.ChartRestriction.G.DVR.cP D'.toPre (DegPre.BF D.toPre (FractionRing R)) mu).left
  set Ω1 := ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q)
    (1 : DegPre.BF D.toPre (FractionRing R) ⟶ D'.toPre.P.A).left
  have HH2 : (val (D'.toPre.psi mu) π z J' ^ 2 * val D'.toPre.rigK π z J' ^ 2) ^ 2 * Ω1 ^ 2 =
      Ωc ^ 2 * (val (D.toPre.psi nu) π z J ^ 2 * val D.toPre.rigK π z J ^ 2) ^ 2 := by
    rw [HH, mul_pow, inv_pow, mul_right_comm, inv_mul_cancel_right]
  have V := congrArg Units.val HH2
  simp only [Units.val_mul, Units.val_pow_eq_pow_val] at V
  rw [V1, V1', V2, V2', O1, O2] at V
  have V' : cst (π ≫ jK R) z (r' ^ 4 * ((a' : R) ^ 4 * (b' : R) ^ 2)) =
      cst (π ≫ jK R) z ((b : R) ^ 2 * (a : R) ^ 4 * r ^ 4) := by
    simp only [cst_eq_cstHom, map_mul, map_pow] at V ⊢
    linear_combination V
  have hR := cst_inj π z V'
  refine ⟨(b ^ 2 * a ^ 4) * (a' ^ 4 * b' ^ 2)⁻¹, ?_⟩
  have k : r ^ 4 * ((b ^ 2 * a ^ 4 : Rˣ) : R) = r' ^ 4 * ((a' ^ 4 * b' ^ 2 : Rˣ) : R) := by
    push_cast
    linear_combination -hR
  rw [Units.val_mul, ← _root_.mul_assoc, k, _root_.mul_assoc, Units.mul_inv, _root_.mul_one]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PullLinInjective
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef

namespace GlobalTheory.PolFan

namespace CarDim

section Pull

variable {O : Type} [CommRing O] {bar : O → O} {ψ : InvFun O} {X X₁ : Type} [AddCommGroup X] [Module O X]
  [AddCommGroup X₁] [Module O X₁] {m : ℕ}

theorem isCell_pull_equiv [Module.Finite O X] [Module.Finite O X₁] {γ : Fin m → LinearMap.BilinForm ℤ X₁}
    (h : IsCell bar ψ γ) (e : X ≃ₗ[O] X₁) : IsCell bar ψ fun i => pull e.toLinearMap (γ i) :=
  ⟨fun i => pull_mem _ (h.mem i), fun i _ => h.nonneg i _, (linearOn_pull_iff e.surjective).2 h.linear,
    IsStrict.of_pull (r := e.symm.toLinearMap) e.symm.surjective (by simpa using h.strict)⟩

def pullLin (r : X →ₗ[O] X₁) : LinearMap.BilinForm ℤ X₁ →ₗ[ℤ] LinearMap.BilinForm ℤ X where
  toFun := pull r
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem pullLin_apply (r : X →ₗ[O] X₁) (β : LinearMap.BilinForm ℤ X₁) : pullLin r β = pull r β := rfl

theorem pullLin_injective {r : X →ₗ[O] X₁} (hr : Function.Surjective r) : Function.Injective (pullLin r) :=
  fun β β' h => LinearMap.ext₂ fun a b => by
    obtain ⟨a, rfl⟩ := hr a
    obtain ⟨b, rfl⟩ := hr b
    exact LinearMap.congr_fun₂ h a b

theorem genRank_pull {r : X →ₗ[O] X₁} (hr : Function.Surjective r) (γ : Fin m → LinearMap.BilinForm ℤ X₁) :
    genRank (fun i => pull r (γ i)) = genRank γ := by
  unfold genRank
  have e : Submodule.span ℤ (Set.range fun i => pull r (γ i)) = (Submodule.span ℤ (Set.range γ)).map (pullLin r) := by
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  rw [e]
  exact (Submodule.equivMapOfInjective _ (pullLin_injective hr) _).finrank_eq.symm

theorem inRCone_pull_iff {r : X →ₗ[O] X₁} (hr : Function.Surjective r) {γ : Fin m → LinearMap.BilinForm ℤ X₁}
    {β : LinearMap.BilinForm ℤ X₁} : InRCone (fun i => pull r (γ i)) (pull r β) ↔ InRCone γ β := by
  refine exists_congr fun c => and_congr_right fun _ => ?_
  constructor
  · intro h
    refine LinearMap.ext₂ fun a b => ?_
    obtain ⟨a, rfl⟩ := hr a
    obtain ⟨b, rfl⟩ := hr b
    have := LinearMap.congr_fun₂ h a b
    simpa [LinearMap.sum_apply] using this
  · intro h
    refine LinearMap.ext₂ fun a b => ?_
    have := LinearMap.congr_fun₂ h (r a) (r b)
    simpa [LinearMap.sum_apply] using this

end Pull

section Rad

variable {O : Type} [CommRing O] {X X₁ : Type} [AddCommGroup X] [Module O X] [AddCommGroup X₁] [Module O X₁]

def orad (β : LinearMap.BilinForm ℤ X) : Submodule O X where
  carrier := {x | ∀ (a : O) (y : X), β (a • x) y = 0}
  add_mem' := by
    intro x x' hx hx' a y
    rw [smul_add, map_add, LinearMap.add_apply, hx a y, hx' a y, add_zero]
  zero_mem' := by
    intro a y
    rw [smul_zero, map_zero, LinearMap.zero_apply]
  smul_mem' := by
    intro c x hx a y
    rw [smul_smul]
    exact hx _ y

theorem mem_orad {β : LinearMap.BilinForm ℤ X} {x : X} : x ∈ orad (O := O) β ↔ ∀ (a : O) (y : X), β (a • x) y = 0 :=
  Iff.rfl

theorem orad_pull {r : X →ₗ[O] X₁} (hr : Function.Surjective r) (β : LinearMap.BilinForm ℤ X₁) :
    orad (pull r β) = (orad β).comap r := by
  ext x
  simp only [Submodule.mem_comap, mem_orad, pull_apply, map_smul]
  constructor
  · intro h a y
    obtain ⟨y, rfl⟩ := hr y
    exact h a y
  · intro h a y
    exact h a (r y)

def qEquiv {r : X →ₗ[O] X₁} (hr : Function.Surjective r) (N : Submodule O X₁) : (X ⧸ N.comap r) ≃ₗ[O] (X₁ ⧸ N) :=
  (Submodule.quotEquivOfEq _ _ (by rw [LinearMap.ker_comp, Submodule.ker_mkQ])).trans
    ((N.mkQ ∘ₗ r).quotKerEquivOfSurjective (N.mkQ_surjective.comp hr))

theorem qEquiv_mk {r : X →ₗ[O] X₁} (hr : Function.Surjective r) (N : Submodule O X₁) (x : X) :
    qEquiv hr N (Submodule.Quotient.mk x) = Submodule.Quotient.mk (r x) := rfl

end Rad

section Def

variable {O : Type} [CommRing O] (bar : O → O) (ψ : InvFun O)

def cdimSet (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] (N : Submodule O X) (β : LinearMap.BilinForm ℤ X) :
    Set ℕ :=
  {k | ∃ (m : ℕ) (δ : Fin m → LinearMap.BilinForm ℤ (X ⧸ N)), IsCell bar ψ δ ∧ InRCone (fun i => pull N.mkQ (δ i)) β ∧
    genRank δ = k}

def cdimQ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] (N : Submodule O X) (β : LinearMap.BilinForm ℤ X) : ℕ :=
  sInf (cdimSet bar ψ X N β)

variable {bar ψ}

theorem cdimSet_pull {X X₁ : Type} [AddCommGroup X] [Module O X] [Module.Finite O X] [AddCommGroup X₁] [Module O X₁]
    [Module.Finite O X₁] {r : X →ₗ[O] X₁} (hr : Function.Surjective r) (β : LinearMap.BilinForm ℤ X₁) :
    cdimSet bar ψ X (orad (pull r β)) (pull r β) = cdimSet bar ψ X₁ (orad β) β := by
  rw [orad_pull hr]
  set N := orad (O := O) β
  let e := qEquiv hr N
  have key : ∀ δ : LinearMap.BilinForm ℤ (X₁ ⧸ N),
      pull (N.comap r).mkQ (pull e.toLinearMap δ) = pull r (pull N.mkQ δ) := fun δ => rfl
  ext k
  constructor
  · rintro ⟨m, δ', h1, h2, rfl⟩
    refine ⟨m, fun i => pull e.symm.toLinearMap (δ' i), isCell_pull_equiv h1 e.symm, ?_,
      genRank_pull e.symm.surjective _⟩
    rw [← inRCone_pull_iff hr]
    convert h2 using 2 with i
    rw [← key, pull_pull_symm]
  · rintro ⟨m, δ, h1, h2, rfl⟩
    refine ⟨m, fun i => pull e.toLinearMap (δ i), isCell_pull_equiv h1 e, ?_, genRank_pull e.surjective _⟩
    simp only [key]
    exact (inRCone_pull_iff hr).2 h2

theorem zero_mem_cdimSet {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X] [Subsingleton X] (N : Submodule O X)
    (β : LinearMap.BilinForm ℤ X) : 0 ∈ cdimSet bar ψ X N β := by
  haveI : Subsingleton (X ⧸ N) := ⟨fun a b => by
    induction a using Submodule.Quotient.induction_on
    induction b using Submodule.Quotient.induction_on
    rename_i a b
    rw [Subsingleton.elim a b]⟩
  refine ⟨0, Fin.elim0, ⟨fun i => i.elim0, fun i => i.elim0, fun c _ => ?_, ?_⟩,
    ⟨Fin.elim0, fun i => i.elim0, ?_⟩, ?_⟩
  · rw [ψ.eval_of_subsingleton]
    simp
  · refine ⟨1, 0, one_pos, fun i => i.elim0, fun β' _ _ => ?_, fun β' _ _ _ => ⟨1, Fin.elim0, one_pos, ?_⟩⟩
    · simp [InvFun.evalZ, ψ.eval_of_subsingleton]
    · rw [Fin.sum_univ_zero, one_smul]
      exact LinearMap.ext₂ fun a b => by rw [Subsingleton.elim a 0]; simp
  · exact LinearMap.ext₂ fun a b => by rw [Subsingleton.elim a 0]; simp
  · simp [genRank]

end Def

section Fun

variable {O : Type} [CommRing O] (bar : O → O) (ψ : InvFun O)

open Classical in

def carFun : InvFun O where
  toFun n B := if h : ∃ β : LinearMap.BilinForm ℤ (Fin n → O), β ∈ balForms bar (Fin n → O) ∧ (∀ y, 0 ≤ β y y) ∧
      ∀ a b, B a b = β a b then (cdimQ bar ψ (Fin n → O) (orad h.choose) h.choose : ℝ) else 0
  inv n m r hr B := by
    obtain ⟨s, hs⟩ := Module.projective_lifting_property r LinearMap.id hr
    have hrs : ∀ a, r (s a) = a := fun a => LinearMap.congr_fun hs a
    by_cases h : ∃ β : LinearMap.BilinForm ℤ (Fin m → O), β ∈ balForms bar (Fin m → O) ∧ (∀ y, 0 ≤ β y y) ∧
        ∀ a b, B a b = β a b
    · have h' : ∃ β : LinearMap.BilinForm ℤ (Fin n → O), β ∈ balForms bar (Fin n → O) ∧ (∀ y, 0 ≤ β y y) ∧
          ∀ a b, B (r a) (r b) = β a b :=
        ⟨pull r h.choose, pull_mem r h.choose_spec.1, fun y => h.choose_spec.2.1 _, fun a b => h.choose_spec.2.2 _ _⟩
      rw [dif_pos h, dif_pos h']
      have e : h'.choose = pull r h.choose := LinearMap.ext₂ fun a b => by
        have h1 := h'.choose_spec.2.2 a b
        have h2 := h.choose_spec.2.2 (r a) (r b)
        rw [pull_apply]
        exact_mod_cast h1.symm.trans h2
      rw [e]
      unfold cdimQ
      rw [cdimSet_pull hr]
    · have h' : ¬ ∃ β : LinearMap.BilinForm ℤ (Fin n → O), β ∈ balForms bar (Fin n → O) ∧ (∀ y, 0 ≤ β y y) ∧
          ∀ a b, B (r a) (r b) = β a b := by
        rintro ⟨β, h1, h2, h3⟩
        exact h ⟨pull s β, pull_mem s h1, fun y => h2 _, fun a b => by rw [pull_apply, ← h3, hrs, hrs]⟩
      rw [dif_neg h, dif_neg h']
  zero B := by
    split_ifs with h
    · have := Nat.sInf_eq_zero.2 (Or.inl (zero_mem_cdimSet (bar := bar) (ψ := ψ) (orad h.choose) h.choose))
      unfold cdimQ
      rw [this, Nat.cast_zero]
    · rfl

variable {bar ψ}

theorem evalZ_carFun {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X] {β : LinearMap.BilinForm ℤ X}
    (hβ : β ∈ balForms bar X) (hp : ∀ y, 0 ≤ β y y) :
    (carFun bar ψ).evalZ β = cdimQ bar ψ X (orad β) β := by
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin' O X
  rw [InvFun.evalZ, (carFun bar ψ).eval_eq hs]
  dsimp only [carFun]
  split_ifs with h
  · have e : h.choose = pull s β := LinearMap.ext₂ fun a b => by
      have := h.choose_spec.2.2 a b
      rw [pull_apply]
      exact_mod_cast this.symm
    rw [e]
    unfold cdimQ
    rw [cdimSet_pull hs]
  · exact absurd ⟨pull s β, pull_mem s hβ, fun y => hp _, fun a b => rfl⟩ h

end Fun

end CarDim

end GlobalTheory.PolFan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RealConeCoordsIntegralOfPartOfIntBasis
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell

theorem GlobalTheory.cone_coords_int_of_isPartOfBasis : ∀ (X : Type) [AddCommGroup X] (m : ℕ) (u : Fin m → LinearMap.BilinForm ℤ X) (hu : ∀ i, u i ∈ balForms (id : ℤ → ℤ) X), IsPartOfBasis (fun i => (⟨u i, hu i⟩ : balForms (id : ℤ → ℤ) X)) → ∀ (β : LinearMap.BilinForm ℤ X) (t : Fin m → ℝ), toReal β = ∑ i, t i • toReal (u i) → ∀ i, ∃ z : ℤ, t i = z := by
  intro X _ m u hu hpb β t h
  obtain ⟨n, b, hb⟩ := hpb
  have hpt : ∀ a y, (β a y : ℝ) = ∑ i, t i * (u i a y : ℝ) := fun a y => by
    have := LinearMap.congr_fun₂ h a y
    simpa [LinearMap.sum_apply, toReal_apply] using this
  have hsym : ∀ a y, β a y = β y a := fun a y => by
    have h1 := hpt a y
    have h2 := hpt y a
    have : (β a y : ℝ) = β y a := by
      rw [h1, h2]
      exact Finset.sum_congr rfl fun i _ => by rw [((mem_balForms_int).1 (hu i)) a y]
    exact_mod_cast this
  let β' : balForms (id : ℤ → ℤ) X := ⟨β, (mem_balForms_int).2 hsym⟩
  set s := b.repr β' with hs
  have hexp : ∀ a y, β a y = ∑ j, s j * ((b j : LinearMap.BilinForm ℤ X) a y) := fun a y => by
    have h0 := congrArg (fun γ : balForms (id : ℤ → ℤ) X => (γ : LinearMap.BilinForm ℤ X) a y) (b.sum_repr β')
    simp only [Submodule.coe_sum, Submodule.coe_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul] at h0
    exact h0.symm
  let e : Fin m ⊕ Fin n → ℝ := Sum.elim t 0
  let c : Fin m ⊕ Fin n → ℝ := fun j => (s j : ℝ) - e j
  have hc : ∑ j, c j • toReal ((balForms (id : ℤ → ℤ) X).subtype (b j)) = 0 := by
    refine LinearMap.ext₂ fun a y => ?_
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, toReal_apply, Submodule.subtype_apply, smul_eq_mul,
      LinearMap.zero_apply, c, sub_mul, Finset.sum_sub_distrib]
    rw [sub_eq_zero]
    have e1 : (∑ j, (s j : ℝ) * ((b j : LinearMap.BilinForm ℤ X) a y : ℝ)) = β a y := by
      rw [hexp a y]; push_cast; rfl
    rw [e1, hpt a y, Fintype.sum_sum_type]
    simp [e, hb]
  intro i
  refine ⟨s (Sum.inl i), ?_⟩
  have := sum_mul_eq_zero_of_sum_toReal (X := X) (j := (balForms (id : ℤ → ℤ) X).subtype) Subtype.val_injective
    (b.coord (Sum.inl i)) hc
  simp only [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply] at this
  rw [Finset.sum_eq_single (Sum.inl i)] at this
  · simp [c, e] at this
    linarith
  · intro j _ hj; simp [hj]
  · simp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowCuspMultiplicityInputStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.row_cusp_multiplicity_input : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : SideA D cf jE) (S : RatDat D.ntw) (In : RatIn D S) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (M : MtFam D) (tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E) (Q : D.what₂.places.Pl → Finset (PlE D.host)), MtInput D M tup Q → (∀ v, NG.OverPl (Pq v) v) → GalEx D → RowCusp D A.row → GlobalTheory.RowTie.ChebSplit D.nd → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → (∀ j g, ∃ z : ℤ, eExp D j g = z) → (∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) → ∃ c0 : Big D, ∀ (b0 b1 : Big D) (Sx : Finset (PlE D.host)) (T : TwR D.LL0 D.nd) (Sp : RingSpec D cf b0 b1 Sx T), (∀ (l : ℕ) [Fact l.Prime] j, (c0 l j).1 ≤ (b0 l j).1) → In.Sb ⊆ Sx → (∀ P P', P ∈ Sx → IsConjPl D.host P P' → P' ∈ Sx) → (∀ p ∈ low, placesOver D.host.E p ⊆ ↑Sx) → ∃ (F : TwF T) (ex : NExp D.R D.host D.what₂ D.LL0 D.nd (T.ntw A.bare F (TwL.empty T))) (h0 : _), (∀ i j b, (ex.Bsup i j b).FG ∧ Submodule.span (FractionRing ((T.ntw A.bare F (TwL.empty T)).O i)) (ex.Bsup i j b : Set (ex.Fm i j b)) = ⊤) ∧ ∀ th, Nonempty (SideB (⟨T.ntw A.bare F (TwL.empty T), ex, h0, th, Sp.br, Sp.br_ind⟩ : TwNew D).toD7 ((⟨T.ntw A.bare F (TwL.empty T), ex, h0, th, Sp.br, Sp.br_ind⟩ : TwNew D).cf cf) ((⟨T.ntw A.bare F (TwL.empty T), ex, h0, th, Sp.br, Sp.br_ind⟩ : TwNew D).row A.row) low Pq ((⟨T.ntw A.bare F (TwL.empty T), ex, h0, th, Sp.br, Sp.br_ind⟩ : TwNew D).rat S) In.hL In.eig In.θ) := by
  first | exact @GlobalTheory.HeightCounting.FormsStep.second_step | exact GlobalTheory.HeightCounting.FormsStep.second_step | (intros; apply GlobalTheory.HeightCounting.FormsStep.second_step <;> assumption)
end

