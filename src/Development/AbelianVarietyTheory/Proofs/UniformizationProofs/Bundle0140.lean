import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigIsoCongr
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0125
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0139
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0012
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0012
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0011
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0041
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CommGroupCommonFactorQuotientCancel
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0077
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0131
import Development.AbelianVarietyTheory.BlockTheory.UniformisationCharts.PairingRatioBijection
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0025
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0053
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0037
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0081
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ToFSurjectiveFractionRing
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem allSixLaws : Laws ∧ Laws2 ∧ Laws3 ∧ Laws4 ∧ Laws5 ∧ Laws6 :=
  ⟨abelianSchemeLaws_all.1, abelianSchemeLaws_all.2,
    furtherLaws_of_laws abelianSchemeLaws_all.1 twistBaseChange⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.EndomorphismTorusExtensionPeriodOfAdjointStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.endomorphism_torusExtension_period_of_adjoint : LL → TwistBCSpanStatement → TWM.VRatioGtStatement → TWStatement → UUStatement → AllUV fun {V} _ _ _ {ϖ} hϖ {D} Q {F} _ _ {v} hv {A} {G} _ _ U => ∀ E E' : EndU U.toUnifPre, Function.Injective E.h → Function.Injective E'.h → LBIso (cubeLB G ![fst G G ≫ E.aG, snd G G] U.LG.L) (cubeLB G ![fst G G, snd G G ≫ E'.aG] U.LG.L) → ∀ y (g g' : GtPtF D.toPre F), GtPtF.IsIota y g → E.Act g g' → GtPtF.IsIota (E'.h y) g' := by
  first | exact @GlobalTheory.KeyIota.main | exact GlobalTheory.KeyIota.main | (intros; apply GlobalTheory.KeyIota.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsPointRepresentingWeightMumfordQuotient
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.WtPoint

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] {X : Type} [AddCommGroup X] {i : splitTorus S X ⟶ G}
  {Y : Scheme.{0}} {f : G.left ⟶ Y}

theorem gm_gen_pull {Z W : Scheme.{0}} {F : Z ⟶ Y} {M : LB Y} {t : LB.Gen (M.pull F)} (ht : t.IsGen) (r : W ⟶ Z) (y : W)
    {j j' : M.ι} (hj : F (r y) ∈ M.U j) (hj' : F (r y) ∈ M.U j') :
    gm r y ((M.pull F).U fun _ => j) (t.s fun _ => j) =
      gm (r ≫ F) y (M.U j ⊓ M.U j') (M.g j j') * gm r y ((M.pull F).U fun _ => j') (t.s fun _ => j') := by
  have hm : r y ∈ (M.pull F).U (fun _ => j) ⊓ (M.pull F).U (fun _ => j') := ⟨mem_pull.2 hj, mem_pull.2 hj'⟩
  have e := congrArg (gm r y _) (ht (fun _ => j) (fun _ => j'))
  rw [map_mul, gm_res _ y _ hm, gm_res _ y _ hm, gm_pull_g M F r y _ _ hm.1 hm.2] at e
  exact e

theorem gm_iso {W : Scheme.{0}} {O N : LB Y} {w : LB.Iso O N} (hw : w.IsGen) (r : W ⟶ Y) (y : W)
    {j j' : N.ι} {k k' : O.ι} (h : r y ∈ N.U j ⊓ O.U k) (h' : r y ∈ N.U j' ⊓ O.U k') :
    gm r y (N.U j ⊓ O.U k) (w.s (j, k)) =
      gm r y (N.U j ⊓ N.U j') (N.g j j') * (gm r y (O.U k ⊓ O.U k') (O.g k k'))⁻¹ *
        gm r y (N.U j' ⊓ O.U k') (w.s (j', k')) := by
  have hm : r y ∈ N.U j ⊓ O.U k ⊓ (N.U j' ⊓ O.U k') := ⟨h, h'⟩
  exact (gm_res r y _ hm _).symm.trans ((congrArg (gm r y _) (hw (j, k) (j', k'))).trans ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) (gm_div O N r y (j, k) (j', k') hm) (gm_res r y _ hm _))))

theorem exists_gen_of_iso
    (hf : ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (g : Z ⟶ G), ((t ≫ i) * g).left ≫ f = g.left ≫ f)
    {O N : LB Y} (hO : O.IsLB) (hN : N.IsLB) (h : LBIso O N) {χ : X} (u : LB.Gen (O.pull f)) (hu : u.IsGen)
    (hχ : ∀ k, IsWt i _ (u.s k).val χ) :
    ∃ v : LB.Gen (N.pull f), v.IsGen ∧ ∀ j, IsWt i _ (v.s j).val χ := by
  obtain ⟨w, hw⟩ := h
  have tr : ∀ (Z : Scheme.{0}) (r : Z ⟶ G.left) (z : Z) (j j' : N.ι) (k k' : O.ι), f (r z) ∈ N.U j ⊓ O.U k →
      f (r z) ∈ N.U j' ⊓ O.U k' →
      gm (r ≫ f) z (N.U j ⊓ O.U k) (w.s (j, k)) * gm r z ((O.pull f).U fun _ => k) (u.s fun _ => k) =
        gm (r ≫ f) z (N.U j ⊓ N.U j') (N.g j j') *
          (gm (r ≫ f) z (N.U j' ⊓ O.U k') (w.s (j', k')) * gm r z ((O.pull f).U fun _ => k') (u.s fun _ => k')) := by
    intro Z r z j j' k k' h h'
    rw [gm_iso hw (r ≫ f) z h h', gm_gen_pull hu r z h.2 h'.2, _root_.mul_assoc, _root_.mul_assoc,
      mul_left_comm (gm (r ≫ f) z (N.U j' ⊓ O.U k') (w.s (j', k'))), inv_mul_cancel_left]
  have glue : ∀ j : N.ι, ∃ s : Γ(G.left, (N.pull f).U fun _ => j)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ G.left) (z : Z) (k : O.ι),
      f (r z) ∈ N.U j ⊓ O.U k → gm r z _ s =
        gm (r ≫ f) z (N.U j ⊓ O.U k) (w.s (j, k)) * gm r z ((O.pull f).U fun _ => k) (u.s fun _ => k) := by
    intro j
    have l₀ : ∀ k, f ⁻¹ᵁ (N.U j ⊓ O.U k) ≤ (N.pull f).U fun _ => j := fun k x hx => mem_pull.2 hx.1
    have l₁ : ∀ k, f ⁻¹ᵁ (N.U j ⊓ O.U k) ≤ (O.pull f).U fun _ => k := fun k x hx => mem_pull.2 hx.2
    obtain ⟨a, ha⟩ : ∃ a : ∀ k, Γ(G.left, f ⁻¹ᵁ (N.U j ⊓ O.U k))ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ G.left) (z : Z) (k : O.ι),
        f (r z) ∈ N.U j ⊓ O.U k → gm r z _ (a k) =
          gm (r ≫ f) z (N.U j ⊓ O.U k) (w.s (j, k)) * gm r z ((O.pull f).U fun _ => k) (u.s fun _ => k) :=
      ⟨fun k => pullU f (N.U j ⊓ O.U k) (w.s (j, k)) * res (l₁ k) (u.s fun _ => k), fun Z r z k hz =>
        (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_pull r f z _ hz _) (gm_res r z (l₁ k) hz _))⟩
    obtain ⟨s, hs⟩ := glue_unit _ _ l₀ (fun x hx => by
        obtain ⟨k, hk⟩ := exists_chart hO (f x)
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨k, mem_pull.1 hx, hk⟩) a (fun k k' x hx => by
        rw [ha _ (𝟙 _) x k hx.1, ha _ (𝟙 _) x k' hx.2, tr _ (𝟙 _) x j j k k' hx.1 hx.2,
          gm_self hN (𝟙 _ ≫ f) x hx.1.1, _root_.one_mul])
    exact ⟨s, fun Z r z k hz => (gm_res r z (l₀ k) hz s).symm.trans
      ((congrArg (gm r z (f ⁻¹ᵁ (N.U j ⊓ O.U k))) (hs k)).trans (ha Z r z k hz))⟩
  choose s hs using glue
  refine ⟨⟨fun J => s (J PUnit.unit)⟩, fun J J' => unit_ext fun y hy => ?_, fun J => isWt_of_gm _ _ ?_⟩
  · obtain ⟨k, hk⟩ := exists_chart hO (f y)
    have h₁ := mem_pull.1 hy.1
    have h₂ := mem_pull.1 hy.2
    exact ((gm_res _ y _ hy _).trans ((hs _ _ (𝟙 _) y k ⟨h₁, hk⟩).trans
      (tr _ (𝟙 _) y _ _ k k ⟨h₁, hk⟩ ⟨h₂, hk⟩))).trans ((map_mul _ _ _).trans (congrArg₂ (· * ·)
        (gm_pull_g N f (𝟙 _) y J J' hy.1 hy.2) ((gm_res _ y _ hy _).trans (hs _ _ (𝟙 _) y k ⟨h₂, hk⟩)))).symm
  · intro Z t g z hz
    obtain ⟨k, hk⟩ := exists_chart hO (f (g.left z))
    have h₂ : f (g.left z) ∈ N.U (J PUnit.unit) ⊓ O.U k := ⟨mem_pull.1 hz, hk⟩
    have h₁ : f (((t ≫ i) * g).left z) ∈ N.U (J PUnit.unit) ⊓ O.U k :=
      (congrArg (fun m : Z.left ⟶ Y => m z ∈ N.U (J PUnit.unit) ⊓ O.U k) (hf Z t g)).mpr h₂
    refine (hs _ _ _ z k h₁).trans (Eq.trans ?_ (congrArg (_ * ·) (hs _ _ _ z k h₂)).symm)
    rw [hf, WtBundle.gm_of_isWt (hχ fun _ => k) t g z (mem_pull.2 h₁.2) (mem_pull.2 h₂.2), gm_charUnit,
      mul_left_comm]

theorem exists_gen_neg {B : Scheme.{0}} {L : LB B} {K : Type} [Fintype K] {φ : K → (Y ⟶ B)} {ε ε' : K → ℤ}
    (hε : ∀ k, ε' k = - ε k) {χ : X} (u : LB.Gen ((LB.LinComb L φ ε).pull f)) (hu : u.IsGen)
    (hχ : ∀ k, IsWt i _ (u.s k).val (-χ)) :
    ∃ v : LB.Gen ((LB.LinComb L φ ε').pull f), v.IsGen ∧ ∀ j, IsWt i _ (v.s j).val χ := by
  refine ⟨⟨fun J => (u.s J)⁻¹⟩, fun J J' => ?_, fun J => ?_⟩
  · refine unit_ext fun y hy => ?_
    have h₁ : f y ∈ LB.wchart L φ (J PUnit.unit) := mem_pull.1 hy.1
    have h₂ : f y ∈ LB.wchart L φ (J' PUnit.unit) := mem_pull.1 hy.2
    have e : gm (𝟙 _ ≫ f) y _ ((LB.LinComb L φ ε').g (J PUnit.unit) (J' PUnit.unit)) =
        (gm (𝟙 _ ≫ f) y _ ((LB.LinComb L φ ε).g (J PUnit.unit) (J' PUnit.unit)))⁻¹ := by
      refine (gm_linComb L φ ε' (𝟙 _ ≫ f) y _ _ h₁ h₂).trans (Eq.trans ?_
        (congrArg (·⁻¹) (gm_linComb L φ ε (𝟙 _ ≫ f) y _ _ h₁ h₂)).symm)
      simp only [hε, zpow_neg, Finset.prod_inv_distrib]
    exact ((gm_res _ y _ hy _).trans ((map_inv _ _).trans ((congrArg (·⁻¹) (gm_gen_pull hu (𝟙 _) y h₁ h₂)).trans
      (mul_inv _ _)))).trans ((map_mul _ _ _).trans (congrArg₂ (· * ·)
        ((gm_pull_g (LB.LinComb L φ ε') f (𝟙 _) y J J' hy.1 hy.2).trans e)
        ((gm_res _ y _ hy _).trans (map_inv _ _)))).symm
  · have := (hχ J).inv
    rwa [neg_neg] at this

theorem sym_of_cp [IsCommMonObj G] (P : CP G) : Out.Sym G P.L.L := fun _ => by
  obtain ⟨t, ht, -⟩ := exists_gen P.L.isLB (K' := Fin 2)
    (φ' := ![(G.hom ⁻¹ᵁ ⊤).ι ≫ (GrpObj.inv : G ⟶ G).left, (G.hom ⁻¹ᵁ ⊤).ι]) (ε' := ![1, -1])
    (fun U _ h => by simp [Fin.prod_univ_two]) (LB.pullGen _ _ _ P.sym (G.hom ⁻¹ᵁ ⊤).ι)
    (LB.isGen_pullGen _ _ _ _ P.sym_gen _)
  exact ⟨⊤, trivial, t, ht⟩

end GlobalTheory.WtPoint

namespace GlobalTheory

theorem exists_point_repWt : Laws → AllSet fun {V} _ _ _ {A} {G} _ _ s => ∀ (t : Tower s) (a : t.Alg), KTriv a.B a.M.L.L → ∀ χ : s.X, ∃ c : 𝟙_ _ ⟶ a.B, ∀ e, a.RepWt c χ e := by
  intro hL V _ _ _ A G _ _ s t a hK χ
  have : IsDiscreteValuationRing V := s.cdvr.1
  obtain ⟨g, hg⟩ := AbelianDim.exists_relDim V a.B a.isAb
  obtain ⟨O, hO, hΛ, hu⟩ := GlobalTheory.T.exists_weightBundle_torusQuotientTower_algebraisation hL V A G s t a (-χ)
  obtain ⟨c, hc⟩ := _root_.GlobalTheory.PrimitiveOverValuationRing.exists_section_translate hL V
    { A := a.B, isAb := a.isAb, g := g, smoothDim := hg, L := a.M.L.L, isLB := a.M.L.isLB,
      rigid := ⟨a.M.L.rig, a.M.L.rigGen⟩, sym := WtPoint.sym_of_cp a.M, ample := a.ample, ktriv := hK } O hO hΛ
  refine ⟨c, fun e => ?_⟩
  obtain ⟨u, hu, hw⟩ := hu e
  obtain ⟨v, hv, hw'⟩ := WtPoint.exists_gen_of_iso (fun Z τ x => by
    rw [← Category.assoc, ← Category.assoc, ← Over.comp_left, ← Over.comp_left, WtBundle.act_comp])
    hO (LB.isLB_linComb a.M.L.isLB _ _) hc u hu hw
  exact WtPoint.exists_gen_neg (fun k => by fin_cases k <;> rfl) v hv hw'

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueLineGen
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PhiOperatorCompare

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.IndefiniteRowSideFullHecke.TorusPointForms GlobalTheory.IndefiniteRowSideFullHecke.TranslatedLineGenerators
open GlobalTheory.GtPointsCompare (castGen pairEquiv ptEquiv rel_iff)

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R}
variable {F : Type} [Field F] [Algebra (FractionRing R) F] {k : ℕ}

theorem hG : GlobalFnsSt := GlobalTheory.abelianSchemeLaws_all.1.globalFns

variable (D F k) in

def rigPow := GeneratorPullback.powGen D.P.L _ _ (LB.pullGen D.P.L _ _ D.rig (toUnit (TF (R := R) F)).left) k

def LineCorr {b : TF (R := R) F ⟶ D.P.A} (t : LineGen D F k b)
    (w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F b) (DegPre.lineε k))) : Prop :=
  LB.Gen.Corr D.P.L _ _ _ _ w (LB.mulGen D.P.L _ _ _ _ (LB.invGen D.P.L _ _ t.1) (rigPow D F k))

theorem phiRel_total (hB : D.TauBimult) (q : QkPt D F k)
    {w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F q.g.b) (DegPre.lineε k))} (hw : w.IsGen) (s : Fam D F k) :
    ∃ s', PhiRel D F k q w s s' :=
  (exists_phi hG q w hw hB s).imp fun _ h => (phiRel_iff hG q w hw _ _).2 h

theorem phiRel_transfer (hB : D.TauBimult) {q q' : QkPt D F k} (he : QkPt.Equiv D F q q')
    {w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F q.g.b) (DegPre.lineε k))} (hw : w.IsGen) :
    ∃ w' : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F q'.g.b) (DegPre.lineε k)), w'.IsGen ∧
      ∀ s s', PhiRel D F k q w s s' ↔ PhiRel D F k q' w' s s' := by
  obtain ⟨w', hw', h⟩ := UT.PhiProj.phiRel_of_equiv hG he hw
  refine ⟨w', hw', fun s s' => ⟨h s s', fun H => ?_⟩⟩
  obtain ⟨r, hr⟩ := phiRel_total hB q hw s
  exact ThetaTranslate.phiRel_unique hG q' hw' (h s r hr) H ▸ hr

theorem weilQkIs_of_equiv (hB : D.TauBimult) {p p' q q' : QkPt D F k} (h : QkPt.Equiv D F p q)
    (h' : QkPt.Equiv D F p' q') {ζ : F} (H : WeilQkIs D F k p p' ζ) : WeilQkIs D F k q q' ζ := by
  intro w w' hw hw' s s₁ s₂ s₃ s₄ h₁ h₂ h₃ h₄
  obtain ⟨v, hv, e⟩ := phiRel_transfer hB (TorusExt.equiv_symm hB h) hw
  obtain ⟨v', hv', e'⟩ := phiRel_transfer hB (TorusExt.equiv_symm hB h') hw'
  exact H v v' hv hv' s s₁ s₂ s₃ s₄ ((e' _ _).1 h₁) ((e _ _).1 h₂) ((e _ _).1 h₃) ((e' _ _).1 h₄)

variable {P : PolAV (Spec (CommRingCat.of (FractionRing R)))} {E : SecA F P k → Fam D F k → Prop}

section Unif

variable {I : Ideal R} {Dd : DegData R I} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
  (U : Unif I Dd P G)

end Unif

end GlobalTheory.PhiOperatorCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TwistedPrincipalPolarisationSectionsBaseChangeStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedPrincipalPolarisation_sections_baseChange : DVR.TwistBaseChangeStatement := by
  first | exact @GlobalTheory.twistBaseChange | exact GlobalTheory.twistBaseChange | (intros; apply GlobalTheory.twistBaseChange <;> assumption)
end

