import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SimilitudesCorrespond
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0239
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionOfIntro
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsOkPins
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsColumnInputAssembled
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0505
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0267
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0402

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CardLiesOverEqIndex
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.IndefiniteRowSideFullHecke.RelativeGroupHatForm (IsOver PullsBack lowerCoeff levelMapF endF relGroup trivAt)

namespace GlobalTheory.ShFam.Pad

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l l₂ : Level H}

def CxPt (Xo : Moduli Dw l) (c : Coeff l) : Type :=
  {y : Sp ℂ ⟶ Xo.XF c // y ≫ pullback.snd _ _ = spMap c.F.val.toRingHom}

def LiesOver (h : l.Dvd l₂) {Xo : Moduli Dw l} {c : Coeff l} {Xo₂ : Moduli Dw l₂} {c₂ : Coeff l₂}
    (y₂ : CxPt Xo₂ c₂) (y : CxPt Xo c) : Prop :=
  ∃ π : Xo₂.X ⟶ Xo.X, IsOver h Xo Xo₂ π ∧ PullsBack Xo Xo₂ π ∧
    y₂.1 ≫ pullback.fst _ _ ≫ π = y.1 ≫ pullback.fst _ _

open Classical in

def levDeg (h : l.Dvd l₂) (Xo : Moduli Dw l) (c : Coeff l) (Xo₂ : Moduli Dw l₂) (c₂ : Coeff l₂) : ℕ :=
  if k : ∃ n, 0 < n ∧ ∀ y : CxPt Xo c, Nat.card {y₂ : CxPt Xo₂ c₂ // LiesOver h y₂ y} = n then Nat.find k else 1

theorem levDeg_pos (h : l.Dvd l₂) (Xo : Moduli Dw l) (c : Coeff l) (Xo₂ : Moduli Dw l₂) (c₂ : Coeff l₂) :
    0 < levDeg h Xo c Xo₂ c₂ := by
  classical
  unfold levDeg
  split_ifs with k
  · exact (Nat.find_spec k).1
  · exact one_pos

theorem card_lifts_pos {k : Type} [Field k] [IsAlgClosed k] {X Y : Scheme.{0}} (π : X ⟶ Y) [IsFinite π] [Surjective π]
    (y : Sp k ⟶ Y) : 0 < Nat.card {x : Sp k ⟶ X // x ≫ π = y} := by
  have hne : Nonempty {x : Sp k ⟶ X // x ≫ π = y} := by
    have : CompactSpace ↥(pullback π y) := QuasiCompact.compactSpace_of_compactSpace (pullback.snd π y)
    obtain ⟨p, -⟩ := (pullback.snd π y).surjective (default : PrimeSpectrum k)
    obtain ⟨q, -, hq⟩ := isClosed_univ.exists_closed_singleton (X := ↥(pullback π y)) ⟨p, trivial⟩
    refine ⟨pointOfClosedPoint (pullback.snd π y) q hq ≫ pullback.fst π y, ?_⟩
    rw [Category.assoc, pullback.condition, ← Category.assoc, pointOfClosedPoint_comp, Category.id_comp]
  have hfin : Finite {x : Sp k ⟶ X // x ≫ π = y} := by
    have hf := (pullback.snd π y).finite_preimage_singleton (IsLocalRing.closedPoint k)
    have := hf.to_subtype
    let s : {x : Sp k ⟶ X // x ≫ π = y} → (Sp k ⟶ pullback π y) := fun x =>
      pullback.lift x.1 (𝟙 _) (x.2.trans (Category.id_comp _).symm)
    refine Finite.of_injective (β := (pullback.snd π y) ⁻¹' {IsLocalRing.closedPoint k})
      (fun x => ⟨s x (IsLocalRing.closedPoint k), Subsingleton.elim (α := PrimeSpectrum k) _ _⟩) fun a b e => ?_
    have e' : s a = s b := ext_of_apply_closedPoint_eq (pullback.snd π y) (pullback.lift_snd _ _ _)
      (pullback.lift_snd _ _ _) (congrArg Subtype.val e)
    exact Subtype.ext ((pullback.lift_fst _ _ _).symm.trans ((congrArg (· ≫ pullback.fst π y) e').trans
      (pullback.lift_fst _ _ _)))
  exact Nat.card_pos

theorem card_liesOver_eq_index (hpq : 1 ≤ Dw.p + Dw.q) (h : l.Dvd l₂) {Xo : Moduli Dw l} {c : Coeff l}
    (Xo₂ : Moduli Dw l₂) (c₂ : Coeff l₂) (y : CxPt Xo c) :
    0 < Nat.card {y₂ : CxPt Xo₂ c₂ // LiesOver h y₂ y} ∧
      Nat.card {y₂ : CxPt Xo₂ c₂ // LiesOver h y₂ y} = ((trivAt Dw l₂).subgroupOf (relGroup Dw l l₂)).index := by
  obtain ⟨π, hπ, hpb, huniq, ρ, hρ, hone, hmul, -, hρπ, hcov⟩ :=
    (GlobalTheory.LevelCompare.levelMaps_iff hpq).1 (GlobalTheory.moduliScheme_levelMaps_heckePoints.2 E H Dw hpq).1 l l₂ h Xo Xo₂
  obtain ⟨k₁, -, k₃, k₄⟩ := hcov c₂
  have w : (y.1 ≫ pullback.fst _ _) ≫ Xo.s =
      spMap c₂.F.val.toRingHom ≫ spMap (IntermediateField.inclusion (lowerCoeff h c₂).le).toRingHom := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, y.2, ← Spec.map_comp, ← Spec.map_comp]
    rfl
  let y' : Sp ℂ ⟶ Xo.XF (lowerCoeff h c₂) := pullback.lift _ _ w
  have hf : levelMapF h hπ c₂ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ π := pullback.lift_fst _ _ _
  have hs := GlobalTheory.LevelCompare.levelMapF_snd h hπ c₂
  let e : {y₂ : CxPt Xo₂ c₂ // LiesOver h y₂ y} ≃ {x : Sp ℂ ⟶ Xo₂.XF c₂ // x ≫ levelMapF h hπ c₂ = y'} :=
    { toFun := fun a => ⟨a.1.1, by
        obtain ⟨π', a₁, a₂, a₃⟩ := a.2
        obtain rfl := huniq π' a₁ a₂
        refine pullback.hom_ext ?_ ?_
        · rw [Category.assoc, hf, a₃]; exact (pullback.lift_fst _ _ _).symm
        · rw [Category.assoc, hs]; exact a.1.2.trans (pullback.lift_snd _ _ _).symm⟩
      invFun := fun x => ⟨⟨x.1, (congrArg (x.1 ≫ ·) hs.symm).trans ((Category.assoc _ _ _).symm.trans
          ((congrArg (· ≫ pullback.snd _ _) x.2).trans (pullback.lift_snd _ _ _)))⟩, π, hπ, hpb, by
        change x.1 ≫ _ = _
        rw [← hf, ← Category.assoc, x.2]; exact pullback.lift_fst _ _ _⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hpos := card_lifts_pos (levelMapF h hπ c₂) y'
  rw [Nat.card_congr e]
  refine ⟨hpos, ?_⟩
  obtain ⟨⟨x, hx⟩⟩ := (Nat.card_pos_iff.1 hpos).1
  have hF : ∀ g, endF (ρ g).hom (hρ g) c₂ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ (ρ g).hom := fun g =>
    pullback.lift_fst _ _ _
  have hS : ∀ g, endF (ρ g).hom (hρ g) c₂ ≫ pullback.snd _ _ = pullback.snd _ _ := fun g => pullback.lift_snd _ _ _
  have hm : ∀ g g', endF (ρ (g * g')).hom (hρ _) c₂ = endF (ρ g).hom (hρ g) c₂ ≫ endF (ρ g').hom (hρ g') c₂ :=
    fun g g' => pullback.hom_ext (by rw [hF, Category.assoc, hF, ← Category.assoc, hF, hmul, Category.assoc]; rfl)
      (by rw [hS, Category.assoc, hS, hS])
  have h1 : endF (ρ 1).hom (hρ _) c₂ = 𝟙 _ :=
    pullback.hom_ext (by rw [hF, hone, Category.id_comp]; exact Category.comp_id _) (by rw [hS, Category.id_comp])
  let f : relGroup Dw l l₂ → {x : Sp ℂ ⟶ Xo₂.XF c₂ // x ≫ levelMapF h hπ c₂ = y'} := fun g =>
    ⟨x ≫ endF (ρ g).hom (hρ g) c₂, by
      rw [← hx, Category.assoc]
      congr 1
      refine pullback.hom_ext ?_ ?_
      · rw [Category.assoc, hf, ← Category.assoc, hF, Category.assoc, hρπ]
      · rw [Category.assoc, hs]; exact hS g⟩
  have hsurj : Function.Surjective f := fun a => by
    obtain ⟨g, hg⟩ := (k₄ ℂ x).1 a.1 (a.2.trans hx.symm)
    exact ⟨g, Subtype.ext hg⟩
  have hker : Setoid.ker f = QuotientGroup.rightRel ((trivAt Dw l₂).subgroupOf (relGroup Dw l l₂)) := by
    ext g g'
    rw [QuotientGroup.rightRel_apply, Subgroup.mem_subgroupOf, ← (k₄ ℂ x).2, Setoid.ker_def, Subtype.ext_iff, hm]
    change x ≫ _ = x ≫ _ ↔ _
    constructor
    · intro a
      rw [← Category.assoc, ← a, Category.assoc, ← hm, mul_inv_cancel, h1, Category.comp_id]
    · intro a
      have := congrArg (· ≫ endF (ρ g).hom (hρ g) c₂) a
      simp only [Category.assoc] at this
      rw [← hm, inv_mul_cancel, h1, Category.comp_id] at this
      exact this.symm
  rw [← Nat.card_congr (Setoid.quotientKerEquivOfSurjective f hsurj), hker,
    Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel _)]
  rfl

theorem card_liesOver (hpq : 1 ≤ Dw.p + Dw.q) (h : l.Dvd l₂) {Xo : Moduli Dw l} {c : Coeff l}
    (Xo₂ : Moduli Dw l₂) (c₂ : Coeff l₂) (y : CxPt Xo c) :
    Nat.card {y₂ : CxPt Xo₂ c₂ // LiesOver h y₂ y} = levDeg h Xo c Xo₂ c₂ := by
  classical
  have k : ∃ n, 0 < n ∧ ∀ y : CxPt Xo c, Nat.card {y₂ : CxPt Xo₂ c₂ // LiesOver h y₂ y} = n :=
    ⟨_, (card_liesOver_eq_index hpq h Xo₂ c₂ y).1, fun y' =>
      (card_liesOver_eq_index hpq h Xo₂ c₂ y').2.trans (card_liesOver_eq_index hpq h Xo₂ c₂ y).2.symm⟩
  rw [levDeg, dif_pos k]
  exact (Nat.find_spec k).2 y

end GlobalTheory.ShFam.Pad
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotConditionOfFalse
section
noncomputable section

namespace GlobalTheory.Mem.Top.Bl.Model

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top.GroupRetwisting NumberField IsDedekindDomain

theorem exists_preX {K : Ctx} {P : Pre} (hO : K.Over P) (X₀ : PreX P) (Q : PiBar P.host) :
    ∃ X : PreX P, InEx.Oriented X Q ∧ ∀ u, P.cOf u * (X.piT u : P.host.E) = (X.piT P.u₀ : P.host.E) := by
  obtain ⟨X, hX⟩ := InEx.exists_oriented X₀ Q
  obtain ⟨sp, hT, hY, hA, hV, hz, rfl, -⟩ := hO
  exact ⟨{ X with
    piT := K.Lv.piT
    piT_K := K.Lv.piT_K
    piT_norm := K.Lv.piT_norm
    piT_cong := fun u => Ideal.mem_span_singleton.1 (K.Lv.piT_cong u) }, hX, fun u => div_mul_cancel₀ _ (K.Lv.piT_ne u)⟩

theorem step_colW (h2b : StandardLattice.SiegelMassRatioCM) : Step KPx (fun _ _ _ _ => True) fun _ B f T => Nonempty (ColW B f T) := by
  refine EvG.imp (evG_of_ev (ev_preX_frame h2b)) fun K _ _ _ _ hfr => (InEx.lg_colIn K).imp ?_
  rintro B f T hO h ⟨⟨δ, hδ⟩, hp⟩ - -
  obtain ⟨X₀⟩ := (hfr _ hO).1
  obtain ⟨X, hX, hc⟩ := exists_preX hO X₀ f.P
  obtain ⟨sel, hsel⟩ := Formalism.L2.Col.exists_sel B.fields
  obtain ⟨J, hJ⟩ := exists_ambIn_ok B.host
  obtain ⟨I, a1, a2, a3, a4, -⟩ := h.1 X hX sel hsel J hJ
  exact ⟨⟨X, I, a1, a2, a3, a4, ⟨hp, hc⟩, TrueColsTest.laws a1, TrueColsTest.law0 a1 _, δ, hδ, h.2.2, h.2.1⟩⟩

theorem prePin_coordPre (P : PreCh) (L : LevCh P) : PrePin (GlobalTheory.StdFrameObj.coordPre P L) :=
  fun a b h => PinsCoord.extTo_basis _ _ a b h

theorem ksCond (hR : GlobalTheory.NT.RayField) (hP : GlobalTheory.Published.PrincipalIdealSt) (hA : GlobalTheory.Published.CMCurveGoodOutsidePrimeSt) :
    V4.KsCond fun B f => ∃ δ : Fld.FieldDat B.toPre, B.KsExact δ f := by
  refine ⟨InEx.ev_of_forall fun K B₀ f₀ S₁ S₂ hO s1 s2 => ?_, fun B B' f f' e hf hS => ?_⟩
  · obtain ⟨δ⟩ := Fld.nonempty_fieldDat hR hA B₀.toPre
    obtain ⟨B₁, e₁, k⟩ := (GlobalTheory.T.rayField_le_and_exists_base hR hP _ f₀ δ).2
    obtain ⟨B₂, e₂, k₂, l₂⟩ := Inh.exists_fixed B₁ (S₁ B₁.KsC) (s1 _)
    obtain ⟨B, e, l₃⟩ := BaseEnl.exists_enl B₂ (S₂ B₁.KsC B₂.fixedCoefficientFieldInComplex) (s2 _ _)
    have hk : B.KsC = B₁.KsC := e.KsC_eq.trans k₂
    have e' : B.toPre = B₀.toPre := e.1.trans (e₂.trans e₁)
    have hH : Has₂ B (S₁ B.KsC) (S₂ B.KsC B.fixedCoefficientFieldInComplex) := by
      rw [hk, Has₂, e.fixedCoefficientField_eq]
      exact ⟨l₂, l₃⟩
    rw [← hk] at k
    clear e e₁ e₂ hO
    generalize B₀.toPre = P₀ at *
    subst e'
    exact ⟨B, f₀, rfl, HEq.rfl, ⟨δ, k⟩, hH⟩
  · have e' := e.1
    unfold Base.KsExact at hS ⊢
    rw [e.KsC_eq]
    clear e
    generalize B.KsC = F at *
    generalize B.toPre = P at *
    subst e'
    obtain rfl := eq_of_heq hf
    exact hS

theorem baseCond_KPx (h2b : StandardLattice.SiegelMassRatioCM) (hR : GlobalTheory.NT.RayField) (hP : GlobalTheory.Published.PrincipalIdealSt)
    (hA : GlobalTheory.Published.CMCurveGoodOutsidePrimeSt) : BaseCond KPx :=
  baseCond_of (PP := fun P _ => PrePin P) (ksCond hR hP hA)
    (EvG.imp (evG_of_ev (ev_preX_frame h2b)) fun K _ _ _ _ hfr => by
      have hO : K.Over (GlobalTheory.StdFrameObj.coordPre K.P K.Lv) :=
        ⟨_, _, _, _, _, _, rfl, GlobalTheory.StdFrameObj.diagSpaces_coordPre K.P K.Lv⟩
      obtain ⟨f⟩ := (hfr _ hO).2
      exact ⟨_, f, hO, prePin_coordPre _ _⟩)

theorem not_step_false (hH : DC.HostExQ) (hLP : LevelPrime) (h2b : StandardLattice.SiegelMassRatioCM) {KP : BaseP} (hK : BaseCond KP) :
    ¬ Step KP (fun _ _ _ _ => True) fun _ _ _ _ => False := fun h =>
  not_exTrueG_false hH hLP h2b hK (exTrueG_iff_step.2 (h.trans (Step.of_all fun _ _ _ _ _ _ _ a => a.elim)))

theorem exists_colW (hH : DC.HostExQ) (hLP : LevelPrime) (h2b : StandardLattice.SiegelMassRatioCM) (hR : GlobalTheory.NT.RayField)
    (hP : GlobalTheory.Published.PrincipalIdealSt) (hA : GlobalTheory.Published.CMCurveGoodOutsidePrimeSt) :
    ∃ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B), K.Over B.toPre ∧ KPx B f ∧ Forced K B T ∧ Nonempty (ColW B f T) := by
  by_contra h
  refine not_step_false hH hLP h2b (baseCond_KPx h2b hR hP hA) ((step_colW h2b).trans (Step.of_all ?_))
  exact fun K B f T a b c d => h ⟨K, B, f, T, a, b, c, d⟩

theorem not_stepW_false (hH : DC.HostExQ) (hLP : LevelPrime) (h2b : StandardLattice.SiegelMassRatioCM) (hR : GlobalTheory.NT.RayField)
    (hP : GlobalTheory.Published.PrincipalIdealSt) (hA : GlobalTheory.Published.CMCurveGoodOutsidePrimeSt) :
    ¬ StepW (fun _ _ _ _ _ => True) fun _ _ _ _ _ => False := fun h =>
  not_step_false hH hLP h2b (baseCond_KPx h2b hR hP hA)
    (((step_colW h2b).and h).trans (Step.of_all fun _ _ _ _ _ _ _ H => H.1.elim fun w => H.2 w trivial))

theorem ColW.kpx {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T) : KPx B f := ⟨⟨w.δ, w.exact⟩, w.pins.iX⟩

theorem not_corePropertyOf_false (K : Ctx) (X : Stages) (f : Fr X.B.toPre) (T : TwDat X.B) (c : V4.Core K X f T) :
    ¬ positionOf (fun _ _ _ _ _ _ _ => False) K X f T c := fun ⟨_, _, _, h, _⟩ => h

theorem positionOf_cols {P : CP} {K : Ctx} {X : Stages} {f : Fr X.B.toPre} {T : TwDat X.B} {c : V4.Core K X f T}
    (h : positionOf P K X f T c) : ∃ w : ColW X.B f T, X.C = w.C :=
  let ⟨w, _, _, _, e⟩ := h; ⟨w, congrArg Sigma.fst e⟩

theorem exists_later {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} (hO : K.Over B.toPre) (w : ColW B f T) (G : GJStage B w.C) :
    ∃ Z : w.Lt, Z.G = G :=
  let ⟨Z⟩ := TrueColsTest.later w.l (JetEx.hasLetters_of_over hO); ⟨⟨Z.W, Z.V, Z.S, Z.N, G⟩, rfl⟩

theorem GIs.exists_colT {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} (hO : K.Over B.toPre) {w : ColW B f T}
    {G : GJStage B w.C} (h : GIs K w G) : ∃ Z : w.Lt, Z.G = G ∧ Formalism.L2.Theta.VolTieG (w.D Z) ∧ Nonempty (ColT w Z) := by
  obtain ⟨⟨W, V, S, N, G'⟩, rfl⟩ := exists_later hO w G
  exact ⟨_, rfl, (h W V S N).1, (h W V S N).2.2⟩

theorem GIs.not_double {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} (hO : K.Over B.toPre) {w : ColW B f T}
    {G : GJStage B w.C} (h : GIs K w G) (X : @HSpace B.host.E _ _ B.host.cmStar) (hX : letI := B.host.cmStar; X.SigOK) :
    ¬ GIs K w { G with vol := fun Y => 2 * G.vol Y, vol_pos := fun Y => mul_pos two_pos (G.vol_pos Y) } := fun h' => by
  obtain ⟨⟨W, V, S, N, G'⟩, rfl⟩ := exists_later hO w G
  obtain ⟨⟨μ, hμ⟩, H⟩ := (h W V S N).1 X hX
  obtain ⟨⟨F, hF⟩, H1⟩ := H μ hμ
  have a := H1 F hF
  have b := (((h' W V S N).1 X hX).2 μ hμ).2 F hF
  have c : ENNReal.ofReal (G'.vol X) = ENNReal.ofReal (2 * G'.vol X) := a.symm.trans b
  have p := G'.vol_pos X
  rw [ENNReal.ofReal_eq_ofReal_iff p.le (by positivity)] at c
  linarith

end GlobalTheory.Mem.Top.Bl.Model

end
end

