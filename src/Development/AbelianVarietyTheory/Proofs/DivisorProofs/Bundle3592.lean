import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0075
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdlAlongEqSpanMonomial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2377
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2971
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2831
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3584
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1765
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1777
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1815
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0261
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1854
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2258
import Development.AutomorphicArithmetic.DivisorFrames.ExistsGeoOfSignatureRankBounds
import Development.AutomorphicArithmetic.DivisorFrames.Bundle0018
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
import Development.AbelianVarietyTheory.Definitions.Divisors.LamRange
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3013
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2993
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3558
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3564
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3562
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3585
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3439
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3452
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0226
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3583
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3512
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3493
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3502
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3497
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0046
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1305
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1359
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1200
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1234
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2222
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1309
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3278
import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsArBaseAway
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExtNormalisedBlowup
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TChart

theorem Taut.exists_ext_normBl : ∀ g : ℕ, 1 ≤ g → ∀ φ : InvFun ℤ, IsPolFan id g φ → NoSelfInt id g φ → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) (OZ : LB Z) (d : ℕ) (S : Scheme.{0}) (π : S ⟶ Z) (j : F.X ⟶ S) [IsOpenImmersion j] (BD : GlobalTheory.EffCartierData S), MinAt5 F z i OZ → BlowAt F z i φ d π j BD → ∀ (C : Taut (zetaAway n) g n φ) (G₁ : Over (Sp C.R)) [GrpObj G₁] (y : Sp (FractionRing C.R) ⟶ F.X) (α₁ : pullback G₁.hom (jK C.R) ⟶ F.univ.A.left), C.IsFam F G₁ y α₁ → ∃ ξ : Sp C.R ⟶ S, y ≫ j = jK C.R ≫ ξ := by
  intro g _ φ hφ _ n hn _ F Z z i OZ d S π j _ BD hM hB C G₁ _ y α₁ hC
  obtain ⟨hsa, hab, hgen, hmum, hy⟩ := hC
  obtain ⟨J, -, -, hval, hbl, -, -, hji, hpre, -, -⟩ := hB
  obtain ⟨hreg, hchar, -, -, hpar, -⟩ := Taut.isRegularLocalRing_and_isRelParam g n φ hn C
  obtain ⟨hmono, hrk, hcone, hdef, ht⟩ := Taut.monomial_chart g n φ (by omega) C
  haveI : IsOpenImmersion i := hM.isThetaCompact.1.2.2.1
  haveI : IsCommMonObj G₁ := hsa.comm
  haveI : IsNoetherianRing C.R := C.compl.1
  haveI : IsIntegrallyClosed C.R := hmum.1.2.1
  obtain ⟨a, ha⟩ := GlobalTheory.MinExt.exists_ext_of_minAt5 g n F Z z i OZ hM C.R G₁ hsa y α₁ hgen C.b hy
  have hon : IsPolFanOn id φ C.Q.X := hφ C.Q.X hrk
  have he : ∀ k, ∃ e : ℕ, (e : ℝ) = d * φ.evalZ ((n : ℤ) • C.δ k) := by
    intro k
    have hmem : (n : ℤ) • C.δ k ∈ balForms (id : ℤ → ℤ) C.Q.X := Submodule.smul_mem _ _ (hcone.mem k)
    have hnn : ∀ w, 0 ≤ ((n : ℤ) • C.δ k) w w := fun w => by
      simpa using mul_nonneg (Int.natCast_nonneg n) (hcone.nonneg k w)
    obtain ⟨c, hc⟩ := hon.integral _ hmem hnn
    have hc0 : 0 ≤ c := by
      have hne : (n : ℤ) • C.δ k ≠ 0 := by
        refine fun h => hcone.basis.linearIndependent.ne_zero k (Subtype.ext ?_)
        exact (smul_eq_zero.1 h).resolve_left (by omega)
      have := hon.pos _ hmem hnn hne
      rw [hc] at this
      exact_mod_cast this.le
    lift c to ℕ using hc0
    exact ⟨d * c, by rw [hc]; push_cast; rfl⟩
  choose e he using he
  have hJ := GlobalTheory.ChartIdeal.idlAlong_eq_span_monomial g n F Z i φ hφ d J hval C.R C.compl.2.1 C.b a C.Q G₁ y α₁ hsa hgen ha
    hmum C.m C.t C.δ e hpar hab hcone hdef hmono he
  obtain ⟨ξ, hξ, -⟩ := GlobalTheory.NormBlLift.lift_normBl g n F Z S i π j J hbl hji hpre C.R a y ha _
    (Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (ht k)) hJ
  refine ⟨ξ, ?_⟩
  have hπ : (jK C.R ≫ ξ) ≫ π = y ≫ i := by rw [Category.assoc, hξ, ha]
  have hr : Set.range (jK C.R ≫ ξ) ⊆ Set.range j := by
    rintro _ ⟨p, rfl⟩
    rw [← hpre]
    exact ⟨y p, by rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hπ]⟩
  have hl := IsOpenImmersion.lift_fac j (jK C.R ≫ ξ) hr
  have : IsOpenImmersion.lift j (jK C.R ≫ ξ) hr = y := by
    rw [← cancel_mono i, ← hπ, ← hji, ← Category.assoc, hl]
  rw [← this, hl]

end GlobalTheory.TChart
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFramesForTriangleStage
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_frames_for_triangle_stage : GlobalTheory.FunPr.Hypotheses₂ →
  GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil), IsStdChar D W.ψ (-1) → ∀ (i j : Fin D.R.m) (p q : ℕ) (A A' WW : HSp D)
    (X : Tri T A A' WW) (lam : T → ℂ) (t : T) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E), GlobalTheory.SqTower.IsStageC W i j p q X →
      Factor X W.ψ W.θ lam → GlobalTheory.SqStepBig.Fit G W i j t μ₀ Bs A.rank A'.rank →
      ∃ (FA : GlobalTheory.ChainFr.Fr A) (FA' : GlobalTheory.ChainFr.Fr A') (FW : GlobalTheory.ChainFr.Fr WW) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig A.rank A'.rank),
        GlobalTheory.SqStepBig.Over X Γ ∧ Γ.p = p ∧ Γ.q = q ∧ Γ.IsGood Bs ∧
        ∀ s, (s = t ∨ s = μ₀) → GlobalTheory.SqStepBig.Carried G W i j X Bs FA FA' FW Γ s := by
  intro _
  refine GlobalTheory.SqStepBig.gbig_two GlobalTheory.T.towerStage_seesawDictionary_framesSignatures GlobalTheory.T.towerStage_seesawDictionary_framesSignatures ?_
  intro D T Lc sc G μ₀ C x b q1 _ W _ i j p q A A' WW X lam t Bs hX _ hB
  obtain ⟨FA, FA', FW, a, b, -, -, -, hd⟩ := q1 W i j p q A A' WW X hX
  obtain ⟨hp, hq, hrA, hrA', hnA, hnA', hnW, hXi⟩ := hX
  obtain ⟨⟨hψ, -⟩, hBs, hemb, -, -, hκ⟩ := hB
  have hsz := GlobalTheory.StageDict.stage_sizes i j hp hq hrA hrA'
  obtain ⟨Γ, hp', hq', hg, hS⟩ := UpperTheory.exists_geo_of_signature_rank_bounds D W.ψ T A A' WW X FA FA' FW hXi.rank Bs p q hBs hψ hemb hXi.rigA hXi.rigA' hXi.rigW
    hXi.meas hXi.meas' hnA hnA' hnW hsz.1 hsz.2.1 hsz.2.2.1 hκ
  refine ⟨FA, FA', FW, Γ, ⟨⟨rfl, hS.JA, hS.latA.1⟩, ⟨rfl, hS.JB, hS.latB.1⟩, ⟨hXi.rank.symm, hS.pairA.JW, hS.latA.2⟩⟩,
    hp', hq', hg, fun s _ => ?_⟩
  obtain ⟨-, -, f1, f2, k1, k2⟩ := hd s
  refine ⟨f1, f2, k1, k2, fun om om' hT => ?_⟩
  obtain ⟨cA, cB, hO, -⟩ := UpperTheory.exists_seesaw_intertwiners_of_triple D W.ψ W.θ hXi.isVac.2.inf T A A' WW X FA FA' FW hXi.rank Bs Γ hS
    (GlobalTheory.SqStep.chs G i j s) om om' hT (X.ω s) (X.ω' s) (hXi.weil s) (hXi.weil' s)
  exact ⟨_, cA, cB, hO⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaloisTowerBaseChangeThetaMember
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.GSep

theorem exists_ringHom_val_of_regAt' : ∀ (X₂ : GSet) (z : X₂.M.Z) {V : Type} [CommRing V] [IsDomain V] (ev : X₂.M.Z.presheaf.stalk z →+* V), RegAt X₂ z ev → ∃ yK : X₂.S.R →+* FractionRing V, ∀ a : X₂.S.R, yK a = X₂.M.val (jK V ≫ spMap ev ≫ X₂.M.Z.fromSpecStalk z) a := by
  intro X₂ z V _ _ ev hr
  have hR : X₂.S.R ≤ X₂.M.O ((jK V ≫ spMap ev ≫ X₂.M.Z.fromSpecStalk z) (IsLocalRing.closedPoint (FractionRing V))) :=
    fun a ha => hr a ha
  exact ⟨(RatModel.valHomOf (jK V ≫ spMap ev ≫ X₂.M.Z.fromSpecStalk z) _
    (RatModel.specializes_of_range_eq (RatModel.range_eq_singleton (M := X₂.M) (jK V ≫ spMap ev ≫ X₂.M.Z.fromSpecStalk z) (IsLocalRing.closedPoint (FractionRing V))))).comp
      (Subalgebra.inclusion hR).toRingHom, fun a => rfl⟩

theorem Tower.comp_act₂_of_comp_act' : ∀ {I : Type} {X₁ : GSet} {act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)} (𝔗 : Tower X₁ act) {K : Type} [Field K] (A' : Over (Sp K)) (y₂ : 𝔗.X₂.S.R →+* K) (φ₂ : A'.left ⟶ 𝔗.X₂.ρ.P.A.left), φ₂ ≫ 𝔗.X₂.ρ.P.A.hom = A'.hom ≫ spMap y₂ → ∀ (e : A' ⟶ A') (a : I), e.left ≫ φ₂ ≫ 𝔗.φ = φ₂ ≫ 𝔗.φ ≫ (act a).left → e.left ≫ φ₂ = φ₂ ≫ (𝔗.act₂ a).left := by
  intro I X₁ act 𝔗 K _ A' y₂ φ₂ hφ e a h
  refine 𝔗.cart.1.hom_ext ?_ ?_
  · simp only [Category.assoc, 𝔗.act_eq a]
    simpa only [Category.assoc] using h
  · simp only [Category.assoc, Over.w (𝔗.act₂ a), hφ]
    rw [← Category.assoc, Over.w e]

theorem Tower.pt_iff_pt_gl' : ∀ {I : Type} {X₁ : GSet} {act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)} (𝔗 : Tower X₁ act) {K : Type} [Field K] (A' : Over (Sp K)) [GrpObj A'] (ya yb : 𝔗.X₂.S.R →+* K) (φa φb : A'.left ⟶ 𝔗.X₂.ρ.P.A.left) (σ : 𝔗.X₂.Ω₁ ≃ₐ[X₁.Ω₁] 𝔗.X₂.Ω₁), IsGrpPullback A' 𝔗.X₂.ρ.P.A (spMap ya) φa → IsGrpPullback A' 𝔗.X₂.ρ.P.A (spMap yb) φb → φa ≫ 𝔗.φ = φb ≫ 𝔗.φ → ya = yb.comp (𝔗.sR σ) → ∀ {L : Type} [Field L] (j : K →+* L) (x : Sp L ⟶ A'.left), x ≫ A'.hom = spMap j → ∀ a, (x ≫ φa = spMap (j.comp ya) ≫ (𝔗.X₂.ρ.pt a).left ↔ x ≫ φb = spMap (j.comp yb) ≫ (𝔗.X₂.ρ.pt (𝔗.gl σ a)).left) := by
  intro I X₁ act 𝔗 K _ A' _ ya yb φa φb σ ha hb hab hy L _ j x hx a
  have hc := 𝔗.cart.1
  have hsec : ∀ b, (𝔗.X₂.ρ.pt b).left ≫ 𝔗.X₂.ρ.P.A.hom = 𝟙 _ := fun b => Over.w (𝔗.X₂.ρ.pt b)
  have hsp : ∀ y : 𝔗.X₂.S.R →+* K, spMap j ≫ spMap y = spMap (j.comp y) := fun y => by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have hxa : (x ≫ φa) ≫ 𝔗.X₂.ρ.P.A.hom = spMap (j.comp ya) := by
    rw [Category.assoc, ha.1.w, ← Category.assoc, hx, hsp]
  have hxb : (x ≫ φb) ≫ 𝔗.X₂.ρ.P.A.hom = spMap (j.comp yb) := by
    rw [Category.assoc, hb.1.w, ← Category.assoc, hx, hsp]
  have hra : (spMap (j.comp ya) ≫ (𝔗.X₂.ρ.pt a).left) ≫ 𝔗.X₂.ρ.P.A.hom = spMap (j.comp ya) := by
    rw [Category.assoc, hsec]
    exact Category.comp_id _
  have hrb : (spMap (j.comp yb) ≫ (𝔗.X₂.ρ.pt (𝔗.gl σ a)).left) ≫ 𝔗.X₂.ρ.P.A.hom = spMap (j.comp yb) := by
    rw [Category.assoc, hsec]
    exact Category.comp_id _
  have hg : spMap (j.comp yb) ≫ (𝔗.X₂.ρ.pt (𝔗.gl σ a)).left ≫ 𝔗.φ = spMap (j.comp ya) ≫ (𝔗.X₂.ρ.pt a).left ≫ 𝔗.φ := by
    rw [𝔗.gl_pt, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, RingHom.comp_assoc, ← hy]
  constructor
  · intro h1
    refine hc.hom_ext ?_ (hxb.trans hrb.symm)
    rw [Category.assoc, ← hab, ← Category.assoc, h1, Category.assoc, Category.assoc, hg]
  · intro h1
    refine hc.hom_ext ?_ (hxa.trans hra.symm)
    rw [Category.assoc, hab, ← Category.assoc, h1, Category.assoc, Category.assoc, hg]

theorem exists_baseChange_gMem_of_tower : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), GlobalTheory.GSep.IsAct X₁ act → ∀ (𝔗 : GlobalTheory.GSep.Tower X₁ act) (z₂ : 𝔗.X₂.M.Z), 𝔗.p z₂ = z₁ → ∀ x₀ : X₁.S.Gam, X₁.M.Div X₁.S.th x₀ z₁ → ∃ eps : X₁.S.Gam → ℕ, ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) (C : Type) (lab : C → X₁.S.Gam) (T : X → C → V), 𝔪.Terms x₀ lab T → ∀ (V' : Type) [CommRing V'] [IsDomain V'] [IsLocalRing V'] (io : V →+* V'), IsCN V' → Function.Injective io → io.Finite → ∃ 𝔪₂ : ∀ ev₂ : 𝔗.X₂.M.Z.presheaf.stalk z₂ →+* V', 𝔗.Ext ev io ev₂ → GlobalTheory.GSep.GMem 𝔗.X₂ z₂ 𝔗.act₂ V' ev₂ X (fun k => io (t k)) δ, (∀ ev₂ h (zt : 𝔗.X₂.M.Z.presheaf.stalk z₂), 𝔗.X₂.M.stalkHom z₂ zt = algebraMap 𝔗.X₂.o₁ 𝔗.X₂.Ω₁ 𝔗.X₂.S.ζ → (𝔪₂ ev₂ h).Terms (𝔗.lam x₀) (fun c => 𝔗.lam (lab c)) (fun mu c => ev₂ zt ^ eps (lab c) * io (T mu c))) ∧ ∀ ev₂ h ev₂' h' (σ : 𝔗.X₂.Ω₁ ≃ₐ[X₁.Ω₁] 𝔗.X₂.Ω₁), (∀ x x', 𝔗.X₂.M.stalkHom z₂ x' = σ (𝔗.X₂.M.stalkHom z₂ x) → ev₂' x = ev₂ x') → (∀ x, ∃ x', 𝔗.X₂.M.stalkHom z₂ x' = σ (𝔗.X₂.M.stalkHom z₂ x)) → ∀ a mu, (𝔪₂ ev₂' h').YY a mu ↔ (𝔪₂ ev₂ h).YY (𝔗.gl σ a) mu := by
  intro I X₁ z₁ act hact 𝔗 z₂ hz₂ x₀ hdiv
  obtain ⟨eps, heps⟩ := GlobalTheory.T.galoisTower_thetaMember_terms_baseChange X₁ act 𝔗 z₁ z₂ hz₂ x₀ hdiv
  refine ⟨eps, ?_⟩
  intro V _ _ _ ev X _ t δ 𝔪 C lab T hT V' _ _ _ io hcn hinj hfin
  have hle : nonZeroDivisors V ≤ (nonZeroDivisors V').comap io :=
    nonZeroDivisors_le_comap_nonZeroDivisors_of_injective io hinj
  let f : FractionRing V →+* FractionRing V' := IsLocalization.map (FractionRing V') io hle
  have hf : ∀ v, f (algebraMap V (FractionRing V) v) = algebraMap V' (FractionRing V') (io v) :=
    fun v => IsLocalization.map_eq hle v
  obtain ⟨D', e₈', G', _, _, A', U', ψ, hD, bc, hsemi, hψ, hw, hbc, hPU, hxe, hgen, hE, hpsi⟩ :=
    GlobalTheory.T.exists_uniformisation_baseChange_finite_injective X₁ z₁ act V ev X t δ 𝔪 V' io f hf hcn hinj hfin
  have hreg : ∀ ev₂ : 𝔗.X₂.M.Z.presheaf.stalk z₂ →+* V', 𝔗.Ext ev io ev₂ → RegAt 𝔗.X₂ z₂ ev₂ :=
    fun ev₂ h => GlobalTheory.T.thetaRing_regular_at_extension_point 𝔗 hz₂ ev io ev₂ hinj h 𝔪.reg
  choose yK hyK using fun (ev₂ : 𝔗.X₂.M.Z.presheaf.stalk z₂ →+* V') (h : 𝔗.Ext ev io ev₂) =>
    exists_ringHom_val_of_regAt' 𝔗.X₂ z₂ ev₂ (hreg ev₂ h)
  have hyKc : ∀ ev₂ h, (yK ev₂ h).comp 𝔗.om = f.comp 𝔪.yK := by
    intro ev₂ h
    ext a
    simp only [RingHom.comp_apply]
    rw [hyK, 𝔪.yK_eq]
    exact GlobalTheory.T.val_extensionPoint_eq_image_of_val 𝔗 hz₂ ev io ev₂ f hf hinj h 𝔪.reg a
  have hsq : ∀ ev₂ h, spMap (yK ev₂ h) ≫ spMap 𝔗.om = spMap f ≫ spMap 𝔪.yK := by
    intro ev₂ h
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hyKc ev₂ h]
  choose φ₂ hφ₂ using fun (ev₂ : 𝔗.X₂.M.Z.presheaf.stalk z₂ →+* V') (h : 𝔗.Ext ev io ev₂) =>
    GlobalTheory.T.isGrpPullback_paste_factorisation X₁.ρ.P.A 𝔗.X₂.ρ.P.A 𝔪.A.A A'.A (spMap 𝔗.om) (spMap 𝔪.yK) (spMap f) (spMap (yK ev₂ h)) 𝔗.φ 𝔪.φ ψ
      𝔗.cart 𝔪.cart hψ (hsq ev₂ h)
  choose wl hwl using fun (ev₂ : 𝔗.X₂.M.Z.presheaf.stalk z₂ →+* V') (h : 𝔗.Ext ev io ev₂) =>
    GlobalTheory.T.exists_lineBundleIso_pullback_commSquare A'.L 𝔪.A.L X₁.ρ.P.L 𝔗.X₂.ρ.P.L ψ 𝔪.φ (φ₂ ev₂ h) 𝔗.φ A'.isLB 𝔪.A.isLB X₁.ρ.P.isLB 𝔗.X₂.ρ.P.isLB
      (hφ₂ ev₂ h).2.symm hw ⟨𝔪.wl, 𝔪.wl_gen⟩ 𝔗.lb
  let 𝔪₂ : ∀ ev₂ : 𝔗.X₂.M.Z.presheaf.stalk z₂ →+* V', 𝔗.Ext ev io ev₂ →
      GMem 𝔗.X₂ z₂ 𝔗.act₂ V' ev₂ X (fun k => io (t k)) δ := fun ev₂ h =>
    { cn := hcn
      loc := h.1
      reg := hreg ev₂ h
      yK := yK ev₂ h
      yK_eq := hyK ev₂ h
      D := D'
      e₈ := e₈'
      G := G'
      semi := hsemi
      A := A'
      U := U'
      φ := φ₂ ev₂ h
      cart := (hφ₂ ev₂ h).1
      wl := wl ev₂ h
      wl_gen := hwl ev₂ h
      equiv := fun a => by
        obtain ⟨E, hE1, hE2⟩ := 𝔪.equiv a
        obtain ⟨E', hE'1, hE'2⟩ := hE E
        refine ⟨E', ?_, fun mu => hD.xe.injective ?_⟩
        · have e2 := (hφ₂ ev₂ h).2
          refine Tower.comp_act₂_of_comp_act' 𝔗 A'.A (yK ev₂ h) (φ₂ ev₂ h) (hφ₂ ev₂ h).1.1.w E'.aA a ?_
          calc E'.aA.left ≫ φ₂ ev₂ h ≫ 𝔗.φ = E'.aA.left ≫ ψ ≫ 𝔪.φ := by rw [e2]
            _ = ψ ≫ E.aA.left ≫ 𝔪.φ := by rw [← Category.assoc, hE'1, Category.assoc]
            _ = ψ ≫ 𝔪.φ ≫ (act a).left := by rw [hE1]
            _ = φ₂ ev₂ h ≫ 𝔗.φ ≫ (act a).left := by rw [← Category.assoc, ← e2, Category.assoc]
        · rw [hE'2, hxe, hE2, hxe]
      psi := hpsi }
  refine ⟨𝔪₂, ?_, ?_⟩
  · intro ev₂ h zt hzt
    exact heps V ev X t δ 𝔪 C lab T hT V' io f hf hinj hfin ev₂ (𝔪₂ ev₂ h) ψ hD bc h (hyKc ev₂ h) hψ hw
      (hφ₂ ev₂ h).2 hbc hPU hxe hgen zt hzt
  · intro ev₂ h ev₂' h' σ h1 h2 a mu
    have hy : yK ev₂' h' = (yK ev₂ h).comp (𝔗.sR σ) := by
      ext b
      simp only [RingHom.comp_apply]
      rw [hyK, hyK]
      exact GlobalTheory.T.val_galoisConjugate_extension_eq 𝔗 ev₂ ev₂' σ h1 h2 (hreg ev₂ h) (hreg ev₂' h') b
    unfold GMem.YY
    refine exists_congr fun p => exists_congr fun x => and_congr_right fun _ => and_congr_right fun _ => ?_
    exact Tower.pt_iff_pt_gl' 𝔗 A'.A (yK ev₂' h') (yK ev₂ h) (φ₂ ev₂' h') (φ₂ ev₂ h) σ (hφ₂ ev₂' h').1 (hφ₂ ev₂ h).1
      ((hφ₂ ev₂' h').2.trans (hφ₂ ev₂ h).2.symm) hy
      (algebraMap (FractionRing V') (AlgebraicClosure (FractionRing V'))) x.left (Over.w x) a

end GlobalTheory.GSep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsotropicSaturatedWeightFiltration
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LowFilt

open GlobalTheory.LowDat

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def twistI {D : Datum H} {R : Type} [CommRing R] [IsDomain R] {D₀ : DegPre R} (hB : D₀.TauBimult) [Module (𝓞 E) D₀.X]
    {oa : letI := H.starRing; D₀.OAct (𝓞 E)} {F : Type} [Field F] [Algebra (FractionRing R) F]
    (I : TateIsoQ D D₀ oa F) (g : ℕ → D.La ≃ₗ[𝓞 E] D.La) (hiso : ∀ n a b, D.EF (g n a) (g n b) = D.EF a b)
    (htow : ∀ n m, 0 < n → 0 < m → ∀ a, ∃ e, g (n * m) a = g n a + n • e) : TateIsoQ D D₀ oa F where
  ζ := I.ζ
  ζ_prim := I.ζ_prim
  ζ_pow := I.ζ_pow
  ev n a := I.ev n (g n a)
  add n hn a b := by rw [map_add]; exact I.add n hn _ _
  lin n hn x a := by rw [map_smul]; exact I.lin n hn x _
  ker n hn a b := (I.ker n hn _ _).trans
    ⟨fun ⟨e, he⟩ => ⟨(g n).symm e, by
        have := congrArg (g n).symm he
        rwa [LinearEquiv.symm_apply_apply, map_add, LinearEquiv.symm_apply_apply, map_nsmul] at this⟩,
     fun ⟨e, he⟩ => ⟨g n e, by rw [he, map_add, map_nsmul]⟩⟩
  onto n hn p := by
    obtain ⟨b, hb⟩ := I.onto n hn p
    exact ⟨(g n).symm b, by rw [LinearEquiv.apply_symm_apply]; exact hb⟩
  tower n m hn hm a := by
    obtain ⟨q, h₁, h₂, h₃⟩ := I.tower n m hn hm (g (n * m) a)
    exact ⟨q, h₁, h₂, GlobalTheory.TorusExt.equiv_trans hB h₃ ((I.ker n hn _ _).2 (htow n m hn hm a))⟩
  isom n hn a b := by rw [← hiso n a b]; exact I.isom n hn _ _

end GlobalTheory.LowFilt

open GlobalTheory.LowFilt GlobalTheory.LowDat in
theorem GlobalTheory.LowFilt.exists_filt : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l)
  (c : Coeff l) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ C : GlobalTheory.UChart.Fam Xo c R,
  1 ≤ Module.finrank (𝓞 E) C.P.D.toPre.X →
  ∃ Z : Submodule (𝓞 E) Dw.La, GlobalTheory.LowDat.IsIsoSat Dw Z ∧ Module.finrank (𝓞 E) Z = Module.finrank (𝓞 E) C.P.D.toPre.X ∧
    ∃ (tK : SAB H (Sp (FractionRing R))) (m1 : SABMap tK C.t (jK R)) (m2 : SABMap tK Xo.univ.t (C.y ≫ pullback.fst _ _)),
      ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F],
        ∃ I : (letI := H.starRing; TateIsoQ Dw C.P.D.toPre C.P.oD F),
          GlobalTheory.LowDat.XFLevel C tK m1 m2 F I ∧ GlobalTheory.LowDat.FiltGraded C Z F I := by
  intro E _ _ _ H Dw l Xo c R _ _ _ hR C hr
  obtain ⟨tK, ⟨m1⟩, ⟨m2⟩⟩ := C.gen
  haveI : CharZero R := hR.2
  letI := H.starRing
  have hB := C.P.D.tau_bimult
  have hT : C.P.TorsionIso := GlobalTheory.FlatTors.torsionIso_holds E H R _ hR.1 C.t C.P
  haveI : IsNoetherianRing R := hR.1.1
  let F₀ := AlgebraicClosure (FractionRing R)
  haveI : CharZero (FractionRing R) := charZero_of_injective_algebraMap (IsFractionRing.injective R _)
  haveI : CharZero F₀ := charZero_of_injective_algebraMap (algebraMap (FractionRing R) F₀).injective
  obtain ⟨I₀, hI₀⟩ := GlobalTheory.T.exists_levelIsometry_genericFibre_boundaryChart Xo c R hR C tK m1 m2 F₀
  obtain ⟨y, hy, hcois⟩ := GlobalTheory.T.tateIso_latticePart_surjective_coisotropicKernel Dw R C.P.D.toPre C.P.oD C.P.D.psi_even hB F₀ I₀
  have htow : ∀ n m, 0 < n → 0 < m → ∀ a, ∃ e, y (n * m) a = y n a + n • e := by
    intro n m hn hm a
    obtain ⟨q, h₁, -, z, h₃, -⟩ := I₀.tower n m hn hm a
    obtain ⟨e₁, he₁⟩ := hy (n * m) (Nat.mul_pos hn hm) a
    obtain ⟨e₂, he₂⟩ := hy n hn a
    have e₃ : (q.y : C.P.D.toPre.X) = (I₀.ev (n * m) a).y := h₁
    have e₄ : q.y = (I₀.ev n a).y - n • z := by rw [h₃]; abel
    refine ⟨m • e₁ - e₂ - z, ?_⟩
    rw [he₁, he₂, ← e₃, e₄]
    simp only [smul_sub, smul_smul]
    abel
  have hM : 0 < l.M' := Nat.lcm_pos (by have := l.three_le; omega) l.A_pos
  obtain ⟨Z, hZ, hZr, g, hgi, hgt, hgN, hker⟩ := GlobalTheory.T.exists_compatible_isometries_coisotropic_kernels Dw y hcois htow (GlobalTheory.T.finrank_uChart_le_min_signature Xo c R hR C) l.M' hM
  refine ⟨Z, hZ, hZr, tK, m1, m2, fun F _ _ _ => ?_⟩
  let I₁ := twistI hB I₀ g hgi hgt
  have hI₁ : XFLevel C tK m1 m2 F₀ I₁ := by
    refine ⟨hI₀.1, fun k a σ hk x hx => hI₀.2 k a σ hk x ?_⟩
    have hk1 : 1 ≤ k ∧ k ∣ l.M' := by
      rcases hk with ⟨rfl, -⟩ | ⟨rfl, -⟩
      · exact ⟨l.A_pos, Nat.dvd_lcm_right _ _⟩
      · exact ⟨by have := l.three_le; omega, Nat.dvd_lcm_left _ _⟩
    obtain ⟨f, f₁, -, f₃, -⟩ := hT F₀ k hk1.1
    rw [f₁] at hx ⊢
    rw [hx]
    refine (f₃ _ _).2 ((I₀.ker k hk1.1 _ _).2 ?_)
    obtain ⟨e, he⟩ := hgN k a
    obtain ⟨j, hj⟩ := hk1.2
    exact ⟨j • e, by rw [smul_smul, ← hj]; exact he⟩
  obtain ⟨I, hIl, hIy⟩ := GlobalTheory.T.exists_levelIsometry_extension_algClosed Xo c R hR C tK m1 m2 I₁ hI₁ F
  refine ⟨I, hIl, fun n hn a => ?_⟩
  rw [GlobalTheory.T.exists_equiv_latticePart_zero_iff_mem_nsmul R _ hB F n hn, hIy, ← hker n hn a]
  obtain ⟨e, he⟩ := hy n hn (g n a)
  change (∃ e, (I₀.ev n (g n a)).y = n • e) ↔ _
  constructor
  · rintro ⟨e', he'⟩; exact ⟨e + e', by rw [he, he', smul_add, add_comm]⟩
  · rintro ⟨e', he'⟩; exact ⟨e' - e, by rw [smul_sub, ← he', he, add_sub_cancel_right]⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLcCutPointOfNotLcOther
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

namespace GlobalTheory.PairStep

theorem exists_lcCut_of_not_lcAt : GlobalTheory.Published.Principalisation → GlobalTheory.Published.NadelVanishingPair → GlobalTheory.Published.NefNumerics → ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → letI := algebraΓOfHom p; ∀ (Δ : X → ℚ) (m : ℕ) (G : CartierDiv X) (N : LB X) (D : X → ℚ) (d h : ℚ) (x x' z : X) (j : ℕ), IsEffQDiv Δ → (∀ y, KltAt p n Δ y) → 0 < m → IsLogCanonicalMultiple p n Δ m G → IsAmpleLB N → QNum p N d D → 0 ≤ d → IsClosed ({x} : Set X) → LcAt p n (Δ + D) x → ¬ LcAt p n (Δ + D) x' → z ⤳ x → IsNkltCentre p n (Δ + D) z → topologicalKrullDim (closure ({z} : Set X)) = (j + 1 : ℕ) → 0 < h → ((j + 1 : ℕ) : ℚ) ^ (j + 1) < h ^ (j + 1) * (interNumRed ℂ (Closeds.closure ({z} : Set X)) fun _ : Fin (j + 1) => N : ℤ) → ∃ (D' : X → ℚ) (d' : ℚ), 0 ≤ d' ∧ d' ≤ d + h ∧ QNum p N d' D' ∧ LcCut p n (Δ + D') x j ∧ ¬ KltAt p n (Δ + D') x' := by
  intro hPr hNad hNef X _ _ _ p n hp hn Δ m G N D d h x x' z j hΔ hklt hm hG hN hQ hd hx hlc hnlc
    hzx hz hzd hh hdeg
  have hDq : IsQCart D := QNum.isQCart hQ

  obtain ⟨B, δ₀, hδ₀, hδ₀1, hBq, hoff, hnk, hfar⟩ :=
    GlobalTheory.T.exists_divisor_nonKlt_at_points_not_containing_centre hPr hNad hNef X p n hp hn Δ m G N D {x} z (j + 1) h hΔ hklt hm hG hN hDq
      (by simp [hx, hzx]) (by omega) hzd (Or.inr hz) hh (by simpa using hdeg)

  obtain ⟨δ₁, hδ₁, hx'⟩ := GlobalTheory.T.exists_not_kltAt_sub_of_not_lcAt X p n hp hn Δ D x' hDq (hklt x') hnlc
  obtain ⟨δ, hδ, hδ1, hδa, hδb⟩ : ∃ δ : ℚ, 0 < δ ∧ δ ≤ 1 ∧ δ ≤ δ₀ ∧ δ ≤ δ₁ :=
    ⟨min δ₀ δ₁, lt_min hδ₀ hδ₁, (min_le_left _ _).trans hδ₀1, min_le_left _ _, min_le_right _ _⟩
  have hBc : IsQCart B := QNum.isQCart hBq
  have hDδ : IsQCart ((1 - δ) • D) := (GlobalTheory.T.isEffectiveQCartierDivisor_convexCone X D D (1 - δ) hDq hDq (by linarith)).2.1

  have hkx : KltAt p n (Δ + (1 - δ) • D) x := GlobalTheory.T.kltAt_add_one_sub_smul_of_kltAt_of_lcAt X p n hp hn Δ D δ x hDq (hklt x) hlc hδ hδ1
  have hnkx : ¬ KltAt p n (Δ + (1 - δ) • D + B) x := hnk δ hδ.le hδa x (Finset.mem_singleton_self x)

  obtain ⟨c, hc, hc1, hlcx, hnklx⟩ :=
    GlobalTheory.T.exists_rational_logCanonicalThreshold_at_point hPr X p n hp hn Δ m G ((1 - δ) • D) B x hm hG hDδ hBc hkx hnkx
  have hcut : LcCut p n (Δ + (1 - δ) • D + c • B) x j :=
    GlobalTheory.T.nonKlt_locus_dim_lt_after_perturbation X p n hp hn Δ D B δ c x z j (hklt x) hDq hBc hlc hδ hδ1 hc1 hoff hfar hzd hlcx hnklx
  refine ⟨(1 - δ) • D + c • B, (1 - δ) * d + c * h, ?_, ?_, ?_, ?_, ?_⟩
  · have : 0 ≤ 1 - δ := by linarith
    positivity
  · nlinarith [mul_nonneg hδ.le hd, mul_le_mul_of_nonneg_right hc1 hh.le]
  · exact qNum_add X p hp N _ _ _ _ (GlobalTheory.T.effQCartierNumEquivMultiple_nonneg_smul X p hp N d (1 - δ) D (by linarith) hQ)
      (GlobalTheory.T.effQCartierNumEquivMultiple_nonneg_smul X p hp N h c B hc.le hBq)
  · rw [← add_assoc]
    exact hcut
  ·
    intro hk
    rw [← add_assoc] at hk
    have h0 := (GlobalTheory.T.kltAt_and_lcAt_antitone_coeff X p n hp hn (Δ + (1 - δ) • D) B 0 c x' hBc hc.le).1 hk
    rw [zero_smul, add_zero] at h0
    exact hx' δ hδ.le hδb h0

end GlobalTheory.PairStep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaMemberInjectiveEvaluationStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_thetaMember_injective_evaluation : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), GlobalTheory.GSep.IsAct X₁ act → ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsLocalRing V) (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) (_ : AddCommGroup X) (t : X → V) (δ : I → X → X), Function.Injective ev ∧ Nonempty (GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) := by
  first | exact @GlobalTheory.GSep.exists_gMem_injective | exact GlobalTheory.GSep.exists_gMem_injective | (intros; apply GlobalTheory.GSep.exists_gMem_injective <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformisedMemberOfRefinedUniformisationStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_uniformised_member_of_refined_uniformisation : ∀ g : ℕ, 1 ≤ g → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) [IsOpenImmersion i], IsProjOver z → IsNormalScheme Z → i ≫ z = F.s → Dense (Set.range i) → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → ThetaInt F W i → ∀ (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsAct X₁ act → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (Q : Data V) (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ Q.X), (∀ k, t k ≠ 0) → (∀ k a b, δ k a b = δ k b a) → (∀ k a, 0 ≤ δ k a a) → Q.IsMonomialTau t δ → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] (ρ : V →+* V₁), IsCN V₁ → Function.Injective ρ → ρ.Finite → ∀ (D₀ : DegData V₁ (maximalIdeal V₁)) (e₀ : D₀.toPre.X ≃+ Q.X), Refines Q ρ D₀.toPre e₀ → ∀ (G₀ : Over (Sp V₁)) [GrpObj G₀] [IsCommMonObj G₀] (A₀ : PolAV (Sp (FractionRing V₁))) (U₀ : Unif (maximalIdeal V₁) D₀ A₀ G₀) (y : Sp (FractionRing V₁) ⟶ F.X) (α : A₀.A.left ⟶ F.univ.A.left) (α₂ : (G2 A₀.A).left ⟶ (G2 F.univ.A).left), IsSemiAbelian G₀ → IsGrpPullback A₀.A F.univ.A y α → IsSquare α α₂ → LBIso (abelian₂ A₀.A A₀.L) (F.univ.P.pull α₂) → ∀ ev : X₁.M.Z.presheaf.stalk z₁ →+* V₁, IsLocalHom ev → RegAt X₁ z₁ ev → jK V₁ ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁ ≫ X₁.π = y ≫ i → ∃ 𝔪 : UMem X₁ z₁ act V₁ ev Q.X (fun k => ρ (t k)) δ, SharpRef W Q ρ 𝔪.D.toPre 𝔪.e₈ := by
  first | exact @GlobalTheory.Poinc.Sep.MkMember.exists_uMem | exact GlobalTheory.Poinc.Sep.MkMember.exists_uMem | (intros; apply GlobalTheory.Poinc.Sep.MkMember.exists_uMem <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreEighthPowerThetaObjectSubfieldStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fibre_eighth_power_theta_object_subfield : ∀ (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (gQ : ℕ), ∃ (J : Type) (_ : Finite J)
    (Mat : J → Matrix (Fin (2 * (8 * gQ))) (Fin (2 * (8 * gQ))) ℤ) (κ : ℕ) (w w' : J),
  ∀ (l : ℕ), l.Prime → Odd l → ∀ j : ℕ, 1 ≤ j →
  ∀ (V V₁ : Type) [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → IsUnit (l : V₁) →
  ∀ (Q : Data V), Q.g = gQ → ∀ (ρ : V →+* V₁), Function.Injective ρ → ∀ (D : DegPre V₁) (e : (Fin 8 → Q.X) ≃+ D.X),
  SharpRef W Q ρ D e → ∀ (C : Type) (u : (Fin 8 → Q.X) → C → V₁) (mo : (Fin 8 → Q.X) → V₁),
  (∀ mu, mo mu ≠ 0 ∧ ∃ c, IsUnit (u mu c)) → IsThetaTerms D ((l ^ j) ^ 2) e (fun mu c => u mu c * mo mu) →
  ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ →
  (∀ mu c c', IsUnit (u mu c') → ∃ r ∈ k₀, ev (u mu c) = r * ev (u mu c')) →
  ∃ (bT : TBase k₀ ((l ^ j) ^ 2)) (t : TObj (8 * gQ) ((l ^ j) ^ 2) J bT (spMap k₀.subtype))
    (v : Ix (8 * gQ) ((l ^ j) ^ 2) → k₀) (ψ : ((Over.pullback (spMap ev)).obj D.P.A).left ⟶ t.A.left),
    t.Shape Mat κ ∧ t.Prim w w' ∧ t.HasTh (𝟙 _) (fun a => k₀.subtype (v a)) ∧
    IsGrpPullback ((Over.pullback (spMap ev)).obj D.P.A) t.A (𝟙 _) ψ ∧
    LBIso (D.P.L.pull (pullback.fst D.P.A.hom (spMap ev))) (t.L.pull ψ) ∧
    ∀ (y : Over.mk (spMap ev) ⟶ D.P.A), y ^ ((l ^ j) ^ 2) = 1 →
      ∀ q : Sp K ⟶ ((Over.pullback (spMap ev)).obj D.P.A).left,
      q ≫ pullback.fst D.P.A.hom (spMap ev) = y.left → q ≫ pullback.snd D.P.A.hom (spMap ev) = 𝟙 _ →
      ∃ a, q ≫ ψ = (t.lab a).left := by
  first | exact @GlobalTheory.Poinc.Sep.sharp_fibre_theta_object | exact GlobalTheory.Poinc.Sep.sharp_fibre_theta_object | (intros; apply GlobalTheory.Poinc.Sep.sharp_fibre_theta_object <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsQuasiLogarithmBasisReductionThickeningStatement
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isQuasiLogarithmBasis_reduction_thickening : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) F.B), IsLift F.θ μ' → (∀ i, map F.θ (μ' i) = c.μ i) → ∀ (k : ℕ) (e : Fin d ⊕ Fin k → MvPowerSeries (Fin d) F.Q), IsBasis μ' e → ∀ Θ : F.Q →+* C, (∀ b, Θ (algebraMap F.B F.Q b) = algebraMap O C (F.θ b)) → IsBasis c.μ (fun l => map Θ (e l)) := by
  first | exact @GlobalTheory.ReduceBasis.isBasis_map | exact GlobalTheory.ReduceBasis.isBasis_map | (intros; apply GlobalTheory.ReduceBasis.isBasis_map <;> assumption)
end

