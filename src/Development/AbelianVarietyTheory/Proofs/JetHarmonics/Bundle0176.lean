import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.CmLiftConditionOfLaws
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0012
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0023
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsBasisOfCoord
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ValuationThetaRatioEqBilinear
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0175
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0099
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0124
import Formalism.LocalToGlobal.ProjectiveLattices.SpMapAlgHomId
import Development.AbelianVarietyTheory.Definitions.Jets.EmbShortThLeThetaPlain
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ThetaLeMsupOfSetC
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0003
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.PairUnfoldPfA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0022
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0014
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsFieldsSeparately
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0092
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0031
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0062
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0019
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0160
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0016
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0016
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0168
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0171
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0173
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.StandardCoverShortValueEqThetaValue
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsUnitOfPrimeNe
section
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

namespace GlobalTheory.GeneratorsAtPoint

theorem isUnit_of_prime_ne {V : Type} [CommRing V] [IsLocalRing V] {g g' : ℕ} (hg : g.Prime) (hg' : g'.Prime)
    (hne : g ≠ g') (hn : ¬ IsUnit ((g : ℕ) : V)) : IsUnit ((g' : ℕ) : V) := by
  have hz : IsCoprime (g : ℤ) (g' : ℤ) := Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hg hg').2 hne)
  obtain ⟨a, b, hab⟩ : IsCoprime ((g : ℕ) : V) ((g' : ℕ) : V) := by
    simpa using hz.map (Int.castRingHom V)
  rcases IsLocalRing.isUnit_or_isUnit_of_add_one hab with h₁ | h₁
  · exact absurd (isUnit_of_mul_isUnit_right h₁) hn
  · exact isUnit_of_mul_isUnit_right h₁

section Cast
variable {R : Type} [CommRing R] [IsDomain R] {Dp : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem famCast_symm {k k' : ℕ} (e : k = k') (s : Fam Dp F k') : famCast e (famCast e.symm s) = s := by
  subst e; rfl

theorem famCast_sum {k k' : ℕ} (e : k = k') {m : ℕ} (a : Fin m → F) (b : Fin m → Fam Dp F k) :
    famCast e (∑ i, a i • b i) = ∑ i, a i • famCast e (b i) := by
  subst e; rfl

end Cast

theorem nuGe_famCast {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    {Dd : DegData V (maximalIdeal V)} {Q : Dd.toPre.X → ℤ} {K : Type} [Field K] [Algebra (FractionRing V) K]
    {v : AddValuation K (WithTop ℚ)} {k k' : ℕ} (e : k = k') {s : Fam Dd.toPre K k} {r : ℚ}
    (h : NuGe Dd Q K v k s r) : NuGe Dd Q K v k' (famCast e s) r := by
  subst e; exact h

theorem unitBall_spanned (hL : Laws) (hT : TwistBaseChangeStatement)
    (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] (D' : DegData V (maximalIdeal V)) (A' : PolAV (Spec (CommRingCat.of (FractionRing V))))
    (G' : Over (Sp V)) [gr : GrpObj G'] [cm : IsCommMonObj G'] (U' : Unif (maximalIdeal V) D' A' G')
    [md : Module (𝓞 E) D'.toPre.X] :
    letI := H.starRing
    ∀ (oD' : D'.toPre.OAct (𝓞 E)) (oA' : A'.OAct (𝓞 E)) (t' : SAB H (Sp V)) (P' : PELUnif (maximalIdeal V) t'),
      P'.TorsionIso → t'.G = G' → HEq t'.grp gr → HEq t'.comm cm → P'.D = D' → HEq P'.mod md → HEq P'.oD oD' →
      P'.A = A' → HEq P'.oA oA' → HEq P'.U U' →
    ∀ (α : 𝓞 E) (N : ℕ), 1 ≤ N → α * star α = (N : 𝓞 E) → (∃ u u' : 𝓞 E, u * α + u' * star α = 1) →
      IsUnit ((N : ℕ) : V) →
    ∀ (ϖ : V), Irreducible ϖ → ∀ (Q : D'.toPre.X → ℤ), IsQ D'.toPre ϖ Q →
    ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] (v : AddValuation F (WithTop ℚ)),
      ValOver ϖ F v →
    ∀ (Dw : Datum H) (_I : TateIso Dw F (TFK (R := V) F ⟶ A'.A) (fun a g => g ≫ oA'.act a)
        (fun n g g' c => WeilIs A'.A A'.L n g g' (unitOn c))),
    ∀ θ : Fam D'.toPre F 1, NuGe D' Q F v 1 θ 0 → ThFrame D' ϖ F θ →
    ∀ θα : Fam D'.toPre F (1 * N), PullAl D' F oD' α 1 N θ θα →
    ∀ s : Fam D'.toPre F (1 * N), NuGe D' Q F v (1 * N) s 0 →
      ∃ (m : ℕ) (p : Fin m → QkPt D'.toPre F (1 * N)) (x : Fin m → (TFK (R := V) F ⟶ A'.A))
        (w : ∀ i, LB.Gen (LB.LinComb D'.toPre.P.L (DegPre.lineφ D'.toPre F (p i).g.b) (DegPre.lineε (1 * N))))
        (ζ : Fin m → F) (t : Fin m → Fam D'.toPre F (1 * N)) (a : Fin m → F),
        (∀ i, QkToAkU U'.toUnifPre F (1 * N) (p i) (x i)) ∧
        (∀ i, x i ≫ oA'.act (star α) = 1) ∧
        (∀ i, (w i).IsGen ∧ ζ i ≠ 0 ∧ FinOrd D' F (1 * N) (p i) (w i) (ζ i)) ∧
        (∀ i, ∃ t' : Fam D'.toPre F (1 * N),
          PhiRel D'.toPre F (1 * N) (p i) (w i) θα t' ∧ Fam.IsSmul D'.toPre F (ζ i) t' (t i)) ∧
        (∀ i, (0 : WithTop ℚ) ≤ v (a i)) ∧
        s = ∑ i, a i • t i := by
  let _ := H.starRing
  intro oD' oA' t' P' hP e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉
  subst e₁ e₄ e₇
  cases e₂
  cases e₃
  cases e₅
  cases e₆
  cases e₈
  cases e₉
  exact ReciprocityTheory.ChartRestriction.G.H1.cmLiftCondition_of_laws hL n1c (GlobalTheory.twisting_statements_of_laws hL hT).1
    (GlobalTheory.UnitBallFree.main hL.globalFns hT) E H V t' P' hP

theorem main : Laws → Laws2 → Laws3 → Laws4 → Laws5 → TwistBaseChangeStatement → GenPointT := by
  intro hL hL2 hL3 hL4 hL5 hT E _ _ _ H Dw l Xo c
  let _ := H.starRing
  intro T io y C hTr P hP hy ϖ hϖ Q hQ g g' hg hg' hne hgo hg'o π π' hπ hπ' hcop hcop' hgnu F _ _ _ _ _ _ v hv I n
    D' A' G' _ _ pD pA pG U' PU _ oD' hx hact s s₂ p w ζ x t₀ t σ' h hbox
  obtain ⟨hs, hs₂, ⟨hw, hζ, hfo⟩, hqx, hxk, hphi, hsm, hexp, hgerm⟩ := hbox
  have hq : 1 ≤ g' * g := Nat.mul_pos hg'.pos hg.pos
  have hπb : star π * star (star π) = (g : 𝓞 E) := by rw [star_star, _root_.mul_comm]; exact hπ
  have hπb' : star π' * star (star π') = (g' : 𝓞 E) := by rw [star_star, _root_.mul_comm]; exact hπ'
  have hw0 : TraceFormTwistIso D'.toPre oD' H.w0 := GlobalTheory.PsiWZeroProd.main T.V n P.D.toPre D'.toPre pD (𝓞 E)
    (fun a x => funext fun i => hx a x i) P.oD oD' hact H.w0 P.w0
  obtain ⟨pl, -, hpl⟩ := PullLin.exists_pull_linearMap hL T.V D' F (𝓞 E) oD' H.w0 hw0 (star π) g g' hg.pos hg'.pos hπb
  obtain ⟨pl₂, -, hpl₂⟩ := PullLin.exists_pull_linearMap hL T.V D' F (𝓞 E) oD' H.w0 hw0 (star π * star π') (g' * g) 1 hq
    le_rfl (by rw [star_mul', Nat.cast_mul, ← hπb, ← hπb']; ring)
  obtain ⟨Φ, hΦ⟩ := phiFun_of hL T.V _ D' F (g' * g) hq p w hw
  obtain ⟨τ, hτ, hτT, hiff⟩ := frameNSt_holds E H T.V C.I.G P _ C.FT C.actT C.ph1T C.ph2T C.syT C.adT C.tgT C.xT C.eT
    C.wPT C.chartT C.frameT C.primT n D' A' G' pD pA pG U' PU
  have hz := GlobalTheory.T.universalJets_power_product T.V C.I.G.G G' n _ pG C.xT (GlobalTheory.T.universal_statement E H Dw l Xo c T io y C)
  obtain ⟨gm, hgm, hgmex⟩ := PairingLinear.exists_germ_linearMap hL hL2 hL4 hT T.V D' A' G' U' _ _ hz τ hτ (hτT hTr) F
    (g' * g) hq
  obtain ⟨θ, θα, hθν, hθF, hθα⟩ := PowThetaFrame.main hL hL2 hL4 hT E H Dw l Xo c n T io y hy C P hP g g' hg hg' hne hgo
    hg'o π π' hπ hπ' hcop hcop' hgnu F v ϖ hϖ hv Q hQ D' A' G' pD pA pG U' PU oD' hx hact
  obtain ⟨oA', hoA, hQ', ⟨Dw', ⟨I'⟩⟩, t', P', hP', e₁, e₂, e₃, e₄, e₅, e₆, e₇, e₈, e₉⟩ :=
    powPEL_of_laws hL hL2 hL3 hL4 hL5 hT E H Dw l Xo c n T io y hy C P hP g g' hg hg' hne hgo
      hg'o π π' hπ hπ' hcop hcop' hgnu F v ϖ hϖ hv I Q hQ D' A' G' pD pA pG U' PU oD' hx hact
  have hcopb : ∃ u u' : 𝓞 E, u * star π' + u' * star (star π') = 1 := by
    obtain ⟨u, u', hu⟩ := hcop'
    exact ⟨u', u, by rw [star_star, ← hu]; ring⟩
  obtain ⟨m, pb, xb, wb, ζb, tb, a, hpx, hxb, hwb, htb, ha, hsum⟩ :=
    unitBall_spanned hL hT E H T.V D' A' G' U' oD' oA' t' P' hP' e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉ (star π') g' hg'.pos hπb' hcopb
      (isUnit_of_prime_ne hg hg' hne hgnu) ϖ hϖ _ hQ' F v hv Dw' I' θ hθν hθF θα hθα
      (famCast (Dp := D'.toPre) (F := F) (one_mul g').symm s) (nuGe_famCast _ hs)
  have hs' : s = ∑ i, a i • famCast (Dp := D'.toPre) (F := F) (one_mul g') (tb i) := by
    rw [← famCast_sum, ← hsum, famCast_symm]
  let Λ : Fam D'.toPre F g' →ₗ[F] Fam D'.toPre F (g' * g) := (ζ • Φ) ∘ₗ pl
  refine ⟨θ, pl₂ θ, m, a, fun i => gm (Λ (famCast (Dp := D'.toPre) (F := F) (one_mul g') (tb i))), hθν, hθF,
    (hpl₂ _ _).2 rfl, ha, ?_, fun i => ?_⟩
  · have ht : t = Λ s := by
      rw [(DVR.isSmul_iff _ _ _).1 hsm, (hΦ _ _).1 hphi, (hpl _ _).1 hs₂]
      rfl
    rw [hgm t σ' h hexp ((hiff F _ σ' h).1 hgerm), ht, hs', map_sum, map_sum]
    simp only [map_smul]
  · obtain ⟨tb₀, h₁, h₂⟩ := htb i
    obtain ⟨θα₂, p₂, w₂, ζ₂, x₂, r₀, r₂, k₁, k₂, k₃, k₄, k₅, k₆, k₇, k₈, k₉⟩ :=
      PowDescent.descentIdF_of_laws hL hL2 hL3 hL4 hL5 hT E H Dw l Xo c n T io y hy C P hP g g' hg hg' hne hgo
        hg'o π π' hπ hπ' hcop hcop' hgnu F v ϖ hϖ hv Q hQ D' A' G' pD pA pG U' PU oD' hx hact oA' hoA θ θα hθα
        (pb i) (wb i) (ζb i) (xb i) tb₀ (tb i) (hpx i) (hxb i) (hwb i).1 (hwb i).2.1 (hwb i).2.2 h₁ h₂
        p w ζ x hw hζ hfo hqx hxk _ _ (Λ (famCast (Dp := D'.toPre) (F := F) (one_mul g') (tb i)))
        ((hpl _ _).2 rfl) ((hΦ _ _).2 rfl) ((DVR.isSmul_iff _ _ _).2 rfl)
    obtain ⟨σ₂, j₁, j₂⟩ := hgmex (Λ (famCast (Dp := D'.toPre) (F := F) (one_mul g') (tb i)))
    refine ⟨p₂, w₂, ζ₂, x₂, r₀, r₂, σ₂, k₂, fun b => ?_, k₄, k₅, k₆, (hpl₂ _ _).1 k₁ ▸ k₇, k₈, k₉ ▸ j₁,
      (hiff F _ σ₂ _).2 j₂⟩
    have := pA.hom b
    rw [← hoA, ← Category.assoc, k₃, MonObj.one_comp]

end GlobalTheory.GeneratorsAtPoint
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.LevActMemMlat
section
open NumberField IsDedekindDomain AlgebraicGeometry CategoryTheory Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.FormTies
open scoped TensorProduct

namespace GlobalTheory.FormTies

theorem fromTest_mvPt {K : Type} [Field K] {ιB : Type}
    {pts : ∀ (S : Type) [CommRing S] [Algebra K S], Type}
    {mapR : ∀ {S T : Type} [CommRing S] [Algebra K S] [CommRing T] [Algebra K T],
      (S →ₐ[K] T) → pts S → pts T → Prop}
    {borR : ∀ {S : Type} [CommRing S] [Algebra K S], (ιB → Sˣ) → pts S → pts S → Prop}
    {G : Type} [Group G] {actR : ∀ {S : Type} [CommRing S] [Algebra K S], G → pts S → pts S → Prop}
    (hL : ActLaws pts mapR borR actR) (g : G) {S : Type} [CommRing S] [Algebra K S] {y : pts S}
    (hy : FromTest pts mapR y) : FromTest pts mapR (mvPt pts actR g y) := by
  obtain ⟨p, φ, z, hz⟩ := hy
  exact ⟨p, φ, _, hL.nat g _ S φ z _ y _ hz (mvPt_spec hL.total g z) (mvPt_spec hL.total g y)⟩

theorem levAct_mem_Mlat : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (w : WeightFamilies.Wt D j) (P : Type) (ℓ : P → (LaMod (T.Q.Dw j) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw j) T.Q.l)) (act : P → (recB h.toLawsCore).Cusp j w → (recB h.toLawsCore).Cusp j w), IsLevAct T h j w ℓ act → ∀ g, ∀ F ∈ (recB h.toLawsCore).Mlat j w, act g F ∈ (recB h.toLawsCore).Mlat j w := by
  intro D T h j hj w P ℓ act hact g F hF
  have hp := h.pins
  have hpq : 1 ≤ (T.Q.Dw j).p + (T.Q.Dw j).q := by
    rw [(hp.2.2.2 j hj).1, (hp.2.2.2 j hj).2.1]
    have := hj.1; have := hj.2; have := D.R.m_add_three_le_k
    simp only [Ranks.sigW]; omega
  have hL := GlobalTheory.T.actLev_full_level_group_framedPoints D T.Q j hpq hp.2.1.2
  have hc : (F.1 : T.R j) ∈ T.C j w := cutR_le T.C j w F.2
  have hnat := ((mem_cusp _ _ _ _ _ _).1 hc).1.1
  rintro la _ ⟨⟨q, S, io, e, ho, y, hy, η, hη, rfl⟩, rfl⟩
  let := io.toAlgebra
  have hmv := mvPt_spec hL.total (ℓ g) y.1
  let y' : IntFr (T.Q.Xo j) T.Q.c S io :=
    ⟨_, fromTest_mvPt hL (ℓ g) y.2.1, GlobalTheory.T.integral_framedPoint_of_level_move _ _ _ _ _ _ (levFull (T.Q.Dw j) T.Q.l (ℓ g)) S io y.1 _ hmv y.2.2⟩
  have h0 : 0 ≤ nval S.V e (evI y' F.1) := hF la _ ⟨PtV.mk la ho y' hy () trivial, rfl⟩
  have e1 : evI y (act g F).1 = evI y' F.1 := by
    rw [hact g F]
    exact evalAt_actL hL (h.evalWD j hj) frMap_trans_id (ℓ g) hnat y.1
  show 0 ≤ nval S.V e (evI y (act g F).1)
  rw [e1]
  exact h0

end GlobalTheory.FormTies
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.LevelActionMemCuspForms
section
namespace GlobalTheory.LevelCusp

section Free

open NumberField AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
  ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}
  {U : Formalism.L2.PjFree.Unf Xo c σ r}

theorem exists_match (hσ : Formalism.L2.PjFree.GoodEmb c σ) (hU : Formalism.L2.PjFree.IsUnf U) (hr : 1 ≤ r)
    (hxi : ∀ k k' (τ : E →+* ℂ), ‖τ (U.X k).ξ0‖ = ‖τ (U.X k').ξ0‖)
    {ρ : Xo.X ⟶ Xo.X} {ν : SABMap Xo.univ.t Xo.univ.t ρ} {k k' : U.Comp} {x : (U.X k).dom} {x' : (U.X k').dom}
    {y' : FrPt Xo c (CAt σ)} {t : Ix Dw → (CAt σ)ˣ} (hm : FrMove ρ ν (U.un k x) y') (hb : FrBor t (U.un k' x') y')
    (hx : IsUnitFr (U.X k) x.1) (hx' : IsUnitFr (U.X k') x'.1) :
    ∃ (a : GL (Fin r) E) (h : IsMatch (U.X k) (U.X k') a), ∃ b ∈ Bor (U.X k').Ψ r,
      x'.1 = rmul (lact a (castFr h.psi x.1)) b ∧ (∀ τ i, ‖b τ i i‖ = 1) ∧ ∀ j, cabs (t j : CAt σ) = 1 := by
  obtain ⟨gam, A, htr, hA0, hA, hAt⟩ := GlobalTheory.T.exists_isometry_triangular_periods_of_framePointMove E H Dw l Xo c σ r U hσ hU ρ ν k k' x x' y' t hm hb
  have hgen := GlobalTheory.T.abs_generatorRatio_eq_one_of_unitFrame_move E H Dw l Xo c σ r U hσ hU ρ ν k k' x x' y' t hm hb hx hx'
  obtain ⟨a, ε, hε, hξ, hav, hlat, hiso⟩ := GlobalTheory.T.exists_rational_isometry_of_trace_isometry E r (U.X k) (U.X k') (hxi k k') gam htr
  obtain ⟨hbij, hrt, -, -⟩ := GlobalTheory.Relab.relab_good E H l c σ hσ
  obtain ⟨hrr, hty, -⟩ := hU
  have hΨ : (U.X k).Ψ = (U.X k').Ψ := Finset.ext fun τ => ((hty k).2 τ).trans ((hty k').2 τ).symm
  have hp : (U.X k).p0 = (U.X k').p0 := (hty k).1.trans (hty k').1.symm
  let e := Equiv.ofBijective _ hbij
  have he : ∀ τ, Formalism.L2.PjFree.relab c σ (e.symm τ) = τ := e.apply_symm_apply
  have m1 : ∀ τ ∈ (U.X k).Ψ, Dw.mult (e.symm τ) = r - (U.X k).p0 := fun τ hτ => by
    unfold Datum.mult
    rw [if_pos ((hrt _).1 (by rw [he]; exact ((hty k).2 τ).1 hτ)), (hty k).1]
    omega
  have m2 : ∀ τ ∉ (U.X k).Ψ, Dw.mult (e.symm τ) = (U.X k).p0 := fun τ hτ => by
    unfold Datum.mult
    rw [if_neg (fun h => hτ (((hty k).2 τ).2 (by rw [← he τ]; exact (hrt _).2 h))), (hty k).1]
  have hrel : ∀ τ, ∀ i < Dw.mult (e.symm τ), ∀ v ∈ (U.X k).Λ,
      Formalism.L2.PjFree.perFr (U.X k') x'.1 ((a : Matrix (Fin r) (Fin r) E) *ᵥ v) τ i =
        ∑ j ∈ Finset.range (Dw.mult (e.symm τ)), A (e.symm τ) i j * Formalism.L2.PjFree.perFr (U.X k) x.1 v τ j :=
    fun τ i hi v hv => by
      have := hA (e.symm τ) i hi ⟨v, hv⟩
      rwa [he, ← hav] at this
  rcases hε with rfl | rfl
  · have h : IsMatch (U.X k) (U.X k') a :=
      ⟨hΨ, hp, by rw [hξ, one_mul], fun u v => by rw [hiso, one_mul], hlat⟩
    obtain ⟨b, hb, hxb, hu⟩ := GlobalTheory.T.frames_differ_by_isometry_and_triangular_of_periods E r _ _ a h (fun τ => Dw.mult (e.symm τ)) m1 m2 x.1 x.2 x'.1 x'.2
      (fun τ => A (e.symm τ)) (fun τ => hA0 _) hrel
    obtain ⟨h1, h2⟩ := hu hx hx'
    refine ⟨a, h, b, hb, hxb, h1, fun j => ?_⟩
    rcases j with _ | ⟨τ, i⟩
    · exact hgen
    · have := h2 (e τ) i (by rw [e.symm_apply_apply]; exact i.2)
      rw [e.symm_apply_apply, hAt] at this
      exact this
  · exact (GlobalTheory.T.not_antiIsometry_of_triangular_related_periods E r _ _ hΨ hp hr a hiso (fun τ => Dw.mult (e.symm τ)) m1 m2 x.1 x.2 x'.1 x'.2
      (fun τ => A (e.symm τ)) (fun τ => hA0 _) hrel).elim

theorem laU_match {k k' : U.Comp} {a : GL (Fin r) E} (h : IsMatch (U.X k) (U.X k') a)
    (w : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (τ : (U.X k').Ψ) (i : Fin r) :
    Formalism.L2.PjFree.laU U w n k' τ i = Formalism.L2.PjFree.laU U w n k ⟨τ.1, h.mem τ⟩ i := by
  unfold Formalism.L2.PjFree.laU
  rw [h.p0]

theorem rdU_mem_SS (hσ : Formalism.L2.PjFree.GoodEmb c σ) (hU : Formalism.L2.PjFree.IsUnf U) (hr : 1 ≤ r)
    (hxi : ∀ k k' (τ : E →+* ℂ), ‖τ (U.X k).ξ0‖ = ‖τ (U.X k').ξ0‖) {w : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} (hD : Dom w n)
    {f g : Rul Xo c} (hf : f ∈ sec Xo c w n) (hg : g ∈ sec Xo c w n)
    (hfc : ∀ k, Formalism.L2.PjFree.rdU U f k ∈ (U.X k).SS (Formalism.L2.PjFree.laU U w n k))
    (hmv : ∀ y : FrPt Xo c (CAt σ), ∃ (ρ : Xo.X ⟶ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t ρ) (y' : FrPt Xo c (CAt σ)),
      FrMove ρ ν y y' ∧ evR Xo c g y = evR Xo c f y') (k : U.Comp) :
    Formalism.L2.PjFree.rdU U g k ∈ (U.X k).SS (Formalism.L2.PjFree.laU U w n k) := by
  have hsec := hU.2.2.2.2.1 w n hD g hg k
  obtain ⟨hun1, hun2⟩ := GlobalTheory.FrameNorm.exists_unitFr_frBor E H Dw l Xo c σ r U hσ hU
  obtain ⟨⟨k', a, h⟩, c₀, hc⟩ := GlobalTheory.T.exists_eq_const_mul_of_forall_exists_norm_eq' (Frame (U.X k).Ψ r)
    (Σ k' : U.Comp, {a : GL (Fin r) E // IsMatch (U.X k) (U.X k') a}) (U.X k).dom (FourierCoefficientDomain.isOpen_dom _)
    (GlobalTheory.frames_isConnected E r (U.X k)).isPreconnected (GlobalTheory.frames_isConnected E r (U.X k)).nonempty
    (Formalism.L2.PjFree.rdU U g k) (fun i x => Formalism.L2.PjFree.rdU U f i.1 (lact i.2.1 (castFr i.2.2.psi x))) hsec.1
    (fun i => (hfc i.1).1.1.1.comp ((GlobalTheory.Dict.Extend.differentiable_lact i.2.1).comp
      (GlobalTheory.Dict.Pull.cast_diff i.2.2.psi)).differentiableOn fun x hx => i.2.2.mem_dom hx)
    (fun x hx => by
      obtain ⟨x₀, hx₀, ⟨b₀, hb₀, e₀⟩, -⟩ := hun1 k ⟨x, hx⟩
      obtain ⟨ρ, ν, y', hm, hv⟩ := hmv (U.un k x₀)
      obtain ⟨k', x', t, hx', hb⟩ := hun2 y'
      obtain ⟨a, h, b, hbB, hxb, hb1, ht⟩ := exists_match hσ hU hr hxi hm hb hx₀ hx'
      refine ⟨⟨k', a, h⟩, ?_⟩
      have hQ := (hfc k').1.1
      have v1 : Formalism.L2.PjFree.rdU U g k x₀.1 = Formalism.L2.PjFree.toC (evR Xo c g (U.un k x₀)) := dif_pos x₀.2
      have v2 : Formalism.L2.PjFree.rdU U f k' x'.1 = Formalism.L2.PjFree.toC (evR Xo c f (U.un k' x')) := dif_pos x'.2
      have v3 := (GlobalTheory.Frames.algebraic_laws GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c).2.2.2.2.2.2 (CAt σ)
        (inferInstanceAs (IsReduced ℂ)) w n f hf t _ y' hb
      have v4 : ‖Formalism.L2.PjFree.toC (wchar (ex Dw w n) t : CAt σ)‖ = 1 := by
        have : Formalism.L2.PjFree.toC (wchar (ex Dw w n) t : CAt σ) =
          ∏ j, Formalism.L2.PjFree.toC (t j : CAt σ) ^ ex Dw w n j := rfl
        rw [this, norm_prod]
        exact Finset.prod_eq_one fun j _ => by
          rw [norm_pow, show ‖Formalism.L2.PjFree.toC (t j : CAt σ)‖ = 1 from ht j, one_pow]
      have v5 : ‖Formalism.L2.PjFree.rdU U g k x₀.1‖ = ‖Formalism.L2.PjFree.rdU U f k' x'.1‖ := by
        rw [v1, v2, hv, v3]
        exact (norm_mul (Formalism.L2.PjFree.toC (wchar (ex Dw w n) t : CAt σ)) _).trans (by rw [v4, one_mul]; rfl)
      have v6 : ‖bchar (Formalism.L2.PjFree.laU U w n k') b‖ = 1 := by
        unfold bchar
        simp only [norm_prod, norm_zpow, hb1, one_zpow, Finset.prod_const_one]
      rw [hxb, hQ.2.1 _ (h.mem_dom x₀.2) b hbB, norm_mul, v6, one_mul, e₀, hsec.2.1 x hx b₀ hb₀,
        GlobalTheory.Dict.Pull.cast_rmul, GlobalTheory.Dict.Extend.lact_rmul,
        hQ.2.1 _ (h.mem_dom hx) _ (GlobalTheory.Dict.Pull.cast_bor h.psi hb₀),
        GlobalTheory.Dict.Pull.cast_bchar h.psi (laU_match h w n), norm_mul, norm_mul] at v5
      exact mul_left_cancel₀ (norm_ne_zero_iff.2 (AR.Up.OntoE.bchar_ne _ _ hb₀)) v5)
  exact GlobalTheory.T.mem_cuspForms_of_multiple_rational_isometry_move E r _ _ a h _ _ (laU_match h w n) _ _ c₀ hsec (hfc k') hc

end Free

end GlobalTheory.LevelCusp

open NumberField IsDedekindDomain AlgebraicGeometry CategoryTheory Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.FormTies
open scoped TensorProduct

theorem GlobalTheory.LevelCusp.actLev_mem_cuspA : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (w : WeightFamilies.Wt D j) (γ : LaMod (T.Q.Dw j) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw j) T.Q.l), ∀ f ∈ T.cuspA j (wtA w) w.n, actLev (Xo := T.Q.Xo j) T.Q.c (levFull (T.Q.Dw j) T.Q.l) γ f ∈ T.cuspA j (wtA w) w.n := by
  intro D T h j hj w γ f hf
  have hp := h.pins
  have hpq : 1 ≤ (T.Q.Dw j).p + (T.Q.Dw j).q := by
    rw [(hp.2.2.2 j hj).1, (hp.2.2.2 j hj).2.1]
    have := hj.1; have := hj.2; have := D.R.m_add_three_le_k
    simp only [Ranks.sigW]; omega
  have hL := GlobalTheory.T.actLev_full_level_group_framedPoints D T.Q j hpq hp.2.1.2
  obtain ⟨hs, hc⟩ := (mem_cusp _ _ _ _ _ _).1 hf
  have hg : actLev (Xo := T.Q.Xo j) T.Q.c (levFull (T.Q.Dw j) T.Q.l) γ f ∈ sec (T.Q.Xo j) T.Q.c (wtA w) w.n :=
    actL_mem _ _ _ _ hL.total hL.nat hL.bor _ γ hs
  refine (mem_cusp _ _ _ _ _ _).2 ⟨hg, fun σ hσ => holCusp_mem_holSub _ _ fun k => ?_⟩
  have hU := h.unf j hj σ hσ
  refine GlobalTheory.LevelCusp.rdU_mem_SS (U := Formalism.L2.PjFree.Unf.ofPj (T.U j σ)) hσ hU (hU.1 ▸ hpq)
    (fun k k' τ => (h.xiAbs j hj σ hσ k τ).trans (h.xiAbs j hj σ hσ k' τ).symm) (dom_wtA w) hs hg
    (fun k => GlobalTheory.CuspSecFin.mem_SS_of_mem_holSub _ _ (hc σ hσ) k) (fun y => ?_) k
  obtain ⟨ρ, ν, -, -, hm⟩ := mvPt_spec hL.total γ y
  exact ⟨ρ, ν, _, hm, evalAt_actL hL (h.evalWD j hj) frMap_trans_id γ hs.1 y⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.StandardCoverShortValueEqThetaValueStatement
section
open NumberField Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standardCover_shortValue_eq_thetaValue : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (nab : NabV Xo c) (n : ℕ) (d : DeltaDat Xo c n), d.IsLev → IsNab Xo c nab → IsNab d.Xo₂ d.c₂ d.nab₂ → ∀ (m N : ℕ) (a : (E →+* ℂ) × ℕ → ℕ) (x : Fin m → Dw.La) (P : MvPolynomial (LtN Dw m) c.F) (q₀ : Fin m → LevQ Dw d.l₂), GenLat.LevOK (⟨stdLat E m⟩ : GenLat E m) N d.l₂.M → P ∈ harmA c a m → (∀ b, levRep (q₀ b) ∈ (d.I • ⊤ : Submodule (𝓞 E) Dw.La) ∧ levRep (q₀ b) - (d.pd : 𝓞 E) • x b ∈ (l.Mb • ⊤ : Submodule (𝓞 E) Dw.La)) → ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra c.F k] [Algebra d.c₂.F k], (∀ t : c.F, algebraMap d.c₂.F k (d.eF t) = algebraMap c.F k t) → ∀ (y : FrPt Xo c k) (y₂ : FrPt d.Xo₂ d.c₂ k), FrOver d y₂ y → ∀ v v' : k, ShortValAt d.Xo₂ d.c₂ d.nab₂ (fun q : Fin m → LevQ Dw d.l₂ => if q = q₀ then (Nat.card (Fin m → LevQ Dw d.l₂) : d.c₂.F) else 0) (⟨stdLat E m⟩ : GenLat E m) 1 N (MvPolynomial.map (d.eF : c.F →+* d.c₂.F) P) y₂ v → ThValAt Xo c nab y x P v' → v = v' := by
  first | exact @GlobalTheory.shortValAt_std_cover_eq_thValAt | exact GlobalTheory.shortValAt_std_cover_eq_thValAt | (intros; apply GlobalTheory.shortValAt_std_cover_eq_thValAt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ValueTranslatePullbackEqGenerator
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)
open IsDedekindDomain

namespace GlobalTheory

theorem value_translate_pullback_eq_generator : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l),
 letI := H.starRing
 ∀ (nab : NabV Xo c), IsNab Xo c nab → ThValTot Xo c nab → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), FrTrunc C.I.G (𝟙 (Sp T.V)) (chD C.ch) C.xT C.eT → ∀ (P : PELUnif (maximalIdeal T.V) C.I.G), P.TorsionIso → y.IsAlg → ∀ (ϖ : T.V), Irreducible ϖ → ∀ (Q : P.D.toPre.X → ℤ), IsQ P.D.toPre ϖ Q → ∀ (F : Type) [Field F] [IsAlgClosed F] [CharZero F] [Algebra T.Fr F] [Algebra T.V F] [IsScalarTower T.V T.Fr F] (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v → ∀ (n : ℕ) (D' : DegData T.V (maximalIdeal T.V)) (A' : PolAV (Spec (CommRingCat.of T.Fr))) (G' : Over (Sp T.V)) [GrpObj G'] [IsCommMonObj G'] (pD : IsPowDeg D'.toPre P.D.toPre n) (pA : IsPowPolAV A' P.A n) (pG : IsPowGrp G' C.I.G.G n) (U' : Unif (maximalIdeal T.V) D' A' G') (PU : UnifPowOf3 pD pA pG U' P.U) [Module (𝓞 E) D'.toPre.X] (oD' : D'.toPre.OAct (𝓞 E)), (∀ (a : 𝓞 E) (x : D'.toPre.X) (i : Fin n), pD.xe (a • x) i = a • pD.xe x i) → (∀ (a : 𝓞 E) (i : Fin n), oD'.onB.act a ≫ pD.pw.pr i = pD.pw.pr i ≫ P.oD.onB.act a) → ∀ (α : 𝓞 E), α * star α = ((l.M : ℕ) : 𝓞 E) → l.Mb = Ideal.span {star α} → ∀ (θ : Fam D'.toPre F 1) (θα : Fam D'.toPre F (1 * l.M)), NuGe D' (sumQ pD.xe Q) F v 1 θ 0 → ThFrame D' ϖ F θ → PullAl D' F oD' α 1 l.M θ θα → ∀ (p : QkPt D'.toPre F (1 * l.M)) (w : LB.Gen (LB.LinComb D'.toPre.P.L (DegPre.lineφ D'.toPre F p.g.b) (DegPre.lineε (1 * l.M)))) (ζ : F) (x : TFK (R := T.V) F ⟶ A'.A) (t₀ t : Fam D'.toPre F (1 * l.M)) (σ' : U'.toUnifPre.SecGF F (1 * l.M)) (h : PS F n (chD C.ch)), w.IsGen → ζ ≠ 0 → FinOrd D' F (1 * l.M) p w ζ → QkToAkU U'.toUnifPre F (1 * l.M) p x → (∀ k, x ≫ pA.pr k ≫ P.oA.act (star α) = 1) → PhiRel D'.toPre F (1 * l.M) p w θα t₀ → Fam.IsSmul D'.toPre F ζ t₀ t → U'.toUnifPre.ExpandsG F (1 * l.M) σ' t → IsGermN P C.xT C.actT C.eT C.wPT pG PU.toUnifPowOf F (1 * l.M) σ' h → ∀ (a : (E →+* ℂ) × ℕ → ℕ), ∀ Ppol ∈ harmA (Dw := Dw) c a n,
 letI := io.toAlgebra
 ∃ f ∈ thGen Xo c nab a n, ∃ e : F, 0 ≤ v e ∧ nabValN C.ch.B F (MvPowerSeries.map (algebraMap T.Fr F) C.ch.h) H.w0 (1 * l.M) h (fun ℓ : LtN Dw n => ℓ.2.2) (fun (ℓ : LtN Dw n) i => algebraMap T.Fr F (C.ch.uvec ⟨ℓ.1, ℓ.2.1⟩ i)) (MvPolynomial.map ((algebraMap T.Fr F).comp io) Ppol) = e * (∏ τ : E →+* ℂ, algebraMap T.Fr F (io (embK c τ α)) ^ (∑ i : Fin (Dw.mult τ), a (τ, i))) * algebraMap T.Fr F (evI y f) := by
  intro E _ _ _ H Dw l Xo c nab hN hT T io y C hTr P hTor hAlg ϖ hϖ Q hQ F _ _ _ _ _ _ v hv n D' A' G' _ _ pD pA pG U' PU _ oD' hxe hoD α hα hMb θ θα _hNu hTh hPull p w ζ x t₀ t σ' h hw hζ hFin hQk hx hPhi hSm hExp hGerm a Ppol hPpol
  obtain ⟨xx, u, hu, hval⟩ := GlobalTheory.PtTie.harmonicValue_translate E H Dw l Xo c nab hN T io y C hTr P hTor hAlg ϖ hϖ Q hQ F v hv n D' A' G' pD pA pG U' PU oD' hxe hoD α l.M rfl hα hMb θ θα hTh hPull p w ζ x t₀ t (1 * l.M) rfl σ' h hw hζ hFin hQk hPhi hSm hExp hGerm hx
  unfold ThValTot at hT
  classical
  let f : Rul Xo c := fun p yy => (hT p.R yy a n xx Ppol hPpol).exists.choose
  have hrule : IsThRule Xo c nab xx Ppol f := by
    unfold IsThRule
    intro p yy
    exact (hT p.R yy a n xx Ppol hPpol).exists.choose_spec
  have hmem : f ∈ thGen Xo c nab a n := by
    simp only [thGen.eq_1, Set.mem_setOf_eq]
    exact ⟨xx, Ppol, hPpol, hrule⟩
  refine ⟨f, hmem, u, le_of_eq hu.symm, ?_⟩
  rw [hval a Ppol hPpol f hrule]
  simp only [GlobalTheory.PtTie.nrm, map_mul, map_prod, map_pow]
  ring

end GlobalTheory
end

