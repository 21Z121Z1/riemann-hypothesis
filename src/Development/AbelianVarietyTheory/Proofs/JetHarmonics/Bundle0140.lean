import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.ExistsSecTieFOfTies
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0019
import Formalism.LocalToGlobal.ProjectiveLattices.BetaAtSymm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
import Formalism.LocalToGlobal.CharacterGerms.Bundle0018
import Formalism.LocalToGlobal.CharacterGerms.RowTieTop
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0137
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0136
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0138
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0033
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0027
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GramSpace
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0026
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0037
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0041
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0039
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.TheoremZeroSplitOfLocalAndSum
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.Bundle0004
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.InertPrimeDepthContentBoundProof
import Development.AbelianVarietyTheory.Definitions.Jets.DepthNumbersThresholdEq
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntegralSmulCurveCoeffSeriesOfChartHOfLinearLog
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0035
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ImagQuadraticMaximalOrderArithmeticAtSplitPrime
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0110
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0016

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsMulEquivUniformisedPointsUniversal
section
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.PowGerm GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

namespace GlobalTheory.PtTie

theorem exists_mulEquiv_of_isGrpPullback {S S' : Scheme.{0}} {G' : Over S'} {G : Over S} [GrpObj G'] [GrpObj G]
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (Z : Over S') :
    ∃ e : (Z ⟶ G') ≃* (Over.mk (Z.hom ≫ f) ⟶ G), ∀ x, (e x).left = x.left ≫ φ := by
  let Φ₀ : (Z ⟶ G') → (Over.mk (Z.hom ≫ f) ⟶ G) := fun x =>
    Over.homMk (x.left ≫ φ) (by
      show (x.left ≫ φ) ≫ G.hom = Z.hom ≫ f
      rw [Category.assoc, h.1.w, ← Category.assoc, Over.w x])
  let Φ : (Z ⟶ G') →ₙ* (Over.mk (Z.hom ≫ f) ⟶ G) :=
    ⟨Φ₀, fun x y => Over.OverMorphism.ext (h.2 Z x y (Φ₀ x) (Φ₀ y) rfl rfl).symm⟩
  have hinj : Function.Injective Φ := fun x y hxy =>
    Over.OverMorphism.ext (h.1.hom_ext (congrArg CommaMorphism.left hxy) (by rw [Over.w x, Over.w y]))
  have hsurj : Function.Surjective Φ := fun x₀ =>
    ⟨Over.homMk (h.1.lift x₀.left Z.hom (Over.w x₀)) (h.1.lift_snd _ _ _),
      Over.OverMorphism.ext (h.1.lift_fst _ _ _)⟩
  exact ⟨MulEquiv.ofBijective Φ ⟨hinj, hsurj⟩, fun x => rfl⟩

open scoped CategoryTheory.Obj in

theorem exists_mulEquiv_ptTieF : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : letI := io.toAlgebra; FrPt Xo c T.Fr) (I : IntData Xo c T io y) (P : PELUnif (maximalIdeal T.V) I.G) (F : Type) [Field F] [Algebra T.Fr F] (xF : Sp F ⟶ Xo.X), xF = spMap (algebraMap T.Fr F) ≫ (letI := io.toAlgebra; y.x) → ∃ e : (TFK (R := T.V) F ⟶ P.A.A) ≃* (ptO Xo xF ⟶ Xo.univ.t.G), (∀ x b, PtTieF I P F xF x b ↔ b = e x) ∧ ∀ (a : 𝓞 E) x, e (x ≫ P.oA.act a) = e x ≫ Xo.univ.t.act.act a := by
  intro E _ _ _ H Dw l Xo c T io y I P F _ _ xF hxF
  letI := H.starRing
  subst hxF
  have := P.U.gen_hom
  have gpG : IsGrpPullback P.A.A I.G.G (jK T.V) (P.U.gen.inv.left ≫ pullback.fst I.G.G.hom (jK T.V)) := by
    have : IsMonHom P.U.gen.symm.hom := by show IsMonHom P.U.gen.inv; infer_instance
    exact ((isGrpPullback_of_iso P.U.gen.symm).comp (isGrpPullback_pullback I.G.G (jK T.V))).congr
      (Category.id_comp _) rfl
  have actA : ∀ a, (P.oA.act a).left ≫ P.U.gen.inv.left ≫ pullback.fst I.G.G.hom (jK T.V) =
      P.U.gen.inv.left ≫ pullback.fst I.G.G.hom (jK T.V) ≫ (I.G.act.act a).left := by
    intro a
    have e : P.oA.act a ≫ P.U.gen.inv = P.U.gen.inv ≫ (Over.pullback (jK T.V)).map (I.G.act.act a) := by
      rw [Iso.comp_inv_eq, Category.assoc]
      exact ((Iso.inv_comp_eq _).2 (P.lin.ext a)).symm
    rw [← Category.assoc, ← Over.comp_left, e, Over.comp_left, Category.assoc]
    exact congrArg _ (pullback.lift_fst _ _ _)
  obtain ⟨eA, hA⟩ := exists_mulEquiv_of_isGrpPullback gpG (TFK (R := T.V) F)
  obtain ⟨e2, h2⟩ := exists_mulEquiv_of_isGrpPullback I.m2.cart (TFK (R := T.V) F)
  obtain ⟨e1, h1⟩ := exists_mulEquiv_of_isGrpPullback I.m1.cart (TFK (R := T.V) F)
  refine ⟨(eA.trans e2.symm).trans e1, fun x b => ⟨?_, ?_⟩, fun a x => ?_⟩
  · rintro ⟨r, hr, hr1, hr2⟩
    let r' : TFK (R := T.V) F ⟶ I.t'.G := Over.homMk r hr
    have h3 : e2 r' = eA x := Over.OverMorphism.ext (by
      rw [h2, hA]
      exact hr2.trans (by rw [Over.comp_left, Category.assoc]))
    show b = e1 (e2.symm (eA x))
    rw [← h3, e2.symm_apply_apply]
    exact Over.OverMorphism.ext (hr1.symm.trans (h1 r').symm)
  · rintro rfl
    refine ⟨(e2.symm (eA x)).left, Over.w _, (h1 _).symm, ?_⟩
    refine (h2 _).symm.trans ?_
    rw [e2.apply_symm_apply, hA, Over.comp_left, Category.assoc]
  · have h3 : e2.symm (eA (x ≫ P.oA.act a)) = e2.symm (eA x) ≫ I.t'.act.act a := by
      rw [MulEquiv.symm_apply_eq]
      apply Over.OverMorphism.ext
      rw [hA, h2, Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, actA, I.m2.act a,
        ← Category.assoc _ I.m2.cm.F, ← h2, e2.apply_symm_apply, hA, Category.assoc, Category.assoc]
    show e1 (e2.symm (eA (x ≫ P.oA.act a))) = e1 (e2.symm (eA x)) ≫ Xo.univ.t.act.act a
    rw [h3]
    apply Over.OverMorphism.ext
    rw [h1, Over.comp_left, Over.comp_left, h1, Category.assoc, Category.assoc, I.m1.act a]

end GlobalTheory.PtTie
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsSecTieFModel
section
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.PtTie

section Move
open GlobalTheory.FieldBaseChange
variable {X' X X₁ X₂ Y Y₁ : Scheme.{0}} {L' : LB X'}

def isoFromPullId {L : LB X} {m : X' ⟶ X} (w : LB.Iso L' (L.pull m)) : LB.Iso (L'.pull (𝟙 X')) (L.pull m) :=
  ⟨fun p => res (fun _ hy => ⟨hy.1, mem_pull.1 hy.2⟩ :
    (L.pull m).U p.1 ⊓ (L'.pull (𝟙 X')).U p.2 ≤ (L.pull m).U p.1 ⊓ L'.U (p.2 PUnit.unit)) (w.s (p.1, p.2 PUnit.unit))⟩

theorem isoVal_isoFromPullId {L : LB X} {m : X' ⟶ X} (w : LB.Iso L' (L.pull m)) {Z : Scheme.{0}} (r : Z ⟶ X') (z : Z)
    (j : L.ι) (k : L'.ι) (hj : m (r z) ∈ L.U j) (hk : r z ∈ L'.U k) :
    isoVal (isoFromPullId w) r z j k = gv w r z (fun _ => j) k := by
  have hm : r z ∈ (L.pull m).U (fun _ => j) ⊓ (L'.pull (𝟙 X')).U (fun _ => k) := ⟨mem_pull.2 hj, mem_pull.2 hk⟩
  show gm r z _ (res _ (w.s (fun _ => j, k))) = _
  exact gm_res r z _ hm _

theorem isoFromPullId_isGen {L : LB X} {m : X' ⟶ X} {w : LB.Iso L' (L.pull m)} (hw : w.IsGen) :
    (isoFromPullId w).IsGen := by
  refine (isGen_iff _).2 fun Z r z j j' k k' hj hj' hk hk' => ?_
  have ik : r z ∈ L'.U (k PUnit.unit) := (mem_pull (F := 𝟙 X') (x := r z)).1 hk
  have ik' : r z ∈ L'.U (k' PUnit.unit) := (mem_pull (F := 𝟙 X') (x := r z)).1 hk'
  have a := isoVal_isoFromPullId w r z j (k PUnit.unit) hj ik
  have a' := isoVal_isoFromPullId w r z j' (k' PUnit.unit) hj' ik'
  have b := (isGen_iff w).1 hw Z r z j j' _ _ hj hj' ik ik'
  have c := (gm_pull_g L' (𝟙 X') r z k k' hk hk').trans
    (congrArg (fun f : Z ⟶ X' => gm f z _ (L'.g (k PUnit.unit) (k' PUnit.unit))) (Category.comp_id r))
  refine a.trans (b.trans ?_)
  exact congrArg₂ (fun s t => _ * s⁻¹ * t) c.symm a'.symm

end Move

section Comparison₂
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {T : CDVR} {io : c.F →+* T.Fr} {y : letI := io.toAlgebra; FrPt Xo c T.Fr}
  {I : IntData Xo c T io y} {F : Type} [Field F] [Algebra T.Fr F] {xF : Sp F ⟶ Xo.X}

variable (I) (P : PELUnif (maximalIdeal T.V) I.G)

end Comparison₂

end GlobalTheory.PtTie
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsSelfConjugatePlaceDataIntChart
section
open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.RowAt

theorem sum_sigma_extend {A C W : Type} [Fintype A] [Field C] [AddCommGroup W] [Module C W] (m : A → ℕ)
    (e : (Σ s : A, Fin (m s)) → W) (a : A) (b : Fin (m a) → C) :
    ∃ b' : (Σ s : A, Fin (m s)) → C, (∀ q, q.1 ≠ a → b' q = 0) ∧ ∑ x, b x • e ⟨a, x⟩ = ∑ q, b' q • e q := by
  refine ⟨fun q => if h : q.1 = a then b (h ▸ q.2) else 0, fun q hq => dif_neg hq, ?_⟩
  rw [Fintype.sum_sigma, Finset.sum_eq_single a]
  · simp
  · intro s _ hs
    simp [hs]
  · simp

theorem card_sigma_fst_add {d : ℕ} [NeZero d] (m : ZMod d → ℕ) (h a : ZMod d) :
    (Finset.univ.filter fun x : (Σ a : ZMod d, Fin (m a)) => x.1 + h = a).card = m (a - h) := by
  rw [← card_sigma_fst m (a - h)]
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact eq_sub_iff_add_eq.symm

theorem exists_selfData : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (lv : Level H) (Xo : Moduli Dw lv) (c : Coeff lv) [StarRing (𝓞 E)], (∀ x : 𝓞 E, star x = H.bar x) → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C3 : IntChart T io y) (C : Type) [Field C] [CharZero C] (V : VF C) (ι : T.Fr →+* C), EmbOK T V ι → ∀ (k : ℕ) (Y : FBChart C V (𝓞 E) (chD C3.ch)), IsBC C3 ι k Y → ∀ (Orb : Type) [Fintype Orb] (lab : LabS E Orb), ArithS V io ι lab → ∃ p : ∀ o, SelfData Y 2 (lab.II Dw o), IsSelfOf C3 ι Y lab p ∧ SelfSep Y p ∧ (lab.RankOK Dw → ∀ o, (Y.rawSelf (p o)).RankHyp ∧ (Y.rawSelf (p o)).AltC) := by
  intro E _ _ _ H Dw lv Xo c _ hstar T io y C3 C _ _ V ι hι k Y hY Orb _ lab ha
  obtain ⟨hint, hsep⟩ := GlobalTheory.T.cmEmbeddings_integral_and_distinct_mod_maximal E H lv c T io C V ι hι ha.unr
  have hsep' : ∀ x x' : Orb × ZMod 2, x ≠ x' →
      ∃ a : 𝓞 E, V.v (emA3 io ι (lab.tau x.1 x.2) a - emA3 io ι (lab.tau x'.1 x'.2) a) = 0 :=
    fun x x' h => hsep _ _ fun e => h (ha.inj e)
  have hsep1 : ∀ o (s s' : ZMod 2), s ≠ s' →
      ∃ a : 𝓞 E, V.v (emA3 io ι (lab.tau o s) a - emA3 io ι (lab.tau o s') a) = 0 :=
    fun o s s' h => hsep' (o, s) (o, s') fun e => h (Prod.mk.inj e).2
  have hconj : ∀ o (a : ZMod 2) (x : 𝓞 E), emA3 io ι (lab.tau o a) (star x) = emA3 io ι (lab.tau o (a + 1)) x := by
    intro o a x
    rw [ha.conj o a, embedding_conjugate hstar]
  have hgeo := fun o => GlobalTheory.T.separatedEmbeddings_directions_typedBasis E H Dw lv Xo c hstar T io y C3 C V ι hι k Y hY (ZMod 2) (lab.tau o) (hsep1 o)
  have := Y.algClosed
  have hgm := fun o => GlobalTheory.T.exists_matrix_standard_to_hyperbolic_inertPlace C V Y.l_odd Y.cpl (𝓞 E) (fun a => emA3 io ι (lab.tau o a))
    (fun a x => hint _ x) (ha.frob o) (hsep1 o 0 1 (by decide)) (hconj o)
  choose gm hlim hhyp using hgm
  let p : ∀ o, SelfData Y 2 (lab.II Dw o) := fun o =>
    { em := fun a => emA3 io ι (lab.tau o a)
      em_int := fun a x => hint _ x
      em_frob := ha.frob o
      em_sep := hsep1 o
      em_unr := GlobalTheory.T.exists_idempotent_frobeniusOrbit_unramified E H lv c T io C V ι hι ha.unr 2 (lab.tau o) (ha.frob o)
      hd := 1
      hd_ne := by decide
      hd_two := by decide
      em_conj := hconj o
      e := fun x i => ι (chartUnitVectors C3 ⟨lab.tau o x.1, x.2⟩ i)
      ty0 := fun x => x.1
      e_int := fun x i => (hgeo o).1 x.1 x.2 i
      e_eig := fun x a => (hgeo o).2.1 x.1 x.2 a
      e_sat := by
        obtain ⟨w, h1, h2⟩ := (hgeo o).2.2.1
        exact ⟨w, h1, fun q q' => by convert h2 q q'⟩
      e_full := fun a v hv => by
        obtain ⟨b, hb⟩ := (hgeo o).2.2.2 a v hv
        obtain ⟨b', h1, h2⟩ := sum_sigma_extend (fun s => Dw.mult (lab.tau o s))
          (fun (x : lab.II Dw o) i => ι (chartUnitVectors C3 ⟨lab.tau o x.1, x.2⟩ i)) a b
        exact ⟨b', h1, hb.trans h2⟩
      gm := gm o
      gm_lim := hlim o
      gm_hyp := hhyp o
      n := lab.n
      j := lab.j
      j' := lab.j'
      big := fun g s => s = ((g.val : ℕ) : ZMod 2) }
  refine ⟨p, ⟨fun _ _ => rfl, fun _ => rfl, fun _ _ _ => rfl, fun _ _ => rfl, fun _ => rfl, fun _ => rfl,
    fun _ => rfl, fun _ _ _ => Iff.rfl⟩, hsep', fun hr o => ⟨⟨?_, ?_, ?_⟩, by decide, ?_⟩⟩
  · show ∀ (g : Fin 2) (a : ZMod 2), a = (((1 - g).val : ℕ) : ZMod 2) ↔ ¬ a = ((g.val : ℕ) : ZMod 2)
    decide
  · intro g a hb
    change a = ((g.val : ℕ) : ZMod 2) at hb
    subst hb
    fin_cases g
    · exact (card_sigma_fst (fun a => Dw.mult (lab.tau o a)) _).trans (hr o).1
    · exact (card_sigma_fst_add (fun a => Dw.mult (lab.tau o a)) 1 _).trans (hr o).1
  · intro g a hb
    change ¬ a = ((g.val : ℕ) : ZMod 2) at hb
    fin_cases g
    · obtain rfl : a = 1 := by revert hb; revert a; decide
      exact (card_sigma_fst (fun a => Dw.mult (lab.tau o a)) _).trans (hr o).2
    · obtain rfl : a = 0 := by revert hb; revert a; decide
      exact (card_sigma_fst_add (fun a => Dw.mult (lab.tau o a)) 1 _).trans (hr o).2
  · show ∀ a : ZMod 2, a = (((0 : Fin 2).val : ℕ) : ZMod 2) ↔ Even a.val
    decide

end GlobalTheory.RowAt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.HalfEXIffOriented
section
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps.EtaleWeightGaps
open GlobalTheory.PtTie
namespace GlobalTheory.PtTie

theorem barE_piG_eq_piBarO {D : D7} (EX : ErrX D) (i : Fin 2) : barE D (EX.piG i) = piBarO EX i := by
  apply IsFractionRing.injective (𝓞 D.host.E) D.host.E
  exact barE_eq_conj D (EX.piG i)

theorem halfEX_iff_oriented : ∀ (D : D7) (T : Top D), LawsP T → ∀ EX : ErrX D, HalfEX T.toCore EX ↔ Oriented T EX := by
  intro D T h EX
  rw [GlobalTheory.Survey.PiTwistNegation.halfEX_iff_le T.toCore h.toLawsCore.toLawsM EX]
  exact forall_congr' fun i => by rw [barE_piG_eq_piBarO]

end GlobalTheory.PtTie
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.InertPrimeDepthContentBoundProofStatement
section
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.UnitaryBoundIntegral Formalism.L2.DIV Formalism.L2.Pj Formalism.BasicNotions GlobalTheory.GoodDepth NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertPrimeDepthContentBound_proof : InertBd := by
  first | exact @GlobalTheory.InertContent.main | exact GlobalTheory.InertContent.main | (intros; apply GlobalTheory.InertContent.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntegralSmulCurveCoeffSeriesOfChartHOfLinearLogStatement
section
open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_smul_curveCoeffSeriesOfChartH_of_linear_log : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (κ : Type) [Fintype κ] (X : RawChart C d I κ), RLaw X V → ∀ γ : κ → PowerSeries C, IsCv V γ → (∀ i n, 2 ≤ n → n < V.l ^ 2 → PowerSeries.coeff n (alongCv γ (X.lg i)) = 0) → IntS V ((V.l : C) • hCoef X γ V.l) ∧ ((∀ v : κ → C, (∀ i, V.Ge 0 (v i)) → V.MM ((V.l : C) * PowerSeries.coeff V.l (alongCv γ (X.sg v)))) → ∀ i μ, V.MM (MvPowerSeries.coeff μ (MvPowerSeries.pderiv C i ((V.l : C) • hCoef X γ V.l)))) := by
  first | exact @GlobalTheory.GaugeCoef.main | exact GlobalTheory.GaugeCoef.main | (intros; apply GlobalTheory.GaugeCoef.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.JetDUnique
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.OrderGerm

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix3

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}

set_option maxHeartbeats 1000000 in

theorem jetD_twist {S : Type} [CommRing S] [Algebra c.F S] [Algebra ℚ S] [StarRing (𝓞 E)] (y : FrPt Xo c S)
    (C : ChartAt Xo c y) (e' : ∀ m, FrTy y C.d C.x m) (m : ℕ) (cc : Fin C.d → Fin C.d → S)
    (he : ∃ u : (Jet S (Fin 2 × Fin C.d) m)ˣ,
      (u : Jet S (Fin 2 × Fin C.d) m) = psJet m (expP (-bilL C.B.G cc)) ∧
        LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (e' m) (scaleGen (Xo := Xo) _ _ (unitΓ u) (C.e m)))
    (k : ℕ) (F : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (ptO Xo y.x))) (f : MvPowerSeries (Fin 1 × Fin C.d) S)
    (hf : JetD y C.d C.x C.B.A.act C.e C.wP k F m f) :
    JetD y C.d C.x C.B.A.act e' C.wP k F m (f * expP ((k : S) • diagL C.B H.w0 cc)) := by
  have hL := Xo.univ.t.PP.isLB
  obtain ⟨F₁, τ₁, hP₁, hC₁, hV₁⟩ := hf
  obtain ⟨u, hu, hCe⟩ := he
  have h1 := corr_pull_scale _ _ (e' m) (C.e m) (unitΓ u) (homAt y.x (GermD.sL m (C.B.A.act H.w0))).left hCe
  rw [FBIdLB.unitΓ_homAt] at h1
  have hEL : LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (eL y C.d C.x C.B.A.act e' C.wP m)
      (scaleGen _ _ (unitΓ (Units.map (GermD.sL m (C.B.A.act H.w0)).toMonoidHom u))
        (eL y C.d C.x C.B.A.act C.e C.wP m)) := by
    have h2 := ReciprocityTheory.ChartRestriction.G.DVR.corr_mulGen
      (ExpTieGerm.corr_refl (L := Xo.univ.t.PP.L) (LB.pullGen Xo.univ.t.PP.L _ _ C.wP (C.x m).left)) h1
    rw [mulGen_scale_right] at h2
    exact h2
  set U : (Jet S (Fin 1 × Fin C.d) m)ˣ := Units.map (GermD.sL m (C.B.A.act H.w0)).toMonoidHom u with hU
  set w : Γ(Sp (Jet S (Fin 1 × Fin C.d) m), ⊤)ˣ := unitΓ U with hw
  have hG : LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (genPow _ _ (eL y C.d C.x C.B.A.act e' C.wP m) k)
      (scaleGen _ _ (w ^ k) (genPow _ _ (eL y C.d C.x C.B.A.act C.e C.wP m) k)) := by
    have := ExpTieGerm.corr_genPow hEL k
    rwa [genPow_scale] at this
  have h3 := ExpTieGerm.corr_scale hC₁ (w ^ k)
  have hC' := ReciprocityTheory.ChartRestriction.G.DVR.corr_trans hL h3 (ReciprocityTheory.ChartRestriction.G.DVR.corr_symm hG)
  have hV' := isValueAt_scale hV₁ (w ^ k)
  have hprod := unit_jet C.B H.w0 cc m k u hu
  have hinv : psJet m (expP ((k : S) • diagL C.B H.w0 cc)) = ↑((U ^ k)⁻¹) := by
    set X := psJet m (expP ((k : S) • diagL C.B H.w0 cc)) with hX
    calc X = X * ((↑(U ^ k) : Jet S (Fin 1 × Fin C.d) m) * ↑((U ^ k)⁻¹)) := by
          rw [Units.mul_inv, _root_.mul_one]
      _ = (X * ↑(U ^ k)) * ↑((U ^ k)⁻¹) := (_root_.mul_assoc _ _ _).symm
      _ = ↑((U ^ k)⁻¹) := by rw [hprod, _root_.one_mul]
  have hw' : ((w ^ k)⁻¹ : Γ(Sp (Jet S (Fin 1 × Fin C.d) m), ⊤)ˣ) = unitΓ ((U ^ k)⁻¹) := by
    simp [hw, unitΓ, map_pow, map_inv]
  refine ⟨F₁, _, hP₁, hC', ?_⟩
  have hv : toΓ _ (psJet m (f * expP ((k : S) • diagL C.B H.w0 cc))) =
      toΓ _ (psJet m f) * (((w ^ k)⁻¹ : Γ(Sp (Jet S (Fin 1 × Fin C.d) m), ⊤)ˣ) :
        Γ(Sp (Jet S (Fin 1 × Fin C.d) m), ⊤)) := by
    rw [hw']
    show _ = toΓ _ _ * toΓ _ _
    rw [← map_mul, FBIdJet.psJet_mul, hinv]
  rw [hv]
  exact hV'

theorem jetD_unique {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (d : ℕ)
    (x : ∀ m, jO y d m 1 ⟶ Xo.univ.t.G) (act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S)
    (e : ∀ m, FrTy y d x m) (wP : PrimTy H Xo) (k : ℕ)
    (F : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (ptO Xo y.x))) (D : ℕ) (f g : MvPowerSeries (Fin 1 × Fin d) S)
    (hf : JetD y d x act e wP k F D f) (hg : JetD y d x act e wP k F D g) : psJet D f = psJet D g := by
  have hL := Xo.univ.t.PP.isLB
  obtain ⟨F₁, τ₁, hP₁, hC₁, hV₁⟩ := hf
  obtain ⟨F₂, τ₂, hP₂, hC₂, hV₂⟩ := hg
  have hF := GermFun.pull_unique _ _ _ _ _ _ _ _ hP₁ hP₂
  subst hF
  have hτ := GermFun.gen_eq_of_corr _ hL _ _ _ _ _ _ _ hC₁ hC₂
  subst hτ
  exact GermFun.toΓ_injective _ (GermFun.value_unique _ _ hL _ _ _ _ _ _ hV₁ hV₂)

theorem ord_holds : OrdStatement := by
  intro E _ _ _ H Dw l Xo c _ nab hnab S _ _ _ y C k n D F f hf a P hP hD
  have hs := hnab.1
  obtain ⟨C₀, hex, hpin⟩ := hnab.2 S y
  choose f₀ hf₀ using fun b => hex k (F b)
  obtain ⟨e', hfr, hrig, cc, hT, -, hsym, hbal, hu⟩ :=
    frFixB_of (frTruncFix_of frRatio_holds) linEigSt_holds E H Dw l Xo c hs S y C
  have hgerm : ∀ b, ∃ g, IsGerm y C.d C.x C.B.A.act e' C.wP k (F b) g := fun b => by
    obtain ⟨g, hg⟩ := germSt_holds E H Xo.X Xo.univ.t S y.x C.d C.B.G.F C.B.A.act (Lt1 Dw)
      (fun ℓ => y.u ℓ.1 ℓ.2) C.uvec C.x C.B.ph1 C.B.ph2 C.B.sy C.B.ad e' C.wP
      ((isChart_iff y C.d _ _ _ _).1 C.chart) ((isFrame_iff y C.d _ _ _ _ _ _ _ _).1 hfr) ((isPrim_iff _).1 C.prim)
      (fun m => hT m) k (F b)
    exact ⟨g, (isGerm_iff y C.d _ _ _ _ _ _ _).2 hg⟩
  choose g hg using hgerm
  have h₁ : chartVal C k g P = chartVal C k f P :=
    harmInv_of (expActOf_of linEigSt_holds) E H Dw l Xo c hs S y C (cc D) (hsym D) (hbal D) k n D f g
      (fun b => jetD_unique y C.d C.x C.B.A.act e' C.wP k (F b) D _ _ (hg b D)
        (jetD_twist y C e' D (cc D) (hu D) k (F b) (f b) (hf b))) a P hP hD
  have h₂ := chartIndep2_of_glob GlobalTheory.SemiRigid.globalFns E H Dw l Xo c hs S y
    { C with e := e', frame := hfr, rig0 := hrig } C₀ k n F g f₀ hg hf₀ a P hP
  refine h₁.symm.trans (h₂.trans ?_)
  refine Finset.sum_congr rfl fun m _ => congrArg _ (Finset.prod_congr rfl fun b _ => ?_)
  exact (hpin k (F b) (f₀ b) (hf₀ b) (colOf m b)).symm

end GlobalTheory.OrderGerm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ScaledThetaTranslationQuotientElliptic
section
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

namespace GlobalTheory.MomOne.ScaledQuot

theorem not_inOK_neg_half (d : ℕ) (hd : 0 < d) : ¬ InOK d ((0 : ℂ) - 1 / 2) := by
  rintro ⟨u, v, h⟩
  have him := congrArg Complex.im h
  have hre := congrArg Complex.re h
  simp [wK] at him hre
  have hv : v = 0 := by
    rcases him with h | h
    · exact h
    · exact absurd h hd.ne'
  subst hv
  have h2 : (2 * u : ℝ) = -1 := by
    simp at hre
    linarith
  have h3 : (2 * u : ℤ) = -1 := by exact_mod_cast h2
  omega

theorem inOK_nat_mul (d s : ℕ) {l : ℂ} (hl : InOK d l) : InOK d ((s : ℂ) * l) := by
  obtain ⟨u, v, rfl⟩ := hl
  exact ⟨s * u, s * v, by push_cast; ring⟩

theorem inOK_nat (d s : ℕ) : InOK d (s : ℂ) := ⟨s, 0, by simp⟩

theorem zero_iff_of_fixed {d : ℕ} {θ : ℂ → ℂ} {x : ℂ} (h : W1 d x θ = θ) (z : ℂ) :
    θ (z + x) = 0 ↔ θ z = 0 := by
  have := congrFun h z
  rw [← this]
  simp [W1, U1, Complex.exp_ne_zero]

theorem scaled_quotient_elliptic : ∀ (d q : ℕ) [Fact q.Prime] (M : Mdl q) (ω : ℂ_[q]) (θ : ℂ → ℂ), d.Prime → d % 16 = 7 → Split d q → IsOK d M.L → M.MChart ω → IsTh d θ → ∀ (t : ℂ) (s : ℕ), 0 < s → Nat.Coprime s q → InOK d ((s : ℂ) * t) → let φ : ℂ → ℂ := fun z => U1 d t θ ((s : ℂ) * z) / θ ((s : ℂ) * z); Ell M.L φ ∧ AnalyticAt ℂ φ 0 ∧ (∀ p, θ ((s : ℂ) * p) ≠ 0 → AnalyticAt ℂ φ p) ∧ (∀ p r, PrimeTo d q r → ¬ InOK d (r - 1 / 2) → θ ((s : ℂ) * p + r) = 0 → ¬ M.Small p) ∧ Bdd (hat M.ι (C ω * logS) φ) := by
  intro d q _ M ω θ hd hd7 hsp hL hch hθ t s hs hsq hst φ
  obtain ⟨hdiff, h0, -, hW, hz⟩ := hθ
  obtain ⟨-, -, hUd, -, -, hper, -, -⟩ := GlobalTheory.T.cmLattice_heisenberg_relations_one_variable d hd.pos
  obtain ⟨-, -, -, -, -, hint, -⟩ := GlobalTheory.MomOne.okArith d q M.ι hd hd7 hsp
  obtain ⟨-, -, -, hsm⟩ := GlobalTheory.T.smallTorsion_killed_by_prime_powers d q M ω hd hd7 hsp hL hch
  have hlin : Differentiable ℂ (fun z : ℂ => (s : ℂ) * z) := by fun_prop
  have hN : ∀ p, AnalyticAt ℂ (fun z => U1 d t θ ((s : ℂ) * z)) p := fun p =>
    ((hUd t θ hdiff).1.comp hlin).analyticAt p
  have hD : ∀ p, AnalyticAt ℂ (fun z => θ ((s : ℂ) * z)) p := fun p =>
    (hdiff.comp hlin).analyticAt p
  have han : ∀ p, θ ((s : ℂ) * p) ≠ 0 → AnalyticAt ℂ φ p := fun p hp =>
    (hN p).div (hD p) hp
  have hE : Ell M.L φ := by
    refine ⟨fun p => (hN p).meromorphicAt.div (hD p).meromorphicAt, ?_⟩
    intro l hl z
    have hl' : InOK d l := (hL l).1 hl
    have hWl := hW _ (inOK_nat_mul d s hl')
    have hk : kap1 d ((s : ℂ) * l) t = 1 := by
      obtain ⟨k, hk⟩ := hint l _ hl' hst
      have e : h1 d ((s : ℂ) * l) t = h1 d l ((s : ℂ) * t) := by
        simp only [h1, map_mul, Complex.conj_natCast]; ring
      rw [kap1, e, hk]
      have := Complex.exp_int_mul_two_pi_mul_I (-k)
      rw [← this]
      congr 1
      push_cast; ring
    have hp := hper θ t ((s : ℂ) * l) ((s : ℂ) * z) hWl
    rw [hk, one_mul] at hp
    show U1 d t θ ((s : ℂ) * (z + l)) / θ ((s : ℂ) * (z + l)) = U1 d t θ ((s : ℂ) * z) / θ ((s : ℂ) * z)
    rw [mul_add]
    by_cases hz0 : θ ((s : ℂ) * z) = 0
    · rw [hz0, (zero_iff_of_fixed hWl _).2 hz0, div_zero, div_zero]
    · have hz1 : θ ((s : ℂ) * z + (s : ℂ) * l) ≠ 0 := fun h => hz0 ((zero_iff_of_fixed hWl _).1 h)
      rw [div_eq_div_iff hz1 hz0]
      exact hp
  have hA0 : AnalyticAt ℂ φ 0 := han 0 (by rw [mul_zero, h0]; exact one_ne_zero)
  have hpole : ∀ p r, PrimeTo d q r → ¬ InOK d (r - 1 / 2) → θ ((s : ℂ) * p + r) = 0 → ¬ M.Small p := by
    intro p r hr hr2 hθ0 hsmall
    exact hr2 (hsm p s r (inOK_nat d s) (by exact_mod_cast hs.ne') hr (hz _ hθ0) hsmall).2
  refine ⟨hE, hA0, han, hpole, GlobalTheory.T.cpSeriesCoeffBounded_taylor_elliptic_of_poles q M _ φ hch hE hA0 ?_⟩
  intro p hp
  have hθp : θ ((s : ℂ) * p) = 0 := by
    by_contra hne
    exact absurd hp (not_lt.mpr (han p hne).meromorphicOrderAt_nonneg)
  exact hpole p 0 ⟨1, one_pos, Nat.coprime_one_left q, ⟨0, 0, by simp⟩⟩ (not_inOK_neg_half d hd.pos) (by rw [add_zero]; exact hθp)

end GlobalTheory.MomOne.ScaledQuot
end

