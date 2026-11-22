import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1716
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0653
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0110
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0019
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1544
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleRigidTranslateLineBundleRationalPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1549
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0192
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsPointPrimitiveBundleEqTranslatePpav
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0056
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2266
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2261
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2189
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2289
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0057
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2226
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2280
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2262
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2250
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0011
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsClopenLocusTorsionSectionsHeckeKernel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2290
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBlockMetricDiagForm
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyValExtOfOverLa
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0062
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1765
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1759
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1679

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleTrivialOfSamePolarization
section
open CategoryTheory AlgebraicGeometry Set Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.ArInt GlobalTheory.TorsionForm GlobalTheory.ThetaRR
open GlobalTheory.LB (toMod)
open GlobalTheory.LieVB (omega)
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe (Fl Pt stdLat symMat tauU siegel symPart ChernIsFlat IsMetric InducesPolarisation cov)
open ReciprocityTheory.L2DbarEstimates (V)
open Filter Topology
open scoped ContDiff
open MonoidalCategory CartesianMonoidalCategory Limits
open GlobalTheory.CechPic (Pic cls lam)
open MonObj
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AmpleKerFibre

theorem relAmple_kTriv_of_lam_eq : ∀ (K : Type) [Field K] [IsAlgClosed K] (B : Over (Sp K)) [GrpObj B], IsAbelianScheme B → ∀ (L₀ : LB B.left) (h₀ : L₀.IsLB), Out.RelAmple B L₀ → Out.KTriv B L₀ → ∀ (N : LB B.left) (hN : N.IsLB), lam (cls N hN) (fst B B) (snd B B) = lam (cls L₀ h₀) (fst B B) (snd B B) → Out.RelAmple B N ∧ Out.KTriv B N := by
  intro K _ _ B _ hB L₀ h₀ hA hK N hN hlam
  have := hB.comm
  obtain ⟨O, hO, eO⟩ := CechPic.cls_surj (cls N hN - cls L₀ h₀)
  have lamO : lam (cls O hO) (fst B B) (snd B B) = 0 := by
    rw [eO, GlobalTheory.PrimitiveOverField.lam_sub, hlam, sub_self]
  obtain ⟨x, hx⟩ := GlobalTheory.PointTranslate.exists_point_cls_eq_lam K B hB L₀ h₀ hK O hO lamO
  have hR : (GlobalTheory.RigidTranslate.rigTransl L₀ x).IsLB := LB.isLB_linComb h₀ _ _
  have hcls : cls _ hR = cls N hN := by
    rw [CechPic.cls_linComb h₀, Fin.sum_univ_two]
    have e1 : cls N hN = cls O hO + cls L₀ h₀ := by rw [eO]; abel
    rw [e1, hx, GlobalTheory.PrimitiveOverField.lam_const, Over.id_left, CechPic.pull_id]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, one_smul, neg_smul]
    rw [GlobalTheory.PrimitiveOverField.pull_const, GlobalTheory.PolTranslate.transl, _root_.mul_comm (𝟙 B)]
    abel
  have hiso := (CechPic.cls_eq_iff hR hN).1 hcls
  refine ⟨?_, GlobalTheory.MulDescent.kTriv_of_lbIso hR hN hiso
    (GlobalTheory.RigidTranslate.kTriv_rigTransl_any _ B L₀ h₀ x hK)⟩
  have hAR := GlobalTheory.RigidTranslate.relAmple_rigTransl_point K B hB L₀ h₀ x hA
  obtain ⟨w, hw⟩ : LBIso N ((GlobalTheory.RigidTranslate.rigTransl L₀ x).pull (𝟙 B.left)) :=
    hiso.symm.chartPull (Geo.Tor.chartPullId N) (Geo.Tor.chartPullPull _ (𝟙 _) (𝟙 _) rfl)
  exact relAmple_pull (A' := B) (IsPullback.id_horiz B.hom) hR hN ((isGen_iff w).1 hw) ⊤
    (isAffineOpen_top _) (fun _ => trivial) hAR

end GlobalTheory.AmpleKerFibre
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanExistenceOfComplexIsomorphicField
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.MBLow

theorem archF_of_arch : ∀ κ : Rule, Funct κ → Arch κ → ArchF κ := by
  intro κ hF hA R _ _ _ _ D hP hT F _ _ _ e N ν g r m k hg hm hk β ζ q hq s hs vB bX σ gm hAd k₀ hK
  letI : Algebra (FractionRing R) ℂ := ((e : F →+* ℂ).comp (algebraMap (FractionRing R) F)).toAlgebra
  have he : ∀ x, e (algebraMap (FractionRing R) F x) = algebraMap (FractionRing R) ℂ x := fun _ => rfl
  obtain ⟨N', ν', I, hb, hh, hl, heX, hth, hrg, hvE, hfam⟩ := GlobalTheory.T.degenerationValues_transport_fieldIso R D F ℂ e he N ν
  obtain ⟨hform, hlev⟩ := GlobalTheory.T.degenerationDataValuesIso_transport_formsLevelsFamilies F ℂ e N N' I hb hh hl
  obtain ⟨β', hβ⟩ := hform k β
  obtain ⟨q', hq', hev⟩ := hlev m g hm ζ q hq
  obtain ⟨hBK, hadp⟩ := GlobalTheory.T.abelianKeyValue_adaptedVectors_fieldIso κ hF R D F ℂ e he N ν N' ν' I hh hl heX hth hvE vB
  obtain ⟨gm', hpull, hAd'⟩ := hadp r g bX σ gm hAd
  choose s' hs1 hs2 using fun a => hfam (m ^ 2) (s a)
  have hs' : ∀ a, ∃ f, ν'.FamV (s' a) f ∧ IsEvFam N' m (q' a) f := by
    intro a
    obtain ⟨f, hf, hf2⟩ := hs a
    obtain ⟨f', hf', hff⟩ := hs1 a f hf
    exact ⟨f', hf', hev a f f' hf2 hff⟩
  obtain ⟨ε, hε, H⟩ := hA R D hP hT N' ν' g r m k hg hm hk β' _ q' hq' s' hs' vB _ σ gm' hAd' _ (hBK k₀ hK)
  have h1 : ∀ a j α, (jc ν' (s' a) (gm' j) (I.e α)).fst = e (jc ν (s a) (gm j) α).fst := by
    intro a j α
    rw [hs2 a _ _ (hpull j) α]
    simp [dualMap]
  have h2 : ∀ a j α, (jc ν' (s' a) (gm' j) (I.e α)).snd = e (jc ν (s a) (gm j) α).snd := by
    intro a j α
    rw [hs2 a _ _ (hpull j) α]
    simp [dualMap]
  refine ⟨ε, hε, fun u hu hu' => ?_⟩
  obtain ⟨hsum, x₀, hg₀, lev₀, ϑ, hϑ, hJ, hκ⟩ := H u hu hu'
  refine ⟨fun a j => ⟨?_, ?_⟩, x₀, hg₀, lev₀, ϑ, fun a j => ?_, ?_, hκ⟩
  · have := ((I.e.toEquiv.summable_iff.2 (hsum a j).1)).mul_left ‖(e (ν.rg ^ (m ^ 2)))⁻¹‖
    refine this.congr fun α => ?_
    simp only [Function.comp, AddEquiv.toEquiv_eq_coe, EquivLike.coe_coe, h1, hβ]
    rw [← norm_mul, map_div₀, div_eq_inv_mul, _root_.mul_assoc]
  · have := ((I.e.toEquiv.summable_iff.2 (hsum a j).2)).mul_left ‖(e (ν.rg ^ (m ^ 2)))⁻¹‖
    refine this.congr fun α => ?_
    simp only [Function.comp, AddEquiv.toEquiv_eq_coe, EquivLike.coe_coe, h2, hβ]
    rw [← norm_mul, map_div₀, div_eq_inv_mul, _root_.mul_assoc]
  · rw [hϑ a j, ← I.e.toEquiv.tsum_eq]
    refine tsum_congr fun α => ?_
    simp only [AddEquiv.toEquiv_eq_coe, EquivLike.coe_coe, h1, hβ, hrg, map_div₀, map_pow]
  · convert hJ using 3 with a j
    rw [← I.e.toEquiv.tsum_eq]
    refine tsum_congr fun α => ?_
    simp only [AddEquiv.toEquiv_eq_coe, EquivLike.coe_coe, h2, hβ, hrg, map_div₀, map_pow]

end GlobalTheory.MBLow
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BLieLieComb
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

open GlobalTheory.FlatModel

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlatModel

noncomputable def lieComb {O : Type} [CommRing O] (G : Over (Spec (CommRingCat.of O))) [GrpObj G] [IsCommMonObj G] :
    ∀ {m : ℕ}, (Fin m → O) → (Fin m → LieG G) → LieG G
  | 0, _, _ => lieZero G
  | _ + 1, a, x => lieAdd (AvDefs.lieScale G (a 0) (x 0)) (lieComb G (Fin.tail a) (Fin.tail x))

theorem lieComb_zero {O : Type} [CommRing O] (G : Over (Spec (CommRingCat.of O))) [GrpObj G] [IsCommMonObj G]
    (a : Fin 0 → O) (x : Fin 0 → LieG G) : lieComb G a x = lieZero G := rfl

theorem lieComb_succ {O : Type} [CommRing O] (G : Over (Spec (CommRingCat.of O))) [GrpObj G] [IsCommMonObj G]
    {m : ℕ} (a : Fin (m + 1) → O) (x : Fin (m + 1) → LieG G) :
    lieComb G a x = lieAdd (AvDefs.lieScale G (a 0) (x 0)) (lieComb G (Fin.tail a) (Fin.tail x)) := rfl

theorem bLie_lieComb {E : Type} [Field E] [NumberField E] {p : ℕ} [Fact p.Prime] [StarRing (𝓞 E)] (P : PtP E p)
    {m : ℕ} (a : Fin m → 𝓞_ℂ_[p])
    (x : Fin m → LieG P.Gt) : P.bLie (lieComb P.Gt a x) = ∑ i, a i • P.bLie (x i) := by
  induction m with
  | zero => simp [lieComb_zero, P.bLie_zero]
  | succ m ih =>
    rw [lieComb_succ, P.bLie_add, P.bLie_scale, ih, Fin.sum_univ_succ]
    rfl

end GlobalTheory.FlatModel

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeAlt
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.DualCon

theorem Rep.baseChange (S : Scheme.{0}) (A B S' S'' B'' : Over S) [GrpObj A] (b : B ⟶ S')
    (P : LB (A ⊗ B).left) (h : S'' ⟶ S') (k : B'' ⟶ B) (b'' : B'' ⟶ S'') (hR : Rep A b P)
    (hpb : IsPullback k b'' b h) : Rep A b'' (ev P (fst A B'') (snd A B'' ≫ k)) := by
  have hP : P.IsLB := hR.fam.isLB
  have hP' : (ev P (fst A B'') (snd A B'' ≫ k)).IsLB := pull_isLB hP _
  have key : ∀ (Y : Over S) (a : Y ⟶ A) (y : Y ⟶ B''), evc hP' a y = evc hP a (y ≫ k) := by
    intro Y a y
    rw [evc_ev hP, lift_fst, lift_snd_assoc]
  have iso : ∀ (T : Over S) (N : LB (A ⊗ T).left) (hN : N.IsLB) (y : T ⟶ B''),
      LBIso N (ev (ev P (fst A B'') (snd A B'' ≫ k)) (fst A T) (snd A T ≫ y)) ↔
        LBIso N (ev P (fst A T) (snd A T ≫ y ≫ k)) := by
    intro T N hN y
    rw [← cls_eq_iff hN (pull_isLB hP' _), ← cls_eq_iff hN (pull_isLB hP _), cls_ev hP', cls_ev hP, key,
      Category.assoc]
  refine ⟨⟨hP', (isAdditive_iff hP').2 fun Y a a' t ↦ ?_⟩, fun T t N hN ↦ ?_⟩
  · rw [key, key, key]
    exact (isAdditive_iff hP).1 hR.fam.add Y a a' (t ≫ k)
  · obtain ⟨x, ⟨hx1, hx2⟩, hu⟩ := hR.univ T (t ≫ h) N hN
    refine ⟨hpb.lift x t hx1, ⟨hpb.lift_snd _ _ _, (iso T N hN.isLB _).2 ?_⟩, fun y ⟨hy1, hy2⟩ ↦ ?_⟩
    · rw [hpb.lift_fst]
      exact hx2
    · have e : y ≫ k = x := hu (y ≫ k) ⟨by rw [Category.assoc, hpb.w, ← Category.assoc, hy1],
        (iso T N hN.isLB y).1 hy2⟩
      exact hpb.hom_ext (by rw [e, hpb.lift_fst]) (by rw [hy1, hpb.lift_snd])

end GlobalTheory.DualCon
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseLocusExponentTwistingSectionMulLe
section
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum

namespace GlobalTheory.RefTwist

theorem vAdd_natCast_pos {K : Type} [Field K] [NumberField K] {q : ℕ} (hq : q ≠ 0) {w : HeightOneSpectrum (𝓞 K)}
    (hw : ((q : ℕ) : 𝓞 K) ∈ w.asIdeal) : 0 < vAdd w (q : K) := by
  have h1 : w.valuation K (algebraMap (𝓞 K) K q) < 1 := (w.valuation_lt_one_iff_mem _).2 hw
  rw [map_natCast] at h1
  have h0 : w.valuation K (q : K) ≠ 0 := (w.valuation K).ne_zero_iff.2 (Nat.cast_ne_zero.2 hq)
  have h2 := (WithZero.log_lt_log h0 one_ne_zero).2 h1
  rw [WithZero.log_one] at h2
  unfold vAdd
  omega

theorem nval_le_add_of_mul {T : CDVR} {e n : ℕ} {m s k : ℝ} (he : 0 < e) (hm : 0 < m) (hn : (n : ℝ) = e * m)
    (hs : s ≤ k * m) {a b : T.Fr} (h : nval T.V e b ≤ nval T.V e a + (s : EReal)) :
    nval T.V n b ≤ nval T.V n a + (k : EReal) := by
  by_cases ha : a = 0
  · rw [ha, nval_zero, EReal.top_add_coe]; exact le_top
  rw [nval_of_ne ha, ← EReal.coe_add] at h ⊢
  by_cases hb : b = 0
  · rw [hb, nval_zero] at h; exact absurd h (not_le.2 (EReal.coe_lt_top _))
  rw [nval_of_ne hb, EReal.coe_le_coe_iff] at h ⊢
  have he' : (0 : ℝ) < e := Nat.cast_pos.2 he
  rw [hn, ← div_div, ← div_div, div_le_iff₀ hm, add_mul, div_mul_cancel₀ _ hm.ne']
  linarith

theorem refExp_vp_add_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r), (∀ σ, GoodEmb c σ → IsUnf (U σ)) → ∀ (x : ℝ) (G G₀ : WTZ E), Even G.2 → ∀ (cst k : ℝ) (q : ℕ), q.Prime → ∀ t : ∀ Z : Comp Xo c, TwSec U x Z G₀, (∀ Z (w : HeightOneSpectrum (𝓞 c.F)), ((q : ℕ) : 𝓞 c.F) ∈ w.asIdeal → (t Z).hi w - (⌊(t Z).lo w⌋ : ℝ) ≤ k * (vAdd w (q : c.F) : ℝ)) → refExp_vp U cst (G + G₀) q ≤ refExp_vp U cst G q + (k : EReal) := by
  intro E _ _ _ H Dw l Xo c r U hU x G G₀ hG cst k q hq t ht
  refine (refExp_vp_le_iff U).2 fun la T io e ho y hy φ hφ => ?_
  have h0 := (refExp_vp_le_iff U).1 (le_refl (refExp_vp U cst G q)) la T io e ho y hy φ hφ
  obtain ⟨Z, hZ⟩ := GlobalTheory.T.exists_component_integral_framedPoint_liesOn E H Dw l Xo c T io y
  have hv : (fun f => nval T.V e (evI y f)) ∈ valOn Z la.1 := ⟨PtV.mk la.1 ho y ⟨hy, hZ⟩ () trivial, rfl⟩
  have hm : 0 < vAdd la.1 (q : c.F) := vAdd_natCast_pos hq.ne_zero la.2
  have hq' : vV T.V (q : T.Fr) = (e : ℤ) * vAdd la.1 (q : c.F) := by
    rw [← map_natCast io q]; exact ho.2 _
  have hn : (((vV T.V (q : T.Fr)).toNat : ℕ) : ℝ) = e * (vAdd la.1 (q : c.F) : ℝ) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg (hq' ▸ mul_nonneg (Int.natCast_nonneg e) hm.le), hq']
    push_cast; rfl
  have hd : depthAt_vp U (G + G₀) q y ≤ depthAt_vp U G q y + (k : EReal) := by
    rw [← EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot _)) (Or.inl (EReal.coe_ne_top _))]
    refine le_iInf₂ fun f hf => ?_
    rw [EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot _)) (Or.inl (EReal.coe_ne_top _))]
    obtain ⟨g, hg, hle⟩ := GlobalTheory.T.exists_twistingSection_mul_lattice_value_le E H Dw l Xo c r U hU x G G₀ hG Z (t Z) la.1 _ hv f hf
    exact (iInf₂_le g hg).trans (nval_le_add_of_mul ho.1 (Int.cast_pos.2 hm) hn (ht Z la.1 la.2) hle)
  rw [add_right_comm]
  exact hd.trans (add_le_add h0 le_rfl)

end GlobalTheory.RefTwist

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseRingUnitsInvertPStatement
section
set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.base_ring_units_invert_p : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l' : Level H) (c' : Coeff l') (W : ValuationSubring ℂ) (p : ℕ), p.Prime → (p : ℂ) ∈ W.nonunits → ∀ (A : Type) [CommRing A] (β : c'.V W →+* A), IsUnit (p : A) → ∀ a : c'.V W, a ≠ 0 → IsUnit (β a) := by
  first | exact @GlobalTheory.CoeffUnit.isUnit_of_ne_zero | exact GlobalTheory.CoeffUnit.isUnit_of_ne_zero | (intros; apply GlobalTheory.CoeffUnit.isUnit_of_ne_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BasisTorsionOfWeilPairingFieldStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.basis_torsion_of_weilPairing_field : ∀ (h N : ℕ) (k : Type) [Field k] (S : Scheme.{0}) (x : Sp k ⟶ S) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : LB A.left) (z : kˣ) (e₀ e : (Fin h ⊕ Fin h → ℤ) → (Over.mk x ⟶ A)), L.IsLB → Odd N → IsPrimitiveRoot z N → (∀ a a', e₀ (a + a') = e₀ a * e₀ a') → (∀ a, e₀ a = 1 ↔ ∃ a', a = N • a') → (∀ g : Over.mk x ⟶ A, g ^ N = 1 → ∃ a, e₀ a = g) → (∀ a a', e (a + a') = e a * e a') → (∀ a, e a ^ N = 1) → (∀ a a', Out.WeilIs A L N (e a) (e a') (unitOn (z ^ (2 * omegaStd a a')))) → (∀ a, e a = 1 ↔ ∃ a', a = N • a') ∧ ∀ g : Over.mk x ⟶ A, g ^ N = 1 → ∃ a, e a = g := by
  first | exact @GlobalTheory.GeomBasis.basis_of_weil | exact GlobalTheory.GeomBasis.basis_of_weil | (intros; apply GlobalTheory.GeomBasis.basis_of_weil <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BigCellEigenbasisCombinationCoeffUnique
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LogPole

open GlobalTheory.Reg GlobalTheory.FlagMod
open MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv mkT tanM_ext tv_mem actR)

attribute [local instance] Over.cartesianMonoidalCategory

theorem cell_eigComb_coeff_unique : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c) (U : TF.Y.X.affineOpens) (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)), IsEigBasis TF U e v → ∀ (W : (Y₀ TF.X Z).Opens) (k : TF.X.F.J) (L N : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) Γ(Y₀ TF.X Z, W)), IsCell TF Z U e v W k L N → ∀ (S : Type) [CommRing S] (zw : Sp S ⟶ Y₀ TF.X Z) (hzw : ⊤ ≤ zw ⁻¹ᵁ W) (x : Sp S ⟶ TF.Y.X) (hx : zw ≫ toBase TF Z = x) (hUx : ⊤ ≤ x ⁻¹ᵁ U.1) (σ : E →+* ℂ) (a b : Fin (Dw.mult σ) → S) (w' : Sp (DualNumber S) ⟶ TF.Y.t.G.left), IsCombAtG TF.Y.t x (fun j => spMap (dualMap (ev x U.1 hUx)) ≫ v (e ⟨σ, j⟩)) a w' → IsCombAtG TF.Y.t x (fun j => spMap (dualMap (ev x U.1 hUx)) ≫ v (e ⟨σ, j⟩)) b w' → a = b := by
  intro E _ _ _ H Dw l Xo c TF Z U n e v hv W k L N hC S _ zw hzw x hx hUx σ a b w' ha hb
  subst hx
  obtain ⟨-, -, hWk, hLz, hLu, hNz, hN1, hcomb⟩ := hC
  have hk : ⊤ ≤ (zw ≫ inc₀ TF.X Z) ⁻¹ᵁ TF.X.F.U k := fun p hp => hWk (hzw hp)
  have hxx : (zw ≫ inc₀ TF.X Z) ≫ TF.X.π = zw ≫ toBase TF Z := Category.assoc _ _ _
  have hvT : ∀ m, IsTanAtG TF.Y.t (zw ≫ toBase TF Z) (spMap (dualMap (ev (zw ≫ toBase TF Z) U.1 hUx)) ≫ v m) :=
    fun m => GlobalTheory.LieMet.isTan_map _ (spMap_ev _ U.2 hUx) (hv.1 m)
  let f : Fin (Dw.mult σ) → TanM (zw ≫ toBase TF Z) TF.Y.t.G := fun j => GlobalTheory.LieMet.tanOf (hvT (e ⟨σ, j⟩))
  have uniq : ∀ {w₁ w₂ : Sp (DualNumber S) ⟶ TF.Y.t.G.left} (cf : Fin (Dw.mult σ) → S),
      IsCombAtG TF.Y.t (zw ≫ toBase TF Z) (fun j => (tv (f j)).left) cf w₁ →
      IsCombAtG TF.Y.t (zw ≫ toBase TF Z) (fun j => (tv (f j)).left) cf w₂ → w₁ = w₂ := by
    intro w₁ w₂ cf h₁ h₂
    obtain ⟨u₁, hu₁, hw₁⟩ := h₁
    obtain ⟨u₂, hu₂, hw₂⟩ := h₂
    have hu : u₁ = u₂ := funext fun i => Over.OverMorphism.ext ((hu₁ i).trans (hu₂ i).symm)
    rw [← hw₁, ← hw₂, hu]
  have hsum : ∀ cf : Fin (Dw.mult σ) → S,
      IsCombAtG TF.Y.t (zw ≫ toBase TF Z) (fun j => (tv (f j)).left) cf (tv (∑ j, cf j • f j)).left :=
    fun cf => (GlobalTheory.LieMet.isComb_iff f cf _).2 rfl
  have hab : ∑ j, a j • f j = ∑ j, b j • f j :=
    GlobalTheory.LieMet.tan_ext ((uniq a (hsum a) ha).trans (uniq b (hsum b) hb).symm)
  let V := TF.X.F.vecAt k (zw ≫ inc₀ TF.X Z) hk hxx σ
  let C : Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) S := (L σ * N σ).map (ev zw W hzw)
  have hV : ∀ i, V i = ∑ j, C i j • f j := fun i =>
    (GlobalTheory.LieMet.isComb_iff f _ _).1 (hcomb S zw hzw hUx hk hxx σ i)
  have hCdet : IsUnit C.det := by
    have hm : C = (L σ).map (ev zw W hzw) * (N σ).map (ev zw W hzw) := Matrix.map_mul
    rw [hm, Matrix.det_mul]
    refine IsUnit.mul ?_ ?_
    · rw [Matrix.det_of_lowerTriangular _ (fun i j h => by
        show ev zw W hzw (L σ i j) = 0
        rw [hLz σ i j (OrderDual.toDual_lt_toDual.1 h), map_zero])]
      exact IsUnit.prod_univ_iff.2 fun i => (hLu σ i).map (ev zw W hzw)
    · rw [Matrix.det_of_upperTriangular (M := (N σ).map (ev zw W hzw)) (fun i j h => by
        show ev zw W hzw (N σ i j) = 0
        rw [hNz σ i j h, map_zero])]
      refine IsUnit.prod_univ_iff.2 fun i => ?_
      show IsUnit (ev zw W hzw (N σ i i))
      rw [hN1, map_one]; exact isUnit_one
  have hf' : ∀ j, f j = ∑ i, C⁻¹ j i • V i := fun j => by
    simp only [hV, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_smul]
    have e2 : ∀ l, (∑ i, C⁻¹ j i * C i l) = (1 : Matrix _ _ S) j l := fun l => by
      rw [← Matrix.nonsing_inv_mul _ hCdet, Matrix.mul_apply]
    simp only [e2, Matrix.one_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have key : ∀ cf : Fin (Dw.mult σ) → S, ∑ j, cf j • f j = ∑ i, Matrix.vecMul cf C⁻¹ i • V i := fun cf => by
    simp only [hf', Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_smul, Matrix.vecMul, dotProduct]
  have hg : Matrix.vecMul a C⁻¹ = Matrix.vecMul b C⁻¹ := funext
    (Fintype.linearIndependent_iffₛ.1 (TF.X.F.linearIndependent_vecAt k _ hk hxx σ) _ _
      (by rw [← key, ← key, hab]))
  calc a = Matrix.vecMul (Matrix.vecMul a C⁻¹) C := by
        rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hCdet, Matrix.vecMul_one]
    _ = Matrix.vecMul (Matrix.vecMul b C⁻¹) C := by rw [hg]
    _ = b := by rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hCdet, Matrix.vecMul_one]

end GlobalTheory.LogPole
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BigCellFramedPointVectorsLowerTriangularEigenbas
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

set_option autoImplicit false

noncomputable section

theorem GlobalTheory.LogPole.frVec_cell_comb : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c) (U : TF.Y.X.affineOpens) (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)), IsEigBasis TF U e v → ∀ (W : (Y₀ TF.X Z).Opens) (k : TF.X.F.J) (L N : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) Γ(Y₀ TF.X Z, W)), IsCell TF Z U e v W k L N → ∀ (S : Type) [CommRing S] [Algebra c.F S] (w : FrPt Xo c S) (zw : Sp S ⟶ Y₀ TF.X Z) (hzw : ⊤ ≤ zw ⁻¹ᵁ W) (x : Sp S ⟶ TF.Y.X) (hx : frX w ≫ TF.Y.j = x) (hUx : ⊤ ≤ x ⁻¹ᵁ U.1), zw ≫ inc₀ TF.X Z = TF.X.ptY w → ∃ B : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) S, (∀ σ i j, i < j → B σ i j = 0) ∧ (∀ σ i, IsUnit (B σ i i)) ∧ ∀ σ i, IsCombAtG TF.Y.t x (fun j => spMap (dualMap (ev x U.1 hUx)) ≫ v (e ⟨σ, j⟩)) (fun j => (B σ * (L σ * N σ).map (ev zw W hzw)) i j) (tv (frVec TF.Y w hx σ i)).left := by
  intro E _ _ _ H Dw l Xo c TF Z U n e v hv W k L N h S _ _ w zw hzw x hx hUx hpt
  have hl : TF.X.F.Lies (zw ≫ inc₀ TF.X Z) w := hpt ▸ TF.X.lies_ptY w
  have hk : ⊤ ≤ (zw ≫ inc₀ TF.X Z) ⁻¹ᵁ TF.X.F.U k := GlobalTheory.FlagMod.le_preimage_map _ h.2.2.1 hzw
  have hxz' : (zw ≫ inc₀ TF.X Z) ≫ TF.X.π = zw ≫ toBase TF Z := Category.assoc _ _ _
  have hxz : zw ≫ toBase TF Z = x := hxz'.symm.trans (hl.1.trans hx)
  subst hxz
  obtain ⟨Q, hQ⟩ := TF.X.top.exists_chartFr (GlobalTheory.FlagMod.frX_snd w) hl.1 k hk
  obtain ⟨t, ht⟩ := hQ.exists_frBor hl
  choose b hb hdiag hsum using fun σ =>
    GlobalTheory.FlagMod.frVec_of_frBor (M := (TF.X.F.M k).toMChart) (TF.X.F.inM hk hxz') (hQ.over.trans hxz') hx ht σ
  refine ⟨fun σ i j => b σ j i, fun σ i j hij => hb σ hij, fun σ i => by show IsUnit (b σ i i); rw [hdiag]; exact Units.isUnit _,
    fun σ i => ?_⟩
  have hv' : ∀ j, IsTanAtG TF.Y.t (zw ≫ toBase TF Z)
      (spMap (dualMap (ev (zw ≫ toBase TF Z) U.1 hUx)) ≫ v j) := by
    intro j
    have h0 := GlobalTheory.FactorDepth.isTanAtG_map TF.Y.t (ev (zw ≫ toBase TF Z) U.1 hUx) (hv.1 j)
    rwa [LogKS.chart, GlobalTheory.FlagMod.spMap_ev _ U.2 hUx] at h0
  have hcell := h.2.2.2.2.2.2.2 S zw hzw hUx hk hxz' σ
  have h2 : IsCombAtG TF.Y.t (zw ≫ toBase TF Z)
      (fun j => (tv (TF.X.F.vecAt k (zw ≫ inc₀ TF.X Z) hk hxz' σ j)).left) (fun j => b σ j i)
      (tv (frVec TF.Y w hx σ i)).left := by
    rw [GlobalTheory.LieMet.isComb_iff, hsum σ i, hQ.frVec_eq hxz' (hQ.over.trans hxz') σ]
  have h3 := GlobalTheory.TangentLinear.isCombAtG_mulVec _ (fun j => hv' (e ⟨σ, j⟩)) _
    (Matrix.of fun m j => ev zw W hzw ((L σ * N σ) j m)) (fun j => b σ j i) _ (fun j => hcell j) h2
  convert h3 using 1
  funext m
  show ∑ j, b σ j i * ev zw W hzw ((L σ * N σ) j m) = ∑ j, ev zw W hzw ((L σ * N σ) j m) * b σ j i
  exact Finset.sum_congr rfl fun j _ => _root_.mul_comm _ _
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomConstantOfBaseStageStatement
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

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bottom_constant_of_base_stage : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ), IsStdChar D W.ψ (-1) →
    NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (A A' WW : HSp D) (X : Tri T A A' WW) (B B' WW₁ : HSp D) (Y : Tri T B B' WW₁) (c : T → ℂ),
      IsBottomTri W i j X → GlobalTheory.SqTower.IsStageC W i j 0 0 Y → Y.IsConst W.ψ W.θ c → ∃ v : T → ℂ,
        X.IsConst W.ψ W.θ (fun t => v t * c t) ∧
        ∀ t, v t ≠ 0 ∧ ∃ ζ : D.what₂.LL, GlobalTheory.Square.IsAwayUnit (Qn G t) ζ ∧ v t = D.what₂.embLL ζ * v μ₀ := by
  first | exact @GlobalTheory.SqTower.bottom_const_ratio | exact GlobalTheory.SqTower.bottom_const_ratio | (intros; apply GlobalTheory.SqTower.bottom_const_ratio <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomTriangleArchimedeanConstantStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bottom_triangle_archimedean_constant : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    (∀ D, GlobalTheory.NormSum.Inp D) → GlobalTheory.SqTop.BotSmall →
    GlobalTheory.SqTop.GBig fun {D} T _ _ G _ _ _ _ => ∀ (W : G.Weil), IsStdChar D W.ψ (-1) → ∀ (i j : Fin D.R.m) (A A' WW : HSp D)
      (X : Tri T A A' WW) (δ t0 : ℂ), IsBottomTri W i j X → X.rW.β = 1 →
      ∃ (r : ℂ) (rc : ℝ) (κ : ℂ), r ≠ 0 ∧ (∀ τ, rc * ‖r‖ ^ 2 = 2 * ‖tauE D τ D.host.xi0‖) ∧ κ ≠ 0 ∧
        ∀ (s : T) (Q : ℕ) (P P' : Pair D ⊤ δ t0 Q), IsBottom G s i j (GlobalTheory.SqTop.modT G s) P P' →
        ∃ u : ℂ, u ≠ 0 ∧ u ∈ Qbar ∧ (∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ GlobalTheory.SqTop.Qn G s → ∀ lam : Qbar →+* ℂ_[p], ‖lamC lam u‖ = 1) ∧
          ∀ (ea : P.a = A.rank) (ed : P.d = WW.rank) (h : GA D P.d) (g : GA D WW) (x : GA D P.a) (y : GA D A),
            GlobalTheory.BotFormula.IsFinPt WW g h → GlobalTheory.BotFormula.IsFinPt A y x →
            GlobalTheory.AdForm.xiN W.θ A WW ea.symm ed.symm r rc (fun w => starRingEnd ℂ (X.ω s (y, g) (X.f s) w)) =
              (κ * starRingEnd ℂ u) • P.W.Om x h P.F := by
  first | exact @GlobalTheory.ReadMatch.bottom_reading | exact GlobalTheory.ReadMatch.bottom_reading | (intros; apply GlobalTheory.ReadMatch.bottom_reading <;> assumption)
end

