import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0013
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0012
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Formalism.LocalToGlobal.ProjectiveLattices.IsGenFrGenFr
import Formalism.LocalToGlobal.ProjectiveLattices.ChartDirectionsIntegral
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
import Formalism.LocalToGlobal.ProjectiveLattices.GenFrPf
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointReducedFromTestRing
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0021
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0212
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0140
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0010
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0087
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0093
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0078
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0041
import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0026
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0023
import Formalism.LocalToGlobal.ProjectiveLattices.DatProofs
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0051
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0031
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0058
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0074
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0076
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FramedPointsLiftToLevelCover
import Development.AbelianVarietyTheory.Proofs.HeightProofs.NoCommonZeroIffOfSec
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0025
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.FromTestIffOfValAtCx
import Formalism.LocalToGlobal.ProjectiveLattices.BetaAtSymm
import Formalism.LocalToGlobal.ProjectiveLattices.OneLtAbsNormReal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0015

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CompNonemptyFiniteGenFrTrdeg
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj

theorem GlobalTheory.Exist.comp_nonempty_finite_genFr_trdeg : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), 1 ≤ Dw.p + Dw.q → Nonempty (Comp Xo c) ∧ Finite (Comp Xo c) ∧ ∃ h : GenFrEx Xo c, GenFromTest Xo c h ∧ (∀ Z, evC h Z 1 = 1) ∧ ∀ Z : Comp Xo c, Algebra.trdeg c.F (kap Z) = Dw.dim := by
  intro E _ _ _ H Dw l Xo c h1
  have hB : Out.SecBaseChangeSt := GlobalTheory.allSixLaws.1.secBaseChange
  have hT : Out.SecTwistSt := GlobalTheory.allSixLaws.2.1.secTwist
  have hA : AllTest Xo c := GlobalTheory.Frames.allTest_of_secBaseChange hB E H Dw l Xo c
  have h : GenFrEx Xo c := genFrEx_of hT
  have hg : GenFromTest Xo c h := fun Z => hA _ _
  obtain ⟨x⟩ := (GlobalTheory.PeriodExists.typeFn_period_exist E H Dw).2.2 GlobalTheory.closing_of_abelianSchemeLaws h1 l Xo c
  exact ⟨⟨⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩⟩,
    CompFin.finite_comp Xo c, h, hg, fun Z => evalAt_one _ _ _ (hg Z),
    (GlobalTheory.Reg.kap_fg_trdeg E H Dw l Xo c).2⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.EvLawsGenFrNonemptyComp
section
namespace GlobalTheory.Reg

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain in
private theorem nonempty_irreducibleComponents_of_point {X : Type*} [TopologicalSpace X] (x : X) :
    Nonempty (irreducibleComponents X) :=
  ⟨⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩⟩

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain in

theorem _root_.GlobalTheory.Reg.evLaws_genFr_nonempty_comp : ∀ (E : Type) [Field E] [NumberField E]
    [IsCMField E] (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (l : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l)
    (c : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l), _root_.GlobalTheory.Reg.EvLaws Xo c ∧ _root_.Formalism.L2.Pj.IntDiagUnit Xo c ∧ _root_.Formalism.L2.Pj.GenFrEx Xo c ∧
      (1 ≤ Dw.p + Dw.q → Nonempty (_root_.Formalism.L2.Pj.Comp Xo c)) := by
  intro E _ _ _ H Dw l Xo c
  have hsec : _root_.ReciprocityTheory.ChartRestriction.G.Out.SecBaseChangeSt := _root_.GlobalTheory.allSixLaws.1.secBaseChange
  have htw : _root_.ReciprocityTheory.ChartRestriction.G.Out.SecTwistSt := _root_.GlobalTheory.allSixLaws.2.1.secTwist
  obtain ⟨-, -, hwd, hwt, hdiag, -, -⟩ :=
    _root_.GlobalTheory.Frames.algebraic_laws hsec E H Dw l Xo c
  refine ⟨⟨hwd, _root_.GlobalTheory.Frames.allTest_of_secBaseChange hsec E H Dw l Xo c, hwt, ?_⟩, hdiag,
    _root_.Formalism.L2.Pj.genFrEx_of htw, ?_⟩
  · intro S T _ _ _ _ φ y
    exact _root_.GlobalTheory.Frames.FramedBaseChange.exists_frMap hsec E H Dw l Xo c S T φ y
  · intro hpq
    obtain ⟨x⟩ := (_root_.GlobalTheory.PeriodExists.typeFn_period_exist E H Dw).2.2
      _root_.GlobalTheory.closing_of_abelianSchemeLaws hpq l Xo c
    unfold _root_.Formalism.L2.Pj.Comp
    exact nonempty_irreducibleComponents_of_point x

end GlobalTheory.Reg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsMemberDictionaryContextGoodEmbedding
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member

namespace GlobalTheory.Member

theorem hostCMType_neg_constant_im_neg (D : D7) (τ : D.host.E →+* ℂ)
    (hτ : τ D.host.sqrtMinusD = D.host.φ₀ D.host.sqrtMinusD) : (τ (-D.host.xi0)).im < 0 := by
  have h1 := xi0_embedding_im_pos D τ ((mem_cm_type_iff D τ).2 hτ)
  have hφ : D.host.φ₀ D.host.sqrtMinusD = Complex.I * (Real.sqrt D.host.d : ℂ) := D.host.φ₀_mem
  have hpos : 0 < (D.host.φ₀ D.host.sqrtMinusD).im := by
    rw [hφ]
    have hd : (0 : ℝ) < D.host.d := by exact_mod_cast d_pos D
    simpa using hd
  rw [if_pos hpos, Int.cast_one, _root_.one_mul] at h1
  rw [map_neg, Complex.neg_im]
  linarith

theorem exists_family_models (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (V : HSp D)
    (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) (hι : IotaOK Dw V ι) (hpos : 1 ≤ Dw.p + Dw.q)
    (hσ : GoodEmb c σ) :
    ∃ (g : ℕ) (e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin (Dw.mult τ))
      (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1))
      (M : GlobalTheory.FrameUnif.ModelsOf F V.rank), GlobalTheory.FrameUnif.ModelBase M ∧ ∀ k, ModelW V rfl (M.X k) := by
  classical
  let e := (Fintype.equivFin (Σ τ : D.host.E →+* ℂ, Fin (Dw.mult τ))).symm
  have hty := (GlobalTheory.Relab.relab_good D.host.E H l c σ hσ).2.2.2 Dw _ e
  obtain ⟨F⟩ := GlobalTheory.closing_of_abelianSchemeLaws D.host.E H Dw l Xo
    (σ.comp (IntermediateField.inclusion c.le).toRingHom) _ (fun j => relab c σ (e j).1) hpos hσ hty
  obtain ⟨-, -, -, -, -, hcF, -, hherm, hdet, hhT, -⟩ := GlobalTheory.Member.latHat_eq_hat_and_gram D V
  have hξ : cc (-D.host.xi0) = -(-D.host.xi0) := by rw [cc, map_neg, conj_xi0_alt]
  have hsp : Submodule.span D.host.E (Set.range ι) = ⊤ := by
    rw [← LinearMap.coe_range, hι.emb.2]
    exact (GlobalTheory.Member.latG_lattice_and_completion D V 1).2.1
  have hG : ∀ a b, cc ((-V.gramᵀ) a b) = (-V.gramᵀ) b a := fun a b => by
    rw [Matrix.neg_apply, Matrix.neg_apply, cc, map_neg, ← hherm a b, hcF, cc]
  have hd : (-V.gramᵀ).det ≠ 0 := by
    rw [Matrix.det_neg]
    exact mul_ne_zero (pow_ne_zero _ (by simp)) hdet
  have hEF : ∀ x y, ((Dw.EF x y : ℤ) : ℚ) =
      Algebra.trace ℚ D.host.E (-(-D.host.xi0) * herm (-V.gramᵀ) (ι x) (ι y)) := fun x y => by
    have h1 : Dw.EF x y = -Dw.EF y x := by
      have h := Dw.alt (x + y)
      simp only [map_add, LinearMap.add_apply, Dw.alt] at h
      linarith
    rw [h1, Int.cast_neg, hι.isom y x, hhT, ← map_neg]
    congr 1
    ring
  obtain ⟨M, hM, -, hMG⟩ := GlobalTheory.ModelsExist.exists_modelsOf GlobalTheory.QNorm.hasseNormSt D.host.E H Dw l Xo _ _ _ F
    V.rank (-D.host.xi0) (-V.gramᵀ) ι hξ
    (fun τ hτ => hostCMType_neg_constant_im_neg D τ (by rw [← hι.rt0, ← hι.rt, hτ])) ⟨hι.emb.1, hsp, hG, hd, hEF⟩
  exact ⟨_, e, F, M, hM, fun k => ⟨(hMG k).1, (hMG k).2⟩⟩

theorem exists_ctx : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (V : HSp D) (r : ℕ) (hr : V.rank = r) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)), IotaOK Dw V ι → 1 ≤ Dw.p + Dw.q → l.A = 1 → GoodEmb c σ → (∃ C : Ctx Xo c σ V r, C.OK ∧ C.ι = ι) ∧ (∀ C : Ctx Xo c σ V r, C.OK → GlobalTheory.FrameUnif.NegXi C.M) ∧ ∀ x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ, (∀ τ : D.host.E →+* ℂ, τ (H.rt : D.host.E) = H.rt0 → gram τ (-(Matrix.reindex (finCongr hr) (finCongr hr) V.gram)ᵀ) (x₀ τ) = Matrix.diagonal fun a : Fin r => ((sgn Dw.q (a : ℕ) : ℝ) : ℂ)) → ∃ C : Ctx Xo c σ V r, C.OK ∧ C.ι = ι ∧ C.x₀ = x₀ := by
  intro D H Dw l Xo c σ V r hr ι hι hpos hA hσ
  subst hr
  obtain ⟨g, e, F, M, hM, hW⟩ := exists_family_models D H Dw l Xo c σ V ι hι hpos hσ
  obtain ⟨θ, hθ⟩ := (GlobalTheory.Member.infiniteAdele_bijective D).1
  have key : ∀ x₀ : (D.host.E →+* ℂ) → Matrix (Fin V.rank) (Fin V.rank) ℂ,
      (∀ τ : D.host.E →+* ℂ, τ (H.rt : D.host.E) = H.rt0 →
        gram τ (-(Matrix.reindex (finCongr rfl) (finCongr rfl) V.gram)ᵀ) (x₀ τ) =
          Matrix.diagonal fun a : Fin V.rank => ((sgn Dw.q (a : ℕ) : ℝ) : ℂ)) →
      ∃ C : Ctx Xo c σ V V.rank, C.OK ∧ C.ι = ι ∧ C.x₀ = x₀ := fun x₀ hx =>
    ⟨⟨rfl, g, e, F, M, ι, θ, x₀⟩, ⟨hι, hpos, hA, hσ, hM, hW, hθ, fun k τ hτ => by
      show gram τ (M.X k).Gm (x₀ τ) = Matrix.diagonal fun a : Fin V.rank => ((sgn (M.X k).p0 (a : ℕ) : ℝ) : ℂ)
      rw [(hW k).1, (hM.type k).1]
      exact hx τ (((hM.type k).2 τ).1 hτ)⟩, rfl, rfl⟩
  refine ⟨?_, fun C hC k τ hτ => ?_, key⟩
  · classical
    let k : Fin F.n := ⟨0, F.n_pos⟩
    obtain ⟨C, hC, h, -⟩ := key
      (fun τ => if h : τ ∈ (M.X k).Ψ then ((M.X k).signature ⟨τ, h⟩).choose else 1) fun τ hτ => by
        have h := ((hM.type k).2 τ).2 hτ
        rw [dif_pos h, ← (hW k).1, ← (hM.type k).1]
        exact ((M.X k).signature ⟨τ, h⟩).choose_spec.2
    exact ⟨C, hC, h⟩
  · rw [(hC.modelW k).2]
    exact hostCMType_neg_constant_im_neg D τ (by rw [← hι.rt0, ← hι.rt, ((hC.base.type k).2 τ).1 hτ])

end GlobalTheory.Member
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsValueBelow
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.FrameLift
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ClassSumCompare

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {n : ℕ} (d : DeltaDat Xo c n)

theorem exists_frUnder {S : Type} [CommRing S] [Algebra c.F S] [Algebra d.c₂.F S]
    (hc : ∀ a : c.F, algebraMap d.c₂.F S (d.eF a) = algebraMap c.F S a) (y₂ : FrPt d.Xo₂ d.c₂ S)
    (hx : (y₂.x ≫ d.r) ≫ Xo.s = sOf c S) : ∃ y : FrPt Xo c S, FrOver d y₂ y := by
  have hc' : ∀ τ a, algebraMap d.c₂.F S (embK d.c₂ τ a) = algebraMap c.F S (embK c τ a) := fun τ a => by
    rw [← embK_eF, hc]
  have e : y₂.x ≫ d.r = y₂.x ≫ d.r := rfl
  obtain ⟨w, hw, hw', -⟩ := d.m.lin
  obtain ⟨p, k, p₁, p₂, hk, hk'⟩ := exists_pm_iso d.m e
  have hL := Xo.univ.t.PP.isLB
  have hL₂ := d.Xo₂.univ.t.PP.isLB
  obtain ⟨s, hs⟩ := exists_up hL hL₂ hw p₁ hk hk' y₂.s
  refine ⟨⟨y₂.x ≫ d.r, hx, fun τ i => y₂.u τ i ≫ d.m.φ, fun τ i => (tan_iff d.m e (y₂.tan τ i).1).1 (y₂.tan τ i),
    fun τ i => (eig_iff d.m τ (hc' τ) (y₂.tan τ i).1).1 (y₂.eig τ i), fun τ v hv hv' => ?_, s, fun s' => ?_⟩,
    (frOver_iff d _ _).2 ⟨e, fun _ _ => rfl, w, p, ⟨hw, hw'⟩, p₁, p₂, hs⟩⟩
  · obtain ⟨v₂, rfl, h₂⟩ := exists_lift d.m e hv.1
    refine (existsUnique_congr fun a => ?_).1
      (y₂.basis τ v₂ ((tan_iff d.m e h₂).2 hv) ((eig_iff d.m τ (hc' τ) h₂).2 hv'))
    exact comb_iff d.m e (fun i => (y₂.tan τ i).1) a h₂
  · obtain ⟨s₂', hs'⟩ := exists_down hL hL₂ hw p₁ s'
    refine (existsUnique_congr fun a => ?_).1 (y₂.gen s₂')
    exact (scal_iff (fst (Over.mk y₂.x) d.Xo₂.univ.t.G).left (toΓ S a) y₂.s s₂').trans
      ((rel_scal_iff hL hL₂ p₁ hk p₂ (toΓ S a) hs hs').trans
        (scal_iff (fst (Over.mk (y₂.x ≫ d.r)) Xo.univ.t.G).left (toΓ S a) s s').symm)

theorem rel_unique {A A₂ Y Y₂ : Scheme.{0}} {L : LB A} {L₂ : LB A₂} {φ : A₂ ⟶ A} (hL₂ : L₂.IsLB)
    {w : LB.Iso L₂ (L.pull φ)} {q₂ : Y₂ ⟶ A₂} {q : Y ⟶ A} {p : Y₂ ⟶ Y} (hp : p ≫ q = q₂ ≫ φ) {k : Y ⟶ Y₂}
    (hk : k ≫ p = 𝟙 _) {s₂ : LB.Sec (LOne L₂ q₂)} {s s' : LB.Sec (LOne L q)} (H : Rel w p s₂ s)
    (H' : Rel w p s₂ s') : s = s' := by
  have : s.f = s'.f := funext fun i => by
    obtain ⟨i, rfl⟩ := exists_const i
    refine fn_ext fun z hz => ?_
    obtain ⟨j, hj⟩ := exists_chart hL₂ (q₂ (k z))
    have hi' : φ (q₂ (k z)) ∈ L.U i :=
      (congrArg (· ∈ L.U i) (pt_eq hp (k z))).mp ((congrArg (fun t => q t ∈ L.U i) (pt_eq hk z)).mpr (mem_ch.1 hz))
    have a := (H Y k z i j hi' hj).trans (H' Y k z i j hi' hj).symm
    rw [hk] at a
    exact a
  cases s; cases s'
  congr

theorem frUnder_unique {S : Type} [CommRing S] [Algebra c.F S] [Algebra d.c₂.F S] {y₂ : FrPt d.Xo₂ d.c₂ S}
    {y z : FrPt Xo c S} (h : FrOver d y₂ y) (h' : FrOver d y₂ z) : y = z := by
  obtain ⟨e, hu, w, p, hw, p₁, p₂, H⟩ := (frOver_iff d _ _).1 h
  obtain ⟨e', hu', w', p', hw', p₁', p₂', H'⟩ := (frOver_iff d _ _).1 h'
  obtain rfl : w = w' := rigidified_iso_unique GlobalTheory.abelianSchemeLaws_all.1.globalFns (UnivPol.pol d.Xo₂)
    Xo.univ.t.PP.isLB d.m.φ w w' hw.1 hw'.1 _ _ hw.2 hw'.2
  obtain ⟨x, xo, u, t, ei, b, s, g⟩ := y
  obtain ⟨x', xo', u', t', ei', b', s', g'⟩ := z
  dsimp only at e e' hu hu' p p' p₁ p₂ p₁' p₂' H H'
  obtain rfl : x = x' := e.symm.trans e'
  obtain rfl : u = u' := funext fun τ => funext fun i => (hu τ i).symm.trans (hu' τ i)
  obtain rfl : p = p' := pm_ext (p₁.trans p₁'.symm) (p₂.trans p₂'.symm)
  obtain ⟨q, k, q₁, q₂, hk, -⟩ := exists_pm_iso d.m e
  obtain rfl : p = q := pm_ext (p₁.trans q₁.symm) (p₂.trans q₂.symm)
  obtain rfl : s = s' := rel_unique d.Xo₂.univ.t.PP.isLB p₁ hk H H'
  rfl

end GlobalTheory.ClassSumCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PsiCoordOfIsPullDegId
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SameCoord

set_option maxHeartbeats 1600000 in

theorem psiCoord_of_isPullDeg_id {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {D D' : DegPre R}
    (hD : IsPullDeg (RingHom.id R) D D') (x : D'.X) (r : R) (hr : PsiCoord D (hD.xe x) r) :
    ∃ u : Rˣ, PsiCoord D' x (u * r) := by
  obtain ⟨j, hj, h, hr⟩ := hr
  have hs := specOf_id R
  set Φ := hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf (RingHom.id R)) with hΦ
  have hc : (D'.c x).left ≫ Φ = (D.c (hD.xe x)).left := by
    rw [hΦ, hD.c_pr x]
    exact (congrArg (· ≫ (D.c (hD.xe x)).left) hs).trans (Category.id_comp _)
  obtain ⟨q, hq⟩ := exists_chart D'.P.isLB ((D'.c x).left (closedPoint R))
  have hq' : (⊤ : (Spec (CommRingCat.of R)).Opens) ≤ (D'.c x).left ⁻¹ᵁ D'.P.L.U q :=
    ((IsLocalRing.closedPoint_mem_iff _).1 hq).ge
  have hp : ∀ y : Spec (CommRingCat.of R), Φ ((D'.c x).left y) ∈ D.P.L.U (j PUnit.unit) := fun y =>
    (congrArg (fun g => g y ∈ D.P.L.U (j PUnit.unit)) hc).mpr (hj trivial)
  have hV : (⊤ : (Spec (CommRingCat.of R)).Opens) ≤
      (D'.c x).left ⁻¹ᵁ ((D.P.L.pull Φ).U (fun _ => j PUnit.unit) ⊓ D'.P.L.U q) := fun y _ =>
    ⟨mem_pull.2 (hp y), hq' trivial⟩
  let u₀ : Γ(Spec (CommRingCat.of R), ⊤)ˣ := res hV (pullU (D'.c x).left _ (hD.w.s (fun _ => j PUnit.unit, q)))
  let u : Rˣ := Units.map (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom.toMonoidHom u₀
  have hu : DegPre.toOpen (R := R) ⊤ u = u₀.val := by
    show ((Spec (CommRingCat.of R)).presheaf.map (𝟙 _)).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
      ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom u₀.val)) = _
    rw [CategoryTheory.Functor.map_id]
    exact congrArg (fun g => g.hom u₀.val) (Scheme.ΓSpecIso (CommRingCat.of R)).hom_inv_id
  have h' : jK R ⁻¹ᵁ ⊤ ≤ (LB.LinComb D'.P.L (K := PUnit) (fun _ => D'.xK x) (fun _ => -1)).U (fun _ => q) :=
    fun z _ => Set.mem_iInter.2 fun _ => hq' (x := jK R z) trivial
  refine ⟨u, fun _ => q, hq', h', ?_⟩
  apply TopCat.Presheaf.section_ext (TK R).left.sheaf
  intro z hz
  have hF : jFK (R := R) (FractionRing R) = 𝟙 _ := by
    show Spec.map (CommRingCat.ofHom (RingHom.id _)) = _
    simp
  have hFz : jFK (R := R) (FractionRing R) z = z := by rw [hF]; rfl
  have m₁ : Φ (D'.xK x (jFK (R := R) (FractionRing R) z)) ∈ D.P.L.U (j PUnit.unit) := by
    rw [hFz]; exact hp (jK R z)
  have m₂ : D'.xK x (jFK (R := R) (FractionRing R) z) ∈ D'.P.L.U q := by
    rw [hFz]; exact hq' (x := jK R z) trivial
  have m₃ : D.xK (hD.xe x) (jFK (R := R) (FractionRing R) z) ∈ D.P.L.U (j PUnit.unit) := by
    rw [hFz]; exact hj (x := jK R z) trivial
  have pm := pmaps_psi hD (FractionRing R) (by
    have : spMap (RingHom.id R) = 𝟙 _ := hs
    rw [this, Category.comp_id]) x _ (𝟙 _) z j (fun _ => q) (fun _ => m₁) (fun _ => m₂)
  rw [Category.comp_id, Fintype.prod_unique] at pm
  have pm' := (gm_pullGen D.P.L (fun _ : PUnit => D.xK (hD.xe x)) _ (D.psi (hD.xe x)) (jFK (R := R) (FractionRing R)) (𝟙 _) z j
    (Set.mem_iInter.2 fun _ => m₃)).symm.trans (pm.trans (congrArg (_ * ·)
      (gm_pullGen D'.P.L (fun _ : PUnit => D'.xK x) _ (D'.psi x) (jFK (R := R) (FractionRing R)) (𝟙 _) z (fun _ => q)
    (Set.mem_iInter.2 fun _ => m₂))))
  rw [hF, Category.comp_id, Category.id_comp, Category.id_comp, zpow_neg_one, eq_inv_mul_iff_mul_eq] at pm'
  have a₁ : gm (jK R) z ⊤ u₀ = gw hD.w (D'.xK x) z (j PUnit.unit) q :=
    (gm_res (jK R) z hV trivial _).trans (gm_pull (jK R) (D'.c x).left z _ (hV (x := jK R z) trivial) _)
  have a₂ := gm_res (𝟙 (TK R).left) z h hz ((D.psi (hD.xe x)).s j)
  have a₃ := gm_res (𝟙 (TK R).left) z h' hz ((D'.psi x).s (fun _ => q))
  have k := congrArg Units.val ((congrArg₂ (fun a b : ((TK R).left.presheaf.stalk z)ˣ => a * b) a₁ a₂).trans (pm'.trans a₃.symm))
  rw [Units.val_mul, gm_val (jK R) z ⊤ trivial, gm_val _ z _ hz, gm_val _ z _ hz] at k
  rw [map_mul, map_mul, hu, hr]
  exact (map_mul _ _ _).trans k

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

set_option maxHeartbeats 1600000 in

theorem exists_move (hU : UnifBaseChangeSt) (h5 : Laws5) {R : Type} [CommRing R] [IsDomain R] {I : Ideal R}
    (hR : AdmBase R I) {t t' : SAB H (Sp R)} (m : SABMap t' t (𝟙 _)) (P : PELUnif I t) :
    ∃ (P' : PELUnif I t') (hD : IsPullDeg (RingHom.id R) P.D.toPre P'.D.toPre),
      ∀ (x : 𝓞 E) y, hD.xe (x • y) = x • hD.xe y := by
  let _ := H.starRing
  have hs := specOf_id R
  have gp₁ : IsGrpPullback t'.G t.G (specOf (RingHom.id R)) m.φ := m.cart.congr hs.symm rfl
  obtain ⟨bc, mbc, hbc⟩ := grpPullback_iso gp₁ (isGrpPullback_pullback t.G (specOf (RingHom.id R)))
  have gpG : IsGrpPullback P.A.A t.G (jK R) (P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R)) := by
    have := P.U.gen_hom
    have : IsMonHom P.U.gen.symm.hom := by show IsMonHom P.U.gen.inv; infer_instance
    exact ((isGrpPullback_of_iso P.U.gen.symm).comp (isGrpPullback_pullback t.G (jK R))).congr
      (Category.id_comp _) rfl
  have gp₂ : IsGrpPullback ((Over.pullback (jK R)).obj t'.G) t.G (jK R)
      (pullback.fst t'.G.hom (jK R) ≫ m.φ) :=
    ((isGrpPullback_pullback t'.G (jK R)).comp m.cart).congr (Category.comp_id _) rfl
  obtain ⟨eA, mE, heA⟩ := grpPullback_iso gp₂ gpG
  have hgi : P.U.gen.inv.left ≫ P.U.gen.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
  have wA : LBIso (P.A.L.pull eA.hom.left) (P.U.LG.L.pull (pullback.fst t'.G.hom (jK R) ≫ bc.hom.left ≫
      pullback.fst t.G.hom (specOf (RingHom.id R)))) :=
    LBIso.chartPull (h := eA.hom.left ≫ P.U.gen.inv.left)
      (chartPullSame P.A.L (fun _ => eA.hom.left) (fun _ => P.U.gen.hom.left) _ _ fun _ => by
        rw [Category.assoc, hgi, Category.comp_id])
      (chartPullSame P.U.LG.L _ (fun _ => pullback.fst t.G.hom (jK R)) _ _ fun _ => by
        rw [hbc, ← heA]; simp only [Category.assoc]) P.U.ext
  obtain ⟨wL', he', gL, rL⟩ := rigIso_congr P.bundle m.cm m.lin hbc
    (e := specOf (RingHom.id R)) (hs.trans m.base.symm)
  obtain ⟨Wo, hWo, hψW⟩ := h5.psiOnExists R I hR P.D
  have hgen : (specOf (RingHom.id R)).base (genericPoint (Spec (CommRingCat.of R))) ∈ Wo := by
    rw [hs]; exact hWo
  have hI : I.map (RingHom.id R) ≤ I := by rw [Ideal.map_id]
  obtain ⟨D'', hD, U'', hLG, hgenU, hPU⟩ := hU R R I I hR hR (RingHom.id R) hI P.D P.A t.G t.semi P.U
    Wo hψW hgen t'.G bc mbc P.A rfl eA mE wA t'.PP wL' he' gL rL
  have a₃ : ∀ x, (t'.act.act x).left ≫ m.φ = m.φ ≫ (t.act.act x).left := m.act
  have hbcact : ∀ x, t'.act.toRingAct.act x ≫ bc.hom =
      bc.hom ≫ (Over.pullback (specOf (RingHom.id R))).map (t.act.toRingAct.act x) := by
    intro x
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · have a₂ : ((Over.pullback (specOf (RingHom.id R))).map (t.act.act x)).left ≫
          pullback.fst t.G.hom (specOf (RingHom.id R)) = pullback.fst _ _ ≫ (t.act.act x).left :=
        pullback.lift_fst _ _ _
      show (t'.act.act x ≫ bc.hom).left ≫ _ =
        (bc.hom ≫ (Over.pullback (specOf (RingHom.id R))).map (t.act.act x)).left ≫ _
      rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, a₂, hbc, ← Category.assoc, hbc, a₃]
    · exact (Over.w (t'.act.act x ≫ bc.hom)).trans
        (Over.w (bc.hom ≫ (Over.pullback (specOf (RingHom.id R))).map (t.act.act x))).symm
  have actA : ∀ x, (P.oA.act x).left ≫ P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R) =
      P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R) ≫ (t.act.act x).left := by
    intro x
    have e : P.oA.act x ≫ P.U.gen.inv = P.U.gen.inv ≫ (Over.pullback (jK R)).map (t.act.act x) := by
      rw [Iso.comp_inv_eq, Category.assoc]
      exact ((Iso.inv_comp_eq _).2 (P.lin.ext x)).symm
    rw [← Category.assoc, ← Over.comp_left, e, Over.comp_left, Category.assoc]
    exact congrArg _ (pullback.lift_fst _ _ _)
  have extA : ∀ x, (Over.pullback (jK R)).map (t'.act.toRingAct.act x) ≫ U''.gen.hom =
      U''.gen.hom ≫ P.oA.act x := by
    intro x
    rw [hgenU]
    apply Over.OverMorphism.ext
    apply gpG.1.hom_ext
    · have a₁ : ((Over.pullback (jK R)).map (t'.act.act x)).left ≫ pullback.fst t'.G.hom (jK R) =
          pullback.fst t'.G.hom (jK R) ≫ (t'.act.act x).left := pullback.lift_fst _ _ _
      show ((Over.pullback (jK R)).map (t'.act.act x) ≫ eA.hom).left ≫ _ = (eA.hom ≫ P.oA.act x).left ≫ _
      rw [Over.comp_left, Category.assoc, heA, ← Category.assoc, a₁, Category.assoc, a₃, Over.comp_left,
        Category.assoc, actA, reassoc_of% heA]
    · rw [Over.w, Over.w]
  obtain ⟨mod'', oD'', xl, -, lin'', w0''⟩ := h5.oLinBaseChange R R I I hR hR (RingHom.id R) P.D P.A t.G P.U
    t'.G bc mbc P.A D'' hD U'' hPU (𝓞 E) P.oD P.oA t.act.toRingAct P.lin t'.act.toRingAct hbcact
    P.oA extA
  exact ⟨{ D := D'', mod := mod'', oD := oD'', A := P.A, oA := P.oA, U := U'', bundle := hLG, lin := lin''
           w0 := w0'' H.w0 P.w0 }, hD, xl⟩

theorem exists_equiv_psiCoord : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CharZero R] (t t' : SAB H (Sp R)) (_ : SABMap t' t (𝟙 _)) (U : PELUnif (maximalIdeal R) t) (U' : PELUnif (maximalIdeal R) t'), IsNoetherianRing R → IsIntegrallyClosed R → IsAdicComplete (maximalIdeal R) R → ∃ e : U.D.toPre.X ≃ₗ[𝓞 E] U'.D.toPre.X, ∀ χ r, PsiCoord U.D.toPre χ r → ∃ u : Rˣ, PsiCoord U'.D.toPre (e χ) (u * r) := by
  intro E _ _ _ H R _ _ _ _ t t' m U U' hN hC hA
  letI := H.starRing
  have hR : AdmBase R (maximalIdeal R) := ⟨hN, inferInstance, hC, hA⟩
  obtain ⟨-, -, -, h4, h5, h6⟩ := GlobalTheory.allSixLaws
  obtain ⟨P, hD₁, xl₁⟩ := exists_move h4.unifBaseChange h5 hR m U
  obtain ⟨wL, -, g₀, -, m₀, -, -⟩ := exists_iso_pair_of_eq (U'.bundle.trans P.bundle.symm)
  obtain ⟨hD₂, -, holin⟩ := h6.unifUniq R _ hR P.D U'.D P.A U'.A t'.G t'.semi P.U U'.U wL g₀ m₀
  obtain ⟨xl₂, -⟩ := holin (𝓞 E) P.oD U'.oD P.oA U'.oA t'.act.toRingAct P.lin U'.lin
  let e₁ : P.D.toPre.X ≃ₗ[𝓞 E] U.D.toPre.X := { hD₁.xe with map_smul' := xl₁ }
  let e₂ : U'.D.toPre.X ≃ₗ[𝓞 E] P.D.toPre.X := { hD₂.xe with map_smul' := xl₂ }
  refine ⟨e₁.symm.trans e₂.symm, fun χ r hr => ?_⟩
  have k₁ : hD₁.xe (e₁.symm χ) = χ := e₁.apply_symm_apply χ
  have k₂ : hD₂.xe (e₂.symm (e₁.symm χ)) = e₁.symm χ := e₂.apply_symm_apply _
  obtain ⟨u₁, hu₁⟩ := psiCoord_of_isPullDeg_id hD₁ (e₁.symm χ) r (by rw [k₁]; exact hr)
  obtain ⟨u₂, hu₂⟩ := psiCoord_of_isPullDeg_id hD₂ (e₂.symm (e₁.symm χ)) _ (by rw [k₂]; exact hu₁)
  exact ⟨u₂ * u₁, by rw [Units.val_mul, mul_assoc]; exact hu₂⟩

end GlobalTheory.SameCoord
end
end

