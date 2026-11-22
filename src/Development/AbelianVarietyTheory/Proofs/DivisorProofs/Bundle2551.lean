import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0069
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.IsLinked
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0502
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0453
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0326
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0026
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2411
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1281
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0077
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EqZeroOfFderivEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2447
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0019
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0030
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0058
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsClopenLocusTorsionSectionsHeckeKernel
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoIffBijectiveOverAlgClosed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2445
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLevelConjugateCharacter
section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
open GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.R3.LinkLev

theorem spack_X_eq_of_heq {D : D7} {F F' : ∀ u, Formalism.L2.Forms.Forms0 D u} (hF : F = F') (P : GlobalTheory.Mem.SRe.SPack D F)
    (P' : GlobalTheory.Mem.SRe.SPack D F') (h : HEq P P') : P.X = P'.X := by
  subst hF
  rw [eq_of_heq h]

theorem conjLevel_of_setting_eq {D : D7} (X X' : Formalism.L2.SG.HidaSetting.HidaSetting D) (hX : X = X')
    (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (h' : X'.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (ι : Formalism.L2.Theta.GA D (D.sp.Y 0) ≃* X.B.I.GA) (hι : ι = (Formalism.L2.SG.RowsJoinPinned.iotaX X h).toMulEquiv)
    (t t' : Formalism.L2.Theta.GA D (Yc D 0)) (ht : t = t') (J : Set (Formalism.L2.Theta.GA D (Yc D 0)))
    (χ : Formalism.L2.Theta.GA D (Yc D 0) → ℂ)
    (hc : Formalism.IndefR.AutomorphicEvaluation.ConjLevel t'⁻¹ J χ (Formalism.L2.SG.RowsJoinPinned.iotaX X' h' ⁻¹' GlobalTheory.Mem.SRe.concreteLevelAdelicSubset X')
      (fun k => GlobalTheory.Mem.SRe.adelicCharacterOfHidaSetting X' (Formalism.L2.SG.RowsJoinPinned.iotaX X' h' k))) :
    Formalism.IndefR.AutomorphicEvaluation.ConjLevel t⁻¹ J χ (ι ⁻¹' seeKS X) (fun k => seeChiS X (ι k)) := by
  subst hX
  subst hι
  subst ht
  exact hc

theorem of_setting_eq {D : D7}
    (P : ∀ X : Formalism.L2.SG.HidaSetting.HidaSetting D, X.B.I = Formalism.L2.SG.InstExistsPf.instOf D → Formalism.L2.Theta.GA D (D.sp.Y 0) → Prop)
    (X X' : Formalism.L2.SG.HidaSetting.HidaSetting D) (hX : X = X') (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (h' : X'.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t t' : Formalism.L2.Theta.GA D (D.sp.Y 0)) (ht : t = t') (hP : P X' h' t') :
    P X h t := by
  subst hX
  subst ht
  exact hP

end GlobalTheory.Mem.R3.LinkLev

namespace GlobalTheory.Mem.R3.LinkLev
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem levels_withErr_updS (R : RealDat3 D A3 Ks) (kap : ℝ) (lam e) (F : Face3 D A3) (Dc Sp Zsc)
    (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t : Formalism.L2.Theta.GA D (D.sp.Y 0)) :
    (Formalism.IndefR.AutomorphicEvaluation.ConjLevel t⁻¹ (levS _ (((R.updS kap lam).withErr e).βY 0) (((R.updS kap lam).withErr e).dat0 (((R.updS kap lam).withErr e).toRealDat.levR (reFace F Dc Sp Zsc).lv2 true)))
      (Formalism.IndefR.Lev.levChi _ (((R.updS kap lam).withErr e).βY 0) (((R.updS kap lam).withErr e).dat0 (((R.updS kap lam).withErr e).toRealDat.levR (reFace F Dc Sp Zsc).lv2 true)))
      (Formalism.L2.SG.RowsJoinPinned.iotaX X h ⁻¹' GlobalTheory.Mem.SRe.concreteLevelAdelicSubset X) (fun k => GlobalTheory.Mem.SRe.adelicCharacterOfHidaSetting X (Formalism.L2.SG.RowsJoinPinned.iotaX X h k)) ∧
      Formalism.L2.SG.RowLevelMatch.RowLevelMatchAt ((R.updS kap lam).withErr e).toRealDat (reFace F Dc Sp Zsc).lv2 X h t) ↔
    (Formalism.IndefR.AutomorphicEvaluation.ConjLevel t⁻¹ (GlobalTheory.Mem.SRe.JR R.toRealDat F.lv2) (GlobalTheory.Mem.SRe.chiR R.toRealDat F.lv2)
      (Formalism.L2.SG.RowsJoinPinned.iotaX X h ⁻¹' GlobalTheory.Mem.SRe.concreteLevelAdelicSubset X) (fun k => GlobalTheory.Mem.SRe.adelicCharacterOfHidaSetting X (Formalism.L2.SG.RowsJoinPinned.iotaX X h k)) ∧
      Formalism.L2.SG.RowLevelMatch.RowLevelMatchAt R.toRealDat F.lv2 X h t) := Iff.rfl

end GlobalTheory.Mem.R3.LinkLev

namespace GlobalTheory.Mem.R3.LinkLev

open GlobalTheory.Mem.Col2 GlobalTheory.Mem.R3.Tr

set_option maxHeartbeats 4000000 in

theorem levels_of_twArgs {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl}
    {L : SizeData₂ (w.st Z).toD7} {hT : GatTies (w.st Z).toD7} {Gi : Formalism.MainNotions.G.Inst (w.st Z).toD7 L} {Gl : Formalism.MainNotions.G.LatInst (w.st Z).toD7}
    {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (w.st Z).toD7} {cX : ExtraC} {ex : Extra (w.st Z).toD7 L hT Gi Gl Kc Yd cX}
    {t : RowsT K w Z Wt ex.p0} (a : TwArgs ex t) (x : TwIn ex) (ax : HEq a.x x) (X : Formalism.L2.SG.HidaSetting.HidaSetting (w.st Z).toD7)
    (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf (w.st Z).toD7) (s : Formalism.L2.Theta.GA (w.st Z).toD7 ((w.st Z).toD7.sp.Y 0))
    (hs : Formalism.IndefR.AutomorphicEvaluation.ConjLevel s⁻¹ (GlobalTheory.Mem.SRe.JR t.r.z.R.toRealDat t.r.z.F.lv2) (GlobalTheory.Mem.SRe.chiR t.r.z.R.toRealDat t.r.z.F.lv2)
      (Formalism.L2.SG.RowsJoinPinned.iotaX X h ⁻¹' GlobalTheory.Mem.SRe.concreteLevelAdelicSubset X) (fun k => GlobalTheory.Mem.SRe.adelicCharacterOfHidaSetting X (Formalism.L2.SG.RowsJoinPinned.iotaX X h k)) ∧
      Formalism.L2.SG.RowLevelMatch.RowLevelMatchAt t.r.z.R.toRealDat t.r.z.F.lv2 X h s) :
    Formalism.IndefR.AutomorphicEvaluation.ConjLevel s⁻¹ (levS _ (x.R.βY 0) (x.R.dat0 (x.R.toRealDat.levR x.F.lv2 true)))
      (Formalism.IndefR.Lev.levChi _ (x.R.βY 0) (x.R.dat0 (x.R.toRealDat.levR x.F.lv2 true)))
      (Formalism.L2.SG.RowsJoinPinned.iotaX X h ⁻¹' GlobalTheory.Mem.SRe.concreteLevelAdelicSubset X) (fun k => GlobalTheory.Mem.SRe.adelicCharacterOfHidaSetting X (Formalism.L2.SG.RowsJoinPinned.iotaX X h k)) ∧
      Formalism.L2.SG.RowLevelMatch.RowLevelMatchAt x.R.toRealDat x.F.lv2 X h s := by
  cases ax
  obtain ⟨Dc, Sp, Zsc, lam, err, lam_eq, x, pack, _⟩ := a
  obtain ⟨G, grp, fin, Pl0, I0, T0, A3, core, alg, R, F, cG, _⟩ := x
  dsimp only at pack ⊢
  cases pack
  exact (levels_withErr_updS _ _ _ _ _ _ _ _ _ _ _).2 hs

end GlobalTheory.Mem.R3.LinkLev

namespace GlobalTheory.Mem.R3.LinkLev

set_option maxHeartbeats 4000000 in

theorem tS_fin_conj_match : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (p : Prm hL), GlobalTheory.Fc.EvP fun _ K => ∀ (q : WPt p.s K) (c : ℝ) (b : GlobalTheory.Fc.Bundle (q.w.D q.Z) q.O c) (w : BWit q b), q.O.L.sc = K.s → w.y.y.tS ∈ Formalism.L2.Theta.GfC (Yc (q.w.D q.Z) 0) ∧ Formalism.IndefR.AutomorphicEvaluation.ConjLevel w.y.y.tS⁻¹ (levS _ (w.x.R.βY 0) (w.x.R.dat0 (w.x.R.toRealDat.levR w.x.F.lv2 true))) (Formalism.IndefR.Lev.levChi _ (w.x.R.βY 0) (w.x.R.dat0 (w.x.R.toRealDat.levR w.x.F.lv2 true))) (w.y.y.ιS ⁻¹' seeKS b.S.X) (fun k => seeChiS b.S.X (w.y.y.ιS k)) ∧ Formalism.L2.SG.RowLevelMatch.RowLevelMatchAt w.x.R.toRealDat w.x.F.lv2 b.S.X w.y.y.instEq w.y.y.tS := by
  intro hL p
  refine GlobalTheory.Fc.EvP.of_all fun _ K _ => ?_
  intro q c b w hsc
  obtain ⟨sP, sS, hP, hS, hb⟩ := w.s
  have see := q.sat.see
  have ht : w.y.y.tS = q.sat.t := eq_of_heq w.pt.1
  have hι := (GlobalTheory.Mem.JIota.heq_iota_iff _ _ w.y.y.instEq w.y.y.ιS).1 w.y.y.ιS_eq
  have hX : b.S.X = q.sat.P.X := by
    rw [hb]
    exact spack_X_eq_of_heq (by rw [w.recPin.s.cols]; exact rfl) sP q.sat.P hP
  have key := levels_of_twArgs w.a w.x w.ax q.sat.P.X q.sat.P.inst q.sat.t ⟨see.conj, see.mat⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [ht]
    exact see.fin
  · exact conjLevel_of_setting_eq _ _ hX _ _ _ hι _ _ ht _ _ key.1
  · exact of_setting_eq (fun X h t => Formalism.L2.SG.RowLevelMatch.RowLevelMatchAt w.x.R.toRealDat w.x.F.lv2 X h t) _ _ hX _ _ _ _ ht key.2

end GlobalTheory.Mem.R3.LinkLev
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMultiplierIntegralImaginary
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.TorusRM

open scoped nonZeroDivisors

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ThetaLiouville

open Matrix Complex

theorem conj_form {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (hH : Hm.IsHermitian) (w l : Fin g → ℂ) :
    l ⬝ᵥ Hm.mulVec (star w) = (starRingEnd ℂ) (w ⬝ᵥ Hm.mulVec (star l)) := by
  simp only [dotProduct, mulVec, map_sum, map_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have h1 : (starRingEnd ℂ) (Hm i j) = Hm j i := by
    have := hH.apply j i
    simpa using this
  simp only [Pi.star_apply, RCLike.star_def, Complex.conj_conj]
  rw [h1]
  ring

theorem exists_basis_in {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ))
    (hΛ : Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤) :
    ∃ (s : Set (Fin g → ℂ)) (b : Module.Basis s ℝ (Fin g → ℂ)), Finite s ∧ ∀ i, b i ∈ Λ := by
  obtain ⟨s, hs, hsp, hli⟩ := exists_linearIndependent ℝ (Λ : Set (Fin g → ℂ))
  let b := Module.Basis.mk hli (by rw [Subtype.range_coe, hsp, hΛ])
  refine ⟨s, b, ?_, ?_⟩
  · exact Module.Finite.finite_basis b
  · intro i
    rw [Module.Basis.mk_apply]
    exact hs i.2

end GlobalTheory.ThetaLiouville

namespace GlobalTheory.ThetaLiouville

open Matrix Complex

theorem im_form_mem_int (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ))
    (hΛ : Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤)
    (Hm : Matrix (Fin g) (Fin g) ℂ) (hH : Hm.IsHermitian) (w : Fin g → ℂ) (θ : (Fin g → ℂ) → ℂ)
    (hθ : Differentiable ℂ θ) (hθ0 : ∀ z, θ z ≠ 0)
    (hper : ∀ l ∈ Λ, ∀ z, θ (z + l) = Complex.exp (Real.pi * (w ⬝ᵥ Hm.mulVec (star l))) * θ z) :
    ∀ l ∈ Λ, ∃ n : ℤ, (w ⬝ᵥ Hm.mulVec (star l)).im = n := by
  set u : Fin g → ℂ := Hm.mulVec (star w) with hu
  let ψ : (Fin g → ℂ) → ℂ := fun z => θ z * Complex.exp (-(Real.pi * (z ⬝ᵥ u)))
  have hlin : Differentiable ℂ (fun z : Fin g → ℂ => z ⬝ᵥ u) := by
    have : (fun z : Fin g → ℂ => z ⬝ᵥ u) = fun z => ∑ i, z i * u i := rfl
    rw [this]
    exact Differentiable.fun_sum fun i _ => (differentiable_apply i).mul_const _
  have hψ : Differentiable ℂ ψ :=
    hθ.mul ((hlin.const_mul _).neg.cexp)

  have hshift : ∀ l ∈ Λ, ∀ z, ψ (z + l) = ψ z *
      Complex.exp (Real.pi * (((2 * (w ⬝ᵥ Hm.mulVec (star l)).im : ℝ) : ℂ) * I)) := by
    intro l hl z
    have hc := conj_form Hm hH w l
    simp only [ψ, hper l hl z, add_dotProduct]
    rw [hc]
    set a := w ⬝ᵥ Hm.mulVec (star l)
    have hsub : a - (starRingEnd ℂ) a = ((2 * a.im : ℝ) : ℂ) * I := by
      rw [Complex.sub_conj]
    rw [← hsub]
    rw [show -(↑Real.pi * (z ⬝ᵥ u + (starRingEnd ℂ) a)) =
        -(↑Real.pi * (z ⬝ᵥ u)) + (-(↑Real.pi * (starRingEnd ℂ) a)) by ring,
      Complex.exp_add,
      show (↑Real.pi * (a - (starRingEnd ℂ) a)) = ↑Real.pi * a + (-(↑Real.pi * (starRingEnd ℂ) a))
        by ring, Complex.exp_add]
    ring
  have hnorm : ∀ l ∈ Λ, ∀ z, ‖ψ (z + l)‖ = ‖ψ z‖ := by
    intro l hl z
    rw [hshift l hl z, norm_mul, Complex.norm_exp]
    simp

  obtain ⟨s, b, hfin, hbΛ⟩ := exists_basis_in Λ hΛ
  haveI : Fintype s := Fintype.ofFinite s
  have hspan : ∀ x ∈ Submodule.span ℤ (Set.range b), x ∈ Λ := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => obtain ⟨i, rfl⟩ := hx; exact hbΛ i
    | zero => exact Λ.zero_mem
    | add x y _ _ hx hy => exact Λ.add_mem hx hy
    | smul n x _ hx => exact Λ.toAddSubgroup.zsmul_mem hx n
  have hcpt : IsCompact (closure (ZSpan.fundamentalDomain b)) :=
    (ZSpan.fundamentalDomain_isBounded b).isCompact_closure
  obtain ⟨C, hC⟩ := hcpt.exists_bound_of_continuousOn hψ.continuous.continuousOn
  have hbd : Bornology.IsBounded (Set.range ψ) := by
    rw [isBounded_iff_forall_norm_le]
    refine ⟨C, ?_⟩
    rintro _ ⟨z, rfl⟩
    have hz : z = ZSpan.fract b z + (ZSpan.floor b z : Fin g → ℂ) := by
      rw [ZSpan.fract_apply]; abel
    rw [hz, hnorm _ (hspan _ (ZSpan.floor b z).2)]
    exact hC _ (subset_closure (ZSpan.fract_mem_fundamentalDomain b z))
  intro l hl
  have hconst : ψ (0 + l) = ψ 0 := hψ.apply_eq_apply_of_bounded hbd _ _
  rw [hshift l hl 0] at hconst
  have hψ0 : ψ 0 ≠ 0 := mul_ne_zero (hθ0 0) (Complex.exp_ne_zero _)
  have hexp : Complex.exp (Real.pi * (((2 * (w ⬝ᵥ Hm.mulVec (star l)).im : ℝ) : ℂ) * I)) = 1 := by
    have := hconst
    rw [mul_eq_left₀ hψ0] at this
    exact this
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp hexp
  refine ⟨n, ?_⟩
  have hI : (I : ℂ) ≠ 0 := Complex.I_ne_zero
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h2 : ((w ⬝ᵥ Hm.mulVec (star l)).im : ℂ) = n := by
    have : (Real.pi : ℂ) * 2 * I * ((w ⬝ᵥ Hm.mulVec (star l)).im : ℂ) =
        (Real.pi : ℂ) * 2 * I * n := by
      push_cast at hn
      linear_combination hn
    have h0 : (Real.pi : ℂ) * 2 * I ≠ 0 := mul_ne_zero (mul_ne_zero hpi two_ne_zero) hI
    exact mul_left_cancel₀ h0 this
  exact_mod_cast h2

end GlobalTheory.ThetaLiouville
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaNonvanishingBundleGenerated
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (defCoord polydisc)
open scoped nonZeroDivisors
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HolUnifSec

open GlobalTheory.CxPts Filter Topology
open ReciprocityTheory.L2DbarEstimates (V)

variable {A : Over (Sp ℂ)} [GrpObj A] {M : LB A.left} {g : ℕ} (u : HolUnif A M g)

def pt (z : Fin g → ℂ) : CxPts A.hom (RingHom.id ℂ) :=
  ⟨(u.ex z).left, (Over.w (u.ex z)).trans (Spec.map_id _).symm⟩

theorem pt_surjective : Function.Surjective (pt u) := fun y => by
  obtain ⟨z, hz⟩ := u.ex_onto (Over.homMk y.1 (y.2.trans (Spec.map_id _)))
  exact ⟨z, Subtype.ext (congrArg (·.left) hz)⟩

theorem sub_mem_of_pt_eq {z w : Fin g → ℂ} (h : pt u z = pt u w) : z - w ∈ u.Λ := by
  have h' : u.ex z = u.ex w := Over.OverMorphism.ext (congrArg Subtype.val h)
  have e := u.ex_add (z - w) w
  rw [sub_add_cancel, h'] at e
  exact (u.ker _).1 (mul_eq_right.1 e.symm)

theorem isOpen_pre (U : A.left.Opens) : IsOpen (pt u ⁻¹' ptsIn _ _ U) := (u.hol U 0).1

theorem differentiableOn_ev (U : A.left.Opens) (f : Γ(A.left, U)) :
    DifferentiableOn ℂ (ev _ _ U f ∘ pt u) (pt u ⁻¹' ptsIn _ _ U) := (u.hol U f).2

theorem continuous_pt : Continuous (pt u) :=
  CxPts.continuous_iff.2 fun U => ⟨isOpen_pre u U, fun f => (differentiableOn_ev u U f).continuousOn⟩

theorem eq_zero_of_fderiv_eq_zero (z₀ w : Fin g → ℂ)
    (hw : ∀ (U : A.left.Opens) (f : Γ(A.left, U)), ⊤ ≤ (u.ex z₀).left ⁻¹ᵁ U →
      fderiv ℂ (fun z => valAt' (u.ex z).left U f) z₀ w = 0) : w = 0 := by
  refine TorusTransfer.eq_zero_of_fderiv_eq_zero u w fun U f h => ?_
  let T : A ⟶ A := (toUnit A ≫ u.ex (-z₀)) * 𝟙 A
  have hT : ∀ z, (u.ex z).left ≫ T.left = (u.ex (-z₀ + z)).left := fun z => by
    rw [← Over.comp_left, u.ex_add]
    congr 1
    rw [MonObj.comp_mul, Category.comp_id, ← Category.assoc, toUnit_unique (u.ex z ≫ toUnit A) (𝟙 _),
      Category.id_comp]
  have h1 := hw (T.left ⁻¹ᵁ U) ((T.left.app U).hom f)
    (by rw [← top_le_preimage_comp, hT, neg_add_cancel]; exact h)
  simp only [valAt'_comp, hT] at h1
  rw [fderiv_comp_add_left (f := fun z => valAt' (u.ex z).left U f), neg_add_cancel] at h1
  exact h1

variable {D : ℕ} (c : AlgChart A.hom (RingHom.id ℂ) D)

theorem isOpen_pre_source : IsOpen (pt u ⁻¹' c.e.source) := c.e.open_source.preimage (continuous_pt u)

theorem analyticOnNhd_chart : AnalyticOnNhd ℂ (c.e ∘ pt u) (pt u ⁻¹' c.e.source) :=
  SCV.analyticOnNhd_of_differentiableOn (isOpen_pre_source u c) (differentiableOn_euclidean.2 fun a =>
    ((differentiableOn_ev u _ (c.x a)).mono fun _ hz => c.source_subset hz).congr fun _ hz => c.apply_eq _ hz a)

theorem injective_fderiv {z₀ : Fin g → ℂ} (hz : pt u z₀ ∈ c.e.source) :
    Function.Injective (fderiv ℂ (c.e ∘ pt u) z₀) := by
  refine (injective_iff_map_eq_zero _).2 fun w hw => eq_zero_of_fderiv_eq_zero u z₀ w fun U f hU => ?_
  have e : ev _ _ U f ∘ pt u =ᶠ[𝓝 z₀] (ev _ _ U f ∘ c.e.symm) ∘ (c.e ∘ pt u) :=
    eventually_of_mem ((isOpen_pre_source u c).mem_nhds hz) fun z hz =>
      (congrArg (ev _ _ U f) (c.e.left_inv hz)).symm
  change fderiv ℂ (ev _ _ U f ∘ pt u) z₀ w = 0
  rw [e.fderiv_eq, fderiv_comp (f := c.e ∘ pt u) z₀ (c.differentiableAt_ev f hz hU)
    (analyticOnNhd_chart u c z₀ hz).differentiableAt, ContinuousLinearMap.comp_apply, hw, map_zero]

theorem dim_le {z₀ : Fin g → ℂ} (hz : pt u z₀ ∈ c.e.source) : D ≤ g := by
  have h1 : dimH ((c.e ∘ pt u) '' (pt u ⁻¹' c.e.source)) ≤ dimH (pt u ⁻¹' c.e.source) :=
    dimH_image_le_of_locally_lipschitzOn fun z hz => by
      obtain ⟨K, t, ht, h⟩ := (analyticOnNhd_chart u c z hz).contDiffAt.exists_lipschitzOnWith
      exact ⟨K, t, mem_nhdsWithin_of_mem_nhds ht, h⟩
  rw [Set.image_comp, Set.image_preimage_eq _ (pt_surjective u), c.e.image_source_eq_target,
    Real.dimH_of_mem_nhds (c.e.open_target.mem_nhds (c.e.map_source hz)),
    Real.dimH_of_mem_nhds ((isOpen_pre_source u c).mem_nhds hz), Nat.cast_le,
    finrank_real_of_complex, finrank_real_of_complex] at h1
  simpa using h1

theorem holoOn_of_comp (R : AnRead A.hom (RingHom.id ℂ) D) {S : Set (CxPts A.hom (RingHom.id ℂ))} (hS : IsOpen S)
    {F : CxPts A.hom (RingHom.id ℂ) → ℂ} (hF : DifferentiableOn ℂ (F ∘ pt u) (pt u ⁻¹' S)) : R.HoloOn S F := by
  intro i v hv
  set c := R.chart i
  obtain ⟨z₀, hz₀⟩ := pt_surjective u (c.e.symm v)
  have hz : pt u z₀ ∈ c.e.source := hz₀ ▸ c.e.map_target hv.1
  have hv₀ : (c.e ∘ pt u) z₀ = v := by rw [Function.comp_apply, hz₀, c.e.right_inv hv.1]
  have hinj := injective_fderiv u c hz
  have hle := LinearMap.finrank_le_finrank_of_injective
    (f := (fderiv ℂ (c.e ∘ pt u) z₀ : (Fin g → ℂ) →ₗ[ℂ] V D)) hinj
  have hrk : Module.finrank ℂ (Fin g → ℂ) = Module.finrank ℂ (V D) :=
    le_antisymm hle (by simpa using dim_le u c hz)
  let L : (Fin g → ℂ) ≃L[ℂ] V D := (LinearEquiv.ofBijective
    (fderiv ℂ (c.e ∘ pt u) z₀ : (Fin g → ℂ) →ₗ[ℂ] V D)
    ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrk).1 hinj⟩).toContinuousLinearEquiv
  have hs : HasStrictFDerivAt (c.e ∘ pt u) (L : (Fin g → ℂ) →L[ℂ] V D) z₀ :=
    (analyticOnNhd_chart u c z₀ hz).hasStrictFDerivAt
  have hd := hs.to_localInverse.hasFDerivAt.differentiableAt
  have hr := hs.eventually_right_inverse
  have hl := hs.localInverse_apply_image
  have ht := hs.localInverse_tendsto
  rw [hv₀] at hd hr hl ht
  have hFz : DifferentiableAt ℂ (F ∘ pt u) (hs.localInverse _ _ _ v) := by
    rw [hl]
    exact hF.differentiableAt ((hS.preimage (continuous_pt u)).mem_nhds (show pt u z₀ ∈ S from hz₀ ▸ hv.2))
  refine ((hFz.comp v hd).congr_of_eventuallyEq ?_).differentiableWithinAt
  filter_upwards [hr, ht ((isOpen_pre_source u c).mem_nhds hz)] with w hw hw'
  exact congrArg F ((congrArg c.e.symm hw.symm).trans (c.e.left_inv hw'))

theorem exists_isFn (hA : IsAbelianScheme A) (hp : IsProjOver A.hom) (hM : M.IsLB) {θ : (Fin g → ℂ) → ℂ}
    (hθ : Differentiable ℂ θ)
    (hper : ∀ l ∈ u.Λ, ∀ i z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ M.U i → θ (z + l) * u.fr i (z + l) = θ z * u.fr i z) :
    ∃ s : M.Sec, u.IsFn s θ := by
  classical
  obtain ⟨D, hD⟩ := AbelianDim.exists_relDim ℂ A hA
  let r := Function.surjInv (pt_surjective u)
  have hr : ∀ y, pt u (r y) = y := Function.surjInv_eq (pt_surjective u)
  let s : M.ι → CxPts A.hom (RingHom.id ℂ) → ℂ := fun i y =>
    if y ∈ ptsIn _ _ (M.U i) then θ (r y) * u.fr i (r y) else 0
  have hs : ∀ i z, pt u z ∈ ptsIn _ _ (M.U i) → s i (pt u z) = θ z * u.fr i z := fun i z hz => by
    have := hper _ (sub_mem_of_pt_eq u (hr (pt u z))) i z hz
    rw [add_sub_cancel] at this
    exact (if_pos hz).trans this
  have hmem : s ∈ (AnRead.all A.hom (RingHom.id ℂ) D).holSec M := by
    refine ⟨⟨fun i j y hi hj => ?_, fun i y h => if_neg h⟩, fun i => holoOn_of_comp u _ (isOpen_ptsIn _) ?_⟩
    · obtain ⟨z, rfl⟩ := pt_surjective u y
      have hij : pt u z ∈ ptsIn _ _ (M.U i ⊓ M.U j) := mem_ptsIn_inf.2 ⟨hi, hj⟩
      have e : u.fr i z = gv _ _ M i j (pt u z) * u.fr j z := u.fr_compat i j z hij
      rw [hs i z hi, hs j z hj, e, mul_left_comm]
    · exact (hθ.differentiableOn.mul (u.fr_hol i)).congr fun z hz => hs i z hz
  obtain ⟨σ, hσ⟩ := (GlobalTheory.Published.serreHolomorphicSections_holds A.left A.hom D hD hp _ M hM).2 ⟨s, hmem⟩
  exact ⟨σ, fun i z hz => (congrFun₂ (congrArg Subtype.val hσ) i (pt u z)).trans (hs i z hz)⟩

theorem isUnit_of_ev_ne_zero {Y : Scheme.{0}} (p : Y ⟶ Sp ℂ) [LocallyOfFiniteType p] {U : Y.Opens} (f : Γ(Y, U))
    (h : ∀ y ∈ ptsIn p (RingHom.id ℂ) U, ev p _ U f y ≠ 0) : IsUnit f := by
  have := LocallyOfFiniteType.jacobsonSpace p
  have hU : U ≤ Y.basicOpen f := by
    by_contra hn
    obtain ⟨x, hx, hx'⟩ := Set.not_subset.1 hn
    obtain ⟨y, hy, hy'⟩ := nonempty_inter_closedPoints (Z := (U : Set Y) ∩ (Y.basicOpen f : Set Y)ᶜ) ⟨x, hx, hx'⟩
      (U.isOpen.isLocallyClosed.inter (Y.basicOpen f).isOpen.isClosed_compl.isLocallyClosed)
    let q : CxPts p (RingHom.id ℂ) :=
      ⟨pointOfClosedPoint p y hy', (pointOfClosedPoint_comp p y hy').trans (Spec.map_id _).symm⟩
    have hq : q.1 (IsLocalRing.closedPoint ℂ) = y := pointOfClosedPoint_apply p y hy' _
    have hqU : q ∈ ptsIn p _ U := mem_ptsIn.2 (hq ▸ hy.1)
    exact hy.2 (hq ▸ mem_ptsIn.1 ((mem_ptsIn_basicOpen hqU f).2 (h q hqU)))
  exact Y.toRingedSpace.isUnit_of_isUnit_germ U f fun x hx => (Y.mem_basicOpen f x hx).1 (hU hx)

theorem hasGen_of_periodic : ∀ (A : Over (Sp ℂ)) [GrpObj A], IsAbelianScheme A → IsProjOver A.hom →
    ∀ (M : LB A.left), M.IsLB → ∀ (g : ℕ) (u : HolUnif A M g) (θ : (Fin g → ℂ) → ℂ), Differentiable ℂ θ →
    (∀ z, θ z ≠ 0) →
    (∀ l ∈ u.Λ, ∀ i z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ M.U i → θ (z + l) * u.fr i (z + l) = θ z * u.fr i z) →
    HasGen M := by
  intro A _ hA hp M hM g u θ hθ h0 hper
  obtain ⟨s, hs⟩ := exists_isFn u hA hp hM hθ hper
  have := hA.proper
  have hu : ∀ i, IsUnit (s.f i) := fun i => isUnit_of_ev_ne_zero A.hom _ fun y hy => by
    obtain ⟨z, rfl⟩ := pt_surjective u y
    exact (hs i z hy).trans_ne (mul_ne_zero (h0 z) (u.fr_ne i z hy))
  exact ⟨⟨fun i => (hu i).unit⟩, fun i j => Units.ext (s.compat i j)⟩

end GlobalTheory.HolUnifSec
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionFamilyKernelExactIsClopenGeometric
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.HTSympCover

noncomputable section

namespace GlobalTheory.KerClopen

variable {S : Scheme.{0}}

theorem comp_zsmul {L : Type} [AddCommGroup L] {G T T' : Over S} [GrpObj G] (e : L → (T ⟶ G))
    (he : ∀ a c, e (a + c) = e a * e c) (h : T' ⟶ T) (n : ℤ) (a : L) : h ≫ e (n • a) = (h ≫ e a) ^ n := by
  let φ : Multiplicative L →* (T' ⟶ G) :=
    MonoidHom.mk' (fun x => h ≫ e x.toAdd) fun x y => by
      change h ≫ e (x.toAdd + y.toAdd) = _
      rw [he, MonObj.comp_mul]
  exact map_zpow φ (Multiplicative.ofAdd a) n

theorem loc_one (G : Over S) [GrpObj G] [IsCommMonObj G] (hG : IsAbelianScheme G) (M : ℕ)
    (hM : IsUnit (M : Γ(S, ⊤))) {L : Type} [AddCommGroup L] (Z : Over S) (e : L → (Z ⟶ G))
    (he : ∀ a c, e (a + c) = e a * e c) (hM' : ∀ a, e a ^ M = 1) (a : L) :
    GlobalTheory.HkClopen.Loc (S := Z.left) (fun k _ _ x =>
      (Over.homMk x rfl : Over.mk (x ≫ Z.hom) ⟶ Z) ≫ e a = 1) := by
  obtain ⟨Z₁, et, R⟩ := GlobalTheory.exists_finiteEtale_latticeTorsionHom S G M ℤ hG hM
  have hx : ∀ n m : ℤ, e ((n + m) • a) = e (n • a) * e (m • a) := fun n m => by rw [add_smul, he]
  have hx' : ∀ n : ℤ, e (n • a) ^ M = 1 := fun n => hM' _
  have R' : GlobalTheory.LevCover.RepTors G M ℤ Z₁ et := R
  have C := GlobalTheory.LevCover.RepTors.clopenCond (T := Z) R' (fun n : ℤ => e (n • a)) (fun _ => 1) hx hx'
    (fun _ _ => (_root_.mul_one _).symm) (fun _ => one_pow _)
  obtain ⟨U, hU, H⟩ := C
  refine ⟨(U : Set Z.left), ⟨hU, U.isOpen⟩, fun k _ _ x => ?_⟩
  rw [← GlobalTheory.HkClopen.range_subset_iff x]
  have := (H (Over.mk (x ≫ Z.hom)) (Over.homMk x rfl)).symm
  refine this.trans ⟨fun h1 => ?_, fun h1 n => ?_⟩
  · have := h1 1
    rwa [one_smul, MonObj.comp_one] at this
  · rw [MonObj.comp_one, comp_zsmul e he, h1, one_zpow]

end GlobalTheory.KerClopen

open GlobalTheory.KerClopen in
theorem GlobalTheory.kerClopen_geom : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G], IsAbelianScheme G → ∀ (M h : ℕ), 0 < M → IsUnit (M : Γ(S, ⊤)) → ∀ (Z : Over S) (e : (Fin h ⊕ Fin h → ℤ) → (Z ⟶ G)), (∀ a c, e (a + c) = e a * e c) → (∀ a, e a ^ M = 1) → GlobalTheory.HkClopen.Loc (S := Z.left) (fun k _ _ x => ∀ a, (Over.homMk x rfl : Over.mk (x ≫ Z.hom) ⟶ Z) ≫ e a = 1 ↔ ∃ c, a = M • c) := by
  intro S G _ _ hG M h hM0 hM Z e he hM'
  let L := Fin h ⊕ Fin h → ℤ
  obtain ⟨κ, _, q, hq⟩ := GlobalTheory.LevCover.exists_finite_mod L hM0
  let I₀ := Set.range q
  let r : I₀ → L := fun i => i.2.choose
  have hr : ∀ i : I₀, q (r i) = i.1 := fun i => i.2.choose_spec
  have hP : ∀ a c : L, e (a + M • c) = e a := fun a c => by
    rw [he, GlobalTheory.LevCover.add_map_nsmul he, hM', _root_.mul_one]
  have hQ : ∀ a c : L, (∃ d, a + M • c = M • d) ↔ ∃ d, a = M • d := fun a c =>
    ⟨fun ⟨d, hd⟩ => ⟨d - c, by rw [smul_sub, ← hd, add_sub_cancel_right]⟩,
     fun ⟨d, hd⟩ => ⟨d + c, by rw [hd, smul_add]⟩⟩
  have Lc := GlobalTheory.HkClopen.Loc.comb (I₀ := I₀)
    (fun i => loc_one G hG M hM Z e he hM' (r i)) fun f => ∀ i, (f i ↔ ∃ c, r i = M • c)
  refine Lc.congr fun k _ _ x => ⟨fun H a => ?_, fun H i => H (r i)⟩
  obtain ⟨c, hc⟩ := hq (r ⟨q a, a, rfl⟩) a (hr _)
  have := H ⟨q a, a, rfl⟩
  beta_reduce at this
  revert this hc
  generalize r ⟨q a, a, rfl⟩ = a₀
  intro hc this
  subst hc
  rw [hP, hQ]
  exact this
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransportPowerDecompositionFieldExtensionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.transport_power_decomposition_field_extension : ∀ (k K k₁ K' : Type) [Field k] [Field K] [Field k₁] [Field K'] (a : k →+* K) (b : k →+* k₁) (c : K →+* K') (d : k₁ →+* K'), c.comp a = d.comp b → ∀ (A₀ : Over (Sp k)) [GrpObj A₀] (A : Over (Sp K)) [GrpObj A] (π : A.left ⟶ A₀.left), IsGrpPullback A A₀ (spMap a) π → ∀ (L₀ M₀ : LB A₀.left) (L M : LB A.left), L₀.IsLB → M₀.IsLB → L.IsLB → M.IsLB → LBIso L (L₀.pull π) → LBIso M (M₀.pull π) → SqDec ((Over.pullback (spMap b)).obj A₀) (L₀.pull (pullback.fst A₀.hom (spMap b))) (M₀.pull (pullback.fst A₀.hom (spMap b))) → SqDec ((Over.pullback (spMap c)).obj A) (L.pull (pullback.fst A.hom (spMap c))) (M.pull (pullback.fst A.hom (spMap c))) := by
  first | exact @GlobalTheory.SqDecTransport.transport | exact GlobalTheory.SqDecTransport.transport | (intros; apply GlobalTheory.SqDecTransport.transport <;> assumption)
end

