import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlockDetBlockTriangular
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0161
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0138
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0336
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0337
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0192
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PiEqOfFinPart
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0007
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EventuallyCongOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteDimensionalModel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAutomorphicFunctionStar
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0023
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0019
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0236
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0221
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0339

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFiniteAdeleProjectionIntegralReduction
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.StepData NumberField
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.SplitPt

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem pr_eq_zero_of_toEAf (q : SplitPt D k) {PP : Formalism.L2.DIV.Pl D.host.E} (he : Formalism.L2.NTheta.IsIdemAt q.e PP)
    (a : AE D) (ha : toEAf D a = 0) : q.pr a = 0 := by
  have h0 : infPart D q.e = 0 := (GlobalTheory.IdemSupport.delta_of_isIdemAt (GlobalTheory.StdFrames.comp_toAd D) he).1
  have h1 : finPart D a = 0 :=
    (Algebra.TensorProduct.comm D.host.F (Formalism.L2.Herm.Af D.host.F) D.host.E).injective (by
      rw [map_zero]; exact ha)
  have h2 : q.e * a = 0 := GlobalTheory.LatVac.eq_zero_of_parts _ (by rw [map_mul, h0, zero_mul]) (by rw [map_mul, h1, mul_zero])
  rw [← q.pr_sec (q.pr a), q.sec_pr, h2, map_zero]

def prF (q : SplitPt D k) {PP : Formalism.L2.DIV.Pl D.host.E} (he : Formalism.L2.NTheta.IsIdemAt q.e PP) : EAf D →+* k :=
  (RingHom.liftOfSurjective (toEAf D) (fun s => GlobalTheory.ResLoc.toEAf_surj s))
    ⟨q.pr, fun a ha => (RingHom.mem_ker).2 (q.pr_eq_zero_of_toEAf he a ((RingHom.mem_ker).1 ha))⟩

theorem prF_toEAf (q : SplitPt D k) {PP : Formalism.L2.DIV.Pl D.host.E} (he : Formalism.L2.NTheta.IsIdemAt q.e PP) (a : AE D) :
    q.prF he (toEAf D a) = q.pr a :=
  RingHom.liftOfRightInverse_comp_apply _ _ _ _ _

theorem pr_mem_iff (q : SplitPt D k) (a : AE D) :
    q.pr a ∈ 𝒪[k] ↔ toEAf D q.e * toEAf D a ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  rw [q.int_iff, q.sec_pr, ← map_mul]
  exact ⟨GlobalTheory.IdemRes.toEAf_mem_of_finPart, GlobalTheory.PlaceDatum.finPart_mem_of_toEAf⟩

end GlobalTheory.FinPl.SplitPt

namespace GlobalTheory.FinPl.SplitPt

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem mem_iff_val_lt (q : SplitPt D k) {PP : Formalism.L2.DIV.Pl D.host.E} (he : Formalism.L2.NTheta.IsIdemAt q.e PP)
    (x : 𝓞 D.host.E) : x ∈ PP.asIdeal ↔
      valuation k (q.prF he (Formalism.L2.DIV.oToS D.host.F D.host.E x : EAf D)) < 1 := by
  have e1 : ((Formalism.L2.DIV.oToS D.host.F D.host.E x : Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) =
      toEAf D (incA D (x : D.host.E)) := rfl
  rw [e1, prF_toEAf]
  by_cases hx : x = 0
  · subst hx
    simp only [map_zero, Submodule.zero_mem, true_iff]
    simp
  have hx' : (x : D.host.E) ≠ 0 := fun h => hx (RingOfIntegers.coe_eq_zero_iff.1 h)
  set y := q.pr (incA D (x : D.host.E)) with hy
  have hy0 : y ≠ 0 := fun h => by
    have : (q.pr.comp (incA D)) (x : D.host.E) = 0 := h
    exact hx' ((map_eq_zero_iff _ (q.pr.comp (incA D)).injective).1 this)
  have hinv : q.pr (incA D ((x : D.host.E)⁻¹)) = y⁻¹ := map_inv₀ (q.pr.comp (incA D)) _
  rw [he.2 x hx, ← q.sec_pr, ← q.int_iff, hinv]
  change ¬ valuation k y⁻¹ ≤ 1 ↔ _
  rw [not_le, Valuation.one_lt_val_iff _ (inv_ne_zero hy0), inv_inv]

theorem val_lt_of_mem_idS (q : SplitPt D k) {PP : Formalism.L2.DIV.Pl D.host.E} (he : Formalism.L2.NTheta.IsIdemAt q.e PP)
    {s : Formalism.L2.Herm.intAf D.host.F D.host.E} (hs : s ∈ Formalism.L2.DIV.idS D.host.F PP.asIdeal) :
    valuation k (q.prF he s.1) < 1 := by
  have hint : ∀ c : Formalism.L2.Herm.intAf D.host.F D.host.E, valuation k (q.prF he c.1) ≤ 1 := fun c => by
    obtain ⟨a, ha⟩ := GlobalTheory.ResLoc.toEAf_surj c.1
    have := (q.pr_mem_iff a).2 (by rw [ha]; exact mul_mem (GlobalTheory.IdemRes.resS_idem_eq_one D q.e PP he).1 c.2)
    rw [← ha, prF_toEAf]; exact this
  refine Submodule.span_induction (p := fun s _ => valuation k (q.prF he s.1) < 1) ?_ ?_ ?_ ?_ hs
  · rintro _ ⟨a, ha, rfl⟩
    exact (q.mem_iff_val_lt he a).1 ha
  · simp
  · intro x y _ _ hx hy
    rw [Subring.coe_add, map_add]
    exact Valuation.map_add_lt _ hx hy
  · intro c x _ hx
    rw [smul_eq_mul, Subring.coe_mul, map_mul, Valuation.map_mul]
    exact (mul_le_mul_of_nonneg_right (hint c) zero_le').trans_lt (by rwa [one_mul])

theorem resS_eq_zero_of_mem {PP : Formalism.L2.DIV.Pl D.host.E} {s : Formalism.L2.Herm.intAf D.host.F D.host.E}
    (hs : s ∈ Formalism.L2.DIV.idS D.host.F PP.asIdeal) : Formalism.L2.DIV.resS D.host.F PP s = 0 := by
  have : Formalism.L2.DIV.idS D.host.F PP.asIdeal ≤ RingHom.ker (Formalism.L2.DIV.resS D.host.F PP) :=
    Ideal.map_le_iff_le_comap.2 fun b hb => Ideal.mem_comap.2 ((RingHom.mem_ker).2 (by
      rw [Formalism.L2.DIV.resS_oToS]; exact Ideal.Quotient.eq_zero_iff_mem.2 hb))
  exact (RingHom.mem_ker).1 (this hs)

end GlobalTheory.FinPl.SplitPt

namespace GlobalTheory.FinPl.SplitPt

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem prF_mem_iff (q : SplitPt D k) {PP : Formalism.L2.DIV.Pl D.host.E} (he : Formalism.L2.NTheta.IsIdemAt q.e PP) (z : EAf D) :
    q.prF he z ∈ 𝒪[k] ↔ toEAf D q.e * z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  obtain ⟨a, rfl⟩ := GlobalTheory.ResLoc.toEAf_surj z
  rw [prF_toEAf]; exact q.pr_mem_iff a

theorem resS_eq_zero_iff (q : SplitPt D k) {PP : Formalism.L2.DIV.Pl D.host.E} (he : Formalism.L2.NTheta.IsIdemAt q.e PP)
    (s : Formalism.L2.Herm.intAf D.host.F D.host.E) :
    Formalism.L2.DIV.resS D.host.F PP s = 0 ↔ valuation k (q.prF he s.1) < 1 := by
  obtain ⟨a, ha0⟩ := GlobalTheory.FunObj.Comparison₂.exists_approx PP.ne_bot s
  have ha : s - Formalism.L2.DIV.oToS D.host.F D.host.E a ∈ Formalism.L2.DIV.idS D.host.F PP.asIdeal := ha0
  have h1 : Formalism.L2.DIV.resS D.host.F PP s = Ideal.Quotient.mk PP.asIdeal a := by
    rw [← Formalism.L2.DIV.resS_oToS (F := D.host.F) PP a, ← sub_eq_zero, ← map_sub]
    exact resS_eq_zero_of_mem ha
  have h2 := q.val_lt_of_mem_idS he ha
  have e2 : ((s - Formalism.L2.DIV.oToS D.host.F D.host.E a : Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) =
      (s : EAf D) - ((Formalism.L2.DIV.oToS D.host.F D.host.E a : Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) := rfl
  rw [e2, RingHom.map_sub] at h2
  rw [h1, Ideal.Quotient.eq_zero_iff_mem, q.mem_iff_val_lt he]
  constructor
  · intro h; simpa using Valuation.map_add_lt _ h2 h
  · intro h; simpa using Valuation.map_sub_lt _ h h2

theorem mem_intAf_iff (q : SplitPt D k) {PP : Formalism.L2.DIV.Pl D.host.E} (he : Formalism.L2.NTheta.IsIdemAt q.e PP) (z : EAf D) :
    z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ↔
      (1 - toEAf D q.e) * z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ∧ q.prF he z ∈ 𝒪[k] := by
  obtain ⟨hint, -⟩ := GlobalTheory.IdemRes.resS_idem_eq_one D q.e PP he
  rw [q.prF_mem_iff he]
  constructor
  · intro hz
    exact ⟨mul_mem (sub_mem (one_mem _) hint) hz, mul_mem hint hz⟩
  · rintro ⟨h1, h2⟩
    have : z = (1 - toEAf D q.e) * z + toEAf D q.e * z := by
      rw [sub_mul, one_mul, sub_add_cancel]
    rw [this]; exact add_mem h1 h2

set_option maxHeartbeats 1000000 in
theorem resS_off (q : SplitPt D k) {PP : Formalism.L2.DIV.Pl D.host.E} (he : Formalism.L2.NTheta.IsIdemAt q.e PP)
    (PP' : Formalism.L2.DIV.Pl D.host.E) (hne : PP' ≠ PP) (z : EAf D) (hz : z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E)
    (hz' : (1 - toEAf D q.e) * z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) :
    Formalism.L2.DIV.resS D.host.F PP' ⟨(1 - toEAf D q.e) * z, hz'⟩ = Formalism.L2.DIV.resS D.host.F PP' ⟨z, hz⟩ := by
  obtain ⟨hint, -⟩ := GlobalTheory.IdemRes.resS_idem_eq_one D q.e PP he
  have h0 : Formalism.L2.DIV.resS D.host.F PP' ⟨toEAf D q.e, hint⟩ = 0 := by
    obtain ⟨a, h1, h2⟩ := GlobalTheory.FunObj.Comparison₂.exists_resS_eq PP' ⟨toEAf D q.e, hint⟩
    rw [h1, GlobalTheory.FunObj.Comparison₂.mk_eq_zero_iff]
    rw [GlobalTheory.FunObj.Comparison₂.cptO_apply PP' ⟨toEAf D q.e, hint⟩] at h2
    change Valued.v (GlobalTheory.StdFrames.cpt PP' (toEAf D q.e) - _) < 1 at h2
    rw [(GlobalTheory.StdFrames.cpt_of_isIdemAt he).2 PP' hne, zero_sub, Valuation.map_neg] at h2
    exact h2
  have e1 : (⟨(1 - toEAf D q.e) * z, hz'⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) =
      (1 - ⟨toEAf D q.e, hint⟩) * ⟨z, hz⟩ :=
    Subtype.ext (by rw [Subring.coe_mul, AddSubgroupClass.coe_sub, OneMemClass.coe_one])
  refine (congrArg (Formalism.L2.DIV.resS D.host.F PP') e1).trans ?_
  rw [map_mul, map_sub, map_one, h0, sub_zero, one_mul]

end GlobalTheory.FinPl.SplitPt

namespace GlobalTheory.FinPl.SplitPt

theorem exists_lift_isRed : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (PP : Formalism.L2.DIV.Pl D.host.E), Formalism.L2.NTheta.IsIdemAt q.e PP → ∃ π' : EAf D →+* k, (∀ a, π' (toEAf D a) = q.pr a) ∧ GlobalTheory.FunObj.Comparison₂.IsRed (Formalism.L2.DIV.resS D.host.F PP) (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) ∧ (∀ z : EAf D, z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ↔ (1 - toEAf D q.e) * z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ∧ π' z ∈ 𝒪[k]) ∧ ∀ PP' : Formalism.L2.DIV.Pl D.host.E, PP' ≠ PP → ∀ (z : EAf D) (hz : z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) (hz' : (1 - toEAf D q.e) * z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E), Formalism.L2.DIV.resS D.host.F PP' ⟨(1 - toEAf D q.e) * z, hz'⟩ = Formalism.L2.DIV.resS D.host.F PP' ⟨z, hz⟩ := by
  intro D k _ _ _ _ q PP he
  obtain ⟨hint, -⟩ := GlobalTheory.IdemRes.resS_idem_eq_one D q.e PP he
  refine ⟨q.prF he, q.prF_toEAf he, ⟨(Ideal.Quotient.maximal_ideal_iff_isField_quotient _).1 PP.isMaximal,
    fun s => (q.prF_mem_iff he s.1).2 (mul_mem hint s.2), fun s => q.resS_eq_zero_iff he s⟩,
    q.mem_intAf_iff he, fun PP' hne z hz hz' => q.resS_off he PP' hne z hz hz'⟩

end GlobalTheory.FinPl.SplitPt

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFiniteAdelicConjSelfDualDoublingCompact
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory.Core.Rk.LatMove

theorem exists_conj_KAd_of_selfDual : ∀ (D : D7) (A : HSp D) (L L' : Lat A), IsSelfDualC A L → IsSelfDualC A L' →
    ∃ k ∈ GfC A, ∀ (a : GL (Fin A.rank) (AE D)) (x : GA D (dblSp A)),
      x ∈ KAd D.sp.cm.sig (dblSp A).gram L' a ↔ (io A (k, k))⁻¹ * x * io A (k, k) ∈ KAd D.sp.cm.sig (dblSp A).gram L a := by
  intro D A L L' hL hL'
  obtain ⟨b, hb, hbL⟩ := GlobalTheory.T.exists_unitary_finiteAdelic_map_selfDual_completions D A L L' hL hL'
  let y : GFin D.sp.cm.sig A.gram := ⟨b, hb⟩
  have hk : ofFin D.sp.cm.sig A.gram y ∈ GfC A := by
    show infHom A (ofFin D.sp.cm.sig A.gram y) = 1
    have := projInf_ofFin D.sp.cm.sig A.gram y
    exact congrArg (GlobalTheory.AdelicU.matHom _ D.sp.cm.sig A.gram) this
  refine ⟨ofFin D.sp.cm.sig A.gram y, hk, GlobalTheory.T.doubledCompactSubgroup_conj_hermitianSpace D A L L' _ hk ?_⟩
  intro v z
  rw [proj_ofFin]
  exact GlobalTheory.T.mem_localLattice_iff_of_finiteAdelic_completion_map D.host.F D.host.E A.rank L L' hL.1.fg hL'.1.fg b hbL v z

end GlobalTheory.Core.Rk.LatMove
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIntegralFramePointOfInertHalfLatticePointStatement
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.InertFrameLoc

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integralFramePoint_of_inertHalf_latticePoint : ∀ (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : IsInertAt D.host.F D.host.E v w) (h : w.under (𝓞 D.host.F) = v) (S T : HSp D) (k : w.adicCompletion D.host.E) (aS : GL (Fin S.rank) (w.adicCompletion D.host.E)) (aT : GL (Fin T.rank) (w.adicCompletion D.host.E)), GlobalTheory.InertLoc.IsGen D w k → IsFrameAt w (frameLat S) aS → IsFrameAt w (frameLat T) aT → ∀ e e', IsPrimeIdem w e e' → ∀ u ∈ latO S T (L0c D S) (L0c D T) (fun _ => True), IsHalf e u ∨ IsHalf (cA D e) u → ∃ x : Matrix (Fin T.rank) (Fin S.rank) (w.adicCompletion D.host.E), (∀ i j, x i j ∈ Formalism.UG.intL (w.adicCompletion D.host.E)) ∧ uPt hw h k aS aT x = u := by
  first | exact @GlobalTheory.InertFrameLoc.exists_uPt_of_half | exact GlobalTheory.InertFrameLoc.exists_uPt_of_half | (intros; apply GlobalTheory.InertFrameLoc.exists_uPt_of_half <;> assumption)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsMemMultT
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.L2.Forms GlobalTheory.Core.Rk GlobalTheory.Core.Rk.Top
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical

noncomputable section

namespace GlobalTheory.Core.Rk.TopLift

open GlobalTheory.Mem.ColAd Filter Topology

section Comp

variable {D : D7} (θ : InfFam D) (V : HSp D) {n : ℕ} (hn : V.rank = n)

theorem finN_mem_UPts (g : GA D V) : finN V hn g ∈ Formalism.UG.UPts D.sp.cm.sig (V.gram.reindex (finCongr hn) (finCongr hn))
    (FiniteAdeleRing (𝓞 D.host.F) D.host.F) := by
  subst hn
  exact GlobalTheory.PrincInLevel.swap_mem_UPts _ _ _ (GlobalTheory.UnitarySplit.finHom_mem V g)

theorem finN_eq (g : GA D V) (y : GL (Fin n) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (h : ∀ i j, (Formalism.UG.bc (Lev.swapAE D) (finHom V g)).1 i j = y.1 (finCongr hn i) (finCongr hn j)) : finN V hn g = y := by
  subst hn
  exact Units.ext (Matrix.ext h)

theorem exists_rat' (hθ : IsInfFam θ) {γ : GA D V} (hγ : γ ∈ GQ V) :
    ∃ δ ∈ Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) (V.gram.reindex (finCongr hn) (finCongr hn)),
      finN V hn γ = Formalism.UG.bc (Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) δ ∧
      ∀ τ, (infN θ V hn (Equiv.refl _) γ τ : Matrix (Fin n) (Fin n) ℂ) = (δ : Matrix (Fin n) (Fin n) D.host.E).map (tauE D τ) := by
  subst hn
  obtain ⟨δ, hδ, e⟩ := hγ
  refine ⟨δ, hδ, ?_, fun τ => ?_⟩
  · show Formalism.UG.bc _ (Formalism.UG.bc _ (matHom V γ)) = _
    rw [show matHom V γ = _ from e.symm]
    rfl
  · show (Formalism.UG.bc _ (Formalism.UG.bc _ (matHom V γ))).1 = _
    rw [show matHom V γ = _ from e.symm]
    exact Matrix.ext fun i j => (hθ τ).1 _

theorem infN_atTau (hθ : IsInfFam θ) (τ : D.what₂.Tau) {g : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) (ρ : D.what₂.Tau) :
    (infN θ V hn (Equiv.refl _) (atTau θ V τ g) ρ : Matrix (Fin n) (Fin n) ℂ) =
      (Function.update (fun _ => (1 : Matrix (Fin V.rank) (Fin V.rank) ℂ)) τ g ρ).reindex (finCongr hn) (finCongr hn) := by
  subst hn
  have h : IsAtTau θ V τ g (atTau θ V τ g) := GlobalTheory.PointAtPlaceHom.atTau_spec hθ V τ hg
  show Formalism.MainNotions.StandardLattice.infMat D.sp.cm.sig V.gram (θ ρ) (atTau θ V τ g) = Function.update (fun _ => (1 : Matrix (Fin V.rank) (Fin V.rank) ℂ)) τ g ρ
  by_cases c : ρ = τ
  · subst c
    rw [Function.update_self]
    exact h.2.1
  · rw [Function.update_of_ne c]
    exact h.2.2 ρ c

open scoped Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes in
open Formalism.L2.Col in
attribute [local instance] Algebra.TensorProduct.rightAlgebra in

theorem continuous_finN : letI := tensTopL (F := D.host.F) (E := D.host.E) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)
    Continuous fun κ : GA D V =>
      (finN V hn κ : GL (Fin n) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)) := by
  subst hn
  haveI : IsTopologicalGroup (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  letI := rlt_top D.host.F D.host.E
  haveI := rlt_isModTop D.host.F D.host.E
  haveI := rlt_topRing (F := D.host.F) (E := D.host.E)
  haveI : IsModuleTopology (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) :=
    ⟨rfl⟩
  have hs : Continuous (Lev.swapAE D) := by
    haveI := IsModuleTopology.toContinuousAdd (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (Lev.EAf D)
    refine (IsModuleTopology.continuous_of_linearMap
      (LinearEquiv.ofBijective (rlt_comm (F := D.host.F) (E := D.host.E)) (TensorProduct.comm _ _ _).bijective).symm.toLinearMap).congr
      fun z => ?_
    refine (LinearEquiv.symm_apply_eq _).2 ?_
    exact ((Algebra.TensorProduct.comm D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.host.E).symm_apply_apply z).symm
  have hf : Continuous fun κ : GA D V => (finN V rfl κ).1 :=
    (GlobalTheory.Mem.VolExists.continuous_finMat (σ := D.sp.cm.sig) V.gram).matrix_map hs
  refine Units.continuous_iff.2 ⟨hf, (hf.comp continuous_inv).congr fun κ => ?_⟩
  exact congrArg Units.val (map_inv (finN V rfl) κ)

end Comp

section Main

variable {D : D7} {u : D.what₂.Word} {K : ClsPTied u} (θ : InfFam D)

def finPt (h : GA D D.sp.X') : Formalism.UG.UPts (sigD D) (gramP D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) :=
  ⟨finN D.sp.X' (rankP D) h, finN_mem_UPts D.sp.X' (rankP D) h⟩

theorem finPt_mul (h k : GA D D.sp.X') : (finPt (h * k)).1 = (finPt h).1 * (finPt k).1 := map_mul (finN D.sp.X' (rankP D)) h k

theorem finPt_one : (finPt (1 : GA D D.sp.X')) = 1 := Subtype.ext (map_one (finN D.sp.X' (rankP D)))

abbrev infPt : GA D D.sp.X' →* (D.what₂.Tau → GL (Fin (D.R.N D.R.m - 1)) ℂ) := infN θ D.sp.X' (rankP D) (Equiv.refl _)

theorem finPt_of_hasMat {h : GA D D.sp.X'} {y} (hh : HasMat h y) : (finPt h).1 = y := finN_eq _ (rankP D) h y hh.2

variable {g : Formalism.UG.UPts (sigD D) (gramP D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) → FrP D → ℂ}

theorem form_level (hg : g ∈ AdForms K.lev (embT D) (sgT u)) (h k : GA D D.sp.X') (κ : K.lev.U) (hk : (finPt k).1 = κ.1) :
    g (finPt (h * k)) = (K.lev.chi κ : ℂ) • g (finPt h) := by
  funext y
  refine hg.1 1 (one_mem _) (finPt h) (finPt (h * k)) κ ?_ y y fun τ => ?_
  · rw [map_one, one_mul, finPt_mul, hk]
  · show y.1 τ = (1 : Matrix _ _ D.host.E).map (embT D τ) * y.1 τ
    rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]

theorem form_left (hθ : IsInfFam θ) (hg : g ∈ AdForms K.lev (embT D) (sgT u)) {γ : GA D D.sp.X'} (hγ : γ ∈ GQ D.sp.X')
    (h : GA D D.sp.X') : lT _ (infPt θ γ) (g (finPt (γ * h))) = g (finPt h) := by
  obtain ⟨δ, hδ, e1, e2⟩ := exists_rat' θ D.sp.X' (rankP D) hθ hγ
  funext y
  have := hg.1 δ hδ (finPt h) (finPt (γ * h)) 1 (by
    rw [finPt_mul, ← e1]
    exact (mul_one _).symm) (frL _ (infPt θ γ) y) y fun τ => congrArg (· * y.1 τ) (e2 τ)
  rw [map_one, Units.val_one, one_mul] at this
  exact this

theorem form_locally (hK : letI := tensTopL (F := D.host.F) (E := D.host.E) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)
      IsOpen {x : Formalism.UG.UPts (sigD D) (gramP D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) |
        ∃ hx : x.1 ∈ K.lev.U, K.lev.chi ⟨x.1, hx⟩ = 1})
    (hg : g ∈ AdForms K.lev (embT D) (sgT u)) :
    ∀ᶠ k in 𝓝 (1 : GA D D.sp.X'), ∀ h, g (finPt (h * k)) = g (finPt h) := by
  letI := tensTopL (F := D.host.F) (E := D.host.E) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)
  have hc : Continuous (finPt (D := D)) := (continuous_finN D.sp.X' (rankP D)).subtype_mk _
  have h1 := (hK.preimage hc).mem_nhds (x := 1) (by
    rw [Set.mem_preimage, finPt_one]
    exact ⟨one_mem _, map_one K.lev.chi⟩)
  filter_upwards [h1] with k hk h
  obtain ⟨hx, e⟩ := hk
  rw [form_level hg h k ⟨_, hx⟩ rfl, e, Units.val_one, one_smul]

def valAt (g : Formalism.UG.UPts (sigD D) (gramP D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) → FrP D → ℂ) (h : GA D D.sp.X') :
    FrP D → ℂ := lT _ (infPt θ h) (g (finPt h))

theorem finPt_mul_inf (h : GA D D.sp.X') {k : GA D D.sp.X'} (hk : k ∈ GinfC D.sp.X') : finPt (h * k) = finPt h := by
  refine Subtype.ext ?_
  rw [finPt_mul, show (finPt k).1 = 1 from finN_of_inf (rankP D) hk, mul_one]

theorem infPt_of_fin {k : GA D D.sp.X'} (hk : k ∈ GfC D.sp.X') : infPt θ k = 1 := infN_of_fin θ (rankP D) _ hk

theorem valAt_mem (hg : g ∈ AdForms K.lev (embT D) (sgT u)) (h : GA D D.sp.X') :
    valAt θ g h ∈ ValC (gramC (gramP D) (embT D)) (sgT u) := lT_mem _ _ _ (hg.2 _ (Set.mem_univ _))

theorem valAt_level (hg : g ∈ AdForms K.lev (embT D) (sgT u)) (h : GA D D.sp.X') {k : GA D D.sp.X'} {κ : K.lev.U}
    (hk : HasMat k κ.1) : valAt θ g (h * k) = (K.lev.chi κ : ℂ) • valAt θ g h := by
  unfold valAt
  have e : infPt θ (h * k) = infPt θ h :=
    ((infPt θ).map_mul h k).trans ((congrArg (infPt θ h * ·) (infPt_of_fin θ hk.1)).trans (mul_one _))
  rw [form_level hg h k κ (finPt_of_hasMat hk), e]
  exact LinearMap.map_smul _ _ _

theorem valAt_of_hasMat {h : GA D D.sp.X'} {y : Formalism.UG.UPts (sigD D) (gramP D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)}
    (hh : HasMat h y.1) : valAt θ g h = g y := by
  unfold valAt
  rw [infPt_of_fin θ hh.1, lT_one, show finPt h = y from Subtype.ext (finPt_of_hasMat hh)]

theorem valAt_atTau (hθ : IsInfFam θ) (h : GA D D.sp.X') (τ : D.what₂.Tau) {a : Matrix (Fin D.sp.X'.rank) (Fin D.sp.X'.rank) ℂ}
    (ha : a ∈ Formalism.QuantumDeterminants.UH (gramAt D D.sp.X' τ)) (y y' : FrP D)
    (hy : IsTr (fun ρ => (Function.update (fun _ => (1 : Matrix (Fin D.sp.X'.rank) (Fin D.sp.X'.rank) ℂ)) τ a ρ).reindex
      (finCongr (rankP D)) (finCongr (rankP D))) y' y) :
    valAt θ g h y = valAt θ g (h * atTau θ D.sp.X' τ a) y' := by
  have e : y = frL _ (infPt θ (atTau θ D.sp.X' τ a)) y' :=
    Subtype.ext (funext fun ρ => (hy ρ).trans (congrArg (· * y'.1 ρ) (infN_atTau θ _ (rankP D) hθ τ ha ρ).symm))
  unfold valAt
  rw [finPt_mul_inf h (GlobalTheory.PointAtPlaceHom.atTau_mem _ τ a), map_mul (infPt θ), lT_mul, e]
  rfl

variable (Bf : (FrP D → ℂ) →ₗ⋆[ℂ] (FrP D → ℂ) →ₗ[ℂ] ℂ)

theorem isAutFunSm_pair (hθ : IsInfFam θ)
    (hK : letI := tensTopL (F := D.host.F) (E := D.host.E) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)
      IsOpen {x : Formalism.UG.UPts (sigD D) (gramP D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) |
        ∃ hx : x.1 ∈ K.lev.U, K.lev.chi ⟨x.1, hx⟩ = 1})
    (hg : g ∈ AdForms K.lev (embT D) (sgT u)) (f : FrP D → ℂ) :
    IsAutFunSm θ D.sp.X' fun h => Bf (valAt θ g h) f := by
  haveI : FiniteDimensional ℂ (ValC (gramC (gramP D) (embT D)) (sgT u)) :=
    GlobalTheory.Mem.Col2.valC_finiteDimensional (embT D) (RingHom.id ℂ) (sgT u)
  let l : (FrP D → ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun F => star (Bf F f)
      map_add' := fun F F' => by rw [map_add, LinearMap.add_apply, star_add]
      map_smul' := fun c F => by simp }
  have h1 := isAutFunDef_of θ (rankP D) (Equiv.refl _) hθ (gramC (gramP D) (embT D)) (sgT u) (fun h => g (finPt h))
    (fun h => hg.2 _ (Set.mem_univ _)) (fun γ hγ h => form_left θ hθ hg hγ h) (form_locally hK hg)
    (fun k hk h => by rw [finPt_mul_inf h hk]) l
  have h2 := GlobalTheory.Mem.AutConj.isAutFunSm_star D θ hθ _ _
    ((GlobalTheory.DefiniteForms.autFunDefIffSm D θ hθ _ D.sp.X'_sig (GlobalTheory.DefiniteEnd.end_definite D) _).1 h1)
  convert h2 using 1
  funext h
  exact (star_star _).symm

end Main

theorem exists_mem_multT : ∀ (D : D7) (u : D.what₂.Word) (K : ClsPTied u) (θ : InfFam D), IsInfFam θ → ∀ (S : D.what₂.Tau → SPar) (M : DSModel D.sp.X' S) (j : SmT M →ₗ[ℂ] (FrP D → ℂ)), IsJ u M j → ∀ (J : Set (GA D D.sp.X')) (χ : GA D D.sp.X' → ℂ), TopLev K J χ → (letI := tensTopL (F := D.host.F) (E := D.host.E) (FiniteAdeleRing (𝓞 D.host.F) D.host.F); IsOpen {x : Formalism.UG.UPts (sigD D) (gramP D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) | ∃ hx : x.1 ∈ K.lev.U, K.lev.chi ⟨x.1, hx⟩ = 1}) → ∀ (Bf : (FrP D → ℂ) →ₗ⋆[ℂ] (FrP D → ℂ) →ₗ[ℂ] ℂ), (∀ a : D.what₂.Tau → Matrix (Fin D.sp.X'.rank) (Fin D.sp.X'.rank) ℂ, (∀ τ, a τ ∈ Formalism.QuantumDeterminants.UH (gramAt D D.sp.X' τ)) → ∀ f f' f₁ f₁' : FrP D → ℂ, f ∈ ValC (gramC (gramP D) (embT D)) (sgT u) → f' ∈ ValC (gramC (gramP D) (embT D)) (sgT u) → (∀ y y' : FrP D, IsTr (fun τ => (a τ).reindex (finCongr (rankP D)) (finCongr (rankP D))) y' y → f₁ y = f y' ∧ f₁' y = f' y') → Bf f₁ f₁' = Bf f f') → ∀ g ∈ AdForms K.lev (embT D) (sgT u), ∃ T ∈ MultT θ M J χ, ∀ (c : (D.fm u).clsP) (v : SmT M) (h : GA D D.sp.X'), HasMat h (K.y c).1 → T v h = Bf (g (K.y c)) (j v) := by
  intro D u K θ hθ S M j hj J χ hJ hK Bf hB g hg
  let T : SmT M →ₗ[ℂ] (GA D D.sp.X' → ℂ) := LinearMap.pi fun h => Bf (valAt θ g h) ∘ₗ j
  have hT : ∀ x h, T x h = Bf (valAt θ g h) (j x) := fun _ _ => rfl
  have hs := D.sp.X'_sig
  have hd := GlobalTheory.DefiniteEnd.end_definite D
  refine ⟨T, (mem_multT θ M J χ T).2 (Submodule.subset_span ⟨fun v => isAutFunSm_pair θ Bf hθ hK hg _,
    fun v => GlobalTheory.DefiniteEnd.isCuspFun_of_definite hs hd _, fun v k hk h => ?_, fun τ a ha v w hw => ?_, fun τ v x => ?_⟩),
    fun c v h hh => ?_⟩
  · obtain ⟨κ, hκ⟩ := (hJ.1 k).1 hk
    show Bf (valAt θ g (h * k)) _ = χ k * Bf (valAt θ g h) _
    rw [hJ.2 k κ hκ, valAt_level θ hg h hκ, LinearMap.map_smulₛₗ₂]
    rfl
  · funext h
    show Bf (valAt θ g h) (j _) = Bf (valAt θ g (h * atTau θ D.sp.X' τ a)) (j _)
    refine hB (Function.update (fun _ => 1) τ a) (fun ρ => ?_) _ _ _ _ (valAt_mem θ hg _)
      (hj.range ▸ LinearMap.mem_range_self j _) fun y y' hy => ⟨valAt_atTau θ hθ h τ ha y y' hy, hj.eqv τ a ha v w hw y y' fun ρ => ?_⟩
    · by_cases c : ρ = τ
      · subst c
        rwa [Function.update_self]
      · rw [Function.update_of_ne c]
        show (1 : Matrix _ _ ℂ).conjTranspose * _ * 1 = _
        rw [Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
    · refine (hy ρ).trans ?_
      by_cases c : ρ = τ
      · subst c
        simp only [Function.update_self]
      · simp only [Function.update_of_ne c, Matrix.reindex_apply, Matrix.submatrix_one_equiv]
  · haveI := GlobalTheory.DefiniteEnd.finiteDimensional_model hs hd M τ
    exact GlobalTheory.DefiniteEnd.exists_sobCont M τ _ v x
  · rw [hT, valAt_of_hasMat θ hh]

end GlobalTheory.Core.Rk.TopLift

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsThetaFunctionSchrodingerFunctionEq
section
open scoped ComplexConjugate Matrix NNReal ENNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP GlobalTheory.Core.Rk.SWLaw
open GlobalTheory.Core.Rk.SW
open scoped ContDiff

namespace GlobalTheory.SchwOnto

noncomputable def ser (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (φ : Mx D B.rank A.rank → ℂ) :
    WO (dblSp A) B → ℂ := fun w =>
  ψ (-(symplOH (dblSp A) B ((dblDec A).extX B (HMul.hMul w (dblDec A).jX)) ((dblDec A).extY B (HMul.hMul w (dblDec A).jY)))) * ∑' ξ : Matrix (Fin B.rank) (Fin A.rank) D.host.E, ψ (symplO (dblSp A) B ((dblDec A).extX B (HMul.hMul w (dblDec A).jX + rat ξ)) ((dblDec A).extY B (HMul.hMul w (dblDec A).jY))) * φ (HMul.hMul w (dblDec A).jX + rat ξ)

theorem schw_onto : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (A B : HSp D) (ν : Measure (WO A B)) (𝓨 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓨 → ∀ φ : Mx D B.rank A.rank → ℂ, GlobalTheory.IndefiniteRowSideFullHecke.SchwartzBruhatMixedFamilies.IsSchwartzBruhat φ → ∃ f, IsThetaFunO ψ (dblSp A) B f ∧ sch ψ A B ν 𝓨 f = φ := by
  intro D ψ hψ A B ν 𝓨 hν φ hφ
  have hlaw := GlobalTheory.T.doubled_theta_series_law_and_level D ψ hψ A B φ hφ (ser D ψ A B φ) (fun _ => rfl)
  have hcs := GlobalTheory.T.thetaSeries_schwartzBruhat_continuous_schrodinger D ψ hψ A B ν 𝓨 hν φ hφ (ser D ψ A B φ) (fun _ => rfl)
  let V : Set (WO (dblSp A) B → ℂ) := {g | ∃ φ', GlobalTheory.IndefiniteRowSideFullHecke.SchwartzBruhatMixedFamilies.IsSchwartzBruhat φ' ∧ g = ser D ψ A B φ'}
  have hVc : ∀ g ∈ V, Continuous g := by
    rintro g ⟨φ', hφ', rfl⟩
    exact (GlobalTheory.T.thetaSeries_schwartzBruhat_continuous_schrodinger D ψ hψ A B ν 𝓨 hν φ' hφ' (ser D ψ A B φ') (fun _ => rfl)).1
  have hVd : ∀ g ∈ V, ∀ M : ℝ →+ WO (dblSp A) B, Continuous M → (∀ t, (M t).map (finPart D) = 0) →
      ∃ g' ∈ V, ∀ w, HasDerivAt (fun t : ℝ => heisO ψ (dblSp A) B (M t) g w) (g' w) 0 := by
    rintro g ⟨φ', hφ', rfl⟩ M hM hMf
    obtain ⟨φ'', hφ'', hd⟩ := GlobalTheory.T.hasDerivAt_heisenberg_thetaSeries D ψ hψ A B φ' hφ' (ser D ψ A B φ') (fun _ => rfl) M hM hMf
    exact ⟨ser D ψ A B φ'', ⟨φ'', hφ'', rfl⟩, hd (ser D ψ A B φ'') (fun _ => rfl)⟩
  have hsm := GlobalTheory.T.contDiff_of_heisenbergDerivativeClosedClass D ψ hψ (dblSp A) B V hVc hVd (ser D ψ A B φ) ⟨φ, hφ, rfl⟩
  exact ⟨ser D ψ A B φ, { quasi := hlaw.1, level := hlaw.2, cont := hcs.1, smooth := hsm }, hcs.2⟩

end GlobalTheory.SchwOnto
end

