import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0258
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0100
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0072
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0276
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0262
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0011
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0206
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0277
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CombAtSingleZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0278
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0003
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaSourceAction
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0280
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0267

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationDisjointPlacesCommuteVacua
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.DisjComb

open GlobalTheory.FinPl.LatMem

variable {D : D7}

theorem mul_eq_zero_of_disj {P P' : Pl D → Prop} (hd : ∀ p, P p → ¬ P' p) {a b : AE D} (ha : a ∈ idAt D P)
    (hb : b ∈ idAt D P') : a * b = 0 := by
  obtain ⟨ha0, haw⟩ := mem_idAt_iff.1 ha
  obtain ⟨hb0, hbw⟩ := mem_idAt_iff.1 hb
  refine GlobalTheory.AdelicU.Supp.adTens_ext (fun w => ?_) fun v => ?_
  · rw [map_mul, compInf_eq_zero ha0, zero_mul, map_zero]
  · rw [map_mul, map_zero, compFin_eq_compAt, compFin_eq_compAt]
    by_cases hv : P v
    · rw [hbw v (hd v hv), mul_zero]
    · rw [haw v hv, zero_mul]

theorem mul_eq_zero_of_off {P : Pl D → Prop} {a b : AE D} (ha : a ∈ idOff D P) (hb : b ∈ idAt D P) : a * b = 0 := by
  obtain ⟨hb0, hbw⟩ := mem_idAt_iff.1 hb
  have haw : ∀ v, P v → compAt D v a = 0 := by
    intro v hv
    unfold idOff at ha
    rw [Submodule.mem_iInf] at ha
    exact RingHom.mem_ker.1 (ha ⟨v, hv⟩)
  refine GlobalTheory.AdelicU.Supp.adTens_ext (fun w => ?_) fun v => ?_
  · rw [map_mul, compInf_eq_zero hb0, mul_zero, map_zero]
  · rw [map_mul, map_zero, compFin_eq_compAt, compFin_eq_compAt]
    by_cases hv : P v
    · rw [haw v hv, zero_mul]
    · rw [hbw v hv, mul_zero]

def idem (P : Pl D → Prop) : AE D := pairA D.host.F 0 (indP D.host.F P) ⊗ₜ[D.host.F] (1 : D.host.E)

theorem idem_mem (P : Pl D → Prop) : idem P ∈ idAt D P := tmul_mem_idAt (indicatorAdele_supported D.host.F P) 1

theorem cA_idem (P : Pl D → Prop) : cA D (idem P) = idem P := by
  show pairA D.host.F 0 (indP D.host.F P) ⊗ₜ[D.host.F] star (1 : D.host.E) = _
  rw [star_one]; rfl

theorem idem_mul {P : Pl D → Prop} {a : AE D} (ha : a ∈ idAt D P) : idem P * a = a := by
  rw [mul_comm]; exact mul_indP ha

theorem symplO_disj {S T : HSp D} {P P' : Pl D → Prop} (hd : ∀ p, P p → ¬ P' p) {x y : WO S T} (hx : MxAt P x)
    (hy : MxAt P' y) : symplO S T x y = 0 := by
  refine GlobalTheory.SplitScalar.symplO_eq_zero S T (a := idem P) (b := idem P') ?_ (fun i j => idem_mul (hx i j))
    (fun i j => idem_mul (hy i j))
  rw [cA_idem]
  exact mul_eq_zero_of_disj hd (idem_mem P) (idem_mem P')

theorem mxAt_mono {P Q : Pl D → Prop} (h : ∀ p, P p → Q p) {m n : ℕ} {x : Mx D m n} (hx : MxAt P x) : MxAt Q x := by
  intro i j
  obtain ⟨h0, hw⟩ := mem_idAt_iff.1 (hx i j)
  exact mem_idAt_iff.2 ⟨h0, fun w hw' => hw w fun hp => hw' (h w hp)⟩

theorem comb_single (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (w : WO S T) (f : WO S T → ℂ) :
    comb ψ S T (Finsupp.single w 1) f = heisO ψ S T w f := by
  unfold comb
  rw [Finsupp.support_single_ne_zero _ one_ne_zero, Finset.sum_singleton, Finsupp.single_eq_same, one_smul]

theorem mem_congGrp' {V : HSp D} {I : Ideal (AE D)} {g : GA D V} (hg : g ∈ congGrp V I) :
    ∀ i j, mt V g i j - (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j ∈ I := by
  unfold congGrp at hg
  rw [MonoidHom.mem_ker] at hg
  intro i j
  have := congrArg (fun x : GL (Fin V.rank) (AE D ⧸ I) => x.1 i j) hg
  rw [← Ideal.Quotient.eq]
  simp [Formalism.L2.Theta.mt, Matrix.one_apply] at this ⊢
  exact this

theorem actO_off {S T : HSp D} {P : Pl D → Prop} {g : GA D S} {h : GA D T} (hg : g ∈ grpOff S P)
    (hh : h ∈ grpOff T P) {u : WO S T} (hu : MxAt P u) : actO S T g h u = u := by
  have hg' := mem_congGrp' (inv_mem hg)
  have hh' := mem_congGrp' hh
  have h1 : HMul.hMul (mt T h - 1 : Matrix (Fin T.rank) (Fin T.rank) (AE D)) (u : Matrix (Fin T.rank) (Fin S.rank) (AE D)) = 0 := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.zero_apply]
    exact Finset.sum_eq_zero fun k _ => mul_eq_zero_of_off (by simpa using hh' i k) (hu k j)
  have h2 : HMul.hMul (u : Matrix (Fin T.rank) (Fin S.rank) (AE D)) (mt S g⁻¹ - 1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) = 0 := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.zero_apply]
    exact Finset.sum_eq_zero fun k _ => by
      rw [mul_comm]; exact mul_eq_zero_of_off (by simpa using hg' k j) (hu i k)
  rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at h1
  rw [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at h2
  unfold actO
  rw [h1]
  exact h2

end GlobalTheory.DisjComb

namespace GlobalTheory.DisjComb

open GlobalTheory.FinPl.LatMem

variable {D : D7}

theorem compAt_idem {P : Pl D → Prop} {w : Pl D} (hpw : P w) : compAt D w (idem P) = 1 := by
  rw [← compFin_eq_compAt]
  show evalV D.host.F w (indP D.host.F P) ⊗ₜ[D.host.F] (1 : D.host.E) = 1
  rw [evalV_indP, if_pos hpw]
  rfl

theorem sub_idem_mem {P P' : Pl D → Prop} {a : AE D} (ha : a ∈ idAt D (fun p => P p ∨ P' p)) :
    a - idem P * a ∈ idAt D P' := by
  obtain ⟨h0, hw⟩ := mem_idAt_iff.1 ha
  refine mem_idAt_iff.2 ⟨by rw [RingHom.map_sub, RingHom.map_mul, h0, mul_zero, sub_zero], fun w hw' => ?_⟩
  by_cases hpw : P w
  · rw [RingHom.map_sub, RingHom.map_mul, compAt_idem hpw, one_mul, sub_self]
  · rw [RingHom.map_sub, RingHom.map_mul, hw w (fun h => h.elim hpw hw'), mul_zero, sub_zero]

set_option maxHeartbeats 1000000 in

theorem split_latO (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) {S T : HSp D} {LS : Lat S} {LT : Lat T}
    (hLS : IsSelfDualC S LS) (hLT : IsSelfDualC T LT) {P P' : Pl D → Prop} (hd : ∀ p, P p → ¬ P' p) {u : WO S T}
    (hu : u ∈ latO S T (LS : Set _) (LT : Set _) (fun p => P p ∨ P' p)) :
    MxAt P (idem P • u) ∧ MxAt P' (u - idem P • u) ∧ idem P • u ∈ latO S T (LS : Set _) (LT : Set _) P ∧
      u - idem P • u ∈ latO S T (LS : Set _) (LT : Set _) P' := by
  have ann := GlobalTheory.SelfDualAt.latO_ann_at D ψ hψ S T LS LT hLS hLT
  have hmono : ∀ (Q Q' : Pl D → Prop), (∀ p, Q p → Q' p) →
      latO S T (LS : Set _) (LT : Set _) Q ≤ latO S T (LS : Set _) (LT : Set _) Q' := by
    intro Q Q' hQ
    apply AddSubgroup.closure_mono
    rintro w ⟨α, hα, hv, rest⟩
    exact ⟨α, hα, fun v hv' => hv v fun hq => hv' (hQ v hq), rest⟩
  have huM := latO_mxAt hu
  have hu1 : MxAt P (idem P • u) := fun i j => by
    rw [Matrix.smul_apply, smul_eq_mul]
    exact Ideal.mul_mem_right _ _ (idem_mem P)
  have hu2 : MxAt P' (u - idem P • u) := fun i j => by
    rw [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    exact sub_idem_mem (huM i j)
  refine ⟨hu1, hu2, (ann P _ hu1).2 fun u' hu' => ?_, (ann P' _ hu2).2 fun u' hu' => ?_⟩
  · have hsub : symplO S T (idem P • u) u' = symplO S T u u' - symplO S T (u - idem P • u) u' := by
      rw [← GlobalTheory.SplitScalar.symplO_sub_left, sub_sub_cancel]
    rw [hsub, symplO_disj (fun p hp' hp => hd p hp hp') hu2 (latO_mxAt hu'), sub_zero]
    exact (ann _ u huM).1 hu u' (hmono _ _ (fun p hp => Or.inl hp) hu')
  · rw [GlobalTheory.SplitScalar.symplO_sub_left, symplO_disj hd hu1 (latO_mxAt hu'), sub_zero]
    exact (ann _ u huM).1 hu u' (hmono _ _ (fun p hp => Or.inr hp) hu')

theorem isHalf_parts {S T : HSp D} {P : Pl D → Prop} {e : AE D} {u : WO S T} (h : IsHalf e u) :
    IsHalf e (idem P • u) ∧ IsHalf e (u - idem P • u) := by
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · simp only [Matrix.smul_apply, smul_eq_mul]
    rw [mul_left_comm, h i j]
  · simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    rw [mul_sub, h i j, mul_left_comm, h i j]

end GlobalTheory.DisjComb

namespace GlobalTheory.DisjComb

open GlobalTheory.FinPl.LatMem

theorem main : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (P P' : Pl D → Prop), (∀ p, P p → ¬ P' p) → (∀ e e' : WO S T →₀ ℂ, CombAt P e → CombAt P' e' → ∀ f, comb ψ S T e (comb ψ S T e' f) = comb ψ S T e' (comb ψ S T e f)) ∧ (∀ e : WO S T →₀ ℂ, CombAt P e → IsFinComb e ∧ ∀ LS LT f, Vac ψ S T LS LT P' f → Vac ψ S T LS LT P' (comb ψ S T e f)) ∧ (∀ χS χT (om : Om S T), IsWeilDatumO ψ S T χS χT om → ∀ e : WO S T →₀ ℂ, CombAt P e → ∀ g ∈ grpOff S P, ∀ h ∈ grpOff T P, ∀ f, IsThetaFunO ψ S T f → om (g, h) (comb ψ S T e f) = comb ψ S T e (om (g, h) f)) ∧ (∀ e e' : WO S T →₀ ℂ, CombAt (fun p => P p ∨ P' p) e → CombAt (fun p => P p ∨ P' p) e' → ∃ e'', CombAt (fun p => P p ∨ P' p) e'' ∧ ∀ f, comb ψ S T e'' f = comb ψ S T e (comb ψ S T e' f)) ∧ ∀ LS LT f, IsSelfDualC S LS → IsSelfDualC T LT → (Vac ψ S T LS LT (fun p => P p ∨ P' p) f ↔ Vac ψ S T LS LT P f ∧ Vac ψ S T LS LT P' f) := by
  intro D ψ hψ S T P P' hd
  have HC := GlobalTheory.HeisComb.main D ψ S T
  have hcomm : ∀ (e : WO S T →₀ ℂ), CombAt P e → ∀ w : WO S T, MxAt P' w → ∀ f,
      heisO ψ S T w (comb ψ S T e f) = comb ψ S T e (heisO ψ S T w f) := by
    intro e he w hw f
    have h := HC.2.1 e (Finsupp.single w 1) (fun x hx y hy => by
      rw [Finsupp.support_single_ne_zero _ one_ne_zero, Finset.mem_singleton] at hy
      subst hy
      exact symplO_disj hd (he x hx) hw) f
    simp only [comb_single] at h
    exact h.symm
  have hmono : ∀ (LS : Lat S) (LT : Lat T) (Q Q' : Pl D → Prop), (∀ p, Q p → Q' p) →
      latO S T (LS : Set _) (LT : Set _) Q ≤ latO S T (LS : Set _) (LT : Set _) Q' := by
    intro LS LT Q Q' hQ
    apply AddSubgroup.closure_mono
    rintro w ⟨α, hα, hv, rest⟩
    exact ⟨α, hα, fun v hv' => hv v fun hq => hv' (hQ v hq), rest⟩
  have hnsmul : ∀ (Q : Pl D → Prop) (x : WO S T), MxAt Q x → MxAt Q ((2 : ℕ) • x) := by
    intro Q x hx i j
    rw [Matrix.smul_apply]
    exact nsmul_mem (hx i j) 2
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro e e' he he' f
    exact HC.2.1 e e' (fun x hx y hy => symplO_disj hd (he x hx) (he' y hy)) f
  · intro e he
    have hfin : IsFinComb e := fun u hu => Matrix.ext fun i j => (mem_idAt_iff.1 (he u hu i j)).1
    refine ⟨hfin, fun LS LT f hf => ⟨HC.2.2.1 e f hf.1 hfin hψ, fun u hu => ?_, fun e' he' u hu hh => ?_⟩⟩
    · rw [hcomm e he _ (hnsmul P' u (latO_mxAt hu)), hf.2.1 u hu]
    · rw [hcomm e he u (latO_mxAt hu), hf.2.2 e' he' u hu hh]
  · intro χS χT om hom e he g hg h hh f hf
    unfold comb
    rw [map_sum]
    refine Finset.sum_congr rfl fun u hu => ?_
    rw [map_smul, hom.om_heis g h u f hf, actO_off hg hh (he u hu)]
  · intro e e' he he'
    obtain ⟨c'', hsupp, heq⟩ := HC.1 e e'
    refine ⟨c'', fun w hw => ?_, heq⟩
    obtain ⟨x, hx, y, hy, rfl⟩ := hsupp w hw
    intro i j
    rw [Matrix.add_apply]
    exact Ideal.add_mem _ (he x hx i j) (he' y hy i j)
  · intro LS LT f hLS hLT
    constructor
    · intro hf
      refine ⟨⟨hf.1, fun u hu => hf.2.1 u (hmono LS LT _ _ (fun p hp => Or.inl hp) hu),
        fun e he u hu hh => hf.2.2 e he u (hmono LS LT _ _ (fun p hp => Or.inl hp) hu) hh⟩,
        ⟨hf.1, fun u hu => hf.2.1 u (hmono LS LT _ _ (fun p hp => Or.inr hp) hu),
        fun e he u hu hh => hf.2.2 e he u (hmono LS LT _ _ (fun p hp => Or.inr hp) hu) hh⟩⟩
    · rintro ⟨hP, hP'⟩
      refine ⟨hP.1, fun u hu => ?_, fun e he u hu hh => ?_⟩
      · obtain ⟨hm1, hm2, hl1, hl2⟩ := split_latO ψ hψ hLS hLT hd hu
        have hsum : u = idem P • u + (u - idem P • u) := (add_sub_cancel _ _).symm
        rw [hsum, nsmul_add, GlobalTheory.SplitScalar.heisO_add_of_orth ψ S T (symplO_disj hd (hnsmul P _ hm1) (hnsmul P' _ hm2)),
          hP'.2.1 _ hl2, hP.2.1 _ hl1]
      · obtain ⟨hm1, hm2, hl1, hl2⟩ := split_latO ψ hψ hLS hLT hd hu
        obtain ⟨h1, h2⟩ := isHalf_parts (P := P) hh
        have hsum : u = idem P • u + (u - idem P • u) := (add_sub_cancel _ _).symm
        rw [hsum, GlobalTheory.SplitScalar.heisO_add_of_orth ψ S T (symplO_disj hd hm1 hm2), hP'.2.2 e he _ hl2 h2,
          hP.2.2 e he _ hl1 h1]

end GlobalTheory.DisjComb
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsThetaFunOTargetSliceOrthogonalSumStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer InDual)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isThetaFunO_target_slice_orthogonal_sum : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S A L T : HSp D) (o : OrthDec S A L) (f : WO T S → ℂ) (y : WO T L), IsThetaFunO ψ T S f → IsThetaFunO ψ T A (fun w => f ((o.resT T).symm (w, y))) := by
  first | exact @GlobalTheory.FinPl.ExtZero.isThetaFunO_sliceT | exact GlobalTheory.FinPl.ExtZero.isThetaFunO_sliceT | (intros; apply GlobalTheory.FinPl.ExtZero.isThetaFunO_sliceT <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaIsotropicStabiliserFinitePlace
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW
namespace GlobalTheory.Core.Rk.IwFin

theorem iwasawa_fin : ∀ (D : D7) (T T₀ : HSp D) (r : ℕ) (d : HypDec T T₀ r), (∀ v : FinPl D, (2 : 𝓞 D.host.F) ∈ v.asIdeal → Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) v) → ∀ (v : FinPl D) (y : Gv T v), ∃ q k : Gv T v, emb D.sp.cm.sig T.gram v q ∈ stab d ∧ k ∈ stabLoc D.sp.cm.sig T.gram (frameLat T) v ∧ y = q * k := by
  intro D T T₀ r d _h2 v y
  by_cases hv : Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) v
  · exact GlobalTheory.T.iwasawa_isotropic_stabiliser_split_place D T T₀ r d v hv y
  · exact GlobalTheory.T.iwasawa_isotropicStabilizer_inertPlace D T T₀ r d v hv y

end GlobalTheory.Core.Rk.IwFin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastSeeSawDatumIsTwoVariableThetaFunction
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LastBiTheta

variable {D : D7}

theorem sOH_zero_left (S T : HSp D) (y : WO S T) : symplOH S T 0 y = 0 := by
  simp [symplOH, symplO, hO]

theorem sOH_zero_right (S T : HSp D) (x : WO S T) : symplOH S T x 0 = 0 := by
  simp [symplOH, symplO, hO]

theorem sOH_resS_symm {V₀ A L : HSp D} (o : OrthDec V₀ A L) (S : HSp D) (a a' : WO A S) (b b' : WO L S) :
    symplOH V₀ S ((o.resS S).symm (a, b)) ((o.resS S).symm (a', b')) = symplOH A S a a' + symplOH L S b b' := by
  rw [o.symplOH_resS, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]

theorem quasi_of_mem {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {f : WO S T → ℂ} (h : IsThetaFunO ψ S T f)
    {x : WO S T} (hx : x ∈ ratMx D T.rank S.rank) (w : WO S T) : f (x + w) = ψ (-(symplOH S T x w)) * f w := by
  obtain ⟨γ, rfl⟩ := hx
  exact h.quasi γ w

theorem resS_symm_mem {V₀ A L : HSp D} (o : OrthDec V₀ A L) (S : HSp D) {a : WO A S} {b : WO L S}
    (ha : a ∈ ratMx D S.rank A.rank) (hb : b ∈ ratMx D S.rank L.rank) :
    (o.resS S).symm (a, b) ∈ ratMx D S.rank V₀.rank := by
  rw [OrthDec.resS_symm_apply]
  exact add_mem (ratMx_mul ha (rat_mem _)) (ratMx_mul hb (rat_mem _))

theorem resS_symm_map {B : Type} [CommRing B] (φ : AE D →+* B) {V₀ A L : HSp D} (o : OrthDec V₀ A L) (S : HSp D)
    {a : WO A S} {b : WO L S} (ha : a.map φ = 0) (hb : b.map φ = 0) : ((o.resS S).symm (a, b)).map φ = 0 := by
  rw [OrthDec.resS_symm_apply, Matrix.map_add φ (map_add φ), map_mul_eq_zero_left φ ha, map_mul_eq_zero_left φ hb,
    add_zero]

set_option maxHeartbeats 1000000 in

theorem isBiTheta_lastBi : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (V₀ A L S X T L'' : HSp D) (o : OrthDec V₀ A L) (o'' : OrthDec X T L'') (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E), τᴴ * (L.gram * τ) = (-(D.host.xi0 * star D.host.xi0)) • L''.gram → ∀ (Ξ : WO V₀ S → ℂ) (Φ₂ : WO S T → ℂ), IsThetaFunO ψ V₀ S Ξ → IsThetaFunO ψ S T Φ₂ → IsBiTheta ψ A S X (lastBi o o'' τ Ξ Φ₂) := by
  intro D ψ _ V₀ A L S X T L'' o o'' τ hτ Ξ Φ₂ hΞ hΦ
  obtain ⟨kadd, kcont, krat, -, ksympl, kpart⟩ := GlobalTheory.LinkKappa.kappa_props D L L'' S τ (-1)
    (by rw [Int.cast_neg, Int.cast_one, neg_one_mul]; exact hτ) (kap τ S) (fun _ => rfl)
  have kH : ∀ w w', symplOH L S (kap τ S w) (kap τ S w') = symplOH S L'' w w' := fun w w' => by
    unfold symplOH
    rw [ksympl]
    simp only [Int.cast_neg, Int.cast_one, neg_one_mul, neg_neg]
  have hC : ∀ u v, lastBi o o'' τ Ξ Φ₂ u v =
      Φ₂ (o''.resT S v).1 * Ξ ((o.resS S).symm (u, kap τ S (o''.resT S v).2)) := fun _ _ => rfl
  let K : WO S L'' →+ WO L S := AddMonoidHom.mk' (kap τ S) kadd
  let P1 : WO S X →+ WO S T := (AddMonoidHom.fst _ _).comp (o''.resT S).toAddMonoidHom
  let P2 : WO S X →+ WO S L'' := (AddMonoidHom.snd _ _).comp (o''.resT S).toAddMonoidHom
  have cP1 : Continuous fun b : WO S X => (o''.resT S b).1 := continuous_fst.comp (o''.continuous_resT S)
  have cP2 : Continuous fun b : WO S X => (o''.resT S b).2 := continuous_snd.comp (o''.continuous_resT S)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    show Continuous fun p : WO A S × WO S X =>
      Φ₂ (o''.resT S p.2).1 * Ξ ((o.resS S).symm (p.1, kap τ S (o''.resT S p.2).2))
    exact (hΦ.cont.comp (cP1.comp continuous_snd)).mul
      (hΞ.cont.comp ((o.continuous_resS_symm S).comp (continuous_fst.prodMk (kcont.comp (cP2.comp continuous_snd)))))
  ·
    intro n L₁ L₂ hL₁ hL₂ hf₁ hf₂ u v
    let M₁ : (Fin n → ℝ) →+ WO S T := P1.comp L₂
    let M₂ : (Fin n → ℝ) →+ WO V₀ S := (o.resS S).symm.toAddMonoidHom.comp (AddMonoidHom.prod L₁ (K.comp (P2.comp L₂)))
    have cM₁ : Continuous M₁ := cP1.comp hL₂
    have cM₂ : Continuous M₂ := (o.continuous_resS_symm S).comp (hL₁.prodMk (kcont.comp (cP2.comp hL₂)))
    have fM₁ : ∀ t, (M₁ t).map (finPart D) = 0 := fun t => map_mul_eq_zero_right (finPart D) _ (hf₂ t)
    have fM₂ : ∀ t, (M₂ t).map (finPart D) = 0 := fun t =>
      resS_symm_map (finPart D) o S (hf₁ t) ((kpart _).2 (map_mul_eq_zero_right (finPart D) _ (hf₂ t)))
    have e : (fun t => lastBi o o'' τ Ξ Φ₂ (u + L₁ t) (v + L₂ t)) = fun t =>
        Φ₂ ((o''.resT S v).1 + M₁ t) * Ξ ((o.resS S).symm (u, kap τ S (o''.resT S v).2) + M₂ t) := by
      funext t
      rw [hC]
      show Φ₂ (o''.resT S (v + L₂ t)).1 * Ξ ((o.resS S).symm (u + L₁ t, kap τ S (o''.resT S (v + L₂ t)).2)) =
        Φ₂ ((o''.resT S v).1 + (o''.resT S (L₂ t)).1) *
          Ξ ((o.resS S).symm (u, kap τ S (o''.resT S v).2) + (o.resS S).symm (L₁ t, kap τ S (o''.resT S (L₂ t)).2))
      rw [map_add, Prod.fst_add, Prod.snd_add, kadd, ← map_add, Prod.mk_add_mk]
    rw [e]
    exact (hΦ.smooth n M₁ cM₁ fM₁ _).mul (hΞ.smooth n M₂ cM₂ fM₂ _)
  ·
    intro γ u v
    rw [hC, hC]
    have e : (o.resS S).symm (ratW S A γ + u, kap τ S (o''.resT S v).2) =
        (o.resS S).symm (ratW S A γ, 0) + (o.resS S).symm (u, kap τ S (o''.resT S v).2) := by
      rw [← map_add, Prod.mk_add_mk, zero_add]
    have hγ : ratW S A γ ∈ ratMx D S.rank A.rank := rat_mem γ
    rw [e, quasi_of_mem hΞ (resS_symm_mem o S hγ (zero_mem _)), sOH_resS_symm, sOH_zero_left, add_zero]
    ring
  ·
    intro γ u v
    rw [hC, hC]
    have h1 : (o''.resT S (ratW X S γ)).1 ∈ ratMx D T.rank S.rank := ratMx_mul (rat_mem _) (rat_mem γ)
    have h2 : (o''.resT S (ratW X S γ)).2 ∈ ratMx D L''.rank S.rank := ratMx_mul (rat_mem _) (rat_mem γ)
    have e : (o.resS S).symm (u, kap τ S ((o''.resT S (ratW X S γ)).2 + (o''.resT S v).2)) =
        (o.resS S).symm (0, kap τ S (o''.resT S (ratW X S γ)).2) + (o.resS S).symm (u, kap τ S (o''.resT S v).2) := by
      rw [kadd, ← map_add, Prod.mk_add_mk, zero_add]
    have ph : ψ (-symplOH S X (ratW X S γ) v) = ψ (-symplOH S T (o''.resT S (ratW X S γ)).1 (o''.resT S v).1) *
        ψ (-symplOH S L'' (o''.resT S (ratW X S γ)).2 (o''.resT S v).2) := by
      rw [← AddChar.map_add_eq_mul, o''.symplOH_resT S (ratW X S γ) v]
      exact congrArg ψ (neg_add _ _)
    rw [map_add, Prod.fst_add, Prod.snd_add, e, quasi_of_mem hΦ h1,
      quasi_of_mem hΞ (resS_symm_mem o S (zero_mem _) (krat _ h2)), sOH_resS_symm, sOH_zero_left, zero_add, kH, ph]
    ring
  ·
    obtain ⟨U, hUo, hU⟩ := hΞ.level
    let iA : WO A S →+ WO V₀ S := (o.resS S).symm.toAddMonoidHom.comp (AddMonoidHom.inl _ _)
    have ciA : Continuous fun a : WO A S => (o.resS S).symm (a, 0) :=
      (o.continuous_resS_symm S).comp (continuous_id.prodMk continuous_const)
    refine ⟨U.comap iA, hUo.preimage ciA, fun a ha hinf v => ?_⟩
    funext u
    have h1 := congrFun (hU (iA a) ha (resS_symm_map (infPart D) o S hinf (by simp)))
      ((o.resS S).symm (u, kap τ S (o''.resT S v).2))
    have e : (o.resS S).symm (u + a, kap τ S (o''.resT S v).2) =
        (o.resS S).symm (u, kap τ S (o''.resT S v).2) + iA a := by
      show _ = _ + (o.resS S).symm (a, 0)
      rw [← map_add, Prod.mk_add_mk, add_zero]
    have ph : symplOH V₀ S ((o.resS S).symm (u, kap τ S (o''.resT S v).2)) (iA a) = symplOH A S u a := by
      show symplOH V₀ S ((o.resS S).symm (u, _)) ((o.resS S).symm (a, 0)) = _
      rw [sOH_resS_symm, sOH_zero_right, add_zero]
    simp only [heisO] at h1 ⊢
    rw [ph] at h1
    rw [hC, hC, e, ← h1]
    ring
  ·
    obtain ⟨UΞ, hUΞo, hUΞ⟩ := hΞ.level
    obtain ⟨UΦ, hUΦo, hUΦ⟩ := hΦ.level
    let jL : WO S X →+ WO V₀ S := (o.resS S).symm.toAddMonoidHom.comp ((AddMonoidHom.inr _ _).comp (K.comp P2))
    have cjL : Continuous fun b : WO S X => (o.resS S).symm (0, kap τ S (o''.resT S b).2) :=
      (o.continuous_resS_symm S).comp (continuous_const.prodMk (kcont.comp cP2))
    refine ⟨UΦ.comap P1 ⊓ UΞ.comap jL, (hUΦo.preimage cP1).inter (hUΞo.preimage cjL), fun b hb hinf u => ?_⟩
    have hT : (o''.resT S b).1.map (infPart D) = 0 := map_mul_eq_zero_right (infPart D) _ hinf
    have hJ : (jL b).map (infPart D) = 0 :=
      resS_symm_map (infPart D) o S (by simp) ((kpart _).1 (map_mul_eq_zero_right (infPart D) _ hinf))
    show heisO ψ S X b (o''.boxT S Φ₂ fun w => Ξ ((o.resS S).symm (u, kap τ S w))) =
      o''.boxT S Φ₂ fun w => Ξ ((o.resS S).symm (u, kap τ S w))
    rw [o''.heisO_boxT, hUΦ (o''.resT S b).1 hb.1 hT]
    congr 1
    funext w
    have h2 := congrFun (hUΞ (jL b) hb.2 hJ) ((o.resS S).symm (u, kap τ S w))
    have e : (o.resS S).symm (u, kap τ S (w + (o''.resT S b).2)) = (o.resS S).symm (u, kap τ S w) + jL b := by
      show _ = _ + (o.resS S).symm (0, kap τ S (o''.resT S b).2)
      rw [kadd, ← map_add, Prod.mk_add_mk, add_zero]
    have ph : symplOH V₀ S ((o.resS S).symm (u, kap τ S w)) (jL b) = symplOH S L'' w (o''.resT S b).2 := by
      show symplOH V₀ S ((o.resS S).symm (u, _)) ((o.resS S).symm (0, kap τ S (o''.resT S b).2)) = _
      rw [sOH_resS_symm, sOH_zero_right, zero_add, kH]
    simp only [heisO] at h2 ⊢
    rw [ph] at h2
    rw [e]
    exact h2

end GlobalTheory.LastBiTheta

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticeOrthogonalSumLineAtSplitPlaceStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_orthogonal_sum_line_at_split_place : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n' : Type) [Fintype n'] [DecidableEq n'] (S A L : HSp D) (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E), IsLineVec L ζ → ∀ (α : Frame p A n') (α₀ : Frame p S (n' ⊕ Fin 1)), IsSumFrame o ζ α α₀ → p.UnitAA → ∀ (LA : Lat A) (LS : Lat S) (ΛA : Submodule 𝒪[k] (n' → k)), IsSelfDualC A LA → IsSelfDualC S LS → α.IsLat LA ΛA → α₀.IsLat LS (lastKer ΛA) → ∃ LL : Lat L, OrthAt o LS LA LL p.v := by
  first | exact @GlobalTheory.LineSplitAt.orthAt_of_frames | exact GlobalTheory.LineSplitAt.orthAt_of_frames | (intros; apply GlobalTheory.LineSplitAt.orthAt_of_frames <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LiftPairPositiveDefiniteWittIndexZeroCartanStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.LiftRows GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liftPair_positiveDefinite_wittIndexZero_cartan : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → (∃ L : SizeData₂ D, Nonempty (ParameterChoice' D L)) → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), GlobalTheory.Cusp.wittIndex (Vc D i) = 0 ∧ (Wc D i).rank < D.R.t ∧ ∃ cA : GlobalTheory.Mem.Th.CptF (Wc D i), GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.HidaSetting R.θ (Wc D i) (Vc D i) (cart (R.MW i σ)) (fun _ => 1) D.R.t cA ∧ ∀ U ∈ R.Wall i σ, ∀ v : ∀ ρ, lowT (R.MW i σ) ρ, U (fun ρ => v ρ) ∈ GlobalTheory.Cusp.A0 R.θ (Wc D i) cA := by
  first | exact @GlobalTheory.PairSetting.main | exact GlobalTheory.PairSetting.main | (intros; apply GlobalTheory.PairSetting.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LineContractionSplitPlaceLocalModelStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lineContraction_splitPlace_localModel : ∀ (D : D7), GlobalTheory.LocFlat.ContrFactor → ContrLoc D := by
  first | exact @GlobalTheory.ContrLocProof.contrLoc | exact GlobalTheory.ContrLocProof.contrLoc | (intros; apply GlobalTheory.ContrLocProof.contrLoc <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocK
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.QuotientFiniteLevel

variable {D : D7} {c : Comm D} {v : VCom c} {t : Tup c}

def locK (F : QFam v t) (j σ : ℕ) (h : j + 2 * (σ + 1) + 2 = D.R.m) (i : Fin F.r) : Subgroup (GA D (c.V (j + 1))) :=
  ((F.Q i).T.lev (j + 1) ((F.Q i).s - j) (by have := (F.Q i).hs; omega)).J.map
    ((F.Q i).gl (j + 1) ((F.Q i).s - j) (by have := (F.Q i).hs; omega))

def qK (F : QFam v t) (j σ : ℕ) (h : j + 2 * (σ + 1) + 2 = D.R.m) : Subgroup (GA D (c.V (j + 1))) :=
  ⨆ i, locK F j σ h i

end GlobalTheory.QuotientFiniteLevel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaContractionExtendByZeroDoubleCombinationStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory Matrix
open GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_contraction_extendByZero_double_combination : ∀ (D : D7) (ρ σ : ℕ) (B : BesLev D ρ) (B' : BesLev D σ) (l : Link B B'.L B'.ζ) (S : HSp D) (vL : VolM D B'.L.rank S.rank) (ψ : AddChar (AF D.host.F) ℂ) (f₁ : WO B.V₀ S → ℂ) (f₂ : WO S B'.V₀ → ℂ), (∀ (u : WO B.A S) (v : WO S B'.A), IntegrableOn (fun w => f₂ ((B'.o.resT S).symm (v, w)) * f₁ ((B.o.resS S).symm (u, l.κ S w))) vL.𝓕 vL.μ) → ∀ (c : WO B.A S →₀ ℂ) (c' : WO S B'.A →₀ ℂ), contr l S vL (comb ψ B.V₀ S (extS B.o S c) f₁) (comb ψ S B'.V₀ (extT B'.o S c') f₂) = biComb ψ B.A S B'.A c c' (contr l S vL f₁ f₂) := by
  first | exact @GlobalTheory.ContrComb.contr_comb_ext | exact GlobalTheory.ContrComb.contr_comb_ext | (intros; apply GlobalTheory.ContrComb.contr_comb_ext <;> assumption)
end

