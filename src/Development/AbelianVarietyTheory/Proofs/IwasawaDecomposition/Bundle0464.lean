import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NeZeroTop
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianFormLastCoordinateUniformizerVectorSelf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0450
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0271
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0453
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0014
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0027
import Formalism.LocalToGlobal.KernelLattices.TopPin
import Formalism.LocalToGlobal.KernelLattices.Bundle0001
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0008
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.Bundle0007
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.PeriodLatticeFinitelyGenerated
import Formalism.GradedWeylDivisibility.FinalD
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
import Formalism.LocalRingCardinality.FactDelDualNabla
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0053
import Formalism.LocalToGlobal.IndefiniteReal.LinksExistW
import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0848
import Formalism.LocalToGlobal.IndefiniteReal.HeckeNonvanishing.Imports
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DivisionPairOfAdelicFormsFaceColumnsData
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0036
import Formalism.LocalToGlobal.Divisibility.Bundle0005

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PointOverXHasAdelicPointBlockExtendMul
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TilQ

section ExtM

variable {A : Type} [CommRing A] {N n : ℕ} (hN : N = n + 1) (g : Matrix (Fin n) (Fin n) A)

theorem extM_iC_iC (i j : Fin n) : TilX.extM hN g (Br.iC hN i) (Br.iC hN j) = g i j := by
  simp [TilX.extM, Br.iC]

theorem extM_iC_iL (i : Fin n) : TilX.extM hN g (Br.iC hN i) (Br.iL hN) = 0 := by
  simp [TilX.extM, Br.iC, Br.iL]

theorem extM_iL_iC (j : Fin n) : TilX.extM hN g (Br.iL hN) (Br.iC hN j) = 0 := by
  simp [TilX.extM, Br.iC, Br.iL]

theorem extM_iL_iL : TilX.extM hN g (Br.iL hN) (Br.iL hN) = 1 := by
  simp [TilX.extM, Br.iL]

end ExtM

section Single

variable {E : Type} [Field E] {N n : ℕ} (hN : N = n + 1)

theorem prH_single_iC (j : Fin n) : GlobalTheory.TopStep.prH E hN (Pi.single (Br.iC hN j) 1) = Pi.single j 1 := by
  funext i
  rw [GlobalTheory.TopStep.prH_apply]
  by_cases h : i = j
  · subst h
    simp
  · rw [Pi.single_eq_of_ne (fun e => h (Br.iC_inj hN e)), Pi.single_eq_of_ne h]

theorem prH_single_iL : GlobalTheory.TopStep.prH E hN (Pi.single (Br.iL hN) 1) = 0 := by
  funext i
  rw [GlobalTheory.TopStep.prH_apply, Pi.single_eq_of_ne]
  · rfl
  · intro e
    have := congrArg Fin.val e
    simp [Br.iC, Br.iL] at this
    omega

end Single

theorem adAt_of_bc_one {B : Base} {n : ℕ} {k : GA B n} (P : HeightOneSpectrum (𝓞 B.host.E))
    (hk : bc (prV (E := B.host.E) (P.under (𝓞 B.host.F))) k = 1) (i j : Fin n) :
    adAt B.host.F P (k.1 i j) = (1 : Matrix (Fin n) (Fin n) (P.adicCompletion B.host.E)) i j := by
  have h2 : prV (E := B.host.E) (P.under (𝓞 B.host.F))
      (k.1 i j - (1 : Matrix (Fin n) (Fin n) (AfE B.host.F B.host.E)) i j) = 0 := by
    have h3 := congrArg (fun g : GL (Fin n) _ => g.1 i j) hk
    simp only [Units.val_one] at h3
    have h4 : prV (E := B.host.E) (P.under (𝓞 B.host.F)) (k.1 i j) = (1 : Matrix (Fin n) (Fin n) _) i j := h3
    rw [map_sub, h4, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have h3 := TilX.adAt_eq_zero_of_prV P _ h2
  rw [map_sub, sub_eq_zero] at h3
  refine h3.trans ?_
  rw [Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

set_option maxHeartbeats 1600000 in

theorem pt_tilF_gen : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → Pins B X → ∀ (l : I.Laws) (Z : Later B (I.cols l)) (u : B.Word) (a : I.ι) (k t : GA B (B.R.N B.R.m)), (∃ p : DecoF B.fields.E (B.R.N B.R.m) ∅ ∅ ∅, PtOf k p ∧ p.deco.1.N = stdLat B.fields.E (B.R.N B.R.m)) → (∀ v : HeightOneSpectrum (𝓞 B.host.F), (B.T u : 𝓞 B.host.F) ∉ v.asIdeal → bc (prV (E := B.host.E) v) k = 1) → (∀ (P : (B.primes X).vT u) (r j : Fin (B.R.N B.R.m)), r.1 + 1 = (B.R.N B.R.m) → HasRes P.1 (adAt B.host.F P.1 ((k⁻¹ : GA B (B.R.N B.R.m)).1 r j)) (if j = r then Ideal.Quotient.mk P.1.asIdeal (B.fields.conjO (X.piT u)) else 0)) → t ∈ K1 B.sp.cm (B.R.N B.R.m) ((B.primes X).vT u) (B.primes X).vGs → (∀ (P : I.Q a) (i j : Fin (B.R.N B.R.m)), adAt B.host.F P.1 (t.1 i j) = algebraMap B.host.E _ (if i = j then (if i.1 + 1 = (B.R.N B.R.m) then ((X.piT u : 𝓞 B.host.E) : B.host.E) else 1) else 0)) → ∀ (d : XPt (B.primes X) B.R I.sel (I.tup a)) (g' : GA B (B.R.N B.R.m - 1)) (g : GA B (B.R.N B.R.m)), PtOf g' d → IsExt (I.rec7 l Z) (z0 X u) (inclE (F := (I.rec7 l Z).host.F) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F)) g'.1 g.1 → PtOf (g * (k * t)) (tilF I.sel (I.tup a) u d) := by
  intro B X I hI hP l Z u a k t hk1 hk2 hk3 ht htP d g' g hg' hext
  haveI : IsEmpty ↥(∅ : Finset (HeightOneSpectrum (𝓞 B.fields.E))) := ⟨fun x => Finset.notMem_empty _ x.2⟩
  obtain ⟨p0, hp0, hN0⟩ := hk1
  have hPr := (base_fields_primes_ok B X).2.1
  have hN := N_m_succ B.R
  have hgw : ∀ w : (B.primes X).vGs, ∃ i, ((B.primes X).g i : 𝓞 B.fields.E) ∈ w.1.asIdeal := by
    intro w
    have h1 : ∃ i, w.1 ∈ (B.primes X).vG i := by
      have h0 := w.2
      unfold Primes.vGs at h0
      simp only [Finset.mem_union] at h0
      rcases h0 with h | h
      exacts [⟨0, h⟩, ⟨1, h⟩]
    obtain ⟨i, hi⟩ := h1
    refine ⟨i, ?_⟩
    rw [← hPr.piG_norm i]
    exact w.1.asIdeal.mul_mem_left _ (mem_of_mem_divs hi)
  have hpi1 : ∀ w : (B.primes X).vGs, (B.primes X).piT u - 1 ∈ w.1.asIdeal := by
    intro w
    obtain ⟨i, hi⟩ := hgw w
    obtain ⟨c, hc⟩ := hPr.piT_cong u
    rw [hc]
    refine w.1.asIdeal.mul_mem_right _ ?_
    have hd : (B.primes X).g i ∣ (B.primes X).cond * ((B.primes X).g 0 * (B.primes X).g 1) ^ 2 := by
      refine dvd_mul_of_dvd_right (dvd_pow ?_ two_ne_zero) _
      fin_cases i
      · exact dvd_mul_right _ _
      · exact dvd_mul_left _ _
    obtain ⟨c', hc'⟩ := hd
    rw [hc']
    push_cast
    exact w.1.asIdeal.mul_mem_right _ hi
  have hTw : ∀ w : (B.primes X).vGs, (B.T u : 𝓞 B.host.F) ∉ (w.1.under (𝓞 B.host.F)).asIdeal := by
    intro w hT
    obtain ⟨i, hi⟩ := hgw w
    have h1 : ((B.primes X).T u : 𝓞 B.fields.E) ∈ w.1.asIdeal := by
      have h2 : algebraMap (𝓞 B.host.F) (𝓞 B.host.E) (B.T u : 𝓞 B.host.F) ∈ w.1.asIdeal := hT
      rw [map_natCast] at h2
      exact h2
    have hc : Nat.Coprime ((B.primes X).T u) ((B.primes X).g i) :=
      (Nat.coprime_primes (hPr.T_prime u) (hPr.g_prime i)).2 (hPr.T_ne_g u i)
    have h3 : ((1 : ℕ) : 𝓞 B.fields.E) ∈ w.1.asIdeal := by
      obtain ⟨a, b, hab⟩ := (Nat.isCoprime_iff_coprime.2 hc)
      have e : ((1 : ℤ) : 𝓞 B.fields.E) = (a : 𝓞 B.fields.E) * ((B.primes X).T u : 𝓞 B.fields.E) +
          (b : 𝓞 B.fields.E) * ((B.primes X).g i : 𝓞 B.fields.E) := by
        rw [← hab]; push_cast; ring
      have e' : ((1 : ℕ) : 𝓞 B.fields.E) = ((1 : ℤ) : 𝓞 B.fields.E) := by simp
      rw [e', e]
      exact add_mem (w.1.asIdeal.mul_mem_left _ h1) (w.1.asIdeal.mul_mem_left _ hi)
    exact w.1.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using h3))
  have hkw : ∀ (w : (B.primes X).vGs) (i j : Fin (B.R.N B.R.m)),
      adAt B.host.F w.1 ((k⁻¹ : GA B (B.R.N B.R.m)).1 i j) = (1 : Matrix (Fin (B.R.N B.R.m)) (Fin (B.R.N B.R.m)) (w.1.adicCompletion B.host.E)) i j := by
    intro w i j
    refine adAt_of_bc_one w.1 ?_ i j
    rw [map_inv, hk2 _ (hTw w), inv_one]
  have hA := TilX.isPtOf_tilFr (hc := B.sp.cm) (ST := (B.primes X).vT u) hN (conj_piT_notMem hPr u) hpi1
    (hg'.extTo (Finset.empty_subset _) (Finset.disjoint_empty_right _)) hp0.uni
    (by have := hp0.lat; rwa [hN0] at this) hkw hk3
  obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.1 ht
  have hB := (isPtOf_mul_J0 B.host.F B.host.E B.sp.cm _ ((B.primes X).vT u) (B.primes X).vGs ∅ _ m.1 _
    (tilFr (ST := (B.primes X).vT u) hN ((B.primes X).piT u) (extTo ∅ d)) 1).2.1 rfl hA m.2 (by rw [inv_one]; exact hm)
  obtain ⟨-, -, hiX, -⟩ := GlobalTheory.T.trueColumn_spaces_standard_in_frameCoords I hI hP l Z
  have hpi0 : ((X.piT u : 𝓞 B.host.E) : B.host.E) ≠ 0 := by
    intro h0
    have h1 : X.piT u = 0 := RingOfIntegers.ext h0
    have h2 := hPr.piT_norm u
    have h3 : (B.primes X).piT u = 0 := h1
    rw [h3, zero_mul] at h2
    exact (hPr.T_prime u).ne_zero (by exact_mod_cast h2.symm)
  have hgext : g = TilX.extGL hN g' := by
    refine Units.ext (TilX.eq_extM_of_ext hN (inclE (F := B.host.F) (FiniteAdeleRing (𝓞 B.host.F) B.host.F)) hpi0
      (TilX.iXm_apply hiX hN) hext.1 ?_)
    have h2 := hext.2
    have hz : z0 X u = Pi.single (Br.iL (N_m_succ B.R)) ((X.piT u : 𝓞 B.host.E) : B.host.E) := TilX.lastCoordinateUniformizerVector_eq_single u
    rw [hz] at h2
    exact h2
  have hQ := PerLaw.piT_notMem_Q hI u a
  have hQ0 : ∀ P : (∅ : Finset (HeightOneSpectrum (𝓞 B.fields.E))), (B.primes X).piT u ∉ P.1.asIdeal := fun P => isEmptyElim P
  have e : (tilF I.sel (I.tup a) u d).deco =
      (tilFr (ST := (B.primes X).vT u) hN ((B.primes X).piT u) (extTo ∅ d)).deco := by
    rw [tilF_deco I.sel (I.tup a) hPr u hQ d, tilFr_deco hN (conj_piT_notMem hPr u) (piT_notMem_vGs hPr u) hQ0, extTo_deco]
  rw [show ((1, 1, 1) : UF B.fields.E (B.R.N B.R.m) × GLG B.fields.E (B.R.N B.R.m) (B.primes X).vGs ×
    GLQ B.fields.E (B.R.N B.R.m) ∅) = 1 from rfl, one_smul] at hB
  rw [hgext, ← mul_assoc]
  refine ⟨hB.uni, ?_, ?_, ?_, ?_⟩
  · rw [e]; exact hB.lat
  · rw [e]; exact hB.f
  · rw [e]; exact hB.be
  · intro P i j
    have hTq : (B.T u : 𝓞 B.host.F) ∉ (P.1.under (𝓞 B.host.F)).asIdeal := by
      intro hT
      have h2 : algebraMap (𝓞 B.host.F) (𝓞 B.host.E) (B.T u : 𝓞 B.host.F) ∈ P.1.asIdeal := hT
      rw [map_natCast] at h2
      exact T_notMem_QE I.sel (I.tup a) u hPr hI.sel_ok (hI.T_mem u) P.1 P.2 h2
    have hkP := adAt_of_bc_one P.1 (hk2 _ hTq)
    have e1 : adAt B.host.F P.1 (((TilX.extGL hN g' * k * (J0 B.sp.cm (B.R.N B.R.m) ((B.primes X).vT u)).subtype m :
        GA B (B.R.N B.R.m)) : Matrix (Fin (B.R.N B.R.m)) (Fin (B.R.N B.R.m)) (AfE B.host.F B.host.E)) i j) =
        adAt B.host.F P.1 (TilX.extM hN g'.1 i j) *
          adAt B.host.F P.1 ((((J0 B.sp.cm (B.R.N B.R.m) ((B.primes X).vT u)).subtype m : GA B (B.R.N B.R.m)) :
            Matrix (Fin (B.R.N B.R.m)) (Fin (B.R.N B.R.m)) (AfE B.host.F B.host.E)) j j) := by
      rw [Units.val_mul, Units.val_mul, Matrix.mul_apply, map_sum, Finset.sum_eq_single j]
      · rw [map_mul, Matrix.mul_apply, map_sum, Finset.sum_eq_single j, map_mul, hkP, Matrix.one_apply_eq, mul_one]
        · rfl
        · intro l _ hl
          rw [map_mul, hkP, Matrix.one_apply_ne hl, mul_zero]
        · simp
      · intro l _ hl
        rw [map_mul, htP P l j, if_neg hl, map_zero, mul_zero]
      · simp
    rw [e1, htP P j j, if_pos rfl, tilF_fr I.sel (I.tup a) hPr u hQ d P]
    rcases GlobalTheory.TopStep.idx_cases hN i with ⟨i', rfl⟩ | rfl <;> rcases GlobalTheory.TopStep.idx_cases hN j with ⟨j', rfl⟩ | rfl
    · have h1 : ¬ ((Br.iC hN j').1 + 1 = B.R.N B.R.m) := by
        show ¬ (j'.1 + 1 = B.R.N B.R.m)
        have := j'.2
        omega
      rw [if_neg h1, map_one, mul_one, extM_iC_iC, hg'.fr P i' j']
      congr 1
      exact ((congrFun (GlobalTheory.TopStep.prH_sumE hN (d.fr P) _ (Pi.single (Br.iC hN j') 1)) i').trans
        (by rw [prH_single_iC])).symm
    · have h0 := (congrFun (GlobalTheory.TopStep.prH_sumE hN (d.fr P) (unitOf ((B.primes X).piT u)) (Pi.single (Br.iL hN) 1)) i').trans
        (by rw [prH_single_iL, map_zero])
      rw [extM_iC_iL, map_zero, zero_mul]
      exact (congrArg (algebraMap B.host.E _) h0).trans (map_zero _) |>.symm
    · rw [extM_iL_iC, map_zero, zero_mul, GlobalTheory.TopStep.sumE_last, Pi.single_eq_of_ne, mul_zero, map_zero]
      intro e
      have := congrArg Fin.val e
      simp [Br.iC, Br.iL] at this
      omega
    · have h1 : (Br.iL hN).1 + 1 = B.R.N B.R.m := by
        show (B.R.N B.R.m - 1) + 1 = B.R.N B.R.m
        omega
      rw [if_pos h1, extM_iL_iL, map_one, one_mul, GlobalTheory.TopStep.sumE_last, Pi.single_eq_same, mul_one,
        unitOf_val (hQ P)]

end GlobalTheory.Mem.Col2.TilQ

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ProdBideterminantsEqColumnChoiceMinorProductStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem.CanonicalSurjection

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prod_bideterminants_eq_columnChoice_minorProduct : ∀ (D : D7) (K : Type) [CommRing K] (N : ℕ) (nu : Bool × Formalism.MainNotions.G.HH D → YoungDiagram)
    (ν : D.what₂.Tau → Fin N → ℕ), NuFits D nu ν → ∀ g : D.what₂.Tau → Matrix (Fin N) (Fin N) K → K,
    (∀ τ, g τ ∈ bideterminantFunctionsOfShape K N (ν τ)) → ∃ J : KM.ColChoice N nu, ∀ y : D.what₂.Tau → Matrix (Fin N) (Fin N) K,
      ∏ τ, g τ (y τ) = GL3Columns.minY N nu J (fun s => GL3Columns.colsOf (y (tauPl D s))) := by
  first | exact @GlobalTheory.Mem.CanonicalSurjection.prod_bidFns_eq_minY | exact GlobalTheory.Mem.CanonicalSurjection.prod_bidFns_eq_minY | (intros; apply GlobalTheory.Mem.CanonicalSurjection.prod_bidFns_eq_minY <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RealDatumPrerequisitesUpdateModels
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.WeilFull
open scoped TensorProduct InnerProductSpace

namespace GlobalTheory.Mem.KeepRef

attribute [local instance] Formalism.BasicNotions.Host.cmStar

scoped macro "obt " p:Lean.Parser.Tactic.rcasesPatMed " := " e:term : tactic => `(tactic| (have x := $e; obtain $p := x))

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def ModW (R : RealDat D A Ks) : Prop := R.models_HW ∧ R.models_gW ∧ R.models_νW ∧ R.models_BV

def WeilAt (R : RealDat D A Ks) (t : T) : Prop := ∀ i : Fin D.R.m,
  IsWeilFull R.ψ (Vc D i) (Wc D i) (Lift.chrTh (R.toLevCh.mu t) R.eta ((i : ℕ) + 1)).1
    (Lift.chrTh (R.toLevCh.mu t) R.eta ((i : ℕ) + 1)).2 (R.ωP i t) ∧
  IsThPVecOf R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.ΛV i) (R.ΛW i) (R.βV i) (R.βW i)
    R.Pg (R.Q t) (R.xiR t) (R.vacP i) (R.vP i t) ∧
  IsIoW R.θ (R.MW i (sg0 D A)) (R.cV i) (R.ωP i t) (R.ptP i t) (RealDat.Delta i) (R.ioP i)

def ModVAt (R : RealDat D A Ks) (t : T) : Prop := ∀ i : Fin D.R.m,
  (R.HV i t).Is (Bridge.AdForms (Bridge.ratF (Vc D i)) (R.cV i).coef.ρ (levEnv _ (R.βV i) (R.datVt i t)).J
      (levEnv _ (R.βV i) (R.datVt i t)).χ)
    (Bridge.adInner (Bridge.ratF (Vc D i)) (levEnv _ (R.βV i) (R.datVt i t)).J (R.B.L i t).pres.y) ∧
  IsMeasDef (Vc D i) (lev D.sp.cm (Vc D i).gram (R.βV i) (R.datVt i t)) (R.νV i t) (R.fdV i t)

def LiftAt (R : RealDat D A Ks) (t : T) : Prop := ∀ i : Fin D.R.m, R.PThF i t (R.thF i t) ∧ R.PThG i t (R.thG i t)

def RatAt (R : RealDat D A Ks) (t : T) : Prop := ∀ (i : Fin D.R.m) (x : A.fam.amb.FL i t) (v : (R.HV i t).H),
  (R.HV i t).e v = R.B.jL i t x → ∃ y, (R.FW i).j (sg0 D A) y = R.thG i t v

def updM (R : RealDat D A Ks) (HX : type_of% R.HX) (HV : type_of% R.HV) (HE : type_of% R.HE)
    (gE : Representation ℂ G HE.H)
    (jX : ∀ t, A.fam.amb.FR t →ₛₗ[D.what₂.embLL] (HX t).H) (jV : ∀ i t, A.fam.amb.FL i t →ₛₗ[D.what₂.embLL] (HV i t).H)
    (νY : type_of% R.νY) (fdY : type_of% R.fdY) (ν0 : type_of% R.ν0) (fd0 : type_of% R.fd0) (νX : type_of% R.νX) (fdX : type_of% R.fdX)
    (νV : type_of% R.νV) (fdV : type_of% R.fdV) (ωP : type_of% R.ωP) (vP : type_of% R.vP)
    (thF : ∀ i t, (HV i t).H →ₗ[ℂ] MMap (R.MW i (sg0 D A))) (thG : ∀ i t, (HV i t).H →ₗ[ℂ] (R.HW i (sg0 D A)).H) : RealDat D A Ks :=
  { R with
    HX := HX, HV := HV, HE := HE, gE := gE, jX := jX, jV := jV,
    νY := νY, fdY := fdY, ν0 := ν0, fd0 := fd0, νX := νX, fdX := fdX, νV := νV, fdV := fdV,
    ioX := fun _ => 0, Th := fun _ => 0, ωP := ωP, vP := vP, thF := thF, thG := thG }

def SameAt (R R' : RealDat D A Ks) (t : T) : Prop := ∀ i : Fin D.R.m,
  R'.ωP i t = R.ωP i t ∧ R'.vP i t = R.vP i t ∧ HEq (R'.HV i t) (R.HV i t) ∧ HEq (R'.thF i t) (R.thF i t) ∧
    HEq (R'.thG i t) (R.thG i t) ∧ R'.νV i t = R.νV i t ∧ R'.fdV i t = R.fdV i t

theorem realDatum_prerequisites_update_models {R : RealDat D A Ks} {F : Face D A} (h : R.Pre0 F)
    (HX HV HE gE jX jV νY fdY ν0 fd0 νX fdX νV fdV ωP vP thF thG) :
    (updM R HX HV HE gE jX jV νY fdY ν0 fd0 νX fdX νV fdV ωP vP thF thG).Pre0 F :=
  ⟨h.lev, h.red_R, h.red_L, h.levels, h.record,
    ⟨h.fam.tie, h.fam.Sb, h.fam.roots, h.fam.pl_onto, h.fam.degR, h.fam.degL, h.fam.muVal, h.fam.etaVal⟩,
    h.inf, h.vpos, h.cX, h.cV, h.prX, h.order, h.std⟩

def PF (R : RealDat D A Ks) (i : Fin D.R.m) (H : HMod (Bridge.Gf (Vc D i) → (R.cV i).W)) (ν : Measure (GA D (Vc D i)))
    (fd : Set (GA D (Vc D i))) (ω : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (WO (Vc D i) (Wc D i) → ℂ))
    (v : WO (Vc D i) (Wc D i) → ℂ) (th : H.H →ₗ[ℂ] MMap (R.MW i (sg0 D A))) : Prop :=
  (∀ x, th x ∈ R.Wall i (sg0 D A)) ∧
    ∃ thP, Lift.IsThetaP ν fd (fun g h f => thetaKO ω h g f)
        (pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.BV i) (onb (R.MW i (sg0 D A))) v) (R.ioP i)
        (LinearMap.range ((R.cV i).ext ∘ₗ H.e)) thP ∧
      ∀ x (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ),
        th x (fun ρ => v ρ) = thP (((R.cV i).ext ∘ₗ H.e).rangeRestrict x) (PiTensorProduct.tprod ℂ v)

def PG (R : RealDat D A Ks) (i : Fin D.R.m) {H : Type} [AddCommGroup H] [Module ℂ H] (th : H →ₗ[ℂ] MMap (R.MW i (sg0 D A)))
    (g : H →ₗ[ℂ] (R.HW i (sg0 D A)).H) : Prop :=
  ∀ x, (R.HW i (sg0 D A)).e (g x) = postOn _ (R.eWf i (sg0 D A)) (th x)

def IsUpd (R R' : RealDat D A Ks) : Prop := R' = R ∨ ∃ HX HV HE HW gE gW jX jV νY fdY ν0 fd0 νX fdX νV fdV νW fdW BV,
  R' = R.upd1 HX HV HE HW gE gW jX jV νY fdY ν0 fd0 νX fdX νV fdV νW fdW BV

theorem realDatum_isUpdate_first_models (R : RealDat D A Ks) : ∀ R' HX HV HE HW gE gW jX jV νY fdY ν0 fd0 νX fdX νV fdV νW fdW BV, IsUpd R R' →
    IsUpd R (R'.upd1 HX HV HE HW gE gW jX jV νY fdY ν0 fd0 νX fdX νV fdV νW fdW BV) := by
  rintro R' HX HV HE HW gE gW jX jV νY fdY ν0 fd0 νX fdX νV fdV νW fdW BV
    (rfl | ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, rfl⟩)
  · exact Or.inr ⟨HX, HV, HE, HW, gE, gW, jX, jV, νY, fdY, ν0, fd0, νX, fdX, νV, fdV, νW, fdW, BV, rfl⟩
  · refine Or.inr ⟨HX, HV, HE, HW, gE, gW, jX, jV, νY, fdY, ν0, fd0, νX, fdX, νV, fdV, νW, fdW, BV, ?_⟩
    exact (by with_unfolding_all exact ((Eq.refl (R.upd1 HX HV HE HW gE gW jX jV νY fdY ν0 fd0 νX fdX νV fdV νW fdW BV)) :))

set_option maxHeartbeats 400000 in

theorem exists_models (hI : Inputs D) (hX : IdemClass A) {F : Face D A} (hL : LiftsAt D A Ks F) (R : RealDat D A Ks) (h : R.Pre0 F) :
    ∃ HX HV HE gE jX jV νY fdY ν0 fd0 νX fdX νV fdV, ∀ R2 : RealDat D A Ks,
      R2 = updM R HX HV HE gE jX jV νY fdY ν0 fd0 νX fdX νV fdV R.ωP R.vP (fun _ _ => 0) (fun _ _ => 0) →
        R2.models_HX ∧ R2.models_HV ∧ R2.models_HE ∧ R2.models_gE ∧ R2.models_jX ∧ R2.models_jV ∧ R2.models_νY ∧ R2.models_νY' ∧
          R2.models_ν0 ∧ R2.models_νX ∧ R2.models_νV := by
  obt ⟨R1, p1, q1⟩ := models_args hI.measFD hI.measDef hI.fund hI.sp hI.lev hI.hc hI.schur hI.pet hI.sm hI.dim hI.act hX
    (IsUpd R) (realDatum_isUpdate_first_models R) R F h (Or.inl rfl) (hL R h)
  have m := p1.2
  have m' : R1.models_HX ∧ R1.models_HV ∧ R1.models_HE ∧ R1.models_gE ∧ R1.models_jX ∧ R1.models_jV ∧ R1.models_νY ∧ R1.models_νY' ∧
      R1.models_ν0 ∧ R1.models_νX ∧ R1.models_νV := ⟨m.HX, m.HV, m.HE, m.gE, m.jX, m.jV, m.νY, m.νY', m.ν0, m.νX, m.νV⟩
  rcases q1 with rfl | ⟨HX, HV, HE, HW, gE, gW, jX, jV, νY, fdY, ν0, fd0, νX, fdX, νV, fdV, νW, fdW, BV, rfl⟩
  · refine ⟨R1.HX, R1.HV, R1.HE, R1.gE, R1.jX, R1.jV, R1.νY, R1.fdY, R1.ν0, R1.fd0, R1.νX, R1.fdX, R1.νV, R1.fdV, ?_⟩
    rintro _ rfl
    exact (by with_unfolding_all exact (m' :))
  · refine ⟨HX, HV, HE, gE, jX, jV, νY, fdY, ν0, fd0, νX, fdX, νV, fdV, ?_⟩
    rintro _ rfl
    exact (by with_unfolding_all exact (m' :))

set_option maxHeartbeats 400000 in

theorem exists_at (hI : Inputs D) {F : Face D A} (hF : SeedFacts D A Ks F) (R : RealDat D A Ks) (h : R.Pre0 F)
    (hω : WeilAt R A.μ0) (hV : ModVAt R A.μ0) (hl : LiftAt R A.μ0) (hr : RatAt R A.μ0) (i : Fin D.R.m) (t : T)
    (H₀ : HMod (Bridge.Gf (Vc D i) → (R.cV i).W)) (j₀ : A.fam.amb.FL i t →ₛₗ[D.what₂.embLL] H₀.H)
    (ν₀ : Measure (GA D (Vc D i))) (fd₀ : Set (GA D (Vc D i)))
    (m1 : H₀.Is (Bridge.AdForms (Bridge.ratF (Vc D i)) (R.cV i).coef.ρ (levEnv _ (R.βV i) (R.datVt i t)).J
          (levEnv _ (R.βV i) (R.datVt i t)).χ)
        (Bridge.adInner (Bridge.ratF (Vc D i)) (levEnv _ (R.βV i) (R.datVt i t)).J (R.B.L i t).pres.y))
    (m2 : ∀ x, H₀.e (j₀ x) = R.B.jL i t x)
    (m3 : IsMeasDef (Vc D i) (lev D.sp.cm (Vc D i).gram (R.βV i) (R.datVt i t)) ν₀ fd₀) :
    ∃ (ω : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (WO (Vc D i) (Wc D i) → ℂ))
      (v : WO (Vc D i) (Wc D i) → ℂ) (H : HMod (Bridge.Gf (Vc D i) → (R.cV i).W)) (j : A.fam.amb.FL i t →ₛₗ[D.what₂.embLL] H.H)
      (ν : Measure (GA D (Vc D i))) (fd : Set (GA D (Vc D i))) (th : H.H →ₗ[ℂ] MMap (R.MW i (sg0 D A)))
      (g : H.H →ₗ[ℂ] (R.HW i (sg0 D A)).H),
      IsWeilFull R.ψ (Vc D i) (Wc D i) (Lift.chrTh (R.toLevCh.mu t) R.eta ((i : ℕ) + 1)).1
        (Lift.chrTh (R.toLevCh.mu t) R.eta ((i : ℕ) + 1)).2 ω ∧
      IsThPVecOf R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.ΛV i) (R.ΛW i) (R.βV i) (R.βW i)
        R.Pg (R.Q t) (R.xiR t) (R.vacP i) v ∧
      H.Is (Bridge.AdForms (Bridge.ratF (Vc D i)) (R.cV i).coef.ρ (levEnv _ (R.βV i) (R.datVt i t)).J
          (levEnv _ (R.βV i) (R.datVt i t)).χ)
        (Bridge.adInner (Bridge.ratF (Vc D i)) (levEnv _ (R.βV i) (R.datVt i t)).J (R.B.L i t).pres.y) ∧
      (∀ x, H.e (j x) = R.B.jL i t x) ∧
      IsMeasDef (Vc D i) (lev D.sp.cm (Vc D i).gram (R.βV i) (R.datVt i t)) ν fd ∧
      OrZero (PF R i H ν fd ω v) th ∧ OrZero (PG R i th) g ∧
      (t = A.μ0 → ω = R.ωP i t ∧ v = R.vP i t ∧ HEq H (R.HV i t) ∧ HEq th (R.thF i t) ∧
        HEq g (R.thG i t) ∧ ν = R.νV i t ∧ fd = R.fdV i t ∧ ∀ x, ∃ y, (R.FW i).j (sg0 D A) y = g (j x)) := by
  obt ⟨hsp, hid⟩ := hF R h
  have sdV : IsSelfDualC (Vc D i) (R.ΛV i) ∧ IsFrame (R.βV i) (R.ΛV i) := by
    obt ⟨c, hc⟩ := h.lev.βV i
    exact ⟨hI.selfDual _ _ _ _ hc, hc.1⟩
  have sdW : IsSelfDualC (Wc D i) (R.ΛW i) ∧ IsFrame (R.βW i) (R.ΛW i) := by
    obt ⟨c, hc⟩ := h.lev.βW i
    exact ⟨hI.selfDual _ _ _ _ hc, hc.1⟩
  by_cases ht : t = A.μ0
  · subst ht
    obt ⟨j, hj⟩ := hMod_lift (hV i).1 (R.B.jL i A.μ0) (fun x => by exact (R.B.L i A.μ0).pres.extMem_holds x)
    have l1 : PF R i (R.HV i A.μ0) (R.νV i A.μ0) (R.fdV i A.μ0) (R.ωP i A.μ0) (R.vP i A.μ0) (R.thF i A.μ0) := (by with_unfolding_all exact ((hl i).1 :))
    have l2 : PG R i (R.thF i A.μ0) (R.thG i A.μ0) := (hl i).2
    exact ⟨R.ωP i _, R.vP i _, R.HV i _, j, R.νV i _, R.fdV i _, R.thF i _, R.thG i _, (hω i).1, (hω i).2.1, (hV i).1, hj, (hV i).2,
      ⟨fun _ => l1, fun hn => absurd ⟨_, l1⟩ hn⟩, ⟨fun _ => l2, fun hn => absurd ⟨_, l2⟩ hn⟩,
      fun _ => ⟨rfl, rfl, HEq.rfl, HEq.rfl, HEq.rfl, rfl, rfl, fun x => hr i x _ (hj x)⟩⟩
  · obt ⟨ω, hω'⟩ := hI.weil R.ψ (Vc D i) (Wc D i) _ _ h.std ((hsp t).2.2 i).1 ((hsp t).2.2 i).2.1
      ((hsp t).2.2 i).2.2.1 ((hsp t).2.2 i).2.2.2
    obt ⟨v, hv⟩ := hI.thPVec R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.ΛV i) (R.ΛW i)
      (R.βV i) (R.βW i) R.Pg (R.Q t) (R.xiR t) sdV.1 sdW.1 sdV.2 sdW.2 (hid t).1 (hid t).2 (R.vacP i) (hω i).2.1.1
    obt ⟨th, hth⟩ := orZero_exists (PF R i H₀ ν₀ fd₀ ω v)
    obt ⟨g, hg⟩ := orZero_exists (PG R i th)
    exact ⟨ω, v, H₀, j₀, ν₀, fd₀, th, g, hω', hv, m1, m2, m3, hth, hg, fun e => absurd e ht⟩

set_option maxHeartbeats 400000 in

theorem exists_thPW_keep (hI : Inputs D) (hX : IdemClass A) {F : Face D A} (hL : LiftsAt D A Ks F) (hF : SeedFacts D A Ks F)
    (R : RealDat D A Ks) (h : R.Pre0 F) (hW : ModW R) (hω : WeilAt R A.μ0) (hV : ModVAt R A.μ0) (hl : LiftAt R A.μ0)
    (hr : RatAt R A.μ0) :
    ∃ HX HV HE gE jX jV νY fdY ν0 fd0 νX fdX νV fdV ωP vP thF thG, ∀ R' : RealDat D A Ks,
      R' = updM R HX HV HE gE jX jV νY fdY ν0 fd0 νX fdX νV fdV ωP vP thF thG →
      R'.Pre1 F ∧ R'.IsThPW ∧ R'.FullP ∧ SameAt R R' A.μ0 ∧
      ∀ i x, ∃ y, (R'.FW i).j (sg0 D A) y = R'.thG i A.μ0 (R'.jV i A.μ0 x) := by
  obt ⟨HX, HV, HE, gE, jX, jV, νY, fdY, ν0, fd0, νX, fdX, νV, fdV, m⟩ := exists_models hI hX hL R h
  obt ⟨mHX, mHV, mHE, mgE, mjX, mjV, mνY, mνY', mν0, mνX, mνV⟩ := m _ rfl
  have key := fun i t => exists_at hI hF R h hω hV hl hr i t (HV i t) (jV i t) (νV i t) (fdV i t)
    ((by with_unfolding_all exact (mHV i t :))) ((by with_unfolding_all exact (mjV i t :))) ((by with_unfolding_all exact (mνV i t :)))
  choose ωP vP HV' jV' νV' fdV' thF thG k1 k2 k3 k4 k5 k6 k7 k8 using key
  refine ⟨HX, HV', HE, gE, jX, jV', νY, fdY, ν0, fd0, νX, fdX, νV', fdV', ωP, vP, thF, thG, fun R2 e => ?_⟩
  have p0 : R2.Pre0 F := e ▸ realDatum_prerequisites_update_models h _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  have p2 : R2.IsModels := by
    subst e
    refine ⟨p0.inf, p0.vpos, p0.cX, p0.cV, p0.prX, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, p0.order⟩
    · exact (by with_unfolding_all exact (mHX :))
    · exact (by with_unfolding_all exact (k3 :))
    · exact (by with_unfolding_all exact (mHE :))
    · exact (by with_unfolding_all exact (hW.1 :))
    · kexactB mgE
    · exact (by with_unfolding_all exact (hW.2.1 :))
    · exact (by with_unfolding_all exact (mjX :))
    · exact (by with_unfolding_all exact (k4 :))
    · exact (by with_unfolding_all exact (mνY :))
    · exact (by with_unfolding_all exact (mνY' :))
    · exact (by with_unfolding_all exact (mν0 :))
    · exact (by with_unfolding_all exact (mνX :))
    · exact (by with_unfolding_all exact (k5 :))
    · exact (by with_unfolding_all exact (hW.2.2.1 :))
    · exact (by with_unfolding_all exact (hW.2.2.2 :))
  have f2 : R2.FullP := by subst e; exact (by with_unfolding_all exact (k1 :))
  have v2 : R2.thP_vP := by subst e; exact (by with_unfolding_all exact (k2 :))
  have i0 : ∀ i, IsIoW R2.θ (R2.MW i (sg0 D A)) (R2.cV i) (R2.ωP i A.μ0) (R2.ptP i A.μ0) (RealDat.Delta i) (R2.ioP i) := fun i => by
    have e' := (hω i).2.2
    unfold RealDat.ptP at e'
    rw [← (k8 i _ rfl).1, ← (k8 i _ rfl).2.1] at e'
    subst e
    exact (by with_unfolding_all exact (e' :))
  have hio : ∀ i, R2.PIoP i (R2.ioP i) := fun i =>
    GlobalTheory.IoAllTuples.ioP_of_isIoW_at D G Pl0 T A Ks R2 p0.lev p0.fam p2 (fun i t => (f2 i t).datum) v2 i A.μ0 _ (i0 i)
  have pt := (GlobalTheory.JointHarm.exists_ioP D G Pl0 T A Ks R2 p0.lev p0.fam p2 (fun i t => (f2 i t).datum) v2).1
  have a6 : R2.tw_thF := by subst e; exact (by with_unfolding_all exact (k6 :))
  have a7 : R2.tw_thG := by subst e; exact (by with_unfolding_all exact (k7 :))
  refine ⟨⟨p0, p2⟩, ⟨fun i t => (f2 i t).datum, v2, pt, fun i => ⟨fun _ => hio i, fun hn => absurd ⟨_, hio i⟩ hn⟩, a6, a7⟩, f2, ?_, ?_⟩
  · subst e
    intro i
    obt ⟨b1, b2, b3, b4, b5, b6, b7, -⟩ := k8 i _ rfl
    exact ⟨b1, b2, b3, b4, b5, b6, b7⟩
  · subst e
    intro i
    exact (by with_unfolding_all exact ((k8 i _ rfl).2.2.2.2.2.2.2 :))

theorem realDatum_thetaPairWeil_update_third {R : RealDat D A Ks} (a : R.IsThPW) (ωY ωX vac vacX vY vX ItY ItX ioY ioX Th) :
    (R.upd3 ωY ωX vac vacX vY vX ItY ItX ioY ioX Th).IsThPW :=
  ⟨a.ωP, a.vP, a.pt_theta, a.ioP, a.thF, a.thG⟩

set_option maxHeartbeats 400000 in

theorem exists_weak_keep (hI : Inputs D) (hX : IdemClass A) {F : Face D A} (hL : LiftsAt D A Ks F) (hF : SeedFacts D A Ks F)
    (Q : RealDat D A Ks → Prop)
    (hQM : ∀ R HX HV HE gE jX jV νY fdY ν0 fd0 νX fdX νV fdV ωP vP thF thG, Q R →
      Q (updM R HX HV HE gE jX jV νY fdY ν0 fd0 νX fdX νV fdV ωP vP thF thG))
    (hQ3 : ∀ R ωY ωX vac vacX vY vX ItY ItX ioY ioX Th, Q R → Q (R.upd3 ωY ωX vac vacX vY vX ItY ItX ioY ioX Th))
    (R : RealDat D A Ks) (h : R.Pre0 F) (hq : Q R) (hW : ModW R) (hω : WeilAt R A.μ0) (hV : ModVAt R A.μ0) (hl : LiftAt R A.μ0)
    (hr : RatAt R A.μ0) :
    ∃ R' : RealDat D A Ks, R'.Pre1 F ∧ R'.IsChainW ∧ R'.IsThPW ∧ R'.FullY ∧ R'.FullP ∧ Q R' ∧ SameAt R R' A.μ0 ∧
      ∀ i x, ∃ y, (R'.FW i).j (sg0 D A) y = R'.thG i A.μ0 (R'.jV i A.μ0 x) := by
  obt ⟨HX, HV, HE, gE, jX, jV, νY, fdY, ν0, fd0, νX, fdX, νV, fdV, ωP, vP, thF, thG, m⟩ :=
    exists_thPW_keep hI hX hL hF R h hW hω hV hl hr
  obt ⟨p2, t2, f2, s2, r2⟩ := m _ rfl
  let Q' : RealDat D A Ks → Prop := fun R' => Q R' ∧ R'.IsThPW ∧ R'.FullP ∧ SameAt R R' A.μ0 ∧
      ∀ i x, ∃ y, (R'.FW i).j (sg0 D A) y = R'.thG i A.μ0 (R'.jV i A.μ0 x)
  have hQ' : ∀ R' ωY ωX vac vacX vY vX ItY ItX ioY ioX Th, Q' R' → Q' (R'.upd3 ωY ωX vac vacX vY vX ItY ItX ioY ioX Th) :=
    fun R' _ _ _ _ _ _ _ _ _ _ _ a => ⟨hQ3 _ _ _ _ _ _ _ _ _ _ _ _ a.1, realDatum_thetaPairWeil_update_third a.2.1 _ _ _ _ _ _ _ _ _ _ _, (by with_unfolding_all exact (a.2.2 :))⟩
  obt ⟨R3, p3, k3', q3⟩ := kerYQ_exists hI hF Q' hQ' _ p2 ⟨hQM _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hq, t2, f2, s2, r2⟩
  obt ⟨R4, p4, c4, f4, q4⟩ := chainW_exists Q' hQ' R3 p3 k3' q3
  exact ⟨R4, p4, c4, q4.2.1, f4, q4.2.2.1, q4.1, q4.2.2.2⟩

end GlobalTheory.Mem.KeepRef

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RecursionLocalRowConditionStatement
section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.R3
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.recursion_local_row_condition : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (K : Formalism.MainNotions.G.Consts) (Yd : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Yd cX) (x : TwIn ex) (Rc : Formalism.L2.RecT ex) (S : Formalism.L2.SG.SpectralTiesReal.STiesR Rc) (y : RealIn x Rc S), ∀ r : RecIn y, (∀ hp : RealPins (realTOf y), Formalism.IndefR.principalLevelFrame.RowLocPin Rc.T.n.gal.lp x.R.θ x.Y.PY (x.R.MY 0) (fun b => levS _ (x.R.βY 0) (x.R.dat0 (x.R.toRealDat.levR x.F.lv2 b))) (fun b => Formalism.IndefR.Lev.levChi _ (x.R.βY 0) (x.R.dat0 (x.R.toRealDat.levR x.F.lv2 b))) (fun _ => x.R.e0) x.Y.eFT → RealRecPins hp (realRecOf r)) ∧ (Formalism.IndefR.RecTie.PartsRec x.R.toRealDat x.F.lv2 x.Y.tupT x.Y.hm x.Y.PY x.Y.PW x.Y.eFT r.E r.labPi r.piOf x.Y.Ish.prt x.Y.IL.prtW → (realRecOf r).PartsRow) ∧ PsiPPTie D (divisionPairOfAdelicFormsFaceColumnsData x).P0 (divisionPairOfAdelicFormsFaceColumnsData x).ψ0 (divisionPairOfAdelicFormsFaceColumnsData x).Ps (divisionPairOfAdelicFormsFaceColumnsData x).ψs (divisionPairOfAdelicFormsFaceColumnsData x).I.eG := by
  first | exact @GlobalTheory.Mem.R3.RecPinsTie.main | exact GlobalTheory.Mem.R3.RecPinsTie.main | (intros; apply GlobalTheory.Mem.R3.RecPinsTie.main <;> assumption)
end

