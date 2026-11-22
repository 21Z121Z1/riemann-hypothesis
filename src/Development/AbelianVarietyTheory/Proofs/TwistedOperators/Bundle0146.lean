import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0144
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0126
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0020
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0103
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0231
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0138
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemClosureUnitary
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0033
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0006
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0027
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
import Formalism.LocalToGlobal.IndefiniteReal.FWExist

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdelicVectorSizeSeenOrthogonalSummandLe
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HtOrth.Transp

open NumberField IsDedekindDomain GlobalTheory.AdelicU GlobalTheory.HtOrth
open scoped NNReal

variable {D : D7}

def bF {m n : ℕ} (Y : Matrix (Fin m) (Fin n) (AE D)) (v : HeightOneSpectrum (𝓞 D.host.F)) : ℝ≥0 :=
  max 1 (Finset.univ.sup fun p : Fin m × Fin n => absFin D.host.F v (compFin D.host.F D.host.E v (Y p.1 p.2)))

theorem absFin_le_bF {m n : ℕ} (Y : Matrix (Fin m) (Fin n) (AE D)) (v : HeightOneSpectrum (𝓞 D.host.F))
    (i : Fin m) (j : Fin n) : absFin D.host.F v (compFin D.host.F D.host.E v (Y i j)) ≤ bF Y v := by
  unfold bF
  refine le_trans ?_ (le_max_right _ _)
  have h := Finset.le_sup (f := fun p : Fin m × Fin n =>
    absFin D.host.F v (compFin D.host.F D.host.E v (Y p.1 p.2))) (Finset.mem_univ (i, j))
  exact h

theorem le_vFin {n : ℕ} (x : Fin n → AE D) (v : HeightOneSpectrum (𝓞 D.host.F)) (i : Fin n) :
    absFin D.host.F v (compFin D.host.F D.host.E v (x i)) ≤ vFin v x := by
  unfold vFin
  have h := Finset.le_sup (f := fun i => absFin D.host.F v (compFin D.host.F D.host.E v (x i))) (Finset.mem_univ i)
  exact h

end GlobalTheory.HtOrth.Transp

namespace GlobalTheory.HtOrth.Transp

open NumberField IsDedekindDomain GlobalTheory.AdelicU GlobalTheory.HtOrth
open scoped NNReal

variable {D : D7}

theorem eventually_bF_eq_one {m n : ℕ} (Y : Matrix (Fin m) (Fin n) (AE D)) :
    ∀ᶠ v in Filter.cofinite, bF Y v = 1 := by
  have h : ∀ᶠ v in Filter.cofinite, ∀ p : Fin m × Fin n,
      absFin D.host.F v (compFin D.host.F D.host.E v (Y p.1 p.2)) ≤ 1 :=
    Filter.eventually_all.2 fun p => eventually_absFin_le_one D.host.F (Y p.1 p.2)
  refine h.mono fun v hv => ?_
  unfold bF
  exact max_eq_left (Finset.sup_le fun p _ => hv p)

theorem finite_mulSupport_bF {m n : ℕ} (Y : Matrix (Fin m) (Fin n) (AE D)) :
    (Function.mulSupport (bF Y)).Finite :=
  (Filter.eventually_cofinite.1 (eventually_bF_eq_one Y)).subset fun _ hv => hv

theorem vFin_mulVec_le {m n : ℕ} (Y : Matrix (Fin m) (Fin n) (AE D)) (x : Fin n → AE D)
    (v : HeightOneSpectrum (𝓞 D.host.F)) : vFin v (Y *ᵥ x) ≤ bF Y v * vFin v x := by
  rw [vFin]
  refine Finset.sup_le fun i _ => ?_
  simp only [Matrix.mulVec, dotProduct, map_sum, map_mul]
  exact absFin_sum_le D.host.F v _ _ fun j _ =>
    (absFin_mul_le D.host.F v _ _).trans (mul_le_mul' (absFin_le_bF Y v i j) (le_vFin x v j))

end GlobalTheory.HtOrth.Transp

namespace GlobalTheory.HtOrth.Transp

open NumberField IsDedekindDomain GlobalTheory.AdelicU GlobalTheory.HtOrth
open scoped NNReal

variable {D : D7}

open Classical in

def bI {m n : ℕ} (Y : Matrix (Fin m) (Fin n) (AE D)) (w : InfinitePlace D.host.F) : ℝ≥0 :=
  max 1 (Finset.univ.sup fun p : EmbOver D.host.E w × Fin m =>
    ∑ j, ‖infEmb p.1 (compInf D.host.F D.host.E w (Y p.2 j))‖₊)

theorem sum_le_bI {m n : ℕ} (Y : Matrix (Fin m) (Fin n) (AE D)) (w : InfinitePlace D.host.F)
    (τ : EmbOver D.host.E w) (i : Fin m) :
    ∑ j, ‖infEmb τ (compInf D.host.F D.host.E w (Y i j))‖₊ ≤ bI Y w := by
  classical
  unfold bI
  refine le_trans ?_ (le_max_right _ _)
  have h := Finset.le_sup (f := fun p : EmbOver D.host.E w × Fin m =>
    ∑ j, ‖infEmb p.1 (compInf D.host.F D.host.E w (Y p.2 j))‖₊) (Finset.mem_univ (τ, i))
  exact h

theorem le_vInf {n : ℕ} (x : Fin n → AE D) (w : InfinitePlace D.host.F) (τ : EmbOver D.host.E w) (i : Fin n) :
    ‖infEmb τ (compInf D.host.F D.host.E w (x i))‖₊ ≤ vInf w x := by
  classical
  unfold vInf
  have h := Finset.le_sup (f := fun p : EmbOver D.host.E w × Fin n =>
    ‖infEmb p.1 (compInf D.host.F D.host.E w (x p.2))‖₊) (Finset.mem_univ (τ, i))
  exact h

theorem vInf_mulVec_le {m n : ℕ} (Y : Matrix (Fin m) (Fin n) (AE D)) (x : Fin n → AE D)
    (w : InfinitePlace D.host.F) : vInf w (Y *ᵥ x) ≤ bI Y w * vInf w x := by
  rw [vInf]
  refine Finset.sup_le fun p _ => ?_
  simp only [Matrix.mulVec, dotProduct, map_sum, map_mul]
  refine (nnnorm_sum_le _ _).trans ?_
  refine le_trans ?_ (mul_le_mul' (sum_le_bI Y w p.1 p.2) le_rfl)
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [nnnorm_mul]
  exact mul_le_mul' le_rfl (le_vInf x w p.1 j)

end GlobalTheory.HtOrth.Transp

namespace GlobalTheory.HtOrth.Transp

open NumberField IsDedekindDomain GlobalTheory.AdelicU GlobalTheory.HtOrth
open scoped NNReal

variable {D : D7}

theorem eventually_vFin_seen_eq_one (V : HSp D) (g : GA D V) {ξ : Fin V.rank → D.host.E} (hξ : ξ ≠ 0) :
    ∀ᶠ v in Filter.cofinite, vFin v (seen V g ξ) = 1 := by
  set u : Fin V.rank → AE D := fun i => incA D (ξ i) with hu
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hξ
  have h1 : ∀ᶠ v in Filter.cofinite, vFin v u ≤ 1 :=
    (Filter.eventually_all.2 fun i => eventually_absFin_le_one D.host.F (u i)).mono fun v hv =>
      Finset.sup_le fun i _ => hv i
  have h2 : ∀ᶠ v in Filter.cofinite, 1 ≤ absFin D.host.F v (compFin D.host.F D.host.E v (incA D (ξ i))) := by
    refine (eventually_absFin_le_one D.host.F (incA D (ξ i)⁻¹)).mono fun v hv => ?_
    have e : incA D (ξ i) * incA D (ξ i)⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel₀ hi, map_one]
    have := absFin_mul_le D.host.F v (compFin D.host.F D.host.E v (incA D (ξ i)))
      (compFin D.host.F D.host.E v (incA D (ξ i)⁻¹))
    rw [← map_mul, e, map_one, absFin_one] at this
    exact this.trans (mul_le_of_le_one_right' hv)
  refine ((h1.and h2).and ((eventually_bF_eq_one (mt V g⁻¹)).and (eventually_bF_eq_one (mt V g)))).mono
    fun v hv => le_antisymm ?_ ?_
  · refine (vFin_mulVec_le _ u v).trans ?_
    rw [hv.2.1, one_mul]; exact hv.1.1
  · have e : u = mt V g *ᵥ seen V g ξ := by
      rw [seen, Matrix.mulVec_mulVec, GlobalTheory.MixModel.mt_mul_inv, Matrix.one_mulVec]
    refine hv.1.2.trans ((le_vFin u v i).trans ?_)
    rw [e]
    refine (vFin_mulVec_le _ _ v).trans ?_
    rw [hv.2.2, one_mul]

theorem seen_emb {S A B : HSp D} (o : GlobalTheory.MixModel.OrthDec S A B) (h : GA D A) (η : Fin A.rank → D.host.E) :
    seen S (o.emb (h, 1)) (o.iA *ᵥ η) = o.jA *ᵥ seen A h η := by
  have e1 : (o.emb (h, 1))⁻¹ = o.emb (h⁻¹, 1) := by rw [← map_inv, Prod.inv_mk, inv_one]
  have e2 : (fun i => incA D ((o.iA *ᵥ η) i)) = o.jA *ᵥ fun i => incA D (η i) := by
    funext i; exact RingHom.map_mulVec (incA D) o.iA η i
  rw [seen, seen, e1, e2, Matrix.mulVec_mulVec, GlobalTheory.MixModel.OrthDec.emb_jA, Matrix.mulVec_mulVec]

end GlobalTheory.HtOrth.Transp

namespace GlobalTheory.HtOrth.Transp

open NumberField IsDedekindDomain GlobalTheory.AdelicU GlobalTheory.HtOrth
open scoped NNReal

variable {D : D7}

theorem vsize_zero {n : ℕ} : vsize (0 : Fin n → AE D) = 0 := by
  have h : ∀ w : InfinitePlace D.host.F, vInf w (0 : Fin n → AE D) = 0 := fun w => by
    classical
    unfold vInf
    refine le_antisymm (Finset.sup_le fun p _ => ?_) zero_le
    simp
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace D.host.F))
  unfold vsize
  rw [Finset.prod_eq_zero (Finset.mem_univ w) (h w), zero_mul, NNReal.coe_zero]

end GlobalTheory.HtOrth.Transp

namespace GlobalTheory.HtOrth.Transp

open NumberField IsDedekindDomain GlobalTheory.AdelicU GlobalTheory.HtOrth
open scoped NNReal

theorem vsize_seen_emb_le : ∀ (D : D7) (S A B : HSp D) (o : GlobalTheory.MixModel.OrthDec S A B), ∃ C : ℝ,
    ∀ (h : GA D A) (η : Fin A.rank → D.host.E),
      GlobalTheory.HtOrth.vsize (GlobalTheory.HtOrth.seen S (o.emb (h, 1)) (o.iA *ᵥ η)) ≤ C * GlobalTheory.HtOrth.vsize (GlobalTheory.HtOrth.seen A h η) := by
  intro D S A B o
  refine ⟨(((∏ w, bI o.jA w) * ∏ᶠ v, bF o.jA v : ℝ≥0) : ℝ), fun h η => ?_⟩
  by_cases hη : η = 0
  · subst hη
    have e : (o.iA *ᵥ (0 : Fin A.rank → D.host.E)) = 0 := Matrix.mulVec_zero _
    have z : ∀ (V : HSp D) (g : GA D V), seen V g 0 = 0 := fun V g => by
      have h0 : (fun i => incA D ((0 : Fin V.rank → D.host.E) i)) = 0 := funext fun i => map_zero _
      rw [seen, h0, Matrix.mulVec_zero]
    rw [e, z, z, vsize_zero]
    exact mul_nonneg (NNReal.coe_nonneg _) (vsize_nonneg _)
  have hη' : o.iA *ᵥ η ≠ 0 := fun e => hη (by
    have := congrArg (o.qA *ᵥ ·) e
    simpa [Matrix.mulVec_mulVec, GlobalTheory.MixModel.OrthDec.qA_iA] using this)
  have f1 := Filter.eventually_cofinite.1 (eventually_vFin_seen_eq_one A h hη)
  have f2 := Filter.eventually_cofinite.1 (eventually_vFin_seen_eq_one S (o.emb (h, 1)) hη')
  rw [seen_emb] at f2 ⊢
  have hf : (Function.mulSupport fun v => vFin v (seen A h η)).Finite := f1.subset fun v hv => hv
  have hf' : (Function.mulSupport fun v => vFin v (o.jA *ᵥ seen A h η)).Finite := f2.subset fun v hv => hv
  unfold vsize
  rw [← NNReal.coe_mul, NNReal.coe_le_coe]
  calc (∏ w, vInf w (o.jA *ᵥ seen A h η)) * ∏ᶠ v, vFin v (o.jA *ᵥ seen A h η)
      ≤ (∏ w, bI o.jA w * vInf w (seen A h η)) * ∏ᶠ v, bF o.jA v * vFin v (seen A h η) :=
        mul_le_mul' (Finset.prod_le_prod' fun w _ => vInf_mulVec_le o.jA _ w)
          (finprod_le_finprod' hf' (((finite_mulSupport_bF o.jA).union hf).subset (Function.mulSupport_mul _ _))
            fun v => vFin_mulVec_le o.jA _ v)
    _ = _ := by
        rw [Finset.prod_mul_distrib, finprod_mul_distrib (finite_mulSupport_bF o.jA) hf, mul_mul_mul_comm]

end GlobalTheory.HtOrth.Transp

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdicCompletionIntegersNormEqOneOfMulEqOne
section
open MeasureTheory Topology Matrix NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.ModuLR
open scoped NNReal ENNReal TensorProduct

namespace GlobalTheory

theorem adicCompletionIntegers_norm_eq_one_of_mul_eq_one (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (x y : v.adicCompletionIntegers F) (h : x * y = 1) : ‖(x : Fv F v)‖ = 1 := by
  have hx : ‖(x : Fv F v)‖ ≤ 1 := (Valued.toNormedField.norm_le_one_iff).mpr x.2
  have hy : ‖(y : Fv F v)‖ ≤ 1 := (Valued.toNormedField.norm_le_one_iff).mpr y.2
  have hxy : ‖(x : Fv F v)‖ * ‖(y : Fv F v)‖ = 1 := by
    rw [← norm_mul]
    have : ((x : Fv F v) * (y : Fv F v)) = 1 := by
      have := congrArg (fun z : v.adicCompletionIntegers F => (z : Fv F v)) h
      simpa using this
    rw [this, norm_one]
  have h0 := norm_nonneg (x : Fv F v)
  have h0' := norm_nonneg (y : Fv F v)
  nlinarith

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CharacterEquivalenceLocalData
section
open MeasureTheory NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Links
open GlobalTheory.IndefiniteRowSideFullHecke.IteratedLiftChains GlobalTheory.PRep GlobalTheory.LFun
open Formalism.UG (IsCommensurated Hecke)
open Formalism.MainNotions.SchurIrreducible (IsSplit)

namespace GlobalTheory.ChrTie

theorem unrAt_iff_and_val_eq : ∀ (D : D7) (c : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E), ChrEq c χ → ∀ w : HeightOneSpectrum (𝓞 D.host.E), (UnrAt c w ↔ χ.UnrAt w) ∧ val c w = χ.val w :=
  fun _ _ _ h w => ⟨GlobalTheory.LFun.unrAt_iff_of_chrEq h w, GlobalTheory.LFun.val_eq_of_chrEq h w⟩

end GlobalTheory.ChrTie
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CmAdeleIdempotentOfPlaceProperties
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PlaceTensor

theorem idem_eq_locIdem (D : D7) (p : Place D) : idem D p = GlobalTheory.LocWeil.idem D p := by
  rcases p with v | τ
  · rw [GlobalTheory.LocWeil.PlaceIdem.idem_inl]
    rfl
  · rw [GlobalTheory.LocWeil.PlaceIdem.idem_inr]
    simp only [idem, GlobalTheory.LocWeil.PlaceIdem.eInf]
    congr 2

theorem idem_spec : ∀ D : D7, (∀ p, idem D p * idem D p = idem D p) ∧ (∀ p q, p ≠ q → idem D p * idem D q = 0) ∧ (∀ p, cA D (idem D p) = idem D p) ∧ (∀ v : FinPl D, infPart D (idem D (.inl v)) = 0 ∧ finPart D (idem D (.inl v)) ∈ intAE D ∧ IsPlaceIdem D v (pairA D.host.F 0 (singleV D.host.F v 1))) ∧ (∀ τ : D.what₂.Tau, finPart D (idem D (.inr τ)) = 0) ∧ infPart D (∑ τ : D.what₂.Tau, idem D (.inr τ)) = 1 ∧ ∀ θ : InfFam D, IsInfFam θ → ∀ τ : D.what₂.Tau, θ τ (infPart D (idem D (.inr τ))) = 1 ∧ ∀ τ' : D.what₂.Tau, τ' ≠ τ → θ τ (infPart D (idem D (.inr τ'))) = 0 := by
  intro D
  have hE : ∀ p, idem D p = GlobalTheory.LocWeil.idem D p := idem_eq_locIdem D
  obtain ⟨hOrth, hTheta, hFinInf, hSum, -, -⟩ := GlobalTheory.LocWeil.PlaceIdem.idem_props D
  simp only [hE]
  refine ⟨fun p => GlobalTheory.LocWeil.idem_mul_self p, fun p q hpq => hOrth p q hpq, fun p => GlobalTheory.LocWeil.cA_idem p,
    ?_, hFinInf, hSum, ?_⟩
  · intro v
    rw [GlobalTheory.LocWeil.PlaceIdem.idem_inl, GlobalTheory.LocWeil.PlaceIdem.infPart_algebraMap,
      GlobalTheory.LocWeil.PlaceIdem.finPart_algebraMap]
    refine ⟨?_, ?_, ⟨singleV D.host.F v 1, rfl, GlobalTheory.LocWeil.PlaceIdem.evalV_single_same _ v,
      fun v' h => GlobalTheory.LocWeil.PlaceIdem.evalV_single_ne _ h⟩⟩
    · exact TensorProduct.zero_tmul _ _
    · apply AddSubgroup.subset_closure
      refine ⟨singleV D.host.F v 1, ?_, 1, ?_⟩
      · simp only [intAf, Set.mem_setOf_eq]
        intro u
        rcases eq_or_ne u v with rfl | h
        · rw [GlobalTheory.LocWeil.PlaceIdem.evalV_single_same]
          exact one_mem _
        · rw [GlobalTheory.LocWeil.PlaceIdem.evalV_single_ne _ h]
          exact zero_mem _
      · rfl
  · intro θ hθ τ
    refine ⟨?_, fun τ' h => ?_⟩
    · rw [hTheta θ hθ τ τ, if_pos rfl]
    · rw [hTheta θ hθ τ' τ, if_neg (Ne.symm h)]

end GlobalTheory.PlaceTensor
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ComplexConjugationMapsMultiplicitySpaceStatement
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complexConjugation_maps_multiplicitySpace : ∀ {D : D7} {V : HSp D} {S S' : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel V S) (M' : DSModel V S') (c : ∀ τ, M'.H τ ≃ₗᵢ⋆[ℂ] M.H τ), (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ w, c τ (M'.rep τ g w) = M.rep τ g (c τ w)) → (∀ τ (w : M'.H τ), w ∈ M'.sm τ ↔ c τ w ∈ M.sm τ) ∧ ∀ J χ, ∀ T ∈ Mult θ M J χ, ∃ T' ∈ Mult θ M' J (fun k => star (χ k)), ∀ (v' : M'.Vec) (v : M.Vec), (∀ τ, (v τ : M.H τ) = c τ (v' τ)) → ∀ g, T' v' g = star (T v g) := by
  first | exact @GlobalTheory.ConjMult.conj_mult | exact GlobalTheory.ConjMult.conj_mult | (intros; apply GlobalTheory.ConjMult.conj_mult <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousAutomorphicEqZeroOfVanishOnFiniteAdeli
section
namespace EqZeroOfFinite
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped Pointwise TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Grid GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle GlobalTheory.ConstRatio

namespace GlobalTheory.CompanionTheory.FiniteVanish

end GlobalTheory.CompanionTheory.FiniteVanish

end

end EqZeroOfFinite
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped Pointwise TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Grid GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle GlobalTheory.ConstRatio
theorem _root_.GlobalTheory.Adopt.continuous_automorphic_eq_zero_of_vanish_on_finiteAdelic : ∀ (D : D7) (V : HSp D) (φ : GA D V → ℂ), (∀ τ, (gramAt D V τ).PosDef) → Continuous φ → (∀ γ ∈ GQ V, ∀ h, φ (γ * h) = φ h) → (∀ h ∈ GfC V, φ h = 0) → ∀ h, φ h = 0 := by
  intro D V φ _ hcont hleft hzero g
  haveI := GlobalTheory.AutFunCounterexample.topGroup_GA D V
  obtain ⟨u, hu, f, hf, rfl⟩ := (GlobalTheory.UnitarySplit.real_finite_split D V).1 g

  set ψ : GA D V → ℂ := fun x => φ (x * f) with hψ
  have hψc : Continuous ψ := hcont.comp (continuous_mul_right f)
  have hvan : ∀ γ ∈ GQ V, ∀ k ∈ GfC V, ψ (γ * k) = 0 := fun γ hγ k hk => by
    simp only [hψ, mul_assoc, hleft γ hγ]
    exact hzero _ ((GfC V).mul_mem hk hf)
  show ψ u = 0
  by_contra hne
  obtain ⟨γ, hγ, k, hk, hin, -⟩ :=
    GlobalTheory.RealApprox.weak_approx_real V u hu {x | ψ x ≠ 0} (isOpen_ne_fun hψc continuous_const) hne
  exact hin (hvan γ hγ k hk)

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqZeroOfIpEqZero
section
namespace GlobalTheory.LinUnit

section General
open MeasureTheory Matrix GlobalTheory.SplitWeil

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

noncomputable def fac (g : GL a k) (h : GL b k) : ℝ :=
  nabs k (Matrix.GeneralLinearGroup.det g) ^ ((Fintype.card b : ℝ) / 2) *
    nabs k (Matrix.GeneralLinearGroup.det h) ^ (-(Fintype.card a : ℝ) / 2)

theorem fac_pos (g : GL a k) (h : GL b k) : 0 < fac g h :=
  mul_pos (Real.rpow_pos_of_pos (nabs_pos' _) _) (Real.rpow_pos_of_pos (nabs_pos' _) _)

theorem om_one_eq (g : GL a k) (h : GL b k) (Φ : Matrix b a k → ℂ) :
    om 1 g h Φ = fun x => (fac g h : ℂ) * Φ ((h⁻¹).val * x * g.val) := by
  funext x
  simp [om, fac]

theorem nabs_inv (x : kˣ) : nabs k x⁻¹ = (nabs k x)⁻¹ := by simp [nabs]

theorem fac_sq_mul (g : GL a k) (h : GL b k) :
    fac g h * fac g h * (nabs k (Matrix.GeneralLinearGroup.det h⁻¹) ^ (-(Fintype.card a : ℝ)) *
        nabs k (Matrix.GeneralLinearGroup.det g) ^ (-(Fintype.card b : ℝ))) = 1 := by
  have hg := nabs_pos' (Matrix.GeneralLinearGroup.det g)
  have hh := nabs_pos' (Matrix.GeneralLinearGroup.det h)
  rw [map_inv, nabs_inv, Real.inv_rpow hh.le, ← Real.rpow_neg hh.le, neg_neg, fac]
  set x := nabs k (Matrix.GeneralLinearGroup.det g)
  set y := nabs k (Matrix.GeneralLinearGroup.det h)
  have e1 : x ^ ((Fintype.card b : ℝ) / 2) * x ^ ((Fintype.card b : ℝ) / 2) * x ^ (-(Fintype.card b : ℝ)) = 1 := by
    rw [← Real.rpow_add hg, ← Real.rpow_add hg]; simp
  have e2 : y ^ (-(Fintype.card a : ℝ) / 2) * y ^ (-(Fintype.card a : ℝ) / 2) * y ^ (Fintype.card a : ℝ) = 1 := by
    rw [← Real.rpow_add hh, ← Real.rpow_add hh]; simp
  linear_combination (y ^ (-(Fintype.card a : ℝ) / 2) * y ^ (-(Fintype.card a : ℝ) / 2) *
    y ^ (Fintype.card a : ℝ)) * e1 + e2

variable [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure]

theorem ip_om_one (g : GL a k) (h : GL b k) (Φ : Matrix b a k → ℂ) :
    ip ν (om 1 g h Φ) (om 1 g h Φ) = ip ν Φ Φ := by
  have key := integral_comp_mul_mul_volM ν g h⁻¹ (fun x => Φ x * (starRingEnd ℂ) (Φ x))
  have e := fac_sq_mul g h
  rw [om_one_eq]
  unfold ip
  have : ∀ x : Matrix b a k, (fac g h : ℂ) * Φ ((h⁻¹).val * x * g.val) *
      (starRingEnd ℂ) ((fac g h : ℂ) * Φ ((h⁻¹).val * x * g.val)) = ((fac g h * fac g h : ℝ) : ℂ) *
      (Φ ((h⁻¹).val * x * g.val) * (starRingEnd ℂ) (Φ ((h⁻¹).val * x * g.val))) := by
    intro x
    rw [map_mul, Complex.conj_ofReal]; push_cast; ring
  simp_rw [this]
  rw [integral_const_mul, key, Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul, e]
  simp

omit [DecidableEq a] [DecidableEq b] in

theorem eq_zero_of_ip_eq_zero {Φ : Matrix b a k → ℂ} (hΦ : Φ ∈ SB (Matrix b a k)) (h0 : ip ν Φ Φ = 0) : Φ = 0 := by
  obtain ⟨hl, hK⟩ : IsLocallyConstant Φ ∧ HasCompactSupport Φ := hΦ
  obtain ⟨h2, ht⟩ := Model.secondCountable_and_t2_local_field (k := k)
  have : BorelSpace (Matrix b a k) := inferInstanceAs (BorelSpace (b → a → k))
  have : (volM ν b a).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have hc : Continuous fun x => Complex.normSq (Φ x) := Complex.continuous_normSq.comp hl.continuous
  have hs : HasCompactSupport fun x => Complex.normSq (Φ x) := hK.comp_left (g := Complex.normSq) (by simp)
  have e : ∫ x, Complex.normSq (Φ x) ∂(volM ν b a) = 0 := by
    unfold ip at h0
    simp_rw [Complex.mul_conj] at h0
    rw [integral_complex_ofReal] at h0
    exact_mod_cast h0
  have := (integral_eq_zero_iff_of_nonneg (fun x => Complex.normSq_nonneg _)
    (hc.integrable_of_hasCompactSupport hs)).1 e
  have := (hc.ae_eq_iff_eq _ continuous_zero).1 this
  funext x
  exact Complex.normSq_eq_zero.1 (congrFun this x)

end General

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem linOm_unitary : ∀ (D : D7) (v : FinPl D) (m n : ℕ) (g : GL (Fin n) (Fv D.host.F v)) (h : GL (Fin m) (Fv D.host.F v)), (∃ r : ℝ, 0 < r ∧ ∀ Φ : Matrix (Fin m) (Fin n) (Fv D.host.F v) → ℂ, linOm v g h Φ = fun x => (r : ℂ) * Φ ((h⁻¹).val * x * g.val)) ∧ ∀ Φ ∈ GlobalTheory.SplitWeil.SB (Matrix (Fin m) (Fin n) (Fv D.host.F v)), linOm v g h Φ ∈ GlobalTheory.SplitWeil.SB (Matrix (Fin m) (Fin n) (Fv D.host.F v)) ∧ ∀ ν : Measure (Fv D.host.F v), ν.IsAddHaarMeasure → GlobalTheory.SplitWeil.ip ν (linOm v g h Φ) (linOm v g h Φ) = GlobalTheory.SplitWeil.ip ν Φ Φ ∧ (GlobalTheory.SplitWeil.ip ν Φ Φ = 0 → Φ = 0) := by
  intro D v m n g h
  letI := GlobalTheory.LocalData.complRel v
  haveI := GlobalTheory.LocalData.isLocalField v
  haveI : BorelSpace (Fv D.host.F v) := ⟨rfl⟩
  refine ⟨⟨fac g h, fac_pos g h, fun Φ => om_one_eq g h Φ⟩, fun Φ hΦ => ⟨?_, fun ν hν => ⟨?_, ?_⟩⟩⟩
  · exact GlobalTheory.SplitWeil.Model.om_mem_SB 1 g h hΦ
  · exact ip_om_one ν g h Φ
  · exact eq_zero_of_ip_eq_zero ν hΦ

end GlobalTheory.LinUnit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvaluatesOfUnif
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem phiC_zero_rule {D : D7} (T : CoreJ D) {j : ℕ} {σ : T.Q.c.F →+* ℂ} {W : HSp D} (hV : T.V j σ = W)
    (a : (D.host.E →+* ℂ) × ℕ → ℕ) : phiC T hV a (0 : T.R j) = 0 := by
  subst hV
  show T.phiJ j σ a 0 = 0
  unfold CoreJ.phiJ
  rw [map_zero, map_zero, smul_zero]

set_option linter.unusedVariables false in

theorem evaluates_of_unif : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie T R κ v₀), R.LUnif → fw.Evaluates := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ fw hU i σ hσ hV f
  by_cases hj : ∃ j' : (Fin (R.nW i) → D.what₂.LL) →ₛₗ[σ] (R.HW i σ).H,
      ∀ f : T.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n,
        ((R.HW i σ).e (j' ((fw.e i f : (R.FW i).WK) : Fin (R.nW i) → D.what₂.LL))) (v₀ i σ) =
          hV ▸ T.phiJ ((i : ℕ) + 1) (σ.comp (algebraMap T.Q.c.F D.what₂.LL)) (wtA (κ i)) (f : T.R ((i : ℕ) + 1))
  · exact fw.ev i σ hσ hV hj f
  · exfalso
    have hz : (R.FW i).j σ = 0 := fw.ev0 i σ hσ hV hj

    have hx : ∀ x : Fin (R.nW i) → D.what₂.LL, x = 0 := by
      intro x
      by_contra hne
      have hli := (hU i σ).1 1 (fun _ => x) (linearIndependent_unique_iff.mpr hne)
      simp only [hz, LinearMap.zero_apply] at hli
      exact hli.ne_zero 0 rfl

    apply hj
    refine ⟨0, fun f' => ?_⟩
    have hf' : f' = 0 := by
      simpa using hx ((fw.e i f' : (R.FW i).WK) : Fin (R.nW i) → D.what₂.LL)
    subst hf'
    simp
    exact (phiC_zero_rule T hV (wtA (κ i))).symm

end GlobalTheory
end

