import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0068
import Formalism.LocalToGlobal.ProjectiveLattices.HostInt
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FactPrincipalDatum
import Formalism.LocalToGlobal.LatticeGeometry.Bundle0001

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.OmAtSmulRight
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.VacUnique

open GlobalTheory.FockCompare

variable {D : D7}

def hAt (S T : HSp D) (τ : D.what₂.Tau) (x y : Matrix (Fin T.rank) (Fin S.rank) ℂ) : ℂ :=
  ((gramAt D S τ)⁻¹ * yᴴ * gramAt D T τ * x).trace

def omAt (S T : HSp D) (τ : D.what₂.Tau) (x y : Matrix (Fin T.rank) (Fin S.rank) ℂ) : ℝ :=
  2 * (tauE D τ D.host.xi0 * hAt S T τ x y).re

theorem omAt_add_left (S T : HSp D) (τ : D.what₂.Tau) (x x' y : Matrix (Fin T.rank) (Fin S.rank) ℂ) :
    omAt S T τ (x + x') y = omAt S T τ x y + omAt S T τ x' y := by
  simp only [omAt, hAt, Matrix.mul_add, Matrix.trace_add, mul_add, Complex.add_re]

theorem omAt_add_right (S T : HSp D) (τ : D.what₂.Tau) (x y y' : Matrix (Fin T.rank) (Fin S.rank) ℂ) :
    omAt S T τ x (y + y') = omAt S T τ x y + omAt S T τ x y' := by
  simp only [omAt, hAt, Matrix.conjTranspose_add, Matrix.mul_add, Matrix.add_mul, Matrix.trace_add, mul_add,
    Complex.add_re]

theorem omAt_smul_left (S T : HSp D) (τ : D.what₂.Tau) (c : ℝ) (x y : Matrix (Fin T.rank) (Fin S.rank) ℂ) :
    omAt S T τ (c • x) y = c * omAt S T τ x y := by
  simp only [omAt, hAt, Matrix.mul_smul, Matrix.trace_smul, mul_smul_comm, Complex.smul_re, smul_eq_mul]
  ring

theorem omAt_smul_right (S T : HSp D) (τ : D.what₂.Tau) (c : ℝ) (x y : Matrix (Fin T.rank) (Fin S.rank) ℂ) :
    omAt S T τ x (c • y) = c * omAt S T τ x y := by
  simp only [omAt, hAt, Matrix.conjTranspose_smul, star_trivial, Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul,
    mul_smul_comm, Complex.smul_re, smul_eq_mul]
  ring

def omO (S T : HSp D) : RW T S →ₗ[ℝ] RW T S →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun x y => ∑ τ, omAt S T τ (x τ) (y τ))
    (fun x x' y => by rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun τ _ => omAt_add_left S T τ _ _ _)
    (fun c x y => by rw [smul_eq_mul, Finset.mul_sum]; exact Finset.sum_congr rfl fun τ _ => omAt_smul_left S T τ c _ _)
    (fun x y y' => by rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun τ _ => omAt_add_right S T τ _ _ _)
    (fun c x y => by rw [smul_eq_mul, Finset.mul_sum]; exact Finset.sum_congr rfl fun τ _ => omAt_smul_right S T τ c _ _)

theorem omO_apply (S T : HSp D) (x y : RW T S) : omO S T x y = ∑ τ, omAt S T τ (x τ) (y τ) := rfl

theorem cplxO_add {m n : ℕ} (s : Matrix (Fin n) (Fin n) ℂ) (t : Matrix (Fin m) (Fin m) ℂ)
    (x y : Matrix (Fin m) (Fin n) ℂ) : cplxO s t (x + y) = cplxO s t x + cplxO s t y := by
  simp only [cplxO, Matrix.mul_add, Matrix.add_mul, smul_add]

theorem cplxO_smul {m n : ℕ} (s : Matrix (Fin n) (Fin n) ℂ) (t : Matrix (Fin m) (Fin m) ℂ) (c : ℝ)
    (x : Matrix (Fin m) (Fin n) ℂ) : cplxO s t (c • x) = c • cplxO s t x := by
  simp only [cplxO, Matrix.mul_smul, Matrix.smul_mul]
  exact smul_comm _ _ _

def jO (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) : RW T S →ₗ[ℝ] RW T S where
  toFun x := fun τ => cplxO (sS τ) (sT τ) (x τ)
  map_add' x y := by funext τ; exact cplxO_add _ _ _ _
  map_smul' c x := by funext τ; exact cplxO_smul _ _ c _

theorem jO_apply (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (x : RW T S) (τ : D.what₂.Tau) :
    jO S T sS sT x τ = cplxO (sS τ) (sT τ) (x τ) := rfl

def infRat (S T : HSp D) : Matrix (Fin T.rank) (Fin S.rank) D.host.E →+ RW T S where
  toFun γ := fun τ i j => tauE D τ (γ i j)
  map_zero' := by funext τ i j; exact (tauE D τ).map_zero
  map_add' x y := by funext τ i j; exact (tauE D τ).map_add _ _

def finRat (S T : HSp D) : Matrix (Fin T.rank) (Fin S.rank) D.host.E →+ WO S T where
  toFun γ := Matrix.of fun i j => (pairA D.host.F 0 1) ⊗ₜ[D.host.F] (γ i j)
  map_zero' := by funext i j; exact TensorProduct.tmul_zero _ _
  map_add' x y := by funext i j; exact TensorProduct.tmul_add _ _ _

theorem finRat_inf (S T : HSp D) (γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    (finRat S T γ).map (infPart D) = 0 := by
  funext i j
  show (0 : Ainf D.host.F) ⊗ₜ[D.host.F] (γ i j) = 0
  exact TensorProduct.zero_tmul _ _

theorem finRat_fin (S T : HSp D) (γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    (finRat S T γ).map (finPart D) = (ratW T S γ).map (finPart D) := rfl

theorem piW_of_inf (θ : InfFam D) {S T : HSp D} {u : WO S T} (hu : u.map (infPart D) = 0) :
    piW θ T S u = 0 := by
  funext τ i j
  have : infPart D (u i j) = 0 := congrFun (congrFun hu i) j
  show θ τ (infPart D (u i j)) = 0
  rw [this, RingHom.map_zero]

theorem piW_ratW {θ : InfFam D} (hθ : IsInfFam θ) (S T : HSp D)
    (γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) : piW θ T S (ratW T S γ) = infRat S T γ := by
  funext τ i j
  exact comp_incA hθ τ _

theorem ratW_eq {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (h : Chart θ σ) (S T : HSp D)
    (γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    ratW T S γ = iotaW σ T S (infRat S T γ) + finRat S T γ := by
  have e : (ratW T S γ - finRat S T γ : WA T S) = iotaW σ T S (infRat S T γ) := by
    refine h.real_ext ?_ (h.real_iota T S _) ?_
    · funext i j
      have e1 : finPart D (finRat S T γ i j) = finPart D (ratW T S γ i j) := rfl
      show finPart D (ratW T S γ i j - finRat S T γ i j) = 0
      rw [RingHom.map_sub, e1, sub_self]
    · rw [AddMonoidHom.map_sub, piW_of_inf θ (finRat_inf S T γ), piW_ratW h.inf, h.pi_iota, sub_zero]
  exact sub_eq_iff_eq_add.1 e

theorem latO_inf (S T : HSp D) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E))
    (P : HeightOneSpectrum (𝓞 D.host.F) → Prop) {u : WO S T} (hu : u ∈ latO S T LS LT P) :
    u.map (infPart D) = 0 := by
  have : latO S T LS LT P ≤ ((infPart D).toAddMonoidHom.mapMatrix (m := Fin T.rank) (n := Fin S.rank)).ker := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨α, -, -, a, -, s, -, t, -, rfl⟩
    funext i j
    show (0 : Ainf D.host.F) ⊗ₜ[D.host.F] _ = 0
    exact TensorProduct.zero_tmul _ _
  exact this hu

end GlobalTheory.VacUnique

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.OneEqSumPlaceIdempotentsOverTwoAddTwoMul
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.LatVac
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LatVac

theorem evalV_singleV_same (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    evalV F v (singleV F v 1) = 1 := by
  classical
  exact RestrictedProduct.single_eq_same
    (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) v 1

theorem evalV_singleV_ne (F : Type) [Field F] [NumberField F] (v v' : HeightOneSpectrum (𝓞 F))
    (h : v' ≠ v) : evalV F v' (singleV F v 1) = 0 := by
  classical
  exact RestrictedProduct.single_eq_of_ne
    (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) 1 h

theorem half_mem_adicCompletionIntegers (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (h : (2 : 𝓞 F) ∉ v.asIdeal) : algebraMap F (Fv F v) (2 : F)⁻¹ ∈ v.adicCompletionIntegers F := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  have h1 : v.valuation F (algebraMap (𝓞 F) F 2) = 1 := (v.valuation_eq_one_iff_notMem (K := F)).2 h
  rw [map_ofNat] at h1
  have h2 : Valued.v (algebraMap F (Fv F v) (2 : F)⁻¹) = v.valuation F (2 : F)⁻¹ :=
    v.valuedAdicCompletion_eq_valuation' _
  rw [h2, map_inv₀, h1, inv_one]

theorem one_eq_sum_singleV_add_two_mul : ∀ (F : Type) [Field F] [NumberField F], ∃ P : Finset (HeightOneSpectrum (𝓞 F)), (∀ v ∈ P, (2 : 𝓞 F) ∈ v.asIdeal) ∧ (∀ v : HeightOneSpectrum (𝓞 F), singleV F v 1 ∈ intAf F ∧ evalV F v (singleV F v 1) = 1 ∧ ∀ v', v' ≠ v → evalV F v' (singleV F v 1) = 0) ∧ ∃ β ∈ intAf F, (1 : Af F) = ∑ v ∈ P, singleV F v 1 + 2 * β := by
  intro F _ _
  classical
  have hfin : {v : HeightOneSpectrum (𝓞 F) | (2 : 𝓞 F) ∈ v.asIdeal}.Finite := by
    have h := Ideal.finite_factors (I := Ideal.span {(2 : 𝓞 F)}) (by simp)
    refine h.subset fun v hv => ?_
    exact Ideal.dvd_span_singleton.2 hv
  refine ⟨hfin.toFinset, fun v hv => by simpa using hv, fun v => ⟨fun w => ?_, evalV_singleV_same F v,
    evalV_singleV_ne F v⟩, algebraMap F (Af F) (2 : F)⁻¹ * (1 - ∑ v ∈ hfin.toFinset, singleV F v 1),
    fun w => ?_, ?_⟩
  · by_cases hw : w = v
    · subst hw
      rw [evalV_singleV_same]; exact one_mem _
    · rw [evalV_singleV_ne F v w hw]; exact zero_mem _
  · rw [map_mul, map_sub, map_one, map_sum, AlgHom.commutes]
    by_cases hw : w ∈ hfin.toFinset
    · rw [Finset.sum_eq_single_of_mem w hw fun b _ hb => evalV_singleV_ne F b w hb.symm,
        evalV_singleV_same, sub_self, mul_zero]
      exact zero_mem _
    · rw [Finset.sum_eq_zero fun b hb => evalV_singleV_ne F b w fun h => hw (h ▸ hb), sub_zero, mul_one]
      exact half_mem_adicCompletionIntegers F w (by simpa using hw)
  · have h2 : (2 : Af F) * algebraMap F (Af F) (2 : F)⁻¹ = 1 := by
      rw [← map_ofNat (algebraMap F (Af F)) 2, ← map_mul, mul_inv_cancel₀ two_ne_zero, map_one]
    rw [← mul_assoc, h2, one_mul, add_sub_cancel]

end GlobalTheory.LatVac
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RationalHermitianRankOneLatticeSelfDual
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.LatVac
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LatVac.RatDual

open Formalism.L2.Pj

variable {D : D7}

theorem mem_mul_of_trace (D : D7) (z : D.host.E)
    (h : ∀ a : 𝓞 D.host.E, ∃ n : ℤ, Algebra.trace ℚ D.host.E (D.host.xi0 * (a * z)) = n) :
    z ∈ D.host.AA * D.host.AAbar := by
  have hP := Formalism.IndefR.Fin.factPrincipalDatum
  have hξ := cmHost_imaginaryGenerator_ne_zero hP D
  have hz : D.host.xi0 * z ∈
      FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) := by
    rw [FractionalIdeal.mem_dual
      (@one_ne_zero (FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) _ _ _)]
    intro a ha
    rw [FractionalIdeal.mem_one_iff] at ha
    obtain ⟨c, rfl⟩ := ha
    obtain ⟨n, hn⟩ := h c
    rw [Algebra.traceForm_apply, mul_assoc, mul_comm z]
    exact ⟨n, (eq_intCast (algebraMap ℤ ℚ) _).trans hn.symm⟩
  rw [← dual_eq hP D] at hz
  have h4 := FractionalIdeal.mul_mem_mul
    (FractionalIdeal.mem_spanSingleton_self (nonZeroDivisors (𝓞 D.host.E)) D.host.xi0⁻¹) hz
  have e1 : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) D.host.xi0⁻¹ *
      (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) D.host.xi0 * D.host.AA * D.host.AAbar) =
      D.host.AA * D.host.AAbar := by
    rw [mul_assoc, ← mul_assoc, FractionalIdeal.spanSingleton_mul_spanSingleton, inv_mul_cancel₀ hξ,
      FractionalIdeal.spanSingleton_one, one_mul]
  rwa [e1, ← mul_assoc, inv_mul_cancel₀ hξ, one_mul] at h4

theorem mem_AA_of_trace (D : D7) (z : D.host.E)
    (h : ∀ a ∈ D.host.AA, ∃ n : ℤ, Algebra.trace ℚ D.host.E (D.host.xi0 * (star a * z)) = n) :
    z ∈ D.host.AA := by
  have hAb : D.host.AAbar ≠ 0 := by
    intro h
    have h1 := Formalism.IndefR.Fin.factPrincipalDatum D.R D.host
    rw [h, mul_zero, zero_mul] at h1
    exact zero_ne_one h1
  have hle : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) z *
      D.host.AAbar ≤ D.host.AA * D.host.AAbar := by
    rw [FractionalIdeal.spanSingleton_mul_le_iff]
    intro b hb
    refine mem_mul_of_trace D _ fun c => ?_
    have hcb : (c : D.host.E) * b ∈ D.host.AAbar :=
      Submodule.smul_mem (D.host.AAbar : Submodule (𝓞 D.host.E) D.host.E) c hb
    have := h _ (conj_mem_AA D hcb)
    have hs : star (D.host.conj ((c : D.host.E) * b)) = (c : D.host.E) * b :=
      (bridge_star_holds D.R D.host _).trans (conj_conj D _)
    rwa [hs, mul_assoc, mul_comm b] at this
  have hle2 : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) z ≤ D.host.AA := by
    calc FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) z
        = D.host.AAbar⁻¹ * (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E))
            z * D.host.AAbar) := by
          rw [mul_comm _ D.host.AAbar, ← mul_assoc, inv_mul_cancel₀ hAb, one_mul]
      _ ≤ D.host.AAbar⁻¹ * (D.host.AA * D.host.AAbar) := CovariantClass.elim D.host.AAbar⁻¹ hle
      _ = D.host.AA := by rw [mul_comm D.host.AA, ← mul_assoc, inv_mul_cancel₀ hAb, one_mul]
  exact hle2 (FractionalIdeal.mem_spanSingleton_self _ _)

theorem form_smul (T : HSp D) (e : D.host.E) (t y : Fin T.rank → D.host.E) :
    ∑ c, ∑ d, star (t c) * T.gram c d * (e • y) d = e * ∑ c, ∑ d, star (t c) * T.gram c d * y d := by
  simp only [Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

theorem genMap_mulVec (S T : HSp D) (a : D.host.E) (s' s : Fin S.rank → D.host.E)
    (t : Fin T.rank → D.host.E) :
    genMap S T a s' t *ᵥ s = (a * ∑ c, ∑ d, star (s' c) * S.gram c d * s d) • t := by
  funext i
  rw [Finset.sum_comm]
  simp only [genMap, Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

theorem hRat_add_left (S T : HSp D) (x x' y : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    hRat S T (x + x') y = hRat S T x y + hRat S T x' y := by
  simp only [hRat, Matrix.add_apply, mul_add, Finset.sum_add_distrib]

theorem hRat_add_right (S T : HSp D) (x y y' : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    hRat S T x (y + y') = hRat S T x y + hRat S T x y' := by
  simp only [hRat, Matrix.add_apply, star_add, mul_add, add_mul, Finset.sum_add_distrib]

theorem hRat_neg_left (S T : HSp D) (x y : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    hRat S T (-x) y = -hRat S T x y := by
  simp only [hRat, Matrix.neg_apply, mul_neg, Finset.sum_neg_distrib]

theorem hRat_neg_right (S T : HSp D) (x y : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    hRat S T x (-y) = -hRat S T x y := by
  simp only [hRat, Matrix.neg_apply, star_neg, mul_neg, neg_mul, Finset.sum_neg_distrib]

theorem hRat_mem (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
    (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT)
    {ρ ℓ : Matrix (Fin T.rank) (Fin S.rank) D.host.E}
    (hρ : ρ ∈ latRat S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)))
    (hℓ : ℓ ∈ latRat S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E))) :
    hRat S T ρ ℓ ∈ NAA D := by
  induction hρ using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨a', ha', s', hs', t', ht', rfl⟩ := hw
    induction hℓ using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨a, ha, s, hs, t, ht, rfl⟩ := hw
      obtain ⟨p, hp⟩ := (hS.2 s).1 hs s' hs'
      obtain ⟨q, hq⟩ := (hT.2 t').1 ht' t ht
      rw [hRat_genMap, genMap_mulVec, form_smul, ← hp, ← hq]
      have hs : star a = D.host.conj a := bridge_star_holds D.R D.host a
      have e : star a * (a' * (p : D.host.E) * (q : D.host.E)) = (p * q) • (a' * D.host.conj a) := by
        rw [hs, Algebra.smul_def, map_mul]
        change _ = (p : D.host.E) * (q : D.host.E) * _
        ring
      rw [e]
      exact Submodule.smul_mem _ _ (FractionalIdeal.mul_mem_mul ha' (conj_mem_AAbar D ha))
    | zero => simp [hRat]
    | add x y _ _ hx hy => rw [hRat_add_right]; exact add_mem hx hy
    | neg x _ hx => rw [hRat_neg_right]; exact neg_mem hx
  | zero => simp [hRat]
  | add x y _ _ hx hy => rw [hRat_add_left]; exact add_mem hx hy
  | neg x _ hx => rw [hRat_neg_left]; exact neg_mem hx

end GlobalTheory.LatVac.RatDual

namespace GlobalTheory.LatVac

open RatDual Formalism.L2.Pj

theorem latRat_selfDual : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → (∃ (n : ℕ) (s s' : Fin n → Fin S.rank → D.host.E), (∀ i, s i ∈ ΛS ∧ s' i ∈ ΛS) ∧ ∀ a j, ∑ i, s i a * ∑ k, star (s' i k) * S.gram k j = if a = j then 1 else 0) → ∀ ρ : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ρ ∈ latRat S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) ↔ ∀ ℓ ∈ latRat S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)), ∃ n : ℤ, Algebra.trace ℚ D.host.E (D.host.xi0 * hRat S T ρ ℓ) = n := by
  intro D S T ΛS ΛT hS hT ⟨n, s, s', hss, hdual⟩ ρ
  have hP := Formalism.IndefR.Fin.factPrincipalDatum
  have hAA := AA_ne_zero hP D
  refine ⟨fun hρ ℓ hℓ => trace_int_of_mem hP D (hRat_mem S T ΛS ΛT hS hT hρ hℓ), fun h => ?_⟩
  have h5 : ∀ v ∈ ΛS, ∀ t ∈ ΛT, ∑ c, ∑ d, star (t c) * T.gram c d * (ρ *ᵥ v) d ∈ D.host.AA := by
    intro v hv t ht
    refine mem_AA_of_trace D _ fun a ha => ?_
    rw [← hRat_genMap]
    exact h _ (AddSubgroup.subset_closure ⟨a, ha, v, hv, t, ht, rfl⟩)
  have h6 : ∀ v ∈ ΛS, ∀ b ∈ D.host.AA⁻¹, b • (ρ *ᵥ v) ∈ ΛT := by
    intro v hv b hb
    refine (hT.2 _).2 fun t ht => ?_
    rw [form_smul]
    have := FractionalIdeal.mul_mem_mul hb (h5 v hv t ht)
    rw [inv_mul_cancel₀ hAA, FractionalIdeal.mem_one_iff] at this
    exact this
  have h7 : ∀ v ∈ ΛS, ∀ v' ∈ ΛS, ∀ e ∈ D.host.AA * D.host.AA⁻¹, genMap S T e v' (ρ *ᵥ v) ∈
      latRat S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) := by
    intro v hv v' hv' e he
    refine FractionalIdeal.mul_induction_on (C := fun e => genMap S T e v' (ρ *ᵥ v) ∈
      latRat S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E))) he
      (fun a ha c hc => ?_) (fun u w hu hw => ?_)
    · refine AddSubgroup.subset_closure ⟨a, ha, v', hv', c • (ρ *ᵥ v), h6 v hv c hc, ?_⟩
      ext i j
      simp only [genMap, Matrix.of_apply, Pi.smul_apply, smul_eq_mul, mul_assoc]
    · have e : genMap S T (u + w) v' (ρ *ᵥ v) = genMap S T u v' (ρ *ᵥ v) + genMap S T w v' (ρ *ᵥ v) := by
        ext i j
        simp only [genMap, Matrix.of_apply, Matrix.add_apply, add_mul]
      show genMap S T (u + w) v' (ρ *ᵥ v) ∈ _
      rw [e]
      exact add_mem hu hw
  have e : ρ = ∑ i, genMap S T 1 (s' i) (ρ *ᵥ s i) := by
    refine Matrix.ext fun a j => ?_
    have h8 : ρ a j = ∑ b, ρ a b * ∑ i, s i b * ∑ k, star (s' i k) * S.gram k j := by
      simp only [hdual, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [h8, Matrix.sum_apply]
    simp only [genMap, Matrix.of_apply, one_mul, Matrix.mulVec, dotProduct]
    simp only [Finset.mul_sum (s := Finset.univ (α := Fin n))]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [← mul_assoc]
    exact (Finset.sum_mul _ _ _).symm
  rw [e]
  exact sum_mem fun i _ => h7 _ (hss i).1 _ (hss i).2 1
    (by rw [mul_inv_cancel₀ hAA]; exact FractionalIdeal.one_mem_one _)

end GlobalTheory.LatVac
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.StdCharFinitePartRationalEqExpTrace
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.LatVac
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdRat

theorem sum_cmType_eq_trace {F E ι : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [Fintype ι] (h2 : Module.finrank F E = 2) (τ : ι → (E →+* ℂ)) (hi : Function.Injective τ)
    (hcm : ∀ σ, (∃ t, τ t = σ) ↔ ¬ ∃ t, τ t = ComplexEmbedding.conjugate σ) (x : F)
    (hx : ∀ σ : E →+* ℂ, ComplexEmbedding.conjugate σ (algebraMap F E x) = σ (algebraMap F E x)) :
    ∑ t, τ t (algebraMap F E x) = ((Algebra.trace ℚ F x : ℚ) : ℂ) := by
  classical
  set y := algebraMap F E x with hy
  have h1 : ((Algebra.trace ℚ E y : ℚ) : ℂ) = ∑ σ : E →+* ℂ, σ y := by
    have := trace_eq_sum_embeddings (K := ℚ) (L := E) ℂ (x := y)
    rw [eq_ratCast] at this
    rw [this]
    exact (Fintype.sum_equiv (RingHom.equivRatAlgHom E ℂ) _ _ fun _ => rfl).symm
  have h3 : Algebra.trace ℚ E y = 2 * Algebra.trace ℚ F x := by
    rw [← Algebra.trace_trace (S := F), hy, Algebra.trace_algebraMap, h2, map_nsmul, nsmul_eq_mul]
    rfl
  have hb : Function.Bijective (Sum.elim τ fun t => ComplexEmbedding.conjugate (τ t)) := by
    have hc : ∀ σ : E →+* ℂ, ComplexEmbedding.conjugate (ComplexEmbedding.conjugate σ) = σ :=
      fun σ => star_star σ
    constructor
    · rintro (a | a) (b | b) h <;> simp only [Sum.elim_inl, Sum.elim_inr] at h
      · rw [hi h]
      · exact absurd ⟨a, h⟩ ((hcm (τ b)).1 ⟨b, rfl⟩)
      · exact absurd ⟨b, h.symm⟩ ((hcm (τ a)).1 ⟨a, rfl⟩)
      · have := congrArg ComplexEmbedding.conjugate h
        rw [hc, hc] at this
        rw [hi this]
    · intro σ
      by_cases h : ∃ t, τ t = ComplexEmbedding.conjugate σ
      · obtain ⟨t, ht⟩ := h
        exact ⟨Sum.inr t, by simp only [Sum.elim_inr]; rw [ht, hc]⟩
      · obtain ⟨t, ht⟩ := (hcm σ).2 h
        exact ⟨Sum.inl t, ht⟩
  have h4 := hb.sum_comp fun σ : E →+* ℂ => σ y
  rw [Fintype.sum_sum_type, ← h1, h3] at h4
  simp only [Sum.elim_inl, Sum.elim_inr, hx] at h4
  push_cast at h4
  linear_combination h4 / 2

theorem tauE_injective (D : D7) : Function.Injective (tauE D) := fun _ _ h =>
  D.eTau.injective (Subtype.ext ((factEmb D.R D.host).1.1 h))

theorem tauE_cm (D : D7) (σ : D.host.E →+* ℂ) :
    (∃ τ, tauE D τ = σ) ↔ ¬ ∃ τ, tauE D τ = ComplexEmbedding.conjugate σ := by
  obtain ⟨g, rfl⟩ := (factEmb D.R D.host).1.2 σ
  have hc : ComplexEmbedding.conjugate (D.host.emb g) = D.host.emb (g * D.R.cc) := by
    rw [Formalism.L2.Geo.emb_mul_cc_comp]
    refine RingHom.ext fun x => ?_
    have hcm := D.host.isCMField_hostE
    have h : IsCMField.complexConj D.host.E x = D.host.conj x := by
      apply D.host.φ₀.injective
      rw [IsCMField.complexEmbedding_complexConj]
      exact (D.host.toHostAx.conjE_apply _ x).symm
    show starRingEnd ℂ (D.host.emb g x) = D.host.emb g (D.host.conj x)
    rw [← h, IsCMField.complexEmbedding_complexConj]
  have h : ∀ g, (∃ τ, tauE D τ = D.host.emb g) ↔ g ∈ D.R.Psi := fun g => by
    rw [← Formalism.L2.Geo.exists_tauEmb_iff D g]
    exact exists_congr fun τ => eq_comm
  rw [hc, h, h]
  exact Formalism.L2.Geo.mem_Psi_iff_mul_cc_notMem g

theorem sum_tauE_eq_trace (D : D7) (x : D.host.F) :
    ∑ t, tauE D t (algebraMap D.host.F D.host.E x) = ((Algebra.trace ℚ D.host.F x : ℚ) : ℂ) := by
  have hcm := D.host.isCMField_hostE
  refine sum_cmType_eq_trace ?_ _ (tauE_injective D) (tauE_cm D) x fun σ => ?_
  · exact Algebra.IsQuadraticExtension.finrank_eq_two _ _
  · show starRingEnd ℂ (σ _) = _
    rw [← IsCMField.complexEmbedding_complexConj]
    exact congrArg σ ((IsCMField.complexConj D.host.E).commutes x)

theorem char_fin_rat {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) (h : IsCharAF F ψ) (x : F) :
    ψ (pairA F 0 (algebraMap F (Af F) x)) = psiInf F ψ (algebraMap F (Ainf F) (-x)) := by
  have e : pairA F 0 (algebraMap F (Af F) x) =
      algebraMap F (AF F) x + pairA F (algebraMap F (Ainf F) (-x)) 0 := by
    refine Prod.ext ?_ (add_zero _).symm
    show (0 : Ainf F) = algebraMap F (Ainf F) x + algebraMap F (Ainf F) (-x)
    rw [map_neg, add_neg_cancel]
  rw [e, AddChar.map_add_eq_mul, h.2.2.1, one_mul, psiInf]

theorem tmul_one_eq {F E A : Type} [Field F] [Field E] [CommRing A] [Algebra F E] [Algebra F A] (x : F) :
    (algebraMap F A x) ⊗ₜ[F] (1 : E) = (1 : A) ⊗ₜ[F] (algebraMap F E x) := by
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]

theorem stdChar_fin_rat : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ x : D.host.F, ψ (pairA D.host.F 0 (algebraMap D.host.F (Af D.host.F) x)) = Complex.exp (2 * Real.pi * Complex.I * ((Algebra.trace ℚ D.host.F x : ℚ) : ℂ)) := by
  intro D ψ hψ x
  obtain ⟨θ, hθ⟩ := hψ.2.1
  rw [char_fin_rat ψ hψ.1, hψ.2.2 θ hθ, tmul_one_eq,
    Finset.sum_congr rfl fun ρ _ => (hθ ρ).1 _, sum_tauE_eq_trace, map_neg]
  congr 1
  push_cast
  ring

end GlobalTheory.StdRat

end
end

