import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialNonneg
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0027
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1010
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0231
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0997
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0008
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0998
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0901
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import GroundTheory.AutomorphicForms.MultiplicityOne.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0978
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlowInvSplit
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolDict

theorem flowInv_herm {n : ℕ} {Hm x₀ : Mt n} {q : ℕ} (h : OrthFr Hm q x₀) : Hmᴴ = Hm := by
  obtain ⟨-, hD⟩ := h
  have hdet : x₀.det ≠ 0 := by
    intro h0
    have hd := congrArg Matrix.det hD
    rw [det_mul, det_mul, h0, mul_zero, det_diagonal] at hd
    refine (Finset.prod_ne_zero_iff.mpr fun a _ => ?_) hd.symm
    unfold ReciprocityTheory.ChartRestriction.G.FD.sgn
    split_ifs <;> norm_num
  have hu : IsUnit x₀ := (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet)
  have huH : IsUnit x₀ᴴ := by
    refine (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr ?_)
    rw [det_conjTranspose]
    exact (star_ne_zero).mpr hdet
  have hself : (x₀ᴴ * Hm * x₀)ᴴ = x₀ᴴ * Hm * x₀ := by
    rw [hD, diagonal_conjTranspose]
    congr 1
    funext a
    simp [Complex.conj_ofReal]
  rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, ← Matrix.mul_assoc] at hself
  exact huH.mul_right_injective (hu.mul_left_injective hself)

theorem flowInv_sq {n : ℕ} {Hm : Mt n} {e : Fin n → ℂ} (he : star e ⬝ᵥ Hm.mulVec e = 0) :
    vecMulVec e (star e ᵥ* Hm) * vecMulVec e (star e ᵥ* Hm) = 0 := by
  rw [vecMulVec_mul_vecMulVec, ← dotProduct_mulVec, he, zero_smul]
  ext i j
  simp [vecMulVec_apply]

theorem flowInv_adj {n : ℕ} {Hm : Mt n} (hH : Hmᴴ = Hm) (e : Fin n → ℂ) :
    (vecMulVec e (star e ᵥ* Hm))ᴴ * Hm = Hm * vecMulVec e (star e ᵥ* Hm) := by
  rw [conjTranspose_vecMulVec, star_vecMul, star_star, hH, vecMulVec_mul, mul_vecMulVec]

private theorem one_sub_sub_smul_vecMulVec_eq_mul_of_isotropic {n : ℕ} {Hm : Mt n} {e : Fin n → ℂ} (he : star e ⬝ᵥ Hm.mulVec e = 0)
    (a b : ℂ) : (1 - (b - a) • vecMulVec e (star e ᵥ* Hm) : Mt n) =
      (1 + a • vecMulVec e (star e ᵥ* Hm)) * (1 - b • vecMulVec e (star e ᵥ* Hm)) := by
  have hS := flowInv_sq he
  rw [add_mul, one_mul, mul_sub, mul_one, smul_mul_assoc, mul_smul_comm, hS, smul_zero, smul_zero, sub_zero,
    sub_smul]
  abel

theorem flowInv_mem {n : ℕ} {Hm : Mt n} (hH : Hmᴴ = Hm) {e : Fin n → ℂ} (he : star e ⬝ᵥ Hm.mulVec e = 0)
    (s : ℝ) : (1 + ((s : ℂ) * Complex.I) • vecMulVec e (star e ᵥ* Hm) : Mt n) ∈ Formalism.QuantumDeterminants.UH Hm := by
  show (1 + ((s : ℂ) * Complex.I) • vecMulVec e (star e ᵥ* Hm))ᴴ * Hm *
    (1 + ((s : ℂ) * Complex.I) • vecMulVec e (star e ᵥ* Hm)) = Hm
  have hc : star ((s : ℂ) * Complex.I) = -((s : ℂ) * Complex.I) := by
    simp [Complex.conj_ofReal]
  have h1 : (1 + ((s : ℂ) * Complex.I) • vecMulVec e (star e ᵥ* Hm))ᴴ * Hm =
      Hm * (1 + (-((s : ℂ) * Complex.I)) • vecMulVec e (star e ᵥ* Hm)) := by
    rw [conjTranspose_add, conjTranspose_one, conjTranspose_smul, add_mul, one_mul, smul_mul_assoc,
      flowInv_adj hH e, hc, mul_add, mul_one, mul_smul_comm]
  have h2 := one_sub_sub_smul_vecMulVec_eq_mul_of_isotropic he (-((s : ℂ) * Complex.I)) (-((s : ℂ) * Complex.I))
  have h3 : (1 - (-((s : ℂ) * Complex.I)) • vecMulVec e (star e ᵥ* Hm) : Mt n) =
      1 + ((s : ℂ) * Complex.I) • vecMulVec e (star e ᵥ* Hm) := by
    rw [neg_smul, sub_neg_eq_add]
  rw [sub_self, zero_smul, sub_zero, h3] at h2
  rw [h1, Matrix.mul_assoc, ← h2, mul_one]

private theorem mul_mem_uh {n : ℕ} {Hm g₁ g₂ : Mt n} (h₁ : g₁ ∈ Formalism.QuantumDeterminants.UH Hm) (h₂ : g₂ ∈ Formalism.QuantumDeterminants.UH Hm) :
    g₁ * g₂ ∈ Formalism.QuantumDeterminants.UH Hm := by
  change g₁ᴴ * Hm * g₁ = Hm at h₁
  change g₂ᴴ * Hm * g₂ = Hm at h₂
  show (g₁ * g₂)ᴴ * Hm * (g₁ * g₂) = Hm
  rw [conjTranspose_mul]
  calc g₂ᴴ * g₁ᴴ * Hm * (g₁ * g₂) = g₂ᴴ * (g₁ᴴ * Hm * g₁) * g₂ := by simp only [Matrix.mul_assoc]
    _ = Hm := by rw [h₁, h₂]

theorem flowInv : ∀ (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (Hm : ι → Mt n) (q : ι → ℕ) (x₀ : ι → Mt n) (w : ι → Fin n → ℤ), (∀ τ, OrthFr (Hm τ) (q τ) (x₀ τ)) → ∀ (P : (ι → Fin n → Fin n → ℂ) → ℂ) (e : ι → Fin n → ℂ), (∀ τ, star (e τ) ⬝ᵥ (Hm τ).mulVec (e τ) = 0) → HolSec Hm q w P → (∀ m : ι → Mt n, (∀ τ, InZe (Hm τ) (e τ) (m τ)) → ∀ u ∈ UG Hm, P (fun τ => (m τ * u τ * x₀ τ : Mt n)) = P (fun τ => (u τ * x₀ τ : Mt n))) → ∀ u ∈ UG Hm, ∀ t : ℝ, 0 ≤ t → P (fun τ => ((1 - (t : ℂ) • vecMulVec (e τ) (star (e τ) ᵥ* Hm τ)) * u τ * x₀ τ : Mt n)) = P (fun τ => (u τ * x₀ τ : Mt n)) := by
  intro n ι _ _ Hm q x₀ w hO P e he hP hInv u hu t ht
  have hH : ∀ τ, (Hm τ)ᴴ = Hm τ := fun τ => flowInv_herm (hO τ)
  have hu' : ∀ τ, u τ ∈ Formalism.QuantumDeterminants.UH (Hm τ) := hu
  obtain ⟨hOpen, -, hStab, hBase⟩ := frDoms_open_preconnected_stable n ι Hm q x₀ hO
  let X : ℂ → (ι → Fin n → Fin n → ℂ) := fun z τ =>
    ((1 - z • vecMulVec (e τ) (star (e τ) ᵥ* Hm τ)) * u τ * x₀ τ : Mt n)
  have hXaff : X = fun z τ i j => (u τ * x₀ τ) i j - z * (vecMulVec (e τ) (star (e τ) ᵥ* Hm τ) * u τ * x₀ τ) i j := by
    funext z τ i j
    simp only [X, sub_mul, one_mul, smul_mul_assoc, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  have hXd : Differentiable ℂ X := by
    rw [hXaff]
    refine differentiable_pi.2 fun τ => differentiable_pi.2 fun i => differentiable_pi.2 fun j => ?_
    exact (differentiable_const _).sub (differentiable_id.mul (differentiable_const _))
  have hHU : {z : ℂ | 0 ≤ z.re} ⊆ X ⁻¹' frDoms Hm q := by
    intro z hz
    have hGS := fun τ => FlowGS.flowGS n (Hm τ) (q τ) (x₀ τ) (hO τ) (w τ) (e τ) (he τ) (u τ) (hu' τ)
    choose C A hCA using hGS
    choose u' hu' b hbf using fun τ => hCA τ z.re hz
    have hmem := hStab (fun τ => (1 + (((-z.im : ℝ) : ℂ) * Complex.I) • vecMulVec (e τ) (star (e τ) ᵥ* Hm τ)) * u' τ)
      (show ∀ τ, _ ∈ Formalism.QuantumDeterminants.UH (Hm τ) from fun τ => mul_mem_uh (flowInv_mem (hH τ) (he τ) (-z.im)) (hu' τ)) b (fun τ => (hbf τ).1)
      (fun τ => (x₀ τ : Mt n)) hBase
    suffices hXz : X z = fun τ => ((1 + (((-z.im : ℝ) : ℂ) * Complex.I) • vecMulVec (e τ) (star (e τ) ᵥ* Hm τ)) * u' τ * x₀ τ * b τ : Mt n) by
      show X z ∈ frDoms Hm q
      rw [hXz]
      exact hmem
    funext τ
    have hfac := (hbf τ).2.1
    have hsplit := one_sub_sub_smul_vecMulVec_eq_mul_of_isotropic (he τ) (((-z.im : ℝ) : ℂ) * Complex.I) (z.re : ℂ)
    have hz' : (z.re : ℂ) - ((-z.im : ℝ) : ℂ) * Complex.I = z := by
      apply Complex.ext <;> simp
    rw [hz'] at hsplit
    show (1 - z • vecMulVec (e τ) (star (e τ) ᵥ* Hm τ)) * u τ * x₀ τ = _
    simp only [Matrix.mul_assoc] at hfac ⊢
    rw [hsplit, Matrix.mul_assoc, hfac]
  let f : ℂ → ℂ := fun z => P (X z)
  have hfU : DifferentiableOn ℂ f (X ⁻¹' frDoms Hm q) :=
    hP.1.comp hXd.differentiableOn fun z hz => hz
  have hUo : IsOpen (X ⁻¹' frDoms Hm q) := hOpen.preimage hXd.continuous
  have h0 : (0 : ℂ) ∈ {z : ℂ | 0 ≤ z.re} := by simp
  have hVo := hUo.connectedComponentIn (x := (0 : ℂ))
  have hHV := (convex_halfSpace_re_ge (0 : ℝ)).isPreconnected.subset_connectedComponentIn h0 hHU
  have hfV : AnalyticOnNhd ℂ f (connectedComponentIn (X ⁻¹' frDoms Hm q) 0) :=
    (hfU.mono (connectedComponentIn_subset _ _)).analyticOnNhd hVo
  have eX0 : X 0 = fun τ => (u τ * x₀ τ : Mt n) := by
    funext τ
    show (1 - (0 : ℂ) • vecMulVec (e τ) (star (e τ) ᵥ* Hm τ)) * u τ * x₀ τ = u τ * x₀ τ
    rw [zero_smul, sub_zero, one_mul]
  have hfreq : ∃ᶠ z in nhdsWithin (0 : ℂ) {0}ᶜ, f z = (fun _ => f 0) z := by
    have hT : Filter.Tendsto (fun s : ℝ => (s : ℂ) * Complex.I) (nhdsWithin 0 {0}ᶜ) (nhdsWithin 0 {0}ᶜ) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · have hc : Continuous (fun s : ℝ => (s : ℂ) * Complex.I) := by fun_prop
        simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with s hs
        exact mul_ne_zero (Complex.ofReal_ne_zero.mpr hs) Complex.I_ne_zero
    apply hT.frequently
    refine Filter.Eventually.frequently (Filter.Eventually.of_forall fun s => ?_)
    have h1 := hInv (fun τ => 1 + (((-s : ℝ) : ℂ) * Complex.I) • vecMulVec (e τ) (star (e τ) ᵥ* Hm τ))
      (fun τ => by unfold InZe; exact ⟨-s, rfl⟩) u hu
    have eX : X ((s : ℂ) * Complex.I) =
        fun τ => ((1 + (((-s : ℝ) : ℂ) * Complex.I) • vecMulVec (e τ) (star (e τ) ᵥ* Hm τ)) * u τ * x₀ τ : Mt n) := by
      funext τ
      simp only [X]
      congr 2
      push_cast
      simp only [neg_mul, neg_smul, sub_eq_add_neg]
    show P (X ((s : ℂ) * Complex.I)) = P (X 0)
    rw [eX, eX0]
    exact h1
  have hEq := hfV.eqOn_of_preconnected_of_frequently_eq analyticOnNhd_const
    isPreconnected_connectedComponentIn (mem_connectedComponentIn (hHU h0)) hfreq
  have ht' : (t : ℂ) ∈ {z : ℂ | 0 ≤ z.re} := by simpa using ht
  have key : f t = f 0 := hEq (hHV ht')
  show f t = _
  rw [key]
  show P (X 0) = _
  rw [eX0]

end GlobalTheory.HolDict
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrAtEmb
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature GlobalTheory.GalLift

namespace GlobalTheory.GalOne

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

section Rec

variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)
  (σ : D.what₂.LL →+* ℂ)

abbrev zAt : Fam (Wc D i) := x0Mat (R.MW i σ)

def ConjW (μ' η' : (AE D)ˣ →* Circle) (ω : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (WO (Vc D i) (Wc D i) → ℂ))
    (f₀ f : WO (Vc D i) (Wc D i) → ℂ) : Prop :=
  OverK σ ∧ ChiAt R i σ μ' ∧ IsEtaConj σ R.eta η' ∧ IsWeilDatumO R.ψ (Vc D i) (Wc D i) μ' (μ' * η'⁻¹) ω ∧
    IsThPVecOf R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i σ)) (R.ΛV i) (R.ΛW i) (R.βV i) (R.βW i)
      R.Pg ∅ (fun _ => 1) f₀ f ∧ IsThetaFunO R.ψ (Vc D i) (Wc D i) f

end Rec

variable {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {i : Fin D.R.m}

variable (T R i) in

abbrev OM : Type 1 := OMDat T.toCore R i Unit (fun _ => A.μ0)

abbrev Pinned (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec)
    (O : OM T R i) : Prop :=
  O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0)

abbrev sOf (O : OM T R i) (σ' : O.c'.F →+* ℂ) : T.Q.c.F →+* ℂ := σ'.comp (incF T.Q.c O.c' O.hle)

omit [Algebra T.Q.c.F D.what₂.LL] in

abbrev dictS {s : T.Q.c.F →+* ℂ} (hV : T.V ((i : ℕ) + 1) s = Wc D i) :
    GA D (Wc D i) → Σ k, Frame ((T.U ((i : ℕ) + 1) s).X k).Ψ D.R.r := castDict hV (T.dict ((i : ℕ) + 1) s)

omit [Algebra T.Q.c.F D.what₂.LL] in

abbrev muS {s : T.Q.c.F →+* ℂ} (hV : T.V ((i : ℕ) + 1) s = Wc D i) : GA D (Wc D i) → ℂ := castDict hV (T.mu ((i : ℕ) + 1) s)

omit [Algebra T.Q.c.F D.what₂.LL] in

abbrev xS {s : T.Q.c.F →+* ℂ} (hV : T.V ((i : ℕ) + 1) s = Wc D i) (h : GA D (Wc D i)) : Data D.host.E D.R.r :=
  (T.U ((i : ℕ) + 1) s).X (dictS hV h).1

variable (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (O : OM T R i) (σ : D.what₂.LL →+* ℂ) (σ' : O.c'.F →+* ℂ)

def FactsAt : Prop :=
  res T σ = sOf O σ' ∧ GoodEmb T.Q.c (sOf O σ') ∧ GoodEmb O.c' σ' ∧
    (∀ τ a, (R.MW i σ).ε τ a = decide ((a : ℕ) < ((Wc D i).sig (tauE D τ)).1)) ∧
    IsONeg (Wc D i) (T.Q.Dw ((i : ℕ) + 1)).q (zAt R i σ) ∧
    cart (R.MW i σ) = cartZ (Wc D i) (T.Q.Dw ((i : ℕ) + 1)).q (zAt R i σ) ∧
    (∀ ρ, T.x₀ ((i : ℕ) + 1) (sOf O σ') (tauE D ρ) =
      Matrix.reindex (finCongr (rank_Wc i)) (finCongr (rank_Wc i)) (zAt R i σ ρ)) ∧
    (∀ ρ, relab O.c' σ' (tauE D (lab σ ρ)) = tauE D ρ) ∧
    ∀ μ' η' : (AE D)ˣ →* Circle, ChiAt R i σ μ' → IsEtaConj σ R.eta η' →
      (∀ hV : T.V ((i : ℕ) + 1) (sOf O σ') = Wc D i, MuVal (Wc D i) μ' (muS hV)) ∧
      (∀ v ε, NonSplitAt D v ε → UnramAt ε μ' ∧ UnramAt ε (μ' * η'⁻¹)) ∧ HypConj R i σ μ' η'

def PointAt (hV : T.V ((i : ℕ) + 1) (sOf O σ') = Wc D i) (h : GA D (Wc D i)) : Prop :=
  ∃ γ ∈ GQ (Wc D i), ∃ (g : ℕ) (eT : D.what₂.Tau ≃ (xS hV h).Ψ)
    (Dc : Dic (T.Q.Dw ((i : ℕ) + 1)) O.c' σ' (xS hV h) g (T.Q.Dw ((i : ℕ) + 1)).p (Vc D i).rank (wtA (κ i)))
    (hx : (dictS hV h).2 ∈ (xS hV h).dom),
    IsSet R.ψ R.θ (Vc D i) (Wc D i) (rank_Wc i) (xS hV h) eT Dc.bas ∧ Matched T.Q.c (sOf O σ') (xS hV h) Dc.idx Dc.e ∧
    (xS hV h).p0 = (T.Q.Dw ((i : ℕ) + 1)).q ∧ SelfD (xS hV h) (xS hV h).Λ ∧
    latW (rank_Wc i) (xS hV h).Λ = latG (Wc D i) (γ * h) ∧
    (dictS hV h).2 = frOf (rank_Wc i) eT (mvZ R.θ (γ * h) (zAt R i σ)) ∧
    letI : Algebra T.Q.c.F ℂ := (sOf O σ').toAlgebra
    (∃ (A₀ : AnFib (xS hV h) Dc.bas Dc.idx Dc.e (dictS hV h).2 (xS hV h).Λ
        (ptC (T.U ((i : ℕ) + 1) (sOf O σ')) (dictS hV h).1 ⟨(dictS hV h).2, hx⟩)) (th : (Fin g → ℂ) → ℂ),
      A₀.Reads 1 (ptC (T.U ((i : ℕ) + 1) (sOf O σ')) (dictS hV h).1 ⟨(dictS hV h).2, hx⟩).s th ∧
        MeanOne (xS hV h) Dc.bas Dc.idx (dictS hV h).2 (xS hV h).Λ th) ∧
    ∀ (g' : ℕ) (bas : (Fin g' ⊕ Fin g' → ℤ) ≃ₗ[ℤ] (xS hV h).Λ) (idx : Fin g' ≃ (xS hV h).Ψ × Fin D.R.r)
      (e : Fin g' ≃ Lt1 (T.Q.Dw ((i : ℕ) + 1))), IsSympl (xS hV h) bas → Matched T.Q.c (sOf O σ') (xS hV h) idx e →
      ∀ (A₁ : AnFib (xS hV h) bas idx e (dictS hV h).2 (xS hV h).Λ
          (ptC (T.U ((i : ℕ) + 1) (sOf O σ')) (dictS hV h).1 ⟨(dictS hV h).2, hx⟩))
        (mk : (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (Fin D.R.r → D.host.E)), (∀ a, mk a ∈ (xS hV h).Λ) →
        MarkAd (rank_Wc i) T.Q.l (iotaW T i) (γ * h) mk → A₁.Marked mk

def FrAtEmb (hV : T.V ((i : ℕ) + 1) (sOf O σ') = Wc D i)
    (ω : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (WO (Vc D i) (Wc D i) → ℂ)) (f₀ : WO (Vc D i) (Wc D i) → ℂ)
    (cc : (T.U ((i : ℕ) + 1) (sOf O σ')).Comp → ℂ) : Prop :=
  FrConst R.ψ R.θ (Vc D i) (rank_Wc i) ω f₀ (T.U ((i : ℕ) + 1) (sOf O σ')) (dictS hV) (muS hV) (zAt R i σ) cc

def TermAt (ω : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (WO (Vc D i) (Wc D i) → ℂ))
    (f₀ f : WO (Vc D i) (Wc D i) → ℂ) (ε : ℤˣ) : Prop :=
  ∀ (h : O.Cl' () → GA D (Vc D i)) (J' : Subgroup (Bridge.Gf (Vc D i))),
    RepsR R i A.μ0 h (O.bad ()) J' (O.Lh ()) (O.gam ()) (O.vol ()) →
    ∀ (k : O.Cl' ()) (g' : GA D (Wc D i)) (X : Data D.host.E D.R.r) (eT : D.what₂.Tau ≃ X.Ψ) (g : ℕ)
      (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin D.R.r),
      IsSet R.ψ R.θ (Vc D i) (Wc D i) (rank_Wc i) X eT bas → X.p0 = (T.Q.Dw ((i : ℕ) + 1)).q →
      ∀ L : Lt D.host.E D.R.r, SelfD X L → latW (rank_Wc i) L = latG (Wc D i) g' →
      ∀ v : TF (Vc D i).rank g, IsVac X bas (T.Q.H.w0 : D.host.E) (tens (stdL D.host.E (Vc D i).rank) L) v →
      ∀ a : ℂ, Zak R.ψ R.θ (rank_Wc i) eT bas idx (frOf (rank_Wc i) eT (mvZ R.θ g' (zAt R i σ))) (a • v) (ω (1, g') f₀) →
      ∀ mk₂ : (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (Fin D.R.r → D.host.E), (∀ b, mk₂ b ∈ L) →
        MarkAd (rank_Wc i) (O.dδ ()).l₂ (iotaW T i) g' mk₂ →
      ∀ Y : (Fin (Vc D i).rank → LevQ (T.Q.Dw ((i : ℕ) + 1)) (O.dδ ()).l₂) → Matrix (Fin (Vc D i).rank) (Fin D.R.r) D.host.E,
        IsRoots (O.dδ ()).l₂ L ((ε : ℤ) • mk₂) (O.Nc () k) Y →
        GlobalTheory.SW.IsSB (gphi X bas (T.Q.H.w0 : D.host.E) (O.La () k).La L v (fun q => inC O.c' (O.w () k q)) Y) ∧
        Zak R.ψ R.θ (rank_Wc i) eT bas idx (frOf (rank_Wc i) eT (mvZ R.θ g' (zAt R i σ)))
          ((a * σ' (O.ep () k * ((((O.La () k).mIdx (O.Nc () k) D.R.r : O.c'.F))⁻¹ *
            ((Nat.card (Fin (Vc D i).rank → LevQ (T.Q.Dw ((i : ℕ) + 1)) (O.dδ ()).l₂) : O.c'.F))⁻¹ *
            ((O.La () k).zCard (O.Nc () k) D.R.r : O.c'.F)))) •
            gphi X bas (T.Q.H.w0 : D.host.E) (O.La () k).La L v (fun q => inC O.c' (O.w () k q)) Y) (ω (h k, g') f)

def IsUp (x : VsV D i D.what₂.LL) (x' : VsV D i O.c'.F) : Prop :=
  (x' : Pol O.c'.F D.what₂.Tau (Vc D i).rank) = MvPolynomial.map O.jL (x : Pol D.what₂.LL D.what₂.Tau (Vc D i).rank)

def IsLtAt (lt : LtN (T.Q.Dw ((i : ℕ) + 1)) (Vc D i).rank → FVar D (Wc D i).rank (Vc D i).rank) : Prop :=
  ∀ ℓ, (lt ℓ).2.2 = ℓ.2.2 ∧ ((relab O.c' σ' ℓ.1 = tauE D (lt ℓ).1 ∧ ((lt ℓ).2.1 : ℕ) = ℓ.2.1) ∨
    (relab O.c' σ' ℓ.1 = ReciprocityTheory.ChartRestriction.G.Geo.Tor.conjEmb (tauE D (lt ℓ).1) ∧
      ((lt ℓ).2.1 : ℕ) = (T.Q.Dw ((i : ℕ) + 1)).p + ℓ.2.1))

def IoAt {c : CoefA (Vc D i)} (c₁ : VsV D i D.what₂.LL →ₛₗ[σ] c.W) (f : WO (Vc D i) (Wc D i) → ℂ)
    (Λ : c.W → WO (Vc D i) (Wc D i) → ℂ) (ph : ℂ) : Prop :=
  ∀ x x', IsUp O x x' → ∃ Q : PolF D (Wc D i).rank (Vc D i).rank,
    Λ (c₁ x) = fv R.ψ R.θ (Vc D i) (Wc D i) (T.Q.Dw ((i : ℕ) + 1)).q (zAt R i σ) f Q ∧
    ∀ (X : Data D.host.E D.R.r) (eT : D.what₂.Tau ≃ X.Ψ) (g : ℕ)
      (Dc : Dic (T.Q.Dw ((i : ℕ) + 1)) O.c' σ' X g (T.Q.Dw ((i : ℕ) + 1)).p (Vc D i).rank (wtA (κ i))),
      (∀ ρ, (eT ρ).1 = tauE D ρ) → MvPolynomial.C ph * toP (Vc D i) (rank_Wc i) eT Dc.hr Q =
        MvPolynomial.C ((lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA (κ i)) : ℝ) : ℂ) *
          MvPolynomial.rename Dc.eL (MvPolynomial.map σ' (O.io x'))

def CovAt (c0 : ℂ) : Prop :=
  letI : Algebra (O.dδ ()).c₂.F ℂ := (σ'.comp ((O.dδ ()).eF.symm : (O.dδ ()).c₂.F →+* O.c'.F)).toAlgebra
  ∀ y₂ : FrPt (O.dδ ()).Xo₂ (O.dδ ()).c₂ ℂ, evR (O.dδ ()).Xo₂ (O.dδ ()).c₂ (O.dδ ()).cδ y₂ = c0

end GlobalTheory.GalOne

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FundamentalCharacterIdealPowers
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.LKCx

variable {p : ℕ} [Fact p.Prime]

theorem continuous_gAf_fst (G : HTGroup p) :
    @Continuous G.GAf (AfP p ⊗[ℚ] G.C) _ (moduleTopology (AfP p) (AfP p ⊗[ℚ] G.C))
      (fun g => (((g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C)) := by
  letI : TopologicalSpace (AfP p ⊗[ℚ] G.C) := moduleTopology (AfP p) (AfP p ⊗[ℚ] G.C)
  exact Units.continuous_val.comp (continuous_fst.comp continuous_subtype_val)

theorem continuous_gAf_snd_inv (G : HTGroup p) :
    Continuous (fun g : G.GAf => ((((g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).2)⁻¹ : (AfP p)ˣ) : AfP p)) := by
  letI : TopologicalSpace (AfP p ⊗[ℚ] G.C) := moduleTopology (AfP p) (AfP p ⊗[ℚ] G.C)
  exact Units.continuous_val.comp (continuous_inv.comp (continuous_snd.comp continuous_subtype_val))

theorem exists_compact_of_isTest (G : HTGroup p) (L : G.Level) (f : G.GAf → ℂ)
    (hf : IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f) (h₁ : G.GAf) :
    ∃ Q : Set G.GAf, IsCompact Q ∧ ∀ g, f (h₁⁻¹ * g * h₁) ≠ 0 → g ∈ Q := by
  obtain ⟨S, hS⟩ := hf.2.2.2
  have hK : IsCompact (L.K : Set G.GAf) := L.compact
  refine ⟨⋃ s ∈ S, (fun q : G.GAf × G.GAf => h₁ * (q.1 * s * q.2) * h₁⁻¹) '' ((L.K : Set G.GAf) ×ˢ (L.K : Set G.GAf)),
    S.isCompact_biUnion fun s _ => (hK.prod hK).image (by fun_prop), fun g hg => ?_⟩
  obtain ⟨s, hs, k₁, hk₁, k₂, hk₂, he⟩ := hS _ hg
  refine Set.mem_biUnion hs ⟨(k₁, k₂), ⟨hk₁, hk₂⟩, ?_⟩
  show h₁ * (k₁ * s * k₂) * h₁⁻¹ = g
  rw [← he]; group

theorem exists_compact_toAfF : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (L : G.Level) (f : G.GAf → ℂ),
    IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f → ∀ (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ)
    (hx : Triv G (AfP p) β x t) (h₁ : G.GAf), ∃ (Ω : Set (AfP p ⊗[ℚ] G.C)) (Ω' : Set (AfP p)),
    @IsCompact _ (moduleTopology (AfP p) (AfP p ⊗[ℚ] G.C)) Ω ∧ IsCompact Ω' ∧ ∀ y : grp G β,
    f (h₁⁻¹ * toAfF G β x t hx y * h₁) ≠ 0 → inC G (AfP p) (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) ∈ Ω ∧
    algebraMap ℚ (AfP p) ((((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ)⁻¹) ∈ Ω' := by
  intro p _ G L f hf β x t hx h₁
  letI : TopologicalSpace (AfP p ⊗[ℚ] G.C) := moduleTopology (AfP p) (AfP p ⊗[ℚ] G.C)
  haveI : IsModuleTopology (AfP p) (AfP p ⊗[ℚ] G.C) := ⟨rfl⟩
  haveI : IsTopologicalRing (AfP p ⊗[ℚ] G.C) := IsModuleTopology.isTopologicalRing (AfP p) (AfP p ⊗[ℚ] G.C)
  obtain ⟨Q, hQ, hmem⟩ := exists_compact_of_isTest G L f hf h₁
  refine ⟨(fun g : G.GAf => ((x⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C) *
      (((g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C) * x) '' Q,
    (fun g : G.GAf => ((((g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).2)⁻¹ : (AfP p)ˣ) : AfP p)) '' Q,
    hQ.image ((continuous_const.mul (continuous_gAf_fst G)).mul continuous_const),
    hQ.image (continuous_gAf_snd_inv G), fun y hy => ⟨⟨_, hmem _ hy, ?_⟩, ⟨_, hmem _ hy, ?_⟩⟩⟩
  · show ((x⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C) *
      ((x * Units.map (inC G (AfP p)).toMonoidHom ((y : G.Cˣ × ℚˣ).1) * x⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) :
        AfP p ⊗[ℚ] G.C) * x = _
    simp only [Units.val_mul, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe]
    rw [← mul_assoc, ← mul_assoc, Units.inv_mul, one_mul, mul_assoc, Units.inv_mul, mul_one]
  · show (((Units.map (algebraMap ℚ (AfP p)).toMonoidHom ((y : G.Cˣ × ℚˣ).2))⁻¹ : (AfP p)ˣ) : AfP p) = _
    rw [← map_inv, Units.coe_map, Units.val_inv_eq_inv_val]
    rfl

end GlobalTheory.LKCx
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussIntegralDiagonalHermitianFormMatricesStatement
section
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gaussIntegral_diagonal_hermitianForm_matrices : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] (ψ : AddChar F ℂ) (hψ : Continuous ψ) (_ : ∀ t, ‖ψ t‖ = 1) (_ : ψ ≠ 1) [MeasurableSpace (Matrix α ν E)] [BorelSpace (Matrix α ν E)] (μ : Measure (Matrix α ν E)) [μ.IsAddHaarMeasure], ∃ g : ℂ, ∀ t : α → ν → Fˣ, HasGauss μ (fun x => ψ (∑ i, ∑ j, (t i j : F) * Algebra.norm F (x i j))) (g * ∏ i, ∏ j, (sgn E (t i j) * ((nabs F (t i j))⁻¹ : ℝ))) := by
  first | exact @GlobalTheory.KSp.hasGauss_diag_norm | exact GlobalTheory.KSp.hasGauss_diag_norm | (intros; apply GlobalTheory.KSp.hasGauss_diag_norm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenReadsOfUnfBC
section
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh

theorem genReads_of_unfBC {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
    {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c c' : Coeff l} (hle : c.F ≤ c'.F) {r g : ℕ}
    (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (σ' : c'.F →+* ℂ) (k : (U (σ'.comp (incF c c' hle))).Comp)
    (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] ((U (σ'.comp (incF c c' hle))).X k).Λ)
    (idx : Fin g ≃ ((U (σ'.comp (incF c c' hle))).X k).Ψ × Fin r) (e : Fin g ≃ Lt1 Dw)
    (x : ((U (σ'.comp (incF c c' hle))).X k).dom) (ϑ : (Fin g → ℂ) → ℂ)
    (h : GenReads (unfBC hle U σ') k bas idx e x ϑ) : GenReads (U (σ'.comp (incF c c' hle))) k bas idx e x ϑ := by
  obtain ⟨B, hB⟩ := h
  letI : Algebra c.F ℂ := (σ'.comp (incF c c' hle)).toAlgebra
  letI : Algebra c'.F ℂ := σ'.toAlgebra
  exact ⟨⟨B.ex, B.ex_add, B.ex_onto, B.ex_ker, B.ex_lin, B.hol, B.der, B.fr, B.fr_hol, B.fr_ne, B.fr_g, B.fr_0, B.χ,
    B.χ_norm, B.fr_per⟩, hB⟩

theorem CcIs.unfBC {D : D7} (θ : InfFam D) (V W : HSp D) {r : ℕ} (hr : W.rank = r)
    {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H}
    {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c c' : Coeff l} (hle : c.F ≤ c'.F)
    (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (σ' : c'.F →+* ℂ)
    (dict : GA D W → Σ k, Frame ((U (σ'.comp (incF c c' hle))).X k).Ψ r) (mu : GA D W → ℂ)
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ)
    (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (f₀ : WO V W → ℂ) (cc : (U (σ'.comp (incF c c' hle))).Comp → ℂ)
    (h : CcIs θ V W hr (U (σ'.comp (incF c c' hle))) dict mu x₀ om f₀ cc) :
    CcIs θ V W hr (Formalism.L2.Pj.unfBC hle U σ') dict mu x₀ om f₀ cc := by
  refine ⟨h.1, fun a γ hA hx' g bas idx e hs hi ϑ hϑ w hw => ?_⟩
  have hrel : relab c' σ' = relab c (σ'.comp (incF c c' hle)) := funext fun τ => RingHom.ext fun x => rfl
  have hi' : IdxIs c (σ'.comp (incF c c' hle)) ((U (σ'.comp (incF c c' hle))).X (dict a).1) idx e := by
    unfold IdxIs at hi ⊢
    rw [hrel] at hi
    exact hi
  exact h.2 a γ hA hx' g bas idx e hs hi' ϑ (genReads_of_unfBC hle U σ' _ bas idx e ⟨_, hx'⟩ ϑ hϑ) w hw

theorem ccIs_extend_field : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.Char F → TieIn T R κ v₀ → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (O : OMDat T.toCore R i Tp tup), O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0) → ∀ cc, CcIs R.θ (Vc D i) (Wc D i) (rank_Wc i) (T.U ((i : ℕ) + 1) O.s0) O.dict O.mu (T.x₀ ((i : ℕ) + 1) O.s0) (R.ωP i A.μ0) (R.vacP i) cc → CcIs R.θ (Vc D i) (Wc D i) (rank_Wc i) (unfBC O.hle (T.U ((i : ℕ) + 1)) (inC O.c')) O.dict O.mu (T.x₀ ((i : ℕ) + 1) O.s0) (R.ωP i A.μ0) (R.vacP i) cc := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ _ _ i Tp tup O _ cc h
  exact CcIs.unfBC _ _ _ _ O.hle (T.U ((i : ℕ) + 1)) (inC O.c') _ _ _ _ _ _ h

end GlobalTheory.AdTh
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlobalWhittakerCoefficientLinearArchimedeanKerneStatement
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.globalWhittakerCoefficient_linear_archimedeanKernel : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (F G : GA E a → ℂ), Continuous F → Continuous G → (∀ K : Set (GA E a), IsCompact K → ∃ (C : ℝ) (N : ℕ), ∀ g ∈ K, ∀ y : GL (Fin a) (Cinf E), ‖F (g * infGL E a y)‖ ≤ C * height y ^ N) → (∀ K : Set (GA E a), IsCompact K → ∃ (C : ℝ) (N : ℕ), ∀ g ∈ K, ∀ y : GL (Fin a) (Cinf E), ‖G (g * infGL E a y)‖ ≤ C * height y ^ N) → (∀ (c : ℂ) (g : GA E a), GlobalTheory.JSW.whit (fun x => F x + c * G x) g = GlobalTheory.JSW.whit F g + c * GlobalTheory.JSW.whit G g) ∧ ∀ (X : Type) [MeasurableSpace X] (ν : Measure X) [SFinite ν] (k : X → ℂ) (γ : X → GL (Fin a) (Cinf E)), GlobalTheory.JSW.IsRapidInf ν k γ → ∀ g, GlobalTheory.JSW.whit (GlobalTheory.JSW.kerInf ν k γ F) g = ∫ x, k x * GlobalTheory.JSW.whit F (g * infGL E a (γ x)) ∂ν := by
  first | exact @GlobalTheory.JSW.WhitAlg.whit_linear_kerInf | exact GlobalTheory.JSW.WhitAlg.whit_linear_kerInf | (intros; apply GlobalTheory.JSW.WhitAlg.whit_linear_kerInf <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodEmbeddingLabelIffStatement
section
open NumberField IsDedekindDomain Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolRead
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.good_embedding_label_iff : ∀ (D : D7) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL], LawsJ T → AlgTie T → ∀ (σ : D.what₂.LL →+* ℂ) (ρ : D.what₂.Tau), (GoodEmb T.Q.c (res T σ) ↔ labE σ (lab σ ρ) = tauE D ρ) ∧ lab ((starRingEnd ℂ).comp σ) ρ = lab σ ρ := by
  first | exact @GlobalTheory.HolRead.good_iff_labE_and_lab_conj | exact GlobalTheory.HolRead.good_iff_labE_and_lab_conj | (intros; apply GlobalTheory.HolRead.good_iff_labE_and_lab_conj <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramHspOf
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField

namespace GlobalTheory.WeilSchrodinger

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : D7)

def sesq {k : ℕ} (G : Matrix (Fin k) (Fin k) D.host.E) :
    (Fin k → D.host.E) →ₗ⋆[D.host.E] (Fin k → D.host.E) →ₗ[D.host.E] D.host.E :=
  Matrix.toLinearMapₛₗ₂' D.host.E (starRingEnd D.host.E) (RingHom.id D.host.E) G

def hspOf {k : ℕ} (G : Matrix (Fin k) (Fin k) D.host.E) (herm : (sesq D G).IsSymm) (nd : (sesq D G).Nondegenerate)
    (L : Submodule (𝓞 D.host.E) (Fin k → D.host.E)) (hL : L.IsLattice D.host.E)
    (hU : Formalism.HermitianLatticesTheory.IsUnimodular (sesq D G) L) (sg : (D.host.E →+* ℂ) → ℕ × ℕ) : HSp D where
  V := Fin k → D.host.E
  hT := sesq D G
  herm := herm
  nondeg := nd
  rank := k
  rank_eq := Module.finrank_fin_fun _
  frame := Pi.basisFun _ _
  sig := sg
  L0 := L
  standardTuple_isLattice := hL
  baseLattice_isUnimodular := hU

variable {D}

theorem gram_hspOf {k : ℕ} (G : Matrix (Fin k) (Fin k) D.host.E) (herm : (sesq D G).IsSymm)
    (nd : (sesq D G).Nondegenerate) (L : Submodule (𝓞 D.host.E) (Fin k → D.host.E)) (hL : L.IsLattice D.host.E)
    (hU : Formalism.HermitianLatticesTheory.IsUnimodular (sesq D G) L) (sg : (D.host.E →+* ℂ) → ℕ × ℕ) :
    (hspOf D G herm nd L hL hU sg).gram = G := by
  funext i j
  have e : ∀ m : Fin k, Pi.basisFun D.host.E (Fin k) m = Pi.single m 1 := fun m => Pi.basisFun_apply _ _ m
  simp only [HSpace.gram, hspOf, sesq]
  erw [e i, e j]
  exact Matrix.toLinearMapₛₗ₂'_single (R := D.host.E) (starRingEnd D.host.E) (RingHom.id D.host.E) G i j

end GlobalTheory.WeilSchrodinger

end
end

