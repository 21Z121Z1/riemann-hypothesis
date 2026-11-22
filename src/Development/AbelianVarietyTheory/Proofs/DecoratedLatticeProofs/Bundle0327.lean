import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0023
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0187
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0129
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0104
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0271
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0317
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0232
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0134
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0417
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0415
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0179
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0147
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0321
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0241
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0021
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0010
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CollSBound
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0054
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.DegenerateConstant
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LoopTerm
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0052
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0020
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatSelfDualOfUnimod
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0318
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0103

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CentralEigenThetaIsFockVectorBoundedDegree
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped InnerProductSpace ComplexConjugate

namespace GlobalTheory.SeeSaw.CenFockPf

variable {D : D7}

theorem thPair_smul_smul {m n : ℕ} (μ : Measure (Mx D m n)) (𝓕 : Set (Mx D m n)) (a b : ℂ) (f g : Mx D m n → ℂ) :
    thPair μ 𝓕 (a • f) (b • g) = (a * star b) * thPair μ 𝓕 f g := by
  unfold thPair
  rw [← integral_const_mul]
  congr 1; funext w
  simp only [Pi.smul_apply, smul_eq_mul, star_mul']
  ring

theorem heisO_sub (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (u : WO S T) (f g : WO S T → ℂ) :
    heisO ψ S T u (f - g) = heisO ψ S T u f - heisO ψ S T u g := by
  funext w; simp only [heisO, Pi.sub_apply]; ring

theorem isLatVac_sub (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) {Λ : AddSubgroup (WO S T)} {f g : WO S T → ℂ}
    (hf : IsLatVac (heisO ψ S T) Λ f) (hg : IsLatVac (heisO ψ S T) Λ g) : IsLatVac (heisO ψ S T) Λ (f - g) :=
  ⟨fun u hu => by rw [heisO_sub, hf.1 u hu, hg.1 u hu],
    fun e he u hu hh => by rw [heisO_sub, hf.2 e he u hu hh, hg.2 e he u hu hh]⟩

theorem comb_single_zero (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (f : WO S T → ℂ) :
    comb ψ S T (Finsupp.single 0 1) f = f := by
  unfold comb
  rw [Finsupp.support_single_ne_zero _ one_ne_zero, Finset.sum_singleton, Finsupp.single_eq_same, one_smul]
  funext w
  simp [heisO, symplOH, symplO, hO]

theorem isFinComb_single_zero (S T : HSp D) : IsFinComb (Finsupp.single (0 : WO S T) (1 : ℂ)) := by
  intro u hu
  rw [Finsupp.support_single_ne_zero _ one_ne_zero, Finset.mem_singleton] at hu
  subst hu
  ext i j; simp

section Pair

variable {m n : ℕ} (μ : Measure (Mx D m n)) (𝓕 : Set (Mx D m n))

theorem thPair_sum_right {ι : Type} (s : Finset ι) (a : ι → ℂ) (g : Mx D m n → ℂ) (h : ι → Mx D m n → ℂ)
    (hi : ∀ i, Integrable (fun w => g w * star (h i w)) (μ.restrict 𝓕)) :
    thPair μ 𝓕 g (∑ i ∈ s, a i • h i) = ∑ i ∈ s, star (a i) * thPair μ 𝓕 g (h i) := by
  unfold thPair
  have e : ∀ w, g w * star ((∑ i ∈ s, a i • h i) w) = ∑ i ∈ s, star (a i) * (g w * star (h i w)) := by
    intro w
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, star_sum, star_mul', Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  simp_rw [e]
  rw [integral_finset_sum _ fun i _ => (hi i).const_mul _]
  exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _

theorem thPair_sub_sum_left {ι : Type} (s : Finset ι) (a : ι → ℂ) (f g : Mx D m n → ℂ) (h : ι → Mx D m n → ℂ)
    (hf : Integrable (fun w => f w * star (g w)) (μ.restrict 𝓕))
    (hi : ∀ i, Integrable (fun w => h i w * star (g w)) (μ.restrict 𝓕)) :
    thPair μ 𝓕 (f - ∑ i ∈ s, a i • h i) g = thPair μ 𝓕 f g - ∑ i ∈ s, a i * thPair μ 𝓕 (h i) g := by
  unfold thPair
  have e : ∀ w, (f - ∑ i ∈ s, a i • h i) w * star (g w) = f w * star (g w) - ∑ i ∈ s, a i * (h i w * star (g w)) := by
    intro w
    simp only [Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, sub_mul, Finset.sum_mul]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by ring
  simp_rw [e]
  rw [integral_sub hf (integrable_finset_sum _ fun i _ => (hi i).const_mul _),
    integral_finset_sum _ fun i _ => (hi i).const_mul _]
  congr 1
  exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _

end Pair

theorem exists_orth_coeff {X : Type} [MeasurableSpace X] (ν : Measure X) {ι : Type} [Fintype ι] (f : X → ℂ) (h : ι → X → ℂ)
    (hf : MemLp f 2 ν) (hh : ∀ i, MemLp (h i) 2 ν) :
    ∃ c : ι → ℂ, ∀ j, ∫ w, f w * star (h j w) ∂ν = ∑ i, c i * ∫ w, h i w * star (h j w) ∂ν := by
  have ip : ∀ (a b : X → ℂ) (ha : MemLp a 2 ν) (hb : MemLp b 2 ν),
      inner ℂ (hb.toLp b) (ha.toLp a) = ∫ w, a w * star (b w) ∂ν := by
    intro a b ha hb
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [ha.coeFn_toLp, hb.coeFn_toLp] with w h1 h2
    rw [h1, h2]
    simp
  let H : ι → Lp ℂ 2 ν := fun i => (hh i).toLp (h i)
  let K : Submodule ℂ (Lp ℂ 2 ν) := Submodule.span ℂ (Set.range H)
  haveI : FiniteDimensional ℂ K := FiniteDimensional.span_of_finite ℂ (Set.finite_range H)
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 (K.starProjection_apply_mem (hf.toLp f))
  refine ⟨c, fun j => ?_⟩
  have h0 := (Submodule.mem_orthogonal K _).1 (K.sub_starProjection_mem_orthogonal (hf.toLp f)) (H j)
    (Submodule.subset_span ⟨j, rfl⟩)
  rw [← hc, inner_sub_right, inner_sum, sub_eq_zero] at h0
  rw [← ip f (h j) hf (hh j)]
  refine h0.trans (Finset.sum_congr rfl fun i _ => ?_)
  rw [inner_smul_right, ← ip (h i) (h j) (hh i) (hh j)]

theorem isLatVac_pureTensorO {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} {x : DefSp S} {y : DefSp T}
    {f₀ : WO S T → ℂ} (hvac : IsVacO ψ θ S T x.s y.s x.L y.L f₀) (φ : MvPolynomial (FVar D T.rank S.rank) ℂ) :
    IsLatVac (heisO ψ S T) (latO S T x.L y.L fun _ => True) (pureTensorO ψ θ S T x.s y.s x.B y.B f₀ φ) := by
  have hth : ∀ φ, IsThetaFunO ψ S T (pureTensorO ψ θ S T x.s y.s x.B y.B f₀ φ) := fun φ =>
    GlobalTheory.Chain.InnerSteps.theta_pureTensorO hvac.1 hvac.2.inf x.s x.B y.s y.B hvac.2.theta φ
  refine ⟨fun u hu => ?_, fun e he u hu hh => ?_⟩
  · exact GlobalTheory.Hk3.FiniteHeis.heisO_pureTensorO_of_finite ψ θ S T hvac.2.inf x.s y.s x.B y.B f₀ hth (2 • u)
      (GlobalTheory.VacGood.infPart_latO (AddSubgroup.nsmul_mem _ hu 2)) (hvac.2.lat.1 u hu) φ
  · exact GlobalTheory.Hk3.FiniteHeis.heisO_pureTensorO_of_finite ψ θ S T hvac.2.inf x.s y.s x.B y.B f₀ hth u
      (GlobalTheory.VacGood.infPart_latO hu) (hvac.2.lat.2 e he u hu hh) φ

theorem thPair_eq_zero_of_eigen {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χ χ' : (AE D)ˣ →* Circle} {om : Om S T}
    (hW : IsWeilDatumO ψ S T χ χ' om) (v : VolM D T.rank S.rank) (p : GA D S × GA D T) {f g : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) (hg : IsThetaFunO ψ S T g) {a b : ℂ} (ha : om p f = a • f) (hb : om p g = b • g)
    (hb1 : ‖b‖ = 1) (hab : b ≠ a) : thPair v.μ v.𝓕 f g = 0 := by
  have h := GlobalTheory.WeilPairing.thPair_om_eq D ψ S T χ χ' om hW v p f g hf hg
  rw [ha, hb] at h
  have h' := (thPair_smul_smul v.μ v.𝓕 a b f g).symm.trans h
  have hbb : star b * b = 1 := by
    have := Complex.conj_mul' b
    rw [hb1] at this
    simpa using this
  have : (a - b) * thPair v.μ v.𝓕 f g = 0 := by
    linear_combination b * h' - a * thPair v.μ v.𝓕 f g * hbb
  exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hab.symm)

theorem cenFock : ∀ D : D7, CenFock D := by
  intro D ψ θ hθ S T x y hx hy k hk χ
  classical
  obtain ⟨wt, hwt, hfin⟩ := GlobalTheory.T.exists_unit_weight_real_center_action_fock_monomial D ψ θ hθ S T x y hx hy k hk
  obtain ⟨χS, χT, hW⟩ := hk.weil
  obtain ⟨v⟩ := (GlobalTheory.Unf.VolExist.measures_exist D).2.2.1 T.rank S.rank
  set pt := pureTensorO ψ θ S T x.s y.s x.B y.B k.vac with hpt
  have hth : ∀ φ, IsThetaFunO ψ S T (pt φ) := fun φ =>
    GlobalTheory.Chain.InnerSteps.theta_pureTensorO hk.vac.1 hθ x.s x.B y.s y.B hk.vac.2.theta φ
  have heig : ∀ α, ∀ z ∈ GinfC S, z ∈ Subgroup.center (GA D S) →
      k.om (z, 1) (pt (MvPolynomial.monomial α 1)) = wt α z • pt (MvPolynomial.monomial α 1) := by
    intro α z hz hzc
    have := (hwt α z hz hzc).2 _ (isFinComb_single_zero S T)
    rwa [comb_single_zero] at this
  have hL2 : ∀ {g : WO S T → ℂ}, IsThetaFunO ψ S T g → MemLp g 2 (v.μ.restrict v.𝓕) := fun hg =>
    GlobalTheory.Size.memLp_theta hk.vac.1 v.covol.1 v.covol.2.1 hg
  have hint : ∀ {g g' : WO S T → ℂ}, IsThetaFunO ψ S T g → IsThetaFunO ψ S T g' →
      Integrable (fun w => g w * star (g' w)) (v.μ.restrict v.𝓕) := fun hg hg' =>
    GlobalTheory.Size.integrableOn_mul_conj hk.vac.1 v.covol.1 v.covol.2.1 hg hg'
  set A := (hfin χ).toFinset with hA
  have hmem : ∀ α, α ∈ A ↔ ∀ z ∈ GinfC S, z ∈ Subgroup.center (GA D S) → wt α z = χ z := fun α => by
    rw [hA, Set.Finite.mem_toFinset]; rfl
  let mon : A → PolF D T.rank S.rank := fun α => MvPolynomial.monomial α.1 1
  refine ⟨Submodule.span ℂ (Set.range mon), FiniteDimensional.span_of_finite ℂ (Set.finite_range mon), ?_⟩
  intro f hf hlat hχ
  obtain ⟨c, hc⟩ := exists_orth_coeff (v.μ.restrict v.𝓕) f (fun α : A => pt (mon α)) (hL2 hf) (fun α => hL2 (hth _))
  refine ⟨∑ α, c α • mon α, (Submodule.mem_span_range_iff_exists_fun ℂ).2 ⟨c, rfl⟩, ?_⟩
  have hg := GlobalTheory.OrientedHeis.theta_sub hf (hth (∑ α, c α • mon α))
  have hgl := isLatVac_sub ψ S T hlat (isLatVac_pureTensorO hk.vac (∑ α, c α • mon α))
  have hsum : pt (∑ α, c α • mon α) = ∑ α, c α • pt (mon α) := by simp only [map_sum, map_smul]
  have hmono : ∀ β, thPair v.μ v.𝓕 (f - pt (∑ α, c α • mon α)) (pt (MvPolynomial.monomial β 1)) = 0 := by
    intro β
    rw [hsum]
    refine (thPair_sub_sum_left v.μ v.𝓕 Finset.univ c f _ (fun α => pt (mon α)) (hint hf (hth _))
      (fun α => hint (hth _) (hth _))).trans ?_
    by_cases hβ : β ∈ A
    · exact sub_eq_zero.2 (hc ⟨β, hβ⟩)
    · rw [hmem] at hβ
      push_neg at hβ
      obtain ⟨z, hz, hzc, hne⟩ := hβ
      rw [thPair_eq_zero_of_eigen hW v (z, 1) hf (hth _) (hχ z hz hzc) (heig β z hz hzc) (hwt β z hz hzc).1 hne, zero_sub,
        neg_eq_zero]
      refine Finset.sum_eq_zero fun α _ => ?_
      rw [thPair_eq_zero_of_eigen hW v (z, 1) (hth _) (hth _) (heig α.1 z hz hzc) (heig β z hz hzc) (hwt β z hz hzc).1
        (by rw [(hmem α.1).1 α.2 z hz hzc]; exact hne), mul_zero]
  refine sub_eq_zero.1 (GlobalTheory.FockTotal.eq_zero_of_orth_fock D ψ θ hθ S T x y hx hy k.vac hk.vac v _ hg hgl fun Q => ?_)
  have hQ : pt Q = ∑ β ∈ Q.support, MvPolynomial.coeff β Q • pt (MvPolynomial.monomial β 1) := by
    conv_lhs => rw [Q.as_sum]
    rw [map_sum]
    refine Finset.sum_congr rfl fun β _ => ?_
    rw [← map_smul, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  show thPair v.μ v.𝓕 (f - pt (∑ α, c α • mon α)) (pt Q) = 0
  rw [hQ]
  refine (thPair_sum_right v.μ v.𝓕 Q.support (fun β => MvPolynomial.coeff β Q) _
    (fun β => pt (MvPolynomial.monomial β 1)) (fun β => hint hg (hth _))).trans ?_
  exact Finset.sum_eq_zero fun β _ => by rw [hmono, mul_zero]

end GlobalTheory.SeeSaw.CenFockPf
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChainStepTwistedNormSqEqUntwisted
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.LiftRows (Given)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (FinPl IsBase onHalf phiQ rdQ)

open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (ipO Place IsBaseOff)

noncomputable section

namespace GlobalTheory.TwistNorm

theorem level_trivial_eq_ofLocal {E : Type} [Field E] [NumberField E] (Pg : Finset (Pl E)) (r : ℕ) :
    LevelP.triv Pg r ℂ = LevelP.ofLocal (fun _ => ⊥) (fun _ => 1) := by
  have hH : (Subgroup.pi Set.univ fun PP : ↥Pg => (⊥ : Subgroup (GL (Fin r) (kP PP.1)))) = ⊥ := by
    ext g
    simp [Subgroup.mem_pi, funext_iff]
  haveI : Subsingleton (↥(⊥ : Subgroup (G0 Pg r)) →* ℂˣ) :=
    ⟨fun f g => MonoidHom.ext fun y => by rw [Subsingleton.elim y 1, map_one, map_one]⟩
  unfold LevelP.triv LevelP.ofLocal
  congr 1
  · exact hH.symm
  · exact Subsingleton.helim (congrArg (fun H : Subgroup (G0 Pg r) => (↥H →* ℂˣ)) hH.symm) _ _

theorem norm_sq_eq_inner_product {D : D7} {S T : HSp D} (μ : Measure (WO S T)) (𝓕 : Set (WO S T)) (g : WO S T → ℂ) :
    ((nrm2 μ 𝓕 g : ℝ) : ℂ) = ipO μ 𝓕 g g := by
  unfold nrm2 ipO
  rw [← integral_complex_ofReal]
  congr 1
  funext w
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]

theorem chainStep_twisted_normSq_eq_untwisted_mul_localFactors : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)) (f₀ : WO S T → ℂ) (m : Measure (WO S T)) (X : Set (WO S T)), IsBase ψ θ S T sS sT ΛS ΛT f₀ → IsCovolOne (ratL T S) m X → Formalism.L2.DIV.IsFrame βS ΛS → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (r t j t' : ℕ) (hr : r ≤ S.rank), S.rank + t' = T.rank → ∀ (Pg Q : Finset (Pl D.host.E)), Disjoint Pg Q → (∀ PP ∈ Q, ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ (χ : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (χj ξ ξ' : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (f f' : WO S T → ℂ), IsStepVecOf ψ θ S T sS sT ΛS ΛT βS βT (Lev.datY S.rank r t j hr Pg Q (LevelP.triv _ _ _) χ ξ Lev.Frm.B) χj Q ξ f₀ f → IsStepVecOf ψ θ S T sS sT ΛS ΛT βS βT (Lev.datY S.rank r t j hr Pg ∅ (LevelP.triv _ _ _) χ ξ' Lev.Frm.B) χj ∅ ξ' f₀ f' → nrm2 m X f = nrm2 m X f' * ∏ PP ∈ Q, (zinv PP 0 r * ((Ideal.absNorm PP.asIdeal : ℝ) ^ (r * (T.rank - r)))⁻¹) := by
  classical
  intro D ψ θ S T sS sT ΛS ΛT βS βT f₀ m X hB hC hFS hFT r t j t' hr ht Pg Q hdisj hQ2 χ χj ξ ξ' f f' hf hf'
  have hP : (Lev.datY S.rank r t j hr Pg Q (LevelP.triv _ _ _) χ ξ Lev.Frm.B).P =
      LevelP.ofLocal (Pg := Pg) (r := r) (LL := ℂ) (fun _ => ⊥) (fun _ => 1) := by
    show (if Lev.Frm.B = Lev.Frm.B then LevelP.triv Pg r ℂ else (LevelP.triv Pg r ℂ).conj) = _
    rw [if_pos rfl]
    exact level_trivial_eq_ofLocal Pg r
  have hP' : (Lev.datY S.rank r t j hr Pg ∅ (LevelP.triv _ _ _) χ ξ' Lev.Frm.B).P =
      LevelP.ofLocal (Pg := Pg) (r := r) (LL := ℂ) (fun _ => ⊥) (fun _ => 1) := by
    show (if Lev.Frm.B = Lev.Frm.B then LevelP.triv Pg r ℂ else (LevelP.triv Pg r ℂ).conj) = _
    rw [if_pos rfl]
    exact level_trivial_eq_ofLocal Pg r
  obtain ⟨⟨x, hx⟩, hall⟩ := GlobalTheory.StepVec.stepVecLocal D ψ θ S T sS sT ΛS ΛT βS βT _ χj Q ξ f₀ f m X t' ht _ _ hP hB hC
    hFS hFT hdisj hf
  have hall' := (GlobalTheory.StepVec.stepVecLocal D ψ θ S T sS sT ΛS ΛT βS βT _ χj ∅ ξ' f₀ f' m X t' ht _ _ hP' hB hC hFS hFT
    (Finset.disjoint_empty_right _) hf').2
  obtain ⟨hvac, e, ⟨⟨es, hes, rfl⟩, hce⟩, -⟩ := hf
  have hes' : ∀ PP ∈ Pg ∪ Q, Formalism.L2.NTheta.IsIdemAt (es PP) PP := hes
  have hce' : (∑ PP ∈ Pg ∪ Q, es PP) * cA D (∑ PP ∈ Pg ∪ Q, es PP) = 0 := hce
  have hsum := GlobalTheory.SplitIdemDict.idem_dictionary D
  choose vA φA hφA hprA using fun i : ↥(Pg ∪ Q) => hsum.1 (es i.1) i.1 (hes' i.1 i.2)
  have hunder : ∀ i : ↥(Pg ∪ Q), (i.1).asIdeal.under (𝓞 D.host.F) = (vA i).asIdeal := fun i =>
    (hsum.2 _ _ _ (hprA i)).1
  have hcross := GlobalTheory.PlaceDatum.cross_eq_zero (R := AE D) GlobalTheory.PlaceDatum.isUnit_natCast (cA D) es (Pg ∪ Q)
    (fun i hi => (hes' i hi).1.1) hce'
  have hinj : Function.Injective vA := by
    intro i j hij
    have h1 := (hφA i).2.1
    have h2 := (hφA j).2.1
    rw [hij] at h1
    have h3 := GlobalTheory.PlaceDatum.idempotent_eq_of_orthogonal_decomp (hes' i.1 i.2).1.1 (hes' i.1 i.2).1.2.1 (hes' j.1 j.2).1.1
      (hes' j.1 j.2).1.2.1 (h1.trans h2.symm) (hcross _ i.2 _ j.2) (hcross _ j.2 _ i.2)
    exact Subtype.ext (GlobalTheory.StepVec.prime_eq_of_idem (hes' i.1 i.2) (h3 ▸ hes' j.1 j.2))

  obtain ⟨x', hx'l, hx'r⟩ : ∃ x' : Place D → WO S T → ℂ, (∀ τ, x' (.inr τ) = f₀) ∧
      ∀ v, x' (.inl v) = if ∃ PP ∈ Pg, PP.asIdeal.under (𝓞 D.host.F) = v.asIdeal then x (.inl v) else f₀ :=
    ⟨Sum.elim (fun v => if ∃ PP ∈ Pg, PP.asIdeal.under (𝓞 D.host.F) = v.asIdeal then x (.inl v) else f₀) fun _ => f₀,
      fun _ => rfl, fun _ => rfl⟩
  have hpure' := hall' x' ⟨⟨hx'l, fun v hv => by
      rw [hx'r, if_neg]
      rintro ⟨PP, h1, h2⟩
      exact hv PP (Finset.mem_union_left _ h1) h2⟩,
    fun v φ e' he' mu => ⟨fun PP hpp hmu J lam hJ => by
      have h := (hx.2 v φ e' he' mu).1 PP hpp hmu J lam hJ
      rw [hx'r, if_pos ⟨PP.1, PP.2, (hsum.2 v φ PP.1 hpp).1⟩]
      exact h, fun PP hq => by simp at hq⟩⟩
  have hpure := hall x hx
  obtain ⟨hfin, hxx⟩ := GlobalTheory.PlaceTensor.PureScalar.ip_pure_eq_finprod D ψ θ S T sS sT ΛS ΛT f₀ m X hB hC x x f f
    hpure hpure
  obtain ⟨-, hxx'⟩ := GlobalTheory.PlaceTensor.PureScalar.ip_pure_eq_finprod D ψ θ S T sS sT ΛS ΛT f₀ m X hB hC x' x' f' f'
    hpure' hpure'
  have h0 : ipO m X f₀ f₀ = 1 := by
    rw [← norm_sq_eq_inner_product, hvac.2.norm.2 (m, X) hC]
    simp

  let iq : ↥Q → ↥(Pg ∪ Q) := fun i => ⟨i.1, Finset.mem_union_right _ i.2⟩
  let U : Finset (Place D) := Q.attach.image fun i => (Sum.inl (vA (iq i)) : Place D)
  have hnotPg : ∀ i : ↥Q, ¬ ∃ PP ∈ Pg, PP.asIdeal.under (𝓞 D.host.F) = (vA (iq i)).asIdeal := by
    rintro i ⟨PP, hPP, hu⟩
    have h1 : vA ⟨PP, Finset.mem_union_left _ hPP⟩ = vA (iq i) := HeightOneSpectrum.ext ((hunder _).symm.trans hu)
    have h2 : PP = i.1 := congrArg Subtype.val (hinj h1)
    exact Finset.disjoint_left.1 hdisj hPP (by rw [h2]; exact i.2)
  have hpt : ∀ p, ipO m X (x p) (x p) =
      ipO m X (x' p) (x' p) * (if p ∈ U then ipO m X (x p) (x p) else 1) := by
    intro p
    by_cases hp : p ∈ U
    · rw [if_pos hp]
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hp
      rw [hx'r, if_neg (hnotPg i), h0, one_mul]
    · rw [if_neg hp, mul_one]
      rcases p with v | τ
      · rw [hx'r]
        by_cases hv : ∃ PP ∈ Pg, PP.asIdeal.under (𝓞 D.host.F) = v.asIdeal
        · rw [if_pos hv]
        · rw [if_neg hv]
          have hxv : x (.inl v) = f₀ := hx.1.2 v fun PP hPP hu => by
            rcases Finset.mem_union.1 hPP with h | h
            · exact hv ⟨PP, h, hu⟩
            · exact hp (Finset.mem_image.2 ⟨⟨PP, h⟩, Finset.mem_attach _ _,
                congrArg Sum.inl (HeightOneSpectrum.ext ((hunder _).symm.trans hu))⟩)
          rw [hxv]
      · rw [hx'l, hx.1.1 τ]
  let s0 : Finset (Place D) := hfin.toFinset ∪ U
  have hA : ∏ᶠ p, ipO m X (x p) (x p) = ∏ p ∈ s0, ipO m X (x p) (x p) :=
    finprod_eq_prod_of_mulSupport_subset _ fun p hp => Finset.mem_union_left _ (hfin.mem_toFinset.2 hp)
  have hA' : ∏ᶠ p, ipO m X (x' p) (x' p) = ∏ p ∈ s0, ipO m X (x' p) (x' p) := by
    refine finprod_eq_prod_of_mulSupport_subset _ fun p hp => ?_
    by_cases hU : p ∈ U
    · exact Finset.mem_union_right _ hU
    · refine Finset.mem_union_left _ (hfin.mem_toFinset.2 ?_)
      have h := hpt p
      rw [if_neg hU, mul_one] at h
      rw [Function.mem_mulSupport] at hp ⊢
      rwa [h]
  have hsplit : ∏ p ∈ s0, ipO m X (x p) (x p) =
      (∏ p ∈ s0, ipO m X (x' p) (x' p)) * ∏ p ∈ U, ipO m X (x p) (x p) := by
    rw [Finset.prod_congr rfl fun p _ => hpt p, Finset.prod_mul_distrib, Finset.prod_ite_mem,
      Finset.inter_eq_right.2 Finset.subset_union_right]
  have hU : ∏ p ∈ U, ipO m X (x p) (x p) = ∏ i ∈ Q.attach, ipO m X (x (.inl (vA (iq i)))) (x (.inl (vA (iq i)))) := by
    refine Finset.prod_image fun i _ j _ h => ?_
    have h1 := hinj (Sum.inl_injective h)
    have h2 : (iq i).1 = (iq j).1 := congrArg Subtype.val h1
    exact Subtype.ext h2
  have hloc : ∀ i : ↥Q, ipO m X (x (.inl (vA (iq i)))) (x (.inl (vA (iq i)))) =
      ((zinv i.1 0 r * ((Ideal.absNorm i.1.asIdeal : ℝ) ^ (r * (T.rank - r)))⁻¹ : ℝ) : ℂ) := by
    intro i
    obtain ⟨mu, hmu⟩ := (GlobalTheory.PlaceRed.red_dict D (vA (iq i)) (φA (iq i)) i.1 (hprA (iq i))).2 (ξ i.1)⁻¹
    have hθ := (hx.2 (vA (iq i)) (φA (iq i)) (es i.1) (hφA (iq i)) mu).2 i.1 i.2 (hprA (iq i)) hmu
    rw [← norm_sq_eq_inner_product, GlobalTheory.T.normSq_thetaLocalDatum_at_twistPlace D ψ θ S T sS sT ΛS ΛT βS βT f₀ m X hB hC hFS hFT i.1 (vA (iq i)) (φA (iq i)) (es i.1)
      (hφA (iq i)) (hprA (iq i)) (GlobalTheory.T.homLatticeIdeal_isUnit_splitPlace D i.1 (hQ2 i.1 i.2) (vA (iq i)) (φA (iq i)) (hprA (iq i))) r hr (by omega)
      (ξ i.1)⁻¹ mu hmu _ hθ]
  apply Complex.ofReal_injective
  rw [Complex.ofReal_mul, Complex.ofReal_prod, norm_sq_eq_inner_product, norm_sq_eq_inner_product, hxx, hxx', hA, hA', hsplit, hU,
    Finset.prod_congr rfl fun i _ => hloc i,
    Finset.prod_attach Q fun PP => ((zinv PP 0 r * ((Ideal.absNorm PP.asIdeal : ℝ) ^ (r * (T.rank - r)))⁻¹ : ℝ) : ℂ)]

end GlobalTheory.TwistNorm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DegenerateCollisionRowBoundAtParams
section
open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Core.Deg

theorem rowsDeg_at_record : ∀ CT cH cV Ca C2 Ch c C : ℝ, 1 ≤ c → CT ≤ c → |cH| + 2 ≤ c → |cV| + 2 ≤ c → 0 ≤ Ch → c ≤ C → 4 + (c ^ 2 + 2 * max (Ch - c) 0) * (6 * c + 2) ≤ C → 2 * C2 ≤ C → |Ca| ≤ C → ∀ (D : D7) (large₂ : SizeData₂ D) (u : D.what₂.Word) (T : TermTie D) (Z : LoopTie D large₂ T u u 1) (C' Cl Cg cb Cu cT C0 : ℝ), 3 * |C2| ≤ C' → Cnt.Hyp D large₂ u u C' Cl Cg cb Cu cT CT C0 1 → UnitaryVolumeMass.MeanFlagPairCount D large₂ u u C' Cl Cg cb Cu cT CT C0 1 3 c → UnitaryVolumeMass.stHH D large₂ u u C' Cl Cg cb Cu cT CT C0 1 cH → UnitaryVolumeMass.stVol D large₂ T u u 1 Z C' Cl Cg cb Cu cT CT C0 1 cV → AmpAt D large₂ C' Cl Cg cb Cu cT CT C0 (9 * c + 3) Ca C2 Ch 1 → SmallAt D large₂ C' Cl Cg cb Cu cT CT C0 1 → BridgeLemma.TermPtsTie T Z → @BridgeLemma.LatticeDeterminantFactorization D T u u → BridgeLemma₂.wordPairEntriesInLattice T u u → BridgeLemma.RowsDeg T Z C := by
  intro CT cH cV Ca C2 Ch c C k2 hCT k3 k4 hCh hcC hCsq1 hC2 hCa D large₂ u T Z C' Cl Cg cb Cu cT C0 h3C hH hC3 hHH hV hA hS hTP hG0 hE
  have hc0 : 0 ≤ c := by linarith
  have hC1 : 1 ≤ C := k2.trans hcC
  have hCsq : 4 + (c ^ 2 + 2 * max (Ch - c) 0) * (6 * c + 2) ≤ C ^ 2 := by nlinarith
  have hHHc : UnitaryVolumeMass.stHH D large₂ u u C' Cl Cg cb Cu cT CT C0 1 c :=
    BridgeLemma₂.rows_stHH_mono (by linarith [le_abs_self cH]) (by linarith [neg_abs_le cH]) hHH
  have hK := BridgeLemma₂.rows_KBound_of Z hH hHHc k2 hCT
  have hr0 : (0 : ℝ) ≤ D.R.rS := by positivity
  have hm2 : (2 : ℝ) ≤ D.R.m := by rw [BridgeLemma₂.rows_m_cast]; linarith
  have hf1 : (1 : ℝ) ≤ D.R.f := by exact_mod_cast BridgeLemma₂.rows_f_pos D
  have hL1 : 1 ≤ large₂.sc.L := BridgeLemma.d_one_le_L D large₂
  have hkm : (D.R.m : ℝ) + 3 ≤ D.R.k := by exact_mod_cast D.R.m_add_three_le_k
  have hk5 : C' * (D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L ≤ D.R.k := hH.1.1.2.1
  have ha2 : |C2| * (D.R.m : ℝ) ^ 2 + |C2| * (D.R.m : ℝ) ^ 4 * 2 ≤ D.R.k := by
    refine le_trans ?_ hk5
    have e1 : (D.R.m : ℝ) ^ 2 ≤ (D.R.m : ℝ) ^ 5 := pow_le_pow_right₀ (by linarith) (by norm_num)
    have e4 : (D.R.m : ℝ) ^ 4 ≤ (D.R.m : ℝ) ^ 5 := pow_le_pow_right₀ (by linarith) (by norm_num)
    have h5 : 0 ≤ (D.R.m : ℝ) ^ 5 := by positivity
    have e2 : (D.R.m : ℝ) ^ 5 ≤ (D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L := by
      nlinarith [mul_nonneg h5 (by linarith : 0 ≤ (D.R.f : ℝ) - 1),
        mul_nonneg (mul_nonneg h5 (by linarith : 0 ≤ (D.R.f : ℝ))) (by linarith : 0 ≤ large₂.sc.L - 1)]
    have hab := abs_nonneg C2
    have hP : 0 ≤ (D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L := by linarith
    calc |C2| * (D.R.m : ℝ) ^ 2 + |C2| * (D.R.m : ℝ) ^ 4 * 2
        = |C2| * ((D.R.m : ℝ) ^ 2 + 2 * (D.R.m : ℝ) ^ 4) := by ring
      _ ≤ |C2| * (3 * ((D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L)) :=
          mul_le_mul_of_nonneg_left (by linarith) hab
      _ = (3 * |C2|) * ((D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L) := by ring
      _ ≤ C' * ((D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L) := mul_le_mul_of_nonneg_right h3C hP
      _ = C' * (D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L := by ring
  obtain ⟨a, hadef⟩ : ∃ a : ℝ, a = 4 * (c * D.R.k) + 4 * BridgeLemma₂.pairCountExponent D c D.R.k +
    4 * (c * (D.R.rS : ℝ) ^ 2) + (|C2| * (D.R.m : ℝ) ^ 2 + |C2| * (D.R.m : ℝ) ^ 4 * 2) / 2 +
    12 * ((D.R.rS : ℝ) + 1) ^ 2 := ⟨_, rfl⟩
  have ha0 : 0 ≤ a := by
    rw [hadef]
    have := BridgeLemma₂.pairCountExponent_nonneg D hc0 D.R.k
    positivity
  have hqb := BridgeLemma₂.rows_q_bound (m := D.R.m) (k := D.R.k) (r := D.R.rS) (c := c)
    (cf := Cnt.cF D.R.f) (a2 := |C2| * (D.R.m : ℝ) ^ 2 + |C2| * (D.R.m : ℝ) ^ 4 * 2)
    (BridgeLemma₂.rows_m_cast _) hr0 hkm hc0 (BridgeLemma₂.rows_cF_le hH) ha2
  have hqb' : ((D.R.rS : ℝ) + 1) * a + 1 ≤ (9 * c + 3) * D.R.k * (D.R.m : ℝ) ^ 2 := by
    rw [hadef]; unfold BridgeLemma₂.pairCountExponent; exact hqb
  have hra0 : 0 ≤ ((D.R.rS : ℝ) + 1) * a := by positivity
  have hyp : BridgeLemma₂.rows_Hyps Z C' Cl Cg cb Cu cT CT C0 1 c (9 * c + 3) Ca C2 Ch 1 1
      ⌈((D.R.rS : ℝ) + 1) * a⌉₊ :=
    { hH := hH
      hC3 := hC3
      hHH := hHHc
      hV := BridgeLemma₂.rows_stVol_mono _ (by linarith [le_abs_self cV]) (by linarith [neg_abs_le cV]) hV
      hDEC := hA.2.2
      ha := hS.1
      hb := hS.2.1
      hp := hA.1
      hpp := hA.2.1
      h6 := hS.2.2.1
      hδ := zero_le_one
      hThA := BridgeLemma.word_theorem_a_admissible D u u
      hT := hTP
      hG0 := hG0
      hE := hE
      hc := hc0
      hCh := hCh
      hdim := BridgeLemma₂.rows_dim_pos Z hH.1 (hS.2.2.2.2 hH.1 u)
      hq := by linarith [(Nat.ceil_lt_add_one hra0).le] }
  refine BridgeLemma₂.rows_RowsDeg_record _ hyp hK k2 hcC hC1 hCsq hC2 hCa ?_
  rw [le_div_iff₀ (by positivity)]
  have h1 := Nat.le_ceil (((D.R.rS : ℝ) + 1) * a)
  have h2 : (C2 * (D.R.m : ℝ) ^ 2 + C2 * (D.R.m : ℝ) ^ 4 * 2) / 2 ≤
      (|C2| * (D.R.m : ℝ) ^ 2 + |C2| * (D.R.m : ℝ) ^ 4 * 2) / 2 := by
    have := le_abs_self C2
    gcongr
  calc _ ≤ a * ((D.R.rS : ℝ) + 1) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        rw [hadef]; linarith
    _ = ((D.R.rS : ℝ) + 1) * a := by ring
    _ ≤ _ := h1

end GlobalTheory.Core.Deg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIntegralAdelePrescribedResiduesAndConjStatement
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.DIV Formalism.L2.SG.InstExistsPf GlobalTheory.FlagBasis
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integralAdele_prescribed_residues_and_conj : ∀ (D : D7) (Pg : Finset (Pl D.host.E)), (∀ PP ∈ Pg, ∀ PP' ∈ Pg, ¬ Formalism.IndefR.Lev.IsConjPl (D := D) PP PP') → ∀ u u' : ∀ PP : Pl D.host.E, kP PP, ∃ s : Formalism.L2.Herm.intAf D.host.F D.host.E, ∀ PP ∈ Pg, resS D.host.F PP s = u PP ∧ resS D.host.F PP (sigInt (instOf D) s) = u' PP := by
  first | exact @GlobalTheory.ConjResidueSurj.exists_res_and_conj | exact GlobalTheory.ConjResidueSurj.exists_res_and_conj | (intros; apply GlobalTheory.ConjResidueSurj.exists_res_and_conj <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsLatticeFrameLiftingSpanningVectorsModStatement
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.DIV Formalism.L2.SG.InstExistsPf GlobalTheory.FlagBasis
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_latticeFrame_lifting_spanning_vectors_mod : ∀ (D : D7) (g : ℕ), g ≠ 0 → ∀ b : ℕ → VA (instOf D), (∀ j, b j ∈ (instOf D).Lf) → (∀ y ∈ (instOf D).Lf, InMod (instOf D) g (Set.range fun j : Fin (instOf D).n => b j.val) y) → ∃ β, IsLiftFrame (instOf D) g b β := by
  first | exact @GlobalTheory.LiftFrameMod.exists_isLiftFrame | exact GlobalTheory.LiftFrameMod.exists_isLiftFrame | (intros; apply GlobalTheory.LiftFrameMod.exists_isLiftFrame <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsLinearMapVaryPureTensorFactorSplitPlaceStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_linearMap_vary_pureTensor_factor_split_place : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : OmT S T) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (f₀ : WO S T → ℂ) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsWeilDatumO ψ S T χS χT om → IsInfFam θ → IsBase ψ θ S T sS sT ΛS ΛT f₀ → IsCovolOne (ratL T S) μ 𝓕 → ∀ (x : Place D → WO S T → ℂ) (f : WO S T → ℂ), IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ x f → ∀ (v : FinPl D) (φ : SplitProj D v) (e : AE D), IsIdemOf φ e → ∀ (BS : GL (Fin S.rank) (Fv D.host.F v)) (BT : GL (Fin T.rank) (Fv D.host.F v)) (Φ₀ : GlobalTheory.SplitWeil.SB (Matrix (Fin T.rank) (Fin S.rank) (Fv D.host.F v))), ∀ Tm, IsPlaceModel ψ (symplO S T) (heisO ψ S T) e (latO S T ΛS ΛT fun _ => True) 1 f₀ Tm → x (.inl v) = Tm (onHalf φ S T BS BT e Φ₀.1) → ∃ T₀ : GlobalTheory.SplitWeil.SB (Matrix (Fin T.rank) (Fin S.rank) (Fv D.host.F v)) →ₗ[ℂ] (WO S T → ℂ), T₀ Φ₀ = f ∧ (∀ u, ∃ x' : Place D → WO S T → ℂ, (∀ p, p ≠ .inl v → x' p = x p) ∧ x' (.inl v) = Tm (onHalf φ S T BS BT e u.1) ∧ IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ x' (T₀ u)) ∧ ∀ g h, gAt S (.inl v) g = g → gAt T (.inl v) h = h → ∀ a b, IsDetAt e S g a → IsDetAt e T h b → ∀ u u' : GlobalTheory.SplitWeil.SB (Matrix (Fin T.rank) (Fin S.rank) (Fv D.host.F v)), u'.1 = linOm v (grpCo φ S BS g) (grpCo φ T BT h) u.1 → om (g, h) (T₀ u) = ((splitFacO χS χT a b : Circle) : ℂ) • T₀ u' := by
  first | exact @GlobalTheory.VarySplitFactor.exists_linearMap_pure | exact GlobalTheory.VarySplitFactor.exists_linearMap_pure | (intros; apply GlobalTheory.VarySplitFactor.exists_linearMap_pure <;> assumption)
end

