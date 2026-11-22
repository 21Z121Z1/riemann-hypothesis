import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.L2UnitaryRepresentationData
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.WeilRepresentationContinuous
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0215
import Formalism.PeriodIntegrals.Bundle0022
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PseudoCoefficientSeparation
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.RealPlaceAnalysis.Bundle0003
import Formalism.RealPlaceAnalysis.Bundle0002
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0220
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0165
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0176
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0097
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0005
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0129
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SumDiagOrderEqOfIntegralTranslateIndicatorRelati
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0149

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealPlaceGroupsActUnitarilyWeaklyOnTheta
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open Formalism.IndefR.Mult (DSModel dualPar parA parB)
open Formalism.MainNotions.SchurIrreducible (AdmGK ARi ARiiiUp ARiiiDown ARiiiLine DiscreteSeriesBlattner admQ5)
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction hiding Mat
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix (SignCompat plainMat barMat)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (fockIp)
open GlobalTheory.Chain (signed)
open GlobalTheory.Chain.RealIt (LPol locS locT IsPolyIso)
open MeasureTheory Matrix
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ArchRec

noncomputable section

namespace GlobalTheory.ThetaL2InnerProduct

open GlobalTheory.OrientedHeis GlobalTheory.Size Filter
open scoped Topology

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
  {ω : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} {μ : Measure (WO S T)} {𝓕 : Set (WO S T)}

def thetaSpace (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) : Submodule ℂ (WO S T → ℂ) where
  carrier := {f | IsThetaFunO ψ S T f}
  add_mem' := theta_add
  zero_mem' := theta_zero
  smul_mem' := fun a _ hf => theta_smul a hf

theorem ipTh_eq (f f' : WO S T → ℂ) : ipTh μ 𝓕 f f' = GlobalTheory.Ker.ipO μ 𝓕 f f' := rfl

theorem bound_near (hω : IsWeilDatumO ψ S T χS χT ω) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
    (p₀ : GA D S × GA D T) : ∃ C : ℝ, ∀ᶠ p in 𝓝 p₀, ∀ w, ‖ω p f w‖ ≤ C := by
  obtain ⟨K, hK, hKγ⟩ := (GlobalTheory.AdelicMatrixLattice.lattice D T S).2.2.2.2.2
  have hcont : Continuous fun q : (GA D S × GA D T) × WO S T => ω q.1 f q.2 :=
    GlobalTheory.ThetaJointCont.continuous_om_oriented hω hf
  have hc0 : ContinuousOn (fun w : WO S T => ω p₀ f w) K :=
    (hcont.comp (by fun_prop : Continuous fun w : WO S T => (p₀, w))).continuousOn
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hc0
  refine ⟨M + 1, ?_⟩
  have hev : ∀ᶠ p in 𝓝 p₀, ∀ y ∈ K, ‖ω p f y‖ < M + 1 := by
    refine hK.eventually_forall_of_forall_eventually fun y hy => ?_
    have hlt : ‖ω p₀ f y‖ < M + 1 := lt_of_le_of_lt (hM y hy) (lt_add_one M)
    exact hcont.norm.continuousAt.eventually_lt continuousAt_const hlt
  filter_upwards [hev] with p hp w
  obtain ⟨γ, hγ, hγK⟩ := hKγ w
  rw [← theta_norm_periodic hω.std (hω.om_pres p f hf) γ hγ w]
  exact (hp _ hγK).le

theorem continuousOn_ip (hω : IsWeilDatumO ψ S T χS χT ω) (hμ : μ.IsAddHaarMeasure)
    (h𝓕 : IsAddFundamentalDomain (ratL T S) 𝓕 μ) {X : Type} [TopologicalSpace X] [FirstCountableTopology X]
    {γ : X → GA D S × GA D T} {U : Set X} (hγ : ContinuousOn γ U) {F E : WO S T → ℂ}
    (hF : IsThetaFunO ψ S T F) (hE : IsThetaFunO ψ S T E) :
    ContinuousOn (fun x => ipTh μ 𝓕 (ω (γ x) F) E) U := by
  intro x₀ hx₀
  obtain ⟨C, hC⟩ := bound_near hω hF (γ x₀)
  obtain ⟨CE, hCE⟩ := theta_bounded hω.std hE
  have hfin : μ 𝓕 ≠ ⊤ := (measure_dom hμ h𝓕).2
  haveI : IsFiniteMeasure (μ.restrict 𝓕) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hfin.lt_top⟩
  unfold ipTh
  refine continuousWithinAt_of_dominated (bound := fun _ => C * CE) ?_ ?_ (integrable_const _) ?_
  · refine Filter.Eventually.of_forall fun x => ?_
    exact (integrableOn_mul_conj hω.std hμ h𝓕 (hω.om_pres (γ x) F hF) hE).aestronglyMeasurable
  · have ht : Tendsto γ (𝓝[U] x₀) (𝓝 (γ x₀)) := hγ x₀ hx₀
    filter_upwards [ht.eventually hC] with x hx
    refine Filter.Eventually.of_forall fun w => ?_
    rw [norm_mul, norm_star]
    exact mul_le_mul (hx w) (hCE w) (norm_nonneg _) ((norm_nonneg _).trans (hx w))
  · refine Filter.Eventually.of_forall fun w => ?_
    exact ((hω.om_cont F hF w).continuousAt.comp_continuousWithinAt (hγ x₀ hx₀)).mul continuousWithinAt_const

theorem weaklyContinuous_unitaryAction_of_realUnitaryHom (hω : IsWeilDatumO ψ S T χS χT ω) (hμ : μ.IsAddHaarMeasure)
    (h𝓕 : IsAddFundamentalDomain (ratL T S) 𝓕 μ) {n : ℕ} {ι : Type} (G : Mn n) (γ : Mn n → GA D S × GA D T)
    (h1 : γ 1 = 1) (hmul : ∀ g ∈ Formalism.QuantumDeterminants.UH G, ∀ g' ∈ Formalism.QuantumDeterminants.UH G, γ (g * g') = γ g * γ g')
    (hc : ContinuousOn γ (Formalism.QuantumDeterminants.UH G)) (pt : MvPolynomial ι ℂ →ₗ[ℂ] (WO S T → ℂ))
    (hpt : ∀ P, IsThetaFunO ψ S T (pt P))
    (hd : ∀ X : Mn n, Xᴴ * G + G * X = 0 → ∀ P, ∃ F', DerAll ψ ω (fun t => γ (NormedSpace.exp (t • X))) (pt P) F') :
    L2UnitaryRepresentationData G (fun g F => ω (γ g) F) pt (ipTh μ 𝓕) (thetaSpace ψ S T) where
  mem := hpt
  pt_lin := fun z P Q => by rw [map_add, map_smul]
  ip_lin := fun z F hF F' hF' E hE => by
    rw [ipTh_eq, ipTh_eq, ipTh_eq, ipO_add_left hω.std hμ h𝓕 (theta_smul z hF) hF' hE, ipO_smul_left]
  ip_symm := fun F _ E _ => by rw [ipTh_eq, ipTh_eq, ipO_conj]
  ip_pos := fun F hF hne => by
    have hc : Continuous F := by
      have h1 : Continuous fun w : WO S T => ω 1 F w :=
        (GlobalTheory.ThetaJointCont.continuous_om_oriented hω hF).comp
          (by fun_prop : Continuous fun w : WO S T => ((1 : GA D S × GA D T), w))
      simpa only [map_one, Module.End.one_apply] using h1
    have h0 : GlobalTheory.Ker.ipO μ 𝓕 F F ≠ 0 := fun h => hne ((ipO_self_eq_zero_iff hω.std hμ h𝓕 hF).1 h)
    rw [ipO_self, sqNormIntegralFundamentalDomain_eq_l2Norm_sq μ 𝓕 hc] at h0
    rw [ipTh_eq, ipO_self, sqNormIntegralFundamentalDomain_eq_l2Norm_sq μ 𝓕 hc, Complex.ofReal_re]
    exact lt_of_le_of_ne (sq_nonneg _) (fun h => h0 (by rw [← h]; simp))
  stable := fun g _ F hF => hω.om_pres _ F hF
  lin := fun g _ z F _ F' _ => by simp only [map_add, map_smul]
  one := fun F _ => by
    show ω (γ 1) F = F
    rw [h1, map_one]
    rfl
  mul := fun g hg g' hg' F _ => by
    show ω (γ (g * g')) F = ω (γ g) (ω (γ g') F)
    rw [hmul g hg g' hg', map_mul]
    rfl
  unit := fun g _ F hF E hE => by
    show ipTh μ 𝓕 (ω (γ g) F) (ω (γ g) E) = ipTh μ 𝓕 F E
    rw [ipTh_eq, ipTh_eq, ipO_om hω hμ h𝓕 hF hE]
  cont := fun F hF E hE => by
    haveI : FirstCountableTopology (Mn n) :=
      inferInstanceAs (FirstCountableTopology (Fin n → Fin n → ℂ))
    exact continuousOn_ip hω hμ h𝓕 hc hF hE
  der := fun X hX P P' hPP' E hE => by
    obtain ⟨F', hF'1, hF'2⟩ := hd X hX P
    have heq : F' = pt P' := by
      funext z
      have hz := hF'1 1 z
      simp only [one_mul, map_one, Module.End.one_apply] at hz
      exact hz.unique (hPP' z)
    have hder := hF'2 μ 𝓕 hμ h𝓕 E hE
    rw [heq] at hder
    exact hder

theorem exists_l2_unitary_theta_of_fundamentalDomain : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (ω : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (τ : D.what₂.Tau), IsInfFam θ → IsWeilDatumO ψ S T χS χT ω → ∀ (frS : Mn S.rank) (εS : Fin S.rank → Bool) (frT : Mn T.rank) (εT : Fin T.rank → Bool) (aS aT : ℚ) (pt : LPol T.rank S.rank →ₗ[ℂ] (WO S T → ℂ)), (∀ P, IsThetaFunO ψ S T (pt P)) → LieAt ψ θ τ ω εS frS εT frT aS aT pt → ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL T S) 𝓕 μ → ∃ Θ, L2UnitaryRepresentationData (gramAt D S τ) (actSrc θ ω τ) pt (ipTh μ 𝓕) Θ ∧ L2UnitaryRepresentationData (gramAt D T τ) (actTgt θ ω τ) pt (ipTh μ 𝓕) Θ := by
  intro D ψ θ S T χS χT ω τ hθ hω frS εS frT εT aS aT pt hpt hL μ 𝓕 hμ h𝓕
  refine ⟨thetaSpace ψ S T, ?_, ?_⟩
  · have hcS := GlobalTheory.PointAtPlaceHom.continuousOn_atTau hθ S τ
    exact weaklyContinuous_unitaryAction_of_realUnitaryHom hω hμ h𝓕 (gramAt D S τ) (fun g => (atTau θ S τ g, (1 : GA D T)))
      (by rw [GlobalTheory.PointAtPlaceHom.atTau_one hθ S τ]; rfl)
      (fun g hg g' hg' => by
        rw [GlobalTheory.PointAtPlaceHom.atTau_mul hθ S τ hg hg', Prod.mk_mul_mk, one_mul])
      (by fun_prop) pt hpt (fun X hX P => ⟨_, hL.1 X hX P⟩)
  · have hcT := GlobalTheory.PointAtPlaceHom.continuousOn_atTau hθ T τ
    exact weaklyContinuous_unitaryAction_of_realUnitaryHom hω hμ h𝓕 (gramAt D T τ) (fun h => ((1 : GA D S), atTau θ T τ h))
      (by rw [GlobalTheory.PointAtPlaceHom.atTau_one hθ T τ]; rfl)
      (fun h hh h' hh' => by
        rw [GlobalTheory.PointAtPlaceHom.atTau_mul hθ T τ hh hh', Prod.mk_mul_mk, one_mul])
      (by fun_prop) pt hpt (fun Y hY P => ⟨_, hL.2 Y hY P⟩)

end GlobalTheory.ThetaL2InnerProduct

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RefineIsotropicFlag
section
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace
open PI.DSInfCharCap (actU Egl)
open GlobalTheory.RealInd.Stages Finset GlobalTheory.FlagMeas Formalism.REAL

namespace GlobalTheory.RealInd.Stages

theorem exists_chain_between {K V : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] :
    ∀ (k : ℕ) (A B : Submodule K V), A ≤ B → Module.finrank K B = Module.finrank K A + k →
      ∃ c : ℕ → Submodule K V, Monotone c ∧ c 0 = A ∧ (∀ t, k ≤ t → c t = B) ∧
        ∀ t ≤ k, Module.finrank K (c t) = Module.finrank K A + t := by
  intro k
  induction k with
  | zero =>
    intro A B hAB h
    have hE : A = B := Submodule.eq_of_le_of_finrank_eq hAB (by omega)
    exact ⟨fun _ => A, fun _ _ _ => le_rfl, rfl, fun _ _ => hE, fun t ht => by
      have : t = 0 := by omega
      subst this; simp⟩
  | succ k ih =>
    intro A B hAB h
    have hne : A ≠ B := by
      rintro rfl; omega
    obtain ⟨v, hvB, hvA⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hAB hne)
    have hA' : Module.finrank K (A ⊔ Submodule.span K {v} : Submodule K V) = Module.finrank K A + 1 :=
      Submodule.finrank_sup_span_singleton hvA
    have hle : (A ⊔ Submodule.span K {v} : Submodule K V) ≤ B :=
      sup_le hAB ((Submodule.span_singleton_le_iff_mem v B).2 hvB)
    obtain ⟨c, hc, hc0, hcB, hcr⟩ := ih _ B hle (by omega)
    refine ⟨fun t => match t with | 0 => A | s + 1 => c s, ?_, rfl, ?_, ?_⟩
    · refine monotone_nat_of_le_succ fun t => ?_
      rcases t with _ | s
      · show A ≤ c 0
        rw [hc0]; exact le_sup_left
      · show c s ≤ c (s + 1)
        exact hc (Nat.le_succ s)
    · intro t ht
      obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
      exact hcB s (by omega)
    · intro t ht
      rcases t with _ | s
      · simp
      · show Module.finrank K (c s) = _
        rw [hcr s (by omega), hA']
        omega

theorem exists_refine_nat {K V : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (Wn : ℕ → Submodule K V) (jn P : ℕ → ℕ) (h0 : Wn 0 = ⊥) (hm : Monotone Wn)
    (hs : ∀ k, Module.finrank K (Wn (k + 1)) = Module.finrank K (Wn k) + jn k)
    (hP0 : P 0 = 0) (hPs : ∀ i, P (i + 1) = P i + jn i) :
    ∀ a, ∃ W' : ℕ → Submodule K V, Monotone W' ∧ (∀ l ≤ P a, Module.finrank K (W' l) = l) ∧
      (∀ i ≤ a, W' (P i) = Wn i) ∧ ∀ l, P a ≤ l → W' l = Wn a := by
  have hr : ∀ i, Module.finrank K (Wn i) = P i := by
    intro i
    induction i with
    | zero => rw [h0, hP0]; simp
    | succ i ih => rw [hs, ih, hPs]
  intro a
  induction a with
  | zero =>
    refine ⟨fun _ => ⊥, fun _ _ _ => le_rfl, fun l hl => ?_, fun i hi => ?_, fun l _ => h0.symm⟩
    · rw [hP0] at hl
      have : l = 0 := by omega
      subst this; simp
    · have : i = 0 := by omega
      subst this; exact h0.symm
  | succ a ih =>
    obtain ⟨W', hW'm, hW'r, hW'p, hW'l⟩ := ih
    obtain ⟨c, hc, hc0, hcB, hcr⟩ := exists_chain_between (jn a) (Wn a) (Wn (a + 1))
      (hm (Nat.le_succ a)) (hs a)
    obtain ⟨W'', hW''⟩ : ∃ W'' : ℕ → Submodule K V, ∀ l, W'' l = if l ≤ P a then W' l else c (l - P a) :=
      ⟨_, fun _ => rfl⟩
    have hPa : W' (P a) = Wn a := hW'l _ le_rfl
    refine ⟨W'', ?_, ?_, ?_, ?_⟩
    · intro l m hlm
      rw [hW'' l, hW'' m]
      by_cases hl : l ≤ P a
      · by_cases hm' : m ≤ P a
        · rw [if_pos hl, if_pos hm']; exact hW'm hlm
        · rw [if_pos hl, if_neg hm']
          calc W' l ≤ W' (P a) := hW'm hl
            _ = c 0 := by rw [hPa, hc0]
            _ ≤ c (m - P a) := hc (Nat.zero_le _)
      · rw [if_neg hl, if_neg (by omega)]
        exact hc (by omega)
    · intro l hl
      rw [hW'' l]
      by_cases hl' : l ≤ P a
      · rw [if_pos hl']; exact hW'r l hl'
      · rw [if_neg hl', hcr _ (by rw [hPs] at hl; omega), hr]
        omega
    · intro i hi
      rw [hW'' (P i)]
      rcases Nat.lt_or_ge i (a + 1) with hia | hia
      · have hle : P i ≤ P a := by
          have key : ∀ d, P i ≤ P (i + d) := by
            intro d
            induction d with
            | zero => exact le_rfl
            | succ d ihd => rw [← Nat.add_assoc, hPs]; omega
          have := key (a - i)
          rwa [show i + (a - i) = a by omega] at this
        rw [if_pos hle]; exact hW'p i (by omega)
      · have hi' : i = a + 1 := by omega
        subst hi'
        by_cases hj : P (a + 1) ≤ P a
        · rw [if_pos hj]
          have hj0 : jn a = 0 := by rw [hPs] at hj; omega
          rw [show P (a + 1) = P a by rw [hPs, hj0, Nat.add_zero], hPa]
          exact hc0.symm.trans (hcB 0 (by omega))
        · rw [if_neg hj, hPs, Nat.add_sub_cancel_left]
          exact hcB _ le_rfl
    · intro l hl
      rw [hPs] at hl
      rw [hW'' l]
      by_cases hl' : l ≤ P a
      · rw [if_pos hl', hW'l l (by omega)]
        exact hc0.symm.trans (hcB 0 (by omega))
      · rw [if_neg hl']
        exact hcB _ (by omega)

theorem exists_refine_isIsoFlag : ∀ {n a : ℕ} {ε : Fin n → Bool} {j : Fin a → ℕ} {W : Flag n a}, IsIsoFlag ε j W → ∃ (b : ℕ) (W' : Flag n b) (β : Fin b → Fin a) (p : Fin (a + 1) → Fin (b + 1)), IsIsoFlag ε (fun _ => 1) W' ∧ (∀ i, W' (p i) = W i) ∧ W' (Fin.last b) = W (Fin.last a) ∧ (∀ l i, β l = i ↔ p i.castSucc ≤ l.castSucc ∧ l.castSucc < p i.succ) ∧ ∀ i, (p i : ℕ) = ∑ l ∈ univ.filter (fun l : Fin a => (l : ℕ) < (i : ℕ)), j l := by
  intro n a ε j W hW
  obtain ⟨h0, hmono, hstep, hiso⟩ := hW
  obtain ⟨jn, hjn⟩ : ∃ jn : ℕ → ℕ, ∀ k, jn k = if h : k < a then j ⟨k, h⟩ else 0 := ⟨_, fun _ => rfl⟩
  obtain ⟨Wn, hWn⟩ : ∃ Wn : ℕ → Submodule ℂ (Fin n → ℂ), ∀ k, Wn k = W ⟨min k a, by omega⟩ :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨P, hP⟩ : ∃ P : ℕ → ℕ, ∀ i, P i = ∑ k ∈ range i, jn k := ⟨_, fun _ => rfl⟩
  have hP0 : P 0 = 0 := by rw [hP]; simp
  have hPs : ∀ i, P (i + 1) = P i + jn i := fun i => by rw [hP, hP, Finset.sum_range_succ]
  have hPm : Monotone P := fun x y h => by
    rw [hP, hP]; exact Finset.sum_le_sum_of_subset (Finset.range_mono h)
  have hWi : ∀ i : Fin (a + 1), Wn i = W i := fun i => by
    rw [hWn]; congr 1; ext; simp; omega
  have hWn0 : Wn 0 = ⊥ := by
    rw [hWn, ← h0]; congr 1
  have hWnm : Monotone Wn := fun x y hxy => by
    rw [hWn, hWn]; exact hmono (Fin.mk_le_mk.2 (by omega))
  have hWns : ∀ k, Module.finrank ℂ (Wn (k + 1)) = Module.finrank ℂ (Wn k) + jn k := by
    intro k
    by_cases hk : k < a
    · have e1 : Wn (k + 1) = W (⟨k, hk⟩ : Fin a).succ := by
        rw [hWn]; congr 1; ext; simp; omega
      have e2 : Wn k = W (⟨k, hk⟩ : Fin a).castSucc := by
        rw [hWn]; congr 1; ext; simp; omega
      rw [e1, e2, hstep ⟨k, hk⟩, hjn, dif_pos hk]
    · have e : Wn (k + 1) = Wn k := by
        rw [hWn, hWn]; congr 1; ext; simp; omega
      rw [e, hjn, dif_neg hk, Nat.add_zero]
  obtain ⟨W', hW'm, hW'r, hW'p, hW'l⟩ := exists_refine_nat Wn jn P hWn0 hWnm hWns hP0 hPs a
  have hlast : W' (P a) = W (Fin.last a) := by
    rw [hW'l _ le_rfl, ← hWi (Fin.last a), Fin.val_last]
  have hβ : ∀ l : Fin (P a), ∃! i : Fin a, P i ≤ l ∧ (l : ℕ) < P (i + 1) := by
    intro l
    have ha : 0 < a := by
      rcases Nat.eq_zero_or_pos a with ha | ha
      · subst ha; have := l.isLt; omega
      · exact ha
    have hla : (l : ℕ) < P (a - 1 + 1) := by rw [show a - 1 + 1 = a by omega]; exact l.isLt
    have hex : ∃ m, (l : ℕ) < P (m + 1) := ⟨a - 1, hla⟩
    have hma : Nat.find hex < a := by
      have hle : Nat.find hex ≤ a - 1 := Nat.find_min' hex hla
      omega
    refine ⟨⟨Nat.find hex, hma⟩, ⟨?_, Nat.find_spec hex⟩, ?_⟩
    · rcases Nat.eq_zero_or_pos (Nat.find hex) with h | h
      · simp only [h, hP0]; exact Nat.zero_le _
      · have := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
        rw [show Nat.find hex - 1 + 1 = Nat.find hex by omega] at this
        simpa using this
    · rintro i ⟨hi1, hi2⟩
      apply Fin.ext
      show (i : ℕ) = Nat.find hex
      rcases lt_trichotomy (i : ℕ) (Nat.find hex) with h | h | h
      · exact absurd hi2 (not_lt.2 ((hPm (by omega : (i : ℕ) + 1 ≤ Nat.find hex)).trans
          (by
            rcases Nat.eq_zero_or_pos (Nat.find hex) with h' | h'
            · omega
            · have := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
              rw [show Nat.find hex - 1 + 1 = Nat.find hex by omega] at this
              omega)))
      · exact h
      · exact absurd (Nat.find_spec hex) (not_lt.2 ((hPm (by omega : Nat.find hex + 1 ≤ (i : ℕ))).trans hi1))
  have hPle : ∀ i : Fin (a + 1), P i < P a + 1 := fun i => Nat.lt_succ_of_le (hPm (Nat.le_of_lt_succ i.isLt))
  refine ⟨P a, fun l => W' l, fun l => Classical.choose (hβ l), fun i => ⟨P i, hPle i⟩, ⟨?_, ?_, ?_, ?_⟩,
    ?_, ?_, ?_, ?_⟩
  · show W' ((0 : Fin (P a + 1)) : ℕ) = ⊥
    rw [Fin.val_zero]
    exact Submodule.finrank_eq_zero.1 (hW'r 0 (Nat.zero_le _))
  · intro x y hxy
    exact hW'm (Fin.le_iff_val_le_val.1 hxy)
  · intro i
    show Module.finrank ℂ (W' ((i.succ : Fin (P a + 1)) : ℕ)) = Module.finrank ℂ (W' ((i.castSucc : Fin (P a + 1)) : ℕ)) + 1
    rw [Fin.val_succ, Fin.coe_castSucc, hW'r _ (by omega), hW'r _ (by omega)]
  · intro x hx y hy
    have e : W' ((Fin.last (P a) : Fin (P a + 1)) : ℕ) = W (Fin.last a) := by rw [Fin.val_last, hlast]
    exact hiso x (e ▸ hx) y (e ▸ hy)
  · intro i
    show W' (P i) = W i
    rw [hW'p i (Nat.le_of_lt_succ i.isLt), hWi]
  · show W' ((Fin.last (P a) : Fin (P a + 1)) : ℕ) = W (Fin.last a)
    rw [Fin.val_last, hlast]
  · intro l i
    have hs := Classical.choose_spec (hβ l)
    constructor
    · rintro rfl
      refine ⟨Fin.le_iff_val_le_val.2 ?_, Fin.lt_iff_val_lt_val.2 ?_⟩
      · simpa using hs.1.1
      · simpa using hs.1.2
    · rintro ⟨h1, h2⟩
      refine (hs.2 i ⟨?_, ?_⟩).symm
      · simpa using Fin.le_iff_val_le_val.1 h1
      · simpa using Fin.lt_iff_val_lt_val.1 h2
  · intro i
    show P i = _
    rw [hP, Finset.sum_filter]
    have e1 : ∀ l : Fin a, (if (l : ℕ) < (i : ℕ) then j l else 0) =
        (fun k => if k < (i : ℕ) then jn k else 0) (l : ℕ) := by
      intro l; simp [hjn, l.isLt]
    rw [Finset.sum_congr rfl (fun l _ => e1 l), Fin.sum_univ_eq_sum_range (fun k => if k < (i : ℕ) then jn k else 0) a,
      ← Finset.sum_filter]
    congr 1
    ext k; simp; omega

end GlobalTheory.RealInd.Stages
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ReframeFunctionOnHomsNormOneCovolumeOne
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open GlobalTheory.AdSpan.ReVec
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.AdSpan.ReVec

variable {D : D7}

def reWEquiv (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V) : WO S T ≃+ WO S T where
  toFun := reW S T b
  invFun := reWi S T b
  left_inv := reWi_reW S T b
  right_inv := reW_reWi S T b
  map_add' := reW_add S T b

theorem continuous_reW (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V) :
    Continuous (reW S T b) := by
  haveI : IsTopologicalRing (AE D) := (Formalism.IndefR.Eqv.ae_facts D).1
  exact continuous_id.matrix_mul continuous_const

theorem continuous_reWi (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V) :
    Continuous (reWi S T b) := by
  haveI : IsTopologicalRing (AE D) := (Formalism.IndefR.Eqv.ae_facts D).1
  exact continuous_id.matrix_mul continuous_const

theorem reW_mem_ratL_iff (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V) (x : WO S T) :
    reW S T b x ∈ ratL T S ↔ x ∈ ratL T S := by
  have key : ∀ (x : Matrix (Fin T.rank) (Fin S.rank) (AE D)) (N : Matrix (Fin S.rank) (Fin S.rank) D.host.E),
      x ∈ ratL T S → HMul.hMul (α := Matrix (Fin T.rank) (Fin S.rank) (AE D)) (β := Matrix (Fin S.rank) (Fin S.rank) (AE D))
        (γ := Matrix (Fin T.rank) (Fin S.rank) (AE D)) x (N.map (incA D)) ∈ ratL T S := by
    rintro x N ⟨γ, rfl⟩
    refine ⟨γ * N, ?_⟩
    show (γ * N).map (incA D) = _
    exact Matrix.map_mul (f := incA D)
  constructor
  · intro h
    have h2 := key _ (frP S b) h
    have : HMul.hMul (α := Matrix (Fin T.rank) (Fin S.rank) (AE D)) (reW S T b x) ((frP S b).map (incA D)) = x :=
      reWi_reW S T b x
    rwa [this] at h2
  · exact key x _

theorem reframeFunctionOnHoms_norm_one_covolumeOne (D : D7) (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V) (f : WO S T → ℂ) :
    AllSome (fun p : Measure (WO S T) × Set (WO S T) => IsCovolOne (ratL T S) p.1 p.2) (fun p => nrm2 p.1 p.2 f = 1) → AllSome (fun p : Measure (WO (reS S b) T) × Set (WO (reS S b) T) => IsCovolOne (ratL T (reS S b)) p.1 p.2) (fun p => nrm2 p.1 p.2 (reF S T b f) = 1) := by
  rintro ⟨⟨p0, hp0⟩, hall⟩
  have he : Continuous (reWEquiv S T b) := continuous_reW S T b
  have he' : Continuous (reWEquiv S T b).symm := continuous_reWi S T b
  have hr : ∀ x, reWEquiv S T b x ∈ ratL T S ↔ x ∈ ratL T S := reW_mem_ratL_iff S T b
  have hr' : ∀ x, (reWEquiv S T b).symm x ∈ ratL T S ↔ x ∈ ratL T S := fun x => by
    rw [← hr, AddEquiv.apply_symm_apply]
  refine ⟨⟨(p0.1.map (reWEquiv S T b).symm, (reWEquiv S T b).symm '' p0.2),
    (GlobalTheory.Unf.ParCont.isCovolOne_map hp0 (reWEquiv S T b).symm he' he hr').1⟩, ?_⟩
  have aux : ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 →
      nrm2 μ 𝓕 (fun x => f (reWEquiv S T b x)) = 1 := by
    intro μ 𝓕 hp
    obtain ⟨h1, hemb⟩ := GlobalTheory.Unf.ParCont.isCovolOne_map hp (reWEquiv S T b) he he' hr
    have h2 := hall (μ.map (reWEquiv S T b), reWEquiv S T b '' 𝓕) h1
    simp only [nrm2] at h2 ⊢
    rw [hemb.setIntegral_map, Set.preimage_image_eq _ (reWEquiv S T b).injective] at h2
    exact h2
  rintro ⟨μ', 𝓕'⟩ hp
  exact aux μ' 𝓕' hp

end GlobalTheory.AdSpan.ReVec
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplittingHeckeCharExistsArchimedeanExponentStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open Formalism.IndefR.Mult (DSModel dualPar parA parB)
open Formalism.MainNotions.SchurIrreducible (AdmGK ARi ARiiiUp ARiiiDown ARiiiLine DiscreteSeriesBlattner admQ5)
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction hiding Mat
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix (SignCompat plainMat barMat)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (fockIp)
open GlobalTheory.Chain (signed)
open GlobalTheory.Chain.RealIt (LPol locS locT IsPolyIso)
open MeasureTheory Matrix
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ArchRec
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splittingHeckeChar_exists_archimedeanExponent : ∀ (D : D7) (θ : InfFam D) (χ : (AE D)ˣ →* Circle) (n : ℕ) (τ : D.what₂.Tau), IsInfFam θ → IsHeckeChar D χ → ResEta D χ n → ∃ a : ℚ, HasInfExp D χ τ a := by
  first | exact @GlobalTheory.SplitCharExp.exists_hasInfExp | exact GlobalTheory.SplitCharExp.exists_hasInfExp | (intros; apply GlobalTheory.SplitCharExp.exists_hasInfExp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SumDiagOrderEqOfIntegralTranslateIndicatorRelatiStatement
section
open Matrix Formalism.UG GlobalTheory.Hk3 GlobalTheory.FinWeil GlobalTheory.SphTheta ValuativeRel Classical
open GlobalTheory.LFun (HasSatU IsSatVecU heckeVec)
open GlobalTheory.LGrp (bcParam extProd)
open GlobalTheory.WeilM (UG IsQuad Darboux symp sbClass SB IsWeilB IsWeilPair TestClass schr dbl diagCols)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlace (str chi IsUnramAdd)
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_diag_order_eq_of_integralTranslateIndicator_relation : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ), IsUnramInv ϖ σ q → ∀ (m : ℕ) (ι κ : Type) [Fintype ι] [Fintype κ] (c : ι → ℂ) (c' : κ → ℂ) (U : ι → GL (Fin m) L) (V : κ → GL (Fin m) L), (∀ i, (U i).1.BlockTriangular id) → (∀ j, (V j).1.BlockTriangular id) → (∀ t : GL (Fin m) L, ∑ i, c i * (if t.1 * (U i).1 ∈ intMat L (Fin m) (Fin m) then 1 else 0) = ∑ j, c' j * (if (V j).1 * t.1 ∈ intMat L (Fin m) (Fin m) then 1 else 0)) → ∀ f : (Fin m → ℤ) → ℂ, ∑ i, c i * f (fun r => ordL ((U i).1 r r)) = ∑ j, c' j * f (fun r => ordL ((V j).1 r.rev r.rev)) := by
  first | exact @GlobalTheory.SphTheta.sum_ordL_diag_eq_of_indicator | exact GlobalTheory.SphTheta.sum_ordL_diag_eq_of_indicator | (intros; apply GlobalTheory.SphTheta.sum_ordL_diag_eq_of_indicator <;> assumption)
end

