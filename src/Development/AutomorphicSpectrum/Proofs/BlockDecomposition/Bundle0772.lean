import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.ThetaOrbits
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0021
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0480
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1842
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0430
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0066

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SummableOfTsumEnormLtTop
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.ThetaOrbit

section Abstract

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] {Γ : Subgroup G} [DiscreteTopology Γ] {μ : Measure G} [μ.IsMulLeftInvariant]
  {X ι : Type*} {κ : ι → Type*} [Countable X] [Countable ι] [∀ i, Countable (κ i)]

theorem summable_of_tsum_enorm_lt_top {Y : Type*} {f : Y → ℂ} (h : ∑' y, ‖f y‖ₑ < ⊤) : Summable f := by
  have h' : Summable (fun y => ‖f y‖₊) :=
    ENNReal.tsum_coe_ne_top_iff_summable.1 (by simpa only [enorm_eq_nnnorm] using h.ne)
  exact Summable.of_norm ((NNReal.summable_coe.2 h').congr fun y => coe_nnnorm _)

theorem hasSum_average_descend (e : (Σ i, κ i) ≃ X) (a : G → X → ℂ) (ha : ∀ x, Measurable fun g => a g x)
    (hA : LeftInv Γ fun g => ∑' x, ‖a g x‖ₑ)
    (hL : ∀ i, LeftInv Γ fun g => ∑' k : κ i, a g (e ⟨i, k⟩))
    (hfin : ∫⁻ q, descend Γ (fun g => ∑' x, ‖a g x‖ₑ) q ∂GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ < ⊤) :
    HasSum (fun i => ⨍ q, descend Γ (fun g => ∑' k : κ i, a g (e ⟨i, k⟩)) q ∂GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ)
      (⨍ q, descend Γ (fun g => ∑' x, a g x) q ∂GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ) := by
  classical
  have hsec : Measurable (sec Γ) := measurableEmbedding_sec.measurable
  have hdescC : ∀ φ : G → ℂ, LeftInv Γ φ → descend Γ φ = φ ∘ sec Γ := by
    intro φ hφ
    funext q
    show φ q.out = φ (sec Γ q)
    apply hφ.eq_of_mk_eq
    rw [mk_sec]
    exact Quotient.out_eq q
  have hdescE : ∀ φ : G → ℝ≥0∞, LeftInv Γ φ → descend Γ φ = φ ∘ sec Γ := by
    intro φ hφ
    funext q
    show φ q.out = φ (sec Γ q)
    apply hφ.eq_of_mk_eq
    rw [mk_sec]
    exact Quotient.out_eq q
  have hNm : Measurable (descend Γ fun g => ∑' x, ‖a g x‖ₑ) := by
    rw [hdescE _ hA]
    exact (Measurable.tsum fun x => (ha x).enorm).comp hsec
  have hFm : ∀ i, AEStronglyMeasurable (descend Γ fun g => ∑' k : κ i, a g (e ⟨i, k⟩))
      (GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ) := by
    intro i
    rw [hdescC _ (hL i)]
    exact ((Measurable.tsum fun k => ha _).comp hsec).aestronglyMeasurable
  have hbound : ∀ g, ∑' i, ‖∑' k : κ i, a g (e ⟨i, k⟩)‖ₑ ≤ ∑' x, ‖a g x‖ₑ := by
    intro g
    calc ∑' i, ‖∑' k : κ i, a g (e ⟨i, k⟩)‖ₑ ≤ ∑' i, ∑' k : κ i, ‖a g (e ⟨i, k⟩)‖ₑ :=
          ENNReal.tsum_le_tsum fun i => enorm_tsum_le_tsum_enorm
      _ = ∑' p : Σ i, κ i, ‖a g (e p)‖ₑ := (ENNReal.tsum_sigma' fun p => ‖a g (e p)‖ₑ).symm
      _ = ∑' x, ‖a g x‖ₑ := e.tsum_eq fun x => ‖a g x‖ₑ
  have hpt : ∀ g, ∑' x, ‖a g x‖ₑ < ⊤ →
      HasSum (fun i => ∑' k : κ i, a g (e ⟨i, k⟩)) (∑' x, a g x) := by
    intro g hg
    have hs : Summable (a g) := summable_of_tsum_enorm_lt_top hg
    have hse : Summable (a g ∘ e) := e.summable_iff.2 hs
    exact (e.hasSum_iff.2 hs.hasSum).sigma fun i => (hse.sigma_factor i).hasSum
  have hlin : ∑' i, ∫⁻ q, ‖descend Γ (fun g => ∑' k : κ i, a g (e ⟨i, k⟩)) q‖ₑ
      ∂GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ < ⊤ := by
    rw [← lintegral_tsum fun i => (hFm i).enorm]
    exact lt_of_le_of_lt (lintegral_mono fun q => hbound q.out) hfin
  have hsI : Summable fun i =>
      ∫ q, descend Γ (fun g => ∑' k : κ i, a g (e ⟨i, k⟩)) q ∂GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ :=
    summable_of_tsum_enorm_lt_top
      (lt_of_le_of_lt (ENNReal.tsum_le_tsum fun i => enorm_integral_le_lintegral_enorm _) hlin)
  have hae : ∀ᵐ q ∂GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ, descend Γ (fun g => ∑' x, ‖a g x‖ₑ) q < ⊤ :=
    ae_lt_top hNm hfin.ne
  have hint : ∫ q, descend Γ (fun g => ∑' x, a g x) q ∂GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ =
      ∑' i, ∫ q, descend Γ (fun g => ∑' k : κ i, a g (e ⟨i, k⟩)) q ∂GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ := by
    rw [← integral_tsum hFm hlin.ne]
    refine integral_congr_ae ?_
    filter_upwards [hae] with q hq
    exact (hpt q.out hq).tsum_eq.symm
  simp only [average_eq]
  rw [hint]
  exact hsI.hasSum.const_smul _

end Abstract

section Rows

variable {K : Type} [Field K]

open GlobalTheory.CompanionTheory.MatrixRowSpace in

theorem bijective_mul_rowBasis (m n : ℕ)
    (c : ∀ U : Submodule K (Fin n → K), Matrix (Fin (Module.finrank K U)) (Fin n) K)
    (hc : ∀ U, LinearIndependent K (c U) ∧ Submodule.span K (Set.range (c U)) = U) :
    Function.Bijective (fun q : (Σ U : Submodule K (Fin n → K),
      {x : Matrix (Fin m) (Fin (Module.finrank K U)) K // x.rank = Module.finrank K U}) => q.2.1 * c q.1) := by
  have hinj : ∀ U, Function.Injective (c U).vecMulLinear := fun U =>
    Matrix.vecMul_injective_iff.2 (hc U).1
  have hrange : ∀ U, LinearMap.range (c U).vecMulLinear = U := fun U => by
    rw [range_vecMulLinear_eq, (hc U).2]
  constructor
  · rintro ⟨U, x, hx⟩ ⟨U', x', hx'⟩ h
    dsimp only at h
    have hU : U = U' := by
      have h1 := span_rows_mul_of_rank x (c U) hx
      have h2 := span_rows_mul_of_rank x' (c U') hx'
      calc U = Submodule.span K (Set.range (c U)) := (hc U).2.symm
        _ = Submodule.span K (Set.range (x * c U)) := h1.symm
        _ = Submodule.span K (Set.range (x' * c U')) := by rw [h]
        _ = Submodule.span K (Set.range (c U')) := h2
        _ = U' := (hc U').2
    subst hU
    have hxx : x = x' := by
      ext i j
      have hi : (x * c U) i = (x' * c U) i := by rw [h]
      rw [row_mul, row_mul] at hi
      exact congrFun (hinj U hi) j
    subst hxx
    rfl
  · intro y
    obtain ⟨U, hU⟩ : ∃ U : Submodule K (Fin n → K), U = Submodule.span K (Set.range y) := ⟨_, rfl⟩
    have hrow : ∀ i, ∃ v : Fin (Module.finrank K U) → K, (c U).vecMulLinear v = y i := by
      intro i
      have hmem : y i ∈ LinearMap.range (c U).vecMulLinear := by
        rw [hrange U, hU]
        exact Submodule.subset_span ⟨i, rfl⟩
      exact LinearMap.mem_range.1 hmem
    choose v hv using hrow
    have hxc : Matrix.of v * c U = y := by
      ext i j
      have hi : (Matrix.of v * c U) i = y i := by
        rw [row_mul]
        exact hv i
      exact congrFun hi j
    have hS : Submodule.span K (Set.range (Matrix.of v)) = ⊤ := by
      apply Submodule.map_injective_of_injective (hinj U)
      rw [Submodule.map_top, hrange U, ← span_rows_mul, hxc, hU]
    exact ⟨⟨U, Matrix.of v, (span_rows_eq_top_iff _).2 hS⟩, hxc⟩

theorem countable_submodule [Countable K] (n : ℕ) : Countable (Submodule K (Fin n → K)) := by
  have hs : Function.Surjective
      (fun s : Finset (Fin n → K) => Submodule.span K (s : Set (Fin n → K))) := fun U =>
    IsNoetherian.noetherian U
  exact hs.countable

end Rows

variable {D : D7}

private theorem exists_invPt_mul_eq_invPt_mul_of_mem_GQ (V : HSp D) {γ : GA D V} (hγ : γ ∈ GQ V) :
    ∃ A : GL (Fin V.rank) D.host.E, ∀ (g : GA D V) {a : ℕ} (ξ : Matrix (Fin V.rank) (Fin a) D.host.E),
      GlobalTheory.SiegelFormula.invPt V (γ * g) ξ =
        GlobalTheory.SiegelFormula.invPt V g ((A : Matrix (Fin V.rank) (Fin V.rank) D.host.E) * ξ) := by
  simp only [GQ, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HFinIn, Subgroup.mem_subgroupOf, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HFin,
    Subgroup.mem_map] at hγ
  obtain ⟨g0, -, hg0⟩ := hγ
  refine ⟨g0⁻¹, fun g a ξ => ?_⟩
  have key : ((Formalism.L2.Theta.matHom V γ⁻¹ : GL _ _) : Matrix _ _ _) =
      ((g0⁻¹ : GL _ _) : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (incA D) := by
    have hγ' : Formalism.L2.Theta.matHom V γ = _ := hg0.symm
    rw [map_inv, hγ', ← map_inv]
    rfl
  simp only [GlobalTheory.SiegelFormula.invPt, Formalism.L2.Theta.mt, mul_inv_rev, map_mul, Units.val_mul,
    Matrix.map_mul, Matrix.mul_assoc, key]

theorem leftInv_rankSum (V : HSp D) {r n : ℕ} (φ : Mx D V.rank n → ℂ) (c : Matrix (Fin r) (Fin n) D.host.E) (s : ℕ) :
    LeftInv (GQ V) fun h => ∑' x : {x : Matrix (Fin V.rank) (Fin r) D.host.E // x.rank = s},
      φ (GlobalTheory.SiegelFormula.invPt V h (x.1 * c)) := by
  intro γ hγ g
  obtain ⟨A, hA⟩ := exists_invPt_mul_eq_invPt_mul_of_mem_GQ V hγ
  have hrank : ∀ (B : GL (Fin V.rank) D.host.E) (x : Matrix (Fin V.rank) (Fin r) D.host.E),
      ((B : Matrix (Fin V.rank) (Fin V.rank) D.host.E) * x).rank = x.rank := fun B x =>
    Matrix.rank_mul_eq_right_of_isUnit_det _ _ ((Matrix.isUnit_iff_isUnit_det _).1 B.isUnit)
  let eqv : {x : Matrix (Fin V.rank) (Fin r) D.host.E // x.rank = s} ≃
      {x : Matrix (Fin V.rank) (Fin r) D.host.E // x.rank = s} :=
    { toFun := fun x => ⟨(A : Matrix (Fin V.rank) (Fin V.rank) D.host.E) * x.1, (hrank A x.1).trans x.2⟩
      invFun := fun x => ⟨((A⁻¹ : GL (Fin V.rank) D.host.E) : Matrix (Fin V.rank) (Fin V.rank) D.host.E) * x.1,
        (hrank A⁻¹ x.1).trans x.2⟩
      left_inv := fun x => Subtype.ext (by simp [← Matrix.mul_assoc])
      right_inv := fun x => Subtype.ext (by simp [← Matrix.mul_assoc]) }
  show ∑' x : {x : Matrix (Fin V.rank) (Fin r) D.host.E // x.rank = s},
      φ (GlobalTheory.SiegelFormula.invPt V (γ * g) (x.1 * c)) =
    ∑' x : {x : Matrix (Fin V.rank) (Fin r) D.host.E // x.rank = s}, φ (GlobalTheory.SiegelFormula.invPt V g (x.1 * c))
  simp only [hA, ← Matrix.mul_assoc]
  exact eqv.tsum_eq fun x => φ (GlobalTheory.SiegelFormula.invPt V g (x.1 * c))

theorem pull_mt (V : HSp D) {r n : ℕ} (φ : Mx D V.rank n → ℂ) (c : Matrix (Fin r) (Fin n) D.host.E) (h : GA D V)
    (x : Matrix (Fin V.rank) (Fin r) D.host.E) :
    pull c φ (HMul.hMul (Formalism.L2.Theta.mt V h⁻¹) (x.map (incA D))) = φ (GlobalTheory.SiegelFormula.invPt V h (x * c)) := by
  simp only [pull, GlobalTheory.SiegelFormula.invPt, Matrix.map_mul, Matrix.mul_assoc]

theorem thetaOrbits : ThetaOrbits := by
  intro D n V θ hθ ν hν Φ hfin c hc
  haveI := hν
  haveI : Countable D.host.E := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableE
  haveI : Countable (Submodule D.host.E (Fin n → D.host.E)) := countable_submodule n
  haveI : ∀ r : ℕ, Countable (Matrix (Fin V.rank) (Fin r) D.host.E) := fun r =>
    inferInstanceAs (Countable (Fin V.rank → Fin r → D.host.E))
  have hcont : Continuous Φ.1 :=
    (GlobalTheory.CompanionTheory.WeilTheta.schwartzA_continuous_and_dominated D θ hθ V.rank n Φ.1 Φ.2).1
  have key := hasSum_average_descend (G := GA D V) (Γ := GQ V) (μ := ν)
    (κ := fun U : Submodule D.host.E (Fin n → D.host.E) =>
      {x : Matrix (Fin V.rank) (Fin (Module.finrank D.host.E U)) D.host.E //
        x.rank = Module.finrank D.host.E U})
    (Equiv.ofBijective _ (bijective_mul_rowBasis V.rank n c hc))
    (fun g ξ => Φ.1 (GlobalTheory.SiegelFormula.invPt V g ξ))
    (fun ξ => (hcont.comp (GlobalTheory.AbsThetaSemi.continuous_invPt V ξ)).measurable)
    (GlobalTheory.SiegelFormula.leftInv_absTheta V Φ.1)
    (fun U => leftInv_rankSum V Φ.1 (c U) (Module.finrank D.host.E U))
    hfin
  convert key using 1
  funext U
  simp only [Ifr, pull_mt]
  rfl

end GlobalTheory.CompanionTheory.ThetaOrbit

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaSumInvariantWeylInvolution
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.ThetaPoisson

section Gen

variable {A : Type} [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A] [T2Space A]
  [LocallyCompactSpace A] [SecondCountableTopology A] [MeasurableSpace A] [BorelSpace A]
  (Γ : AddSubgroup A) [DiscreteTopology Γ] (K : Set A) (hK : IsCompact K) (hcov : ∀ x, ∃ γ ∈ Γ, γ + x ∈ K)
  (B : A → A → ℂ) (hc : ∀ y, Continuous fun x => B x y) (hsy : ∀ x y, B x y = B y x)
  (hadd : ∀ x x' y, B (x + x') y = B x y * B x' y) (hn : ∀ x y, ‖B x y‖ = 1)
  (hker : ∀ x, (∀ γ ∈ Γ, B γ x = 1) ↔ x ∈ Γ) (hinj : ∀ γ ∈ Γ, (∀ x, B γ x = 1) → γ = 0)
  (μ : Measure A) (𝓕 : Set A) [hμ : μ.IsAddHaarMeasure] (hF : IsAddFundamentalDomain Γ 𝓕 μ) (h1 : μ 𝓕 = 1)

include hK hcov hc hsy hadd hn hker hinj hμ hF h1

theorem poisson_translates {f : A → ℂ} (hf : Continuous f)
    (hb : ∀ Q : Set A, IsCompact Q → ∃ b : Γ → ℝ, Summable b ∧ ∀ x ∈ Q, ∀ ξ : Γ, ‖f (ξ + x)‖ ≤ b ξ)
    (hsum : Summable fun γ : Γ => ‖∫ x, f x * B x γ ∂μ‖) :
    ∑' ξ : Γ, f ξ = ∑' γ : Γ, ∫ x, f x * B x γ ∂μ := by
  have : Countable Γ := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  have hc' : ∀ y, Continuous (B y) := fun y => (hc y).congr fun x => hsy x y
  have hadd' : ∀ y x x', B y (x + x') = B y x * B y x' := fun y x x' => by
    rw [hsy y, hadd, hsy x, hsy x']
  have hU : GlobalTheory.CompanionTheory.Hypotheses₂.OneV.PoiAbs.UnifSummable Γ.subtype f := fun Q hQ => by
    obtain ⟨b, hb1, hb2⟩ := hb Q hQ
    refine ⟨b, hb1, fun c x hx => ?_⟩
    have h := hb2 x hx c
    rwa [add_comm] at h
  have hfi : Integrable f μ := GlobalTheory.CompanionTheory.Hypotheses₂.OneV.PoiAbs.integrable_of_unif hf hU μ hK fun x => by
    obtain ⟨γ, hγ, h⟩ := hcov x
    refine ⟨⟨-γ, Γ.neg_mem hγ⟩, ?_⟩
    simpa [sub_neg_eq_add, add_comm] using h
  have hcont : Continuous fun x => ∑' ξ : Γ, f (ξ + x) := by
    refine continuous_iff_continuousAt.2 fun x => ?_
    obtain ⟨Q, hQ, hxQ⟩ := exists_compact_mem_nhds x
    obtain ⟨b, hb1, hb2⟩ := hb Q hQ
    have h : ContinuousOn (fun x => ∑' ξ : Γ, f (ξ + x)) Q :=
      continuousOn_tsum (fun ξ => (hf.comp (continuous_const.add continuous_id)).continuousOn) hb1
        (fun ξ x hx => hb2 x hx ξ)
    exact h.continuousAt hxQ
  have hcoef : ∀ γ : Γ, ∫ x in 𝓕, B γ x * (∑' ξ : Γ, f (ξ + x)) ∂μ = ∫ x, f x * B x γ ∂μ := by
    intro γ
    have hi : Integrable (fun x => f x * B x γ) μ :=
      hfi.mul_bdd (c := 1) (hc γ).aestronglyMeasurable (Filter.Eventually.of_forall fun y => (hn y γ).le)
    rw [(GlobalTheory.CovolumeOneSelfDual.unfold Γ μ 𝓕 hF _ hi).2]
    congr 1
    funext x
    rw [← tsum_mul_left]
    refine tsum_congr fun ξ => ?_
    rw [hadd, (hker γ).2 γ.2 ξ ξ.2, one_mul, mul_comm, hsy]
  have key := GlobalTheory.CompactQuotientFourier.inversion_at_zero A Γ K hK hcov Γ (fun γ x => B γ x)
    (fun γ => hc' γ) (fun γ x y => hadd' γ x y) (fun a b x => hadd a b x) (fun a x => hn a x)
    (fun x => by rw [← hker x]; exact ⟨fun h γ hγ => h ⟨γ, hγ⟩, fun h γ => h γ γ.2⟩)
    (fun a h => Subtype.ext (hinj a a.2 h)) μ 𝓕 hμ hF h1 (fun x => ∑' ξ : Γ, f (ξ + x))
    hcont
    (fun γ hγ x => by
      rw [← (Equiv.addRight (⟨γ, hγ⟩ : Γ)).tsum_eq fun ξ : Γ => f (ξ + x)]
      refine tsum_congr fun ξ => ?_
      simp [add_assoc])
    (by simp only [hcoef]; exact hsum)
  simp only [hcoef, add_zero] at key
  exact key

end Gen

section Adelic

variable {D : D7} {m n : ℕ}

def ratEquiv (D : D7) (m n : ℕ) : Matrix (Fin m) (Fin n) D.host.E ≃ ratMx D m n :=
  Equiv.ofBijective (fun ξ => ⟨rat ξ, ⟨ξ, rfl⟩⟩)
    ⟨fun _ _ h => rat_injective (congrArg Subtype.val h), fun ⟨_, ξ, h⟩ => ⟨ξ, Subtype.ext h⟩⟩

theorem tsum_ratMx (f : Mx D m n → ℂ) :
    ∑' γ : ratMx D m n, f γ = ∑' ξ : Matrix (Fin m) (Fin n) D.host.E, f (ξ.map (incA D)) :=
  ((ratEquiv D m n).tsum_eq fun γ : ratMx D m n => f γ).symm

theorem pairing_symm {T : Matrix (Fin m) (Fin m) D.host.E} (hT : IsHermND D.sp.cm.sig T)
    (ψ : AddChar (AF D.host.F) ℂ) (x y : Mx D m n) :
    GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.pairing T ψ x y = GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.pairing T ψ y x := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.pairing GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.trA
  rw [← GlobalTheory.SiegelWeilLitCompare.gramQ_adj hT x y, ← GlobalTheory.DualPairCheck.trace_cA (Matrix.trace (GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.gramQ T x y))]
  congr 2
  simp only [Matrix.trace, map_sum]
  rfl

theorem translates_bound {θ : InfFam D} (hθ : IsInfFam θ) (φ : schwartzA θ m n) (Q : Set (Mx D m n)) (hQ : IsCompact Q) :
    ∃ b : ratMx D m n → ℝ, Summable b ∧ ∀ x ∈ Q, ∀ ξ : ratMx D m n, ‖φ.1 (ξ + x)‖ ≤ b ξ := by
  obtain ⟨N, hN⟩ := GlobalTheory.T.exists_summable_bound_schwartz_majorant_rational_translates D θ hθ m n
  obtain ⟨-, K, hK, hC⟩ := GlobalTheory.T.schwartzBruhatAdelicMatrix_continuous_le_majorant D θ hθ m n φ.1
    (GlobalTheory.SchwartzPure.isSchwartzBruhat_of_mem_schwartzA D θ hθ m n φ.1 φ.2)
  obtain ⟨C, hC⟩ := hC N
  obtain ⟨b, hb, hb'⟩ := hN K Q hK hQ
  refine ⟨fun γ => |C| * b ((ratEquiv D m n).symm γ), ((ratEquiv D m n).symm.summable_iff.2 hb).mul_left |C|, ?_⟩
  intro x hx γ
  obtain ⟨ξ, rfl⟩ := (ratEquiv D m n).surjective γ
  have h1 := hb' x hx ξ
  have h2 := hC (x + rat ξ)
  have e : ((ratEquiv D m n ξ : Mx D m n) + x) = x + rat ξ := add_comm _ _
  rw [e]
  beta_reduce
  rw [Equiv.symm_apply_apply]
  exact h2.trans (mul_le_mul (le_abs_self C) h1 (GlobalTheory.Unf.maj_nonneg _ _ _ _) (abs_nonneg C))

end Adelic

theorem theta_weyl : ∀ (D : D7) (n : ℕ) (V : HSp D) ψ χ θ μ ω, HidaSetting D n V ψ χ θ μ ω →
    ∀ g : G D n, mat g = blk4 0 1 (-1) 0 →
    ∀ Φ : schwartzA θ V.rank n,
      ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E, (ω g Φ).1 (ξ.map (incA D)) =
        ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E, Φ.1 (ξ.map (incA D)) := by
  intro D n V ψ χ θ μ ω hS g hg Φ
  obtain ⟨-, -, hψ, -, -, hθ, ⟨𝓕, hμ⟩, hω⟩ := hS
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := lattice_Mx D V.rank n
  haveI : BorelSpace (Mx D V.rank n) := ⟨rfl⟩
  have hT := isHermND_gram V
  obtain ⟨h1, h2⟩ := GlobalTheory.T.rationalAdelicMatrices_self_annihilator D V.rank n V.gram hT ψ hψ
  have hs := pairing_symm (n := n) hT ψ
  have hval : ∀ x, (ω g Φ).1 x = ∫ y, Φ.1 y * GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.pairing V.gram ψ y x ∂μ := fun x => by
    rw [hω.weyl g hg Φ x]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    beta_reduce
    rw [hs y x]
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.pairing, GlobalTheory.SiegelWeilLitCompare.gramQ_eq]
    rfl
  haveI := hμ.1
  have key := poisson_translates (ratMx D V.rank n) K hK hKc (GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.pairing (n := n) V.gram ψ)
    (fun y => ?_) hs (fun x x' y => ?_) (fun x y => hψ.2.1 _) h1 h2 μ 𝓕 hμ.2.1 hμ.2.2 (f := Φ.1) ?_
    (translates_bound hθ Φ) ?_
  · simp only [← hval] at key
    rw [tsum_ratMx, tsum_ratMx (fun x => (ω g Φ).1 x)] at key
    exact key.symm
  · simp only [hs _ y]
    haveI := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
    haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
    have ht : Continuous (GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.trA (D := D)) :=
      IsModuleTopology.continuous_of_linearMap (Algebra.trace (AF D.host.F) (AE D))
    exact hψ.1.comp (ht.comp (continuous_const.matrix_mul continuous_id).matrix_trace)
  · simp only [hs _ y]
    unfold GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.pairing GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.trA GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.gramQ GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.mmul
    rw [Matrix.mul_add, Matrix.trace_add, map_add, AddChar.map_add_eq_mul]
  · exact (GlobalTheory.T.schwartzBruhatAdelicMatrix_continuous_le_majorant D θ hθ _ n Φ.1
      (GlobalTheory.SchwartzPure.isSchwartzBruhat_of_mem_schwartzA D θ hθ _ n Φ.1 Φ.2)).1
  · simp only [← hval]
    exact (ratEquiv D V.rank n).summable_iff.1 (GlobalTheory.SiegelWeilLitCompare.summable_rat hθ (ω g Φ))

end GlobalTheory.CompanionTheory.ThetaPoisson
end
end

