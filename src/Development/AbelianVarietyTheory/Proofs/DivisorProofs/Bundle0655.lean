import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0633
import Formalism.PadicSubsetSums.CentralIdempotents.GaloisConjCentralIdempotent
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0012
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0623

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantCoeffFrob
section
set_option autoImplicit false

noncomputable section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog

namespace GlobalTheory.QLog.Window

section Integral

variable {B Q : Type} [CommRing B] [CommRing Q] [Algebra B Q] {σ : Type}

theorem in_top_iff (f : MvPowerSeries σ Q) :
    In (⊤ : Ideal B) f ↔ ∃ s : MvPowerSeries σ B, f = map (algebraMap B Q) s := by
  constructor
  · intro h
    choose b _ hb using h
    let s : MvPowerSeries σ B := fun α => b α
    refine ⟨s, ?_⟩
    ext α
    rw [coeff_map, hb]
    rfl
  · rintro ⟨s, rfl⟩ α
    exact ⟨coeff α s, Submodule.mem_top, by rw [coeff_map]⟩

theorem in_zero (N : Ideal B) : In N (0 : MvPowerSeries σ Q) := fun _ =>
  ⟨0, N.zero_mem, by simp⟩

theorem in_add {N : Ideal B} {f g : MvPowerSeries σ Q} (hf : In N f) (hg : In N g) :
    In N (f + g) := fun α => by
  obtain ⟨a, ha, ea⟩ := hf α
  obtain ⟨b, hb, eb⟩ := hg α
  exact ⟨a + b, N.add_mem ha hb, by rw [map_add, ea, eb, map_add]⟩

theorem in_neg {N : Ideal B} {f : MvPowerSeries σ Q} (hf : In N f) : In N (-f) := fun α => by
  obtain ⟨a, ha, ea⟩ := hf α
  exact ⟨-a, N.neg_mem ha, by rw [map_neg, ea, map_neg]⟩

theorem in_smul {N : Ideal B} {f : MvPowerSeries σ Q} (hf : In N f) (b : B) :
    In N (algebraMap B Q b • f) := fun α => by
  obtain ⟨a, ha, ea⟩ := hf α
  exact ⟨b * a, N.mul_mem_left b ha, by rw [map_smul, smul_eq_mul, ea, ← map_mul]⟩

theorem in_sum {N : Ideal B} {ι : Type} (s : Finset ι) (f : ι → MvPowerSeries σ Q)
    (hf : ∀ i ∈ s, In N (f i)) : In N (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using in_zero (σ := σ) (Q := Q) N
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact in_add (hf a (Finset.mem_insert_self a s))
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

end Integral

section Frob

variable {B Q : Type} [CommRing B] [CommRing Q] [Algebra B Q] (p : ℕ) [hp : Fact p.Prime]
  {σ : Type} [Finite σ] (s : Q →+* Q)

theorem hasSubst_X_pow : HasSubst (fun i : σ => (X i : MvPowerSeries σ Q) ^ p) :=
  HasSubst.X_pow hp.out.ne_zero

theorem frob_add (f g : MvPowerSeries σ Q) : frob p s (f + g) = frob p s f + frob p s g := by
  unfold frob
  rw [map_add, subst_add (hasSubst_X_pow p)]

theorem frob_zero : frob p s (0 : MvPowerSeries σ Q) = 0 := by
  have h := frob_add p s (0 : MvPowerSeries σ Q) 0
  rw [add_zero] at h
  exact left_eq_add.1 h

theorem frob_sub (f g : MvPowerSeries σ Q) : frob p s (f - g) = frob p s f - frob p s g := by
  unfold frob
  rw [map_sub, subst_sub (hasSubst_X_pow p)]

theorem map_smul' {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (r : R)
    (f : MvPowerSeries σ R) : map φ (r • f) = φ r • map φ f := by
  ext α
  rw [coeff_map, MvPowerSeries.coeff_smul, MvPowerSeries.coeff_smul, coeff_map, map_mul]

theorem frob_smul (r : Q) (f : MvPowerSeries σ Q) : frob p s (r • f) = s r • frob p s f := by
  unfold frob
  rw [map_smul', subst_smul (hasSubst_X_pow p)]

theorem frob_sum {ι : Type} (t : Finset ι) (f : ι → MvPowerSeries σ Q) :
    frob p s (∑ i ∈ t, f i) = ∑ i ∈ t, frob p s (f i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using frob_zero p s
  | insert a t ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, frob_add, ih]

theorem frob_comb (σ' : B →+* B) (hs : ∀ b, s (algebraMap B Q b) = algebraMap B Q (σ' b))
    {ι : Type} [Fintype ι] (b : ι → B) (e : ι → MvPowerSeries σ Q) :
    frob p s (comb b e) = comb (fun i => σ' (b i)) fun i => frob p s (e i) := by
  unfold comb
  rw [frob_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [frob_smul, hs]

theorem constantCoeff_frob {f : MvPowerSeries σ Q} (hf : constantCoeff f = 0) :
    constantCoeff (frob p s f) = 0 := by
  unfold frob
  refine constantCoeff_subst_eq_zero (hasSubst_X_pow p) (fun i => ?_) ?_
  · rw [map_pow, constantCoeff_X, zero_pow hp.out.ne_zero]
  · rw [constantCoeff_map, hf, map_zero]

theorem in_frob (σ' : B →+* B) (hs : ∀ b, s (algebraMap B Q b) = algebraMap B Q (σ' b))
    {f : MvPowerSeries σ Q} (hf : In (⊤ : Ideal B) f) : In (⊤ : Ideal B) (frob p s f) := by
  obtain ⟨t, rfl⟩ := (in_top_iff f).1 hf
  refine (in_top_iff _).2 ⟨subst (fun i : σ => (X i : MvPowerSeries σ B) ^ p) (map σ' t), ?_⟩
  have hm : map s (map (algebraMap B Q) t) = map (algebraMap B Q) (map σ' t) := by
    ext α
    simp only [coeff_map, hs]
  unfold frob
  rw [hm, map_subst (HasSubst.X_pow hp.out.ne_zero)]
  simp only [map_pow, map_X]

end Frob

section Cob

theorem map_formalGroupLawCoboundaryOne_eq {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {d : ℕ}
    (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) (h : ∀ i, constantCoeff (μ i) = 0)
    (f : MvPowerSeries (Fin d) R) :
    map φ (cob1 μ f) = cob1 (fun i => map φ (μ i)) (map φ f) := by
  unfold cob1 inL inR
  rw [map_sub, map_sub, map_subst (hasSubst_of_constantCoeff_zero h),
    map_subst (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _),
    map_subst (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _)]
  simp only [map_X]

variable {B Q : Type} [CommRing B] [CommRing Q] [Algebra B Q] {d : ℕ}
  {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B}

theorem constantCoeff_up (hμ : ∀ i, constantCoeff (μ i) = 0) (i : Fin d) :
    constantCoeff (up Q μ i) = 0 := by
  rw [up, constantCoeff_map, hμ, map_zero]

theorem ql_zero (hμ : ∀ i, constantCoeff (μ i) = 0) (N : Ideal B) :
    QL μ N (0 : MvPowerSeries (Fin d) Q) := by
  refine ⟨map_zero _, fun i => ⟨0, N.zero_mem, by simp [lin]⟩, ?_⟩
  have h := formalCoboundary_smul (constantCoeff_up (Q := Q) hμ) (0 : Q) 0
  rw [zero_smul, zero_smul] at h
  rw [h]
  exact in_zero N

theorem ql_add_smul (hμ : ∀ i, constantCoeff (μ i) = 0) {N : Ideal B}
    {f g : MvPowerSeries (Fin d) Q} (hf : QL μ N f) (hg : QL μ N g) (b : B) :
    QL μ N (f + algebraMap B Q b • g) := by
  refine ⟨?_, fun i => ?_, ?_⟩
  · rw [← coeff_zero_eq_constantCoeff_apply, map_add, map_smul, coeff_zero_eq_constantCoeff_apply,
      coeff_zero_eq_constantCoeff_apply, hf.1, hg.1, smul_zero, add_zero]
  · obtain ⟨a, ha, ea⟩ := hf.2.1 i
    obtain ⟨a', ha', ea'⟩ := hg.2.1 i
    refine ⟨a + b * a', N.add_mem ha (N.mul_mem_left b ha'), ?_⟩
    simp only [lin] at ea ea' ⊢
    rw [map_add, map_smul, ea, ea', smul_eq_mul, map_add, map_mul]
  · rw [formalCoboundary_add (constantCoeff_up hμ), formalCoboundary_smul (constantCoeff_up hμ)]
    exact in_add hf.2.2 (in_smul hg.2.2 b)

theorem ql_comb (hμ : ∀ i, constantCoeff (μ i) = 0) {N : Ideal B} {ι : Type} [Fintype ι]
    (e : ι → MvPowerSeries (Fin d) Q) (he : ∀ i, QL μ N (e i)) (b : ι → B) :
    QL μ N (comb b e) := by
  classical
  unfold comb
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty => simpa using ql_zero (Q := Q) hμ N
  | insert a t ha ih =>
    rw [Finset.sum_insert ha, add_comm]
    exact ql_add_smul hμ ih (he a) (b a)

end Cob

end GlobalTheory.QLog.Window
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantCoeffSubstOfForallConstantCoeffZero
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory

theorem constantCoeff_subst_of_constantCoeff_zero :
    ∀ (R : Type) [CommRing R] (σ τ : Type) [Finite σ] (a : σ → MvPowerSeries τ R),
      (∀ i, constantCoeff (a i) = 0) → ∀ g : MvPowerSeries σ R,
        constantCoeff (subst a g) = constantCoeff g := by
  intro R _ σ τ _ a h g
  have ha : HasSubst a := hasSubst_of_constantCoeff_zero h
  have e : g = MvPowerSeries.C (constantCoeff g) + (g - MvPowerSeries.C (constantCoeff g)) := by ring
  conv_lhs => rw [e]
  rw [subst_add ha, map_add, subst_C,
    constantCoeff_subst_eq_zero ha h (f := g - MvPowerSeries.C (constantCoeff g)) (by simp)]
  simp

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffAtPsiOfNotMemZeroSet
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.OTY

theorem contDiffAt_psi_of_notMem_zeroSet : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (L : La) (s : Fin n → ι → Y → ℂ), (∀ k, A.IsSec L (s k)) → ∀ y, y ∉ A.zeroSet s → ∀ i, y ∈ (A.chart i).source → ContDiffAt ℝ ∞ (psi A L s ∘ (A.chart i).symm) (A.chart i y) := by
  intro n Y _ _ _ _ _ ι La _ A L s hs y hy i hi
  have hv : A.chart i y ∈ (A.chart i).target := (A.chart i).map_source hi
  have hU : (A.chart i).target ∈ 𝓝 (A.chart i y) := (A.chart i).open_target.mem_nhds hv
  have hsk : ∀ k, ContDiffAt ℝ ∞ (s k i ∘ (A.chart i).symm) (A.chart i y) := fun k =>
    hyq_contDiffAt_of_holo (A.chart i).open_target (by simpa using (hs k).1 i) hv
  have hph : ContDiffAt ℝ ∞ (A.ph L i ∘ (A.chart i).symm) (A.chart i y) :=
    (A.smooth_ph L i).contDiffAt hU
  have h1 : ContDiffAt ℝ ∞ (fun v => ∑ k, ‖(s k i ∘ (A.chart i).symm) v‖ ^ 2 *
      Real.exp (-(A.ph L i ∘ (A.chart i).symm) v)) (A.chart i y) :=
    ContDiffAt.sum fun k _ => ((hsk k).norm_sq ℂ).mul hph.neg.exp
  have h2 : ContDiffAt ℝ ∞ (A.sqn L s ∘ (A.chart i).symm) (A.chart i y) := by
    refine h1.congr_of_eventuallyEq ?_
    filter_upwards [hU] with v hv'
    simp only [Function.comp, WeightedAtlas.sqn]
    exact Finset.sum_congr rfl fun k _ =>
      WeightedAtlas.nsq_eq_chart A (hs k) ((A.chart i).map_target hv')
  have hpos : 0 < A.sqn L s y := by
    obtain ⟨k, hk⟩ : ∃ k, s k (A.pick y) y ≠ 0 := by
      by_contra h
      exact hy fun k => by_contra fun hk => h ⟨k, hk⟩
    unfold WeightedAtlas.sqn WeightedAtlas.nsq
    refine Finset.sum_pos' (fun _ _ => by positivity) ⟨k, Finset.mem_univ _, ?_⟩
    have := norm_pos_iff.2 hk
    positivity
  have h3 : (A.sqn L s ∘ (A.chart i).symm) (A.chart i y) ≠ 0 := by
    simp only [Function.comp, (A.chart i).left_inv hi]
    exact hpos.ne'
  exact contDiffAt_const.mul (h2.log h3)

end GlobalTheory.OTY
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalPiTensorNoBlockUnipotentFixedStatement
section
open CategoryTheory Polynomial Formalism.IrreducibleCountingLemmas.TYPES Formalism.L2.DIV GlobalTheory.HcIrr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspidal_piTensor_no_blockUnipotent_fixed : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (r s : ℕ) (b : Fin r → Fin s) (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K)), (∀ c, IsCuspidal K (lam c)) → ∀ S : Finset (Fin r), (∃ i j, natBlocks b i = natBlocks b j ∧ i ∈ S ∧ j ∉ S) → ∀ y : PiTensorProduct ℂ (fun c => (lam c : Type)), (∀ u : blockTri (κ := K) (natBlocks b), (∀ i j, ((u : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) i j ≠ (1 : Matrix (Fin r) (Fin r) K) i j → natBlocks b i = natBlocks b j ∧ i ∈ S ∧ j ∉ S) → leviTensor b lam u y = y) → y = 0 := by
  first | exact @GlobalTheory.HcIrr.cuspidal_tensor_no_unip_fixed | exact GlobalTheory.HcIrr.cuspidal_tensor_no_unip_fixed | (intros; apply GlobalTheory.HcIrr.cuspidal_tensor_no_unip_fixed <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CutoffHoloSmoothDbarFormula
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff
namespace GlobalTheory.L2Cutoff

theorem cutoff_smooth_dbar : ∀ (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M], ∀ (X : EtaleStein n M) (ψ : M → ℝ) (G : M → ℂ) (Ω : Set M) (δ b : ℝ) (θ : ℝ → ℝ), SmoothR n X.z ψ → ContDiff ℝ ∞ θ → (∀ t, b ≤ t → θ t = 0) → IsOpen Ω → (∀ e : OpenPartialHomeomorph M (V n), IsChart n X.z e → DifferentiableOn ℂ (G ∘ e.symm) (e.target ∩ e.symm ⁻¹' Ω)) → (∀ x, δ * ψ x ≤ b → x ∈ Ω) → Smooth n X.z (fun x => (θ (δ * ψ x) : ℂ) * G x) ∧ ∀ (x : M) (ξ : Fin n → ℂ), dbarDot n X.z (fun y => (θ (δ * ψ y) : ℂ) * G y) x ξ = ((deriv θ (δ * ψ x) * δ : ℝ) : ℂ) * G x * dbarDot n X.z (fun y => (ψ y : ℂ)) x ξ := by
  intro n M _ _ _ _ _ X ψ G Ω δ b θ hψ hθ hθ0 hΩ hG hsub
  have hψe : ∀ e : OpenPartialHomeomorph M (V n), IsChart n X.z e →
      ContDiffOn ℝ ∞ (fun v => ψ (e.symm v)) e.target := by
    intro e he
    have h1 := (Complex.reCLM.contDiff (n := ∞)).comp_contDiffOn (hψ e he)
    refine h1.congr fun v _ => ?_
    simp
  have hθd : ∀ t, DifferentiableAt ℝ θ t := fun t => (hθ.differentiable (by simp)) t
  have hθzero : ∀ t, b < t → θ =ᶠ[𝓝 t] fun _ => 0 := by
    intro t ht
    filter_upwards [lt_mem_nhds ht] with s hs
    exact hθ0 s hs.le
  have hloc : ∀ e : OpenPartialHomeomorph M (V n), IsChart n X.z e → ∀ v ∈ e.target,
      (e.symm v ∈ Ω → DifferentiableAt ℂ (G ∘ e.symm) v) ∧
      (e.symm v ∉ Ω → ((fun x => (θ (δ * ψ x) : ℂ) * G x) ∘ e.symm) =ᶠ[𝓝 v] fun _ => 0) := by
    intro e he v hv
    constructor
    · intro hvΩ
      exact (hG e he).differentiableAt
        ((e.isOpen_inter_preimage_symm hΩ).mem_nhds ⟨hv, hvΩ⟩)
    · intro hvΩ
      have hb : b < δ * ψ (e.symm v) := by
        by_contra h
        exact hvΩ (hsub _ (not_lt.1 h))
      have hc : ContinuousAt (fun w => δ * ψ (e.symm w)) v :=
        continuousAt_const.mul ((hψe e he).continuousOn.continuousAt (e.open_target.mem_nhds hv))
      filter_upwards [hc.eventually (lt_mem_nhds hb)] with w hw
      simp [hθ0 _ hw.le]
  refine ⟨?_, ?_⟩
  · intro e he v hv
    apply ContDiffAt.contDiffWithinAt
    by_cases hvΩ : e.symm v ∈ Ω
    · have hU := (e.isOpen_inter_preimage_symm hΩ).mem_nhds ⟨hv, hvΩ⟩
      have hGc : ContDiffAt ℝ ∞ (G ∘ e.symm) v :=
        ((contDiffOn_of_differentiableOn n _ _ (e.isOpen_inter_preimage_symm hΩ) (hG e he)).contDiffAt
          hU).restrict_scalars ℝ
      have hk : ContDiffAt ℝ ∞ (fun w => ((θ (δ * ψ (e.symm w)) : ℝ) : ℂ)) v :=
        Complex.ofRealCLM.contDiff.contDiffAt.comp v
          (hθ.contDiffAt.comp v (contDiffAt_const.mul
            ((hψe e he).contDiffAt (e.open_target.mem_nhds hv))))
      exact hk.mul hGc
    · exact contDiffAt_const.congr_of_eventuallyEq ((hloc e he v hv).2 hvΩ)
  · intro x ξ
    obtain ⟨e, he, hx⟩ := exists_chart n X.z X.isLocalHomeomorph x
    have hzx : X.z x = e x := he hx
    have hv : X.z x ∈ e.target := by rw [hzx]; exact e.map_source hx
    have hsx : e.symm (X.z x) = x := by rw [hzx]; exact e.left_inv hx
    unfold dbarDot
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [db_eq_wdb n X.z e he j _ x hx, db_eq_wdb n X.z e he j _ x hx]
    by_cases hxΩ : x ∈ Ω
    · have hGd := (hloc e he _ hv).1 (by rw [hsx]; exact hxΩ)
      have hψd : DifferentiableAt ℝ (fun w => ψ (e.symm w)) (X.z x) :=
        ((hψe e he).contDiffAt (e.open_target.mem_nhds hv)).differentiableAt (by simp)
      have hkd : DifferentiableAt ℝ (fun t => θ (δ * t)) (ψ (e.symm (X.z x))) :=
        (hθd _).comp _ ((differentiableAt_id).const_mul δ)
      have hderiv : deriv (fun t => θ (δ * t)) (ψ (e.symm (X.z x))) =
          deriv θ (δ * ψ (e.symm (X.z x))) * δ := by
        have h1 : HasDerivAt (fun t : ℝ => δ * t) δ (ψ (e.symm (X.z x))) := by
          simpa using (hasDerivAt_id (ψ (e.symm (X.z x)))).const_mul δ
        exact ((hθd _).hasDerivAt.comp _ h1).deriv
      have h1 : ((fun y => (θ (δ * ψ y) : ℂ) * G y) ∘ e.symm) =
          fun w => (((fun t => θ (δ * t)) (ψ (e.symm w)) : ℝ) : ℂ) * (G ∘ e.symm) w := rfl
      have hkd' : DifferentiableAt ℝ (fun w => (((fun t => θ (δ * t)) (ψ (e.symm w)) : ℝ) : ℂ))
          (X.z x) := differentiableAt_ofReal (DifferentiableAt.comp (f := fun w => ψ (e.symm w)) (X.z x) hkd hψd)
      rw [h1, wdb_mul hkd' (hGd.restrictScalars ℝ), wdb_of_differentiableAt hGd,
        wdb_ofReal_comp (k := fun t => θ (δ * t)) (v := fun w => ψ (e.symm w)) hkd hψd, hderiv]
      have h2 : ((fun y => (ψ y : ℂ)) ∘ e.symm) = fun w => ((ψ (e.symm w) : ℝ) : ℂ) := rfl
      rw [h2]
      simp only [Function.comp_apply, hsx]
      push_cast
      ring
    · have hb : b < δ * ψ x := by
        by_contra h
        exact hxΩ (hsub _ (not_lt.1 h))
      rw [wdb_congr ((hloc e he _ hv).2 (by rw [hsx]; exact hxΩ)),
        ((hθzero _ hb).deriv_eq)]
      simp [wdb]

end GlobalTheory.L2Cutoff
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarEnergyOnCoverBallsLtTopOfSmooth
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory

theorem n1_lt_infty_of_isSSec : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (C : Cover A) (la : La) (F0 : ι → Y → ℂ), A.IsSSec (A.kap + la) F0 → n1 C la F0 < ⊤ := by
  intro n Y _ _ _ _ _ ι La _ A C la F0 hF
  unfold n1
  rw [ENNReal.sum_lt_top]
  intro a _
  set i := C.idx a
  set T := (A.chart i).target
  have hT : IsOpen T := (A.chart i).open_target
  have hsub : closedBall (C.c a) (C.r a) ⊆ T := C.sub a
  have hF' : ContDiffOn ℝ ∞ (F0 i ∘ (A.chart i).symm) T := hF.1 i
  have hD : ContinuousOn (fun v => fderiv ℝ (F0 i ∘ (A.chart i).symm) v) T :=
    hF'.continuousOn_fderiv_of_isOpen hT (by simp)
  have hph : ContinuousOn (fun v => A.ph la i ((A.chart i).symm v)) T :=
    (A.smooth_ph la i).continuousOn
  have hcont : ContinuousOn (fun v => (∑ j, ‖wdb n j (F0 i ∘ (A.chart i).symm) v‖ ^ 2) *
      Real.exp (-A.ph la i ((A.chart i).symm v))) (closedBall (C.c a) (C.r a)) := by
    refine ContinuousOn.mono ?_ hsub
    refine ContinuousOn.mul ?_ ?_
    · refine continuousOn_finset_sum _ (fun j _ => ?_)
      refine ContinuousOn.pow (ContinuousOn.norm ?_) 2
      unfold wdb
      refine ContinuousOn.div_const (ContinuousOn.add ?_ (ContinuousOn.mul continuousOn_const ?_)) _
      · exact hD.clm_apply continuousOn_const
      · exact hD.clm_apply continuousOn_const
    · exact (hph.neg).rexp
  have hint : IntegrableOn (fun v => (∑ j, ‖wdb n j (F0 i ∘ (A.chart i).symm) v‖ ^ 2) *
      Real.exp (-A.ph la i ((A.chart i).symm v))) (closedBall (C.c a) (C.r a)) :=
    hcont.integrableOn_compact (isCompact_closedBall _ _)
  calc _ ≤ ∫⁻ v in closedBall (C.c a) (C.r a), ENNReal.ofReal
        ((∑ j, ‖wdb n j (F0 i ∘ (A.chart i).symm) v‖ ^ 2) *
          Real.exp (-A.ph la i ((A.chart i).symm v))) :=
        lintegral_mono_set ball_subset_closedBall
    _ < ⊤ := hint.lintegral_lt_top

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarGlueSectionByPartitionEq
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory

theorem glue_wdb_eq : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (C : Cover A) (la : La) (u : Fin C.m → V n → ℂ) (i : ι) (v : V n) (w : ℂ) (j : Fin n), (∀ a, DifferentiableOn ℂ (u a) (ball (C.c a) (C.r a))) → v ∈ (A.chart i).target → wdb n j (glue C la u i ∘ (A.chart i).symm) v = ∑ a, wdb n j (fun x => (C.chi a ((A.chart i).symm x) : ℂ)) v * (A.g (A.kap + la) i (C.idx a) ((A.chart i).symm v) * u a (A.chart (C.idx a) ((A.chart i).symm v)) - w) := by
  intro n Y _ _ _ _ _ ι La _ A C la u i v w j hu hv
  have hopen : IsOpen (A.chart i).target := (A.chart i).open_target
  have hchi : ∀ a, DifferentiableAt ℝ (fun x => (C.chi a ((A.chart i).symm x) : ℂ)) v := by
    intro a
    have h1 : ContDiffOn ℝ ∞ (C.chi a ∘ (A.chart i).symm) (A.chart i).target := C.smooth a i
    have h2 : DifferentiableAt ℝ (C.chi a ∘ (A.chart i).symm) v :=
      (h1.contDiffAt (hopen.mem_nhds hv)).differentiableAt (by simp)
    exact ReciprocityTheory.L2DbarEstimates.differentiableAt_ofReal h2
  have key : ∀ a, DifferentiableAt ℝ (fun x => (C.chi a ((A.chart i).symm x) : ℂ) *
        A.g (A.kap + la) i (C.idx a) ((A.chart i).symm x) *
        u a (A.chart (C.idx a) ((A.chart i).symm x))) v ∧
      wdb n j (fun x => (C.chi a ((A.chart i).symm x) : ℂ) *
        A.g (A.kap + la) i (C.idx a) ((A.chart i).symm x) *
        u a (A.chart (C.idx a) ((A.chart i).symm x))) v =
      wdb n j (fun x => (C.chi a ((A.chart i).symm x) : ℂ)) v *
        (A.g (A.kap + la) i (C.idx a) ((A.chart i).symm v) *
          u a (A.chart (C.idx a) ((A.chart i).symm v))) := by
    intro a
    by_cases hs : (A.chart i).symm v ∈ tsupport (C.chi a)
    · have hsrc := (C.supp a hs).1
      have hball : A.chart (C.idx a) ((A.chart i).symm v) ∈ ball (C.c a) (C.r a) := (C.supp a hs).2
      have hovl : IsOpen (ovl A.chart i (C.idx a)) :=
        (A.chart i).isOpen_inter_preimage_symm (A.chart (C.idx a)).open_source
      have hmem : v ∈ ovl A.chart i (C.idx a) := ⟨hv, hsrc⟩
      have hg : DifferentiableAt ℂ (A.g (A.kap + la) i (C.idx a) ∘ (A.chart i).symm) v :=
        (A.holo_g _ i (C.idx a)).differentiableAt (hovl.mem_nhds hmem)
      have htr : DifferentiableAt ℂ (A.chart (C.idx a) ∘ (A.chart i).symm) v :=
        (A.holo_trans i (C.idx a)).differentiableAt (hovl.mem_nhds hmem)
      have hua : DifferentiableAt ℂ (u a) (A.chart (C.idx a) ((A.chart i).symm v)) :=
        (hu a).differentiableAt (isOpen_ball.mem_nhds hball)
      have hh : DifferentiableAt ℂ (fun x => A.g (A.kap + la) i (C.idx a) ((A.chart i).symm x) *
          u a (A.chart (C.idx a) ((A.chart i).symm x))) v :=
        hg.mul (hua.comp v htr)
      have heq : (fun x => (C.chi a ((A.chart i).symm x) : ℂ) *
          A.g (A.kap + la) i (C.idx a) ((A.chart i).symm x) *
          u a (A.chart (C.idx a) ((A.chart i).symm x))) =
          (fun x => (C.chi a ((A.chart i).symm x) : ℂ) *
          (A.g (A.kap + la) i (C.idx a) ((A.chart i).symm x) *
          u a (A.chart (C.idx a) ((A.chart i).symm x)))) := by
        funext x; ring
      rw [heq]
      refine ⟨(hchi a).mul (hh.restrictScalars ℝ), ?_⟩
      rw [ReciprocityTheory.L2DbarEstimates.wdb_mul (hchi a) (hh.restrictScalars ℝ),
        ReciprocityTheory.L2DbarEstimates.wdb_of_differentiableAt hh]
      ring
    · have hn : (A.chart i).symm ⁻¹' (tsupport (C.chi a))ᶜ ∈ 𝓝 v :=
        ((A.chart i).continuousAt_symm hv).preimage_mem_nhds
          ((isClosed_tsupport _).isOpen_compl.mem_nhds hs)
      have hz : ∀ᶠ x in 𝓝 v, C.chi a ((A.chart i).symm x) = 0 :=
        Filter.mem_of_superset hn fun x hx => image_eq_zero_of_notMem_tsupport hx
      have hf0 : (fun x => (C.chi a ((A.chart i).symm x) : ℂ) *
          A.g (A.kap + la) i (C.idx a) ((A.chart i).symm x) *
          u a (A.chart (C.idx a) ((A.chart i).symm x))) =ᶠ[𝓝 v] fun _ => (0 : ℂ) :=
        hz.mono fun x hx => by simp [hx]
      have hc0 : (fun x => (C.chi a ((A.chart i).symm x) : ℂ)) =ᶠ[𝓝 v] fun _ => (0 : ℂ) :=
        hz.mono fun x hx => by simp [hx]
      have hw0 : wdb n j (fun _ : V n => (0 : ℂ)) v = 0 :=
        ReciprocityTheory.L2DbarEstimates.wdb_of_differentiableAt (differentiableAt_const _)
      refine ⟨(differentiableAt_const (0 : ℂ)).congr_of_eventuallyEq hf0, ?_⟩
      rw [ReciprocityTheory.L2DbarEstimates.wdb_congr hf0, ReciprocityTheory.L2DbarEstimates.wdb_congr hc0, hw0, zero_mul]
  have hglue : glue C la u i ∘ (A.chart i).symm = fun x => ∑ a, (C.chi a ((A.chart i).symm x) : ℂ) *
        A.g (A.kap + la) i (C.idx a) ((A.chart i).symm x) *
        u a (A.chart (C.idx a) ((A.chart i).symm x)) := by
    funext x; rfl
  have hone : (fun x => ∑ a, (C.chi a ((A.chart i).symm x) : ℂ)) = fun _ : V n => (1 : ℂ) := by
    funext x; rw [← Complex.ofReal_sum, C.sum_one]; simp
  have hsum0 : ∑ a, wdb n j (fun x => (C.chi a ((A.chart i).symm x) : ℂ)) v = 0 := by
    rw [← ReciprocityTheory.L2DbarEstimates.wdb_sum Finset.univ (fun a _ => hchi a), hone]
    exact ReciprocityTheory.L2DbarEstimates.wdb_of_differentiableAt (differentiableAt_const _)
  rw [hglue, ReciprocityTheory.L2DbarEstimates.wdb_sum Finset.univ (fun a _ => (key a).1)]
  simp_rw [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hsum0, zero_mul, sub_zero]
  exact Finset.sum_congr rfl fun a _ => (key a).2

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffCoeffsInIdealTopPowerSeriesLog
section
set_option autoImplicit false

open MvPowerSeries GlobalTheory GlobalTheory.QLog

namespace GlobalTheory.QLog.LogDiff

theorem dIn_log : ∀ (B Q : Type) [CommRing B] [CommRing Q] [Algebra B Q] [Algebra ℚ Q],
    DIn (⊤ : Ideal B) (PowerSeries.log Q : MvPowerSeries Unit Q) := by
  intro B Q _ _ _ _ α i
  have hc : MvPowerSeries.coeff α (PowerSeries.log Q : MvPowerSeries Unit Q) =
      PowerSeries.coeff (α i) (PowerSeries.log Q) := by
    rw [PowerSeries.coeff_def (s := α) (n := α i) rfl]
  rw [hc, PowerSeries.coeff_log]
  by_cases h : α i = 0
  · exact ⟨0, trivial, by simp [h]⟩
  · refine ⟨(-1) ^ (α i + 1), trivial, ?_⟩
    have h' : ((α i : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.2 h
    rw [if_neg h, ← map_natCast (algebraMap ℚ Q), ← map_mul, mul_div_cancel₀ _ h']
    simp

end GlobalTheory.QLog.LogDiff
end

