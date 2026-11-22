import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Mathlib
import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import ReciprocityTheory.L2DbarEstimates.LeviForms.Bundle0002
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0646
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0064
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
import Development.AbelianVarietyTheory.Counterexamples.AbelianLawCounterexamples.WeilIsUniqueOfLocal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0604
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0640
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0635

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPDivGroupChartLevelOneNilpotentModP
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.AugNil

theorem aeval_mem_span {A R : Type} [CommRing A] [CommRing R] [Algebra R A] {d : ℕ}
    (x : Fin d → A) (P : MvPolynomial (Fin d) R) (h0 : MvPolynomial.constantCoeff P = 0) :
    MvPolynomial.aeval x P ∈ Ideal.span (Set.range x) := by
  classical
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq]
  refine Ideal.sum_mem _ fun m hm => ?_
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact (MvPolynomial.mem_support_iff.1 hm) (by rwa [MvPolynomial.constantCoeff_eq] at h0)
  obtain ⟨i, hi⟩ : ∃ i, m i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hm0 (Finsupp.ext h)
  refine Ideal.mul_mem_left _ _ ?_
  have hdvd : x i ∣ ∏ j ∈ m.support, x j ^ m j :=
    (dvd_pow_self (x i) hi).trans (Finset.dvd_prod_of_mem _ (Finsupp.mem_support_iff.2 hi))
  obtain ⟨c, hc⟩ := hdvd
  rw [hc]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨i, rfl⟩)

theorem dvd_pow_of_mem_span {A : Type} [CommRing A] {d : ℕ} (x : Fin d → A) (p : A) (N₀ : ℕ)
    (hx : ∀ i, p ∣ x i ^ N₀) (a : A) (ha : a ∈ Ideal.span (Set.range x)) :
    p ∣ a ^ (d * N₀ + 1) := by
  obtain ⟨r, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun A).1 ha
  have h := Ideal.sum_pow_mem_span_pow Finset.univ (fun i => r i • x i) N₀
  rw [Finset.card_univ, Fintype.card_fin] at h
  rw [← Ideal.mem_span_singleton]
  refine Ideal.span_le.2 ?_ h
  rintro _ ⟨i, -, rfl⟩
  rw [SetLike.mem_coe, Ideal.mem_span_singleton]
  simp only [smul_eq_mul, mul_pow]
  exact Dvd.dvd.mul_left ((hx i).trans (pow_dvd_pow _ (Nat.le_succ _))) _

theorem aug_nil : ∀ (p : ℕ) (O : Type) [CommRing O] (G : PDivGroup p O) (d : ℕ)
    (c : QLog.Chart G d), ∃ N : ℕ, ∀ f : MvPowerSeries (Fin d) O, constantCoeff f = 0 →
      (p : G.A 1) ∣ c.ev 1 f ^ N := by
  intro p O _ G d c
  classical
  choose Ni hNi using c.nil 1
  let N₀ := Finset.univ.sup Ni
  have hx : ∀ i, (p : G.A 1) ∣ c.x 1 i ^ N₀ := fun i =>
    (hNi i).trans (pow_dvd_pow _ (Finset.le_sup (Finset.mem_univ i)))
  obtain ⟨N₁, hN₁⟩ := (c.isEval 1).2 1
  refine ⟨d * N₀ + 1, fun f hf => ?_⟩
  set P := trunc' O (Finsupp.equivFunOnFinite.symm fun _ => N₁) f with hPdef
  have hR : (p : G.A 1) ∣ c.ev 1 (f - (P : MvPowerSeries (Fin d) O)) := by
    have h := hN₁ (f - P) (fun α hα => ?_)
    · simpa using h
    rw [map_sub, MvPolynomial.coeff_coe, coeff_trunc', if_pos, sub_self]
    intro i
    have : α i ≤ α.degree := by
      rw [Finsupp.degree]
      by_cases hi : α i = 0
      · rw [hi]; exact Nat.zero_le _
      · exact Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finsupp.mem_support_iff.2 hi)
    simpa using this.trans hα.le
  have hP : c.ev 1 (P : MvPowerSeries (Fin d) O) = MvPolynomial.aeval (c.x 1) P := by
    have : (c.ev 1).comp (MvPolynomial.coeToMvPowerSeries.algHom O) = MvPolynomial.aeval (c.x 1) :=
      MvPolynomial.algHom_ext fun i => by simp [(c.isEval 1).1 i]
    exact congrArg (fun φ => φ P) this
  have hP0 : MvPolynomial.constantCoeff P = 0 := by
    rw [MvPolynomial.constantCoeff_eq, hPdef, coeff_trunc', if_pos (zero_le')]
    simpa using hf
  have ha := dvd_pow_of_mem_span (c.x 1) (p : G.A 1) N₀ hx _ (aeval_mem_span (c.x 1) P hP0)
  rw [← hP] at ha
  have hsub := sub_dvd_pow_sub_pow (c.ev 1 f) (c.ev 1 P) (d * N₀ + 1)
  rw [← map_sub] at hsub
  simpa using dvd_add (hR.trans hsub) ha

end GlobalTheory.AugNil
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothCutoffSlopeThreeQuarters
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory

theorem exists_isCut (T : ℝ) : ∃ θ : ℝ → ℝ, IsCut T θ := by
  obtain ⟨χ, hχ⟩ : ∃ χ : ℝ → ℝ, ReciprocityTheory.L2DbarEstimates.I.IsCutoff χ :=
    ⟨_, ReciprocityTheory.L2DbarEstimates.I.SmoothCutoff.isCutoff_chi⟩
  obtain ⟨hs, h1, h0, hb, hd⟩ := hχ
  set a : ℝ → ℝ := fun x => (x + T + 1) / 4 + 1 / 2 with ha
  have haS : ContDiff ℝ ∞ a := by
    simp only [ha]; fun_prop
  have hda : ∀ x, HasDerivAt a (1 / 4) x := by
    intro x
    have := (((hasDerivAt_id x).add_const T).add_const 1).div_const 4
    simpa [ha] using this.add_const (1 / 2)
  refine ⟨χ ∘ a, ?_, ?_, ?_, ?_, ?_⟩
  · exact hs.comp haS
  · intro x hx
    exact h1 _ (by simp only [ha]; linarith)
  · intro x hx
    exact h0 _ (by simp only [ha]; linarith)
  · intro x
    exact hb _
  · intro x
    have hχd : DifferentiableAt ℝ χ (a x) :=
      (hs.differentiable (by simp)) _
    have hD : HasDerivAt (χ ∘ a) (deriv χ (a x) * (1 / 4)) x :=
      hχd.hasDerivAt.comp x (hda x)
    rw [hD.deriv, abs_mul]
    have := hd (a x)
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)]
    linarith

theorem exists_isCut₂ : ∀ T : ℝ, ∃ θ : ℝ → ℝ, IsCut T θ := exists_isCut

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTiltAutomorphismTransport
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

noncomputable section
namespace GlobalTheory.GammaAct

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (Ideal.span {(p : O)}) O]

def wittEquiv (G : PreTilt O p ≃+* PreTilt O p) : Ainf p O ≃+* Ainf p O :=
  RingEquiv.ofRingHom (WittVector.map (G : PreTilt O p →+* PreTilt O p))
    (WittVector.map (G.symm : PreTilt O p →+* PreTilt O p))
    (by ext x n; simp [WittVector.map_coeff])
    (by ext x n; simp [WittVector.map_coeff])

theorem wittEquiv_apply (G : PreTilt O p ≃+* PreTilt O p) (a : Ainf p O) :
    wittEquiv G a = WittVector.map (G : PreTilt O p →+* PreTilt O p) a := rfl

theorem wittEquiv_ofPadic (G : PreTilt O p ≃+* PreTilt O p) (x : ℤ_[p]) :
    wittEquiv G (ofPadic p O x) = ofPadic p O x := by
  rw [wittEquiv_apply, ofPadic, RingHom.comp_apply]
  generalize (WittVector.equiv p).symm.toRingHom x = y
  ext n
  simp only [WittVector.map_coeff]
  exact congrArg (fun f : ZMod p →+* PreTilt O p => f (y.coeff n))
    (RingHom.ext_zmod ((G : PreTilt O p →+* PreTilt O p).comp (ZMod.castHom (dvd_refl p) _)) _)

theorem frob_symm_comm (G : PreTilt O p ≃+* PreTilt O p) (x : PreTilt O p) :
    G ((_root_.frobeniusEquiv (PreTilt O p) p).symm x) =
      (_root_.frobeniusEquiv (PreTilt O p) p).symm (G x) := by
  apply (_root_.frobeniusEquiv (PreTilt O p) p).injective
  rw [RingEquiv.apply_symm_apply, frobeniusEquiv_apply, frobenius_def, ← map_pow,
    ← frobenius_def, ← frobeniusEquiv_apply, RingEquiv.apply_symm_apply]

theorem wittEquiv_phiInv (G : PreTilt O p ≃+* PreTilt O p) (a : Ainf p O) :
    wittEquiv G (phiInv p O a) = phiInv p O (wittEquiv G a) := by
  ext n
  simp [wittEquiv_apply, phiInv, WittVector.map_coeff, frob_symm_comm]

theorem wittEquiv_teich (G : PreTilt O p ≃+* PreTilt O p) (x : PreTilt O p) :
    wittEquiv G (WittVector.teichmuller p x) = WittVector.teichmuller p (G x) := by
  rw [wittEquiv_apply, WittVector.map_teichmuller]; rfl

end GlobalTheory.GammaAct

namespace GlobalTheory.GammaAct

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (Ideal.span {(p : O)}) O]

def wittAlgEquiv (G : PreTilt O p ≃+* PreTilt O p) : Ainf p O ≃ₐ[ℤ_[p]] Ainf p O :=
  AlgEquiv.ofRingEquiv (f := wittEquiv G) (fun x => wittEquiv_ofPadic G x)

variable (Λ : Type) [CommRing Λ] [Algebra ℤ_[p] Λ]

def tensorEquiv (G : PreTilt O p ≃+* PreTilt O p) : RL p O Λ ≃+* RL p O Λ :=
  (Algebra.TensorProduct.congr (wittAlgEquiv G) (AlgEquiv.refl : Λ ≃ₐ[ℤ_[p]] Λ)).toRingEquiv

theorem tensorEquiv_tmul (G : PreTilt O p ≃+* PreTilt O p) (a : Ainf p O) (l : Λ) :
    tensorEquiv Λ G (a ⊗ₜ l) = wittEquiv G a ⊗ₜ l := rfl

theorem tensorEquiv_symm_tmul (G : PreTilt O p ≃+* PreTilt O p) (a : Ainf p O) (l : Λ) :
    (tensorEquiv Λ G).symm (a ⊗ₜ l) = (wittEquiv G).symm a ⊗ₜ l := rfl

end GlobalTheory.GammaAct

namespace GlobalTheory.GammaAct

section
variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (Ideal.span {(p : O)}) O]

theorem map_root (G : PreTilt O p ≃+* PreTilt O p) (ε : PreTilt O p) :
    G (root ε) = root (G ε) := frob_symm_comm G ε

theorem wittEquiv_xi (G : PreTilt O p ≃+* PreTilt O p) (ε : PreTilt O p) :
    wittEquiv G (xi ε) = xi (G ε) := by
  simp only [xi, map_sum, map_pow, wittEquiv_teich, map_root]

theorem wittEquiv_mu (G : PreTilt O p ≃+* PreTilt O p) (ε : PreTilt O p) :
    wittEquiv G (mu ε) = mu (G ε) := by
  simp only [mu, map_sub, map_one, wittEquiv_teich]

theorem tensorEquiv_inA (Λ : Type) [CommRing Λ] [Algebra ℤ_[p] Λ]
    (G : PreTilt O p ≃+* PreTilt O p) (a : Ainf p O) :
    tensorEquiv Λ G (inA a) = inA (wittEquiv G a) := rfl

end

theorem exists_tensor_action : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (ε : PreTilt O p) (Λ : Type) [CommRing Λ] [Algebra ℤ_[p] Λ] (ψ : RL p O Λ →+* RL p O Λ) (γ : O ≃+* O), IsPsi ψ → IsPrimitiveRoot (root ε).untilt p → ∃ (Γ : RL p O Λ ≃+* RL p O Λ) (ε' : PreTilt O p), IsPrimitiveRoot (root ε').untilt p ∧ Γ (inA (xi ε)) = inA (xi ε') ∧ Γ (inA (mu ε)) = inA (mu ε') ∧ (∀ r, Γ (ψ r) = ψ (Γ r)) ∧ ∀ (σ : Λ →+* O) (f : RL p O Λ →+* O), IsTheta σ f → ∃ f', IsTheta ((γ : O →+* O).comp σ) f' ∧ ∀ r, f' (Γ r) = γ (f r) := by
  intro p _ O _ _ _ ε Λ _ _ ψ γ hψ hε
  obtain ⟨G, hu, hθ⟩ := GlobalTheory.T.tilt_lift_of_ring_automorphism p O γ
  refine ⟨tensorEquiv Λ G, G ε, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← map_root, hu]
    exact hε.map_of_injective γ.injective
  · rw [tensorEquiv_inA, wittEquiv_xi]
  · rw [tensorEquiv_inA, wittEquiv_mu]
  · intro r
    induction r using TensorProduct.induction_on with
    | zero => simp
    | tmul a l => rw [hψ, tensorEquiv_tmul, tensorEquiv_tmul, hψ, wittEquiv_phiInv]
    | add x y hx hy => simp only [map_add, hx, hy]
  · intro σ f hf
    refine ⟨((γ : O →+* O).comp f).comp ((tensorEquiv Λ G).symm : RL p O Λ →+* RL p O Λ),
      fun a l => ?_, fun r => by simp⟩
    have h := hθ ((wittEquiv G).symm a)
    rw [← wittEquiv_apply, RingEquiv.apply_symm_apply] at h
    show γ (f ((tensorEquiv Λ G).symm (a ⊗ₜ l))) = _ * γ (σ l)
    rw [tensorEquiv_symm_tmul, hf, map_mul, h]

end GlobalTheory.GammaAct
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTruncationCongrOfPadicContinuousEvalEqZero
section
open GlobalTheory.QLog

namespace GlobalTheory

theorem evalPoly_eq {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {d : ℕ}
    (x : Fin d → A) (E : MvPowerSeries (Fin d) O →ₐ[O] A) (hX : ∀ i, E (MvPowerSeries.X i) = x i)
    (P : MvPolynomial (Fin d) O) : E (P : MvPowerSeries (Fin d) O) = MvPolynomial.aeval x P := by
  have key : E.comp (MvPolynomial.coeToMvPowerSeries.algHom O) = MvPolynomial.aeval x :=
    MvPolynomial.algHom_ext fun i => by simp [hX]
  have := congrArg (fun F : MvPolynomial (Fin d) O →ₐ[O] A => F P) key
  simpa using this

theorem aeval_monomial_mem_span_pow {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {d : ℕ}
    (x : Fin d → A) (N : ℕ) (α : Fin d →₀ ℕ) (hα : N ≤ α.degree) (c : O) :
    MvPolynomial.aeval x (MvPolynomial.monomial α c) ∈ Ideal.span (Set.range x) ^ N := by
  rw [MvPolynomial.aeval_monomial]
  refine Ideal.mul_mem_left _ _ (Ideal.pow_le_pow_right hα ?_)
  rw [Finsupp.degree_apply, ← Finset.prod_pow_eq_pow_sum]
  exact Ideal.prod_mem_prod fun i _ => Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_range_self i)) _

end GlobalTheory

namespace GlobalTheory

theorem trunc_dec : ∀ (p : ℕ) (O A : Type) [CommRing O] [CommRing A] [Algebra O A] (d : ℕ) (x : Fin d → A) (E : MvPowerSeries (Fin d) O →ₐ[O] A), IsEval p x E → ∀ (n N : ℕ) (f : MvPowerSeries (Fin d) O), E f = 0 → ∃ P : MvPolynomial (Fin d) O, (∀ α : Fin d →₀ ℕ, N ≤ α.degree → MvPolynomial.coeff α P = 0) ∧ (∀ α : Fin d →₀ ℕ, α.degree < N → MvPolynomial.coeff α P = MvPowerSeries.coeff α f) ∧ MvPolynomial.aeval x P ∈ Ideal.span (Set.range x) ^ N ⊔ Ideal.span {(p : A) ^ n} := by
  intro p O A _ _ _ d x E hE n N f hf
  obtain ⟨hX, hc⟩ := hE
  obtain ⟨M, hM⟩ := hc n
  classical
  set F : Finset (Fin d →₀ ℕ) := Finset.Iic (Finsupp.equivFunOnFinite.symm fun _ => max N M) with hF
  have memF : ∀ α : Fin d →₀ ℕ, α.degree < max N M → α ∈ F := by
    intro α h
    rw [hF, Finset.mem_Iic]
    intro i
    simpa using (Finsupp.le_degree i α).trans h.le
  set P : MvPolynomial (Fin d) O :=
    ∑ α ∈ F.filter (fun α => α.degree < N), MvPolynomial.monomial α (MvPowerSeries.coeff α f) with hP
  set Q : MvPolynomial (Fin d) O :=
    ∑ α ∈ F.filter (fun α => ¬ α.degree < N), MvPolynomial.monomial α (MvPowerSeries.coeff α f) with hQ
  have cP : ∀ β, MvPolynomial.coeff β P = if β ∈ F ∧ β.degree < N then MvPowerSeries.coeff β f else 0 := by
    intro β
    rw [hP, MvPolynomial.coeff_sum]
    simp only [MvPolynomial.coeff_monomial]
    rw [Finset.sum_ite_eq' (F.filter _) β]
    simp only [Finset.mem_filter]
  have cQ : ∀ β, MvPolynomial.coeff β Q = if β ∈ F ∧ ¬ β.degree < N then MvPowerSeries.coeff β f else 0 := by
    intro β
    rw [hQ, MvPolynomial.coeff_sum]
    simp only [MvPolynomial.coeff_monomial]
    rw [Finset.sum_ite_eq' (F.filter _) β]
    simp only [Finset.mem_filter]
  refine ⟨P, ?_, ?_, ?_⟩
  · intro α hα
    rw [cP, if_neg]
    omega
  · intro α hα
    rw [cP, if_pos ⟨memF α (lt_of_lt_of_le hα (le_max_left _ _)), hα⟩]
  · have hrest : (p : A) ^ n ∣ E (f - (P : MvPowerSeries (Fin d) O) - (Q : MvPowerSeries (Fin d) O)) := by
      apply hM
      intro α hα
      have hαF := memF α (lt_of_lt_of_le hα (le_max_right _ _))
      rw [map_sub, map_sub, MvPolynomial.coeff_coe, MvPolynomial.coeff_coe, cP, cQ]
      by_cases h : α.degree < N
      · simp [hαF, h]
      · simp [hαF, h]
    have hQmem : MvPolynomial.aeval x Q ∈ Ideal.span (Set.range x) ^ N := by
      rw [hQ, map_sum]
      refine Ideal.sum_mem _ fun α hα => aeval_monomial_mem_span_pow x N α ?_ _
      exact not_lt.1 (Finset.mem_filter.1 hα).2
    have hsplit : MvPolynomial.aeval x P = -(MvPolynomial.aeval x Q) -
        E (f - (P : MvPowerSeries (Fin d) O) - (Q : MvPowerSeries (Fin d) O)) := by
      rw [map_sub, map_sub, hf, evalPoly_eq x E hX, evalPoly_eq x E hX]
      ring
    rw [hsplit]
    refine Ideal.sub_mem _ ((Ideal.neg_mem_iff _).2 (Ideal.mem_sup_left hQmem)) (Ideal.mem_sup_right ?_)
    exact Ideal.mem_span_singleton.2 hrest

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformConvolutionPowApplyMemLocalDual
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.LawDer

namespace GlobalTheory.LocalDualNil

theorem exists_pow_mem_map {O R : Type*} [CommRing O] [CommRing R] [Algebra O R]
    [Module.Finite O R] [IsLocalRing R] (ε : R →ₐ[O] O) (m : Ideal O) (hm : m.IsMaximal) :
    ∃ r : ℕ, ∀ φ : R, ε φ ∈ m → ∀ s, r ≤ s → φ ^ s ∈ m.map (algebraMap O R) := by
  set J : Ideal R := m.map (algebraMap O R) with hJ
  by_cases htop : J = ⊤
  · exact ⟨0, fun φ _ s _ => htop ▸ Submodule.mem_top⟩
  letI : Field (O ⧸ m) := Ideal.Quotient.field m
  haveI : Nontrivial (R ⧸ J) := Ideal.Quotient.nontrivial_iff.2 htop
  haveI : IsLocalRing (R ⧸ J) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  haveI : Module.Finite (O ⧸ m) (R ⧸ J) := Module.Finite.of_restrictScalars_finite O _ _
  haveI : IsArtinianRing (R ⧸ J) := IsArtinianRing.of_finite (O ⧸ m) _
  obtain ⟨r, hr⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := R ⧸ J)
  rw [IsLocalRing.jacobson_eq_maximalIdeal _ bot_ne_top] at hr
  haveI : IsLocalHom (Ideal.Quotient.mk J) :=
    IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  refine ⟨r, fun φ hφ s hs => ?_⟩
  have h1 : ¬ IsUnit φ := fun h => hm.ne_top (Ideal.eq_top_of_isUnit_mem _ hφ (h.map ε))
  have h2 : Ideal.Quotient.mk J φ ∈ IsLocalRing.maximalIdeal (R ⧸ J) :=
    fun h => h1 (isUnit_of_map_unit _ _ h)
  have h3 := Ideal.pow_mem_pow h2 r
  rw [hr, Submodule.zero_eq_bot, Ideal.mem_bot, ← map_pow, Ideal.Quotient.eq_zero_iff_mem] at h3
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hs
  rw [pow_add]
  exact J.mul_mem_right _ h3

theorem exists_pow_apply_mem : ∀ (p : ℕ) (O : Type) [CommRing O] (G : PDivGroup p O) (n : ℕ)
    (m : Ideal O), m.IsMaximal → IsLocalRing (G.dual.A n) → ∃ r : ℕ, ∀ φ : G.dual.A n,
      φ 1 ∈ m → ∀ s, r ≤ s → ∀ a : G.A n, (φ ^ s) a ∈ m := by
  intro p O _ G n m hm hloc
  obtain ⟨r, hr⟩ := exists_pow_mem_map (Bialgebra.counitAlgHom O (G.dual.A n)) m hm
  refine ⟨r, fun φ hφ s hs a => ?_⟩
  have h := hr φ hφ s hs
  generalize φ ^ s = ψ at h
  have h' : ψ ∈ m • (⊤ : Submodule O (G.dual.A n)) := by
    rw [Ideal.smul_top_eq_map]
    exact h
  refine Submodule.smul_induction_on (p := fun ψ : G.dual.A n => ψ a ∈ m) h' ?_ ?_
  · intro c hc χ _
    exact m.mul_mem_right (χ a) hc
  · intro x y hx hy
    exact m.add_mem hx hy

end GlobalTheory.LocalDualNil
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueDualOfCompatibleModPow
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory.PDiv

theorem exists_unique_dual_of_compatible_mod_pow :
    ∀ (O M : Type) [CommRing O] [AddCommGroup M] [Module O M] (a : O)
      [IsAdicComplete (Ideal.span {a}) O] (u : ∀ n : ℕ, M →ₗ[O] O ⧸ Ideal.span {a ^ n}),
      (∀ n w (x : O), u (n + 1) w = Ideal.Quotient.mk _ x → u n w = Ideal.Quotient.mk _ x) →
      ∃! l : Module.Dual O M, ∀ n w, Ideal.Quotient.mk _ (l w) = u n w := by
  intro O M _ _ _ a _ u hu

  have sep : ∀ y : O, (∀ n : ℕ, y ∈ Ideal.span {a ^ n}) → y = 0 := by
    intro y hy
    refine IsHausdorff.haus' (I := Ideal.span {a}) y fun n => ?_
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow]
    exact hy n
  have key : ∀ w : M, ∃! y : O, ∀ n, Ideal.Quotient.mk (Ideal.span {a ^ n}) y = u n w := by
    intro w
    choose x hx using fun n => Ideal.Quotient.mk_surjective (u n w)
    have step : ∀ n, x n - x (n + 1) ∈ Ideal.span {a ^ n} := by
      intro n
      exact Ideal.Quotient.eq.mp ((hx n).trans (hu n w (x (n + 1)) (hx (n + 1)).symm))
    have cauchy : ∀ m n, m ≤ n → x m - x n ∈ Ideal.span {a ^ m} := by
      intro m n hmn
      induction n, hmn using Nat.le_induction with
      | base => simp
      | succ k hmk ih =>
        have h2 : x k - x (k + 1) ∈ Ideal.span {a ^ m} :=
          (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow a hmk)) (step k)
        have := Ideal.add_mem _ ih h2
        simpa using this
    obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := Ideal.span {a}) x (fun {m n} hmn => by
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow]
      exact cauchy m n hmn)
    refine ⟨L, fun n => ?_, fun y hy => ?_⟩
    · have h := hL n
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow] at h
      rw [← hx n]
      exact Ideal.Quotient.eq.mpr (by simpa using (Ideal.span {a ^ n}).neg_mem h)
    · refine sub_eq_zero.mp (sep _ fun n => ?_)
      have h := hL n
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow] at h
      exact Ideal.Quotient.eq.mp ((hy n).trans (hx n).symm) |> fun h' => by
        simpa using Ideal.add_mem _ h' h
  choose f hf huniq using key
  refine ⟨{ toFun := f, map_add' := ?_, map_smul' := ?_ }, ?_, ?_⟩
  · intro w w'
    refine (huniq (w + w') _ fun n => ?_).symm
    rw [map_add, map_add, hf, hf]
  · intro c w
    refine (huniq (c • w) _ fun n => ?_).symm
    rw [RingHom.id_apply, smul_eq_mul, map_mul, map_smul, ← hf w n, Algebra.smul_def,
      Ideal.Quotient.algebraMap_eq]
  · exact fun n w => hf w n
  · intro l hl
    exact LinearMap.ext fun w => huniq w (l w) fun n => hl n w

end GlobalTheory.PDiv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueFullLevel
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FullLevel

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem weilIs_unitOn_unique {S : Scheme.{0}} (G : Over S) [GrpObj G] {L : LB G.left} (hL : L.IsLB)
    {k : Type} [Field k] (x : Sp k ⟶ S) (n : ℤ) (g g' : Over.mk x ⟶ G) (c c' : kˣ)
    (h : Out.WeilIs G L n g g' (unitOn c)) (h' : Out.WeilIs G L n g g' (unitOn c')) : c = c' := by
  have hU : Subsingleton (Sp k) := by
    show Subsingleton (PrimeSpectrum k); infer_instance
  obtain ⟨p⟩ : Nonempty (Sp k) := by
    show Nonempty (PrimeSpectrum k); infer_instance
  have hp : ∀ V : (Over.mk x).left.Opens, p ∈ V → V = ⊤ := by
    intro V hV
    apply TopologicalSpace.Opens.ext
    ext y
    exact ⟨fun _ => trivial, fun _ => (Subsingleton.elim (α := Sp k) p y) ▸ hV⟩
  have H := GlobalTheory.ThetaGroupTest.weilIs_unique_of_local p hp hL h h'
  have hinj : Function.Injective (Units.map ((⊤ : (Over.mk x).left.Opens).ι.appTop.hom.toMonoidHom)) := by
    apply Units.map_injective
    haveI : IsIso ((⊤ : (Over.mk x).left.Opens).ι.app ⊤) := Scheme.Hom.isIso_app _ _ (by simp)
    exact (ConcreteCategory.bijective_of_isIso ((⊤ : (Over.mk x).left.Opens).ι.app ⊤)).1
  have H2 : unitOn c = unitOn c' := hinj H
  unfold unitOn at H2
  have hinj2 : Function.Injective (Units.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom.toMonoidHom) := by
    apply Units.map_injective
    exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of k)).inv).1
  exact hinj2 H2

theorem exists_unique_fullLevel {D : Datum H} {l : Level H} {B : Type} [CommRing B] {b : Base l B}
    {S : Scheme.{0}} {s : S ⟶ Sp B} (o : Obj D l b s) (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S)
    (β : B →+* k) (hx : x ≫ s = spMap β) (z : kˣ) (hz : IsPrimitiveRoot z l.M')
    (hzA : (z : k) ^ (l.M' / l.A) = β b.ζ) :
    ∃! ev : D.La → (Over.mk x ⟶ o.t.G),
      IsSympLevel D (fun a g => g ≫ o.t.act.act a)
          (fun n g g' c => Out.WeilIs o.t.G o.t.PP.L n g g' (unitOn c)) l.M' z ev ∧
        Induces l (fun a => toUnit _ ≫ o.etaA a) (fun a => toUnit _ ≫ o.eta a) ev := by
  obtain ⟨-, I, hIA, hetaA, heta⟩ := o.geom k x β hx
  have hzA' : z ^ (l.M' / l.A) = I.ζ l.A := Units.ext (by rw [Units.val_pow_eq_pow_val, hzA, hIA])
  obtain ⟨ev, hev, hA, hM⟩ := GlobalTheory.T.exists_fullSymplecticLevelStructure_of_tateIso l I hz hzA'
  have hi : Induces l (fun a => toUnit _ ≫ o.etaA a) (fun a => toUnit _ ≫ o.eta a) ev :=
    ⟨fun a => (hA a).trans (hetaA a).symm, fun a ha => (hM a ha).trans (heta a ha).symm⟩
  refine ⟨ev, ⟨hev, hi⟩, ?_⟩
  rintro ev' ⟨h1, h2⟩
  have := GlobalTheory.T.isFullSymplecticLevelStructure_unique_of_levels l (fun g g' c c' => weilIs_unitOn_unique o.t.G o.t.PP.isLB x _ g g' c c') hz
    hev hi h1 h2
  exact this.symm

end GlobalTheory.FullLevel
end
end

