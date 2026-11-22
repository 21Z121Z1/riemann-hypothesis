import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0760
import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
import GroundTheory.AutomorphicForms.ReductionCore
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0654
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0750
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0739
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0690
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0701
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0752
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0758
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0657
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0003
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0761
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTaylorExpansionOrderOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0022
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonvanishingSetEtaleSteinStatement
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonvanishingSet_etale_stein : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (Λ : La) (τ : ι → Y → ℂ) (z : Y → V n), A.IsSec Λ τ → A.Pos Λ (fun _ => 0) → Etale A (nz A τ) z → ∃ X : EtaleStein n (nz A τ), X.z = (fun y : nz A τ => z y) ∧ X.e = fun y : nz A τ => -Real.log (A.nsq Λ τ y) := by
  first | exact @GlobalTheory.nzEtaleStein | exact GlobalTheory.nzEtaleStein | (intros; apply GlobalTheory.nzEtaleStein <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemBand
section
noncomputable section

open NumberField GlobalTheory.CuspRep

namespace GlobalTheory.HCF

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

def absDetA (g : GA E a) : ℝ :=
  GroundTheory.Automorphic.Reduction.adeleAbs ((Matrix.GeneralLinearGroup.det g : (Ad E)ˣ) : Ad E)

theorem absDetA_pos (g : GA E a) : 0 < absDetA g := by
  unfold absDetA
  rw [GroundTheory.Automorphic.Reduction.adeleAbs_units (K := E) (Matrix.GeneralLinearGroup.det g)]
  exact ((GroundTheory.Global.IdeleGroup.ideleModule E) (Matrix.GeneralLinearGroup.det g)).2

theorem absDetA_one : absDetA (1 : GA E a) = 1 := by
  unfold absDetA
  rw [GroundTheory.Automorphic.Reduction.adeleAbs_units (K := E) (Matrix.GeneralLinearGroup.det (1 : GA E a)), map_one, map_one]
  rfl

variable (E a) in

def band : Set (GA E a) := {g | 1 ≤ absDetA g ∧ absDetA g ≤ 2}

theorem one_mem_band : (1 : GA E a) ∈ band E a := by
  simp only [band, Set.mem_setOf_eq, absDetA_one]; norm_num

end GlobalTheory.HCF

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivGroupDualTangentLinearKillsIntegral
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LieLin

variable {p : ℕ} {O : Type} [CommRing O]

theorem eq_zero_of_forall_dvd [IsHausdorff (Ideal.span {(p : O)}) O] (x : O)
    (h : ∀ n : ℕ, (p : O) ^ n ∣ x) : x = 0 :=
  IsHausdorff.haus' (I := Ideal.span {(p : O)}) x fun n => by
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton, sub_zero]
    exact h n

variable {G : PDivGroup p O}

theorem exists_form (n : ℕ) (w : G.dual.omega) :
    ∃ φ : CartierDual O (G.A n), PDiv.dUnit O φ = w.1 n ∧ φ 1 = 0 := by
  obtain ⟨φ, hφ⟩ := AugCot.d_surjective _ (w.1 n)
  refine ⟨φ - algebraMap O _ (φ 1), ?_, ?_⟩
  · change AugCot.d _ (φ - algebraMap O _ (φ 1)) = _
    rw [map_sub, AugCot.d_algebraMap, sub_zero]
    exact hφ
  · have h1 : (algebraMap O (CartierDual O (G.A n)) (φ 1)) 1 = φ 1 := by
      rw [Algebra.algebraMap_eq_smul_one]
      change φ 1 * Coalgebra.counit (R := O) (1 : G.A n) = _
      rw [Bialgebra.counit_one, mul_one]
    change φ 1 - (algebraMap O (CartierDual O (G.A n)) (φ 1)) 1 = 0
    rw [h1, sub_self]

theorem lie_eq_zero [IsHausdorff (Ideal.span {(p : O)}) O] (l : G.dual.Lie)
    (h : ∀ (n : ℕ) (w : G.dual.omega) (φ : CartierDual O (G.A n)), PDiv.dUnit O φ = w.1 n →
      φ 1 = 0 → (p : O) ^ n ∣ l w) : l = 0 :=
  LinearMap.ext fun w => eq_zero_of_forall_dvd _ fun n => by
    obtain ⟨φ, hφ, h1⟩ := exists_form n w
    exact h n w φ hφ h1

variable {σ τ R : Type} [CommRing R] [Finite σ]

theorem constantCoeff_subst_of {a : σ → MvPowerSeries τ R} (ha0 : ∀ i, constantCoeff (a i) = 0)
    (f : MvPowerSeries σ R) : constantCoeff (subst a f) = constantCoeff f := by
  have hs := hasSubst_of_constantCoeff_zero ha0
  have hg : constantCoeff (f - C (constantCoeff f)) = 0 := by simp
  have e : f = C (constantCoeff f) + (f - C (constantCoeff f)) := by ring
  calc constantCoeff (subst a f)
      = constantCoeff (subst a (C (constantCoeff f) + (f - C (constantCoeff f)))) := by rw [← e]
    _ = constantCoeff f := by
      have hC : (C (constantCoeff f) : MvPowerSeries σ R) =
          algebraMap R (MvPowerSeries σ R) (constantCoeff f) := by
        rw [MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
      rw [subst_add hs, map_add, constantCoeff_subst_eq_zero hs ha0 hg, add_zero,
        ← coe_substAlgHom hs, hC, AlgHom.commutes, MvPowerSeries.algebraMap_apply]
      simp

end GlobalTheory.LieLin

namespace GlobalTheory.LieLin

variable {p : ℕ} {O : Type} [CommRing O] {G : PDivGroup p O} {d : ℕ} (c : QLog.Chart G d)

theorem ev_subst_eq (n : ℕ) (a : Fin d → MvPowerSeries (Fin d) O)
    (ha0 : ∀ i, constantCoeff (a i) = 0) (hz : ∀ i, c.ev n (a i) = 0)
    (s : MvPowerSeries (Fin d) O) :
    ∃ y : G.A n, c.ev n (subst a s) = algebraMap O (G.A n) (constantCoeff s) + (p : O) ^ n • y := by
  have hs := hasSubst_of_constantCoeff_zero ha0
  obtain ⟨N, hN⟩ := (c.isEval n).2 n
  set P := trunc' O (Finsupp.equivFunOnFinite.symm fun _ : Fin d => N) s with hP
  have hT : ∀ α : Fin d →₀ ℕ, α.degree < N →
      coeff α (subst a (s - (P : MvPowerSeries (Fin d) O))) = 0 := by
    have h1 : (N : ℕ∞) ≤ (s - (P : MvPowerSeries (Fin d) O)).order := by
      refine nat_le_order fun α hα => ?_
      rw [map_sub, MvPolynomial.coeff_coe, hP, coeff_trunc', if_pos, sub_self]
      intro i
      have : α i ≤ α.degree := Finsupp.le_degree i α
      have h' : (Finsupp.equivFunOnFinite.symm fun _ : Fin d => N) i = N := by simp
      rw [h']
      omega
    have h2 : (1 : ℕ∞) ≤ ⨅ i, (a i).order :=
      le_iInf fun i => one_le_order_iff_constCoeff_eq_zero.2 (ha0 i)
    have h3 := le_order_subst hs (s - (P : MvPowerSeries (Fin d) O))
    intro α hα
    apply coeff_of_lt_order
    calc (α.degree : ℕ∞) < N := by exact_mod_cast hα
      _ = 1 * (N : ℕ∞) := (one_mul _).symm
      _ ≤ (⨅ i, (a i).order) * (s - (P : MvPowerSeries (Fin d) O)).order := mul_le_mul' h2 h1
      _ ≤ _ := h3
  obtain ⟨y, hy⟩ := hN _ hT
  refine ⟨y, ?_⟩
  have e : subst a s = subst a (P : MvPowerSeries (Fin d) O) +
      subst a (s - (P : MvPowerSeries (Fin d) O)) := by
    rw [← subst_add hs, add_sub_cancel]
  have hz' : (fun i => c.ev n (a i)) = 0 := funext hz
  rw [e, map_add, subst_coe, ← AlgHom.comp_apply, MvPolynomial.comp_aeval, hy, hz',
    MvPolynomial.aeval_zero, Algebra.smul_def, map_pow, map_natCast, MvPolynomial.constantCoeff_eq,
    hP, coeff_trunc', if_pos (by simp), coeff_zero_eq_constantCoeff_apply]

end GlobalTheory.LieLin

namespace GlobalTheory.LieLin

variable {p : ℕ} {O : Type} [CommRing O] {G : PDivGroup p O} {d : ℕ} (c : QLog.Chart G d)
  {E : Type} [CommRing E] [Algebra O E]

theorem lie_eq_zero_of_integral [IsHausdorff (Ideal.span {(p : O)}) O]
    (hz : ∀ n i, c.ev n (nmul c.μ (p ^ n) i) = 0) (s0 : MvPowerSeries (Fin d) O)
    (l : G.dual.Lie) (h : c.IsLie (map (algebraMap O E) s0) l) : l = 0 := by
  refine lie_eq_zero l fun n w φ hφ h1 => ?_
  have ha0 : ∀ i, constantCoeff (nmul c.μ (p ^ n) i) = 0 :=
    QLogDefect.constantCoeff_nmul c.isLaw.const _
  have hs := hasSubst_of_constantCoeff_zero ha0
  have hD : map (algebraMap O E) (((p ^ n : ℕ) : O) • s0 - subst (nmul c.μ (p ^ n)) s0) =
      defect c.μ (p ^ n) (map (algebraMap O E) s0) := by
    rw [defect, map_sub, map_subst hs]
    congr 1
    ext α
    simp [coeff_map]
  have h2 := h.2 n w φ _ hφ hD
  obtain ⟨y, hy⟩ := ev_subst_eq c n _ ha0 (hz n) s0
  have hφa : ∀ k : O, φ (algebraMap O (G.A n) k) = 0 := fun k => by
    rw [Algebra.algebraMap_eq_smul_one, map_smul, h1, smul_zero]
  have e : φ (c.ev n (((p ^ n : ℕ) : O) • s0 - subst (nmul c.μ (p ^ n)) s0)) =
      (p : O) ^ n * (φ (c.ev n s0) - φ y) := by
    rw [map_sub, map_smul, hy, map_sub, map_smul, map_add, map_smul, hφa, smul_eq_mul, smul_eq_mul]
    push_cast
    ring
  rw [e] at h2
  have h3 := dvd_add h2 (dvd_mul_right ((p : O) ^ n) (φ (c.ev n s0) - φ y))
  rwa [sub_add_cancel] at h3

theorem quasiLogarithmDefect_eq_zero_of_coboundary (f : MvPowerSeries (Fin d) E) (hf : cob1 (up E c.μ) f = 0) (k : ℕ) :
    defect c.μ k f = 0 := by
  have hμ := c.isLaw.const
  have hM : ∀ j, constantCoeff (up E c.μ j) = 0 := fun j => by
    simp only [up]
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply, hμ j,
      map_zero]
  have hc : constantCoeff f = 0 := by
    have h := congrArg constantCoeff hf
    rw [cob1, inL, inR, map_sub, map_sub, constantCoeff_subst_of hM,
      constantCoeff_subst_of (fun _ => constantCoeff_X _),
      constantCoeff_subst_of (fun _ => constantCoeff_X _), map_zero] at h
    linear_combination -h
  induction k with
  | zero =>
    have h0 : up E (nmul c.μ 0) = 0 := by funext i; simp [up, nmul]
    rw [defect, h0, Nat.cast_zero, zero_smul, zero_sub, subst_zero_of_constantCoeff_zero hc,
      neg_zero]
  | succ k ih =>
    rw [QLogDefect.defect_succ c.μ hμ k f, ih, hf]
    have hE : ∀ j, constantCoeff (Sum.elim (up E (nmul c.μ k))
        (fun i => (X i : MvPowerSeries (Fin d) E)) j) = 0 := by
      rintro (j | j)
      · simp only [Sum.elim_inl, up]
        rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply,
          QLogDefect.constantCoeff_nmul hμ k j, map_zero]
      · simp
    rw [← coe_substAlgHom (hasSubst_of_constantCoeff_zero hE), map_zero, sub_zero]

theorem lie_eq_zero_of_cob1 [IsHausdorff (Ideal.span {(p : O)}) O] (f : MvPowerSeries (Fin d) E)
    (hf : cob1 (up E c.μ) f = 0) (l : G.dual.Lie) (h : c.IsLie f l) : l = 0 := by
  refine lie_eq_zero l fun n w φ hφ _ => ?_
  have h2 := h.2 n w φ 0 hφ (by rw [map_zero, quasiLogarithmDefect_eq_zero_of_coboundary c f hf])
  rwa [map_zero, map_zero, sub_zero] at h2

theorem exists_of_in {σ : Type} {f : MvPowerSeries σ E} (h : In (⊤ : Ideal O) f) :
    ∃ s : MvPowerSeries σ O, map (algebraMap O E) s = f := by
  choose b _ hb using h
  refine ⟨(show MvPowerSeries σ O from fun α => b α), ?_⟩
  ext α
  rw [coeff_map, hb α]
  rfl

theorem defect_add_smul (f g : MvPowerSeries (Fin d) E) (a : E) (k : ℕ) :
    defect c.μ k (f + a • g) = defect c.μ k f + a • defect c.μ k g := by
  have hU : ∀ j, constantCoeff (up E (nmul c.μ k) j) = 0 := fun j => by
    simp only [up]
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply,
      QLogDefect.constantCoeff_nmul c.isLaw.const _ j, map_zero]
  have hsub := hasSubst_of_constantCoeff_zero hU
  simp only [defect]
  rw [subst_add hsub, subst_smul hsub, smul_add, smul_sub, smul_comm ((k : ℕ) : E) a g]
  abel

theorem isLie_add_smul (hinj : Function.Injective (algebraMap O E))
    {f g : MvPowerSeries (Fin d) E} {l l' : G.dual.Lie} (a : O)
    (hf : c.IsLie f l) (hg : c.IsLie g l') :
    c.IsLie (f + algebraMap O E a • g) (l + a • l') := by
  have hmap : ∀ sf sg : MvPowerSeries (Fin d) O, map (algebraMap O E) (sf + a • sg) =
      map (algebraMap O E) sf + algebraMap O E a • map (algebraMap O E) sg := fun sf sg => by
    ext α
    simp [coeff_map]
    exact (Algebra.smul_def _ _).symm
  refine (c.isLie_iff hinj _ _).2 fun n => ?_
  obtain ⟨sf, hsf⟩ := exists_of_in (hf.1 n)
  obtain ⟨sg, hsg⟩ := exists_of_in (hg.1 n)
  refine ⟨sf + a • sg, by rw [hmap, defect_add_smul, hsf, hsg], fun w φ hφ => ?_⟩
  have h1 := hf.2 n w φ sf hφ hsf
  have h2 := hg.2 n w φ sg hφ hsg
  rw [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, map_add,
    map_smul, smul_eq_mul]
  have h3 := dvd_add h1 (dvd_mul_of_dvd_right h2 a)
  convert h3 using 1
  ring

theorem isLie_add [Fact p.Prime] (hF : IsFrame p E (RingHom.id O))
    (_hL : IsLift (RingHom.id O) c.μ) {f g : MvPowerSeries (Fin d) E} {l l' : G.dual.Lie} (a : O)
    (hf : c.IsLie f l) (hg : c.IsLie g l') (_qf : QL c.μ ⊤ f) (_qg : QL c.μ ⊤ g) :
    c.IsLie (f + algebraMap O E a • g) (l + a • l') :=
  isLie_add_smul c hF.inj a hf hg

end GlobalTheory.LieLin

namespace GlobalTheory.LieLin

theorem main : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (E : Type) [CommRing E] [Algebra O E], IsFrame p E (RingHom.id O) → ∀ (f g : MvPowerSeries (Fin d) E) (l l' : G.dual.Lie) (a : O), c.IsLie f l → c.IsLie g l' → (QL c.μ ⊤ f → QL c.μ ⊤ g → c.IsLie (f + algebraMap O E a • g) (l + a • l')) ∧ ((∃ s : MvPowerSeries (Fin d) O, f = map (algebraMap O E) s) → l = 0) ∧ (cob1 (up E c.μ) f = 0 → l = 0) := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv G d c E _ _ hF f g l l' a hf hg
  have hz : ∀ n i, c.ev n (nmul c.μ (p ^ n) i) = 0 := fun n i => GlobalTheory.chart_ev_nmul_pow_self p C v O hv G d c n i
  have hL : IsLift (RingHom.id O) c.μ :=
    ⟨c.isLaw.const, c.isLaw.unit, c.isLaw.comm, by simpa using c.isLaw⟩
  refine ⟨fun qf qg => isLie_add c hF hL a hf hg qf qg, ?_, fun h => lie_eq_zero_of_cob1 c f h l hf⟩
  rintro ⟨s, rfl⟩
  exact lie_eq_zero_of_integral c hz s l hf

end GlobalTheory.LieLin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivGroupDualTangentOfQuasiLogarithm
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
open TensorProduct

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.QLogTangent

theorem smodEq_iff' {O : Type} [CommRing O] (p : O) (n : ℕ) (x y : O) :
    x ≡ y [SMOD (Ideal.span {p} ^ n • ⊤ : Submodule O O)] ↔ p ^ n ∣ x - y := by
  rw [SModEq.sub_mem, Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top, Ideal.mem_span_singleton]

theorem eq_zero_of_forall_dvd {O : Type} [CommRing O] (p : O) [IsHausdorff (Ideal.span {p}) O] (x : O)
    (h : ∀ n : ℕ, p ^ n ∣ x) : x = 0 :=
  IsHausdorff.haus' x fun n => (smodEq_iff' p n x 0).2 (by simpa using h n)

theorem main : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (E : Type) [CommRing E] [Algebra O E], IsFrame p E (RingHom.id O) → ∀ f : MvPowerSeries (Fin d) E, QL c.μ ⊤ f → ∃! l : G.dual.Lie, c.IsLie f l := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv G d c E _ _ hF f hf
  have hinj : Function.Injective (algebraMap O E) := hF.inj
  have hlift : IsLift (RingHom.id O) c.μ :=
    ⟨c.isLaw.const, c.isLaw.unit, c.isLaw.comm, by simpa using c.isLaw⟩
  have hser : ∀ {τ : Type} (F : MvPowerSeries τ E), In (⊤ : Ideal O) F →
      ∃ s : MvPowerSeries τ O, map (algebraMap O E) s = F := by
    intro τ F hF'
    choose b _ hb using hF'
    let S : MvPowerSeries τ O := fun α => b α
    exact ⟨S, by ext α; rw [coeff_map, hb α]; rfl⟩
  have hminj : ∀ (s s' : MvPowerSeries (Fin d) O),
      map (algebraMap O E) s = map (algebraMap O E) s' → s = s' := by
    intro s s' h
    ext α
    apply hinj
    have := congrArg (coeff α) h
    simpa [coeff_map] using this
  have hdef : ∀ k, ∃ s : MvPowerSeries (Fin d) O, map (algebraMap O E) s = defect c.μ k f :=
    fun k => hser _ (GlobalTheory.QLogDefect.main p O O E (RingHom.id O) hF d c.μ hlift ⊤ f hf k).1
  obtain ⟨g, hg⟩ := hser _ hf.2.2
  choose s hs using hdef
  let a : ∀ n, G.A n := fun n => c.ev n (s (p ^ n))
  have hprim : ∀ n, ∃ t : G.A n ⊗[O] G.A n,
      Coalgebra.comul (R := O) (a n) = a n ⊗ₜ[O] (1 : G.A n) + (1 : G.A n) ⊗ₜ[O] a n + ((p : O) ^ n) • t := by
    intro n
    obtain ⟨h1, h2⟩ := GlobalTheory.CobDefect.main O E d c.μ c.isLaw hinj f g (s (p ^ n)) (p ^ n) hf.1 hg (hs _)
    refine ⟨c.ev₂ n g, ?_⟩
    show Coalgebra.comul (R := O) (c.ev n (s (p ^ n))) = _
    rw [GlobalTheory.QLog.Chart.comul_ev p C v O hv G d c n, h1, map_sub, map_smul, GlobalTheory.EvTor.ev₂_at_nmul_pow_self p C v O hv G d c n, h2, map_zero, sub_zero,
      Nat.cast_pow]
  have hcomp : ∀ n, ∃ b : G.A (n + 1), a (n + 1) = G.mulP n (a n) + ((p : O) ^ n) • b := by
    intro n
    have h := GlobalTheory.DefectComp.main O E d c.μ c.isLaw hinj f hf.1 (p ^ n) p (s (p ^ n)) (s p) (s (p ^ n * p))
      (hs _) (hs _) (hs _)
    refine ⟨c.ev (n + 1) (s p), ?_⟩
    show c.ev (n + 1) (s (p ^ (n + 1))) = G.mulP n (c.ev n (s (p ^ n))) + _
    rw [pow_succ, h, map_add, map_smul, GlobalTheory.EvP.ev_subst_nmul_p p C v O hv G d c n, Nat.cast_pow]
  have key : ∀ n (φ ψ : CartierDual O (G.A n)), PDiv.dUnit O φ = PDiv.dUnit O ψ →
      (p : O) ^ n ∣ φ (a n) - ψ (a n) := by
    intro n φ ψ h
    obtain ⟨t, ht⟩ := hprim n
    exact GlobalTheory.CotDualLin.dvd_sub_of_dUnit_eq O (G.A n) (a n) _ t ht φ ψ h
  have dsurj : ∀ n (x : PDiv.Cot O (CartierDual O (G.A n))), ∃ φ : CartierDual O (G.A n),
      PDiv.dUnit O φ = x := fun n x => AugCot.d_surjective _ x
  have haus : ∀ x : O, (∀ n : ℕ, (p : O) ^ n ∣ x) → x = 0 := eq_zero_of_forall_dvd (p : O)
  let Good : G.dual.omega → O → Prop := fun w L => ∀ n (φ : CartierDual O (G.A n)),
    PDiv.dUnit O φ = w.1 n → (p : O) ^ n ∣ L - φ (a n)
  have good_unique : ∀ w L L', Good w L → Good w L' → L = L' := by
    intro w L L' h h'
    refine sub_eq_zero.1 (haus _ fun n => ?_)
    obtain ⟨φ, hφ⟩ := dsurj n (w.1 n)
    have := dvd_sub (h n φ hφ) (h' n φ hφ)
    rwa [sub_sub_sub_cancel_right] at this
  have good_exists : ∀ w, ∃ L, Good w L := by
    intro w
    choose φ hφ using fun n => dsurj n (w.1 n)
    have step : ∀ n, (p : O) ^ n ∣ φ (n + 1) (a (n + 1)) - φ n (a n) := by
      intro n
      obtain ⟨b, hb⟩ := hcomp n
      have h1 : PDiv.dUnit O (CartierDual.map (G.mulP n) (φ (n + 1))) = w.1 n := by
        rw [← w.2 n, ← hφ (n + 1)]
        exact (PDiv.cotMap_d (G.dual.res n) (φ (n + 1))).symm
      have h2 := key n _ _ (h1.trans (hφ n).symm)
      rw [CartierDual.map_apply] at h2
      rw [hb, map_add, map_smul, smul_eq_mul]
      have e : φ (n + 1) (G.mulP n (a n)) + (p : O) ^ n * φ (n + 1) b - φ n (a n) =
          (φ (n + 1) (G.mulP n (a n)) - φ n (a n)) + (p : O) ^ n * φ (n + 1) b := by ring
      rw [e]
      exact dvd_add h2 (dvd_mul_right _ _)
    have cauchy : ∀ m n, m ≤ n → (p : O) ^ m ∣ φ n (a n) - φ m (a m) := by
      intro m n hmn
      induction n, hmn using Nat.le_induction with
      | base => simp
      | succ n hmn ih =>
        have := dvd_add ih ((pow_dvd_pow (p : O) hmn).trans (step n))
        rwa [add_comm, sub_add_sub_cancel] at this
    obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := Ideal.span {(p : O)}) (fun n => φ n (a n))
      (fun {m n} hmn => (smodEq_iff' _ _ _ _).2 (dvd_sub_comm.1 (cauchy m n hmn)))
    refine ⟨L, fun n ψ hψ => ?_⟩
    have h1 := (smodEq_iff' _ _ _ _).1 (hL n)
    have h2 := key n _ _ ((hφ n).trans hψ.symm)
    have := dvd_add (dvd_sub_comm.1 h1) h2
    rwa [sub_add_sub_cancel] at this
  choose Lf hLf using good_exists
  have hgood_add : ∀ w w', Good (w + w') (Lf w + Lf w') := by
    intro w w' n φ hφ
    obtain ⟨φ1, h1⟩ := dsurj n (w.1 n)
    obtain ⟨φ2, h2⟩ := dsurj n (w'.1 n)
    have e : PDiv.dUnit O (φ1 + φ2) = PDiv.dUnit O φ := by
      have ea : PDiv.dUnit O (φ1 + φ2) = PDiv.dUnit O φ1 + PDiv.dUnit O φ2 := map_add (AugCot.d _) φ1 φ2
      rw [ea, h1, h2, hφ]; rfl
    have k := key n _ _ e
    have := dvd_add (dvd_add (hLf w n φ1 h1) (hLf w' n φ2 h2)) k
    have e2 : (φ1 + φ2) (a n) = φ1 (a n) + φ2 (a n) := rfl
    rw [e2] at this
    have e3 : Lf w - φ1 (a n) + (Lf w' - φ2 (a n)) + (φ1 (a n) + φ2 (a n) - φ (a n)) =
        Lf w + Lf w' - φ (a n) := by ring
    rwa [e3] at this
  have hgood_smul : ∀ (r : O) w, Good (r • w) (r * Lf w) := by
    intro r w n φ hφ
    obtain ⟨φ1, h1⟩ := dsurj n (w.1 n)
    have e : PDiv.dUnit O (r • φ1) = PDiv.dUnit O φ := by
      have ea : PDiv.dUnit O (r • φ1) = r • PDiv.dUnit O φ1 := map_smul (AugCot.d _) r φ1
      rw [ea, h1, hφ]; rfl
    have k := key n _ _ e
    have := dvd_add (dvd_mul_of_dvd_right (hLf w n φ1 h1) r) k
    have e2 : (r • φ1) (a n) = r * φ1 (a n) := rfl
    rw [e2] at this
    have e3 : r * (Lf w - φ1 (a n)) + (r * φ1 (a n) - φ (a n)) = r * Lf w - φ (a n) := by ring
    rwa [e3] at this
  let l : G.dual.Lie :=
    { toFun := Lf
      map_add' := fun w w' => good_unique _ _ _ (hLf (w + w')) (hgood_add w w')
      map_smul' := fun r w => good_unique _ _ _ (hLf (r • w)) (hgood_smul r w) }
  have hisLie : ∀ l' : G.dual.Lie, c.IsLie f l' ↔ ∀ w, Good w (l' w) := by
    intro l'
    constructor
    · intro h w n φ hφ
      exact h.2 n w φ (s (p ^ n)) hφ (hs _)
    · intro h
      refine ⟨fun n => In.top_iff.2 ⟨s (p ^ n), hs _⟩, fun n w φ s' hφ hs' => ?_⟩
      have : s' = s (p ^ n) := hminj _ _ (hs'.trans (hs _).symm)
      subst this
      exact h w n φ hφ
  refine ⟨l, (hisLie l).2 fun w => hLf w, fun l' hl' => ?_⟩
  exact LinearMap.ext fun w => good_unique _ _ _ ((hisLie l').1 hl' w) (hLf w)

end GlobalTheory.QLogTangent
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialZetaDenominatorsCMFieldOfSiegelKlingenDelStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.partialZetaDenominatorsCMField_of_siegelKlingenDeligneRibet : GlobalTheory.Published.SiegelKlingenDeligneRibet → GlobalTheory.IndefiniteRowSideFullHecke.ZetaValueIdeals.ZetaDenominators := by
  first | exact @GlobalTheory.ZetaDenom.zetaDenominators | exact GlobalTheory.ZetaDenom.zetaDenominators | (intros; apply GlobalTheory.ZetaDenom.zetaDenominators <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeakSectionsFiniteWeightedAtlasStatement
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.peak_sections_finite_weighted_atlas : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (C : Cover A), ∀ (H : La), (∀ i y, y ∈ (A.chart i).source → ∀ ξ : Fin n → ℂ, ξ ≠ 0 → 0 < A.leviAt i (A.ph H i) y ξ) → ∀ T : Finset Y, ∃ (q : Y → V n → ℂ) (c Cq r0 : ℝ), 0 < c ∧ 0 < r0 ∧ (∀ P ∈ T, Differentiable ℂ (q P) ∧ closedBall (A.chart (A.pick P) P) r0 ⊆ (A.chart (A.pick P)).target ∧ ∀ v ∈ closedBall (A.chart (A.pick P) P) r0, A.ph H (A.pick P) ((A.chart (A.pick P)).symm v) - 2 * (q P v).re ≤ Cq * ‖v - (A.chart (A.pick P) P)‖ ^ 2) ∧ ∀ (G : La) (p : Y → V n → ℂ), (∀ P, Differentiable ℂ (p P)) → ∃ K : ℝ, 0 ≤ K ∧ ∀ k : ℕ, ∃ F0 : ι → Y → ℂ, A.IsSSec (A.kap + (G + k • H)) F0 ∧ (∀ P ∈ T, ∀ v ∈ ball (A.chart (A.pick P) P) r0, F0 (A.pick P) ((A.chart (A.pick P)).symm v) = p P v * Complex.exp (k * q P v)) ∧ n1 C (G + k • H) F0 ≤ ENNReal.ofReal (K * Real.exp (-c * k)) := by
  first | exact @GlobalTheory.OTY.peak_sections_finite | exact GlobalTheory.OTY.peak_sections_finite | (intros; apply GlobalTheory.OTY.peak_sections_finite <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodClassLinearRelationUniqueOfNilpotentStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer GlobalTheory.PeriodFamily
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.periodClass_linear_relation_unique_of_nilpotent : ∀ {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F₀ : Fam Empty g Λ} (K₀ : Charts F₀) {R : Type} [CommRing R] [Algebra ℂ R] (et : Hol F₀.V →+* R) (M : Ideal R), K₀.Rich → (∀ z, z ∈ F₀.V) → IsNilpotent M → (∀ (f : Hol F₀.V), ∀ z ∈ F₀.V, et f = algebraMap ℂ R (f.fn z)) → ∀ {io : Type} (S : Finset io) (d : io → R) (q : io → (Λ →+ R)) (q' : Λ →+ R), K₀.perClD et M q' = ∑ i ∈ S, d i • K₀.perClD et M (q i) → ∀ l, q' l = ∑ i ∈ S, d i * q i l := by
  first | exact @GlobalTheory.AnPer.perClD_relation_unique | exact GlobalTheory.AnPer.perClD_relation_unique | (intros; apply GlobalTheory.AnPer.perClD_relation_unique <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodConstExtStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer GlobalTheory.PeriodFamily
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coefD_pull1_eq_perClD_of_pull1_eq_perCl : ∀ {I₀ : Type} [Fintype I₀] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F₀ : Fam I₀ g Λ} (K₀ : Charts F₀) {R : Type} [CommRing R] (et : Hol F₀.V →+* R) (M : Ideal R) {B₀ D : Type} [CommRing B₀] [CommRing D] {X₀ : Scheme.{0}} {s₀ : X₀ ⟶ Sp B₀} {σ₀ : B₀ →+* Hol F₀.V} (r₀ : GlobalTheory.AnPer.Real K₀ s₀ σ₀) {J : Ideal D} (dl : DividedPowers J) {s' : X₀ ⟶ Sp D} {π : D →+* B₀} {io : D →+* R} (H : IsOver et M s₀ σ₀ J s' π io) (j : B₀ →+* D) (φ₀ : X₀ ⟶ X₀) (n : IsMor (dp0 B₀) s₀ dl s' j φ₀), φ₀ = 𝟙 X₀ → (∀ b, et (σ₀ b) = io (j b)) → ∀ (c : FirstDeRham s₀) (per : Λ →+ Hol F₀.V), r₀.coef.pull1 c = K₀.perCl per → (r₀.coefD dl H).pull1 (n.pull1 c) = K₀.perClD et M (et.toAddMonoidHom.comp per) := by
  first | exact @GlobalTheory.AnPer.period_const_ext | exact GlobalTheory.AnPer.period_const_ext | (intros; apply GlobalTheory.AnPer.period_const_ext <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiEmbeddingDeterminantPropertyStatement
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.psi_embedding_determinant_property : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (ε : PreTilt O p), IsPrimitiveRoot (root ε).untilt p → ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [Algebra ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ] [FaithfulSMul ℤ_[p] Λ], ∀ τ₀ : Λ →+* O, ∃ (κ₀ : ℝ) (κ : (Λ →+* O) → ℝ), ∀ (γ : O ≃+* O), IsIsom C v γ → ∀ (N h : ℕ), h = Module.finrank ℤ_[p] Λ * N → ∀ (D : Datum ε h Λ) ι (lam : C), IsIota C D ((γ : O →+* O).comp τ₀) N ι → lam ≠ 0 → ι '' (detLattice C (actT D) ((γ : O →+* O).comp τ₀) N : Set (detLine C (actT D) ((γ : O →+* O).comp τ₀) N)) = (fun w => lam • w) '' (detLattice C (actH D) ((γ : O →+* O).comp τ₀) N : Set (detLine C (actH D) ((γ : O →+* O).comp τ₀) N)) → Real.log (v lam) = N * κ₀ + ∑ᶠ σ, (D.lieRank ((γ : O →+* O).comp σ) : ℝ) * κ σ := by
  first | exact @GlobalTheory.DetInv.detConst_linear_isom | exact GlobalTheory.DetInv.detConst_linear_isom | (intros; apply GlobalTheory.DetInv.detConst_linear_isom <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiLogLiftPdivGroupFrameStatement
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quasi_log_lift_pdiv_group_frame : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) F.B), IsLift F.θ μ' → (∀ i, map F.θ (μ' i) = c.μ i) → ∀ f : MvPowerSeries (Fin d) F.Q, QL μ' ⊤ f → QL μ' ⊤ (frob p F.s f) ∧ (In (RingHom.ker F.θ) (cob1 (up F.Q μ') f) → QL μ' (Ideal.span {(p : F.B)}) (frob p F.s f)) := by
  first | exact @GlobalTheory.QLog.ql_frob | exact GlobalTheory.QLog.ql_frob | (intros; apply GlobalTheory.QLog.ql_frob <;> assumption)
end

