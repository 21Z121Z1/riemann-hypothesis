import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalLabelOperatorsOnHyperspecialFixedVector
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0171
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0178
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0174
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0146
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0004
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0172
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0646
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeilTraceEqOfSameWd
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0017
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0175
import Formalism.LocalToGlobal.Divisibility.LiftLatLemmas
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalHeckeSplitTopDegreeRecursion
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitTopStep

open Formalism.L2.NTheta

theorem opOf_sum_single {D : D7} {V : HSp D} {M : Type} [AddCommGroup M] [Module ℂ M] (π : GA D V →* Module.End ℂ M)
    (P : Pl D.host.E) {ι : Type} (s : Finset ι) (l : ι → List ℤ) (z : ι → ℂ) :
    opOf π P (∑ i ∈ s, Finsupp.single (l i) (z i)) = ∑ i ∈ s, z i • ∑ γ ∈ rep V P (l i), π γ := by
  classical
  unfold opOf
  rw [← Finsupp.sum_finset_sum_index (by simp) (by intros; simp [add_smul])]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finsupp.sum_single_index (by simp)]

theorem pos_iff_lt : ∀ {n : ℕ} (d : Fin n → ℤ), Antitone d →
    ∀ i : Fin n, 0 < d i ↔ (i : ℕ) < ((List.ofFn d).filter fun x => 0 < x).length
  | 0, _, _, i => i.elim0
  | n + 1, d, hd, i => by
    have ih := pos_iff_lt (fun j : Fin n => d j.succ) (fun a b h => hd (Fin.succ_le_succ_iff.2 h))
    rw [List.ofFn_succ, List.filter_cons]
    by_cases h0 : 0 < d 0
    · simp only [h0, decide_true, if_true, List.length_cons]
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [h0]
      · simp [ih j]
    · have hnil : (List.ofFn fun j : Fin n => d j.succ).filter (fun x => 0 < x) = [] := by
        rw [List.filter_eq_nil_iff]
        intro x hx
        obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hx
        have := hd (Fin.zero_le j.succ)
        simp only [decide_eq_true_eq, not_lt]
        omega
      simp only [h0, decide_false, Bool.false_eq_true, if_false, hnil, List.length_nil]
      have := hd (Fin.zero_le i)
      constructor
      · intro h; omega
      · intro h; omega

theorem dualLab_splitLab (n k : ℕ) (hk : k ≤ n) :
    dualLab (splitLab n k) = List.ofFn fun i : Fin n => if (i : ℕ) < k then (1 : ℤ) else 0 := by
  apply List.ext_getElem
  · simp [dualLab, splitLab]; omega
  · intro i h1 h2
    simp [dualLab, splitLab, List.getElem_reverse, List.getElem_append, List.getElem_replicate]

theorem top_step : ∀ {D : D7} (V : HSp D) (P : Pl D.host.E), conjPl P ≠ P → ∀ d : List ℤ, IsLab V P d → (∀ x ∈ d, 0 ≤ x) → (∃ x ∈ d, 0 < x) → ∃ m : ℕ, 0 < m ∧ ∃ c : List ℤ →₀ ℂ, (∀ d' ∈ c.support, (∀ x ∈ d', 0 ≤ x) ∧ d'.sum = d.sum ∧ (d'.map fun x => x ^ 2).sum < (d.map fun x => x ^ 2).sum) ∧ ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (π : GA D V →* Module.End ℂ M) (u : M), (∀ k ∈ hyp V P, π k u = u) → opOf π P (Finsupp.single (d.map fun x => if 0 < x then x - 1 else x) 1) (opOf π P (Finsupp.single (dualLab (splitLab V.rank (d.filter fun x => 0 < x).length)) 1) u) = (m : ℂ) • opOf π P (Finsupp.single d 1) u + opOf π P c u := by
  classical
  intro D V P hP d hd hnn _
  obtain ⟨K, hK⟩ := GlobalTheory.SphLabelOps.exists_hyp V P
  obtain ⟨R0, e, f, ϖ, α0, -, hpi, h1, h2, hdp, -, -, -, hD0, -, -⟩ := hd
  obtain ⟨he, rfl⟩ := GlobalTheory.CentralShift.split_of_primeIdem hP hpi
  have hKl : ∀ k ∈ K, k ∈ KsphC V ∅ ∧ Formalism.L2.Theta.SuppAt e V k := fun k hk => by
    have : k ∈ hyp V P := hK ▸ hk
    rw [GlobalTheory.DualSplitRel.hyp_eq_locPart he V] at this
    exact this
  obtain ⟨dF, rfl⟩ : ∃ dF : Fin V.rank → ℤ, d = List.ofFn dF :=
    ⟨fun i => d[i.1]'(by have := hD0.1; omega), by apply List.ext_getElem <;> simp [hD0.1]⟩
  have hanti : Antitone dF := fun i j hij => by
    rcases hij.lt_or_eq with h | h
    · exact List.pairwise_ofFn.1 hdp h
    · rw [h]
  have hnn' : ∀ i, 0 ≤ dF i := fun i => hnn _ (List.mem_ofFn.2 ⟨i, rfl⟩)
  set kk := ((List.ofFn dF).filter fun x => 0 < x).length with hkk
  have hk := pos_iff_lt dF hanti
  have hkn : kk ≤ V.rank := by
    have := List.length_filter_le (fun x => decide (0 < x)) (List.ofFn dF)
    simpa using this
  set d₁ : Fin V.rank → ℤ := fun i => if 0 < dF i then dF i - 1 else dF i with hd₁
  set aF : Fin V.rank → ℤ := fun i => if (i : ℕ) < kk then 1 else 0 with haF
  have e1 : (List.ofFn dF).map (fun x => if 0 < x then x - 1 else x) = List.ofFn d₁ := by
    rw [List.map_ofFn]; rfl
  rw [e1, dualLab_splitLab _ _ hkn]

  obtain ⟨ρ, hon, hint, hdiv⟩ := GlobalTheory.T.exists_splitPrime_GL_chart_of_unitaryGroup V P e he ϖ h1 h2
  set ϖL := algebraMap D.host.E (P.adicCompletion D.host.E) (ϖ : D.host.E) with hϖL
  have hv : Formalism.UG.IsUnifV D.host.E P ϖL :=
    (P.valuedAdicCompletion_eq_valuation' (ϖ : D.host.E)).trans
      ((P.valuation_of_algebraMap ϖ).trans (GlobalTheory.LatIntFacts.intValuation_uniformiser P h1 h2))
  have hvO : ϖL ∈ Formalism.UG.Ov D.host.E P := (Formalism.UG.P.cartan_unif_lt_one D.host.E P _ hv).le
  have hϖ0 : ϖL ≠ 0 := by
    intro h0
    have := hv
    unfold Formalism.UG.IsUnifV at this
    rw [h0, map_zero] at this
    exact WithZero.zero_ne_coe this
  let mkD : (Fin V.rank → ℤ) → GL (Fin V.rank) (P.adicCompletion D.host.E) := fun a =>
    ⟨Formalism.UG.diagPow D.host.E P ϖL a, Formalism.UG.diagPow D.host.E P ϖL (-a),
      by simp only [Formalism.UG.diagPow, Matrix.diagonal_mul_diagonal, Pi.neg_apply, ← zpow_add₀ hϖ0, add_neg_cancel,
          zpow_zero, Matrix.diagonal_one],
      by simp only [Formalism.UG.diagPow, Matrix.diagonal_mul_diagonal, Pi.neg_apply, ← zpow_add₀ hϖ0, neg_add_cancel,
          zpow_zero, Matrix.diagonal_one]⟩
  have hmk : ∀ a, ((mkD a : GL (Fin V.rank) (P.adicCompletion D.host.E)) : Matrix (Fin V.rank) (Fin V.rank) _) =
      Formalism.UG.diagPow D.host.E P ϖL a := fun a => rfl
  have hdiag : ∀ g a, ρ g = mkD a → DivAt V e (ϖ : D.host.E) (List.ofFn a) g := fun g a h =>
    hdiv g a 1 (one_mem _) 1 (one_mem _) (by rw [h, hmk]; simp)
  obtain ⟨g, hgS, hg⟩ := hon (mkD d₁)
  obtain ⟨h, hhS, hh⟩ := hon (mkD aF)
  have hgh : ρ (g * h) = mkD dF := by
    rw [map_mul, hg, hh]
    apply Units.ext
    simp only [Units.val_mul, hmk, Formalism.UG.diagPow, Matrix.diagonal_mul_diagonal]
    congr 1
    funext l
    rw [← zpow_add₀ hϖ0]
    congr 1
    have := hk l
    have := hnn' l
    simp only [d₁, aF]
    split_ifs <;> omega
  have hpi' : IsPrimeIdem P e (e + cA D e) := Or.inl ⟨he, rfl⟩
  have pw : ∀ a : Fin V.rank → ℤ, Antitone a → (List.ofFn a).Pairwise fun x y => y ≤ x :=
    fun a ha => List.pairwise_ofFn.2 fun i j hij => ha hij.le
  have hS : ∀ x, Formalism.L2.Theta.SuppAt e V x → ∀ a, Antitone a → DivAt V e (ϖ : D.host.E) (List.ofFn a) x →
      GlobalTheory.SphLabelOps.Reps K x (rep V P (List.ofFn a)) := fun x hx a ha hD =>
    GlobalTheory.SphLabelOps.reps_of_sphOp hK hpi' h1 h2 hx hD
      (GlobalTheory.SphLabelOps.sphOp_rep (GlobalTheory.SphLabelOps.isLab_of_divAt hpi' h1 h2 (pw a ha) hx hD))
  have a₁ : Antitone d₁ := fun i j hij => by
    have := hanti hij
    simp only [d₁]; split_ifs <;> omega
  have a₂ : Antitone aF := fun i j hij => by
    have : (i : ℕ) ≤ j := hij
    simp only [aF]; split_ifs <;> omega
  have r₁ := hS g hgS d₁ a₁ (hdiag g d₁ hg)
  have r₂ := hS h hhS aF a₂ (hdiag h aF hh)
  have hghS : Formalism.L2.Theta.SuppAt e V (g * h) := GlobalTheory.SplitHecke.suppAt_mul hgS hhS
  have r₀ := hS (g * h) hghS dF hanti (hdiag _ _ hgh)
  obtain ⟨T, m, hghT, hT, hTi, hsum⟩ := GlobalTheory.SphLabelOps.reps_mul_decomp K g h _ _ r₁ r₂

  have hx : ∀ x ∈ T, Formalism.L2.Theta.SuppAt e V x ∧ ∃ k₁ ∈ K, ∃ k₂ ∈ K, ∃ k₃ ∈ K, x = k₁ * g * k₂ * h * k₃ := by
    intro x hxT
    obtain ⟨-, γ, hγ, γ', hγ', k₁, hk₁, k₂, hk₂, rfl⟩ := hT x hxT
    obtain ⟨a, ha, b, hb, rfl⟩ := r₁.1 γ hγ
    obtain ⟨a', ha', b', hb', rfl⟩ := r₂.1 γ' hγ'
    have s : ∀ k ∈ K, Formalism.L2.Theta.SuppAt e V k := fun k hk => (hKl k hk).2
    have hxe : k₁ * (a * g * b * (a' * h * b')) * k₂ = k₁ * a * g * (b * a') * h * (b' * k₂) := by group
    rw [hxe]
    refine ⟨?_, k₁ * a, K.mul_mem hk₁ ha, b * a', K.mul_mem hb ha', b' * k₂, K.mul_mem hb' hk₂, rfl⟩
    have m := @GlobalTheory.SplitHecke.suppAt_mul
    exact m (m (m (m (m (s _ hk₁) (s _ ha)) hgS) (m (s _ hb) (s _ ha'))) hhS) (m (s _ hb') (s _ hk₂))

  have cart : ∀ x : GA D V, ∃ a : Fin V.rank → ℤ, Antitone a ∧
      ∃ k₁ ∈ Formalism.UG.GLint (Fin V.rank) (Formalism.UG.Ov D.host.E P), ∃ k₂ ∈ Formalism.UG.GLint (Fin V.rank) (Formalism.UG.Ov D.host.E P),
        ((ρ x : GL (Fin V.rank) (P.adicCompletion D.host.E)) : Matrix (Fin V.rank) (Fin V.rank) _) =
          (k₁ : Matrix (Fin V.rank) (Fin V.rank) _) * Formalism.UG.diagPow D.host.E P ϖL a * (k₂ : Matrix (Fin V.rank) (Fin V.rank) _) :=
    fun x => Formalism.UG.Final.CartanDecomp D.host.E P V.rank ϖL hvO hv (ρ x)
  choose cx hcx k₁x hk₁x k₂x hk₂x hcxe using cart
  have hcxD : ∀ x, DivAt V e (ϖ : D.host.E) (List.ofFn (cx x)) x := fun x =>
    hdiv x (cx x) _ (hk₁x x) _ (hk₂x x) (hcxe x)

  have hineq : ∀ x ∈ T, x ≠ g * h → (∀ i, 0 ≤ cx x i) ∧
      (∑ i, cx x i = ∑ i, dF i ∧ ∑ i, cx x i ^ 2 < ∑ i, dF i ^ 2) := by
    intro x hxT hne
    obtain ⟨sx, k₁, hk₁, k₂, hk₂, k₃, hk₃, hxe⟩ := hx x hxT
    have key := GlobalTheory.T.cartanExponents_nonneg_minusculeTop_product D.host.E P V.rank ϖL hv dF kk hanti hnn' hk (ρ k₁) (hint _ (hKl _ hk₁).1)
      (ρ k₂) (hint _ (hKl _ hk₂).1) (ρ k₃) (hint _ (hKl _ hk₃).1) (cx x) (hcx x) _ (hk₁x x) _ (hk₂x x) (by
        rw [← hcxe x, hxe]
        simp only [map_mul, Units.val_mul, hg, hh, hmk] <;> rfl)
    refine ⟨key.1, key.2.resolve_left fun heq => hne ?_⟩
    have rx := hS x sx (cx x) (hcx x) (hcxD x)
    rw [heq] at rx
    obtain ⟨γ, ⟨hγ, hγx⟩, -⟩ := rx.2 x ⟨1, K.one_mem, 1, K.one_mem, by group⟩
    obtain ⟨a, ha, b, hb, hγe⟩ := r₀.1 γ hγ
    refine (hTi (g * h) hghT x hxT ⟨a, ha, b * (γ⁻¹ * x), K.mul_mem hb hγx, by rw [← mul_assoc, ← hγe]; group⟩).symm
  refine ⟨m (g * h), (hT _ hghT).1, ∑ x ∈ T.erase (g * h), Finsupp.single (List.ofFn (cx x)) (m x : ℂ), ?_, ?_⟩
  · intro d' hd'
    obtain ⟨x, hxT, hd'x⟩ := Finset.mem_biUnion.1 (Finsupp.support_finset_sum hd')
    obtain ⟨hne, hxT⟩ := Finset.mem_erase.1 hxT
    rw [Finset.mem_singleton.1 (Finsupp.support_single_subset hd'x)]
    obtain ⟨c1, c2, c3⟩ := hineq x hxT hne
    refine ⟨fun y hy => ?_, ?_, ?_⟩
    · obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hy
      exact c1 i
    · rw [List.sum_ofFn, List.sum_ofFn]; exact c2
    · rw [List.map_ofFn, List.map_ofFn, List.sum_ofFn, List.sum_ofFn]; exact c3
  · intro M _ _ π u hu
    have hu' : ∀ k ∈ K, π k u = u := fun k hk => hu k (hK ▸ hk)
    rw [GlobalTheory.SphLabelOps.opOf_single, GlobalTheory.SphLabelOps.opOf_single, GlobalTheory.SphLabelOps.opOf_single, opOf_sum_single,
      LinearMap.sum_apply]
    have hsum' := hsum (fun x => if x = g * h then rep V P (List.ofFn dF) else rep V P (List.ofFn (cx x)))
      (fun x hxT => by
        by_cases hxe : x = g * h
        · rw [if_pos hxe, hxe]; exact r₀
        · rw [if_neg hxe]; exact hS x (hx x hxT).1 (cx x) (hcx x) (hcxD x)) M π u hu'
    have lhs : ∑ γ ∈ rep V P (List.ofFn d₁), π γ (∑ γ' ∈ rep V P (List.ofFn aF), π γ' u) =
        ∑ γ ∈ rep V P (List.ofFn d₁), ∑ γ' ∈ rep V P (List.ofFn aF), π (γ * γ') u := by
      refine Finset.sum_congr rfl fun γ _ => ?_
      rw [map_sum]
      refine Finset.sum_congr rfl fun γ' _ => ?_
      rw [map_mul, Module.End.mul_apply]
    rw [lhs, hsum', ← Finset.add_sum_erase _ _ hghT, if_pos rfl]
    congr 1
    · rw [Nat.cast_smul_eq_nsmul]
    · refine Finset.sum_congr rfl fun x hxT => ?_
      rw [if_neg (Finset.mem_erase.1 hxT).1, LinearMap.smul_apply, LinearMap.sum_apply, Nat.cast_smul_eq_nsmul]

end GlobalTheory.SplitTopStep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnitarySegmentOfCentralUnit
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel

noncomputable section

namespace GlobalTheory.UnitLSeg

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def stabForm {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V)
    (l : Module.Dual ℂ V) : Subgroup (GL (Fin N) k) where
  carrier := {g | l ∘ₗ π g = l}
  one_mem' := by
    show l ∘ₗ π 1 = l
    rw [map_one, Module.End.one_eq_id, LinearMap.comp_id]
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at *
    rw [map_mul, Module.End.mul_eq_comp, ← LinearMap.comp_assoc, ha, hb]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at *
    calc l ∘ₗ π a⁻¹ = (l ∘ₗ π a) ∘ₗ π a⁻¹ := by rw [ha]
      _ = l := by rw [LinearMap.comp_assoc, ← Module.End.mul_eq_comp, ← map_mul, mul_inv_cancel, map_one,
            Module.End.one_eq_id, LinearMap.comp_id]

theorem stab_le {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V)
    (χ : kˣ →* ℂˣ) (l : Module.Dual ℂ V) :
    stabForm π l ⊓ (detChar (Fin N) χ).ker ≤ stabForm (twist π (detChar (Fin N) χ)) l := by
  intro g ⟨h1, h2⟩
  have h2' : detChar (Fin N) χ g = 1 := h2
  change l ∘ₗ π g = l at h1
  change l ∘ₗ twist π (detChar (Fin N) χ) g = l
  refine LinearMap.ext fun v => ?_
  rw [LinearMap.comp_apply, twist_apply, h2', Units.val_one, one_smul, ← LinearMap.comp_apply, h1]

theorem coeffLp_of_twist {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] {p : ℝ}
    {π : Representation ℂ (GL (Fin N) k) V} {χ : kˣ →* ℂˣ} (hχ : IsSmoothChar χ) (hu : ∀ z, ‖(χ z : ℂ)‖ = 1)
    (h : CoeffLp p (twist π (detChar (Fin N) χ))) : CoeffLp p π := by
  intro _ _ μ hμ v l hl
  have ho : IsOpen ((stabForm (twist π (detChar (Fin N) χ)) l : Subgroup (GL (Fin N) k)) : Set (GL (Fin N) k)) :=
    Subgroup.isOpen_mono (stab_le π χ l) (IsOpen.inter hl (hχ.detChar (n := Fin N)))
  obtain ⟨F, hF, hm⟩ := h μ hμ v l ho
  refine ⟨F, fun g => ?_, hm⟩
  rw [hF, twist_apply, map_smul, norm_smul, detChar_apply, hu, one_mul]

theorem isUnitarisable_of_twist {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ (GL (Fin N) k) V} {χ : kˣ →* ℂˣ} (hu : ∀ z, ‖(χ z : ℂ)‖ = 1)
    (h : IsUnitarisable (twist π (detChar (Fin N) χ))) : IsUnitarisable π := by
  obtain ⟨B, h1, h2, h3⟩ := h
  refine ⟨B, h1, h2, fun g v w => ?_⟩
  have e := h3 g v w
  have : (detChar (Fin N) χ g : ℂ) * starRingEnd ℂ (detChar (Fin N) χ g) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, detChar_apply, hu]; simp
  rw [twist_apply, twist_apply, B.map_smul, LinearMap.smul_apply, LinearMap.map_smulₛₗ, smul_eq_mul, smul_eq_mul,
    ← mul_assoc, this, one_mul] at e
  exact e

theorem isUnitarisable_of_equiv' {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {π : Representation ℂ G V} {σ : Representation ℂ G W} (E : π.Equiv σ) (h : IsUnitarisable σ) : IsUnitarisable π := by
  obtain ⟨B, h1, h2, h3⟩ := h
  refine ⟨(B.comp E.toLinearMap).compl₂ E.toLinearMap, fun v w => h1 _ _, fun v hv => h2 _ ?_, fun g v w => ?_⟩
  · exact fun h => hv (E.toLinearEquiv.map_eq_zero_iff.1 h)
  · show B (E.toIntertwiningMap (π g v)) (E.toIntertwiningMap (π g w)) = _
    rw [E.toIntertwiningMap.isIntertwining, E.toIntertwiningMap.isIntertwining, h3]
    rfl

end GlobalTheory.UnitLSeg

open GlobalTheory.UnitLSeg in
theorem GlobalTheory.UnitLSeg.main : GlobalTheory.Published.EssSquareIntegrableSegments → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] (δ : IrrGL k) (Δ : Segment k) (ω : kˣ →* ℂˣ), IsLSeg Δ δ.rep → HasCentralChar δ.rep ω → (∀ z, ‖(ω z : ℂ)‖ = 1) → 1 ≤ δ.1 ∧ IsSqIntCoeff δ.rep ∧ GlobalTheory.GenericUnitary.IsUnitaryLSeg δ := by
  intro hP k _ _ _ _ _ δ Δ ω hL hω hωu
  have hd : 1 ≤ δ.1 := by
    have h1 := hL.deg_eq
    have := Nat.mul_pos Δ.len_pos Δ.d_pos
    simp only [Segment.deg] at h1
    omega
  obtain ⟨χ, hχ, hsq⟩ := (hP k δ hd).2 ⟨Δ, hL⟩
  have hU : IsUnitarisable (δ.tw χ hχ).rep :=
    GlobalTheory.T.unitarisable_of_square_integrable k _ _ _ (δ.tw χ hχ).2.rep.smooth (δ.tw χ hχ).2.rep.irr (fun {c d} => @hsq c d)
  haveI := Model.nontrivial_of_isIrreducible (δ.tw χ hχ).2.rep.irr
  have hc := hasCentralChar_of_equiv (δ.twEquiv χ hχ) (hasCentralChar_twist hω χ)
  have hχu : ∀ z, ‖(χ z : ℂ)‖ = 1 := fun z => by
    have h1 := GlobalTheory.LocLanglands.TemperedRec.norm_centralChar_eq_one hU hc z
    rw [Fintype.card_fin, MonoidHom.mul_apply, MonoidHom.pow_apply, Units.val_mul, Units.val_pow_eq_pow_val, norm_mul,
      norm_pow, hωu, one_mul] at h1
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by omega)).1 h1
  have hU' : IsUnitarisable δ.rep :=
    isUnitarisable_of_twist hχu (isUnitarisable_of_equiv' (δ.twEquiv χ hχ) hU)
  have h1 : CoeffLp 2 (δ.tw χ hχ).rep := hsq
  have h2 : CoeffLp 2 (twist δ.rep (detChar (Fin δ.1) χ)) :=
    @GlobalTheory.Published.TemperedProduct.coeffLp_of_equiv k _ _ _ _ _ _ _ _ δ.1 2 _ _ (δ.twEquiv χ hχ).symm @h1
  have hsq' : IsSqIntCoeff δ.rep := coeffLp_of_twist hχ hχu h2
  exact ⟨hd, hsq', ⟨Δ, hL⟩, hU'⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeilTraceEqOfSameWdStatement
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_trace_eq_of_same_wd : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ) (r r' : G E Ω →* GL (Fin a) (Qbar l)) (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (h : IsPlaceOver A w) (x : WD h), ((l : ℕ) : 𝓞 E) ∉ w.asIdeal → IsWDOf ι r x → IsWDOf ι r' x → ∀ σ : Weil h, (r (σ : G E Ω)).val.trace = (r' (σ : G E Ω)).val.trace := by
  first | exact @GlobalTheory.WdTrace.trace_eq_of_isWDOf | exact GlobalTheory.WdTrace.trace_eq_of_isWDOf | (intros; apply GlobalTheory.WdTrace.trace_eq_of_isWDOf <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ZeroEigensystemNotPassageOfFiniteType
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ZeroPassage

theorem dualPoly_coeff_zero {K : Type} [Field K] (s : K) (p : K[X]) (hp : p ≠ 0) : (dualPoly s p).coeff 0 = 1 := by
  unfold dualPoly
  rw [coeff_C_mul, coeff_zero_eq_eval_zero, eval_comp]
  simp [← coeff_zero_eq_eval_zero, hp]

theorem heckePoly_zero {L Pl : Type} [Field L] (n : ℕ) (q : Pl → ℕ) (P : Pl) :
    Formalism.L2.Col.heckePoly n q (fun _ => (0 : L)) P = 0 := by
  simp [Formalism.L2.Col.heckePoly, Formalism.L2.Col.heckePolyOf]

theorem mem_resSet_of_mem_ixFin3 {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G]
    {Pl0 I0 Ty : Type} {B : BlockDat K G Pl0} (D : InertDat3 B I0 Ty) {X : Finset (G → K)}
    {p : Typ3 K Pl0 I0 Ty} (hp : p ∈ D.ixFin3 X) : p.1 ∈ B.resSet X := by
  unfold InertDat3.ixFin3 at hp
  split_ifs at hp with hfin
  · rw [Set.Finite.mem_toFinset] at hp
    refine ⟨hp.1, fun hb => hp.2.2 ?_⟩
    have hle : D.inertTypeEigenspaceSum p ≤ B.partF p.1 := by
      refine iSup₂_le fun x hx => ?_
      refine le_trans ?_ (Formalism.L2.Col.eigAt_le_eigSum (op := B.op) (C := B.HasRes p.1) (x := fun i => x (Sum.inl i)) hx.1)
      exact le_iInf fun i => iInf_le (fun k => (D.opAll k).maxGenEigenspace (x k)) (Sum.inl i)
    rw [eq_bot_iff] at hb ⊢
    exact le_trans (Submodule.comap_mono (Submodule.map_mono hle)) hb
  · simp at hp

theorem zero_not_passage : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), R.WeakCharacterisation F → ∀ j (p : A3.fam3.base3.Ix), ¬ cxSys D.what₂.embLL ((A3.liftI j A3.A.μ0).HasRes3 (A3.fam3.tr3 j p.1)) 0 := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F h j p
  rintro ⟨x, hx, hx0⟩
  obtain ⟨P, hP⟩ := (GlobalTheory.CoreThree.heckeCharacterisation_places_parts_of_weak R F h).2.2.2.2.2.2
  have hxz : (fun i => x (Sum.inl i)) = fun _ => (0 : D.what₂.LL) := by
    funext i
    have h1 := congrFun hx0 (Sum.inl i)
    exact (map_eq_zero_iff _ D.what₂.embLL.injective).1 h1.symm
  let P' : (A3.A.fam.L j A3.A.μ0).Pl := ⟨P, hP⟩
  have hres := hx.1 P'
  rw [hxz] at hres
  replace hres := (heckePoly_zero (L := D.what₂.LL) (Pl := (A3.A.fam.L j A3.A.μ0).Pl) _ _ _).symm.trans hres
  have hmem : p.1.1 ∈ (A3.A.fam.R A3.A.μ0).resSet A3.A.X := mem_resSet_of_mem_ixFin3 (A3.rowI A3.A.μ0) p.2
  have hc : (p.1.1 P).coeff 0 = 1 :=
    (A3.A.fam.R A3.A.μ0).lf_coeff_zero_of_mem_resSet (fun Q => (h.base.fam.degR A3.A.μ0 Q).1) hmem P
  have hne : p.1.1 P ≠ 0 := fun h0 => by rw [h0, coeff_zero] at hc; exact zero_ne_one hc
  have hb : ((A3.A.fam.L j A3.A.μ0).blockProd P').coeff 0 = 1 := by
    rw [coeff_zero_eq_eval_zero]; exact (A3.A.fam.L j A3.A.μ0).lf_blockProd_eval_zero P'
  have ht : ((A3.fam3.tr3 j p.1).1 ((A3.A.fam.L j A3.A.μ0).pl P')).coeff 0 = 1 := dualPoly_coeff_zero _ _ hne
  have h2 := congrArg (fun f => Polynomial.coeff f 0) hres
  simp only [coeff_zero, mul_coeff_zero, hb, ht, mul_one] at h2
  exact zero_ne_one h2

end GlobalTheory.ZeroPassage
end
end

