import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0064
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0653
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0668
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0677
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0683
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0672
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0669
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0654
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0655
import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0656

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantCoeffIterateInvariantDerivationMem
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.LawDer

set_option autoImplicit false

namespace GlobalTheory.LawDer.Kernel

variable {R : Type} [CommRing R] {d : ℕ}

open MvPowerSeries in
set_option autoImplicit false in
variable {R : Type} [CommRing R] {d : ℕ} in
private lemma coeff_atZero_eq_coeff_mapDomain_inl {S : Type} [CommRing S] {n : ℕ}
    (G : MvPowerSeries (Fin n ⊕ Fin n) S) (α : Fin n →₀ ℕ) :
    coeff α (_root_.GlobalTheory.LawDer.atZero G) = coeff (Finsupp.mapDomain Sum.inl α) G :=
  (_root_.GlobalTheory.coeff_subst_restrict_sum G).1 α

open MvPowerSeries in
set_option autoImplicit false in
variable {R : Type} [CommRing R] {d : ℕ} in
private lemma coeff_subst_X_comp_eq_finsum {σ τ S : Type} [CommRing S] [Finite σ] [DecidableEq τ] (g : σ → τ)
    (F : MvPowerSeries σ S) (γ : τ →₀ ℕ) :
    coeff γ (subst (fun s => (X (g s) : MvPowerSeries τ S)) F) =
      ∑ᶠ e : σ →₀ ℕ, if γ = Finsupp.mapDomain g e then coeff e F else 0 := by
  rw [coeff_subst (hasSubst_of_constantCoeff_zero fun s => constantCoeff_X _)]
  refine finsum_congr fun e => ?_
  rw [← Finsupp.prod_mapDomain_index (h := fun t k => (X t : MvPowerSeries τ S) ^ k) (by simp)
    (by intros; simp [pow_add]), ← monomial_one_eq, coeff_monomial]
  split_ifs <;> simp

open MvPowerSeries in
set_option autoImplicit false in
variable {R : Type} [CommRing R] {d : ℕ} in
private lemma coeff_subst_X_comp_eq_zero_of_not_mem_range {σ τ S : Type} [CommRing S] [Finite σ] (g : σ → τ)
    (F : MvPowerSeries σ S) {γ : τ →₀ ℕ} (hγ : γ ∉ Set.range (Finsupp.mapDomain g)) :
    coeff γ (subst (fun s => (X (g s) : MvPowerSeries τ S)) F) = 0 := by
  classical
  rw [coeff_subst_X_comp_eq_finsum]
  exact (finsum_congr fun e => if_neg fun h => hγ ⟨e, h.symm⟩).trans finsum_zero

open MvPowerSeries in
set_option autoImplicit false in
variable {R : Type} [CommRing R] {d : ℕ} in
private lemma coeff_mapDomain_subst_X_comp_of_injective {σ τ S : Type} [CommRing S] [Finite σ] {g : σ → τ}
    (hg : Function.Injective g) (F : MvPowerSeries σ S) (e : σ →₀ ℕ) :
    coeff (Finsupp.mapDomain g e) (subst (fun s => (X (g s) : MvPowerSeries τ S)) F) =
      coeff e F := by
  classical
  rw [coeff_subst_X_comp_eq_finsum, finsum_eq_single _ e, if_pos rfl]
  intro e' he'
  rw [if_neg]
  exact fun h => he' (Finsupp.mapDomain_injective hg h).symm

open MvPowerSeries in
set_option autoImplicit false in
variable {R : Type} [CommRing R] {d : ℕ} in

theorem _root_.GlobalTheory.LawDer.Kernel.constantCoeff_iterate_invDer_mem : ∀ (B Q : Type) [CommRing B] [CommRing Q] [Algebra B Q] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B), (∀ i, constantCoeff (μ i) = 0) → ∀ (N : Ideal B) (l : MvPowerSeries (Fin d) Q) (j : Fin d), _root_.GlobalTheory.QLog.In N (_root_.GlobalTheory.Katz.cob1 (_root_.GlobalTheory.QLog.up Q μ) l) → _root_.GlobalTheory.Katz.lin l = Pi.single j 1 → ∀ (u : Fin d → B) (n : ℕ), 2 ≤ n → ∃ b ∈ N, constantCoeff ((_root_.GlobalTheory.LawDer.invDer (_root_.GlobalTheory.QLog.up Q μ) (fun i => algebraMap B Q (u i)))^[n] l) = algebraMap B Q b := by
  intro B Q _ _ _ d μ hμ N l j hc hl u n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  unfold _root_.GlobalTheory.QLog.In at hc
  set μ' := _root_.GlobalTheory.QLog.up Q μ with hμ'
  set D := _root_.GlobalTheory.LawDer.invDer μ' (fun i => algebraMap B Q (u i)) with hD
  let S : Submodule B Q := Submodule.map (Algebra.linearMap B Q) N
  have memS : ∀ x : Q, x ∈ S ↔ ∃ b ∈ N, x = algebraMap B Q b := fun x => by
    simp only [S, Submodule.mem_map, Algebra.linearMap_apply]
    exact ⟨fun ⟨b, hb, h⟩ => ⟨b, hb, h.symm⟩, fun ⟨b, hb, h⟩ => ⟨b, hb, h.symm⟩⟩
  have hμ0 : ∀ i, constantCoeff (μ' i) = 0 := fun i => by
    simp [μ', _root_.GlobalTheory.QLog.up, constantCoeff_map, hμ i]
  have hlin := _root_.GlobalTheory.LawDer.Linear.invDer_linear Q d μ' hμ0 (fun i => algebraMap B Q (u i))
  have hlinD : ∀ F G : MvPowerSeries (Fin d) Q, D (F + G) = D F + D G := hlin.1
  have hcoeffD : ∀ (F : MvPowerSeries (Fin d) Q) (β : Fin d →₀ ℕ), coeff β (D F) =
      ∑ i, algebraMap B Q (u i) * (coeff (Finsupp.mapDomain Sum.inl β +
        Finsupp.single (Sum.inr i) 1) (subst μ' F) *
          ((Finsupp.mapDomain Sum.inl β (Sum.inr i) : Q) + 1)) := by
    intro F β
    rw [hD]
    unfold _root_.GlobalTheory.LawDer.invDer
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [coeff_smul, coeff_atZero_eq_coeff_mapDomain_inl, coeff_pderiv]
  have hP : ∀ F : MvPowerSeries (Fin d) Q, (∀ α, coeff α F ∈ S) → ∀ β, coeff β (D F) ∈ S := by
    intro F hF β
    rw [hcoeffD]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [← Algebra.smul_def]
    refine S.smul_mem _ ?_
    rw [← Nat.cast_succ, mul_comm, ← nsmul_eq_mul]
    exact nsmul_mem (_root_.GlobalTheory.SubstSub.coeff_subst_up_mem B Q (Fin d) (Fin d ⊕ Fin d) S F μ
      hμ hF _) _
  have hPit : ∀ (k : ℕ) (F : MvPowerSeries (Fin d) Q), (∀ α, coeff α F ∈ S) →
      ∀ β, coeff β (D^[k] F) ∈ S := by
    intro k
    induction k with
    | zero => intro F hF; simpa using hF
    | succ k ih => intro F hF; rw [Function.iterate_succ_apply]; exact ih _ (hP F hF)
  have hadd : ∀ (k : ℕ) (F G : MvPowerSeries (Fin d) Q), D^[k] (F + G) = D^[k] F + D^[k] G := by
    intro k
    induction k with
    | zero => intro F G; rfl
    | succ k ih =>
      intro F G
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, Function.iterate_succ_apply,
        hlinD, ih]
  have hD0 : D 0 = 0 := by
    have h := hlinD 0 0
    rw [add_zero] at h
    simpa using h
  have hDC : ∀ c : Q, D (C c) = 0 := by
    intro c
    ext β
    rw [hcoeffD]
    simp [subst_C, coeff_C]
  have hCit : ∀ (k : ℕ) (c : Q), D^[k + 1] (C c) = 0 := fun k c => by
    rw [Function.iterate_succ_apply, hDC, Function.iterate_fixed hD0]
  have hzero : ∀ (β : Fin d →₀ ℕ) (i : Fin d), Finsupp.mapDomain Sum.inl β (Sum.inr i) = 0 :=
    fun β i => Finsupp.mapDomain_notin_range _ _ (by simp)
  have hsplit : subst μ' l = _root_.GlobalTheory.Katz.cob1 μ' l + _root_.GlobalTheory.Katz.inL l +
      _root_.GlobalTheory.Katz.inR l := by
    unfold _root_.GlobalTheory.Katz.cob1
    ring
  have hleft : ∀ (β : Fin d →₀ ℕ) (i : Fin d), coeff (Finsupp.mapDomain Sum.inl β +
      Finsupp.single (Sum.inr i) 1) (_root_.GlobalTheory.Katz.inL l) = 0 := by
    intro β i
    unfold _root_.GlobalTheory.Katz.inL
    apply coeff_subst_X_comp_eq_zero_of_not_mem_range
    rintro ⟨e, he⟩
    have h := congrArg (fun x => x (Sum.inr i)) he
    simp [hzero] at h
  have hright : ∀ (β : Fin d →₀ ℕ) (i : Fin d), coeff (Finsupp.mapDomain Sum.inl β +
      Finsupp.single (Sum.inr i) 1) (_root_.GlobalTheory.Katz.inR l) =
        if β = 0 then (Pi.single j 1 : Fin d → Q) i else 0 := by
    intro β i
    unfold _root_.GlobalTheory.Katz.inR
    split_ifs with hβ
    · subst hβ
      rw [Finsupp.mapDomain_zero, zero_add, ← Finsupp.mapDomain_single,
        coeff_mapDomain_subst_X_comp_of_injective Sum.inr_injective, ← hl]
      rfl
    · apply coeff_subst_X_comp_eq_zero_of_not_mem_range
      rintro ⟨e, he⟩
      obtain ⟨k, hk⟩ : ∃ k, β k ≠ 0 := by
        by_contra h
        push_neg at h
        exact hβ (Finsupp.ext h)
      have h := congrArg (fun x => x (Sum.inl k)) he
      rw [Finsupp.mapDomain_notin_range _ _ (by simp)] at h
      simp [Finsupp.mapDomain_apply Sum.inl_injective] at h
      omega
  have hg : ∀ β, coeff β (D l - C (algebraMap B Q (u j))) ∈ S := by
    intro β
    have hsum : coeff β (D l - C (algebraMap B Q (u j))) = ∑ i, algebraMap B Q (u i) *
        coeff (Finsupp.mapDomain Sum.inl β + Finsupp.single (Sum.inr i) 1)
          (_root_.GlobalTheory.Katz.cob1 μ' l) := by
      rw [map_sub, hcoeffD]
      simp only [hsplit, map_add, hleft, hright, hzero, Nat.cast_zero, zero_add, add_zero,
        mul_one, mul_add, Finset.sum_add_distrib]
      by_cases hβ : β = 0 <;> simp [hβ, Pi.single_apply, coeff_C]
    rw [hsum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [← Algebra.smul_def]
    refine S.smul_mem _ ((memS _).2 ?_)
    obtain ⟨b, hb, h⟩ := hc (Finsupp.mapDomain Sum.inl β + Finsupp.single (Sum.inr i) 1)
    exact ⟨b, hb, h⟩
  have key : D^[m + 2] l = D^[m + 1] (D l - C (algebraMap B Q (u j))) := by
    conv_lhs => rw [Function.iterate_succ_apply, ← sub_add_cancel (D l) (C (algebraMap B Q (u j)))]
    rw [hadd, hCit, add_zero]
  rw [key]
  obtain ⟨b, hb, h⟩ := (memS _).1 (hPit (m + 1) _ hg 0)
  refine ⟨b, hb, ?_⟩
  rw [← coeff_zero_eq_constantCoeff_apply]
  exact h

end GlobalTheory.LawDer.Kernel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantCoeffSubstZero
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Katz.PullQuasiLog

theorem lift_X (p : ℕ) [Fact p.Prime] {k : Type} [Field k] [CharP k p] {σ : Type} (j : σ) :
    Katz.lift p (X j : MvPowerSeries σ k) = X j := by
  classical
  ext α
  rw [coeff_lift, coeff_X, coeff_X]
  split_ifs <;> simp

theorem intBy_le_one (p : ℕ) [Fact p.Prime] {k : Type} [Field k] [CharP k p] {σ : Type}
    (c : WittVector p k) : intBy p k σ c ≤ intBy p k σ 1 := by
  intro f hf α
  obtain ⟨w, hw⟩ := hf α
  exact ⟨c * w, by rw [hw, one_mul]⟩

theorem constantCoeff_subst_zero {R : Type} [CommRing R] {σ τ : Type} [Finite σ]
    {a : σ → MvPowerSeries τ R} (ha : ∀ s, constantCoeff (a s) = 0) {f : MvPowerSeries σ R}
    (hf : constantCoeff f = 0) : constantCoeff (subst a f) = 0 :=
  constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero ha) ha hf

theorem elim_const {R : Type} [CommRing R] {d : ℕ} {τ : Type} {u v : Fin d → MvPowerSeries τ R}
    (hu : ∀ i, constantCoeff (u i) = 0) (hv : ∀ i, constantCoeff (v i) = 0) :
    ∀ s, constantCoeff (Sum.elim u v s) = 0 := fun s => by cases s <;> simp [hu, hv]

theorem main : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (d e : ℕ) (ν : Fin e → MvPowerSeries (Fin e ⊕ Fin e) k) (hν : IsLaw ν), ∀ f ∈ quasiLog p hν, subst (fun j => Katz.lift p (X j : MvPowerSeries (Fin e) k)) f = f ∧ (∀ (d' : ℕ) (φ : Fin d → MvPowerSeries (Fin d') k) (ψ : Fin e → MvPowerSeries (Fin d) k), (∀ j, constantCoeff (φ j) = 0) → (∀ j, constantCoeff (ψ j) = 0) → subst (fun l => Katz.lift p (subst φ (ψ l))) f - subst (fun j => Katz.lift p (φ j)) (subst (fun l => Katz.lift p (ψ l)) f) ∈ intBy p k (Fin d') 1) ∧ ∀ φ ψ : Fin e → MvPowerSeries (Fin d) k, (∀ j, constantCoeff (φ j) = 0) → (∀ j, constantCoeff (ψ j) = 0) → subst (fun l => Katz.lift p (op ν φ ψ l)) f - subst (fun l => Katz.lift p (φ l)) f - subst (fun l => Katz.lift p (ψ l)) f ∈ intBy p k (Fin d) 1 := by
  intro p _ k _ _ _ d e ν hν f hf
  have hf' : f ∈ quasiInt p k (Fin e) ∧ cob1 (fun i => lift p (ν i)) f ∈ intBy p k _ 1 := hf
  have hred := fun (σ : Type) => GlobalTheory.T.mvPowerSeries_reduction_mod_prime_rules p k σ
  refine ⟨?_, ?_, ?_⟩
  · have : (fun j => Katz.lift p (X j : MvPowerSeries (Fin e) k)) = X := funext fun j => lift_X p j
    rw [this, subst_self]; rfl
  · intro d' φ ψ hφ hψ
    have hΦ : ∀ j, constantCoeff (lift p (φ j)) = 0 := fun j => constantCoeff_lift p (hφ j)
    have hΨ : ∀ j, constantCoeff (lift p (ψ j)) = 0 := fun j => constantCoeff_lift p (hψ j)
    rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero hΨ)
      (hasSubst_of_constantCoeff_zero hΦ)]
    apply intBy_le_one p (p : WittVector p k)
    refine GlobalTheory.T.subst_sub_subst_integral_of_integral_differential p k (Fin e) (Fin d') _ _ (fun l => subst φ (ψ l)) f
      (fun l => constantCoeff_lift p (constantCoeff_subst_zero hφ (hψ l)))
      (fun l => constantCoeff_subst_zero hΦ (hΨ l))
      (fun l => (hred (Fin d')).2.2.1 _)
      (fun l => (GlobalTheory.T.isIntegralReducingToMvPowerSeries_subst p k (Fin d) (Fin d') (fun j => lift p (φ j)) φ hΦ
        (fun j => (hred (Fin d')).2.2.1 _)).1 _ _ ((hred (Fin d)).2.2.1 _)) hf'.1
  · intro φ ψ hφ hψ
    set Φ : Fin e → MvPowerSeries (Fin d) (Fr p k) := fun l => lift p (φ l) with hΦdef
    set Ψ : Fin e → MvPowerSeries (Fin d) (Fr p k) := fun l => lift p (ψ l) with hΨdef
    have hΦ : ∀ j, constantCoeff (Φ j) = 0 := fun j => constantCoeff_lift p (hφ j)
    have hΨ : ∀ j, constantCoeff (Ψ j) = 0 := fun j => constantCoeff_lift p (hψ j)
    have hL : ∀ i, constantCoeff (lift p (ν i)) = 0 := fun i => constantCoeff_lift p (hν.const i)
    have hcalc := GlobalTheory.T.powerSeriesEvalTwoGroups_rules (Fr p k) e (Fin d) (Fin d) Φ Ψ hΦ hΨ
    have hredE : ∀ s, Red p (Sum.elim Φ Ψ s) (Sum.elim φ ψ s) := fun s => by
      cases s <;> exact (hred (Fin d)).2.2.1 _
    have hsub := GlobalTheory.T.isIntegralReducingToMvPowerSeries_subst p k (Fin e ⊕ Fin e) (Fin d) (Sum.elim Φ Ψ) (Sum.elim φ ψ)
      (elim_const hΦ hΨ) hredE
    have hcob : at2 (cob1 (fun i => lift p (ν i)) f) Φ Ψ =
        subst (op (fun i => lift p (ν i)) Φ Ψ) f - subst Φ f - subst Ψ f := by
      unfold cob1
      rw [(hcalc.2.2.1 _ _).2, (hcalc.2.2.1 _ _).2, hcalc.1, hcalc.2.1,
        hcalc.2.2.2.2.2.1 e _ hL f]
      rfl
    have h1 : at2 (cob1 (fun i => lift p (ν i)) f) Φ Ψ ∈ intBy p k (Fin d) 1 :=
      hsub.2 1 _ hf'.2
    have h2 : subst (fun l => lift p (op ν φ ψ l)) f - subst (op (fun i => lift p (ν i)) Φ Ψ) f
        ∈ intBy p k (Fin d) 1 := by
      apply intBy_le_one p (p : WittVector p k)
      refine GlobalTheory.T.subst_sub_subst_integral_of_integral_differential p k (Fin e) (Fin d) _ _ (op ν φ ψ) f
        (fun l => constantCoeff_lift p (constantCoeff_subst_zero (elim_const hφ hψ) (hν.const l)))
        (fun l => constantCoeff_subst_zero (elim_const hΦ hΨ) (hL l))
        (fun l => (hred (Fin d)).2.2.1 _)
        (fun l => hsub.1 _ _ ((hred (Fin e ⊕ Fin e)).2.2.1 _)) hf'.1
    have := add_mem h2 h1
    rw [hcob] at this
    convert this using 1
    abel

end GlobalTheory.Katz.PullQuasiLog
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantCoeffUpNmul
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
open TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.DefectComp

variable {R Q : Type} [CommRing R] [CommRing Q] [Algebra R Q] {d : ℕ}

set_option autoImplicit false in
open MvPowerSeries TensorProduct in
variable {R Q : Type} [CommRing R] [CommRing Q] [Algebra R Q] {d : ℕ} in
variable {S : Type} [CommRing S] in
private lemma nmul_zero (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) S) :
    _root_.GlobalTheory.QLog.nmul μ 0 = fun _ => 0 := rfl

set_option autoImplicit false in
open MvPowerSeries TensorProduct in
variable {R Q : Type} [CommRing R] [CommRing Q] [Algebra R Q] {d : ℕ} in
variable {S : Type} [CommRing S] in
private lemma nmul_succ_eq_op_X (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) S) (k : ℕ) :
    _root_.GlobalTheory.QLog.nmul μ (k + 1) =
      _root_.GlobalTheory.Katz.op μ (_root_.GlobalTheory.QLog.nmul μ k) (fun i => X i) := by
  rw [_root_.GlobalTheory.QLog.nmul, _root_.GlobalTheory.QLog.nmul, Function.iterate_succ_apply']

set_option autoImplicit false in
open MvPowerSeries TensorProduct in
variable {R Q : Type} [CommRing R] [CommRing Q] [Algebra R Q] {d : ℕ} in
variable {S : Type} [CommRing S] in
private lemma hasSubst_sumElim_of_constantCoeff_eq_zero {τ : Type} {v w : Fin d → MvPowerSeries τ S}
    (hv : ∀ i, constantCoeff (v i) = 0) (hw : ∀ i, constantCoeff (w i) = 0) :
    HasSubst (Sum.elim v w) :=
  hasSubst_of_constantCoeff_zero fun s => by cases s <;> simp [hv, hw]

set_option autoImplicit false in
open MvPowerSeries TensorProduct in
variable {R Q : Type} [CommRing R] [CommRing Q] [Algebra R Q] {d : ℕ} in
variable {S : Type} [CommRing S] in
private lemma constantCoeff_katz_op_eq_zero {τ : Type} (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) S)
    (hμ : ∀ i, constantCoeff (μ i) = 0) {v w : Fin d → MvPowerSeries τ S}
    (hv : ∀ i, constantCoeff (v i) = 0) (hw : ∀ i, constantCoeff (w i) = 0) (i : Fin d) :
    constantCoeff (_root_.GlobalTheory.Katz.op μ v w i) = 0 :=
  constantCoeff_subst_eq_zero (hasSubst_sumElim_of_constantCoeff_eq_zero hv hw)
    (fun s => by cases s <;> simp [hv, hw]) (hμ i)

set_option autoImplicit false in
open MvPowerSeries TensorProduct in
variable {R Q : Type} [CommRing R] [CommRing Q] [Algebra R Q] {d : ℕ} in
variable {S : Type} [CommRing S] in
private lemma constantCoeff_nmul_eq_zero' (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) S)
    (hμ : ∀ i, constantCoeff (μ i) = 0) (k : ℕ) (i : Fin d) :
    constantCoeff (_root_.GlobalTheory.QLog.nmul μ k i) = 0 := by
  induction k generalizing i with
  | zero => simp [nmul_zero]
  | succ k ih =>
    rw [nmul_succ_eq_op_X]
    exact constantCoeff_katz_op_eq_zero μ hμ ih (fun j => constantCoeff_X j) i

set_option autoImplicit false in
open MvPowerSeries TensorProduct in
variable {R Q : Type} [CommRing R] [CommRing Q] [Algebra R Q] {d : ℕ} in
variable {S : Type} [CommRing S] in
private lemma mvPowerSeries_map_injective {σ A B : Type} [CommRing A] [CommRing B] {h : A →+* B}
    (hh : Function.Injective h) : Function.Injective (map (σ := σ) h) := fun p q hpq => by
  ext n
  apply hh
  simpa using congrArg (coeff n) hpq

set_option autoImplicit false in
open MvPowerSeries TensorProduct in
variable {R Q : Type} [CommRing R] [CommRing Q] [Algebra R Q] {d : ℕ} in
variable {S : Type} [CommRing S] in
private lemma subst_zero_divisor {σ τ : Type} {c : σ → MvPowerSeries τ S} (hc : HasSubst c) :
    subst c (0 : MvPowerSeries σ S) = 0 := by
  rw [← coe_substAlgHom hc, map_zero]

set_option autoImplicit false in
open MvPowerSeries TensorProduct in
variable {R Q : Type} [CommRing R] [CommRing Q] [Algebra R Q] {d : ℕ} in
variable {S : Type} [CommRing S] in
private lemma subst_subst_sumElim_eq_subst_sumElim_subst {τ υ : Type} {v w : Fin d → MvPowerSeries τ S}
    (hv : ∀ i, constantCoeff (v i) = 0) (hw : ∀ i, constantCoeff (w i) = 0)
    {c : τ → MvPowerSeries υ S} (hc : HasSubst c) (g : MvPowerSeries (Fin d ⊕ Fin d) S) :
    subst c (subst (Sum.elim v w) g) =
      subst (Sum.elim (fun j => subst c (v j)) (fun j => subst c (w j))) g := by
  rw [subst_comp_subst_apply (hasSubst_sumElim_of_constantCoeff_eq_zero hv hw) hc]
  congr 1
  funext s
  cases s <;> rfl

set_option autoImplicit false in
open MvPowerSeries TensorProduct in
variable {R Q : Type} [CommRing R] [CommRing Q] [Algebra R Q] {d : ℕ} in
variable {S : Type} [CommRing S] in
private lemma subst_katz_op_eq_op_subst {τ υ : Type} (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) S)
    {v w : Fin d → MvPowerSeries τ S}
    (hv : ∀ i, constantCoeff (v i) = 0) (hw : ∀ i, constantCoeff (w i) = 0)
    {c : τ → MvPowerSeries υ S} (hc : HasSubst c) (i : Fin d) :
    subst c (_root_.GlobalTheory.Katz.op μ v w i) =
      _root_.GlobalTheory.Katz.op μ (fun j => subst c (v j)) (fun j => subst c (w j)) i :=
  subst_subst_sumElim_eq_subst_sumElim_subst hv hw hc (μ i)

set_option autoImplicit false in
open MvPowerSeries TensorProduct in
variable {R Q : Type} [CommRing R] [CommRing Q] [Algebra R Q] {d : ℕ} in
variable {S : Type} [CommRing S] in
private lemma nmul_add_eq_op {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) S}
    (hG : _root_.GlobalTheory.Katz.IsLaw μ) (a b : ℕ) :
    _root_.GlobalTheory.QLog.nmul μ (a + b) =
      _root_.GlobalTheory.Katz.op μ (_root_.GlobalTheory.QLog.nmul μ a) (_root_.GlobalTheory.QLog.nmul μ b) := by
  have hμ := hG.const
  have hN := constantCoeff_nmul_eq_zero' μ hμ
  have ha : HasSubst (_root_.GlobalTheory.QLog.nmul μ a) := hasSubst_of_constantCoeff_zero (hN a)
  induction b with
  | zero =>
    funext i
    have h := congrArg (subst (_root_.GlobalTheory.QLog.nmul μ a))
      (congrFun hG.unit i)
    rw [subst_katz_op_eq_op_subst μ (fun j => constantCoeff_X j) (fun _ => by simp) ha] at h
    simp only [subst_X ha, subst_zero_divisor ha] at h
    rw [Nat.add_zero, nmul_zero]
    exact h.symm
  | succ b ih =>
    rw [← Nat.add_assoc, nmul_succ_eq_op_X, ih, nmul_succ_eq_op_X]
    funext i
    have hc : HasSubst (Sum.elim (_root_.GlobalTheory.QLog.nmul μ a)
        (Sum.elim (_root_.GlobalTheory.QLog.nmul μ b) fun j => (X j : MvPowerSeries (Fin d) S))) :=
      hasSubst_of_constantCoeff_zero fun s => by rcases s with s | s | s <;> simp [hN]
    have h := congrArg (subst (Sum.elim (_root_.GlobalTheory.QLog.nmul μ a)
        (Sum.elim (_root_.GlobalTheory.QLog.nmul μ b) fun j => (X j : MvPowerSeries (Fin d) S))))
      (congrFun hG.assoc i)
    have h1 : ∀ j, constantCoeff (_root_.GlobalTheory.Katz.x1 (R := S) (d := d) j) = 0 := fun j => by
      simp [_root_.GlobalTheory.Katz.x1]
    have h2 : ∀ j, constantCoeff (_root_.GlobalTheory.Katz.x2 (R := S) (d := d) j) = 0 := fun j => by
      simp [_root_.GlobalTheory.Katz.x2]
    have h3 : ∀ j, constantCoeff (_root_.GlobalTheory.Katz.x3 (R := S) (d := d) j) = 0 := fun j => by
      simp [_root_.GlobalTheory.Katz.x3]
    rw [subst_katz_op_eq_op_subst μ (constantCoeff_katz_op_eq_zero μ hμ h1 h2) h3 hc,
      subst_katz_op_eq_op_subst μ h1 (constantCoeff_katz_op_eq_zero μ hμ h2 h3) hc] at h
    simp_rw [subst_katz_op_eq_op_subst μ h1 h2 hc, subst_katz_op_eq_op_subst μ h2 h3 hc] at h
    simp only [_root_.GlobalTheory.Katz.x1, _root_.GlobalTheory.Katz.x2, _root_.GlobalTheory.Katz.x3,
      subst_X hc, Sum.elim_inl, Sum.elim_inr] at h
    exact h

set_option autoImplicit false in
open MvPowerSeries TensorProduct in
variable {R Q : Type} [CommRing R] [CommRing Q] [Algebra R Q] {d : ℕ} in
variable {S : Type} [CommRing S] in
private lemma subst_nmul_nmul_eq_nmul_mul {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) S}
    (hG : _root_.GlobalTheory.Katz.IsLaw μ) (k m : ℕ) (i : Fin d) :
    subst (_root_.GlobalTheory.QLog.nmul μ m) (_root_.GlobalTheory.QLog.nmul μ k i) =
      _root_.GlobalTheory.QLog.nmul μ (k * m) i := by
  have hμ := hG.const
  have hN := constantCoeff_nmul_eq_zero' μ hμ
  have hm : HasSubst (_root_.GlobalTheory.QLog.nmul μ m) := hasSubst_of_constantCoeff_zero (hN m)
  induction k generalizing i with
  | zero =>
    simp only [Nat.zero_mul, nmul_zero]
    exact subst_zero_divisor hm
  | succ k ih =>
    rw [nmul_succ_eq_op_X, subst_katz_op_eq_op_subst μ (hN k) (fun j => constantCoeff_X j) hm]
    simp_rw [ih, subst_X hm]
    rw [Nat.succ_mul, nmul_add_eq_op hG]

set_option autoImplicit false in
open MvPowerSeries TensorProduct in
variable {R Q : Type} [CommRing R] [CommRing Q] [Algebra R Q] {d : ℕ} in
variable {S : Type} [CommRing S] in

theorem _root_.GlobalTheory.DefectComp.main : ∀ (R Q : Type) [CommRing R] [CommRing Q] [Algebra R Q] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R), _root_.GlobalTheory.Katz.IsLaw μ → Function.Injective (algebraMap R Q) → ∀ (f : MvPowerSeries (Fin d) Q), constantCoeff f = 0 → ∀ (k m : ℕ) (s t u : MvPowerSeries (Fin d) R), map (algebraMap R Q) s = _root_.GlobalTheory.QLog.defect μ k f → map (algebraMap R Q) t = _root_.GlobalTheory.QLog.defect μ m f → map (algebraMap R Q) u = _root_.GlobalTheory.QLog.defect μ (k * m) f → u = subst (_root_.GlobalTheory.QLog.nmul μ m) s + (k : R) • t := by
  intro R Q _ _ _ d μ hG hinj f _ k m s t u hs ht hu
  have hμ := hG.const
  have hm : HasSubst (_root_.GlobalTheory.QLog.nmul μ m) :=
    hasSubst_of_constantCoeff_zero (constantCoeff_nmul_eq_zero' μ hμ m)
  have hmQ := _root_.GlobalTheory.QLog.hasSubst_up_nmul (Q := Q) hμ m
  have hkQ := _root_.GlobalTheory.QLog.hasSubst_up_nmul (Q := Q) hμ k
  apply mvPowerSeries_map_injective hinj
  rw [map_add, map_subst hm, hs, hu, Nat.cast_smul_eq_nsmul, map_nsmul, ht]
  change _ = subst (_root_.GlobalTheory.QLog.up Q (_root_.GlobalTheory.QLog.nmul μ m))
    (_root_.GlobalTheory.QLog.defect μ k f) + _
  simp only [_root_.GlobalTheory.QLog.defect]
  rw [subst_sub hmQ, subst_smul hmQ, subst_comp_subst_apply hkQ hmQ]
  have hcomp : (fun i => subst (_root_.GlobalTheory.QLog.up Q (_root_.GlobalTheory.QLog.nmul μ m))
      (_root_.GlobalTheory.QLog.up Q (_root_.GlobalTheory.QLog.nmul μ k) i)) =
      _root_.GlobalTheory.QLog.up Q (_root_.GlobalTheory.QLog.nmul μ (k * m)) := by
    funext i
    change subst (fun j => map (algebraMap R Q) (_root_.GlobalTheory.QLog.nmul μ m j))
      (map (algebraMap R Q) (_root_.GlobalTheory.QLog.nmul μ k i)) =
        map (algebraMap R Q) (_root_.GlobalTheory.QLog.nmul μ (k * m) i)
    rw [← map_subst hm, subst_nmul_nmul_eq_nmul_mul hG]
  rw [hcomp, ← Nat.cast_smul_eq_nsmul Q, Nat.cast_mul, mul_smul, smul_sub]
  abel

end GlobalTheory.DefectComp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CutoffHoloSmoothDbarFormulaStatement
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cutoff_holo_smooth_dbar_formula : ∀ (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M], ∀ (X : EtaleStein n M) (ψ : M → ℝ) (G : M → ℂ) (Ω : Set M) (δ b : ℝ) (θ : ℝ → ℝ), SmoothR n X.z ψ → ContDiff ℝ ∞ θ → (∀ t, b ≤ t → θ t = 0) → IsOpen Ω → (∀ e : OpenPartialHomeomorph M (V n), IsChart n X.z e → DifferentiableOn ℂ (G ∘ e.symm) (e.target ∩ e.symm ⁻¹' Ω)) → (∀ x, δ * ψ x ≤ b → x ∈ Ω) → Smooth n X.z (fun x => (θ (δ * ψ x) : ℂ) * G x) ∧ ∀ (x : M) (ξ : Fin n → ℂ), dbarDot n X.z (fun y => (θ (δ * ψ y) : ℂ) * G y) x ξ = ((deriv θ (δ * ψ x) * δ : ℝ) : ℂ) * G x * dbarDot n X.z (fun y => (ψ y : ℂ)) x ξ := by
  first | exact @GlobalTheory.L2Cutoff.cutoff_smooth_dbar | exact GlobalTheory.L2Cutoff.cutoff_smooth_dbar | (intros; apply GlobalTheory.L2Cutoff.cutoff_smooth_dbar <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarEnergyCutoffMulSectionLeStatement
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.n1_cutoff_mul_section_le_lintegral : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (C : Cover A) (χ : Y → ℝ), A.SmoothFn χ → ∃ K : ℝ, 0 ≤ K ∧ ∀ (la : La) (W Z : Set Y) (h : ι → Y → ℂ), IsOpen W → tsupport χ ⊆ W → A.IsSecOn (A.kap + la) W h → MeasurableSet Z → (∀ y, y ∉ Z → ∀ᶠ x in 𝓝 y, χ x = χ y) → n1 C la (fun i y => (χ y : ℂ) * h i y) ≤ ENNReal.ofReal K * ∫⁻ y in Z ∩ W, ENNReal.ofReal (A.nsq (A.kap + la) h y) ∂A.mu := by
  first | exact @GlobalTheory.CutEnergy.dbarEnergy_cutoff_mul_section_le | exact GlobalTheory.CutEnergy.dbarEnergy_cutoff_mul_section_le | (intros; apply GlobalTheory.CutEnergy.dbarEnergy_cutoff_mul_section_le <;> assumption)
end

