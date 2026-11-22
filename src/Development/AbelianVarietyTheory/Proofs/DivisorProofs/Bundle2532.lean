import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0018
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftSystemRealStructure
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsTjCorrDiagModel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicHomDetermined
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsAffineLieBasisBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2430
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2364
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2432
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2362
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicValIntDiscrDivLeDeltaVp
section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal UpperHalfPlane ReciprocityTheory.ChartRestriction.L1
open scoped UpperHalfPlane

namespace GlobalTheory.DiscrTower

theorem finrank_mul_padicValInt_discr_le (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (l : ℕ) (hl : l.Prime) :
    Module.finrank K L * padicValInt l (discr K) ≤ padicValInt l (discr L) := by
  haveI : Fact l.Prime := ⟨hl⟩
  have h := natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow K (𝓞 K) L (𝓞 L)
  have hL : (discr L).natAbs ≠ 0 := Int.natAbs_ne_zero.2 (discr_ne_zero L)
  rw [h] at hL
  unfold padicValInt
  rw [h, padicValNat.mul (left_ne_zero_of_mul hL) (right_ne_zero_of_mul hL), padicValNat.pow]
  omega

theorem padicValInt_discr_div_le_delta_vp :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (l : ℕ), l.Prime →
      (padicValInt l (discr (maximalRealSubfield E)) : ℝ) / Module.finrank ℚ (maximalRealSubfield E) ≤
        GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.delta_vp E l := by
  intro E _ _ _ l hl
  have h := finrank_mul_padicValInt_discr_le (maximalRealSubfield E) E l hl
  have h2 := Module.finrank_mul_finrank ℚ (maximalRealSubfield E) E
  have hF : (0 : ℝ) < Module.finrank ℚ (maximalRealSubfield E) := by exact_mod_cast Module.finrank_pos
  have hE : (0 : ℝ) < Module.finrank ℚ E := by exact_mod_cast Module.finrank_pos
  unfold GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.delta_vp
  rw [div_le_div_iff₀ hF hE, ← h2]
  have h' : (Module.finrank (maximalRealSubfield E) E : ℝ) * padicValInt l (discr (maximalRealSubfield E)) ≤
      padicValInt l (discr E) := by exact_mod_cast h
  push_cast
  nlinarith

end GlobalTheory.DiscrTower
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PdPolynomialCompatibleFormsGeneratedInduction
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

namespace GlobalTheory.PDForm

theorem rel_mul_mem_right {R B : Type} [CommRing R] [CommRing B] [Algebra R B] {J : Ideal B}
    (δ : DividedPowers J) {x : DR R B} (hx : x ∈ rel R δ) (y : DR R B) : x * y ∈ rel R δ := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨n, a, ha, rfl⟩ := hx
    rw [ι_mul]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨n, a, ha, rfl⟩)
  | zero => simp
  | add x z _ _ hx hz => rw [add_mul]; exact add_mem hx hz
  | smul a x _ ih => rw [smul_eq_mul, mul_assoc]; exact Ideal.mul_mem_left _ _ ih

section Poly

variable {R B : Type} [CommRing R] [CommRing B] [Algebra R B] {J : Ideal B}
  {Q : PDPoly B} [Algebra R Q.P] [IsScalarTower R B Q.P] (η : DividedPowers (Q.ext J))
  (h : SemiHom (RingHom.id R) (algebraMap B Q.P))

def pdGen : Set (DR R Q.P) :=
  {x | ∃ n α, x = Q.e n • h.mDR α} ∪ {x | ∃ n α, x = Q.e n • (ι1 (D R Q.P (Q.e 1)) * h.mDR α)} ∪
    (rel R η : Set (DR R Q.P))

theorem pdGen_mem_one (n : ℕ) (α : DR R B) : Q.e n • h.mDR α ∈ pdGen η h :=
  Set.mem_union_left _ (Set.mem_union_left _ ⟨n, α, rfl⟩)

theorem pdGen_mem_two (n : ℕ) (α : DR R B) : Q.e n • (ι1 (D R Q.P (Q.e 1)) * h.mDR α) ∈ pdGen η h :=
  Set.mem_union_left _ (Set.mem_union_right _ ⟨n, α, rfl⟩)

theorem pdGen_mem_rel {x : DR R Q.P} (hx : x ∈ rel R η) : x ∈ pdGen η h :=
  Set.mem_union_right _ hx

theorem smul_gen_mem (b : Q.P) : ∀ α : DR R B,
    b • h.mDR α ∈ AddSubgroup.closure (pdGen η h) ∧
      b • (ι1 (D R Q.P (Q.e 1)) * h.mDR α) ∈ AddSubgroup.closure (pdGen η h) := by
  have hb : b ∈ Submodule.span B (Set.range Q.e) := by rw [Q.e.span_eq]; trivial
  induction hb using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨n, rfl⟩ := hx
    exact fun α ↦ ⟨AddSubgroup.subset_closure (pdGen_mem_one η h n α),
      AddSubgroup.subset_closure (pdGen_mem_two η h n α)⟩
  | zero => intro α; simp only [zero_smul]; exact ⟨zero_mem _, zero_mem _⟩
  | add x y _ _ hx hy =>
    intro α
    rw [add_smul, add_smul]
    exact ⟨add_mem (hx α).1 (hy α).1, add_mem (hx α).2 (hy α).2⟩
  | smul c x _ ih =>
    intro α
    have e1 : (c • x) • h.mDR α = x • h.mDR (c • α) := by
      rw [h.mDR_smul, Algebra.smul_def c x, mul_comm, mul_smul]
    have e2 : (c • x) • (ι1 (D R Q.P (Q.e 1)) * h.mDR α) = x • (ι1 (D R Q.P (Q.e 1)) * h.mDR (c • α)) := by
      rw [h.mDR_smul, mul_smul_comm, Algebra.smul_def c x, mul_comm, mul_smul]
    rw [e1, e2]
    exact ih (c • α)

theorem smul_mem_closure (b : Q.P) {x : DR R Q.P} (hx : x ∈ AddSubgroup.closure (pdGen η h)) :
    b • x ∈ AddSubgroup.closure (pdGen η h) := by
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    rcases hx with (⟨n, α, rfl⟩ | ⟨n, α, rfl⟩) | hx
    · rw [smul_smul]; exact (smul_gen_mem η h _ α).1
    · rw [smul_smul]; exact (smul_gen_mem η h _ α).2
    · refine AddSubgroup.subset_closure (pdGen_mem_rel η h ?_)
      rw [Algebra.smul_def]; exact Ideal.mul_mem_left _ _ hx
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

theorem D_mem_closure {δ : DividedPowers J} (hs : Q.IsStd δ η) (b : Q.P) :
    ι1 (D R Q.P b) ∈ AddSubgroup.closure (pdGen η h) := by
  have hb : b ∈ Submodule.span B (Set.range Q.e) := by rw [Q.e.span_eq]; trivial
  induction hb using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨n, rfl⟩ := hx
    cases n with
    | zero => rw [Q.e_zero, Derivation.map_one_eq_zero, map_zero]; exact zero_mem _
    | succ n =>
      have hr : ι1 (D R Q.P (η.dpow (n + 1) (Q.e 1)) - η.dpow n (Q.e 1) • D R Q.P (Q.e 1)) ∈ rel R η :=
        Ideal.subset_span ⟨n, Q.e 1, Q.e_one_mem_ext J, rfl⟩
      rw [hs.var, hs.var] at hr
      have e : ι1 (D R Q.P (Q.e (n + 1))) = ι1 (D R Q.P (Q.e (n + 1)) - Q.e n • D R Q.P (Q.e 1)) +
          Q.e n • (ι1 (D R Q.P (Q.e 1)) * h.mDR 1) := by
        rw [map_one h.mDR, mul_one, map_sub, map_smul, sub_add_cancel]
      rw [e]
      exact add_mem (AddSubgroup.subset_closure (pdGen_mem_rel η h hr))
        (AddSubgroup.subset_closure (pdGen_mem_two η h n 1))
  | zero => rw [map_zero, map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add, map_add]; exact add_mem hx hy
  | smul c x _ ih =>
    rw [Algebra.smul_def, Derivation.leibniz, map_add, map_smul, map_smul]
    refine add_mem (smul_mem_closure η h _ ih) ?_
    have e : ι1 (D R Q.P (algebraMap B Q.P c)) = h.mDR (ι1 (D R B c)) := by rw [h.mDR_ι, h.m1_D]
    rw [e]; exact (smul_gen_mem η h x _).1

omit [IsScalarTower R B Q.P] in

theorem mDR_mul_dtau (α β : DR R B) :
    h.mDR α * (ι1 (D R Q.P (Q.e 1)) * h.mDR β) = ι1 (D R Q.P (Q.e 1)) * h.mDR (sgn α * β) := by
  rw [← mul_assoc, map_mul, h.mDR_sgn, ← mul_assoc, ι_mul (D R Q.P (Q.e 1)) (sgn (h.mDR α)), sgn_sgn]

theorem gen_mul_gen {x y : DR R Q.P} (hx : x ∈ pdGen η h) (hy : y ∈ pdGen η h) :
    x * y ∈ AddSubgroup.closure (pdGen η h) := by
  have base : ∀ α : DR R B, h.mDR α ∈ AddSubgroup.closure (pdGen η h) := fun α ↦ by
    have := (smul_gen_mem η h 1 α).1; rwa [one_smul] at this
  have base2 : ∀ α : DR R B, ι1 (D R Q.P (Q.e 1)) * h.mDR α ∈ AddSubgroup.closure (pdGen η h) := fun α ↦ by
    have := (smul_gen_mem η h 1 α).2; rwa [one_smul] at this
  have relL : ∀ {z : DR R Q.P} (w : DR R Q.P), z ∈ rel R η → w * z ∈ AddSubgroup.closure (pdGen η h) :=
    fun w hz ↦ AddSubgroup.subset_closure (pdGen_mem_rel η h (Ideal.mul_mem_left _ w hz))
  rcases hx with (⟨m, α, rfl⟩ | ⟨m, α, rfl⟩) | hx
  · rcases hy with (⟨n, β, rfl⟩ | ⟨n, β, rfl⟩) | hy
    · rw [smul_mul_assoc, mul_smul_comm, ← map_mul]
      exact smul_mem_closure η h _ (smul_mem_closure η h _ (base _))
    · rw [smul_mul_assoc, mul_smul_comm, mDR_mul_dtau]
      exact smul_mem_closure η h _ (smul_mem_closure η h _ (base2 _))
    · exact relL _ hy
  · rcases hy with (⟨n, β, rfl⟩ | ⟨n, β, rfl⟩) | hy
    · rw [smul_mul_assoc, mul_smul_comm, mul_assoc, ← map_mul]
      exact smul_mem_closure η h _ (smul_mem_closure η h _ (base2 _))
    · rw [smul_mul_assoc, mul_smul_comm, mul_assoc, mDR_mul_dtau, ← mul_assoc, ExteriorAlgebra.ι_sq_zero,
        zero_mul, smul_zero, smul_zero]
      exact zero_mem _
    · exact relL _ hy
  · exact AddSubgroup.subset_closure (pdGen_mem_rel η h (rel_mul_mem_right η hx _))

theorem mul_mem_closure {x y : DR R Q.P} (hx : x ∈ AddSubgroup.closure (pdGen η h))
    (hy : y ∈ AddSubgroup.closure (pdGen η h)) : x * y ∈ AddSubgroup.closure (pdGen η h) := by
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    induction hy using AddSubgroup.closure_induction with
    | mem y hy => exact gen_mul_gen η h hx hy
    | zero => rw [mul_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [mul_add]; exact add_mem hy hz
    | neg y _ hy => rw [mul_neg]; exact neg_mem hy
  | zero => rw [zero_mul]; exact zero_mem _
  | add x z _ _ hx hz => rw [add_mul]; exact add_mem hx hz
  | neg x _ hx => rw [neg_mul]; exact neg_mem hx

end Poly

theorem pdPoly_forms_induction : ∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B] (J : Ideal B)
    (δ : DividedPowers J) (Q : PDPoly B) [Algebra R Q.P] [IsScalarTower R B Q.P] (η : DividedPowers (Q.ext J))
    (v : Derivation R Q.P Q.P) (h : SemiHom (RingHom.id R) (algebraMap B Q.P)), Q.IsStd δ η →
    (∀ b, v (algebraMap B Q.P b) = 0) → (∀ n, v (Q.e (n + 1)) = Q.e n) →
    (∀ n, ∀ a ∈ Q.ext J, v (η.dpow (n + 1) a) = η.dpow n a * v a) → ∀ (p : DR R Q.P → Prop),
    (∀ x ∈ rel R η, p x) → (∀ x y, p x → p y → p (x + y)) → (∀ n α, p (Q.e n • h.mDR α)) →
    (∀ n α, p (Q.e n • (ι1 (D R Q.P (Q.e 1)) * h.mDR α))) → ∀ x, p x := by
  intro R B _ _ _ J δ Q _ _ η _ h hs _ _ _ p hrel hadd h1 h2 x
  have hS : ∀ x, x ∈ AddSubgroup.closure (pdGen η h) := fun x ↦ by
    induction x using indDR with
    | h b =>
      have := (smul_gen_mem η h b 1).1
      rwa [map_one, ← Algebra.algebraMap_eq_smul_one] at this
    | hd b => exact D_mem_closure η h hs b
    | hm x y hx hy => exact mul_mem_closure η h hx hy
    | ha x y hx hy => exact add_mem hx hy
  have key : ∀ x ∈ AddSubgroup.closure (pdGen η h), p x ∧ p (-x) := by
    intro x hx
    induction hx using AddSubgroup.closure_induction with
    | mem x hx =>
      rcases hx with (⟨n, α, rfl⟩ | ⟨n, α, rfl⟩) | hx
      · exact ⟨h1 n α, by rw [← smul_neg, ← map_neg]; exact h1 n (-α)⟩
      · exact ⟨h2 n α, by rw [← smul_neg, ← mul_neg, ← map_neg]; exact h2 n (-α)⟩
      · exact ⟨hrel x hx, hrel _ (neg_mem hx)⟩
    | zero => exact ⟨hrel 0 (zero_mem _), by rw [neg_zero]; exact hrel 0 (zero_mem _)⟩
    | add x y _ _ hx hy => exact ⟨hadd _ _ hx.1 hy.1, by rw [neg_add]; exact hadd _ _ hx.2 hy.2⟩
    | neg x _ hx => exact ⟨hx.2, by rw [neg_neg]; exact hx.1⟩
  exact (key x (hS x)).1

end GlobalTheory.PDForm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PerfectPairingTorsionModule
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.perfect_pairing_torsion_module : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (r : ℤ) (w : Ideal (𝓞 D.F)) (j c : ℕ), w.IsMaximal → uIdeal D r ≤ w → (∃ e : ℕ, c = p ^ e) → ∀ (M : Type) [AddCommGroup M] [Module (𝓞 D.F) M] [Finite M], (∀ x : M, c • x = 0) → ∀ (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (e : M → M → kˣ), (∀ x x' y, e (x + x') y = e x y * e x' y) → (∀ x y y', e x (y + y') = e x y * e x y') → (∀ (a : 𝓞 D.F) x y, e (a • x) y = e x (D.bar a • y)) → (∀ x y, e x y * e y x = 1) → (∀ x, (∀ y, e x y = 1) → x = 0) → Ideal.absNorm w ^ j ≤ Nat.card {x : M // ∀ a ∈ w, a • x = 0} → ∃ H : Submodule (𝓞 D.F) M, (∀ x ∈ H, ∀ y ∈ H, e x y = 1) ∧ (∀ x, (∀ y ∈ H, e x y = 1) → x ∈ H) ∧ (∀ x ∈ H, (∃ i : ℕ, ∀ a ∈ uIdeal D r ^ i, a • x = 0) → ∀ a ∈ w, a • x = 0) ∧ Nat.card {x : M // x ∈ H ∧ ∀ a ∈ w, a • x = 0} = Ideal.absNorm w ^ j := by
  first | (exact @GlobalTheory.UPel.HT.ES.exists_maximal_isotropic_of_type) | (exact GlobalTheory.UPel.HT.ES.exists_maximal_isotropic_of_type) | (intros; apply GlobalTheory.UPel.HT.ES.exists_maximal_isotropic_of_type  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodTransportGaloisConjugate
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false

noncomputable section
namespace GlobalTheory.DiagConj
open GlobalTheory.HolHom

theorem fderiv_diag {n : ℕ} {X : Scheme.{0}} {c : (Fin n → ℂ) → (Sp ℂ ⟶ X)} (hc : HolAt c 0)
    (m w : Fin n → ℂ) (U : X.Opens) (hU : ⊤ ≤ c 0 ⁻¹ᵁ U) (f : Γ(X, U)) :
    fderiv ℂ (fun t => valAt' (c (fun j => m j * t j)) U f) 0 w =
      fderiv ℂ (fun t => valAt' (c t) U f) 0 (fun j => m j * w j) := by
  have h0 : (fun j => m j * (0 : Fin n → ℂ) j) = 0 := by funext j; simp
  have hL : HasFDerivAt (fun z : Fin n → ℂ => (fun j => m j * z j)) (ContinuousLinearMap.mul ℂ (Fin n → ℂ) m) 0 :=
    (ContinuousLinearMap.mul ℂ (Fin n → ℂ) m).hasFDerivAt
  have hg := ((hc U hU).2 f).hasFDerivAt
  rw [← h0] at hg
  have hcomp := HasFDerivAt.comp (0 : Fin n → ℂ) hg hL
  have e1 := congrArg (fun L => L w) hcomp.fderiv
  simp only [Function.comp_def, ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.mul_apply',
    h0] at e1
  exact e1

theorem isDerivAt_diag_iff {n : ℕ} {X : Scheme.{0}} {c : (Fin n → ℂ) → (Sp ℂ ⟶ X)} (hc : HolAt c 0)
    (m w : Fin n → ℂ) (v : Sp (DualNumber ℂ) ⟶ X) :
    IsDerivAt (fun z => c (fun j => m j * z j)) 0 w v ↔ IsDerivAt c 0 (fun j => m j * w j) v := by
  have h0 : (fun j => m j * (0 : Fin n → ℂ) j) = 0 := by funext j; simp
  unfold IsDerivAt
  simp only [h0]
  refine and_congr_right fun _ => forall_congr' fun U => forall_congr' fun hU => forall_congr' fun f => ?_
  rw [fderiv_diag hc m w U hU f]

theorem spMap_dual_cancel (g : ℂ ≃+* ℂ) {X : Scheme.{0}} (x y : Sp (DualNumber ℂ) ⟶ X)
    (h : spMap (Chart.dualMapR (g : ℂ →+* ℂ)) ≫ x = spMap (Chart.dualMapR (g : ℂ →+* ℂ)) ≫ y) : x = y := by
  have e0 : (Chart.dualMapR (g.symm : ℂ →+* ℂ)).comp (Chart.dualMapR (g : ℂ →+* ℂ)) = RingHom.id _ := by
    apply RingHom.ext; intro a
    apply TrivSqZeroExt.ext <;> simp [Chart.dualMapR]
  have e : spMap (Chart.dualMapR (g.symm : ℂ →+* ℂ)) ≫ spMap (Chart.dualMapR (g : ℂ →+* ℂ)) = 𝟙 _ := by
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1
    ext1
    exact e0
  have := congrArg (spMap (Chart.dualMapR (g.symm : ℂ →+* ℂ)) ≫ ·) h
  simpa [← Category.assoc, e] using this

theorem diag_endo_iff_conj_diag : ∀ (A A' : Over (Sp ℂ)) [GrpObj A] [GrpObj A'] (L : LB A.left) (L' : LB A'.left) (n : ℕ)
    (u : HolUnif A L n) (u' : HolUnif A' L' n) (g : ℂ ≃+* ℂ) (p : A'.left ⟶ A.left),
    IsGrpPullback A' A (spMap (g : ℂ →+* ℂ)) p → ∀ (Ω₀ Ω₁ : ℂ), Ω₀ ≠ 0 → Ω₁ ≠ 0 →
    (∀ (w : Fin n → ℂ) (v : epsR ℂ ⟶ A) (v' : epsR ℂ ⟶ A'), v'.left ≫ p = spMap (Chart.dualMapR (g : ℂ →+* ℂ)) ≫ v.left →
      u.IsDiff w v → u'.IsDiff (fun j ↦ g (Ω₀ * w j) / Ω₁) v') →
    ∀ (m : Fin n → ℂ) (α : A ⟶ A) [IsMonHom α] (α' : A' ⟶ A') [IsMonHom α'], α'.left ≫ p = p ≫ α.left →
      ((∀ w, u.ex (fun j ↦ m j * w j) = u.ex w ≫ α) ↔ (∀ w, u'.ex (fun j ↦ g (m j) * w j) = u'.ex w ≫ α')) := by
  intro A A' _ _ L L' n u u' g p hp Ω₀ Ω₁ hΩ₀ hΩ₁ htr m α _ α' _ hαp
  have holA : IsHolTo Set.univ (fun z => (u.ex z).left) := fun U f => by
    simpa only [Set.mem_univ, true_and, Set.sep_univ] using u.hol U f
  have holA' : IsHolTo Set.univ (fun z => (u'.ex z).left) := fun U f => by
    simpa only [Set.mem_univ, true_and, Set.sep_univ] using u'.hol U f
  have hA : ∀ z, HolAt (fun z => (u.ex z).left) z := fun z => holAt_of_isHolTo holA (Set.mem_univ z)
  have hA' : ∀ z, HolAt (fun z => (u'.ex z).left) z := fun z => holAt_of_isHolTo holA' (Set.mem_univ z)
  have one0 : u.ex 0 = 1 := map_zero_eq_one u.ex_add
  have one0' : u'.ex 0 = 1 := map_zero_eq_one u'.ex_add
  have eta : (u.ex 0).left = η[A].left := by
    rw [one0, Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
  have eta' : (u'.ex 0).left = η[A'].left := by
    rw [one0', Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]

  have tan : ∀ w, ∃ v : epsR ℂ ⟶ A, IsDerivAt (fun z => (u.ex z).left) 0 w v.left := by
    intro w
    obtain ⟨v, hv⟩ := (hA 0).exists_isDerivAt w
    have hv2 : v ≫ A.hom = (epsR ℂ).hom := by
      have h1 := hv.comp A.hom
      have h2 : (fun t => (u.ex t).left ≫ A.hom) = fun _ => 𝟙 (Sp ℂ) := funext fun t => Over.w (u.ex t)
      rw [h2] at h1
      rw [h1.unique (isDerivAt_const (𝟙 (Sp ℂ)) 0 w)]
      simp [constVec]
    exact ⟨Over.homMk v hv2, hv⟩

  have ringSq : spMap (Chart.dualMapR (g : ℂ →+* ℂ)) ≫ spMap (algebraMap ℂ (DualNumber ℂ)) =
      spMap (algebraMap ℂ (DualNumber ℂ)) ≫ spMap (g : ℂ →+* ℂ) := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext1
    apply RingHom.ext; intro a
    apply TrivSqZeroExt.ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
  have fstSq : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ spMap (Chart.dualMapR (g : ℂ →+* ℂ)) =
      spMap (g : ℂ →+* ℂ) ≫ spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext1
    apply RingHom.ext; intro a
    simp [Chart.dualMapR]
  have fstAlg : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ spMap (algebraMap ℂ (DualNumber ℂ)) = 𝟙 _ := by
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1
    all_goals (ext1; apply RingHom.ext; intro a; simp)
  have conj : ∀ v : epsR ℂ ⟶ A, ∃ v' : epsR ℂ ⟶ A',
      v'.left ≫ p = spMap (Chart.dualMapR (g : ℂ →+* ℂ)) ≫ v.left := by
    intro v
    have w : (spMap (Chart.dualMapR (g : ℂ →+* ℂ)) ≫ v.left) ≫ A.hom = (epsR ℂ).hom ≫ spMap (g : ℂ →+* ℂ) := by
      rw [Category.assoc, Over.w v]
      exact ringSq
    exact ⟨Over.homMk (hp.1.lift _ _ w) (hp.1.lift_snd _ _ _), hp.1.lift_fst _ _ _⟩
  have conj0 : ∀ (v : epsR ℂ ⟶ A) (v' : epsR ℂ ⟶ A'),
      v'.left ≫ p = spMap (Chart.dualMapR (g : ℂ →+* ℂ)) ≫ v.left →
      spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (u.ex 0).left →
      spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v'.left = (u'.ex 0).left := by
    intro v v' hv' h0
    apply hp.1.hom_ext
    · rw [Category.assoc, hv', ← Category.assoc, fstSq, Category.assoc, h0, eta, eta',
        GlobalTheory.LieChart.unit_comp_of_isGrpPullback hp]
    · rw [Category.assoc, Over.w v', Over.w (u'.ex 0)]
      exact fstAlg

  have trD : ∀ (w : Fin n → ℂ) (v : epsR ℂ ⟶ A) (v' : epsR ℂ ⟶ A'),
      v'.left ≫ p = spMap (Chart.dualMapR (g : ℂ →+* ℂ)) ≫ v.left →
      IsDerivAt (fun z => (u.ex z).left) 0 w v.left →
      IsDerivAt (fun z => (u'.ex z).left) 0 (fun j => g (Ω₀ * w j) / Ω₁) v'.left := by
    intro w v v' hv' hv
    have h0' := conj0 v v' hv' hv.1
    have hd : u.IsDiff w v := ((isDerivAt0_iff _ _ _).2 hv).2
    exact (isDerivAt0_iff _ _ _).1 ⟨h0', htr w v v' hv' hd⟩
  have Tsurj : ∀ w' : Fin n → ℂ, (fun j => g (Ω₀ * (fun j => Ω₀⁻¹ * g.symm (Ω₁ * w' j)) j) / Ω₁) = w' := by
    intro w'; funext j
    simp only
    rw [← _root_.mul_assoc, mul_inv_cancel₀ hΩ₀, _root_.one_mul, RingEquiv.apply_symm_apply, mul_div_cancel_left₀ _ hΩ₁]
  have Tmul : ∀ w : Fin n → ℂ, (fun j => g (Ω₀ * (fun j => m j * w j) j) / Ω₁) =
      fun j => g (m j) * (fun j => g (Ω₀ * w j) / Ω₁) j := by
    intro w; funext j
    simp only
    rw [mul_left_comm, map_mul, mul_div_assoc]
  have hz : (fun j => m j * (0 : Fin n → ℂ) j) = 0 := by funext j; simp
  have hz' : (fun j => g (m j) * (0 : Fin n → ℂ) j) = 0 := by funext j; simp
  constructor
  · intro hα
    have he : ∀ z w : Fin n → ℂ, u'.ex (fun j => g (m j) * (z + w) j) =
        u'.ex (fun j => g (m j) * z j) * u'.ex (fun j => g (m j) * w j) := by
      intro z w
      rw [← u'.ex_add]
      congr 1
      funext j
      simp [mul_add]
    have he' : ∀ z w : Fin n → ℂ, u'.ex (z + w) ≫ α' = (u'.ex z ≫ α') * (u'.ex w ≫ α') := by
      intro z w
      rw [u'.ex_add, MonObj.mul_comp]
    have hol : IsHolTo Set.univ (fun (z : Fin n → ℂ) => (u'.ex (fun j => g (m j) * z j)).left) :=
      isHolTo_of_holAt isOpen_univ fun z _ =>
        (hA' _).precomp (k := fun (t : Fin n → ℂ) j => g (m j) * t j)
          (ContinuousLinearMap.mul ℂ (Fin n → ℂ) (fun j => g (m j))).differentiableAt
    have hol' : IsHolTo Set.univ (fun z => (u'.ex z ≫ α').left) := by
      have e : (fun z => (u'.ex z ≫ α').left) = (fun z => (u'.ex z).left ≫ α'.left) :=
        funext fun z => by rw [Over.comp_left]
      rw [e]
      exact isHolTo_of_holAt isOpen_univ fun z _ => (hA' z).comp α'.left
    have hd : ∀ U : A'.left.Opens, ⊤ ≤ (u'.ex (fun j => g (m j) * (0 : Fin n → ℂ) j)).left ⁻¹ᵁ U →
        ∀ f : Γ(A'.left, U), fderiv ℂ (fun (z : Fin n → ℂ) => valAt' (u'.ex (fun j => g (m j) * z j)).left U f) 0 =
          fderiv ℂ (fun z => valAt' (u'.ex z ≫ α').left U f) 0 := by
      intro U hU f
      simp only [Over.comp_left]
      refine ContinuousLinearMap.ext fun w' => ?_
      obtain ⟨v, hv⟩ := tan (fun j => Ω₀⁻¹ * g.symm (Ω₁ * w' j))
      obtain ⟨v', hv'⟩ := conj v
      have D1 := trD _ v v' hv' hv
      rw [Tsurj] at D1
      have hcα : (fun t => (u.ex t).left ≫ α.left) = fun t => (u.ex (fun j => m j * t j)).left :=
        funext fun t => by rw [hα t]; rfl
      have Dα := hv.comp α.left
      rw [hcα] at Dα
      have Dα' := (isDerivAt_diag_iff (hA 0) m _ _).1 Dα
      have hv'α : (v'.left ≫ α'.left) ≫ p = spMap (Chart.dualMapR (g : ℂ →+* ℂ)) ≫ (v.left ≫ α.left) := by
        rw [Category.assoc, hαp, ← Category.assoc, hv', Category.assoc]
      have D2 := trD _ (v ≫ α) (v' ≫ α') hv'α Dα'
      rw [Tmul, Tsurj] at D2
      have D2' := (isDerivAt_diag_iff (hA' 0) (fun j => g (m j)) w' _).2 D2
      have D3 := D1.comp α'.left
      have hU' : ⊤ ≤ (u'.ex 0).left ⁻¹ᵁ U := by rw [← hz']; exact hU
      have hU'' : ⊤ ≤ ((u'.ex 0).left ≫ α'.left) ⁻¹ᵁ U := by
        rw [← Over.comp_left, one0', MonObj.one_comp, ← one0']; exact hU'
      have e1 := D2'.2 U hU f
      have e2 := D3.2 U hU'' f
      exact e1.symm.trans e2
    have key : (fun (w : Fin n → ℂ) => u'.ex (fun j => g (m j) * w j)) = (fun w => u'.ex w ≫ α') :=
      eq_of_fderiv_eq (y := 𝟙 (Sp ℂ)) he he' hol hol' hd
    exact fun w => congrFun key w
  · intro hα'
    have he : ∀ z w : Fin n → ℂ, u.ex (fun j => m j * (z + w) j) =
        u.ex (fun j => m j * z j) * u.ex (fun j => m j * w j) := by
      intro z w
      rw [← u.ex_add]
      congr 1
      funext j
      simp [mul_add]
    have he' : ∀ z w : Fin n → ℂ, u.ex (z + w) ≫ α = (u.ex z ≫ α) * (u.ex w ≫ α) := by
      intro z w
      rw [u.ex_add, MonObj.mul_comp]
    have hol : IsHolTo Set.univ (fun (z : Fin n → ℂ) => (u.ex (fun j => m j * z j)).left) :=
      isHolTo_of_holAt isOpen_univ fun z _ =>
        (hA _).precomp (k := fun (t : Fin n → ℂ) j => m j * t j) (ContinuousLinearMap.mul ℂ (Fin n → ℂ) m).differentiableAt
    have hol' : IsHolTo Set.univ (fun z => (u.ex z ≫ α).left) := by
      have e : (fun z => (u.ex z ≫ α).left) = (fun z => (u.ex z).left ≫ α.left) :=
        funext fun z => by rw [Over.comp_left]
      rw [e]
      exact isHolTo_of_holAt isOpen_univ fun z _ => (hA z).comp α.left
    have hd : ∀ U : A.left.Opens, ⊤ ≤ (u.ex (fun j => m j * (0 : Fin n → ℂ) j)).left ⁻¹ᵁ U →
        ∀ f : Γ(A.left, U), fderiv ℂ (fun (z : Fin n → ℂ) => valAt' (u.ex (fun j => m j * z j)).left U f) 0 =
          fderiv ℂ (fun z => valAt' (u.ex z ≫ α).left U f) 0 := by
      intro U hU f
      simp only [Over.comp_left]
      refine ContinuousLinearMap.ext fun w => ?_
      obtain ⟨v, hv⟩ := tan w
      obtain ⟨v', hv'⟩ := conj v
      obtain ⟨v₂, hv₂⟩ := tan (fun j => m j * w j)
      obtain ⟨v₂', hv₂'⟩ := conj v₂
      have D1 := trD w v v' hv' hv
      have hcα' : (fun t => (u'.ex t).left ≫ α'.left) = fun t => (u'.ex (fun j => g (m j) * t j)).left :=
        funext fun t => by rw [hα' t]; rfl
      have D1α := D1.comp α'.left
      rw [hcα'] at D1α
      have D1α' := (isDerivAt_diag_iff (hA' 0) _ _ _).1 D1α
      have D2 := trD _ v₂ v₂' hv₂' hv₂
      rw [Tmul] at D2
      have huq := D2.unique D1α'
      have hv₂α : v₂.left = v.left ≫ α.left := by
        apply spMap_dual_cancel g
        rw [← hv₂', huq, Category.assoc, hαp, ← Category.assoc, hv', Category.assoc]
      have E1 := (isDerivAt_diag_iff (hA 0) m w _).2 hv₂
      have E2 := hv.comp α.left
      have hU' : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ U := by rw [← hz]; exact hU
      have hU'' : ⊤ ≤ ((u.ex 0).left ≫ α.left) ⁻¹ᵁ U := by
        rw [← Over.comp_left, one0, MonObj.one_comp, ← one0]; exact hU'
      have e1 := E1.2 U hU f
      have e2 := E2.2 U hU'' f
      rw [hv₂α] at e1
      exact e1.symm.trans e2
    have key : (fun (w : Fin n → ℂ) => u.ex (fun j => m j * w j)) = (fun w => u.ex w ≫ α) :=
      eq_of_fderiv_eq (y := 𝟙 (Sp ℂ)) he he' hol hol' hd
    exact fun w => congrFun key w

end GlobalTheory.DiagConj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PinchedChartOffClosedPartFromBaseStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pinched_chart_off_closed_part_from_base : ∀ (R : Type) [CommRing R] (R' : Type) [CommRing R'] [Algebra R R'], Function.Injective (algebraMap R R') → ∀ c : Ideal R, (∀ x ∈ c, ∀ r : R', ∃ y ∈ c, algebraMap R R' y = algebraMap R R' x * r) → ∀ (g : ℕ) (B' C Y : Scheme.{0}) (b' : B' ⟶ Sp R') (e : C ⟶ Sp (R ⧸ c)) (i : Y ⟶ B') (q : Y ⟶ C), SmoothOfRelativeDimension g b' → ∀ x : B', (b' ≫ spMap (algebraMap R R')) x ∉ Set.range (spMap (Ideal.Quotient.mk c)) → GlobalTheory.Pinch.Pinched g (spMap (algebraMap R R')) (spMap (Ideal.Quotient.mk c)) b' e i q x := by
  first | exact @GlobalTheory.Pinch.pinched_off | exact GlobalTheory.Pinch.pinched_off | (intros; apply GlobalTheory.Pinch.pinched_off <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowEqOneOfGeometricPointsTorsionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pow_eq_one_of_geometric_points_torsion : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (n : ℕ), IsUnit (n : Γ(S, ⊤)) → ∀ (T : Over S) (x : T ⟶ A), x ^ n = 1 → ∀ d : ℕ, (∀ (k : Type) [Field k] [IsAlgClosed k] (ξ : Sp k ⟶ T.left), ((Over.homMk ξ rfl : Over.mk (ξ ≫ T.hom) ⟶ T) ≫ x) ^ d = 1) → x ^ d = 1 := by
  first | (exact @GlobalTheory.TorsGeomPow.pow_eq_one_of_geometric_points) | (exact GlobalTheory.TorsGeomPow.pow_eq_one_of_geometric_points) | (intros; apply GlobalTheory.TorsGeomPow.pow_eq_one_of_geometric_points  <;> assumption)
end

