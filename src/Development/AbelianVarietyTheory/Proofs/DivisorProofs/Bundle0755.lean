import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0012
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCuspidalIffCompositions
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0705
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0734
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0741
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0743
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0736
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0747
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0732
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0720
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0731
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0737
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveCrystalHodgeLiftClasses
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.ThetaValues.MemAnalyticAtZeroOfEventuallyDifferentiableAt
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0005
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0729
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0711
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStableCharacterFlagOfCharpolyFactor
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticChartsRealizationCompPointEq
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0022
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0656
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerFiltration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0738
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTaylorExpansionOrderOne
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0012

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNeZeroIntertwiningOfCommutingIsotypicFacto
section
open Formalism.L2.DIV GlobalTheory.FinGL GlobalTheory.Parabolic GlobalTheory.IndefiniteRowSideFullHecke.BlockProductIsomorphism

namespace GlobalTheory.IsotypicFactors

open Representation Module

section One

variable {H W V : Type} [Group H] [AddCommGroup W] [Module ℂ W] [AddCommGroup V] [Module ℂ V]

theorem finiteDimensional_of_isotypic [FiniteDimensional ℂ V] [Nontrivial V]
    (τ : Representation ℂ H V) (ρ : Representation ℂ H W) (hρ : ρ.IsIrreducible)
    (h : IsIsotypicOf τ ρ) : FiniteDimensional ℂ W := by
  have : ∃ g : IntertwiningMap ρ τ, g ≠ 0 := by
    by_contra hc
    push Not at hc
    have : (⨆ f : IntertwiningMap ρ τ, LinearMap.range f.toLinearMap) = ⊥ := by
      refine iSup_eq_bot.2 fun f => ?_
      rw [hc f]
      exact LinearMap.range_eq_bot.2 rfl
    exact bot_ne_top (this.symm.trans h)
  obtain ⟨g, hg⟩ := this
  have hi := (IsIrreducible.injective_or_eq_zero g).resolve_right hg
  exact FiniteDimensional.of_injective g.toLinearMap hi

theorem classSum_scalar [Fintype H] [FiniteDimensional ℂ W] (ρ : Representation ℂ H W)
    (hρ : ρ.IsIrreducible) (h : H) : ∃ s : ℂ, ∀ w, (∑ k, ρ (k * h * k⁻¹)) w = s • w := by
  have hT : ∀ g v, (∑ k, ρ (k * h * k⁻¹)) (ρ g v) = ρ g ((∑ k, ρ (k * h * k⁻¹)) v) := by
    intro g v
    simp only [LinearMap.sum_apply, map_sum]
    rw [← Equiv.sum_comp (Equiv.mulLeft g)]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
    simp [mul_assoc]
  obtain ⟨c, hc⟩ := (IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed (ρ := ρ)).2
    ((∑ k, ρ (k * h * k⁻¹)).intertwiningMap_of_isIntertwiningMap ρ ρ hT)
  refine ⟨c, fun v => ?_⟩
  have := congrArg (fun f : IntertwiningMap ρ ρ => f v) hc
  simpa using this.symm

theorem classSum_of_isotypic [Fintype H] (τ : Representation ℂ H V) (ρ : Representation ℂ H W)
    (hi : IsIsotypicOf τ ρ) (h : H) (s : ℂ) (hs : ∀ w, (∑ k, ρ (k * h * k⁻¹)) w = s • w) :
    (∑ k, τ (k * h * k⁻¹)) = s • (1 : Module.End ℂ V) := by
  have : (⊤ : Submodule ℂ V) ≤ LinearMap.eqLocus (∑ k, τ (k * h * k⁻¹)) (s • (1 : Module.End ℂ V)) := by
    rw [← (show _ = ⊤ from hi)]
    refine iSup_le fun f => ?_
    rintro _ ⟨w, rfl⟩
    rw [LinearMap.mem_eqLocus]
    have e := congrArg f.toLinearMap (hs w)
    simp only [LinearMap.sum_apply, map_sum, map_smul] at e
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, Module.End.one_apply, ← e]
    exact Finset.sum_congr rfl fun k _ => (f.isIntertwining _ _ _ w).symm
  exact LinearMap.ext fun v => this Submodule.mem_top

theorem card_mul_character {M : Type} [Group M] [Fintype H] (τ : Representation ℂ M V) (f : H →* M)
    (h : H) (s : ℂ) (hs : (∑ k, τ (f (k * h * k⁻¹))) = s • (1 : Module.End ℂ V)) (a : M)
    (ha : ∀ k, Commute (f k) a) :
    (Fintype.card H : ℂ) * τ.character (f h * a) = s * τ.character a := by
  have e := congrArg (fun T => LinearMap.trace ℂ V (T * τ a)) hs
  simp only [Finset.sum_mul, map_sum, smul_mul_assoc, one_mul, map_smul, smul_eq_mul] at e
  have e2 : ∀ k, LinearMap.trace ℂ V (τ (f (k * h * k⁻¹)) * τ a) = τ.character (f h * a) := by
    intro k
    rw [← map_mul, ← char_conj τ (f h * a) (f k)]
    have : f (k * h * k⁻¹) * a = f k * (f h * a) * (f k)⁻¹ := by
      rw [map_mul, map_mul, mul_assoc, (ha k⁻¹).eq, map_inv]
      simp only [mul_assoc]
    rw [this]
    rfl
  simp only [e2, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at e
  exact e

end One

theorem exists_ne_zero {G V W : Type} [Group G] [Finite G] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ V] [FiniteDimensional ℂ W] [Nontrivial V]
    [Nontrivial W] (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    (h : ∀ g, (finrank ℂ W : ℂ) * ρ.character g = (finrank ℂ V : ℂ) * σ.character g) :
    ∃ f : IntertwiningMap ρ σ, f ≠ 0 := by
  have := Fintype.ofFinite G
  have : Invertible (Nat.card G : ℂ) :=
    invertibleOfNonzero (by exact_mod_cast Nat.card_pos.ne')
  have h1 := card_inv_mul_sum_char_mul_char_eq_finrank ρ ρ
  have h2 := card_inv_mul_sum_char_mul_char_eq_finrank ρ σ
  have h4 : (finrank ℂ W : ℂ) * finrank ℂ (IntertwiningMap ρ ρ)
      = (finrank ℂ V : ℂ) * finrank ℂ (IntertwiningMap ρ σ) := by
    rw [← h1, ← h2, mul_left_comm, mul_left_comm (finrank ℂ V : ℂ),
      Finset.mul_sum _ _ (finrank ℂ V : ℂ), Finset.mul_sum _ _ (finrank ℂ W : ℂ)]
    congr 1
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [← mul_assoc, ← mul_assoc, h]
  have : Nontrivial (IntertwiningMap ρ ρ) := by
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    exact ⟨⟨IntertwiningMap.id ρ, 0, fun e => hv (congrArg (fun f : IntertwiningMap ρ ρ => f v) e)⟩⟩
  have h5 : finrank ℂ W * finrank ℂ (IntertwiningMap ρ ρ)
      = finrank ℂ V * finrank ℂ (IntertwiningMap ρ σ) := by exact_mod_cast h4
  have h3 : 0 < finrank ℂ (IntertwiningMap ρ σ) := by
    have : 0 < finrank ℂ W * finrank ℂ (IntertwiningMap ρ ρ) :=
      Nat.mul_pos Module.finrank_pos Module.finrank_pos
    rw [h5] at this
    exact Nat.pos_of_mul_pos_left this
  have := Module.nontrivial_of_finrank_pos h3
  exact exists_ne 0

theorem exists_intertwining_ne_zero : ∀ (M : Type) [Group M] [Finite M] (ι : Type) [Finite ι] (H : ι → Type) [∀ c, Group (H c)] [∀ c, Finite (H c)] (f : ∀ c, H c →* M), (⨆ c, (f c).range) = ⊤ → (∀ c c', c ≠ c' → ∀ (x : H c) (y : H c'), Commute (f c x) (f c' y)) → ∀ (W : ι → Type) [∀ c, AddCommGroup (W c)] [∀ c, Module ℂ (W c)] (ρ : ∀ c, Representation ℂ (H c) (W c)), (∀ c, (ρ c).IsIrreducible) → ∀ (V V' : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] [Nontrivial V] [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V'] [Nontrivial V'] (τ : Representation ℂ M V) (τ' : Representation ℂ M V'), (∀ c, IsIsotypicOf (show Representation ℂ (H c) V from τ.comp (f c)) (ρ c)) → (∀ c, IsIsotypicOf (show Representation ℂ (H c) V' from τ'.comp (f c)) (ρ c)) → ∃ T : Representation.IntertwiningMap τ τ', T ≠ 0 := by
  intro M _ _ ι _ H _ _ f htop hcomm W _ _ ρ hρ V V' _ _ _ _ _ _ _ _ τ τ' hτ hτ'
  classical
  have := Fintype.ofFinite ι
  have hcomm' : Pairwise fun i j : ι => ∀ (x : H i) (y : H j), Commute (f i x) (f j y) :=
    fun i j hij => hcomm i j hij
  refine exists_ne_zero τ τ' fun m => ?_
  obtain ⟨h, rfl⟩ : m ∈ (MonoidHom.noncommPiCoprod f hcomm').range := by
    rw [MonoidHom.noncommPiCoprod_range, htop]
    exact Subgroup.mem_top m
  have key : ∀ (S : Finset ι) (comm : (S : Set ι).Pairwise (Function.onFun Commute fun i => f i (h i))),
      (finrank ℂ V' : ℂ) * τ.character (S.noncommProd (fun i => f i (h i)) comm)
        = (finrank ℂ V : ℂ) * τ'.character (S.noncommProd (fun i => f i (h i)) comm) := by
    intro S
    induction S using Finset.induction_on with
    | empty => intro comm; simp [mul_comm]
    | insert c S hc ih =>
      intro comm
      have := Fintype.ofFinite (H c)
      have := finiteDimensional_of_isotypic _ _ (hρ c) (hτ c)
      obtain ⟨s, hs⟩ := classSum_scalar (ρ c) (hρ c) (h c)
      rw [Finset.noncommProd_insert_of_notMem _ _ _ _ hc]
      have ha : ∀ comm k, Commute (f c k) (S.noncommProd (fun i => f i (h i)) comm) := fun comm k =>
        Finset.noncommProd_commute _ _ _ _ fun i hi => hcomm c i (fun e => hc (e ▸ hi)) _ _
      have hcard : (Fintype.card (H c) : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
      refine mul_left_cancel₀ hcard ?_
      rw [mul_left_comm, card_mul_character τ (f c) (h c) s (classSum_of_isotypic _ _ (hτ c) _ _ hs) _ (ha _),
        mul_left_comm (Fintype.card (H c) : ℂ),
        card_mul_character τ' (f c) (h c) s (classSum_of_isotypic _ _ (hτ' c) _ _ hs) _ (ha _),
        mul_left_comm, ih, mul_left_comm]
  exact key Finset.univ fun _ _ _ _ hij => hcomm' hij _ _

end GlobalTheory.IsotypicFactors
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPDivGroupFormalChartOfConnected
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
open TensorProduct

namespace GlobalTheory.ChartEx

theorem isEval_comp {p : ℕ} {O A A' σ : Type} [CommRing O] [CommRing A] [CommRing A'] [Algebra O A]
    [Algebra O A'] {x : σ → A} {E : MvPowerSeries σ O →ₐ[O] A} (φ : A →ₐ[O] A')
    (h : IsEval p x E) : IsEval p (fun i => φ (x i)) (φ.comp E) := by
  refine ⟨fun i => by simp [h.1 i], fun m => ?_⟩
  obtain ⟨N, hN⟩ := h.2 m
  refine ⟨N, fun f hf => ?_⟩
  obtain ⟨a, ha⟩ := hN f hf
  exact ⟨φ a, by rw [AlgHom.comp_apply, ha, map_mul, map_pow, map_natCast]⟩

theorem nil_map {p : ℕ} {A A' : Type} [CommRing A] [CommRing A'] (φ : A →+* A') {a : A}
    (h : ∃ N : ℕ, (p : A) ∣ a ^ N) : ∃ N : ℕ, (p : A') ∣ φ a ^ N := by
  obtain ⟨N, b, hb⟩ := h
  exact ⟨N, φ b, by rw [← map_pow, hb, map_mul, map_natCast]⟩

theorem eq_zero_of_dvd {p : ℕ} {O : Type} [CommRing O] [IsHausdorff (Ideal.span {(p : O)}) O]
    {c : O} (h : ∀ m : ℕ, (p : O) ^ m ∣ c) : c = 0 := by
  refine IsHausdorff.haus' (I := Ideal.span {(p : O)}) c fun m => ?_
  obtain ⟨b, hb⟩ := h m
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  exact ⟨b, hb⟩

theorem eq_zero_of_ker {p : ℕ} {O σ : Type} [CommRing O] [IsHausdorff (Ideal.span {(p : O)}) O]
    {A : ℕ → Type} [∀ n, CommRing (A n)] [∀ n, Algebra O (A n)]
    (E : ∀ n, MvPowerSeries σ O →ₐ[O] A n)
    (hker : ∀ m N : ℕ, ∃ n, ∀ f, E n f = 0 → ∀ α : σ →₀ ℕ, α.degree < N → (p : O) ^ m ∣ coeff α f)
    {f : MvPowerSeries σ O} (hf : ∀ n, E n f = 0) : f = 0 := by
  ext α
  rw [map_zero]
  refine eq_zero_of_dvd (p := p) fun m => ?_
  obtain ⟨n, hn⟩ := hker m (α.degree + 1)
  exact hn f (hf n) α (Nat.lt_succ_self _)

theorem chart_exists : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ G : PDivGroup p O, IsConn G → ∃ d : ℕ, Nonempty (QLog.Chart G d) := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv G hG
  obtain ⟨d, x, ev, hnil, hev, hres, haug, hsurj, hker⟩ := GlobalTheory.T.exists_coordinates_of_isConnected p C v O hv G hG
  have hc2 : ∀ n, IsAdicComplete (Ideal.span {(p : G.A n ⊗[O] G.A n)}) (G.A n ⊗[O] G.A n) :=
    fun n => GlobalTheory.T.isAdicComplete_span_natCast_of_finite_projective' p O _
  have hc3 : ∀ n, IsAdicComplete (Ideal.span {(p : G.A n ⊗[O] (G.A n ⊗[O] G.A n))})
      (G.A n ⊗[O] (G.A n ⊗[O] G.A n)) := fun n => GlobalTheory.T.isAdicComplete_span_natCast_of_finite_projective' p O _
  have hcA : ∀ n, IsAdicComplete (Ideal.span {(p : G.A n)}) (G.A n) := fun n => GlobalTheory.T.isAdicComplete_span_natCast_of_finite_projective' p O _
  have nil2 : ∀ n, ∀ j, ∃ N : ℕ, (p : G.A n ⊗[O] G.A n) ∣
      (Sum.elim (fun i => x n i ⊗ₜ[O] (1 : G.A n)) fun i => (1 : G.A n) ⊗ₜ[O] x n i) j ^ N := by
    rintro n (i | i)
    · simpa using nil_map (Algebra.TensorProduct.includeLeft : G.A n →ₐ[O] G.A n ⊗[O] G.A n).toRingHom (hnil n i)
    · simpa using nil_map (Algebra.TensorProduct.includeRight : G.A n →ₐ[O] G.A n ⊗[O] G.A n).toRingHom (hnil n i)
  have nil3 : ∀ n, ∀ j, ∃ N : ℕ, (p : G.A n ⊗[O] (G.A n ⊗[O] G.A n)) ∣
      (Sum.elim (fun i => x n i ⊗ₜ[O] (1 : G.A n ⊗[O] G.A n)) (Sum.elim (fun i => (1 : G.A n) ⊗ₜ[O] (x n i ⊗ₜ[O] (1 : G.A n))) fun i => (1 : G.A n) ⊗ₜ[O] ((1 : G.A n) ⊗ₜ[O] x n i))) j ^ N := by
    rintro n (i | i | i)
    · simpa using nil_map (Algebra.TensorProduct.includeLeft : G.A n →ₐ[O] G.A n ⊗[O] (G.A n ⊗[O] G.A n)).toRingHom (hnil n i)
    · simpa using nil_map ((Algebra.TensorProduct.includeRight : G.A n ⊗[O] G.A n →ₐ[O] G.A n ⊗[O] (G.A n ⊗[O] G.A n)).comp (Algebra.TensorProduct.includeLeft : G.A n →ₐ[O] G.A n ⊗[O] G.A n)).toRingHom (hnil n i)
    · simpa using nil_map ((Algebra.TensorProduct.includeRight : G.A n ⊗[O] G.A n →ₐ[O] G.A n ⊗[O] (G.A n ⊗[O] G.A n)).comp (Algebra.TensorProduct.includeRight : G.A n →ₐ[O] G.A n ⊗[O] G.A n)).toRingHom (hnil n i)
  have hE2 : ∀ n, ∃ E : MvPowerSeries (Fin d ⊕ Fin d) O →ₐ[O] G.A n ⊗[O] G.A n,
      IsEval p (Sum.elim (fun i => x n i ⊗ₜ[O] (1 : G.A n)) fun i => (1 : G.A n) ⊗ₜ[O] x n i) E := by
    intro n
    haveI := hc2 n
    exact (GlobalTheory.T.padicContinuousEvaluation_existsUnique_subst_natural p O _ _ _ (nil2 n)).1.exists
  choose E₂ hE₂ using hE2
  have hE3 : ∀ n, ∃ E : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) O →ₐ[O] G.A n ⊗[O] (G.A n ⊗[O] G.A n),
      IsEval p (Sum.elim (fun i => x n i ⊗ₜ[O] (1 : G.A n ⊗[O] G.A n)) (Sum.elim (fun i => (1 : G.A n) ⊗ₜ[O] (x n i ⊗ₜ[O] (1 : G.A n))) fun i => (1 : G.A n) ⊗ₜ[O] ((1 : G.A n) ⊗ₜ[O] x n i))) E := by
    intro n
    haveI := hc3 n
    exact (GlobalTheory.T.padicContinuousEvaluation_existsUnique_subst_natural p O _ _ _ (nil3 n)).1.exists
  choose E₃ hE₃ using hE3
  have hsurj2 : ∀ n, Function.Surjective (E₂ n) := fun n => by
    haveI := hc2 n
    exact GlobalTheory.T.surjective_isEval_tmul_of_surjective p O _ _ _ _ (x n) (x n) (ev n) (ev n) (E₂ n) (hev n) (hev n) (hE₂ n) (hsurj n) (hsurj n)
  have hker2 : ∀ m N : ℕ, ∃ n, ∀ f, E₂ n f = 0 → ∀ α : Fin d ⊕ Fin d →₀ ℕ, α.degree < N → (p : O) ^ m ∣ coeff α f := by
    intro m N
    obtain ⟨n, hn⟩ := hker m N
    exact ⟨n, GlobalTheory.T.dvd_coeff_of_ker_sum_of_dvd_coeff_ker p O _ _ _ _ (x n) (x n) (ev n) (ev n) (E₂ n) m N (hev n) (hev n) (hE₂ n) (hsurj n) (hsurj n) hn hn⟩
  have hker3 : ∀ m N : ℕ, ∃ n, ∀ f, E₃ n f = 0 → ∀ α : Fin d ⊕ (Fin d ⊕ Fin d) →₀ ℕ, α.degree < N → (p : O) ^ m ∣ coeff α f := by
    intro m N
    obtain ⟨n, hn⟩ := hker m N
    have hn2 := GlobalTheory.T.dvd_coeff_of_ker_sum_of_dvd_coeff_ker p O _ _ _ _ (x n) (x n) (ev n) (ev n) (E₂ n) m N (hev n) (hev n) (hE₂ n) (hsurj n) (hsurj n) hn hn
    have hpt : (Sum.elim (fun i => x n i ⊗ₜ[O] (1 : G.A n ⊗[O] G.A n)) fun j => (1 : G.A n) ⊗ₜ[O] (Sum.elim (fun i => x n i ⊗ₜ[O] (1 : G.A n)) (fun i => (1 : G.A n) ⊗ₜ[O] x n i) j)) = (Sum.elim (fun i => x n i ⊗ₜ[O] (1 : G.A n ⊗[O] G.A n)) (Sum.elim (fun i => (1 : G.A n) ⊗ₜ[O] (x n i ⊗ₜ[O] (1 : G.A n))) fun i => (1 : G.A n) ⊗ₜ[O] ((1 : G.A n) ⊗ₜ[O] x n i))) := by
      funext j
      rcases j with j | j | j <;> rfl
    have hE3' := hE₃ n
    rw [← hpt] at hE3'
    exact ⟨n, GlobalTheory.T.dvd_coeff_of_ker_sum_of_dvd_coeff_ker p O _ _ _ _ (x n) _ (ev n) (E₂ n) (E₃ n) m N (hev n) (hE₂ n) hE3' (hsurj n) (hsurj2 n) hn hn2⟩
  have hstep : ∀ i n f, E₂ (n + 1) f = Coalgebra.comul (R := O) (x (n + 1) i) →
      E₂ n f = Coalgebra.comul (R := O) (x n i) := by
    intro i n f hf
    let ρ : G.A (n + 1) ⊗[O] G.A (n + 1) →ₐ[O] G.A n ⊗[O] G.A n :=
      Algebra.TensorProduct.map (AlgHomClass.toAlgHom (G.res n)) (AlgHomClass.toAlgHom (G.res n))
    have hρ : ρ.comp (E₂ (n + 1)) = E₂ n := by
      haveI := hc2 n
      refine (GlobalTheory.T.padicContinuousEvaluation_existsUnique_subst_natural p O _ _ _ (nil2 n)).1.unique ?_ (hE₂ n)
      have h1 := isEval_comp ρ (hE₂ (n + 1))
      convert h1 using 1
      funext j
      rcases j with j | j <;> simp [ρ, hres]
    rw [← hρ, AlgHom.comp_apply, hf]
    exact (CoalgHomClass.map_comp_comul_apply (G.res n) (x (n + 1) i)).trans (by rw [hres])
  have hμ : ∀ i, ∃ g, ∀ n, E₂ n g = Coalgebra.comul (R := O) (x n i) := by
    intro i
    exact GlobalTheory.T.exists_series_of_compatible' p O (Fin d ⊕ Fin d) (fun n => G.A n ⊗[O] G.A n) (fun n => (hc2 n).toIsHausdorff) _ E₂
      (fun n => Coalgebra.comul (R := O) (x n i)) hE₂ (fun n => hsurj2 n _) (hstep i) hker2
  choose μ hμ using hμ
  have hconst : ∀ i, constantCoeff (μ i) = 0 :=
    GlobalTheory.T.constantCoeff_eq_zero_of_eval_eq_comul' p O (G.A 0) (x 0) (E₂ 0) μ (haug 0) (hE₂ 0) (fun i => hμ i 0)
  refine ⟨d, ⟨⟨x, ev, E₂, μ, hnil, hev, hE₂, hres, haug, hsurj, hker, ?_, fun n i => hμ i n⟩⟩⟩
  refine ⟨hconst, ?_, fun i => ?_, ?_⟩
  · funext i
    refine sub_eq_zero.1 (eq_zero_of_ker (p := p) ev hker fun n => ?_)
    haveI := hcA n
    rw [map_sub, GlobalTheory.T.formalChart_groupLaw_eval_right_unit p O (G.A n) (x n) (ev n) (E₂ n) μ (hnil n) (haug n) (hev n) (hE₂ n) (fun i => hμ i n) i,
      (hev n).1 i, sub_self]
  · refine sub_eq_zero.1 (eq_zero_of_ker (p := p) E₂ hker2 fun n => ?_)
    haveI := hc2 n
    rw [map_sub, GlobalTheory.T.eval_swap_eq' p O (G.A n) (x n) (E₂ n) μ (hnil n) (hE₂ n) (fun i => hμ i n) i, sub_self]
  · funext i
    refine sub_eq_zero.1 (eq_zero_of_ker (p := p) E₃ hker3 fun n => ?_)
    haveI := hc3 n
    rw [map_sub, GlobalTheory.T.isEval_comul_assoc_of_isEval p O (G.A n) (x n) (E₂ n) (E₃ n) μ (hnil n) hconst (hE₂ n) (hE₃ n) (fun i => hμ i n) i, sub_self]

end GlobalTheory.ChartEx
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPermOfBlockSizeBijection
section
open Formalism.L2.DIV GlobalTheory.FinGL GlobalTheory.Parabolic GlobalTheory.IndefiniteRowSideFullHecke.BlockProductIsomorphism

namespace GlobalTheory

theorem exists_perm_of_block_bijection : ∀ (r : ℕ) (b b' : Fin r → ℕ) (R : ℕ → ℕ → Prop), (∀ c ∈ Set.range b, ∃! c', c' ∈ Set.range b' ∧ R c c') → (∀ c' ∈ Set.range b', ∃! c, c ∈ Set.range b ∧ R c c') → (∀ c ∈ Set.range b, ∀ c' ∈ Set.range b', R c c' → (block b c).card = (block b' c').card) → ∃ w : Equiv.Perm (Fin r), (∀ i, R (b i) (b' (w i))) ∧ ∀ i j : Fin r, b i = b j ↔ b' (w i) = b' (w j) := by
  classical
  intro r b b' R h1 h2 h3
  have h1' : ∀ i : Fin r, ∃ c', c' ∈ Set.range b' ∧ R (b i) c' :=
    fun i => (h1 (b i) ⟨i, rfl⟩).exists
  choose f hf1 hf2 using h1'
  have hiff : ∀ i c c', c ∈ Set.range b → c' ∈ Set.range b' → R c c' → (f i = c' ↔ b i = c) := by
    intro i c c' hc hc' hR
    constructor
    · intro h
      exact (h2 c' hc').unique ⟨⟨i, rfl⟩, h ▸ hf2 i⟩ ⟨hc, hR⟩
    · intro h
      subst h
      exact (h1 (b i) hc).unique ⟨hf1 i, hf2 i⟩ ⟨hc', hR⟩
  have hcard : ∀ c' : ℕ, Fintype.card {i // f i = c'} = Fintype.card {i // b' i = c'} := by
    intro c'
    rw [Fintype.card_subtype, Fintype.card_subtype]
    by_cases hc' : c' ∈ Set.range b'
    · obtain ⟨c, hc, hR⟩ := (h2 c' hc').exists
      have h := h3 c hc c' hc' hR
      unfold block at h
      rw [← h]
      congr 1
      ext i
      simp [hiff i c c' hc hc' hR]
    · rw [Finset.filter_eq_empty_iff.2, Finset.filter_eq_empty_iff.2]
      · intro i _ h
        exact hc' ⟨i, h⟩
      · intro i _ h
        exact hc' (h ▸ hf1 i)
  let e : ∀ c' : ℕ, {i // f i = c'} ≃ {i // b' i = c'} := fun c' => Fintype.equivOfCardEq (hcard c')
  have hw : ∀ i, b' (Equiv.ofFiberEquiv e i) = f i := fun i => Equiv.ofFiberEquiv_map e i
  refine ⟨Equiv.ofFiberEquiv e, fun i => ?_, fun i j => ?_⟩
  · rw [hw]; exact hf2 i
  · rw [hw, hw]
    exact (hiff i (b j) (f j) ⟨j, rfl⟩ (hf1 j) (hf2 j)).symm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionLiftSmoothNilpotentThickeningStatement
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_section_lift_smooth_nilpotent_thickening : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀), Function.Surjective π → IsNilpotent (RingHom.ker π) →
    ∀ (X : Over (Sp R)) (X₀ : Over (Sp R₀)) (i : X₀.left ⟶ X.left), IsPullback i X₀.hom X.hom (spMap π) → Smooth X.hom →
    ∀ e₀ : Sp R₀ ⟶ X₀.left, e₀ ≫ X₀.hom = 𝟙 _ → ∃ e : Sp R ⟶ X.left, e ≫ X.hom = 𝟙 _ ∧ e₀ ≫ i = spMap π ≫ e := by
  first | exact @GlobalTheory.SecLift.exists_section_lift | exact GlobalTheory.SecLift.exists_section_lift | (intros; apply GlobalTheory.SecLift.exists_section_lift <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSliceTaylorAlgHom
section
set_option autoImplicit false

noncomputable section

open Filter Topology TopologicalSpace GlobalTheory.AnPer TensorProduct

namespace GlobalTheory.AnPer.SliceTaylor

variable {I : Type} [Fintype I] [DecidableEq I] {g : ℕ}

theorem analyticAt_shift (q : (I ⊕ Fin g → ℂ) × (Fin g → ℂ)) :
    AnalyticAt ℂ (fun y : (I ⊕ Fin g → ℂ) × (Fin g → ℂ) ↦
      (((fun i ↦ y.1 (Sum.inl i)), y.2 + fun b ↦ y.1 (Sum.inr b)) : (I → ℂ) × (Fin g → ℂ))) q := by
  have h1 : ∀ j, AnalyticAt ℂ (fun y : (I ⊕ Fin g → ℂ) × (Fin g → ℂ) ↦ y.1 j) q := fun j ↦
    ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : I ⊕ Fin g ↦ ℂ) j).comp
      (ContinuousLinearMap.fst ℂ (I ⊕ Fin g → ℂ) (Fin g → ℂ))).analyticAt q
  refine AnalyticAt.prod (analyticAt_pi_iff.2 fun i ↦ h1 _) ?_
  exact analyticAt_snd.add (analyticAt_pi_iff.2 fun i ↦ h1 _)

theorem analyticAt_joint {W : Opens ((I → ℂ) × (Fin g → ℂ))} (h : Hol W) {w : Fin g → ℂ}
    (hw : ((0 : I → ℂ), w) ∈ W) :
    AnalyticAt ℂ (fun y : (I ⊕ Fin g → ℂ) × (Fin g → ℂ) ↦
      h.fn ((fun i ↦ y.1 (Sum.inl i)), y.2 + fun b ↦ y.1 (Sum.inr b))) (0, w) := by
  refine AnalyticAt.comp_of_eq (h.analytic _ hw) (analyticAt_shift _) ?_
  ext <;> simp

theorem analyticAt_slice {W : Opens ((I → ℂ) × (Fin g → ℂ))} (h : Hol W) {w : Fin g → ℂ}
    (hw : ((0 : I → ℂ), w) ∈ W) :
    AnalyticAt ℂ (fun x : I ⊕ Fin g → ℂ ↦
      h.fn ((fun i ↦ x (Sum.inl i)), w + fun b ↦ x (Sum.inr b))) 0 :=
  AnalyticAt.comp_of_eq (f := fun x : I ⊕ Fin g → ℂ ↦ (x, w)) (analyticAt_joint h hw)
    (analyticAt_id.prod analyticAt_const) rfl

theorem eventually_mem {W : Opens ((I → ℂ) × (Fin g → ℂ))} {w : Fin g → ℂ}
    (hw : ((0 : I → ℂ), w) ∈ W) :
    ∀ᶠ x : I ⊕ Fin g → ℂ in 𝓝 0,
      (((fun i ↦ x (Sum.inl i)), w + fun b ↦ x (Sum.inr b)) : (I → ℂ) × (Fin g → ℂ)) ∈ W := by
  have hc : Continuous (fun x : I ⊕ Fin g → ℂ ↦
      (((fun i ↦ x (Sum.inl i)), w + fun b ↦ x (Sum.inr b)) : (I → ℂ) × (Fin g → ℂ))) := by
    fun_prop
  refine hc.continuousAt.eventually (W.isOpen.mem_nhds ?_)
  have e : (((fun i ↦ (0 : I ⊕ Fin g → ℂ) (Sum.inl i)), w + fun b ↦ (0 : I ⊕ Fin g → ℂ) (Sum.inr b)) :
      (I → ℂ) × (Fin g → ℂ)) = (0, w) := by
    ext <;> simp
  change _ ∈ W
  simp only [e]
  exact hw

end GlobalTheory.AnPer.SliceTaylor

open GlobalTheory.AnPer.SliceTaylor in

theorem GlobalTheory.AnPer.exists_sliceTaylor_algHom : ∀ {I : Type} [Fintype I] [DecidableEq I] {g : ℕ} {D : Type} [CommRing D] [Algebra ℂ D] (N : ℕ) (t : I ⊕ Fin g → D), (∀ s : Fin (N + 1) → I ⊕ Fin g, ∏ a, t (s a) = 0) → ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] (W : Opens ((I → ℂ) × (Fin g → ℂ))) (W₀ : Opens E) (a : E → Fin g → ℂ), AnalyticOnNhd ℂ a W₀ → (∀ p ∈ W₀, ((0 : I → ℂ), a p) ∈ W) → ∃ ρ : Hol W →ₐ[ℂ] D ⊗[ℂ] Hol W₀, ∀ (h : Hol W) (p : E) (hp : p ∈ W₀), Algebra.TensorProduct.lift (AlgHom.id ℂ D) ((Algebra.ofId ℂ D).comp (Hol.ev p hp)) (fun _ _ ↦ Commute.all _ _) (ρ h) = GlobalTheory.PeriodFamily.taylor N t (fun x : I ⊕ Fin g → ℂ ↦ h.fn (fun i ↦ x (Sum.inl i), a p + fun b ↦ x (Sum.inr b))) := by
  intro I _ _ g D _ _ N t ht E _ _ _ W W₀ a ha hW
  have key : ∀ h : Hol W, ∃ r : D ⊗[ℂ] Hol W₀, ∀ (p : E) (hp : p ∈ W₀), Algebra.TensorProduct.lift (AlgHom.id ℂ D) ((Algebra.ofId ℂ D).comp (Hol.ev p hp)) (fun _ _ ↦ Commute.all _ _) r = GlobalTheory.PeriodFamily.taylor N t (fun x : I ⊕ Fin g → ℂ ↦ h.fn (fun i ↦ x (Sum.inl i), a p + fun b ↦ x (Sum.inr b))) := by
    intro h
    have han : ∀ (k : ℕ) (v : Fin k → (I ⊕ Fin g → ℂ)), AnalyticOnNhd ℂ (fun p ↦ iteratedFDeriv ℂ k
        (fun x : I ⊕ Fin g → ℂ ↦ h.fn (fun i ↦ x (Sum.inl i), a p + fun b ↦ x (Sum.inr b))) 0 v) W₀ :=
      fun k v p hp ↦
        AnalyticAt.comp_of_eq (GlobalTheory.T.analyticAt_iteratedFDeriv_slice_and_fderiv_eq _ (a p) k v (analyticAt_joint h (hW p hp))).1 (ha p hp) rfl
    unfold GlobalTheory.PeriodFamily.taylor
    refine ⟨∑ k ∈ Finset.range (N + 1), ∑ s : Fin k → I ⊕ Fin g,
      ((k.factorial : ℂ)⁻¹ • ∏ b, t (s b)) ⊗ₜ[ℂ] Hol.mk _ (han k fun b ↦ Pi.single (s b) 1), fun p hp ↦ ?_⟩
    simp only [map_sum]
    refine Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun s _ ↦ ?_
    rw [Algebra.TensorProduct.lift_tmul, AlgHom.comp_apply, Hol.ev_apply, Hol.fn_mk _ _ hp,
      AlgHom.id_apply, Algebra.ofId_apply, mul_comm, ← Algebra.smul_def, smul_smul, mul_comm]
  choose r hr using key
  obtain ⟨hadd, -, hconst, hcongr, -, -⟩ := GlobalTheory.T.taylorPolynomialEvalAlgebra_formal_properties N t
  have hc : ∀ c : ℂ, r (algebraMap ℂ _ c) = algebraMap ℂ _ c := fun c ↦ by
    refine GlobalTheory.T.tensor_holomorphic_ext_of_values W₀ D _ _ fun p hp ↦ ?_
    rw [hr, AlgHom.commutes, ← hconst c]
    refine hcongr _ _ ?_
    filter_upwards [eventually_mem (hW p hp)] with x hx using Hol.fn_algebraMap c hx
  have hA : ∀ f h : Hol W, r (f + h) = r f + r h := fun f h ↦ by
    refine GlobalTheory.T.tensor_holomorphic_ext_of_values W₀ D _ _ fun p hp ↦ ?_
    rw [map_add, hr, hr, hr, ← hadd _ _ (analyticAt_slice f (hW p hp)) (analyticAt_slice h (hW p hp))]
    refine hcongr _ _ ?_
    filter_upwards [eventually_mem (hW p hp)] with x hx using Hol.fn_add f h hx
  have hM : ∀ f h : Hol W, r (f * h) = r f * r h := fun f h ↦ by
    refine GlobalTheory.T.tensor_holomorphic_ext_of_values W₀ D _ _ fun p hp ↦ ?_
    rw [map_mul, hr, hr, hr,
      ← GlobalTheory.T.taylorPolynomialEvalAlgebra_mul_of_prod_eq_zero N t ht _ _ (analyticAt_slice f (hW p hp)) (analyticAt_slice h (hW p hp))]
    refine hcongr _ _ ?_
    filter_upwards [eventually_mem (hW p hp)] with x hx using Hol.fn_mul f h hx
  exact ⟨{ toFun := r
           map_one' := by simpa only [map_one] using hc 1
           map_mul' := hM
           map_zero' := by simpa using hc 0
           map_add' := hA
           commutes' := hc }, hr⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStableCharacterFlagOfCharpolyFactorStatement
section
open Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_stable_character_flag_of_charpoly_factor : ∀ (k Γ : Type) [Field k] [Group Γ] (n a t : ℕ) (r : Γ →* GL (Fin n) k) (ρ : Γ →* GL (Fin a) k) (ψ : Fin t → Γ →* kˣ), a + t = n → (∀ g, (r g : Matrix (Fin n) (Fin n) k).charpoly = (ρ g : Matrix (Fin a) (Fin a) k).charpoly * ∏ s, (Polynomial.X - Polynomial.C ((ψ s g : kˣ) : k))) → ∃ (R : ℕ) (V : Fin (R + 1) → Submodule k (Fin n → k)) (rs : Fin t → Fin R), V 0 = ⊥ ∧ V (Fin.last R) = ⊤ ∧ Monotone V ∧ (∀ g j x, x ∈ V j → (r g : Matrix (Fin n) (Fin n) k).mulVec x ∈ V j) ∧ Function.Injective rs ∧ ∀ s, ∃ x ∈ V (rs s).succ, x ∉ V (rs s).castSucc ∧ V (rs s).succ = V (rs s).castSucc ⊔ Submodule.span k {x} ∧ ∀ g, (r g : Matrix (Fin n) (Fin n) k).mulVec x - ((ψ s g : kˣ) : k) • x ∈ V (rs s).castSucc := by
  first | exact @GlobalTheory.CharFlag.main | exact GlobalTheory.CharFlag.main | (intros; apply GlobalTheory.CharFlag.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStrictlyHenselianIndEtaleOverPrimeStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_strictlyHenselian_indEtale_over_prime : ∀ (A : Type) [CommRing A] (p : Ideal A) [p.IsPrime], ∃ (O : Type) (_ : CommRing O) (_ : Algebra A O) (_ : IsLocalRing O), SH O ∧ IndEt A O ∧ (IsLocalRing.maximalIdeal O).comap (algebraMap A O) = p := by
  first | (exact @GlobalTheory.StrictHensPrime.exists_sh_indEt) | (exact GlobalTheory.StrictHensPrime.exists_sh_indEt) | (intros; apply GlobalTheory.StrictHensPrime.exists_sh_indEt  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTangentOfUniformisationJetStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_tangent_of_uniformisation_jet : ∀ {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g), A.left.IsSeparated → ∀ (W : Opens (Tot Empty g)) (x : Sp (Hol W) ⟶ A.left), (∀ (p : Tot Empty g) (hp : p ∈ W), spMap (Hol.ev p hp).toRingHom ≫ x = (u.ex p.2).left) → x ≫ A.hom = spMap (algebraMap ℂ (Hol W)) → (0 : Tot Empty g) ∈ W → ∀ (w : Fin g → ℂ) (ρ : Hol W →ₐ[ℂ] DualNumber ℂ), (∀ h, (ρ h).fst = h.fn 0 ∧ (ρ h).snd = fderiv ℂ h.fn 0 (0, w)) → ∃ v : epsR ℂ ⟶ A, v.left = spMap ρ.toRingHom ≫ x ∧ IsTangent v ∧ u.IsDiff w v := by
  first | exact @GlobalTheory.AnPer.exists_tangent_of_jet | exact GlobalTheory.AnPer.exists_tangent_of_jet | (intros; apply GlobalTheory.AnPer.exists_tangent_of_jet <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTaylorAlgHomHolomorphicNilpotentStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer GlobalTheory.PeriodFamily
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_taylor_algHom_holomorphic_nilpotent : ∀ {I : Type} [Fintype I] [DecidableEq I] {R : Type} [CommRing R] [Algebra ℂ R] (N : ℕ) (t : I → R), (∀ s : Fin (N + 1) → I, ∏ a, t (s a) = 0) → ∀ (V : Opens (I → ℂ)), 0 ∈ V → ∃ θ : Hol V →ₐ[ℂ] R, ∀ f, θ f = taylor N t f.fn := by
  first | exact @GlobalTheory.AnPer.exists_taylor_algHom | exact GlobalTheory.AnPer.exists_taylor_algHom | (intros; apply GlobalTheory.AnPer.exists_taylor_algHom <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryHarishChandraDiscreteSeriesStatement
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitary_harishChandra_discreteSeries : ∀ (p q : ℕ) (T : GrpData p q) (D : DSRep T), ∃ M : UGKMod p q, M.M = D.HK := by
  first | exact @GlobalTheory.DiscreteSeriesUnitary.exists_unitary | exact GlobalTheory.DiscreteSeriesUnitary.exists_unitary | (intros; apply GlobalTheory.DiscreteSeriesUnitary.exists_unitary <;> assumption)
end

