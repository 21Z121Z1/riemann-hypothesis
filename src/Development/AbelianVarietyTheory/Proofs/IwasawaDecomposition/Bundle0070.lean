import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0066
import Formalism.LocalToGlobal.Columns.Bundle0002
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0059
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0064
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0060
import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0012
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0067
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0045
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0063
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0055
import Formalism.LocalToGlobal.Divisibility.ProjLemmas

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AbsIrrCharMemClosurePrimitiveRootCardStatement
section
open Formalism.L2.DIV
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.absIrrChar_mem_closure_primitiveRoot_card : ∀ {G : Type} [inst : Group G] [inst_1 : Fintype G] {K : Type} [inst_2 : Field K] [inst_3 : CharZero K] (z : K), IsPrimitiveRoot z (Fintype.card G) → ∀ (χ : G → K), IsAbsIrrChar χ → ∀ g : G, χ g ∈ Subring.closure ({z} : Set K) := by
  first | exact @GlobalTheory.absIrrChar_mem_closure_primitiveRoot | exact GlobalTheory.absIrrChar_mem_closure_primitiveRoot | (intros; apply GlobalTheory.absIrrChar_mem_closure_primitiveRoot <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AbsIrrCharRealiseOfPrimitiveRootCardStatement
section
open Formalism.L2.DIV
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.absIrrChar_realise_of_primitiveRoot_card : ∀ {G : Type} [inst : Group G] [inst_1 : Fintype G] {K : Type} [inst_2 : Field K] (σ : K →+* ℂ) (z : K), IsPrimitiveRoot z (Fintype.card G) → ∀ (ψ : G → ℂ), ψ ∈ Formalism.L2.Col.gxIrrSet (G := G) ℂ → ∃ χ : G → K, IsAbsIrrChar χ ∧ ∀ g, σ (χ g) = ψ g := by
  first | exact @GlobalTheory.BrauerRealise.absIrr_realise_of_isPrimitiveRoot | exact GlobalTheory.BrauerRealise.absIrr_realise_of_isPrimitiveRoot | (intros; apply GlobalTheory.BrauerRealise.absIrr_realise_of_isPrimitiveRoot <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AcrisDivisibleOfKernelPowers
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc.PdModP

variable {R A : Type} [CommRing R] [CommRing A] [Algebra R A]

def low (R : Type) {A : Type} [CommRing R] [CommRing A] [Algebra R A] (γ : ℕ → A) (N : ℕ) : Submodule R A :=
  Submodule.span R (γ '' {m | m < N})

theorem low_mono (γ : ℕ → A) {M N : ℕ} (h : M ≤ N) : low R γ M ≤ low R γ N :=
  Submodule.span_mono (Set.image_mono fun _ hm => lt_of_lt_of_le hm h)

theorem mem_low_succ (γ : ℕ → A) (N : ℕ) (s : A) (hs : s ∈ low R γ (N + 1)) :
    ∃ (a : R) (y : A), y ∈ low R γ N ∧ s = a • γ N + y := by
  have e : {m | m < N + 1} = insert N {m | m < N} := by
    ext m; simp only [Set.mem_ofPred_eq, Set.mem_insert_iff]; omega
  rw [low, e, Set.image_insert_eq, Submodule.mem_span_insert] at hs
  exact hs

section
variable (hu : ∀ n : ℕ, IsUnit ((n.factorial : ℕ) : A)) (ξ : R) (γ : ℕ → A)
  (hγ : ∀ n : ℕ, ((n.factorial : ℕ) : A) * γ n = algebraMap R A ξ ^ n)
include hu hγ

theorem pow_dvd_gamma {m n : ℕ} (h : m ≤ n) : algebraMap R A ξ ^ m ∣ γ n := by
  obtain ⟨v, hv⟩ := (hu n).exists_left_inv
  have : γ n = v * algebraMap R A ξ ^ n := by rw [← hγ, ← mul_assoc, hv, one_mul]
  rw [this]
  exact Dvd.dvd.mul_left (pow_dvd_pow _ h) _

theorem mul_gamma (n : ℕ) : algebraMap R A ξ * γ n = ((n + 1 : ℕ) : A) * γ (n + 1) := by
  refine (hu n).mul_left_cancel ?_
  have h1 := hγ n
  have h2 := hγ (n + 1)
  rw [Nat.factorial_succ, Nat.cast_mul, pow_succ] at h2
  linear_combination (algebraMap R A ξ) * h1 - h2

theorem low_inter (hreg : ∀ y : A, algebraMap R A ξ * y = 0 → y = 0)
    (hsat : ∀ a : R, algebraMap R A ξ ∣ algebraMap R A a → ξ ∣ a) (N : ℕ) :
    ∀ s ∈ low R γ N, algebraMap R A ξ ^ N ∣ s → ∃ c : R, s = c • ((N : A) * γ N) := by
  have hregn : ∀ (n : ℕ) (y : A), algebraMap R A ξ ^ n * y = 0 → y = 0 := by
    intro n
    induction n with
    | zero => intro y hy; simpa using hy
    | succ n ih => intro y hy; exact hreg y (ih _ (by rw [← hy]; ring))
  induction N with
  | zero =>
    intro s hs _
    refine ⟨0, ?_⟩
    simpa [low] using hs
  | succ N ih =>
    intro s hs hd
    obtain ⟨a, y, hy, rfl⟩ := mem_low_succ γ N s hs
    have h1 : algebraMap R A ξ ^ N ∣ a • γ N := by
      rw [Algebra.smul_def]
      exact Dvd.dvd.mul_left (pow_dvd_gamma hu ξ γ hγ le_rfl) _
    obtain ⟨c, rfl⟩ := ih y hy ((dvd_add_right h1).1 ((pow_dvd_pow _ N.le_succ).trans hd))
    obtain ⟨z, hz⟩ := hd
    have h2 : algebraMap R A ξ ∣ algebraMap R A (a + c * N) := by
      refine ⟨(N.factorial : ℕ) * z, sub_eq_zero.1 (hregn N _ ?_)⟩
      rw [Algebra.smul_def, Algebra.smul_def] at hz
      rw [map_add, map_mul, map_natCast]
      have h3 := hγ N
      linear_combination ((N.factorial : ℕ) : A) * hz - (algebraMap R A a + algebraMap R A c * N) * h3
    obtain ⟨d, hd⟩ := hsat _ h2
    refine ⟨d, ?_⟩
    have h4 := congrArg (algebraMap R A) hd
    rw [map_add, map_mul, map_natCast, map_mul] at h4
    rw [← mul_gamma hu ξ γ hγ, Algebra.smul_def, Algebra.smul_def, Algebra.smul_def]
    linear_combination γ N * h4

theorem split_low (N : ℕ) (w : A) (hw : w ∈ Submodule.span R (Set.range γ)) :
    ∃ w₁ ∈ low R γ N, algebraMap R A ξ ^ N ∣ w - w₁ := by
  first
  | exact @_root_.GlobalTheory.IsolatedTheoremThree.main
  | exact _root_.GlobalTheory.IsolatedTheoremThree.main
  | (apply _root_.GlobalTheory.IsolatedTheoremThree.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.IsolatedTheoremThree.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IsolatedTheoremThree.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IsolatedTheoremThree.main ..)

end

theorem exists_low (γ : ℕ → A) (s : A) (hs : s ∈ Submodule.span R (Set.range γ)) : ∃ M, s ∈ low R γ M := by
  induction hs using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, rfl⟩ := hx
    exact ⟨m + 1, Submodule.subset_span ⟨m, m.lt_succ_self, rfl⟩⟩
  | zero => exact ⟨0, zero_mem _⟩
  | add x y _ _ hx hy =>
    obtain ⟨M, h1⟩ := hx
    obtain ⟨N, h2⟩ := hy
    exact ⟨max M N, add_mem (low_mono γ (le_max_left _ _) h1) (low_mono γ (le_max_right _ _) h2)⟩
  | smul a x _ hx =>
    obtain ⟨M, h1⟩ := hx
    exact ⟨M, Submodule.smul_mem _ _ h1⟩

theorem mem_of_forall (hu : ∀ n : ℕ, IsUnit ((n.factorial : ℕ) : A)) (ξ : R) (γ : ℕ → A)
    (hγ : ∀ n : ℕ, ((n.factorial : ℕ) : A) * γ n = algebraMap R A ξ ^ n)
    (hreg : ∀ y : A, algebraMap R A ξ * y = 0 → y = 0)
    (hsat : ∀ a : R, algebraMap R A ξ ∣ algebraMap R A a → ξ ∣ a) (p : ℕ) (hp : 0 < p)
    (s : A) (hs : s ∈ Submodule.span R (Set.range γ))
    (h : ∀ n : ℕ, ∃ u : A, ∃ w ∈ Submodule.span R (Set.range γ), s = u + p * w ∧ algebraMap R A ξ ^ n ∣ u) :
    ∃ w ∈ Submodule.span R (Set.range γ), s = p * w := by
  obtain ⟨M, hM⟩ := exists_low γ s hs
  obtain ⟨u, w, hw, e, hd⟩ := h (p * M)
  obtain ⟨w₁, h1, h2⟩ := split_low hu ξ γ hγ (p * M) w hw
  have h3 : s - p * w₁ ∈ low R γ (p * M) := by
    refine sub_mem (low_mono γ (Nat.le_mul_of_pos_left M hp) hM) ?_
    rw [← nsmul_eq_mul]
    exact nsmul_mem h1 p
  obtain ⟨c, hc⟩ := low_inter hu ξ γ hγ hreg hsat (p * M) _ h3
    (by convert dvd_add hd (Dvd.dvd.mul_left h2 (p : A)) using 1; rw [e]; ring)
  refine ⟨w₁ + (c * M) • γ (p * M), add_mem (Submodule.span_mono (Set.image_subset_range _ _) h1)
    (Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)), ?_⟩
  rw [Algebra.smul_def] at hc
  rw [Algebra.smul_def, map_mul, map_natCast]
  push_cast at hc
  linear_combination hc

theorem exists_eps (l : ℕ) [Fact l.Prime] : ∃ e : Per.Fl l, IsEps e := by
  obtain ⟨ζ, e, h0, -, h1, hr⟩ := exists_zeta_eps l
  refine ⟨e, ?_, fun h => ?_⟩
  · have h := hr 0
    rw [h0, map_one] at h
    exact Subtype.ext h
  · have h' := hr 1
    have h2 : rootT e 1 = 1 := h
    rw [h2] at h'
    apply h1
    apply (algebraMap (Om l) ℂ_[l]).injective
    rw [map_one, ← h']
    rfl

theorem xi_sat_pow {l : ℕ} [Fact l.Prime] {e : Per.Fl l} (he : IsEps e) (k : ℕ) (a : Per.Ainf l)
    (h : xi e ∣ (l : Per.Ainf l) ^ k * a) : xi e ∣ a := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
    apply ih
    have := XiHaus.xi_sat he 1 ((l : Per.Ainf l) ^ k * a) (by rwa [pow_one, ← mul_assoc, ← pow_succ'])
    rwa [pow_one] at this

end GlobalTheory.MemLoc.PdModP

namespace GlobalTheory.MemLoc
open PdModP in

theorem dvd_of_forall_fil_add : ∀ (l : ℕ) [Fact l.Prime], ∀ s : Per.Acris0 l,
    (∀ n : ℕ, ∃ (u w : Per.Acris0 l), s = u + (l : Per.Acris0 l) * w ∧ (u : Per.AinfP l) ∈ Per.kerP l ^ n) →
    (l : Per.Acris0 l) ∣ s := by
  intro l hl s h
  obtain ⟨e, he⟩ := exists_eps l
  have hu : ∀ n : ℕ, IsUnit ((n.factorial : ℕ) : Per.AinfP l) := fun n => GlobalTheory.RingBasics.isUnit_nat l _ n.factorial_ne_zero
  have hex : ∀ n : ℕ, ∃ g : Per.AinfP l,
      ((n.factorial : ℕ) : Per.AinfP l) * g = algebraMap (Per.Ainf l) (Per.AinfP l) (xi e) ^ n := fun n => by
    obtain ⟨v, hv⟩ := (hu n).exists_right_inv
    exact ⟨v * _, by rw [← mul_assoc, hv, one_mul]⟩
  choose γ hγ using hex
  have hspan : ∀ x : Per.AinfP l, x ∈ Per.Acris0 l ↔ x ∈ Submodule.span (Per.Ainf l) (Set.range γ) := by
    intro x
    rw [mem_Acris0_iff_span l e he]
    congr! 2
    ext y
    constructor
    · rintro ⟨n, hn⟩
      exact ⟨n, (hu n).mul_left_cancel (by rw [hγ, hn])⟩
    · rintro ⟨n, rfl⟩
      exact ⟨n, hγ n⟩
  have := XiHaus.isDomain_Fl (l := l)
  have hle : Submonoid.powers (l : Per.Ainf l) ≤ nonZeroDivisors _ :=
    powers_le_nonZeroDivisors_of_noZeroDivisors (WittVector.p_nonzero l (Per.Fl l))
  have hdom : IsDomain (Per.AinfP l) := IsLocalization.isDomain_of_le_nonZeroDivisors _ hle
  have hinj := IsLocalization.injective (Per.AinfP l) hle
  have hx0 : algebraMap (Per.Ainf l) (Per.AinfP l) (xi e) ≠ 0 := by
    rw [map_ne_zero_iff _ hinj]
    intro h0
    exact XiHaus.xi_coeff_zero_ne he (by rw [h0, WittVector.zero_coeff])
  obtain ⟨w, hw, e1⟩ := mem_of_forall hu (xi e) γ hγ (fun y hy => (mul_eq_zero.1 hy).resolve_left hx0)
    (by
      rintro a ⟨z, hz⟩
      obtain ⟨⟨b, ⟨_, k, rfl⟩⟩, hb⟩ := IsLocalization.surj (Submonoid.powers (l : Per.Ainf l)) z
      refine xi_sat_pow he k a ⟨b, hinj ?_⟩
      simp only at hb
      rw [map_mul, map_mul, hz, ← hb]
      ring)
    l hl.out.pos s ((hspan _).1 s.2) (fun n => by
      obtain ⟨u, w, h1, h2⟩ := h n
      refine ⟨u, w, (hspan _).1 w.2, by rw [h1]; simp, ?_⟩
      rwa [ker_localizedTheta_eq_span_xi l e he, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h2)
  exact ⟨⟨w, (hspan _).2 hw⟩, Subtype.ext (by simpa using e1)⟩

end GlobalTheory.MemLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AcrisMembershipSpanIffStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.acris_membership_span_iff : ∀ (l : ℕ) [Fact l.Prime], ∀ e : Per.Fl l, IsEps e → ∀ s : Per.AinfP l, s ∈ Per.Acris0 l ↔ s ∈ Submodule.span (Per.Ainf l) {y : Per.AinfP l | ∃ n : ℕ, ((n.factorial : ℕ) : Per.AinfP l) * y = algebraMap (Per.Ainf l) (Per.AinfP l) (xi e) ^ n} := by
  first | exact @GlobalTheory.MemLoc.mem_Acris0_iff_span | exact GlobalTheory.MemLoc.mem_Acris0_iff_span | (intros; apply GlobalTheory.MemLoc.mem_Acris0_iff_span <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgebraMapAinfInvPrimeBdRPlusInjective
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc

theorem exists_isEps_for_inj (l : ℕ) [Fact l.Prime] : ∃ e : Per.Fl l, IsEps e := by
  obtain ⟨ζ, ε, h0, -, h1, h⟩ := GlobalTheory.MemLoc.exists_zeta_eps l
  refine ⟨ε, ?_, ?_⟩
  · have := h 0
    rw [h0, map_one] at this
    exact Subtype.ext this
  · intro hh
    have := h 1
    apply h1
    apply (algebraMap (Om l) ℂ_[l]).injective
    rw [← this, map_one]
    exact congrArg Subtype.val hh

theorem eq_zero_of_mem_span_pow_away {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] (r ξ : A)
    [IsLocalization.Away r B] (hs : ∀ n : ℕ, ∀ a : A, ξ ^ n ∣ r * a → ξ ^ n ∣ a)
    (hh : ∀ a : A, (∀ n : ℕ, ξ ^ n ∣ a) → a = 0) (x : B)
    (hx : ∀ n : ℕ, x ∈ Ideal.span {algebraMap A B ξ} ^ n) : x = 0 := by
  have hs' : ∀ n m : ℕ, ∀ a : A, ξ ^ n ∣ r ^ m * a → ξ ^ n ∣ a := by
    intro n m
    induction m with
    | zero => intro a ha; simpa using ha
    | succ m ih =>
      intro a ha
      apply ih
      apply hs
      rwa [← mul_assoc, ← pow_succ']
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers r) x
  have ha : a = 0 := by
    apply hh
    intro n
    have h1 : algebraMap A B a ∈ Ideal.map (algebraMap A B) (Ideal.span {ξ ^ n}) := by
      rw [Ideal.map_span, Set.image_singleton, map_pow, ← Ideal.span_singleton_pow,
        ← IsLocalization.mk'_spec B a s]
      exact Ideal.mul_mem_right _ _ (hx n)
    rw [IsLocalization.algebraMap_mem_map_algebraMap_iff (Submonoid.powers r)] at h1
    obtain ⟨_, ⟨m, rfl⟩, hm⟩ := h1
    exact hs' n m a (Ideal.mem_span_singleton.1 hm)
  simp [ha]

theorem algebraMap_AinfP_BdRp_injective (l : ℕ) [Fact l.Prime] :
    Function.Injective (algebraMap (Per.AinfP l) (Per.BdRp l)) := by
  obtain ⟨e, he⟩ := exists_isEps_for_inj l
  rw [injective_iff_map_eq_zero]
  intro x hx
  refine eq_zero_of_mem_span_pow_away (l : Per.Ainf l) (xi e)
    (fun n a h => XiHaus.xi_sat he n a h) (GlobalTheory.MemLoc.eq_zero_of_forall_xi_pow_dvd l e he) x fun n => ?_
  rw [← GlobalTheory.T.kerThetaLocalized_eq_span_fontaineXiElement l e he, ← Ideal.Quotient.eq_zero_iff_mem]
  have h1 : Per.ev l n (algebraMap (Per.AinfP l) (Per.BdRp l) x) = Ideal.Quotient.mk _ x :=
    GlobalTheory.RingIface.ev_alg l n x
  rw [← h1, hx, map_zero]

end GlobalTheory.MemLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgebraicWeightSpanTranslatesFactorCommutantStatement
section
open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algebraicWeight_span_translates_factor_commutant : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : AlgWt L n) (ι : Type) [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℂ a.W) (P : ι → ι → MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ), Agrees a b P → ∀ (τ : L →+* ℂ) (v : ι → ℂ), v ≠ 0 → ∀ w : ι → ℂ, w ∈ Submodule.span ℂ {x | ∃ (B : GL (Fin n) ℂ) (M : Matrix ι ι ℂ), (∀ A : GL (Fin n) ℂ, M * evM P (evPt τ A) = evM P (evPt τ A) * M) ∧ x = evM P (evPt τ B) *ᵥ (M *ᵥ v)} := by
  first | exact @GlobalTheory.AlgWtHW.span_tau_commutant | exact GlobalTheory.AlgWtHW.span_tau_commutant | (intros; apply GlobalTheory.AlgWtHW.span_tau_commutant <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AxSenTateComplexPadicFixedClosureStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ax_sen_tate_complex_padic_fixed_closure : ∀ (l : ℕ) [Fact l.Prime], ∀ (H : Subgroup (GQ l)) (x : ℂ_[l]), (∀ g ∈ H, Per.σC g x = x) → x ∈ closure ((fun y : Om l => (y : ℂ_[l])) '' {y | ∀ g ∈ H, g y = y}) := by
  first | exact @GlobalTheory.MemLoc.ax_sen_tate | exact GlobalTheory.MemLoc.ax_sen_tate | (intros; apply GlobalTheory.MemLoc.ax_sen_tate <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BdRPlusFiltrationEqFontaineXiPow
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc.FilPrincipal

section General
variable {R : Type} [CommRing R] {I : Ideal R} {a : R}

theorem evalₐ_eq_zero_iff (h : I = Ideal.span {a}) (n : ℕ) (y : AdicCompletion I R) :
    AdicCompletion.evalₐ I n y = 0 ↔ algebraMap R (AdicCompletion I R) a ^ n ∣ y := by
  have hfg : I.FG := ⟨{a}, by simp [h]⟩
  have e : (I ^ n).map (algebraMap R (AdicCompletion I R)) =
      Ideal.span {algebraMap R (AdicCompletion I R) a ^ n} := by
    have : I ^ n = Ideal.span {a ^ n} := by rw [h, Ideal.span_singleton_pow]
    rw [this, Ideal.map_span, Set.image_singleton, map_pow]
  rw [← Ideal.mem_span_singleton, ← e, ← Submodule.restrictScalars_mem R,
    ← Ideal.smul_top_eq_map, AdicCompletion.pow_smul_top_eq_ker_eval hfg, LinearMap.mem_ker]
  have h' : (I ^ n • ⊤ : Ideal R) = I ^ n := by ext x; simp
  exact map_eq_zero_iff _ (Ideal.quotientEquivAlgOfEq R h').injective

theorem evalₐ_algebraMap (n : ℕ) (r : R) :
    AdicCompletion.evalₐ I n (algebraMap R (AdicCompletion I R) r) = Ideal.Quotient.mk _ r := by
  rw [AlgHom.commutes]; rfl

theorem evalₐ_surj (n : ℕ) : Function.Surjective (AdicCompletion.evalₐ I n) := by
  intro x
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact ⟨_, evalₐ_algebraMap n r⟩

theorem regular_of_isDomain [IsDomain R] (h : I = Ideal.span {a}) (ha : a ≠ 0) (y : AdicCompletion I R)
    (hy : algebraMap R (AdicCompletion I R) a * y = 0) : y = 0 := by
  refine AdicCompletion.ext_evalₐ fun n => ?_
  rw [map_zero, evalₐ_eq_zero_iff h]
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I (n + 1) y)
  have h1 : algebraMap R (AdicCompletion I R) a ^ (n + 1) ∣ y - algebraMap R _ r := by
    rw [← evalₐ_eq_zero_iff h, map_sub, evalₐ_algebraMap, hr, sub_self]
  have h2 := congrArg (AdicCompletion.evalₐ I (n + 1)) hy
  rw [map_mul, map_zero, evalₐ_algebraMap, ← hr, ← map_mul, Ideal.Quotient.eq_zero_iff_mem] at h2
  have h3 : I ^ (n + 1) = Ideal.span {a ^ (n + 1)} := by rw [h, Ideal.span_singleton_pow]
  rw [h3, Ideal.mem_span_singleton, pow_succ', mul_dvd_mul_iff_left ha] at h2
  have h4 : algebraMap R (AdicCompletion I R) a ^ n ∣ algebraMap R _ r := by
    rw [← map_pow]; exact map_dvd _ h2
  have h5 := dvd_add ((pow_dvd_pow _ (Nat.le_succ n)).trans h1) h4
  rwa [sub_add_cancel] at h5

theorem isAdicComplete_span (h : I = Ideal.span {a}) :
    IsAdicComplete (Ideal.span {algebraMap R (AdicCompletion I R) a}) (AdicCompletion I R) := by
  have hfg : I.FG := ⟨{a}, by simp [h]⟩
  have e : I.map (algebraMap R (AdicCompletion I R)) =
      Ideal.span {algebraMap R (AdicCompletion I R) a} := by
    have : ∀ J : Ideal R, J = Ideal.span {a} → J.map (algebraMap R (AdicCompletion I R)) =
        Ideal.span {algebraMap R (AdicCompletion I R) a} := by
      rintro J rfl
      rw [Ideal.map_span, Set.image_singleton]
    exact this I h
  rw [← e, IsAdicComplete.map_algebraMap_iff]
  exact AdicCompletion.isAdicComplete hfg

end General

theorem xi_ne_zero {l : ℕ} [Fact l.Prime] (e : Per.Fl l) (he : IsEps e) : xi e ≠ 0 := by
  intro h0
  set a := (frobeniusEquiv (Per.Fl l) l).symm e with ha
  have h1 : xi e * (Per.tm a - 1) = Per.tm a ^ l - 1 := geom_sum_mul _ _
  rw [h0, zero_mul, eq_comm, sub_eq_zero, ← map_pow] at h1
  have h2 := congrArg (fun w : Per.Ainf l => w.coeff 0) h1
  simp only [WittVector.teichmuller_coeff_zero, WittVector.one_coeff_zero] at h2
  have h3 : a = 1 := by
    apply (frobeniusEquiv (Per.Fl l) l).injective
    rw [frobeniusEquiv_apply, frobenius_def, h2, map_one]
  apply he.2
  rw [← ha, h3, map_one]

end GlobalTheory.MemLoc.FilPrincipal

open GlobalTheory.MemLoc.FilPrincipal in

theorem GlobalTheory.MemLoc.filtration_eq_xi_pow : ∀ (l : ℕ) [Fact l.Prime], ∀ e : Per.Fl l, IsEps e →
    (∀ (n : ℕ) (y : Per.BdRp l), y ∈ Per.FilP l n ↔ aDp l (xi e) ^ n ∣ y) ∧
    (∀ y : Per.BdRp l, aDp l (xi e) * y = 0 → y = 0) ∧
    IsAdicComplete (Ideal.span {aDp l (xi e)}) (Per.BdRp l) ∧
    (∀ n : ℕ, Function.Surjective (Per.ev l n)) := by
  intro l _ e he
  have hk := GlobalTheory.T.kerThetaLocalized_eq_span_fontaineXiElement l e he
  obtain ⟨-, hd, hinj⟩ := GlobalTheory.T.usage l
  have hne : algebraMap (Per.Ainf l) (Per.AinfP l) (xi e) ≠ 0 := fun h =>
    xi_ne_zero e he (hinj (h.trans (map_zero _).symm))
  obtain ⟨E, hE, hev⟩ := GlobalTheory.RingIface.exists_bdRp_equiv l
  have ha : E (aDp l (xi e)) = algebraMap (Per.AinfP l) (AdicCompletion (Per.kerP l) (Per.AinfP l))
      (algebraMap (Per.Ainf l) (Per.AinfP l) (xi e)) := by
    rw [aDp, RingHom.comp_apply, hE]
  refine ⟨fun n y => ?_, fun y hy => ?_, ?_, fun n => GlobalTheory.RingIface.ev_surj l n⟩
  · rw [GlobalTheory.RingIface.mem_filtration_iff_mem_kerTheta_pow, ← hev, evalₐ_eq_zero_iff hk n (E y), ← ha, ← map_pow]
    exact map_dvd_iff E
  · have h1 := congrArg E hy
    rw [map_mul, map_zero, ha] at h1
    exact E.injective ((regular_of_isDomain hk hne (E y) h1).trans (map_zero E).symm)
  · rw [← IsAdicComplete.congr_ringEquiv _ E, Ideal.map_span, Set.image_singleton, ha]
    exact isAdicComplete_span hk
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BdRPlusSimpleRootsSectionUniqueEquivariantStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bdRPlus_simple_roots_section_unique_equivariant : ∀ (l : ℕ) [Fact l.Prime], ∀ o : Om l →+* Per.BdRp l, IsSec o → (∀ (x : Om l) (y : Per.BdRp l) (f : Polynomial (Om l)), Per.θD l y = (x : ℂ_[l]) → f.eval x = 0 → f.derivative.eval x ≠ 0 → (f.map o).eval y = 0 → y = o x) ∧ (∀ o' : Om l →+* Per.BdRp l, IsSec o' → o' = o) ∧ ∀ (g : Per.Gq l) (x : Om l), Per.σDp g (o x) = o (g x) := by
  first | exact @GlobalTheory.MemLoc.SecUniq.main | exact GlobalTheory.MemLoc.SecUniq.main | (intros; apply GlobalTheory.MemLoc.SecUniq.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CentralGroupAlgebraOpPreservesIntegralLevelForms
section
set_option autoImplicit false

noncomputable section

open NumberField
open scoped Matrix ComplexOrder

namespace GlobalTheory.CentralLevelOp

open Formalism.DivisionValues Formalism.L2.DIV

theorem lvlOp_mem_lvlNab : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (v0 : NumberField.InfinitePlace K), Formalism.DivisionValues.IsConjAt v0 →
    ∀ (S : Formalism.L2.DIV.CSD K), (S.H.map v0.embedding).PosDef →
    ∀ (G : Type) [Group G] [Fintype G] (r : Representation K G S.Forms), S.ActGood r →
    ∀ (P : Subgroup G) (ψ : P →* Kˣ) (a : MonoidAlgebra K G), (∀ b, a * b = b * a) → (∀ t : G, ∃ n : ℤ, a.coeff t = n) →
    ∀ x ∈ S.lvlNab r P ψ, (S.lvlOp r P ψ a).mulVec x ∈ S.lvlNab r P ψ := by
  intro K _ _ _ v0 h0 S hH G _ _ r hr P ψ a hc hz x hx
  have hE := (level_operator_spec K v0 h0 S hH G r hr P ψ a (hc _)).1
  change (S.lvlE r P ψ).mulVec x ∈ S.nabLat at hx
  change (S.lvlE r P ψ).mulVec ((S.lvlOp r P ψ a).mulVec x) ∈ S.nabLat
  rw [Matrix.mulVec_mulVec, hE, ← Matrix.mulVec_mulVec, CSD.gaMat, Matrix.sum_mulVec]
  refine Submodule.sum_mem _ fun t _ => ?_
  obtain ⟨n, hn⟩ := hz t
  rw [Matrix.smul_mulVec, hn, Int.cast_smul_eq_zsmul]
  exact Submodule.smul_of_tower_mem _ n ((action_preserves_lattice K S G r hr t).1 _ hx)

end GlobalTheory.CentralLevelOp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CentralIdempotentEqSumCharacterIdempotentsStatement
section
open Formalism.L2.DIV
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.centralIdempotent_eq_sum_character_idempotents : ∀ {G : Type} [inst : Group G] [inst_1 : Fintype G] [inst_2 : DecidableEq G] (A : Finset (G → ℂ)) (e : MonoidAlgebra ℂ G), (∀ ψ ∈ A, ψ 1 ≠ 0) → (∀ g : G, ∑ ψ ∈ A, ψ 1 * ψ g = if g = 1 then (Fintype.card G : ℂ) else 0) → (∀ ψ ∈ A, ∀ x : G, ψ 1 * ∑ g, e.coeff g * ψ (g * x) = (∑ g, e.coeff g * ψ g) * ψ x) → e * e = e → e = idemOf (A.filter fun ψ => ∑ g, e.coeff g * ψ g = ψ 1) := by
  first | exact @GlobalTheory.IdemExpand.eq_idemOf_filter | exact GlobalTheory.IdemExpand.eq_idemOf_filter | (intros; apply GlobalTheory.IdemExpand.eq_idemOf_filter <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClassFunctionActsByScalarOnIrrCharStatement
section
open Formalism.L2.DIV
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.classFunction_acts_by_scalar_on_irrChar : ∀ {G : Type} [inst : Group G] [inst_1 : Fintype G] (e : MonoidAlgebra ℂ G), (∀ x y : G, e.coeff (y * x * y⁻¹) = e.coeff x) → ∀ (ψ : G → ℂ), ψ ∈ Formalism.L2.Col.gxIrrSet (G := G) ℂ → ∀ x : G, ψ 1 * ∑ g, e.coeff g * ψ (g * x) = (∑ g, e.coeff g * ψ g) * ψ x := by
  first | exact @GlobalTheory.classFun_char_scalar | exact GlobalTheory.classFun_char_scalar | (intros; apply GlobalTheory.classFun_char_scalar <;> assumption)
end

