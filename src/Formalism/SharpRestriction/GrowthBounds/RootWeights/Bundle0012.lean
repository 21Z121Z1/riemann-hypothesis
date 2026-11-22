import Formalism.SharpRestriction.GrowthBounds.RootWeights.TwistSubEqMatrixSubst
import Formalism.SharpRestriction.GrowthBounds.RootWeights.GenericMatrixEvaluationDet
import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle0011
import Formalism.SharpRestriction.GrowthBounds.RootWeights.ValuationNonnegIffIntegral
import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle0007
import Formalism.SharpRestriction.GrowthBounds.RootWeights.LagrangeProjectorPreservesStable
import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle0005
import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle0010

-- bundled from Formalism.SharpRestriction.GrowthBounds.RootWeights.BinomialStableContainsComponents
section
noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

def genericMatrixRootWeights (R : Type*) [CommRing R] (n : ℕ) : Matrix (Fin n) (Fin n) (GLCoord R n) :=
  (genMat R n).map fun x => algebraMap _ (GLCoord R n) x

def genericMatrixInverse (R : Type*) [CommRing R] (n : ℕ) : Matrix (Fin n) (Fin n) (GLCoord R n) :=
  ((genMat R n).adjugate).map fun x =>
    IsLocalization.Away.invSelf (genMat R n).det * algebraMap _ (GLCoord R n) x

def coefficientMap (R : Type*) [CommRing R] (n : ℕ) : R →+* GLCoord R n :=
  (algebraMap (MvPolynomial (Fin n × Fin n) R) (GLCoord R n)).comp MvPolynomial.C

def genericTranslate {R : Type*} [CommRing R] {ι : Type*} {n : ℕ} (LL : Letters ι) (S : Set ι)
    (G : MvPolynomial (ι × Fin n) R) : MvPolynomial (ι × Fin n) (GLCoord R n) :=
  matrixSubst LL S (coefficientMap R n) (genericMatrixInverse R n) (genericMatrixRootWeights R n) G

open Classical in

def weightComponent {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] {n : ℕ} (LL : Letters ι) (S : Set ι)
    (nu : Fin n → ℤ) (F : MvPolynomial (ι × Fin n) R) : MvPolynomial (ι × Fin n) R :=
  ∑ m ∈ F.support.filter (fun m => wtS LL S m = nu), monomial m (F.coeff m)

def TorusActsThroughWeight : Prop :=
  ∀ (R B : Type) [CommRing R] [CommRing B] (ι : Type) [Fintype ι] (LL : Letters ι) (n : ℕ) (S : Set ι)
    (φ : R →+* B) (D : Fin n → Bˣ) (m : ι × Fin n →₀ ℕ) (c : R),
      matrixSubst LL S φ (Matrix.diagonal fun a => ((D a : Bˣ) : B)) (Matrix.diagonal fun a => (((D a)⁻¹ : Bˣ) : B))
        (monomial m c) = monomial m (φ c * ((∏ a, D a ^ (wtS LL S m a) : Bˣ) : B))

def BinomialStableContainsComponents : Prop :=
  ∀ (R : Type) [CommRing R] (ι : Type) [Fintype ι] (LL : Letters ι) (n : ℕ) (S : Set ι)
    (W : Submodule R (MvPolynomial (ι × Fin n) R)), (∀ a k, ∀ x ∈ W, binomPol R LL S a k x ∈ W) →
    ∀ x ∈ W, ∀ nu, weightComponent LL S nu x ∈ W

def TwistExponentsAreWeightEntries : Prop :=
  ∀ (R : Type) [Field R] (ι : Type) [Fintype ι] (LL : Letters ι) (n : ℕ) (S : Set ι) (j : Fin n)
    (G : MvPolynomial (ι × Fin n) R),
      sDegs LL S j G = (genericTranslate LL S G).support.image (fun m => wtS LL S m j)

def GenericMonomialsSpecialise : Prop :=
  ∀ (R : Type) [Field R] (ι : Type) [Fintype ι] (LL : Letters ι) (n : ℕ) (S : Set ι)
    (k1 : Type) [CommRing k1] (φ : R →+* k1) (g0 g0inv : Matrix (Fin n) (Fin n) k1), g0 * g0inv = 1 →
    ∀ G : MvPolynomial (ι × Fin n) R, (matrixSubst LL S φ g0inv g0 G).support ⊆ (genericTranslate LL S G).support

end Formalism.MainNotions.G.GLWeightTheory
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.RootWeights.ExistsHighestCoordinateFunctional
section
noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

section hw

variable {n : ℕ} {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {V : Type*} [AddCommGroup V] [Module (KK O) V] [Module O V] [IsScalarTower O (KK O) V]

def weightHeightAscending (nu : Fin n → ℤ) : ℤ := ∑ c : Fin n, ((c : ℕ) : ℤ) * nu c

theorem weightHeightAscending_add_root (nu : Fin n → ℤ) (a b : Fin n) :
    weightHeightAscending (nu + rootW a b) = weightHeightAscending nu + (((a : ℕ) : ℤ) - ((b : ℕ) : ℤ)) := by
  unfold weightHeightAscending rootW
  simp only [Pi.add_apply, Pi.sub_apply, mul_add, mul_sub, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]

theorem irreducible_lowering_word_weight [NeZero n] {E : GLOps n (KK O) V} {lam : Fin n → ℤ} {v : V} (hI : IsIrrHW E lam v)
    {u : Module.End (KK O) V} (hu : u ∈ loweringOperatorMonoid E) :
    ∃ nu, u v ∈ weightSp E nu ∧ ((nu = lam ∧ u v = v) ∨ weightHeightAscending lam < weightHeightAscending nu) ∧
      nu 0 ≤ lam 0 ∧ lam (lastIdx n) ≤ nu (lastIdx n) := by
  have hE : IsGLRep E := hI.1
  have hv : v ∈ weightSp E lam := hI.2.2.1.2.1
  unfold loweringOperatorMonoid at hu
  induction hu using Submonoid.closure_induction_left with
  | one => exact ⟨lam, hv, Or.inl ⟨rfl, rfl⟩, le_rfl, le_rfl⟩
  | mul_left g hg w _ ih =>
    obtain ⟨a, b, hba, rfl⟩ := hg
    obtain ⟨nu, hnu, hor, h0, hl⟩ := ih
    refine ⟨nu + rootW a b, gl_rep_operator_weight_shift hE hnu a b, Or.inr ?_, ?_, ?_⟩
    · have hab : ((b : ℕ) : ℤ) < ((a : ℕ) : ℤ) := by exact_mod_cast hba
      rw [weightHeightAscending_add_root]
      rcases hor with ⟨rfl, -⟩ | h
      · linarith
      · linarith
    · have ha0 : a ≠ 0 := by
        intro h; rw [h] at hba; exact absurd hba (Fin.not_lt_zero _)
      have : (nu + rootW a b) 0 ≤ nu 0 := by
        simp only [rootW, Pi.add_apply, Pi.sub_apply, Pi.single_apply, if_neg (Ne.symm ha0)]
        split_ifs <;> omega
      exact this.trans h0
    · have hbl : b ≠ lastIdx n := by
        intro h
        have : (a : ℕ) ≤ n - 1 := Nat.le_sub_one_of_lt a.isLt
        have hb : (b : ℕ) = n - 1 := by rw [h]; rfl
        have : (b : ℕ) < (a : ℕ) := hba
        omega
      have : nu (lastIdx n) ≤ (nu + rootW a b) (lastIdx n) := by
        simp only [rootW, Pi.add_apply, Pi.sub_apply, Pi.single_apply, if_neg (Ne.symm hbl)]
        split_ifs <;> omega
      exact hl.trans this

theorem top_le_line_sup_higher_weights [NeZero n] {E : GLOps n (KK O) V} {lam : Fin n → ℤ} {v : V} (hI : IsIrrHW E lam v) :
    (⊤ : Submodule (KK O) V) ≤ Submodule.span (KK O) {v} ⊔ ⨆ nu, ⨆ (_ : weightHeightAscending lam < weightHeightAscending nu), weightSp E nu := by
  rw [← irreducible_lowering_span_top hI, Submodule.span_le]
  rintro x ⟨u, hu, rfl⟩
  obtain ⟨nu, hnu, h1 | h1, -⟩ := irreducible_lowering_word_weight hI hu
  · rw [h1.2]
    exact Submodule.mem_sup_left (Submodule.mem_span_singleton_self v)
  · exact Submodule.mem_sup_right (Submodule.mem_iSup_of_mem nu (Submodule.mem_iSup_of_mem h1 hnu))

theorem top_le_end_bounded_weights [NeZero n] {E : GLOps n (KK O) V} {lam : Fin n → ℤ} {v : V} (hI : IsIrrHW E lam v) :
    (⊤ : Submodule (KK O) V) ≤ ⨆ nu, ⨆ (_ : nu 0 ≤ lam 0 ∧ lam (lastIdx n) ≤ nu (lastIdx n)), weightSp E nu := by
  rw [← irreducible_lowering_span_top hI, Submodule.span_le]
  rintro x ⟨u, hu, rfl⟩
  obtain ⟨nu, hnu, -, h0, hl⟩ := irreducible_lowering_word_weight hI hu
  exact Submodule.mem_iSup_of_mem nu (Submodule.mem_iSup_of_mem ⟨h0, hl⟩ hnu)

theorem irreducible_weight_end_bounds [NeZero n] [CharZero (KK O)] {E : GLOps n (KK O) V} {lam : Fin n → ℤ} {v : V}
    (hI : IsIrrHW E lam v) {nu : Fin n → ℤ} {x : V} (hx : x ∈ weightSp E nu) (h0 : x ≠ 0) :
    nu 0 ≤ lam 0 ∧ lam (lastIdx n) ≤ nu (lastIdx n) := by
  by_contra hn
  exact h0 (weight_support_sum_eq_zero E (fun mu => mu 0 ≤ lam 0 ∧ lam (lastIdx n) ≤ mu (lastIdx n)) hx
    (top_le_end_bounded_weights hI Submodule.mem_top) hn)

theorem irreducible_highest_weight_line [NeZero n] [CharZero (KK O)] {E : GLOps n (KK O) V} {lam : Fin n → ℤ} {v : V}
    (hI : IsIrrHW E lam v) {x : V} (hx : x ∈ weightSp E lam) : ∃ c : KK O, x = c • v := by
  have hx2 := top_le_line_sup_higher_weights hI (Submodule.mem_top (x := x))
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx2
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
  have hv : v ∈ weightSp E lam := hI.2.2.1.2.1
  have hzw : z ∈ weightSp E lam := by
    have e : z = (c • v + z) - c • v := by abel
    rw [e]
    exact Submodule.sub_mem _ hx (Submodule.smul_mem _ c hv)
  have hz0 : z = 0 := weight_support_sum_eq_zero E (fun nu => weightHeightAscending lam < weightHeightAscending nu) hzw hz (lt_irrefl _)
  exact ⟨c, by rw [hz0, add_zero]⟩

theorem highest_line_isCompl_other_weights [NeZero n] [CharZero (KK O)] {E : GLOps n (KK O) V} {lam : Fin n → ℤ} {v : V}
    (hI : IsIrrHW E lam v) : IsCompl (Submodule.span (KK O) {v}) (otherWts E lam) := by
  constructor
  · rw [Submodule.disjoint_def]
    intro x hx hx2
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
    exact weight_support_sum_eq_zero E (fun mu => mu ∈ {mu | mu ≠ lam}) (Submodule.smul_mem _ c hI.2.2.1.2.1) hx2
      (fun h => h rfl)
  · rw [codisjoint_iff, eq_top_iff, ← hI.1.2.2, iSup_le_iff]
    intro mu x hx
    by_cases h : mu = lam
    · subst h
      obtain ⟨c, rfl⟩ := irreducible_highest_weight_line hI hx
      exact Submodule.mem_sup_left (Submodule.smul_mem _ c (Submodule.mem_span_singleton_self v))
    · apply Submodule.mem_sup_right
      show x ∈ ⨆ mu ∈ {mu | mu ≠ lam}, weightSp E mu
      exact Submodule.mem_iSup_of_mem mu (Submodule.mem_iSup_of_mem h hx)

theorem exists_highest_coordinate_functional [NeZero n] [CharZero (KK O)] {E : GLOps n (KK O) V} {lam : Fin n → ℤ} {v : V}
    (hI : IsIrrHW E lam v) : ∃ xi : V →ₗ[KK O] KK O, xi v = 1 ∧ (∀ w ∈ otherWts E lam, xi w = 0) ∧
      ∀ x, x - xi x • v ∈ otherWts E lam := by
  have hc := highest_line_isCompl_other_weights hI
  have hv0 : v ≠ 0 := hI.2.2.1.1
  let P := Submodule.linearProjOfIsCompl _ _ hc
  let e := LinearEquiv.toSpanNonzeroSingleton (KK O) V v hv0
  refine ⟨e.symm.toLinearMap ∘ₗ P, ?_, ?_, ?_⟩
  · have h1 : P v = ⟨v, Submodule.mem_span_singleton_self v⟩ :=
      Submodule.linearProjOfIsCompl_apply_left hc ⟨v, Submodule.mem_span_singleton_self v⟩
    show e.symm (P v) = 1
    rw [h1, LinearEquiv.symm_apply_eq, LinearEquiv.toSpanNonzeroSingleton_one]
  · intro w hw
    have h2 : P w = 0 := Submodule.linearProjOfIsCompl_apply_right hc ⟨w, hw⟩
    show e.symm (P w) = 0
    rw [h2, map_zero]
  · intro x
    have h8 : ∀ s : KK O, ((e s : Submodule.span (KK O) {v}) : V) = s • v := fun s => by
      first
        | rfl
        | simp [e, LinearEquiv.toSpanNonzeroSingleton_apply]
    have h3 : (e.symm (P x)) • v = (P x : V) := by
      rw [← h8, LinearEquiv.apply_symm_apply]
    show x - (e.symm (P x)) • v ∈ otherWts E lam
    rw [h3]
    have hPP : P (P x : V) = P x := Submodule.linearProjOfIsCompl_apply_left hc (P x)
    have h5 : P (x - (P x : V)) = 0 := by
      rw [map_sub, hPP, sub_self]
    have h6 := LinearMap.mem_ker.mpr h5
    have h7 := Submodule.linearProjOfIsCompl_ker hc
    rw [SetLike.ext_iff] at h7
    exact (h7 _).mp h6

end hw

end Formalism.MainNotions.G.GLWeightTheory
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.RootWeights.IntegralPolyLinearMapClosed
section
noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

def halfFactorialValuation (p : ℕ) {σ : Type} (m : σ →₀ ℕ) : WithTop ℚ := (((padicValNat p (expFact m) : ℚ) / 2 : ℚ) : WithTop ℚ)

theorem mem_fock_lattice_iff_coeff {p : ℕ} (hV : ValuationProperties p O) {σ : Type} (F : MvPolynomial σ (KK O)) :
    InBB (O := O) p F ↔ ∀ m, 0 ≤ vK p (F.coeff m) + halfFactorialValuation p m := by
  obtain ⟨hV0, -, -, -, -, -⟩ := id hV
  rw [InBB, vBB, Finset.le_inf_iff]
  constructor
  · intro h m
    by_cases hm : m ∈ F.support
    · exact h m hm
    · rw [MvPolynomial.notMem_support_iff.1 hm, hV0, top_add]
      exact le_top
  · intro h m _
    exact h m

theorem fock_lattice_zero_mem {p : ℕ} (hV : ValuationProperties p O) {σ : Type} : InBB (O := O) p (0 : MvPolynomial σ (KK O)) := by
  obtain ⟨hV0, -, -, -, -, -⟩ := id hV
  refine (mem_fock_lattice_iff_coeff hV 0).2 fun m => ?_
  rw [coeff_zero, hV0, top_add]
  exact le_top

theorem fock_lattice_add_mem {p : ℕ} (hV : ValuationProperties p O) {σ : Type} {F G : MvPolynomial σ (KK O)}
    (hF : InBB (O := O) p F) (hG : InBB (O := O) p G) : InBB (O := O) p (F + G) := by
  obtain ⟨-, -, hVadd, -, -, -⟩ := id hV
  rw [mem_fock_lattice_iff_coeff hV] at hF hG ⊢
  intro m
  rw [coeff_add]
  calc (0 : WithTop ℚ)
      ≤ min (vK p (F.coeff m) + halfFactorialValuation p m) (vK p (G.coeff m) + halfFactorialValuation p m) := le_min (hF m) (hG m)
    _ = min (vK p (F.coeff m)) (vK p (G.coeff m)) + halfFactorialValuation p m := min_add_add_right _ _ _
    _ ≤ vK p (F.coeff m + G.coeff m) + halfFactorialValuation p m := add_le_add_left (hVadd _ _) _

theorem fock_lattice_sum_mem {p : ℕ} (hV : ValuationProperties p O) {σ α : Type} (s : Finset α) (f : α → MvPolynomial σ (KK O))
    (h : ∀ i ∈ s, InBB (O := O) p (f i)) : InBB (O := O) p (∑ i ∈ s, f i) := by
  exact Finset.sum_induction f (InBB (O := O) p) (fun _ _ => fock_lattice_add_mem hV) (fock_lattice_zero_mem hV) h

theorem fock_lattice_smul_mem {p : ℕ} (hV : ValuationProperties p O) {σ : Type} (o : O) {F : MvPolynomial σ (KK O)}
    (hF : InBB (O := O) p F) : InBB (O := O) p (o • F) := by
  obtain ⟨-, hVmul, -, -, -, hVint⟩ := id hV
  rw [mem_fock_lattice_iff_coeff hV] at hF ⊢
  intro m
  rw [coeff_smul, Algebra.smul_def, hVmul]
  have ho : 0 ≤ vK p (algebraMap O (KK O) o) := (hVint _).2 ⟨o, rfl⟩
  calc (0 : WithTop ℚ) ≤ vK p (F.coeff m) + halfFactorialValuation p m := hF m
    _ ≤ vK p (algebraMap O (KK O) o) + vK p (F.coeff m) + halfFactorialValuation p m :=
        add_le_add_left (le_add_of_nonneg_left ho) _

theorem fock_lattice_monomial_iff {p : ℕ} (hV : ValuationProperties p O) {σ : Type} (m : σ →₀ ℕ) (c : KK O) :
    InBB (O := O) p (monomial m c) ↔ 0 ≤ vK p c + halfFactorialValuation p m := by
  classical
  obtain ⟨hV0, -, -, -, -, -⟩ := id hV
  rw [mem_fock_lattice_iff_coeff hV]
  constructor
  · intro h
    have hm := h m
    rwa [coeff_monomial, if_pos rfl] at hm
  · intro h m'
    rw [coeff_monomial]
    split_ifs with hm
    · rw [← hm]
      exact h
    · rw [hV0, top_add]
      exact le_top

theorem fock_lattice_iff_monomials {p : ℕ} (hV : ValuationProperties p O) {σ : Type} (F : MvPolynomial σ (KK O)) :
    InBB (O := O) p F ↔ ∀ m, InBB (O := O) p (monomial m (F.coeff m)) := by
  rw [mem_fock_lattice_iff_coeff hV]
  exact forall_congr' fun m => (fock_lattice_monomial_iff hV m _).symm

theorem fock_lattice_linear_map_closed {p : ℕ} (hV : ValuationProperties p O) {σ : Type}
    (u : MvPolynomial σ (KK O) →ₗ[KK O] MvPolynomial σ (KK O))
    (h : ∀ m c, InBB (O := O) p (monomial m c) → InBB (O := O) p (u (monomial m c)))
    (F : MvPolynomial σ (KK O)) (hF : InBB (O := O) p F) : InBB (O := O) p (u F) := by
  rw [← F.support_sum_monomial_coeff, map_sum]
  exact fock_lattice_sum_mem hV _ _ fun m _ => h m _ ((fock_lattice_iff_monomials hV F).1 hF m)

theorem valuation_intCast_padicVal {p : ℕ} (hV : ValuationProperties p O) (z : ℤ) (hz : z ≠ 0) :
    vK p (z : KK O) = ((padicValInt p z : ℚ) : WithTop ℚ) := by
  obtain ⟨-, -, -, hVnat, hVneg, -⟩ := id hV
  have hn : z.natAbs ≠ 0 := Int.natAbs_ne_zero.2 hz
  have e : padicValInt p z = padicValNat p z.natAbs := rfl
  rw [e]
  rcases Int.natAbs_eq z with h | h
  · conv_lhs => rw [h]
    rw [Int.cast_natCast]
    exact hVnat _ hn
  · conv_lhs => rw [h]
    rw [Int.cast_neg, Int.cast_natCast, hVneg]
    exact hVnat _ hn

theorem fock_lattice_monomial_rescale {p : ℕ} (hV : ValuationProperties p O) {σ : Type} (m m' : σ →₀ ℕ) (c : KK O) (z : ℤ)
    (h : InBB (O := O) p (monomial m c))
    (hz : z = 0 ∨ padicValNat p (expFact m) ≤ 2 * padicValInt p z + padicValNat p (expFact m')) :
    InBB (O := O) p (monomial m' (c * (z : KK O))) := by
  obtain ⟨hV0, hVmul, -, -, -, -⟩ := id hV
  rw [fock_lattice_monomial_iff hV] at h ⊢
  by_cases hz0 : z = 0
  · rw [hz0, Int.cast_zero, mul_zero, hV0, top_add]
    exact le_top
  have hz' : padicValNat p (expFact m) ≤ 2 * padicValInt p z + padicValNat p (expFact m') :=
    hz.resolve_left hz0
  rw [hVmul, valuation_intCast_padicVal hV z hz0]
  have hq : ((padicValNat p (expFact m) : ℚ) / 2) ≤
      (padicValInt p z : ℚ) + (padicValNat p (expFact m') : ℚ) / 2 := by
    have : (padicValNat p (expFact m) : ℚ) ≤ 2 * (padicValInt p z : ℚ) + padicValNat p (expFact m') := by
      exact_mod_cast hz'
    linarith
  have hw : halfFactorialValuation p m ≤ ((padicValInt p z : ℚ) : WithTop ℚ) + halfFactorialValuation p m' := by
    simp only [halfFactorialValuation]
    rw [← WithTop.coe_add]
    exact WithTop.coe_le_coe.2 hq
  calc (0 : WithTop ℚ) ≤ vK p c + halfFactorialValuation p m := h
    _ ≤ vK p c + (((padicValInt p z : ℚ) : WithTop ℚ) + halfFactorialValuation p m') := add_le_add_right hw _
    _ = vK p c + ((padicValInt p z : ℚ) : WithTop ℚ) + halfFactorialValuation p m' := (add_assoc _ _ _).symm

theorem mem_integral_poly_iff_map {σ : Type} (F : MvPolynomial σ (KK O)) :
    F ∈ IntPol O σ ↔ ∃ F0 : MvPolynomial σ O, MvPolynomial.map (algebraMap O (KK O)) F0 = F := by
  simp only [IntPol, LinearMap.mem_range, AlgHom.toLinearMap_apply]
  rfl

theorem mem_integral_poly_iff_coeff {σ : Type} (F : MvPolynomial σ (KK O)) :
    F ∈ IntPol O σ ↔ ∀ m, ∃ o : O, F.coeff m = algebraMap O (KK O) o := by
  rw [mem_integral_poly_iff_map]
  constructor
  · rintro ⟨F0, rfl⟩ m
    exact ⟨F0.coeff m, coeff_map _ _ _⟩
  · intro h
    choose g hg using h
    refine ⟨∑ m ∈ F.support, monomial m (g m), ?_⟩
    rw [map_sum]
    conv_rhs => rw [← F.support_sum_monomial_coeff]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [map_monomial, hg]

theorem integer_monomial_mem_integral {σ : Type} (m : σ →₀ ℕ) (z : ℤ) : monomial m (z : KK O) ∈ IntPol O σ := by
  exact (mem_integral_poly_iff_map _).2 ⟨monomial m (z : O), by rw [map_monomial, map_intCast]⟩

theorem integral_poly_linear_map_closed {σ : Type} (u : MvPolynomial σ (KK O) →ₗ[KK O] MvPolynomial σ (KK O))
    (h : ∀ m, u (monomial m 1) ∈ IntPol O σ) (F : MvPolynomial σ (KK O)) (hF : F ∈ IntPol O σ) :
    u F ∈ IntPol O σ := by
  choose g hg using (mem_integral_poly_iff_coeff F).1 hF
  rw [← F.support_sum_monomial_coeff, map_sum]
  refine Submodule.sum_mem _ fun m _ => ?_
  have e : monomial m (F.coeff m) = (algebraMap O (KK O) (g m)) • monomial m (1 : KK O) := by
    rw [smul_monomial, smul_eq_mul, mul_one, hg]
  rw [e, map_smul, algebraMap_smul]
  exact Submodule.smul_mem _ _ (h m)

theorem fock_lattice_closure_holds {p : ℕ} (hV : ValuationProperties p O) : FockLatticeClosure p O :=
  fun _ => ⟨fock_lattice_zero_mem hV, fun _ _ => fock_lattice_add_mem hV, fun o _ => fock_lattice_smul_mem hV o,
  fun m c => fock_lattice_monomial_iff hV m c, fock_lattice_iff_monomials hV, fun u h F hF => fock_lattice_linear_map_closed hV u h F hF,
  fun m m' c z h hz => fock_lattice_monomial_rescale hV m m' c z h hz, fun u h F hF => integral_poly_linear_map_closed u h F hF,
  fun m z => integer_monomial_mem_integral m z, mem_integral_poly_iff_coeff⟩

end Formalism.MainNotions.G.GLWeightTheory
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.RootWeights.IsotypicLatticeCorollary
section
namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

theorem isotypic_lattice_corollary (D : Formalism.BasicNotions.D7) (h2 : adm2 D) (h12 : NablaDeltaComparisonField D) : TranslateCorollaryField D :=
  isotypic_lattice_of_five_parts D (isotypic_projector_fixed_mem D h2) hwv_generated_multiple_of_hwv dual_lattice_values_mem_scaled lattice_inter_subspace_basis (generated_lattice_corollary_of_thm D h12 hwv_generated_multiple_of_hwv)

end Formalism.MainNotions.G.GLWeightTheory
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.RootWeights.PolynomialIsotypicLatticeOfParts
section
noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

theorem operator_list_lattice_scaling {O : Type} [CommRing O] [IsDomain O] {σ : Type} (p : ℕ)
    (L : Submodule O (MvPolynomial σ (KK O))) (W : Submodule (KK O) (MvPolynomial σ (KK O)))
    (l : List (Module.End (KK O) (MvPolynomial σ (KK O)) × ℕ))
    (hW : ∀ eD ∈ l, ∀ F ∈ W, eD.1 F ∈ W)
    (hL : ∀ eD ∈ l, ∀ F ∈ W, F ∈ L → ((p : KK O) ^ eD.2) • eD.1 F ∈ L) :
    ∀ F ∈ W, F ∈ L → (l.map Prod.fst).prod F ∈ W ∧
      ((p : KK O) ^ (l.map Prod.snd).sum) • (l.map Prod.fst).prod F ∈ L := by
  induction l with
  | nil =>
    intro F hF hFL
    simp [hF, hFL]
  | cons eD l ih =>
    intro F hF hFL
    have hW' : ∀ e ∈ l, ∀ F ∈ W, e.1 F ∈ W := fun e he => hW e (List.mem_cons_of_mem _ he)
    have hL' : ∀ e ∈ l, ∀ F ∈ W, F ∈ L → ((p : KK O) ^ e.2) • e.1 F ∈ L :=
      fun e he => hL e (List.mem_cons_of_mem _ he)
    obtain ⟨h1, h2⟩ := ih hW' hL' F hF hFL
    simp only [List.map_cons, List.prod_cons, List.sum_cons]
    refine ⟨hW eD (by simp) _ h1, ?_⟩
    have h3 := hL eD (by simp) _ (W.smul_mem ((p : KK O) ^ (l.map Prod.snd).sum) h1) h2
    rw [map_smul, smul_smul, ← pow_add] at h3
    exact h3

theorem polynomial_isotypic_lattice_of_parts (D : Formalism.BasicNotions.D7) (hCR : CompleteReducibilityIsotypic) (hOrth : ContravariantIsotypicOrthogonal) (hDom : HighestWeightDominant)
    (hRes : SubrepRestrictionRep) (hPol : PolynomialGLRepresentation) (hLat : AdmissibleDVRIntegralFormLatticesStable) (h13 : IsotypicProjectorTheoremField D) : FilteredProjectorCorollaryField D := by
  intro p n' O _ _ _ S0 hG n ι _ LL N Ss hmono
  obtain ⟨hchar, hLat'⟩ := hLat p n' O S0 hG
  obtain ⟨hL1, hL2, BBs, hBB, hL3⟩ := hLat' n ι LL
  refine ⟨fun i => hL1 (Ss i), ?_⟩
  intro ee hee
  obtain ⟨hP1, hP2, hP3, -, -, -, B, hB1, hB2⟩ := hPol (KK O) ι n LL
  have hT : ∀ S : Set ι, (⨆ mu : Fin n → ℤ, isoSub (glOps (KK O) n LL S) mu) = ⊤ :=
    fun S => hCR (KK O) _ n _ (hP1 S)

  have hdis : ∀ i lam (S' : Set ι), Disjoint (Ss i) S' → ∀ a b,
      ee i lam * glOps (KK O) n LL S' a b = glOps (KK O) n LL S' a b * ee i lam := by
    intro i lam S' hS' a b
    refine isotypic_projector_commutes _ (hT (Ss i)) lam _ (hee i lam) _ fun mu x hx => ?_
    exact isotypic_stable_commuting _ _ (fun c d => (hP2 (Ss i) S' hS' c d a b).symm) mu x hx
  have hle : ∀ i j, i ≤ j → ∀ lam a b,
      ee i lam * glOps (KK O) n LL (Ss j) a b = glOps (KK O) n LL (Ss j) a b * ee i lam := by
    intro i j hij lam a b
    rw [hP3 (Ss i) (Ss j) (hmono hij) a b, mul_add, add_mul, hdis i lam _ Set.disjoint_sdiff_right a b]
    congr 1
    exact isotypic_projector_commutes _ (hT (Ss i)) lam _ (hee i lam) _ fun mu x hx => isotypic_stable_gl_operator _ mu a b x hx
  have hcomm' : ∀ i j, i ≤ j → ∀ lam mu, ee i lam * ee j mu = ee j mu * ee i lam := by
    intro i j hij lam mu
    refine (isotypic_projector_commutes _ (hT (Ss j)) mu _ (hee j mu) _ fun nu x hx => ?_).symm
    exact isotypic_stable_commuting _ _ (fun c d => hle i j hij lam c d) nu x hx
  refine ⟨hle, hdis, ?_, ?_, ?_⟩
  · intro i j lam mu
    rcases le_total i j with h | h
    · exact hcomm' i j h lam mu
    · exact (hcomm' j i h mu lam).symm
  · intro i lam F G
    rw [← hB1, ← hB1]
    exact isotypic_projector_selfAdjoint _ (hT (Ss i)) lam _ (hee i lam) B
      (hOrth (KK O) _ n _ (hP1 (Ss i)) B (fun a b x y => hB2 (Ss i) a b x y)) F G
  · intro T d F hF
    have hstep := fun (i : Fin N) (lam : Fin n → ℤ) =>
      isotypic_projector_lattice_scaling D hDom hRes hPol h13 p n' O S0 hG n ι LL (Ss i) d lam (ee i lam) (hee i lam)
    have main : ∀ L : Submodule O (MvPolynomial (ι × Fin n) (KK O)),
        (∀ S : Set ι, ∀ u ∈ UZgens (glOps (KK O) n LL S), ∀ F ∈ L, u F ∈ L) → (latticeMultidegreePart L d).FG →
        MQ (K := KK O) (latticeMultidegreePart L d) = ⊤ → F ∈ L →
        ((p : KK O) ^ (∑ i, N0 n * Nat.log p (2 * degIn d (Ss i) + n - 1))) •
          (∑ t ∈ T, (List.ofFn fun i => ee i (t i)).prod) F ∈ L := by
      intro L hst hFG hMQ hFL
      rw [LinearMap.sum_apply, Finset.smul_sum]
      refine Submodule.sum_mem _ fun t _ => ?_
      have h := operator_list_lattice_scaling p L (Pol (KK O) n d)
        (List.ofFn fun i => (ee i (t i), N0 n * Nat.log p (2 * degIn d (Ss i) + n - 1)))
        (by
          intro eD heD
          obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 heD
          exact (hstep i (t i)).1)
        (by
          intro eD heD
          obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 heD
          exact (hstep i (t i)).2 L (hst (Ss i)) hFG hMQ) F hF hFL
      rw [List.map_ofFn, List.map_ofFn, List.sum_ofFn] at h
      exact h.2
    obtain ⟨h1, h2, h3, h4⟩ := hL3 d
    refine ⟨fun hFL => main _ (fun S u hu => (hL2 S u hu).1) h1 h2 hFL, fun hFB => ?_⟩
    rw [← hBB] at hFB ⊢
    exact main BBs (fun S u hu F hF => (hBB _).2 ((hL2 S u hu).2 F ((hBB _).1 hF))) h3 h4 hFB

end Formalism.MainNotions.G.GLWeightTheory
end
end

