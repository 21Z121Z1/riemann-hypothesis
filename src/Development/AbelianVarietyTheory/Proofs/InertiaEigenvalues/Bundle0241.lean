import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0006
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TracePairingInjectiveEquivariantLevelMap
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.GaloisCohomology.LocalTateDualityK
import Formalism.LocalRingCardinality.DataParams
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0191
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0206
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0222
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0208
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0207
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0218
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0228
import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaOfPow
section
open Polynomial

namespace GlobalTheory.GLq.LabelModel
theorem lift {F : Type} [Field F] {m M : ℕ} (hM : 0 < M) (hm : m ∣ M) {ξ ζ : F} (hξ : IsPrimitiveRoot ξ M)
    (hζ : IsPrimitiveRoot ζ m) : ∃ ξ' : F, IsPrimitiveRoot ξ' M ∧ ξ' ^ (M / m) = ζ := by
  obtain ⟨c, rfl⟩ := hm
  have hm0 : 0 < m := Nat.pos_of_mul_pos_right hM
  haveI : NeZero m := ⟨hm0.ne'⟩
  haveI : NeZero (m * c) := ⟨hM.ne'⟩
  have hη : IsPrimitiveRoot (ξ ^ c) m := hξ.pow hM (mul_comm _ _)
  obtain ⟨a, -, hac, ha⟩ := (hη.isPrimitiveRoot_iff).1 hζ
  obtain ⟨U, hU⟩ := ZMod.unitsMap_surjective (n := m) (m := m * c) (Dvd.intro _ rfl) (ZMod.unitOfCoprime a hac)
  refine ⟨ξ ^ (U : ZMod (m * c)).val, hξ.pow_of_coprime _ (ZMod.val_coe_unit_coprime U), ?_⟩
  rw [Nat.mul_div_cancel_left _ hm0, ← pow_mul, mul_comm, pow_mul, ← ha]
  have h1 : (((U : ZMod (m * c)).val : ℕ) : ZMod m) = (a : ZMod m) := by
    have := congrArg (fun u : (ZMod m)ˣ => (u : ZMod m)) hU
    simpa [ZMod.unitsMap_val] using this
  have h2 := (ZMod.natCast_eq_natCast_iff _ _ _).1 h1
  rw [pow_eq_pow_mod _ hη.pow_eq_one, pow_eq_pow_mod a hη.pow_eq_one, h2]

variable (g : ℕ) [hg : Fact g.Prime]

theorem pos {d : ℕ} (hd : 0 < d) : 0 < g ^ d - 1 :=
  Nat.sub_pos_of_lt (Nat.one_lt_pow hd.ne' hg.out.one_lt)

theorem dv {d e : ℕ} (h : d ∣ e) : g ^ d - 1 ∣ g ^ e - 1 := Nat.pow_sub_one_dvd_pow_sub_one g h

theorem exprim {d : ℕ} (hd : 0 < d) : ∃ ξ : Formalism.CyclotomicNorms.Fbar g, IsPrimitiveRoot ξ (g ^ d - 1) := by
  haveI : NeZero (((g ^ d - 1 : ℕ)) : Formalism.CyclotomicNorms.Fbar g) := ⟨by
    rw [Nat.cast_sub (Nat.one_le_pow _ _ hg.out.pos), Nat.cast_pow, CharP.cast_eq_zero (Formalism.CyclotomicNorms.Fbar g) g, zero_pow hd.ne']
    simp⟩
  haveI : NeZero (g ^ d - 1) := ⟨(pos g hd).ne'⟩
  exact HasEnoughRootsOfUnity.exists_primitiveRoot _ _

theorem chain : ∃ z : ℕ → Formalism.CyclotomicNorms.Fbar g, ∀ n, IsPrimitiveRoot (z n) (g ^ n.factorial - 1) ∧
    z (n+1) ^ ((g ^ (n+1).factorial - 1) / (g ^ n.factorial - 1)) = z n := by
  have step : ∀ n (x : {x : Formalism.CyclotomicNorms.Fbar g // IsPrimitiveRoot x (g ^ n.factorial - 1)}),
      ∃ y : {x : Formalism.CyclotomicNorms.Fbar g // IsPrimitiveRoot x (g ^ (n+1).factorial - 1)},
        y.1 ^ ((g ^ (n+1).factorial - 1) / (g ^ n.factorial - 1)) = x.1 := by
    intro n x
    obtain ⟨ξ, hξ⟩ := exprim g (Nat.factorial_pos (n+1))
    obtain ⟨y, hy, hy'⟩ := lift (pos g (Nat.factorial_pos (n+1))) (dv g (Nat.factorial_dvd_factorial (Nat.le_succ n))) hξ x.2
    exact ⟨⟨y, hy⟩, hy'⟩
  choose f hf using step
  obtain ⟨x0, hx0⟩ := exprim g (Nat.factorial_pos 0)
  let s : ∀ n : ℕ, {x : Formalism.CyclotomicNorms.Fbar g // IsPrimitiveRoot x (g ^ n.factorial - 1)} :=
    fun n => Nat.rec ⟨x0, hx0⟩ (fun n x => f n x) n
  exact ⟨fun n => (s n).1, fun n => ⟨(s n).2, hf n (s n)⟩⟩

theorem divmul {a b c : ℕ} (h1 : a ∣ b) (h2 : b ∣ c) (hb : 0 < b) : c / b * (b / a) = c / a := by
  obtain ⟨u, rfl⟩ := h1
  obtain ⟨v, rfl⟩ := h2
  have ha : 0 < a := Nat.pos_of_mul_pos_right hb
  rw [Nat.mul_div_cancel_left _ hb, Nat.mul_div_cancel_left _ ha, mul_assoc, Nat.mul_div_cancel_left _ ha, mul_comm]

theorem gensys : ∃ ζ : ℕ → Formalism.CyclotomicNorms.Fbar g, ∀ d, 0 < d → IsPrimitiveRoot (ζ d) (g ^ d - 1) ∧
    ∀ d', d ∣ d' → 0 < d' → ζ d' ^ ((g ^ d' - 1) / (g ^ d - 1)) = ζ d := by
  obtain ⟨z, hz⟩ := chain g
  have hc : ∀ n k, z (n + k) ^ ((g ^ (n+k).factorial - 1) / (g ^ n.factorial - 1)) = z n := by
    intro n k
    induction k with
    | zero => simp [Nat.div_self (pos g (Nat.factorial_pos n))]
    | succ k ih =>
      rw [← ih, ← (hz (n+k)).2, ← pow_mul, ← add_assoc,
        divmul (dv g (Nat.factorial_dvd_factorial (Nat.le_add_right n k)))
          (dv g (Nat.factorial_dvd_factorial (Nat.le_succ _))) (pos g (Nat.factorial_pos _))]
  refine ⟨fun d => z d ^ ((g ^ d.factorial - 1) / (g ^ d - 1)), fun d hd => ⟨?_, fun d' hdd hd' => ?_⟩⟩
  · exact (hz d).1.pow (pos g (Nat.factorial_pos _)) (Nat.div_mul_cancel (dv g (Nat.dvd_factorial hd le_rfl))).symm
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_dvd hd' hdd)
    beta_reduce
    rw [← hc d k, ← pow_mul, ← pow_mul,
      divmul (dv g hdd) (dv g (Nat.dvd_factorial hd' le_rfl)) (pos g hd'),
      divmul (dv g (Nat.dvd_factorial hd le_rfl)) (dv g (Nat.factorial_dvd_factorial (Nat.le_add_right d k))) (pos g (Nat.factorial_pos _))]

theorem level (x : Formalism.CyclotomicNorms.Fbar g) (hx : x ≠ 0) : ∃ d, 0 < d ∧ x ^ (g ^ d - 1) = 1 := by
  have hint : IsIntegral (ZMod g) x := Algebra.IsIntegral.isIntegral x
  let K := IntermediateField.adjoin (ZMod g) {x}
  haveI : FiniteDimensional (ZMod g) K := IntermediateField.adjoin.finiteDimensional hint
  haveI : Finite K := Module.finite_of_finite (ZMod g)
  letI : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = g ^ Module.finrank (ZMod g) K := by
    rw [Module.card_eq_pow_finrank (K := ZMod g), ZMod.card]
  let y : K := ⟨x, IntermediateField.mem_adjoin_simple_self _ x⟩
  have hy : y ≠ 0 := fun h => hx (congrArg Subtype.val h)
  have := FiniteField.pow_card_sub_one_eq_one y hy
  rw [hcard] at this
  exact ⟨_, Module.finrank_pos, by simpa [y] using congrArg Subtype.val this⟩

noncomputable def E (d : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / ((g ^ d - 1 : ℕ) : ℂ))

theorem E_prim {d : ℕ} (hd : 0 < d) : IsPrimitiveRoot (E g d) (g ^ d - 1) :=
  Complex.isPrimitiveRoot_exp _ (pos g hd).ne'

theorem E_pow {d d' : ℕ} (h : d ∣ d') (hd : 0 < d) (hd' : 0 < d') : E g d' ^ ((g ^ d' - 1) / (g ^ d - 1)) = E g d := by
  obtain ⟨c, hc⟩ := dv g h
  have h1 := pos g hd
  have h2 := pos g hd'
  have hc0 : c ≠ 0 := by rintro rfl; omega
  unfold E
  rw [← Complex.exp_nat_mul, hc, Nat.mul_div_cancel_left _ h1]
  congr 1
  have : ((g ^ d - 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 h1.ne'
  have : (c : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hc0
  rw [Nat.cast_mul]
  field_simp

theorem prim_iff {R : Type} [CommMonoid R] {z : R} {m : ℕ} (h : IsPrimitiveRoot z m) (hm : 0 < m) (a b : ℕ) :
    z ^ a = z ^ b ↔ a ≡ b [MOD m] := by
  have hf : IsOfFinOrder z := isOfFinOrder_iff_pow_eq_one.2 ⟨m, hm, h.pow_eq_one⟩
  rw [hf.pow_eq_pow_iff_modEq, ← h.eq_orderOf]

theorem inhab : Nonempty (LabelDatum g) := by
  classical
  obtain ⟨ζ, hζ⟩ := gensys g
  let R : Formalism.CyclotomicNorms.Fbar g → ℂ → Prop := fun x c => ∃ d, 0 < d ∧ ∃ j, x = ζ d ^ j ∧ c = E g d ^ j
  have common : ∀ x c y c', R x c → R y c' → ∃ d, 0 < d ∧ ∃ j j', x = ζ d ^ j ∧ c = E g d ^ j ∧ y = ζ d ^ j' ∧ c' = E g d ^ j' := by
    rintro x c y c' ⟨d, hd, j, rfl, rfl⟩ ⟨e, he, k, rfl, rfl⟩
    have hde := Nat.mul_pos hd he
    refine ⟨d * e, hde, (g ^ (d * e) - 1) / (g ^ d - 1) * j, (g ^ (d * e) - 1) / (g ^ e - 1) * k, ?_, ?_, ?_, ?_⟩
    · rw [pow_mul (ζ _), (hζ d hd).2 _ (Dvd.intro _ rfl) hde]
    · rw [pow_mul (E _ _), E_pow g (Dvd.intro _ rfl) hd hde]
    · rw [pow_mul (ζ _), (hζ e he).2 _ (Dvd.intro_left _ rfl) hde]
    · rw [pow_mul (E _ _), E_pow g (Dvd.intro_left _ rfl) he hde]
  have key : ∀ x c y c', R x c → R y c' → (x = y ↔ c = c') := by
    intro x c y c' h h'
    obtain ⟨d, hd, j, j', rfl, rfl, rfl, rfl⟩ := common _ _ _ _ h h'
    rw [prim_iff (hζ d hd).1 (pos g hd), prim_iff (E_prim g hd) (pos g hd)]
  have mul : ∀ x c y c', R x c → R y c' → R (x * y) (c * c') := by
    intro x c y c' h h'
    obtain ⟨d, hd, j, j', rfl, rfl, rfl, rfl⟩ := common _ _ _ _ h h'
    exact ⟨d, hd, j + j', (pow_add _ _ _).symm, (pow_add _ _ _).symm⟩
  have ex : ∀ x, x ≠ 0 → ∃ c, R x c := by
    intro x hx
    obtain ⟨d, hd, h⟩ := level g x hx
    haveI : NeZero (g ^ d - 1) := ⟨(pos g hd).ne'⟩
    obtain ⟨j, -, hj⟩ := (hζ d hd).1.eq_pow_of_pow_eq_one h
    exact ⟨_, d, hd, j, hj.symm, rfl⟩
  choose! t ht using ex
  let t' : Formalism.CyclotomicNorms.Fbar g → ℂ := fun x => if x = 0 then 0 else t x
  have ht' : ∀ x, x ≠ 0 → R x (t' x) := fun x hx => by simpa [t', hx] using ht x hx
  refine ⟨⟨⟨⟨t', ?_⟩, ?_⟩, ?_, ζ, fun d hd => (hζ d hd).1.eq_orderOf.symm,
    fun d e hd he => (hζ d hd).2 _ (Dvd.intro _ rfl) (Nat.mul_pos hd he)⟩⟩
  · exact (key _ _ _ _ (ht' 1 one_ne_zero) ⟨1, one_pos, 0, by simp, by simp⟩).1 rfl
  · intro x y
    by_cases hx : x = 0
    · simp [t', hx]
    by_cases hy : y = 0
    · simp [t', hy]
    exact (key _ _ _ _ (ht' _ (mul_ne_zero hx hy)) (mul _ _ _ _ (ht' x hx) (ht' y hy))).1 rfl
  · intro x y hx hy h
    exact (key _ _ _ _ (ht' x hx) (ht' y hy)).2 h

theorem inhab_teich (t : Formalism.CyclotomicNorms.Fbar g →* ℂ) (ht : ∀ x y, x ≠ 0 → y ≠ 0 → t x = t y → x = y) :
    ∃ L : LabelDatum g, L.teich = t := by
  obtain ⟨L⟩ := inhab g
  exact ⟨⟨t, ht, L.gen, L.gen_order, L.gen_norm⟩, rfl⟩

theorem thetaOf_pow (L : LabelDatum g) {d : ℕ} (hd : 0 < d) {x : Formalism.CyclotomicNorms.Fbar g} (hx : x ^ (g ^ d - 1) = 1) (n : ℕ) :
    thetaOf L d x (L.gen d ^ n) = L.teich x ^ n := by
  have h : ∃ m : ℕ, L.gen d ^ n = L.gen d ^ m := ⟨n, rfl⟩
  have hp : IsPrimitiveRoot (L.gen d) (g ^ d - 1) := L.gen_order d hd ▸ IsPrimitiveRoot.orderOf _
  have h1 := (prim_iff hp (pos g hd) _ _).1 h.choose_spec
  have h2 : L.teich x ^ (g ^ d - 1) = 1 := by rw [← map_pow, hx, map_one]
  rw [thetaOf, dif_pos h, pow_eq_pow_mod _ h2, pow_eq_pow_mod n h2, h1]

theorem isCusp_one (χ : Gn g 1 → ℂ) : IsCusp χ ↔ IsIrr χ :=
  ⟨fun h => h.2.1, fun h => ⟨one_pos, h, fun a h1 h2 => by omega⟩⟩

end GlobalTheory.GLq.LabelModel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TraceMemAdjoin
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module TensorProduct GlobalTheory.Pass

namespace GlobalTheory.CentralIdem

theorem trace_mem_adjoin {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (T : Module.End ℂ V) {n : ℕ} (hn : n ≠ 0) (hT : T ^ (n + 1) = T) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ n) :
    LinearMap.trace ℂ V T ∈ Algebra.adjoin ℤ ({ζ} : Set ℂ) := by
  haveI : NeZero n := ⟨hn⟩
  rw [Module.End.trace_eq_sum_roots_charpoly_of_splits (IsAlgClosed.splits _)]
  apply Subalgebra.multiset_sum_mem
  intro μ hμ
  have hr : T.charpoly.IsRoot μ := Polynomial.isRoot_of_mem_roots hμ
  have he : T.HasEigenvalue μ := (Module.End.hasEigenvalue_iff_isRoot_charpoly T μ).2 hr
  obtain ⟨v, hv⟩ := he.exists_hasEigenvector
  have h1 := hv.pow_apply (n + 1)
  rw [hT, hv.apply_eq_smul] at h1
  have h2 : μ = μ ^ (n + 1) := smul_left_injective ℂ hv.2 h1
  by_cases h0 : μ = 0
  · rw [h0]; exact Subalgebra.zero_mem _
  · have h3 : μ ^ n = 1 := by
      rw [pow_succ] at h2
      exact mul_right_cancel₀ h0 (by rw [one_mul]; exact h2.symm)
    obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one h3
    rw [← hi]
    exact Subalgebra.pow_mem _ (Algebra.subset_adjoin (Set.mem_singleton ζ)) _

theorem trace_lmul {Γ : Type} [Group Γ] [Finite Γ] (x : MonoidAlgebra ℂ Γ) :
    LinearMap.trace ℂ _ (Algebra.lmul ℂ (MonoidAlgebra ℂ Γ) x) = (Nat.card Γ : ℂ) * x.coeff 1 := by
  classical
  haveI := Fintype.ofFinite Γ
  rw [LinearMap.trace_eq_matrix_trace ℂ (MonoidAlgebra.basis Γ ℂ), Matrix.trace]
  have : ∀ g : Γ, (LinearMap.toMatrix (MonoidAlgebra.basis Γ ℂ) (MonoidAlgebra.basis Γ ℂ)
      (Algebra.lmul ℂ (MonoidAlgebra ℂ Γ) x)).diag g = x.coeff 1 := by
    intro g
    rw [Matrix.diag, LinearMap.toMatrix_apply]
    have hb : MonoidAlgebra.basis Γ ℂ g = MonoidAlgebra.single g 1 := by simp
    rw [hb]
    change (x * MonoidAlgebra.single g (1 : ℂ)).coeff g = _
    rw [MonoidAlgebra.coeff_mul_single_apply]
    simp
  rw [Finset.sum_congr rfl fun g _ => this g]
  simp

theorem centralIdemCoeff : CentralIdemCoeff := by
  intro Γ _ _ e he hc ζ hζ h
  haveI : Module.Finite ℂ (MonoidAlgebra ℂ Γ) := Module.Finite.of_basis (MonoidAlgebra.basis Γ ℂ)
  set x : MonoidAlgebra ℂ Γ := MonoidAlgebra.single h⁻¹ (1 : ℂ) * e with hx
  have hcm : Commute (MonoidAlgebra.single h⁻¹ (1 : ℂ)) e := (hc _).symm
  have hid : IsIdempotentElem e := he
  have hp : x ^ (Nat.card Γ + 1) = x := by
    rw [hx, hcm.mul_pow, hid.pow_succ_eq, MonoidAlgebra.single_pow, one_pow, pow_succ,
      pow_card_eq_one', one_mul]
  have hT := trace_mem_adjoin (Algebra.lmul ℂ (MonoidAlgebra ℂ Γ) x) (n := Nat.card Γ)
    Nat.card_pos.ne' (by rw [← map_pow, hp]) hζ
  rw [trace_lmul, hx, MonoidAlgebra.coeff_single_mul_apply] at hT
  simpa using hT

end GlobalTheory.CentralIdem
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TracePairingInjectiveEquivariantLevelMapStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tracePairing_injective_equivariant_levelMap : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL] (A A' : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (LA' : Lattice (O := O) A'.ρ) (m : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDualLat1 (P.PD K) LA LA' m → ∀ (lam : LL →ₗ[ℚ_[l]] ℚ_[l]), (∀ a : LL, (∀ b : O, ∃ u : ℤ_[l], lam (a * algebraMap O LL b) = (u : ℚ_[l])) ↔ ∃ b : O, algebraMap O LL b = a) → ∀ (r : ℕ) (hI : StableSub LA (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA.T)) (hI' : StableSub LA' (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA'.T)), (∀ g : ↥(GK K), ∃ u : ℤ_[l], (((P.PD K).χ g : ℚ_[l]ˣ) : ℚ_[l]) = (u : ℚ_[l]) ∧ (PadicInt.toZModPow r u : ZMod (l ^ r)) = ((Formalism.GaloisCohomology.cycK l K.1 r (IntermediateField.fixingSubgroupEquiv K.1 g) : (ZMod (l ^ r))ˣ) : ZMod (l ^ r))) → ∀ (M : Type) [AddCommGroup M] [Module (ZMod (l ^ r)) M] (e : (↥LA.T ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA.T)) ≃+ M) (rho : Representation (ZMod (l ^ r)) (Formalism.GaloisCohomology.GK l K.1) M), (∀ g x, rho g (e x) = e (actQ LA _ hI ((IntermediateField.fixingSubgroupEquiv K.1).symm g) x)) → ∃ Ψ : (↥LA'.T ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA'.T)) →+ ReciprocityTheory.Gal.TDual (ZMod (l ^ r)) M, Function.Injective Ψ ∧ ∀ g y, Ψ (actQ LA' _ hI' ((IntermediateField.fixingSubgroupEquiv K.1).symm g) y) = ReciprocityTheory.Gal.twDual (Formalism.GaloisCohomology.cycK l K.1 r) rho g (Ψ y) := by
  first | exact @GlobalTheory.tracePairing_levelMap | exact GlobalTheory.tracePairing_levelMap | (intros; apply GlobalTheory.tracePairing_levelMap <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedDualFamiliesContinuous
section
noncomputable section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module TensorProduct GlobalTheory.Pass

namespace GlobalTheory.Pass.FamCont

theorem epsU_cont {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (i : N.Loc) :
    Continuous fun g => ((epsU N i g : (N.O i)ˣ) : N.O i) := by
  have h : ∀ g, ((epsU N i g : (N.O i)ˣ) : N.O i) =
      ((N.chi i 1 g : (N.O i)ˣ) : N.O i) * ((N.chi i 2 g⁻¹ : (N.O i)ˣ) : N.O i) := by
    intro g
    have := R.rank_add_five_le
    rw [← Units.val_mul, N.chi_def i 2 (by omega) (by omega)]
    simp [Glob.epsO]
  simp only [h]
  exact (N.chi_cont i 1).mul ((N.chi_cont i 2).comp continuous_inv)

theorem stepCont : StepCont := by
  intro D i r hr x
  have hc := (hr x).1
  constructor
  · have h1 : Continuous fun g : GE D.nd => ((D.nd.chi i 1 g⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) :=
      (D.nd.chi_cont i 1).comp continuous_inv
    refine (h1.smul hc).congr fun g => ?_
    simp [rTwO, twistM, rO]
  · have h1 := (D.nd.chi_cont i 1).mul (epsU_cont D.nd i)
    have h2 := (hc.comp continuous_inv).matrix_transpose
    refine (h1.smul h2).congr fun g => ?_
    rfl

end GlobalTheory.Pass.FamCont

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TypePrimeExceedsConstant
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

namespace GlobalTheory

theorem typePrime_real_bound {C F N k b : ℝ} (hF0 : 0 ≤ F) (hN0 : 0 ≤ N)
    (hC : C ≤ b) (hF : F ≤ 5 * b) (hN : N ≤ 3 * (k * b)) (hk : 5 ≤ k) (hb : 1 ≤ b) :
    C * (F * N ^ 2 + N ^ 3) < (k * b) ^ 8 := by
  set y := k * b with hy
  have hby : 5 * b ≤ y := by rw [hy]; nlinarith
  have hy5 : 5 ≤ y := by linarith
  have hy0 : 0 < y := by linarith
  have h1 : F * N ^ 2 + N ^ 3 ≤ y * (3 * y) ^ 2 + (3 * y) ^ 3 := by
    have hFy : F ≤ y := by linarith
    gcongr
  have h0 : 0 ≤ F * N ^ 2 + N ^ 3 := by positivity
  have h2 : C * (F * N ^ 2 + N ^ 3) ≤ y * (y * (3 * y) ^ 2 + (3 * y) ^ 3) :=
    mul_le_mul (by linarith) h1 h0 hy0.le
  have h3 : y * (y * (3 * y) ^ 2 + (3 * y) ^ 3) = 36 * y ^ 4 := by ring
  have h4 : (5 : ℝ) ^ 4 ≤ y ^ 4 := by gcongr
  have h5 : 0 < y ^ 4 := by positivity
  have h6 : y ^ 8 = y ^ 4 * y ^ 4 := by ring
  rw [h6]
  nlinarith

theorem typePrime_exceeds_constant :
    ∀ (D : D7) (L : SizeData₂ D), ParameterChoice' D L → L.etaSz + D.R.t + L.Sc ≤ L.sc.b → 1 ≤ L.sc.b → ∀ CT : ℕ, (CT : ℝ) ≤ L.sc.b → (⌊L.etaSz⌋₊ + D.R.t + 1 < ⌊3 * L.sc.b⌋₊ + 2) ∧ ((⌊L.etaSz⌋₊ : ℝ) ≤ 2 * L.etaSz) ∧ ∀ k : Fin 2, CT * ((⌊3 * L.sc.b⌋₊ + 2 + 0) * (D.R.nV + 1) ^ 2 + (D.R.nV + 1) ^ 3) < D.host.g k := by
  intro D L P hsum hb CT hCT
  have heta := L.etaSz_pos
  have hSc := L.Sc_pos
  have hfl : (⌊L.etaSz⌋₊ : ℝ) ≤ L.etaSz := Nat.floor_le heta.le
  have ht0 : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
  refine ⟨?_, by linarith, fun i => ?_⟩
  · have : ⌊L.etaSz⌋₊ + D.R.t ≤ ⌊3 * L.sc.b⌋₊ := by
      apply Nat.le_floor
      push_cast
      linarith
    omega
  · obtain ⟨Y, hY, -, -, hg⟩ := P.g_Y
    have hgi := (hg i).1
    have hm := D.R.m_add_three_le_k
    have hm2 := D.R.two_le_m
    have hk5 : (5 : ℝ) ≤ D.R.k := by exact_mod_cast (by omega : 5 ≤ D.R.k)
    have hnV : D.R.nV + 1 ≤ 2 * D.R.k + D.R.t := by
      unfold Ranks.nV Ranks.r
      omega
    have hnVR : (D.R.nV : ℝ) + 1 ≤ 2 * D.R.k + D.R.t := by exact_mod_cast hnV
    have hfl3 : (⌊3 * L.sc.b⌋₊ : ℝ) ≤ 3 * L.sc.b := Nat.floor_le (by linarith)
    have hN : (D.R.nV : ℝ) + 1 ≤ 3 * ((D.R.k : ℝ) * L.sc.b) := by nlinarith
    have key := typePrime_real_bound (C := (CT : ℝ)) (F := (⌊3 * L.sc.b⌋₊ : ℝ) + 2)
      (N := (D.R.nV : ℝ) + 1) (by positivity) (by positivity) hCT (by linarith) hN hk5 hb
    have : ((CT * ((⌊3 * L.sc.b⌋₊ + 2 + 0) * (D.R.nV + 1) ^ 2 + (D.R.nV + 1) ^ 3) : ℕ) : ℝ) <
        (D.host.g i : ℝ) := by
      push_cast
      simp only [add_zero]
      linarith
    exact_mod_cast this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitDiscriminantMatrixQuotientIsUnit
section
open Matrix

namespace GlobalTheory.UnitDiscAlg

theorem unit_split {E : Type} [NontriviallyNormedField E] [IsUltrametricDist E]
    [LocallyCompactSpace E] {n : ℕ} {N : Matrix (Fin n) (Fin n) E} {ϖ : E}
    (hN : ∀ i j, ‖N i j‖ ≤ 1)
    (hB : ∃ u v : Polynomial E, (∀ i, ‖u.coeff i‖ ≤ 1) ∧ (∀ i, ‖v.coeff i‖ ≤ 1) ∧
      u * N.charpoly + v * Polynomial.derivative N.charpoly = 1)
    (h0 : 0 < ‖ϖ‖) (h1 : ‖ϖ‖ < 1) (hϖ : ∀ y : E, ‖y‖ < 1 → ‖y‖ ≤ ‖ϖ‖)
    (hcomm : ∀ x y : Matrix (Fin n) (Fin n) E, x * N = N * x → y * N = N * y → x * y = y * x)
    (y : Matrix (Fin n) (Fin n) E) (hyN : y * N = N * y) (hy : ∀ i j, ‖y i j‖ ≤ 1) :
    ∃ e a : Matrix (Fin n) (Fin n) E, e * N = N * e ∧ a * N = N * a ∧ (∀ i j, ‖e i j‖ ≤ 1 ∧ ‖a i j‖ ≤ 1) ∧
      e * e = e ∧ ‖(y * e + (1 - e)).det‖ = 1 ∧ y * (1 - e) = ϖ • a := by
  obtain ⟨x, z, a₁, a₂, a₃, ⟨hxN, hzN, h1N, h2N, h3N⟩, hint, hx, hyx, hyz⟩ :=
    GlobalTheory.T.commuting_integral_matrix_decompose E n N ϖ hN hB h0 h1 hϖ y hyN hy
  haveI : ProperSpace E := ProperSpace.of_locallyCompactSpace E
  obtain ⟨e, a', heN, ha'N, he, heI, ha'I, hea⟩ :=
    GlobalTheory.T.exists_integral_idempotent_lift_newton E n N x a₁ ϖ h1 hxN (fun i j => (hint i j).1) (fun i j => (hint i j).2.2.1) hx
  have hzI : ∀ i j, ‖z i j‖ ≤ 1 := fun i j => (hint i j).2.1
  have ha₂I : ∀ i j, ‖a₂ i j‖ ≤ 1 := fun i j => (hint i j).2.2.2.1
  have ha₃I : ∀ i j, ‖a₃ i j‖ ≤ 1 := fun i j => (hint i j).2.2.2.2
  refine ⟨e, a₂ - y * a', heN, ?_, fun i j => ⟨heI i j, integ_sub ha₂I (integ_mul hy ha'I) i j⟩,
    he, ?_, ?_⟩
  · rw [sub_mul, mul_sub, h2N, Matrix.mul_assoc, ha'N, ← Matrix.mul_assoc, hyN, Matrix.mul_assoc]
  ·
    have hye : y * e = e * y := hcomm y e hyN heN
    have hze : z * e = e * z := hcomm z e hzN heN
    have hyz' : y * z = z * y := hcomm y z hyN hzN
    have hprod : (y * e + (1 - e)) * (z * e + (1 - e)) = 1 + ϖ • (a₃ + y * z * a' - a') := by
      have e1 : e = x + ϖ • a' := by rw [← hea]; abel
      have e2 : y * z * x = x + ϖ • a₃ := by rw [← hyz]; abel
      have key : (y * e + (1 - e)) * (z * e + (1 - e)) = 1 + y * z * e - e := by
        have : (y * e + (1 - e)) * (z * e + (1 - e)) =
            y * (e * z) * e + y * e * (1 - e) + (1 - e) * z * e + (1 - e) * (1 - e) := by
          noncomm_ring
        rw [this, ← hze]
        have hee : e * (1 - e) = 0 := by rw [mul_sub, mul_one, he, sub_self]
        have hee' : (1 - e) * z * e = 0 := by
          rw [Matrix.mul_assoc, hze, ← Matrix.mul_assoc, sub_mul, one_mul, he, sub_self,
            Matrix.zero_mul]
        have hee'' : (1 - e) * (1 - e) = 1 - e := by
          rw [sub_mul, one_mul, mul_sub, mul_one, he, sub_self, sub_zero]
        rw [Matrix.mul_assoc y e (1 - e), hee, Matrix.mul_zero, hee', hee'',
          ← Matrix.mul_assoc, Matrix.mul_assoc (y * z) e e, he]
        abel
      rw [key]
      conv_lhs => rw [e1]
      rw [Matrix.mul_add, e2, Matrix.mul_smul]
      simp only [smul_add, smul_sub]
      abel
    have hwI : ∀ i j, ‖(y * e + (1 - e)) i j‖ ≤ 1 :=
      integ_add (integ_mul hy heI) (integ_sub integ_one heI)
    have hw'I : ∀ i j, ‖(z * e + (1 - e)) i j‖ ≤ 1 :=
      integ_add (integ_mul hzI heI) (integ_sub integ_one heI)
    have hd := congrArg (fun m => ‖m.det‖) hprod
    simp only [Matrix.det_mul, norm_mul] at hd
    rw [GlobalTheory.T.ultrametric_norm_det_one_add_smul E n _ ϖ h1 (integ_sub (integ_add ha₃I (integ_mul (integ_mul hy hzI) ha'I)) ha'I)]
      at hd
    have ha := GlobalTheory.T.norm_det_le_one_of_entries_norm_le_one E n _ hwI
    have hb := GlobalTheory.T.norm_det_le_one_of_entries_norm_le_one E n _ hw'I
    nlinarith [norm_nonneg (y * e + (1 - e)).det, norm_nonneg (z * e + (1 - e)).det]
  · have : y * (1 - e) = y * (1 - x) - y * (e - x) := by noncomm_ring
    rw [this, hyx, hea, Matrix.mul_smul, ← smul_sub]

theorem units_quotient : ∀ (E : Type) [NontriviallyNormedField E] [IsUltrametricDist E] [LocallyCompactSpace E] (n : ℕ) (N c b : Matrix (Fin n) (Fin n) E) (ϖ : E), (∀ i j, ‖N i j‖ ≤ 1) → (∃ u v : Polynomial E, (∀ i, ‖u.coeff i‖ ≤ 1) ∧ (∀ i, ‖v.coeff i‖ ≤ 1) ∧ u * N.charpoly + v * Polynomial.derivative N.charpoly = 1) → 0 < ‖ϖ‖ → ‖ϖ‖ < 1 → (∀ y : E, ‖y‖ < 1 → ‖y‖ ≤ ‖ϖ‖) → IsUnit c → c * N = N * c → b * N = N * b → (∀ i j, ‖b i j‖ ≤ 1) → ‖b.det‖ = 1 → IsUnit (ϖ • (1 : Matrix (Fin n) (Fin n) E) + c ^ 2) ∧ IsUnit (ϖ • (1 : Matrix (Fin n) (Fin n) E) + c ^ 3) ∧ IsUnit (ϖ • c ^ 2 + b ^ 2) ∧ IsUnit (ϖ • c ^ 3 + b ^ 3) ∧ (∀ i j, ‖((ϖ • c ^ 3 + b ^ 3) * (ϖ • (1 : Matrix (Fin n) (Fin n) E) + c ^ 2) * ((ϖ • (1 : Matrix (Fin n) (Fin n) E) + c ^ 3) * (ϖ • c ^ 2 + b ^ 2))⁻¹) i j‖ ≤ 1) ∧ ‖((ϖ • c ^ 3 + b ^ 3) * (ϖ • (1 : Matrix (Fin n) (Fin n) E) + c ^ 2) * ((ϖ • (1 : Matrix (Fin n) (Fin n) E) + c ^ 3) * (ϖ • c ^ 2 + b ^ 2))⁻¹).det‖ = 1 := by
  intro E _ _ _ n N c b ϖ hN hB h0 h1 hϖ hc hcN hbN hb hbd
  have hB' : ∃ u v : Polynomial E, u * N.charpoly + v * Polynomial.derivative N.charpoly = 1 := by
    obtain ⟨u, v, -, -, h⟩ := hB
    exact ⟨u, v, h⟩
  have hcomm : ∀ x y : Matrix (Fin n) (Fin n) E, x * N = N * x → y * N = N * y → x * y = y * x :=
    fun x y hx hy => comm_of_bezout hB' hx hy
  obtain ⟨e₁, e₂, e₃, u, a₂, a₃, hN6, hI6, hu, h11, h22, h33, h12, h13, h23, hs, hc1, hc2, hc3⟩ :=
    GlobalTheory.T.matrix_commutant_valuation_decomposition E n N ϖ h0 h1 hcomm (unit_split hN hB h0 h1 hϖ hcomm) c hc hcN
  exact GlobalTheory.T.quotient_integral_unit_alt E n N c b e₁ e₂ e₃ u a₂ a₃ ϖ h0 h1 hcomm hc hcN hbN hb hbd hN6 hI6 hu h11 h22 h33
    h12 h13 h23 hs hc1 hc2 hc3

end GlobalTheory.UnitDiscAlg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedPadicDecompositionHomExistsStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramified_padic_decomposition_hom_exists : ReciprocityTheory.ChartRestriction.T2.UnrDec := by
  first | exact @GlobalTheory.UnrChar.unrDec | exact GlobalTheory.UnrChar.unrDec | (intros; apply GlobalTheory.UnrChar.unrDec <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeightLocalisationRegularAlgebraic
section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory

theorem weight_localisation_regular_algebraic : ∀ (D : D7) (i : D.nd.Loc) (P : D.naut.AV i) (τ : D.host.E →+* ℂ),
    (D.naut.infWt i τ).Nodup ∧ ∀ z ∈ D.naut.infWt i τ, ∃ k : ℤ, z = (k : ℂ) + ((D.R.nV : ℂ) - 1) / 2 := by
  intro D i P τ
  rw [D.nbc.embAV_inf i P]
  exact D.nbc.infW_alg _ _ τ

end GlobalTheory
end

